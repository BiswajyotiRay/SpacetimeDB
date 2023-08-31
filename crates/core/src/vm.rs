//! The [DbProgram] that execute arbitrary queries & code against the database.
use crate::db::cursor::{CatalogCursor, IndexCursor, TableCursor};
use crate::db::datastore::locking_tx_datastore::MutTxId;
use crate::db::datastore::traits::{ColumnDef, IndexDef, IndexId, SequenceId, TableDef};
use crate::db::relational_db::RelationalDB;
use itertools::Itertools;
use nonempty::NonEmpty;
use spacetimedb_lib::auth::{StAccess, StTableType};
use spacetimedb_lib::identity::AuthCtx;
use spacetimedb_lib::relation::{DbTable, FieldExpr, Relation};
use spacetimedb_lib::relation::{Header, MemTable, RelIter, RelValue, RowCount, Table};
use spacetimedb_lib::table::ProductTypeMeta;
use spacetimedb_sats::{AlgebraicValue, ProductValue, SatsString};
use spacetimedb_vm::dsl::mem_table;
use spacetimedb_vm::env::EnvDb;
use spacetimedb_vm::errors::ErrorVm;
use spacetimedb_vm::eval::IterRows;
use spacetimedb_vm::expr::*;
use spacetimedb_vm::program::{ProgramRef, ProgramVm};
use spacetimedb_vm::rel_ops::RelOps;
use std::collections::HashMap;
use std::ops::RangeBounds;

//TODO: This is partially duplicated from the `vm` crate to avoid borrow checker issues
//and pull all that crate in core. Will be revisited after trait refactor
#[tracing::instrument(skip_all)]
pub fn build_query<'a>(
    stdb: &'a RelationalDB,
    tx: &'a MutTxId,
    query: QueryCode,
) -> Result<Box<IterRows<'a>>, ErrorVm> {
    let q = match &query.table {
        Table::MemTable(x) => SourceExpr::MemTable(x.clone()),
        Table::DbTable(x) => SourceExpr::DbTable(x.clone()),
    };

    let mut ops = query.query.into_iter();
    let first = ops.next();

    // If the first operation is an index scan, open an index cursor, else a table cursor.
    let (mut result, ops) = if let Some(Query::IndexScan(IndexScan {
        table,
        col_id,
        lower_bound,
        upper_bound,
    })) = first
    {
        (
            iter_by_col_range(stdb, tx, table, col_id, (lower_bound, upper_bound))?,
            ops.collect(),
        )
    } else if let Some(op) = first {
        (get_table(stdb, tx, q)?, std::iter::once(op).chain(ops).collect())
    } else {
        (get_table(stdb, tx, q)?, vec![])
    };

    for op in ops {
        result = match op {
            Query::IndexScan(_) => {
                unreachable!()
            }
            Query::Select(cmp) => {
                let header = result.head().clone();
                let iter = result.select(move |row| cmp.compare(row, &header));
                Box::new(iter)
            }
            Query::Project(cols) => {
                if cols.is_empty() {
                    result
                } else {
                    let header = result.head().clone();
                    let iter = result.project(&cols.clone(), move |row| Ok(row.project(&cols, &header)?))?;
                    Box::new(iter)
                }
            }
            Query::JoinInner(q) => {
                //Pick the smaller set to be at the left
                let col_lhs = FieldExpr::Name(q.col_lhs);
                let col_rhs = FieldExpr::Name(q.col_rhs);
                let key_lhs = col_lhs.clone();
                let key_rhs = col_rhs.clone();

                let rhs = build_query(stdb, tx, q.rhs.into())?;
                let lhs = result;
                let key_lhs_header = lhs.head().clone();
                let key_rhs_header = rhs.head().clone();
                let col_lhs_header = lhs.head().clone();
                let col_rhs_header = rhs.head().clone();

                let iter = lhs.join_inner(
                    rhs,
                    move |row| {
                        let f = row.get(&key_lhs, &key_lhs_header);
                        Ok(f.into())
                    },
                    move |row| {
                        let f = row.get(&key_rhs, &key_rhs_header);
                        Ok(f.into())
                    },
                    move |l, r| {
                        let l = l.get(&col_lhs, &col_lhs_header);
                        let r = r.get(&col_rhs, &col_rhs_header);
                        Ok(l == r)
                    },
                )?;
                Box::new(iter)
            }
        }
    }
    Ok(result)
}

fn get_table<'a>(stdb: &'a RelationalDB, tx: &'a MutTxId, query: SourceExpr) -> Result<Box<dyn RelOps + 'a>, ErrorVm> {
    let head = query.head();
    let row_count = query.row_count();
    Ok(match query {
        SourceExpr::MemTable(x) => Box::new(RelIter::new(head, row_count, x)) as Box<IterRows<'_>>,
        SourceExpr::DbTable(x) => {
            let iter = stdb.iter(tx, x.table_id)?;
            Box::new(TableCursor::new(x, iter)?) as Box<IterRows<'_>>
        }
    })
}

fn iter_by_col_range<'a>(
    db: &'a RelationalDB,
    tx: &'a MutTxId,
    table: DbTable,
    col_id: u32,
    range: impl RangeBounds<AlgebraicValue> + 'a,
) -> Result<Box<dyn RelOps + 'a>, ErrorVm> {
    let iter = db.iter_by_col_range(tx, table.table_id, col_id, range)?;
    Ok(Box::new(IndexCursor::new(table, iter)?) as Box<IterRows<'_>>)
}

/// A [ProgramVm] implementation that carry a [RelationalDB] for it
/// query execution
pub struct DbProgram<'db, 'tx> {
    pub(crate) env: EnvDb,
    pub(crate) stats: HashMap<String, u64>,
    pub(crate) db: &'db RelationalDB,
    pub(crate) tx: &'tx mut MutTxId,
    pub(crate) auth: AuthCtx,
}

impl<'db, 'tx> DbProgram<'db, 'tx> {
    pub fn new(db: &'db RelationalDB, tx: &'tx mut MutTxId, auth: AuthCtx) -> Self {
        let mut env = EnvDb::new();
        Self::load_ops(&mut env);
        Self {
            env,
            db,
            stats: Default::default(),
            tx,
            auth,
        }
    }

    fn _eval_query(&mut self, query: QueryCode) -> Result<Code, ErrorVm> {
        let table_access = query.table.table_access();

        let result = build_query(self.db, self.tx, query)?;
        let head = result.head().clone();
        let rows: Vec<_> = result.collect_vec()?;

        Ok(Code::Table(MemTable::new(&head, table_access, &rows)))
    }

    fn _execute_insert(&mut self, table: &Table, rows: Vec<ProductValue>) -> Result<Code, ErrorVm> {
        match table {
            // TODO: How do we deal with mutating values?
            Table::MemTable(_) => Err(ErrorVm::Other(anyhow::anyhow!("How deal with mutating values?"))),
            Table::DbTable(x) => {
                for row in rows {
                    self.db.insert(self.tx, x.table_id, row)?;
                }
                Ok(Code::Pass)
            }
        }
    }

    fn _execute_delete(&mut self, table: &Table, rows: Vec<ProductValue>) -> Result<Code, ErrorVm> {
        match table {
            // TODO: How do we deal with mutating values?
            Table::MemTable(_) => Err(ErrorVm::Other(anyhow::anyhow!("How deal with mutating values?"))),
            Table::DbTable(t) => {
                let count = self.db.delete_by_rel(self.tx, t.table_id, rows)?;
                Ok(Code::Value(count.unwrap_or_default().into()))
            }
        }
    }

    fn delete_query(&mut self, query: QueryCode) -> Result<Code, ErrorVm> {
        let table = query.table.clone();
        let result = self._eval_query(query)?;

        match result {
            Code::Table(result) => {
                self._execute_delete(&table, result.data.into_iter().map(|row| row.data).collect_vec())
            }
            _ => Ok(result),
        }
    }

    fn insert_query(&mut self, table: &Table, query: QueryCode) -> Result<Code, ErrorVm> {
        let result = self._eval_query(query)?;
        match result {
            Code::Table(result) => {
                self._execute_insert(table, result.data.into_iter().map(|row| row.data).collect_vec())
            }
            _ => Ok(result),
        }
    }

    fn create_table(
        &mut self,
        table_name: SatsString,
        columns: ProductTypeMeta,
        table_type: StTableType,
        table_access: StAccess,
    ) -> Result<Code, ErrorVm> {
        let mut cols = Vec::with_capacity(columns.columns.len());
        let mut indexes = Vec::new();
        for (i, column) in columns.columns.iter().enumerate() {
            let meta = columns.attr[i];
            if meta.is_unique() {
                indexes.push(IndexDef {
                    table_id: 0, // Ignored
                    cols: NonEmpty::new(i as u32),
                    name: SatsString::from_string(format!("{}_{}_idx", table_name, i)),
                    is_unique: true,
                });
            }
            cols.push(ColumnDef {
                col_name: column
                    .name
                    .clone()
                    .unwrap_or_else(|| SatsString::from_string(i.to_string())),
                col_type: column.algebraic_type.clone(),
                is_autoinc: meta.is_autoinc(),
            })
        }
        self.db.create_table(
            self.tx,
            TableDef {
                table_name,
                columns: cols.into(),
                indexes,
                table_type,
                table_access,
            },
        )?;
        Ok(Code::Pass)
    }

    fn drop(&mut self, name: SatsString, kind: DbType) -> Result<Code, ErrorVm> {
        match kind {
            DbType::Table => {
                if let Some(id) = self.db.table_id_from_name(self.tx, name)? {
                    self.db.drop_table(self.tx, id)?;
                }
            }
            DbType::Index => {
                if let Some(id) = self.db.index_id_from_name(self.tx, name)? {
                    self.db.drop_index(self.tx, IndexId(id))?;
                }
            }
            DbType::Sequence => {
                if let Some(id) = self.db.sequence_id_from_name(self.tx, name)? {
                    self.db.drop_sequence(self.tx, SequenceId(id))?;
                }
            }
        }

        Ok(Code::Pass)
    }
}

impl ProgramVm for DbProgram<'_, '_> {
    fn env(&self) -> &EnvDb {
        &self.env
    }

    fn env_mut(&mut self) -> &mut EnvDb {
        &mut self.env
    }

    fn ctx(&self) -> &dyn ProgramVm {
        self as &dyn ProgramVm
    }

    fn auth(&self) -> &AuthCtx {
        &self.auth
    }

    fn eval_query(&mut self, query: CrudCode) -> Result<Code, ErrorVm> {
        query.check_auth(self.auth.owner, self.auth.caller)?;

        match query {
            CrudCode::Query(query) => self._eval_query(query),
            CrudCode::Insert { table, rows } => self._execute_insert(&table, rows),
            CrudCode::Update { mut insert, delete } => {
                let table = delete.table.clone();
                let result = self._eval_query(delete)?;

                let deleted = match result {
                    Code::Table(result) => result,
                    _ => return Ok(result),
                };
                self._execute_delete(
                    &table,
                    deleted.data.clone().into_iter().map(|row| row.data).collect_vec(),
                )?;

                let to_insert = mem_table(table.head(), deleted.data.into_iter().map(|row| row.data));
                insert.table = Table::MemTable(to_insert);

                let result = self.insert_query(&table, insert)?;
                Ok(result)
            }
            CrudCode::Delete { query } => {
                let result = self.delete_query(query)?;
                Ok(result)
            }
            CrudCode::CreateTable {
                name,
                columns,
                table_type,
                table_access,
            } => {
                let result = self.create_table(name, columns, table_type, table_access)?;
                Ok(result)
            }
            CrudCode::Drop {
                name,
                kind,
                table_access: _,
            } => self.drop(name, kind),
        }
    }

    fn as_program_ref(&self) -> ProgramRef<'_> {
        ProgramRef {
            env: &self.env,
            stats: &self.stats,
            ctx: self.ctx(),
        }
    }
}

impl RelOps for TableCursor<'_> {
    fn head(&self) -> &Header {
        &self.table.head
    }

    fn row_count(&self) -> RowCount {
        RowCount::unknown()
    }

    #[tracing::instrument(skip_all)]
    fn next(&mut self) -> Result<Option<RelValue>, ErrorVm> {
        Ok(self.iter.next().map(|row| row.into()))
    }
}

impl<R: RangeBounds<AlgebraicValue>> RelOps for IndexCursor<'_, R> {
    fn head(&self) -> &Header {
        &self.table.head
    }

    fn row_count(&self) -> RowCount {
        RowCount::unknown()
    }

    #[tracing::instrument(skip_all)]
    fn next(&mut self) -> Result<Option<RelValue>, ErrorVm> {
        Ok(self.iter.next().map(|row| row.into()))
    }
}

impl<I> RelOps for CatalogCursor<I>
where
    I: Iterator<Item = ProductValue>,
{
    fn head(&self) -> &Header {
        &self.table.head
    }

    fn row_count(&self) -> RowCount {
        self.row_count
    }

    #[tracing::instrument(skip_all)]
    fn next(&mut self) -> Result<Option<RelValue>, ErrorVm> {
        if let Some(row) = self.iter.next() {
            return Ok(Some(RelValue::new(row, None)));
        };
        Ok(None)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::db::datastore::system_tables::{
        st_columns_schema, st_indexes_schema, st_sequences_schema, st_table_schema, StColumnFields, StColumnRow,
        StIndexFields, StIndexRow, StSequenceFields, StSequenceRow, StTableFields, StTableRow, ST_COLUMNS_ID,
        ST_SEQUENCES_ID, ST_TABLES_ID,
    };
    use crate::db::relational_db::tests_utils::make_test_db;
    use crate::db::relational_db::{ST_COLUMNS_NAME, ST_INDEXES_NAME, ST_SEQUENCES_NAME, ST_TABLES_NAME};
    use spacetimedb_lib::error::ResultTest;
    use spacetimedb_lib::relation::{DbTable, FieldName};
    use spacetimedb_sats::{product, string, AlgebraicType, ProductType, ProductValue, SatsString};
    use spacetimedb_vm::dsl::*;
    use spacetimedb_vm::eval::run_ast;
    use spacetimedb_vm::operator::OpCmp;

    pub(crate) fn create_table_with_rows(
        db: &RelationalDB,
        tx: &mut MutTxId,
        table_name: &str,
        schema: ProductType,
        rows: &[ProductValue],
    ) -> ResultTest<u32> {
        let table_id = db.create_table(
            tx,
            TableDef {
                table_name: string(table_name),
                columns: schema
                    .elements
                    .iter()
                    .enumerate()
                    .map(|(i, e)| ColumnDef {
                        col_name: e.name.clone().unwrap_or_else(|| SatsString::from_string(i.to_string())),
                        col_type: e.algebraic_type.clone(),
                        is_autoinc: false,
                    })
                    .collect(),
                indexes: vec![],
                table_type: StTableType::User,
                table_access: StAccess::for_name(table_name),
            },
        )?;
        for row in rows {
            db.insert(tx, table_id, row.clone())?;
        }

        Ok(table_id)
    }

    pub(crate) fn create_table_from_program(
        p: &mut DbProgram,
        table_name: &str,
        schema: ProductType,
        rows: &[ProductValue],
    ) -> ResultTest<u32> {
        let db = &mut p.db;
        create_table_with_rows(db, p.tx, table_name, schema, rows)
    }

    #[test]
    /// Inventory
    /// | inventory_id: u64 | name : String |
    /// Player
    /// | entity_id: u64 | inventory_id : u64 |
    /// Location
    /// | entity_id: u64 | x : f32 | z : f32 |
    fn test_db_query() -> ResultTest<()> {
        let (stdb, _tmp_dir) = make_test_db()?;

        let mut tx = stdb.begin_tx();
        let p = &mut DbProgram::new(&stdb, &mut tx, AuthCtx::for_testing());

        let head = ProductType::from_iter([("inventory_id", AlgebraicType::U64), ("name", AlgebraicType::String)]);
        let row = product!(1u64, string("health"));
        let table_id = create_table_from_program(p, "inventory", head.clone(), &[row])?;

        let inv = db_table(head, string("inventory"), table_id);

        let data = MemTable::from_value(scalar(1u64));
        let rhs = data.get_field(0).unwrap().clone();

        let q = query(inv).with_join_inner(data, FieldName::positional("inventory", 0), rhs);

        let result = match run_ast(p, q.into()) {
            Code::Table(x) => x,
            x => panic!("invalid result {x}"),
        };

        //The expected result
        let inv = ProductType::from_iter([
            (Some("inventory_id"), AlgebraicType::U64),
            (Some("name"), AlgebraicType::String),
            (None, AlgebraicType::U64),
        ]);
        let row = product!(1u64, string("health"), 1u64);
        let input = mem_table(inv, vec![row]);

        assert_eq!(result.data, input.data, "Inventory");

        stdb.rollback_tx(tx);

        Ok(())
    }

    fn check_catalog(p: &mut DbProgram, name: &str, row: ProductValue, q: QueryExpr, schema: DbTable) {
        let result = run_ast(p, q.into());

        //The expected result
        let input = mem_table(schema.head, vec![row]);

        assert_eq!(result, Code::Table(input), "{}", name);
    }

    #[test]
    fn test_query_catalog_tables() -> ResultTest<()> {
        let (stdb, _tmp_dir) = make_test_db()?;

        let mut tx = stdb.begin_tx();
        let p = &mut DbProgram::new(&stdb, &mut tx, AuthCtx::for_testing());

        let q = query(&st_table_schema()).with_select_cmp(
            OpCmp::Eq,
            FieldName::named(ST_TABLES_NAME, StTableFields::TableName.name()),
            scalar(string(ST_TABLES_NAME)),
        );
        check_catalog(
            p,
            ST_TABLES_NAME,
            (StTableRow {
                table_id: ST_TABLES_ID.0,
                table_name: string(ST_TABLES_NAME),
                table_type: StTableType::System,
                table_access: StAccess::Public,
            })
            .into(),
            q,
            DbTable::from(&st_table_schema()),
        );

        stdb.rollback_tx(tx);

        Ok(())
    }

    #[test]
    fn test_query_catalog_columns() -> ResultTest<()> {
        let (stdb, _tmp_dir) = make_test_db()?;

        let mut tx = stdb.begin_tx();
        let p = &mut DbProgram::new(&stdb, &mut tx, AuthCtx::for_testing());

        let q = query(&st_columns_schema())
            .with_select_cmp(
                OpCmp::Eq,
                FieldName::named(ST_COLUMNS_NAME, StColumnFields::TableId.name()),
                scalar(ST_COLUMNS_ID.0),
            )
            .with_select_cmp(
                OpCmp::Eq,
                FieldName::named(ST_COLUMNS_NAME, StColumnFields::ColId.name()),
                scalar(StColumnFields::TableId as u32),
            );
        check_catalog(
            p,
            ST_COLUMNS_NAME,
            (StColumnRow {
                table_id: ST_COLUMNS_ID.0,
                col_id: StColumnFields::TableId as u32,
                col_name: string(StColumnFields::TableId.name()),
                col_type: AlgebraicType::U32,
                is_autoinc: false,
            })
            .into(),
            q,
            (&st_columns_schema()).into(),
        );

        stdb.rollback_tx(tx);

        Ok(())
    }

    #[test]
    fn test_query_catalog_indexes() -> ResultTest<()> {
        let (db, _tmp_dir) = make_test_db()?;

        let head = ProductType::from_iter([("inventory_id", AlgebraicType::U64), ("name", AlgebraicType::String)]);
        let row = product!(1u64, string("health"));

        let mut tx = db.begin_tx();
        let table_id = create_table_with_rows(&db, &mut tx, "inventory", head, &[row])?;
        db.commit_tx(tx)?;

        let mut tx = db.begin_tx();
        let index = IndexDef::new(string("idx_1"), table_id, 0, true);
        let index_id = db.create_index(&mut tx, index)?;

        let p = &mut DbProgram::new(&db, &mut tx, AuthCtx::for_testing());

        let q = query(&st_indexes_schema()).with_select_cmp(
            OpCmp::Eq,
            FieldName::named(ST_INDEXES_NAME, StIndexFields::IndexName.name()),
            scalar(string("idx_1")),
        );
        check_catalog(
            p,
            ST_INDEXES_NAME,
            (StIndexRow {
                index_id: index_id.0,
                index_name: string("idx_1"),
                table_id,
                cols: NonEmpty::new(0),
                is_unique: true,
            })
            .into(),
            q,
            (&st_indexes_schema()).into(),
        );

        db.rollback_tx(tx);

        Ok(())
    }

    #[test]
    fn test_query_catalog_sequences() -> ResultTest<()> {
        let (db, _tmp_dir) = make_test_db()?;

        let mut tx = db.begin_tx();
        let p = &mut DbProgram::new(&db, &mut tx, AuthCtx::for_testing());

        let q = query(&st_sequences_schema()).with_select_cmp(
            OpCmp::Eq,
            FieldName::named(ST_SEQUENCES_NAME, StSequenceFields::TableId.name()),
            scalar(ST_SEQUENCES_ID.0),
        );
        check_catalog(
            p,
            ST_SEQUENCES_NAME,
            (StSequenceRow {
                sequence_id: 1,
                sequence_name: string("sequence_id_seq"),
                table_id: 2,
                col_id: 0,
                increment: 1,
                start: 4,
                min_value: 1,
                max_value: 4294967295,
                allocated: 4096,
            })
            .into(),
            q,
            (&st_sequences_schema()).into(),
        );

        db.rollback_tx(tx);

        Ok(())
    }
}
