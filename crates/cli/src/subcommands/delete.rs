use crate::config::Config;
use crate::util::{add_auth_header_opt, database_address, get_auth_header_only};
use clap::{Arg, ArgMatches};

pub fn cli() -> clap::Command {
    clap::Command::new("delete")
        .about("Deletes a SpacetimeDB database")
        .arg(
            Arg::new("database")
                .required(true)
                .help("The domain or address of the database to delete"),
        )
        .arg(
            Arg::new("identity")
                .long("identity")
                .short('i')
                .help("The identity to use for deleting this database")
                .long_help("The identity to use for deleting this database. If no identity is provided, the default one will be used."),
        )
        .after_help("Run `spacetime help delete` for more detailed information.\n")
}

pub async fn exec(mut config: Config, args: &ArgMatches) -> Result<(), anyhow::Error> {
    let database = args.get_one::<String>("database").unwrap();
    let identity_or_name = args.get_one::<String>("identity");

    let address = database_address(&config, database).await?;

    let builder = reqwest::Client::new().post(format!("{}/database/delete/{}", config.get_host_url(), address));
    let auth_header = get_auth_header_only(&mut config, false, identity_or_name).await;
    let builder = add_auth_header_opt(builder, &auth_header);
    builder.send().await?.error_for_status()?;

    Ok(())
}