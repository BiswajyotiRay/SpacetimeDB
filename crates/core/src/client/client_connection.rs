use std::ops::Deref;

use crate::host::{ModuleHost, NoSuchModule, ReducerArgs, ReducerCallError, ReducerCallResult};
use crate::protobuf::client_api::Subscribe;
use crate::worker_metrics::{CONNECTED_CLIENTS, WEBSOCKET_SENT, WEBSOCKET_SENT_MSG_SIZE};
use futures::prelude::*;
use tokio::sync::mpsc;

use super::messages::ServerMessage;
use super::{message_handlers, ClientActorId, MessageHandleError};

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum Protocol {
    Text,
    Binary,
}

#[derive(Clone, Debug)]
pub struct ClientConnectionSender {
    pub id: ClientActorId,
    pub protocol: Protocol,
    sendtx: mpsc::Sender<DataMessage>,
}

#[derive(Debug, thiserror::Error)]
#[error("client disconnected")]
pub struct ClientClosed;

impl ClientConnectionSender {
    pub fn dummy(id: ClientActorId, protocol: Protocol) -> Self {
        let (sendtx, _) = mpsc::channel(1);
        Self { id, protocol, sendtx }
    }

    pub fn send_message(&self, message: impl ServerMessage) -> impl Future<Output = Result<(), ClientClosed>> + '_ {
        self.send(message.serialize(self.protocol))
    }

    pub async fn send(&self, message: DataMessage) -> Result<(), ClientClosed> {
        let bytes_len = message.len();

        self.sendtx.send(message).await.map_err(|_| ClientClosed)?;

        WEBSOCKET_SENT
            .with_label_values(&[self.id.identity.to_hex().as_str()])
            .inc();

        WEBSOCKET_SENT_MSG_SIZE
            .with_label_values(&[self.id.identity.to_hex().as_str()])
            .observe(bytes_len as f64);

        Ok(())
    }
}

#[derive(Clone)]
#[non_exhaustive]
pub struct ClientConnection {
    sender: ClientConnectionSender,
    pub database_instance_id: u64,
    pub module: ModuleHost,
}

impl Deref for ClientConnection {
    type Target = ClientConnectionSender;
    fn deref(&self) -> &Self::Target {
        &self.sender
    }
}

#[derive(Debug)]
pub enum DataMessage {
    Text(String),
    Binary(Vec<u8>),
}

impl DataMessage {
    pub fn len(&self) -> usize {
        match self {
            DataMessage::Text(s) => s.len(),
            DataMessage::Binary(b) => b.len(),
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl From<String> for DataMessage {
    fn from(text: String) -> Self {
        DataMessage::Text(text)
    }
}

impl From<Vec<u8>> for DataMessage {
    fn from(bin: Vec<u8>) -> Self {
        DataMessage::Binary(bin)
    }
}

impl ClientConnection {
    /// Returns an error if ModuleHost closed
    pub async fn spawn<F, Fut>(
        id: ClientActorId,
        protocol: Protocol,
        database_instance_id: u64,
        module: ModuleHost,
        actor: F,
    ) -> Result<ClientConnection, NoSuchModule>
    where
        F: FnOnce(ClientConnection, mpsc::Receiver<DataMessage>) -> Fut,
        Fut: Future<Output = ()> + Send + 'static,
    {
        // Add this client as a subscriber
        // TODO: Right now this is connecting clients directly to an instance, but their requests should be
        // logically subscribed to the database, not any particular instance. We should handle failover for
        // them and stuff. Not right now though.
        module.call_identity_connected_disconnected(id.identity, true).await?;

        // Buffer up to 64 client messages
        let (sendtx, sendrx) = mpsc::channel::<DataMessage>(64);

        let sender = ClientConnectionSender { id, protocol, sendtx };
        let this = Self {
            sender,
            database_instance_id,
            module,
        };

        let actor_fut = actor(this.clone(), sendrx);
        tokio::spawn(async move {
            CONNECTED_CLIENTS.inc();
            actor_fut.await;
            CONNECTED_CLIENTS.dec();
        });

        Ok(this)
    }

    pub fn dummy(id: ClientActorId, protocol: Protocol, database_instance_id: u64, module: ModuleHost) -> Self {
        Self {
            sender: ClientConnectionSender::dummy(id, protocol),
            database_instance_id,
            module,
        }
    }

    pub fn sender(&self) -> ClientConnectionSender {
        self.sender.clone()
    }

    #[inline]
    pub fn handle_message(
        &self,
        message: impl Into<DataMessage>,
    ) -> impl Future<Output = Result<(), MessageHandleError>> + '_ {
        message_handlers::handle(self, message.into())
    }

    pub async fn call_reducer(&self, reducer: &str, args: ReducerArgs) -> Result<ReducerCallResult, ReducerCallError> {
        self.module
            .call_reducer(self.id.identity, Some(self.sender()), reducer, args)
            .await
    }

    pub fn subscribe(&self, subscription: Subscribe) -> Result<(), NoSuchModule> {
        self.module.subscription().add_subscriber(self.sender(), subscription)
    }
}