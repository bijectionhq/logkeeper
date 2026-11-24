mod registry;

pub(super) use registry::Registry;

use super::{
    ApplicationRoute, Checkpoint, Credentials, Endpoint, Failure, InstalledGroup, MANAGEMENT,
    Placement, invalid, tls,
};
use serde::{Deserialize, Serialize};
use std::{io, time::Duration};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::time::timeout;
use tokio_rustls::TlsConnector;
use uuid::Uuid;

const MAX_FRAME: usize = 8 << 20;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RouteBinding {
    pub name: String,
    pub organization: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublishedRoute {
    pub binding: RouteBinding,
    pub route: ApplicationRoute,
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "operation", rename_all = "snake_case", deny_unknown_fields)]
pub enum ManagementRequest {
    InstallGroup {
        group: Box<InstalledGroup>,
        expected_absent: bool,
    },
    PublishRoute {
        placement: Placement,
        binding: RouteBinding,
    },
    RouteByDeployment {
        deployment: Uuid,
    },
    RouteByName {
        name: String,
    },
    RetireGroup {
        placement: Placement,
        final_checkpoint: Checkpoint,
    },
    RetirementStatus {
        deployment: Uuid,
    },
    RetirementCheckpoint {
        placement: Placement,
    },
    Enrollment {
        placement: Placement,
        worker: Uuid,
    },
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "outcome",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum ManagementReply {
    Installed(ApplicationRoute),
    Published(PublishedRoute),
    Retired(Checkpoint),
    RetirementStatus {
        route: PublishedRoute,
        checkpoint: Checkpoint,
    },
    RetirementCheckpoint(Checkpoint),
    Enrollment(Option<super::Enrollment>),
    Absent,
    Conflict,
    Forbidden,
    Deferred,
}

pub struct DaemonClient {
    connector: TlsConnector,
    deadline: Duration,
}

impl DaemonClient {
    pub fn new(credentials: &Credentials, deadline: Duration) -> io::Result<Self> {
        Ok(Self {
            connector: credentials.client(MANAGEMENT)?,
            deadline,
        })
    }

    pub async fn call(
        &self,
        voter: &Endpoint,
        request: &ManagementRequest,
    ) -> Result<ManagementReply, Failure> {
        Ok(timeout(self.deadline, async {
            let mut channel = tls::open(&self.connector, voter, MANAGEMENT, [0; 32]).await?;
            write(&mut channel, request).await?;
            read(&mut channel).await
        })
        .await??)
    }
}

async fn read<T: serde::de::DeserializeOwned>(
    stream: &mut (impl AsyncRead + Unpin),
) -> io::Result<T> {
    let size = stream.read_u32().await? as usize;
    if size > MAX_FRAME {
        return Err(invalid("ordered management frame too large"));
    }
    let mut bytes = vec![0; size];
    stream.read_exact(&mut bytes).await?;
    serde_json::from_slice(&bytes).map_err(invalid)
}

async fn write(stream: &mut (impl AsyncWrite + Unpin), message: &impl Serialize) -> io::Result<()> {
    let bytes = serde_json::to_vec(message).map_err(invalid)?;
    if bytes.len() > MAX_FRAME {
        return Err(invalid("ordered management frame too large"));
    }
    stream.write_u32(bytes.len() as u32).await?;
    stream.write_all(&bytes).await?;
    stream.flush().await
}
