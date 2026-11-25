mod authentication;

use super::{
    Failure, GroupConfig, InstalledGroup, MANIFEST_BYTES, Manifest, TlsPeers, VOTER,
    group_directory, invalid, sign,
};
use crate::ordered::{
    Fingerprint,
    replication::{DurableVoter, RepairSeed, transport::RemoteVoter},
    service::Coordinator,
};
use crate::server::durability::sync_directory;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;
use uuid::Uuid;

const TICKET: &[u8; 8] = b"LKPREP01";
const TICKET_BODY: usize = 8 + 32 + 16 + 8;
const SIGNATURE_BYTES: usize = 32 + 64;

impl Manifest {
    /// Pays for the successor before its predecessor can be sealed.
    pub fn reserve_repair(self, deployment: Uuid, output: &Path) -> Result<(), Failure> {
        let (manifest, groups) = self.resolve()?;
        let group = successor(&groups, deployment)?;
        let issuer = sign::Issuer::load(&manifest.barrier_key)?;
        if group.keys.active.get(&manifest.voter) != Some(&issuer.public_key()) {
            return Err(invalid(
                "the successor reservation signer does not match its installed voter",
            )
            .into());
        }
        let directory = manifest
            .directory
            .join(group_directory(group.group.identity()));
        fs::create_dir_all(&directory)?;
        let capacity = DurableVoter::reserve_repair(&group.group, manifest.voter, &directory)?;
        sync_directory(&manifest.directory)?;
        sync_parent(&manifest.directory)?;
        let mut body = BytesMut::with_capacity(TICKET_BODY + 64);
        body.put_slice(TICKET);
        body.put_slice(&group.group.identity());
        body.put_slice(manifest.voter.as_bytes());
        body.put_u64(capacity);
        let proof = issuer.sign_bytes(&body)?;
        body.put_slice(&proof.proof);
        publish_evidence(output, &[&body])?;
        Ok(())
    }

    /// Runs on a coordinator belonging to the old installed group.
    /// The exact successor must already have its independent paid votes.
    pub async fn seal_repair(
        self,
        destination: &Path,
        tickets: &[&Path],
        output: &Path,
    ) -> Result<(), Failure> {
        let body = read_evidence(destination, MANIFEST_BYTES)?;
        let configured: InstalledGroup = serde_json::from_slice(&body)?;
        let destination = configured.config()?;
        validate_tickets(&destination, tickets)?;
        let (manifest, mut groups) = self.resolve()?;
        let predecessor = destination
            .group
            .predecessor()
            .ok_or_else(|| invalid("the destination is not a successor"))?;
        let source = groups
            .remove(&predecessor)
            .ok_or_else(|| invalid("the source manifest lacks the exact predecessor"))?;
        destination.keys.validate_successor_keys(&source.keys)?;
        let issuer = sign::Issuer::load(&manifest.barrier_key)?;
        if source.keys.active.get(&manifest.voter) != Some(&issuer.public_key())
            || !destination.keys.predecessor.contains(&issuer.public_key())
        {
            return Err(
                invalid("the predecessor signer is outside the repair authorization").into(),
            );
        }
        let deadline = Duration::from_millis(manifest.exchange_ms);
        let members = Arc::new(source.members);
        let tls = TlsPeers {
            connector: manifest.credentials.client(VOTER)?,
            group: source.group.identity(),
            members: Arc::clone(&members),
        };
        let peers = members
            .keys()
            .map(|voter| RemoteVoter::new(&source.group, *voter, tls.clone(), deadline))
            .collect::<Result<Vec<_>, _>>()?;
        let coordinator = Coordinator::new(source.group, peers);
        let seed = coordinator
            .seal_for_repair(&destination.group)
            .await?
            .encode();
        let proof = issuer.sign_bytes(&seed)?;
        publish_evidence(output, &[&proof.issuer, &proof.proof, &seed])?;
        Ok(())
    }

    pub fn install_repair(self, deployment: Uuid, package: &Path) -> Result<(), Failure> {
        let (manifest, groups) = self.resolve()?;
        let target = successor(&groups, deployment)?;
        let maximum = (target.group.maximum_prefix_bytes() as u64)
            .checked_add(72 + SIGNATURE_BYTES as u64)
            .ok_or_else(|| invalid("repair package limit overflows"))?;
        let packet = read_evidence(package, maximum)?;
        if packet.len() <= SIGNATURE_BYTES {
            return Err(invalid("the repair package has no certified image").into());
        }
        authentication::verify_repair_signature(
            &target.keys,
            packet[..32].try_into()?,
            &packet[SIGNATURE_BYTES..],
            &packet[32..SIGNATURE_BYTES],
        )?;
        let seed = RepairSeed::decode(packet.slice(SIGNATURE_BYTES..))?;
        let directory = manifest
            .directory
            .join(group_directory(target.group.identity()));
        DurableVoter::initialize_repaired(target.group.clone(), manifest.voter, &directory, &seed)?;
        Ok(())
    }
}

fn successor(
    groups: &BTreeMap<Fingerprint, GroupConfig>,
    deployment: Uuid,
) -> Result<&GroupConfig, Failure> {
    let mut current = groups.values().filter(|group| {
        group.group.placement().deployment == deployment && group.group.predecessor().is_some()
    });
    let candidate = current
        .next()
        .ok_or_else(|| invalid("there is no installed successor for that deployment"))?;
    if current.next().is_some() {
        return Err(invalid("the repair manifest names more than one successor").into());
    }
    Ok(candidate)
}

fn validate_tickets(destination: &GroupConfig, tickets: &[&Path]) -> Result<(), Failure> {
    let mut paid = BTreeSet::new();
    for path in tickets {
        let packet = read_evidence(path, (TICKET_BODY + 64) as u64)?;
        if packet.len() != TICKET_BODY + 64
            || &packet[..8] != TICKET
            || packet[8..40] != destination.group.identity()
        {
            return Err(invalid("a repair reservation addresses a different successor").into());
        }
        let voter = Uuid::from_slice(&packet[40..56])?;
        let key = destination
            .keys
            .active
            .get(&voter)
            .ok_or_else(|| invalid("a repair reservation names an unknown voter"))?;
        sign::verify_bytes(key, &packet[..TICKET_BODY], &packet[TICKET_BODY..])?;
        let mut capacity = &packet[56..TICKET_BODY];
        if capacity.get_u64() != DurableVoter::reserved_bytes(&destination.group)?
            || !paid.insert(voter)
        {
            return Err(invalid("a repair reservation has the wrong scope or was repeated").into());
        }
    }
    if !super::super::cohort::has_paid_repair_quorum(paid.len(), destination.group.quorum()) {
        return Err(invalid("no prepaid successor quorum is available").into());
    }
    Ok(())
}

fn read_evidence(path: &Path, limit: u64) -> Result<Bytes, Failure> {
    let mut bytes = Vec::new();
    File::open(path)?
        .take(
            limit
                .checked_add(1)
                .ok_or_else(|| invalid("repair evidence limit overflows"))?,
        )
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit {
        return Err(invalid("repair evidence exceeds its installed bound").into());
    }
    Ok(Bytes::from(bytes))
}

fn evidence_matches(path: &Path, parts: &[&[u8]]) -> Result<bool, Failure> {
    let mut file = File::open(path)?;
    let mut scratch = [0; 8192];
    let mut equal = true;
    for part in parts {
        for expected in part.chunks(scratch.len()) {
            match file.read_exact(&mut scratch[..expected.len()]) {
                Ok(()) => equal &= &scratch[..expected.len()] == expected,
                Err(error) if error.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(false),
                Err(error) => return Err(error.into()),
            }
        }
    }
    loop {
        match file.read(&mut scratch[..1]) {
            Ok(0) => break,
            Ok(_) => return Err(invalid("repair evidence exceeds its installed bound").into()),
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => (),
            Err(error) => return Err(error.into()),
        }
    }
    Ok(equal)
}

fn publish_evidence(path: &Path, parts: &[&[u8]]) -> Result<(), Failure> {
    if path.try_exists()? {
        if evidence_matches(path, parts)? {
            return Ok(());
        }
        return Err(invalid("a different repair receipt occupies this path").into());
    }
    let stage = path.with_extension(format!("pending-{}", Uuid::new_v4()));
    let published = (|| -> Result<(), Failure> {
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&stage)?;
        for part in parts {
            file.write_all(part)?;
        }
        file.sync_all()?;
        // Publish without overwriting a concurrent original result.
        match fs::hard_link(&stage, path) {
            Ok(()) => Ok(()),
            Err(error)
                if error.kind() == std::io::ErrorKind::AlreadyExists
                    && evidence_matches(path, parts)? =>
            {
                Ok(())
            }
            Err(error) => Err(error.into()),
        }
    })();
    let cleanup = fs::remove_file(&stage);
    published?;
    cleanup?;
    sync_parent(path)?;
    Ok(())
}

fn sync_parent(path: &Path) -> std::io::Result<()> {
    sync_directory(
        path.parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new(".")),
    )
}
