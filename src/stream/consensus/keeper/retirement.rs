//! Offline retirement of the enrollment that owns a lost voter.

use std::{
    fs::File,
    io::{self, Read},
    path::Path,
};

use ::ring::signature;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use tokio_rustls::rustls::{
    SignatureScheme,
    client::verify_server_cert_signed_by_trust_anchor,
    crypto::ring,
    pki_types::{CertificateDer, UnixTime, pem::PemObject},
    server::ParsedCertificate,
};
use uuid::Uuid;

use super::{Config, invalid};
use crate::stream::{
    consensus::storage::Incarnations,
    transport::{Credentials, keeper_id},
    wire::KeeperId,
};

const PROOF_BYTES: u64 = 256 * 1024;
const PURPOSE: &[u8] = b"logkeeper:retire-keeper-for-recovery:v1\0";
const SCHEMES: &[SignatureScheme] = &[
    SignatureScheme::ED25519,
    SignatureScheme::ECDSA_NISTP256_SHA256,
    SignatureScheme::ECDSA_NISTP384_SHA384,
    SignatureScheme::RSA_PSS_SHA256,
    SignatureScheme::RSA_PSS_SHA384,
    SignatureScheme::RSA_PSS_SHA512,
];

/// The retired keeper's signed acknowledgement that its trusted enrollment
/// permanently rejects this incarnation at startup.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FenceProof {
    catalog: Uuid,
    keeper: Uuid,
    incarnation: Uuid,
    chain: Vec<Vec<u8>>,
    scheme: u16,
    signature: Vec<u8>,
}

impl FenceProof {
    pub fn read(path: &Path) -> io::Result<Self> {
        let mut bytes = Vec::new();
        File::open(path)?
            .take(PROOF_BYTES + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() as u64 > PROOF_BYTES {
            return Err(invalid("retirement proof exceeds the size limit"));
        }
        Ok(serde_json::from_slice(&bytes)?)
    }

    fn statement(&self) -> Vec<u8> {
        [
            PURPOSE,
            self.catalog.as_bytes(),
            self.keeper.as_bytes(),
            self.incarnation.as_bytes(),
        ]
        .concat()
    }

    fn verify(&self, credentials: &Credentials) -> io::Result<()> {
        let (leaf, intermediates) = self
            .chain
            .split_first()
            .ok_or_else(|| invalid("retirement proof has no certificate"))?;
        let leaf = CertificateDer::from(leaf.as_slice());
        if keeper_id(&leaf)? != KeeperId(self.keeper.as_u128()) {
            return Err(invalid(
                "retirement proof certificate belongs to another keeper",
            ));
        }
        let intermediates = intermediates
            .iter()
            .map(|der| CertificateDer::from(der.as_slice()))
            .collect::<Vec<_>>();
        let parsed = ParsedCertificate::try_from(&leaf).map_err(io::Error::other)?;
        verify_server_cert_signed_by_trust_anchor(
            &parsed,
            &credentials.root_store()?,
            &intermediates,
            UnixTime::now(),
            ring::default_provider()
                .signature_verification_algorithms
                .all,
        )
        .map_err(io::Error::other)?;
        let (_, certificate) = x509_parser::parse_x509_certificate(leaf.as_ref())
            .map_err(|_| invalid("invalid retirement proof certificate"))?;
        let public_key = &certificate.public_key().subject_public_key;
        let algorithm: &dyn signature::VerificationAlgorithm =
            match SignatureScheme::from(self.scheme) {
                SignatureScheme::ED25519 => &signature::ED25519,
                SignatureScheme::ECDSA_NISTP256_SHA256 => &signature::ECDSA_P256_SHA256_ASN1,
                SignatureScheme::ECDSA_NISTP384_SHA384 => &signature::ECDSA_P384_SHA384_ASN1,
                SignatureScheme::RSA_PSS_SHA256 => &signature::RSA_PSS_2048_8192_SHA256,
                SignatureScheme::RSA_PSS_SHA384 => &signature::RSA_PSS_2048_8192_SHA384,
                SignatureScheme::RSA_PSS_SHA512 => &signature::RSA_PSS_2048_8192_SHA512,
                _ => return Err(invalid("unsupported retirement proof signature scheme")),
            };
        signature::UnparsedPublicKey::new(algorithm, public_key.data.as_ref())
            .verify(&self.statement(), &self.signature)
            .map_err(|_| invalid("invalid retirement proof signature"))
    }
}

impl Config {
    /// Permanently retires this stopped keeper for operator recovery. The
    /// caller supplies the expected identity and must account for every group
    /// hosted by the keeper before taking it offline.
    pub fn fence_recovery(&self, expected: Uuid) -> io::Result<FenceProof> {
        self.validate()?;
        if self.keeper != expected {
            return Err(invalid(
                "the confirmed keeper does not match the local configuration",
            ));
        }
        if self.keeper == self.catalog && self.catalog_voters.is_none() {
            return Err(invalid("cannot retire the sole catalog keeper"));
        }
        let pem = std::fs::read(&self.tls.certificate)?;
        let certificate_digest = Sha256::digest(&pem).into();
        let chain = CertificateDer::pem_slice_iter(&pem)
            .map(|cert| cert.map(|cert| cert.to_vec()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(io::Error::other)?;
        let signing_key =
            ring::sign::any_supported_type(&self.tls.key()?).map_err(io::Error::other)?;
        let signer = signing_key
            .choose_scheme(SCHEMES)
            .ok_or_else(|| invalid("unsupported keeper key for retirement proof"))?;
        self.enrollment_with_certificate_digest(certificate_digest)?
            .retire(|incarnation| {
                let mut proof = FenceProof {
                    catalog: self.catalog,
                    keeper: self.keeper,
                    incarnation,
                    chain,
                    scheme: signer.scheme().into(),
                    signature: Vec::new(),
                };
                proof.signature = signer.sign(&proof.statement()).map_err(io::Error::other)?;
                proof.verify(&self.tls)?;
                if serde_json::to_vec(&proof)?.len() as u64 > PROOF_BYTES {
                    return Err(invalid("retirement proof exceeds the size limit"));
                }
                Ok(proof)
            })
    }

    pub(super) fn verify_recovery_fences(
        &self,
        others: [Uuid; 2],
        proofs: &[FenceProof],
    ) -> io::Result<()> {
        let [first, second] = proofs else {
            return Err(invalid(
                "refused: supply two independently signed keeper retirement proofs with --fence-proof",
            ));
        };
        let mut proven = [first.keeper, second.keeper];
        proven.sort_unstable();
        if proven != others {
            return Err(invalid("retirement proofs must name the two lost voters"));
        }
        let known = Incarnations::load(&Incarnations::path(&self.enrollment, self.keeper))?;
        if known.reused {
            return Err(invalid(
                "a reused survivor identity cannot recover a stream",
            ));
        }
        for proof in proofs {
            if proof.catalog != self.catalog {
                return Err(invalid(
                    "retirement proof belongs to another keeper cluster",
                ));
            }
            if known.reincarnated.contains(&proof.keeper)
                || known.peers.get(&proof.keeper) != Some(&proof.incarnation)
            {
                return Err(invalid(format!(
                    "no unique matching media incarnation recorded for retired keeper {}",
                    proof.keeper,
                )));
            }
            proof.verify(&self.tls)?;
        }
        Ok(())
    }
}
