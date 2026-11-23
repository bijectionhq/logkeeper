pub use crate::contracts::{Input, invalid, verify_bytes};

#[path = "../../../src/ordered/daemon/receipt_keys.rs"]
pub mod receipt_keys;
#[path = "../../../src/ordered/daemon/repair/authentication.rs"]
pub mod repair;
#[path = "../../../src/ordered/service/wire/receipt.rs"]
pub mod receipt;
#[path = "../../../src/ordered/codec/signed.rs"]
pub mod signed;
#[path = "../../../src/ordered/daemon/sign/verification.rs"]
pub mod verification;

// Rotation receipt / evidence payload codecs belong to the decision codec.
mod service {
    pub use crate::contracts::receipt;
}
