"""Representation mappings used by the translator.

Types and fields refer to Lean carriers. Equivalences.lean proves how those
carriers relate to the independently stated reference.
"""

from translate import BOOL, BYTE, INT, NAT, U64, ty


FINGERPRINT = ty("Array", BYTE, ty("32"))
BALLOT = ty("Ballot")


SHAPES = {
    "Ballot": ("Ballot", (), {
        "round": ("round", U64), "nonce": ("nonce", ty("u128")),
    }),
    "VoterState": ("VoterState", (), {
        "promised": ("promised", ty("Option", BALLOT)),
        "accepted": ("accepted", ty("Option", ty("tuple", BALLOT, U64))),
    }),
    "ReceiptKeys": ("ReceiptKeys", (), {
        "active": ("active", ty("Map", ty("u128"), FINGERPRINT)),
        "predecessor": ("predecessor", ty("Seq", FINGERPRINT)),
        "retained": ("retained", ty("Seq", FINGERPRINT)),
    }),
    "VoterSlots": ("VoterSlots", (), {
        "voter": ("voter", ty("u128")), "slots": ("slots", ty("SlotPair")),
    }),
    "Vote": ("Vote", (), {
        "voter": ("voter", ty("u128")), "ballot": ("ballot", BALLOT),
        "digest": ("digest", FINGERPRINT), "slots": ("slots", ty("SlotPair")),
        "read_back": ("readBack", BOOL),
    }),
    "SlotPair": ("SlotPair", (), {
        "selected": ("selected", BYTE), "images": ("images", ty("Array", ty("SlotImage"), ty("2"))),
    }),
    "SlotImage": ("SlotImage", (), {
        "generation": ("generation", U64), "digest": ("digest", FINGERPRINT),
    }),
    "ReadInterval": ("ReadInterval", (), {
        "empty": ("empty", BOOL), "floor": ("floor", U64), "from": ("first", U64),
        "through": ("through", U64), "retained": ("retained", ty("usize")),
    }),
    "CheckpointAccess": ("CheckpointAccess", (), {
        "cut": ("cut", U64), "erasure_floor": ("erasureFloor", U64),
        "retained": ("retained", BOOL), "closed": ("closed", BOOL),
    }),
    "Cut": ("Cut", (), {
        "next_lsn": ("nextLsn", U64), "history": ("history", ty("Array", BYTE, ty("32"))),
    }),
    "RetainedOutcome": ("ReceiptRow", ("R",), {
        "fingerprint": ("fingerprint", ty("Array", BYTE, ty("32"))), "receipt": ("original", ty("R")),
    }),
}


def camel_case(name):
    first, *rest = name.split("_")
    return first + "".join(part.capitalize() for part in rest)


# Expose the reference's Nat-coded key order in the Rust mathematical Int fields.
REDUCER_COORDINATES = ("position", "time", "epoch", "generation", "enrollment_serial", "lease_duration")
REDUCER_COUNTS = (
    "roster_limit", "old_root_limit", "ordinary_hold_limit", "activation_hold_limit",
    "retry_horizon", "lease_limit", "root_reference_limit", "fence_limit",
    "ordinary_holds", "activation_holds", "object_control_used", "object_control_capacity",
)
REDUCER_KEY_LISTS = (
    "roster_keys", "old_root_keys", "hold_keys", "receipt_keys", "lease_keys",
    "root_reference_keys", "fence_keys",
)
SHAPES["ReducerImage"] = ("Logkeeper.CompactImage.ReducerImage", (), {
    **{name: (camel_case(name), U64) for name in REDUCER_COORDINATES},
    **{name: (camel_case(name), NAT) for name in REDUCER_COUNTS},
    **{name: (camel_case(name), ty("Seq", INT), "intKeys") for name in REDUCER_KEY_LISTS},
    "current_grant": ("currentGrant", ty("Option", ty("tuple", U64, U64, BOOL))),
    "hold_receipts": ("holdReceipts", ty("Seq", ty("tuple", U64, ty("Option", U64)))),
    "receipt_positions": ("receiptPositions", ty("Seq", U64)),
    "leases": ("leases", ty("Seq", ty("tuple", U64, U64, BOOL))),
    "known_root_references": ("knownRootReferences", ty("Seq", BOOL)),
    "fences": ("fences", ty("Seq", ty("tuple", U64, U64))),
    "complete_references": ("completeReferences", BOOL),
    "withdrawal_receipts_match": ("withdrawalReceiptsMatch", BOOL),
    "references": ("references", ty("Seq", ty("Seq", INT)), "intReferences"),
})


ENUMS = {
    "ReplaceDecision": ("Logkeeper.StreamReplacement.ReplaceDecision", (), {
        "Fenced": (".fenced", ()), "NotSynced": (".notSynced", ()),
        "Replaced": (".replaced", ()), "WrongEnsemble": (".wrongEnsemble", ()),
        "Unauthorized": (".unauthorized", ()), "Persist": (".persist", ()),
    }),
    "ResponseKind": ("Logkeeper.VoterTransport.ResponseKind", (), {
        "Expected": (".expected", ()), "Deposed": (".deposed", ()),
        "Rejected": (".rejected", ()), "Invalid": (".invalid", ()),
    }),
    "AbstractAuthority": ("AbstractAuthority", ("G",), {
        "Active": (".active", (ty("G"),)), "Vacant": (".vacant", (ty("G"),)),
    }),
    "AppendClass": ("Logkeeper.Protocol.ChargeClass", (), {
        "Data": (".ordinary", ()), "Maintenance": (".maintenance", ()),
    }),
    "Comparison": ("Ordering", (), {
        "Less": (".lt", ()), "Equal": (".eq", ()), "Greater": (".gt", ()),
    }),
}
