"""Project the guarded, synchronous publication calls from the keeper's WAL."""

import re


WAL = "src/stream/keeper/wal.rs"
CHECKPOINT = "src/stream/keeper/checkpoint.rs"


def function(source, declaration):
    indent = re.match(r" *", declaration)[0]
    match = re.search(rf"^{re.escape(declaration)}[^\n]*\n(.*?)^{indent}\}}$", source, re.M | re.S)
    if match is None:
        raise ValueError(f"stream WAL projection: missing {declaration}")
    return match[1]


def calls(body, actions):
    """Preserve the source order of the fallible statements at this call site."""
    found = []
    for call, events in actions:
        positions = list(re.finditer(rf"^ +{re.escape(call)}(?:\?;)?$", body, re.M))
        if len(positions) != 1:
            raise ValueError(f"stream WAL projection: expected one call to {call}")
        found.append((positions[0].start(), events))
    return [event for _, events in sorted(found) for event in events]


def publication_events(read):
    wal = read(WAL)
    checkpoint = read(CHECKPOINT)
    segment = calls(function(wal, "fn new_segment("), [
        ("sync_file(&file)?;", ["syncSegmentFile"]),
        ("sync_directory(dir)?;", ["nameSegment"]),
    ])
    calls(function(wal, "    fn open_next_segment("), [
        ("(self.file, self.bytes) = new_segment(&self.segments, next, continuation)?;", []),
    ])
    pack_sync = function(checkpoint, "    fn sync(")
    calls(pack_sync, [("file.flush()?;", [])])
    pack = calls(pack_sync, [
        ("sync_file(file.get_ref())?;", ["syncPackFile"]),
        ("sync_directory(root)?;", ["syncPackDirectory"]),
    ])
    atomic_file = function(wal, "pub(super) fn atomic_file(")
    calls(atomic_file, [("write(&mut file)?;", []), ("file.flush()?;", [])])
    index = calls(atomic_file, [
        ("sync_file(file.get_ref())?;", ["syncIndexFile"]),
        ("fs::rename(temporary, path)?;", ["renameIndex"]),
        ('sync_directory(path.parent().expect("file has parent"))', ["syncIndexDirectory"]),
    ])
    write = function(checkpoint, "    pub fn write(")
    calls(write, [("})?;", [])])
    checkpoint_write = calls(write, [
        ("pack.sync(root)?;", pack),
        ('atomic_file(&root.join("INDEX"), |file| {', index),
        ("self.retire_packs(root)", ["retireFiles"]),
    ])
    return calls(function(wal, "    pub fn start_rotation("), [
        ("self.open_next_segment(false)?", segment),
        ("index.write(&root, next, snapshots, rewrite)?;", checkpoint_write),
        ("retire_segments(&segment_dir, next)?;", ["retireFiles"]),
    ])


def generated_publication(read):
    events = ", ".join(f".{event}" for event in publication_events(read))
    return f"""
namespace stream_wal

def publication : List Logkeeper.StreamWAL.PublishEvent := [{events}]

end stream_wal
"""
