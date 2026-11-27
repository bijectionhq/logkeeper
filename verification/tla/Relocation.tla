----------------------------- MODULE Relocation -----------------------------
EXTENDS Naturals

CONSTANTS KeepCheckpointPin, RewriteSnapshotPages, KeepParkPins, AtomicMoveHold,
          WatermarkFirst

Old == "source"
New == "destination"
None == "none"
Index == "index-page"

VARIABLES wal, image, blocks, replica, parkedOnce, crashed

vars == <<wal, image, blocks, replica, parkedOnce, crashed>>

Init ==
    /\ \E pending \in {None, Old}:
        wal = [inflight |-> "idle", live |-> Old, selected |-> Old, pending |-> pending]
    /\ image = [selected |-> Old, building |-> FALSE, pages |-> Old, rebuild |-> FALSE,
                moved |-> FALSE]
    /\ blocks = {Old, Index}
    /\ replica = [mode |-> "open", mark |-> {}]
    /\ parkedOnce = FALSE /\ crashed = FALSE

Running == replica.mode # "down"
Open == replica.mode = "open"
Parked == replica.mode = "parked"

StageMove ==
    /\ Open /\ wal.inflight = "idle" /\ wal.live = Old
    /\ wal' = [wal EXCEPT !.inflight = "staged"]
    /\ UNCHANGED <<image, blocks, replica, parkedOnce, crashed>>

SyncMove ==
    /\ Running /\ wal.inflight = "staged"
    /\ wal' = [wal EXCEPT !.inflight = "durable"]
    /\ blocks' = blocks \cup {New}
    /\ UNCHANGED <<image, replica, parkedOnce, crashed>>

(* Replay ignores Relocate. The runtime pointer may switch only after the
   WAL boundary. The old Arc is still held until both retirement holds
   have been installed. With AtomicMoveHold (Objects::relocate with
   `hold`), the move hold is registered under the same table lock as the
   swap, so no park pin observes the slice at its copy without the hold. *)
SwapSlice ==
    /\ Running /\ wal.inflight = "durable"
    /\ wal' = [wal EXCEPT !.live = New,
                          !.inflight = IF AtomicMoveHold THEN "registered" ELSE "swapped"]
    /\ image' = IF AtomicMoveHold THEN [image EXCEPT !.moved = image.selected = Old] ELSE image
    /\ UNCHANGED <<blocks, replica, parkedOnce, crashed>>

RegisterMove ==
    /\ Running /\ wal.inflight = "swapped"
    /\ wal' = [wal EXCEPT !.inflight = "registered"]
    /\ image' = [image EXCEPT !.moved = image.selected = Old]
    /\ UNCHANGED <<blocks, replica, parkedOnce, crashed>>

CaptureCheckpoint ==
    /\ Running /\ wal.inflight = "registered"
    /\ wal.pending = None /\ wal.selected # wal.live
    /\ wal' = [wal EXCEPT !.pending = wal.live]
    /\ UNCHANGED <<image, blocks, replica, parkedOnce, crashed>>

PublishCheckpoint ==
    /\ Running /\ wal.pending # None
    /\ wal' = [wal EXCEPT !.selected = wal.pending, !.pending = None]
    /\ UNCHANGED <<image, blocks, replica, parkedOnce, crashed>>

(* Read the move watermark before constructing pages
   (SnapshotBuilder::build_snapshot reads Objects::last_move first). A
   build that started before relocation can still select an old page, but
   cannot clear the later move's hold. The pages are fixed when the build
   starts; with RewriteSnapshotPages a rebuild writes every page again at
   the slice's current location, otherwise it reuses the selected pages.
   Without WatermarkFirst the watermark is read at selection. *)
BeginSnapshot ==
    /\ Open /\ ~image.building /\ image.selected = Old
    /\ image' = [image EXCEPT !.building = TRUE, !.rebuild = image.moved,
                    !.pages = IF image.moved /\ ~RewriteSnapshotPages
                              THEN image.selected ELSE wal.live]
    /\ UNCHANGED <<wal, blocks, replica, parkedOnce, crashed>>

SelectSnapshot ==
    /\ Open /\ image.building
    /\ LET release == IF WatermarkFirst THEN image.rebuild ELSE image.moved
       IN image' = [image EXCEPT !.building = FALSE, !.selected = image.pages,
                       !.moved = IF release THEN FALSE ELSE @]
    /\ UNCHANGED <<wal, blocks, replica, parkedOnce, crashed>>

(* Closing waits for snapshot selection. The state machine then contributes
   its current extent and scope hold, and the durable park mark also names
   the old locations held by relocation. *)
Park ==
    /\ Open /\ ~image.building /\ ~parkedOnce
    /\ replica' = [mode |-> "parked", mark |->
         IF KeepParkPins
         THEN {wal.live, Index} \cup (IF image.moved THEN {Old} ELSE {})
         ELSE {}]
    /\ parkedOnce' = TRUE
    /\ UNCHANGED <<wal, image, blocks, crashed>>

Wake ==
    /\ Parked /\ {image.selected, Index} \subseteq blocks
    /\ replica' = [mode |-> "open", mark |-> {}]
    /\ image' = [image EXCEPT !.moved = image.selected # wal.live]
    /\ UNCHANGED <<wal, blocks, parkedOnce, crashed>>

Crash ==
    /\ Running /\ ~crashed
    /\ replica' = [replica EXCEPT !.mode = "down"]
    /\ wal' = [wal EXCEPT !.inflight = "idle", !.pending = None, !.live = wal.selected]
    /\ image' = [image EXCEPT !.building = FALSE, !.rebuild = FALSE, !.moved = FALSE]
    /\ crashed' = TRUE
    /\ UNCHANGED <<blocks, parkedOnce>>

Restore ==
    /\ ~Running
    /\ replica' = [replica EXCEPT !.mode = IF parkedOnce /\ replica.mark # {} THEN "parked" ELSE "open"]
    /\ image' = [image EXCEPT !.moved = replica.mark = {} /\ image.selected # wal.live]
    /\ UNCHANGED <<wal, blocks, parkedOnce, crashed>>

RuntimePins ==
    {wal.live}
    \cup (IF KeepCheckpointPin THEN {wal.selected, wal.pending} ELSE {})
    \cup (IF image.moved \/ wal.inflight = "swapped" THEN {Old} ELSE {})
    \cup (IF Open THEN {Index} ELSE replica.mark)

Reap(b) ==
    /\ Running /\ b \in blocks \ RuntimePins
    /\ b # New
    /\ blocks' = blocks \ {b}
    /\ UNCHANGED <<wal, image, replica, parkedOnce, crashed>>

Next ==
    \/ StageMove \/ SyncMove \/ SwapSlice \/ RegisterMove \/ CaptureCheckpoint
    \/ PublishCheckpoint \/ BeginSnapshot \/ SelectSnapshot \/ Park \/ Wake
    \/ Crash \/ Restore \/ Reap(Old) \/ Reap(Index)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(StageMove) /\ WF_vars(SyncMove) /\ WF_vars(SwapSlice) /\ WF_vars(RegisterMove)
    /\ WF_vars(CaptureCheckpoint) /\ WF_vars(PublishCheckpoint)
    /\ WF_vars(BeginSnapshot) /\ WF_vars(SelectSnapshot)
    /\ WF_vars(Wake) /\ WF_vars(Restore) /\ WF_vars(Reap(Old))

RootsReadable ==
    /\ {wal.selected, image.selected, Index} \subseteq blocks
    /\ wal.pending = None \/ wal.pending \in blocks
    /\ Running => wal.live \in blocks
ParkCanReopenAfterRestart == Parked /\ crashed => {image.selected, Index} \subseteq blocks

ReclaimsSource == <>(Old \notin blocks)

=============================================================================
