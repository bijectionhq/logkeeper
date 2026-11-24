import Logkeeper.StreamAsync

/-! # The shipped stream journal as an I/O automaton

Three keepers, a lossy network and any number of writers, one per epoch. Every keeper
effect is a Study 119 `Step` under the ghost writer, every other action leaves the keepers
unchanged, and the ghost writer only grows. Reply packets carry the durable evidence that
produced them. From these invariants every reachable state yields a Study 119
`Execution`, so the contract theorems hold for every execution. -/

namespace Logkeeper.StreamIO

open PrefixAgreement StreamJournal

set_option warningAsError true
set_option autoImplicit false

variable {Payload : Type}

/-! ## A growing ghost writer -/

/-- Rounds are fixed once chosen, issued histories only extend, advertised cuts persist. -/
structure Grows (w w' : Writer Payload) : Prop where
  round : ∀ e r, w.round e = some r → w'.round e = some r
  issued : ∀ e, w.issued e <+: w'.issued e
  advertised : ∀ h, w.advertised h → w'.advertised h

theorem Grows.refl (w : Writer Payload) : Grows w w :=
  ⟨fun _ _ h => h, fun _ => List.prefix_rfl, fun _ h => h⟩

theorem Grows.trans {a b c : Writer Payload} (ab : Grows a b) (bc : Grows b c) : Grows a c :=
  ⟨fun e r h => bc.round e r (ab.round e r h), fun e => (ab.issued e).trans (bc.issued e),
    fun h x => bc.advertised h (ab.advertised h x)⟩

theorem Grows.owns {w w' : Writer Payload} (grows : Grows w w') {k : Keeper Payload} {e : Nat}
    (owns : w.owns k e) : w'.owns k e :=
  let ⟨r, round, identity⟩ := owns
  ⟨r, grows.round e r round, identity⟩

theorem Grows.seed {w w' : Writer Payload} (grows : Grows w w') {k : Keeper Payload} {e : Nat}
    (owns : w.owns k e) : w'.seed e = w.seed e := by
  obtain ⟨r, round, _⟩ := owns
  simp [Writer.seed, round, grows.round e r round]

theorem Grows.take {w w' : Writer Payload} (grows : Grows w w') {e n : Nat}
    (within : n ≤ (w.issued e).length) : (w'.issued e).take n = (w.issued e).take n :=
  (take_of_prefix (grows.issued e) within).symm

theorem step_mono {w w' : Writer Payload} (grows : Grows w w') {k k' : Keeper Payload}
    (step : Step w k k') : Step w' k k' := by
  cases step with
  | create fresh => exact .create fresh
  | sealKeeper live allowed => exact .sealKeeper live allowed
  | syncPart live promised owns awaiting admitted =>
      rw [← grows.seed owns]
      exact .syncPart live promised (grows.owns owns) awaiting admitted
  | sync live promised owns admitted image same issued raises within covered advertised =>
      have seed := grows.seed owns
      rw [← seed]
      exact .sync live promised (grows.owns owns) admitted (seed ▸ image)
        (seed ▸ same) (seed ▸ issued.trans (grows.issued _)) raises (seed ▸ within) covered
        (seed ▸ grows.advertised _ advertised)
  | @installFloor epoch head live admitted owns floor seed history within advertised =>
      have long : max k.tail head ≤ (w.issued epoch).length :=
        Nat.max_le_of_le_of_le history.length_le within
      rw [← grows.take long]
      refine .installFloor live admitted (grows.owns owns) floor ((grows.seed owns).symm ▸ seed)
        (history.trans (grows.issued _)) (Nat.le_trans within (grows.issued _).length_le) ?_
      rw [grows.take within]
      exact grows.advertised _ advertised
  | append live admitted owns nonempty seed issued bounded advertised =>
      exact .append live admitted (grows.owns owns) nonempty ((grows.seed owns).symm ▸ seed)
        (issued.trans (grows.issued _)) bounded (grows.advertised _ advertised)
  | publish live admitted owns bounded advertised =>
      exact .publish live admitted (grows.owns owns) bounded (grows.advertised _ advertised)
  | trim live owns admitted => exact .trim live (grows.owns owns) admitted
  | check live => exact .check live
  | read live => exact .read live
  | delete => exact .delete

theorem reachable_mono {w w' : Writer Payload} (grows : Grows w w') {k : Keeper Payload}
    (reached : Reachable w k) : Reachable w' k := by
  induction reached with
  | initial => exact .initial
  | extend _ step prior => exact .extend prior (step_mono grows step)


/-! ## Requests, keeper effects and replies

A request is named by the keeper decision it reaches. The trace replay checks that the
shipped keeper reaches the same decision: an incomplete Sync stages, a complete Sync
installs, the empty Sync at `head + 1` installs a floor, and an Append either extends
the tail or publishes. -/

inductive Request (Payload : Type) where
  | create
  | promise (epoch : Nat)
  | stage (epoch floor start : Nat) (records : History Payload)
  | sync (epoch floor start : Nat) (records : History Payload) (head : Nat)
  | installFloor (epoch head : Nat)
  | append (epoch position : Nat) (payloads : List Payload) (head : Nat)
  | publish (epoch head : Nat)
  | trim (epoch through : Nat)
  | observe
  | delete

def SealMatches (sameOwner : Bool) (stored requested : Nat) : Prop :=
  sameOwner = true ∧ stored = requested

def EpochRunValid (epoch promised first last next tail : Nat) : Prop :=
  first = next ∧ first ≤ last ∧ last ≤ tail ∧ epoch ≤ promised

def RecordCharge (len : Nat) : Nat := max 1 len

def SyncHeadAdmitted (current head tail floor : Nat) : Prop :=
  current ≤ head ∧ head ≤ tail ∧ 0 < floor ∧ floor ≤ head + 1

instance (current head tail floor : Nat) : Decidable (SyncHeadAdmitted current head tail floor) :=
  inferInstanceAs (Decidable (current ≤ head ∧ head ≤ tail ∧ 0 < floor ∧ floor ≤ head + 1))

/-- The keeper's own admission rule for a request from `caller`. -/
def Admitted (k : Keeper Payload) (caller : Nat) : Request Payload → Prop
  | .create => k.deleted = false
  | .promise e => k.live ∧ SealAllowed k e caller
  | .stage e floor start _ => k.live ∧ k.promised = e ∧ k.identity = caller ∧ k.synced ≠ e ∧
      SyncAdmitted k floor start
  | .sync e floor start records head => k.live ∧ k.promised = e ∧ k.identity = caller ∧
      k.synced ≠ e ∧ SyncAdmitted k floor start ∧
      SyncHeadAdmitted k.head head (start - 1 + records.length) (k.syncFloor floor)
  | .installFloor e head => k.live ∧ MayAppend k e ∧ k.identity = caller ∧ k.floor ≤ head
  | .append e position payloads head => k.live ∧ MayAppend k e ∧ k.identity = caller ∧
      position = k.tail + 1 ∧ payloads ≠ [] ∧ head ≤ k.tail + payloads.length
  | .publish e head => k.live ∧ MayAppend k e ∧ k.identity = caller ∧ head ≤ k.tail
  | .trim e through => k.live ∧ k.identity = caller ∧ MayTrim k e through
  | .observe => k.live
  | .delete => True

theorem complete_sync_head_within_request {k : Keeper Payload}
    {caller epoch floor start head : Nat} {records : History Payload}
    (admitted : Admitted k caller (.sync epoch floor start records head)) :
    head ≤ start - 1 + records.length := by
  obtain ⟨_, _, _, _, _, bounds⟩ := admitted
  exact bounds.2.1

/-- The keeper's durable effect. The ghost writer supplies only the seed and issued history
    that ghost-fill positions the keeper skips over a trimmed prefix. -/
def effect (w : Writer Payload) (caller : Nat) (k : Keeper Payload) : Request Payload → Keeper Payload
  | .create => { k with created := true }
  | .promise e => sealKeeper k e caller
  | .stage e floor start records =>
      { k with staging := some (k.syncFloor floor, syncImage k (w.seed e) floor start records) }
  | .sync e floor start records head =>
      { accept k e (syncImage k (w.seed e) floor start records) with
        head, floor := max k.floor (k.syncFloor floor) }
  | .installFloor e head =>
      { accept k e ((w.issued e).take (max k.tail head)) with
        head := max k.head head, floor := head + 1 }
  | .append e _ payloads head =>
      { accept k e (k.history ++ stamp e payloads) with head := max k.head head }
  | .publish _ head => { k with head := max k.head head }
  | .trim _ through => { k with floor := max k.floor (through + 1) }
  | .observe => k
  | .delete => deleteKeeper k true

/-- Complete Sync builds from the incoming records. The writer's seed supplies
    only ghost records before a skipped prefix. -/
theorem complete_sync_uses_request_records (w : Writer Payload) (k : Keeper Payload)
    (caller epoch floor start head : Nat) (records : History Payload)
    (kept : start ≠ k.syncFloor floor) :
    (effect w caller k (.sync epoch floor start records head)).history =
      k.image.take (start - 1) ++ records := by
  change syncImage k (w.seed epoch) floor start records = _
  simp [syncImage, kept]

/-- A reply and the durable fact its effect established. -/
inductive Reply (Payload : Type) where
  /-- A Seal reply: the promise holder and the view the keeper reports. -/
  | sealed (epoch identity : Nat) (view : Vote (Record Payload))
  /-- A complete Sync or Append reply: the keeper's durable vote. -/
  | voted (epoch : Nat) (history : History Payload)
  | done

def reply (k : Keeper Payload) : Request Payload → Reply Payload
  | .promise e => .sealed e k.identity k.latest
  | .sync e .. | .installFloor e _ | .append e .. | .publish e _ => .voted e k.history
  | _ => .done

inductive Packet (Payload : Type) where
  | call (keeper : KeeperId) (identity : Nat) (request : Request Payload)
  | reply (keeper : KeeperId) (reply : Reply Payload)

/-- The keeper's image below `start` agrees with the seed. The writer establishes it by
    comparing epoch runs in a Seal reply. It stays true while the keeper is promised to the
    epoch and unsynced, because staging leaves the view unchanged. -/
def Agrees (k : Keeper Payload) (e : Nat) (seed : History Payload) (floor start : Nat) : Prop :=
  k.promised = e → k.synced ≠ e → start ≤ k.image.length + 1 → start ≠ k.syncFloor floor →
    k.image.take (start - 1) = seed.take (start - 1)

def Elected (w : Writer Payload) (e identity : Nat) : Prop :=
  ∃ r, w.round e = some r ∧ r.identity = identity

/-- What the writer guarantees about a request it sends to `keeper`. -/
def Sendable (w : Writer Payload) (k : Keeper Payload) (identity : Nat) : Request Payload → Prop
  | .create | .observe | .delete => True
  | .promise e => 0 < e
  | .stage e floor start records => Elected w e identity ∧ e ≤ k.promised ∧
      records <+: (w.seed e).drop (start - 1) ∧ Agrees k e (w.seed e) floor start
  | .sync e floor start records head => Elected w e identity ∧ e ≤ k.promised ∧
      records = (w.seed e).drop (start - 1) ∧ Agrees k e (w.seed e) floor start ∧
      head ≤ (w.seed e).length ∧ w.advertised ((w.seed e).take head)
  | .installFloor e head => Elected w e identity ∧ head ≤ (w.issued e).length ∧
      w.advertised ((w.issued e).take head)
  | .append e position payloads head => Elected w e identity ∧
      position - 1 + payloads.length ≤ (w.issued e).length ∧
      stamp e payloads = ((w.issued e).drop (position - 1)).take payloads.length ∧
      head ≤ (w.issued e).length ∧ w.advertised ((w.issued e).take head)
  | .publish e head => Elected w e identity ∧ head ≤ (w.issued e).length ∧
      w.advertised ((w.issued e).take head)
  | .trim e _ => Elected w e identity

/-! ## State and actions -/

inductive CapacityRefusal where
  | full
  | tooLarge
  deriving DecidableEq

/-- Capacity is checked only for a new append. A retained identical retry bypasses it. -/
def CapacityAt (k : Keeper Payload) (position : Nat) : Prop :=
  position = k.tail + 1

theorem capacity_refusal_excludes_retry {k : Keeper Payload} {position : Nat}
    (refused : CapacityAt k position) : k.tail < position := by
  unfold CapacityAt at refused
  omega

/-- The suffix still waiting for its first durable acceptance. A lost reply pins every
    position its request could still reach. Replies are scoped to one writer revision. -/
structure Pending (Payload : Type) where
  payloads : List Payload := []
  revision : Nat := 0
  uncertainThrough : Nat := 0
  refused : KeeperId → Option CapacityRefusal := fun _ => none

def Pending.reset (p : Pending Payload) (payloads : List Payload) : Pending Payload :=
  { p with payloads, revision := p.revision + 1, refused := fun _ => none }

structure State (Payload : Type) where
  keeper : KeeperId → Keeper Payload
  writer : Writer Payload
  net : List (Packet Payload)
  /-- The first Seal replies each election collects, with the promise holder. -/
  seals : Nat → KeeperId → Option (Nat × Vote (Record Payload))
  /-- The latest vote each writer's lane has received from each keeper. -/
  votes : Nat → KeeperId → Option (History Payload)
  pending : Nat → Pending Payload

def State.initial : State Payload :=
  ⟨fun _ => StreamJournal.initial, ⟨fun _ => none, fun _ => [], fun h => h = []⟩, [], fun _ _ => none,
    fun _ _ => none, fun _ => {}⟩

def update {α : Type} (f : KeeperId → α) (k : KeeperId) (value : α) : KeeperId → α :=
  fun j => if j = k then value else f j

/-- One action per await point or effect. Writers act only through `send`, the collection
    of replies, election, certification and issue. Crashes and cancellation remove no
    durable state: a crashed writer simply takes no further action and its packets remain. -/
inductive Action (Payload : Type) where
  | send (packet : Packet Payload)
  | deliver (packet : Packet Payload)
  | refuse (packet : Packet Payload)
  | drop
  | collectSeal (epoch : Nat) (keeper : KeeperId)
  | choose (epoch : Nat) (round : Round Payload)
  | collectVote (epoch : Nat) (keeper : KeeperId)
  | certify (epoch : Nat) (history : History Payload)
  | assign (epoch : Nat) (payloads : List Payload)
  | loseAppend (epoch count : Nat)
  | rejectCapacity (epoch : Nat) (keeper : KeeperId) (revision : Nat) (reason : CapacityRefusal)
  | discard (epoch : Nat)
  | issue (epoch : Nat) (payloads : List Payload)
  | restart (keeper : KeeperId)

def advertise (w : Writer Payload) (h : History Payload) : Writer Payload :=
  { w with advertised := fun x => w.advertised x ∨ x = h }

def elect (w : Writer Payload) (e : Nat) (r : Round Payload) : Writer Payload :=
  { w with round := fun x => if x = e then some r else w.round x,
           issued := fun x => if x = e then r.winner.history else w.issued x }

def extend (w : Writer Payload) (e : Nat) (payloads : List Payload) : Writer Payload :=
  { w with issued := fun x => if x = e then w.issued e ++ stamp e payloads else w.issued x }

/-- Appends can be dispatched from the assigned suffix before any keeper can
    durably accept it. The durable automaton only admits ordinary sends after
    the covering prefix has been issued. -/
def WireSendable (s : State Payload) (k : KeeperId) (caller : Nat) : Request Payload → Prop
  | .append epoch start payloads head =>
      Sendable (extend s.writer epoch (s.pending epoch).payloads) (s.keeper k) caller
        (.append epoch start payloads head) ∧ head ≤ (s.writer.issued epoch).length
  | request => Sendable s.writer (s.keeper k) caller request

def State.withSeal (s : State Payload) (e : Nat) (k : KeeperId) (report : Nat × Vote (Record Payload)) :
    State Payload :=
  { s with seals := fun x j => if x = e ∧ j = k then some report else s.seals x j }

def State.withVote (s : State Payload) (e : Nat) (k : KeeperId) (h : History Payload) :
    State Payload :=
  { s with votes := fun x j => if x = e ∧ j = k then some h else s.votes x j }

def State.withPending (s : State Payload) (e : Nat) (p : Pending Payload) : State Payload :=
  { s with pending := fun x => if x = e then p else s.pending x }

def State.apply (s : State Payload) (k : KeeperId) (i : Nat) (req : Request Payload) :
    State Payload :=
  let next := effect s.writer i (s.keeper k) req
  { s with keeper := update s.keeper k next, net := .reply k (reply next req) :: s.net }

inductive Next : State Payload → Action Payload → State Payload → Prop
  | send {s k i req} : Sendable s.writer (s.keeper k) i req →
      Next s (.send (.call k i req)) { s with net := .call k i req :: s.net }
  /-- The keeper's round: decide, make the effect durable, then reply. The packet stays in
      the network, so it can be delivered again. -/
  | deliver {s k i req} : .call k i req ∈ s.net → Admitted (s.keeper k) i req →
      Next s (.deliver (.call k i req)) (s.apply k i req)
  | refuse {s p} : p ∈ s.net → Next s (.refuse p) s
  | drop {s} {net : List (Packet Payload)} : net.Sublist s.net → Next s .drop { s with net }
  | collectSeal {s e k i v} : .reply k (.sealed e i v) ∈ s.net → s.writer.round e = none →
      Next s (.collectSeal e k) (s.withSeal e k (i, v))
  | choose {s e} {r : Round Payload} : 0 < e → s.writer.round e = none →
      s.seals e r.first = some (r.identity, r.report r.first) →
      s.seals e r.second = some (r.identity, r.report r.second) →
      Next s (.choose e r) { s with writer := elect s.writer e r }
  | collectVote {s e k h} : .reply k (.voted e h) ∈ s.net →
      Next s (.collectVote e k) (s.withVote e k h)
  /-- `decision::acknowledged`: two distinct lanes hold durable votes covering the cut. -/
  | certify {s e h} (a b : KeeperId) {ha hb : History Payload} : a ≠ b →
      s.votes e a = some ha → s.votes e b = some hb → h <+: ha → h <+: hb →
      Next s (.certify e h) { s with writer := advertise s.writer h }
  | assign {s e payloads} {r : Round Payload} : s.writer.round e = some r →
      Next s (.assign e payloads) (s.withPending e ((s.pending e).reset ((s.pending e).payloads ++ payloads)))
  /-- An unanswered pending Append can still have a durable effect. -/
  | loseAppend {s e count} : 0 < count → count ≤ (s.pending e).payloads.length →
      Next s (.loseAppend e count) (s.withPending e { s.pending e with
        uncertainThrough := max (s.pending e).uncertainThrough ((s.writer.issued e).length + count) })
  /-- A lane's completed capacity reply. The model compresses the request and collection
      of this definitive refusal. It supplies the capacity outcome as an input. -/
  | rejectCapacity {s e k revision reason caller payloads head} :
      revision = (s.pending e).revision → Elected s.writer e caller →
      payloads <+: (s.pending e).payloads →
      Admitted (s.keeper k) caller (.append e ((s.writer.issued e).length + 1) payloads head) →
      CapacityAt (s.keeper k) ((s.writer.issued e).length + 1) →
      Next s (.rejectCapacity e k revision reason) (s.withPending e { s.pending e with
        refused := update (s.pending e).refused k (some reason) })
  | discard {s e} : (s.pending e).payloads ≠ [] →
      (∀ k, (s.pending e).refused k ≠ none) →
      (s.pending e).uncertainThrough ≤ (s.writer.issued e).length →
      Next s (.discard e) (s.withPending e ((s.pending e).reset []))
  /-- Freeze the exact assigned prefix at the boundary of its first possible durable
      acceptance. Subsequent sends use the ordinary issued-history rule. -/
  | issue {s e payloads rest} {r : Round Payload} : s.writer.round e = some r →
      (s.pending e).payloads = payloads ++ rest →
      Next s (.issue e payloads)
        { s.withPending e ((s.pending e).reset rest) with writer := extend s.writer e payloads }
  /-- A keeper restart reopens its durable state; the trace replay checks the WAL image. -/
  | restart {s k} : Next s (.restart k) s

theorem discard_preserves_pending_evidence {s s' : State Payload} {e : Nat}
    (next : Next s (.discard e) s') :
    (∀ k, (s.pending e).refused k ≠ none) ∧
      (s.pending e).uncertainThrough ≤ (s.writer.issued e).length ∧
      s'.writer = s.writer ∧ (s'.pending e).payloads = [] := by
  cases next with
  | discard _ unanimous certain =>
      exact ⟨unanimous, certain, rfl, by simp [State.withPending, Pending.reset]⟩

/-! ## Keeper actions refine Study 119 -/

theorem latest_voted {w : Writer Payload} {k : Keeper Payload} (reached : StreamJournal.Reachable w k) :
    k.durable.votes k.latest := by
  induction reached with
  | initial => exact Or.inr rfl
  | @extend before after _ step ih =>
      cases step with
      | sealKeeper _ _ =>
          unfold sealKeeper
          split
          · exact ih
          · exact ih
      | sync => exact Or.inr rfl
      | installFloor => exact Or.inr rfl
      | append => exact Or.inr rfl
      | delete =>
          unfold deleteKeeper
          exact ih
      | _ => exact ih

theorem latest_eta (k : Keeper Payload) : k.latest = ⟨k.synced, k.history⟩ := rfl

/-- A synced keeper's history extends its epoch's seed and lies within the issued history. -/
theorem synced_history {w : Writer Payload} {k : Keeper Payload} (reached : StreamJournal.Reachable w k)
    (reserved : w.round 0 = none) (initiallyEmpty : w.issued 0 = []) {e : Nat} (synced : k.synced = e) :
    w.seed e <+: k.history ∧ k.history <+: w.issued e := by
  have follows := vote_follows_writer reached reserved initiallyEmpty (latest_voted reached)
  rw [latest_eta, synced] at follows
  exact follows.2

theorem take_of_issued {issued history : History Payload} (prefixed : history <+: issued) :
    history = issued.take history.length := by
  obtain ⟨rest, rfl⟩ := prefixed
  simp

/-- Every admitted request that the writer could send is a reference step or a stutter. -/
theorem deliver_refines {w : Writer Payload} {k : Keeper Payload} {i : Nat} {req : Request Payload}
    (reached : StreamJournal.Reachable w k) (reserved : w.round 0 = none)
    (initiallyEmpty : w.issued 0 = []) (seeded : ∀ e, w.seed e <+: w.issued e)
    (sendable : Sendable w k i req) (admitted : Admitted k i req) :
    Step w k (effect w i k req) ∨ effect w i k req = k := by
  cases req with
  | create => exact Or.inl (.create admitted)
  | promise e => exact Or.inl (.sealKeeper admitted.1 admitted.2)
  | stage e floor start records =>
      obtain ⟨live, promised, identity, awaiting, sync⟩ := admitted
      obtain ⟨⟨r, round, owner⟩, _, _, _⟩ := sendable
      exact Or.inl (.syncPart live promised ⟨r, round, owner.trans identity.symm⟩ awaiting sync)
  | sync e floor start records head =>
      obtain ⟨live, promised, identity, awaiting, sync, bounds⟩ := admitted
      obtain ⟨⟨r, round, owner⟩, _, exact, agrees, within, advertised⟩ := sendable
      have built : syncImage k (w.seed e) floor start records = w.seed e := by
        unfold syncImage
        rw [exact]
        split
        · exact List.take_append_drop _ _
        · rename_i kept
          rw [agrees promised awaiting (sync.2.2.2.2.resolve_right kept) kept]
          exact List.take_append_drop _ _
      refine Or.inl ?_
      simp only [effect, built]
      exact .sync (start := start) (records := records) live promised
        ⟨r, round, owner.trans identity.symm⟩ sync built (fun same => absurd same awaiting)
        (seeded e) bounds.1 within bounds.2.2.2 advertised
  | installFloor e head =>
      obtain ⟨live, synced, identity, floor⟩ := admitted
      obtain ⟨⟨r, round, owner⟩, within, advertised⟩ := sendable
      obtain ⟨seed, history⟩ := synced_history reached reserved initiallyEmpty synced.2
      exact Or.inl (.installFloor live synced ⟨r, round, owner.trans identity.symm⟩ floor seed history
        within advertised)
  | append e position payloads head =>
      obtain ⟨live, synced, identity, next, nonempty, bounded⟩ := admitted
      obtain ⟨⟨r, round, owner⟩, fits, exact, _, advertised⟩ := sendable
      obtain ⟨seed, history⟩ := synced_history reached reserved initiallyEmpty synced.2
      subst next
      have extended : k.history ++ stamp e payloads = (w.issued e).take (k.tail + payloads.length) := by
        have long : k.history.length ≤ (w.issued e).length := history.length_le
        conv => lhs; rw [take_of_issued history]
        simp only [Nat.add_sub_cancel] at exact
        rw [exact]
        simp only [Keeper.tail]
        exact List.take_add.symm
      refine Or.inl (.append live synced ⟨r, round, owner.trans identity.symm⟩ nonempty seed
        (extended ▸ List.take_prefix _ _) bounded ?_)
      rw [extended, List.take_take, Nat.min_eq_left bounded]
      exact advertised
  | publish e head =>
      obtain ⟨live, synced, identity, bounded⟩ := admitted
      obtain ⟨⟨r, round, owner⟩, _, advertised⟩ := sendable
      obtain ⟨_, history⟩ := synced_history reached reserved initiallyEmpty synced.2
      refine Or.inl (.publish live synced ⟨r, round, owner.trans identity.symm⟩ bounded ?_)
      rw [take_of_issued history, List.take_take]
      rw [Nat.min_eq_left (show head ≤ k.history.length from bounded)]
      exact advertised
  | trim e through =>
      obtain ⟨live, identity, allowed⟩ := admitted
      obtain ⟨r, round, owner⟩ := sendable
      exact Or.inl (.trim live ⟨r, round, owner.trans identity.symm⟩ allowed)
  | observe => exact Or.inr rfl
  | delete => exact Or.inl .delete

/-! ## Durable facts persist -/

theorem durable_step {w : Writer Payload} {k k' : Keeper Payload} (reached : StreamJournal.Reachable w k)
    (step : Step w k k') : DurableAcceptor.Step k.durable k'.durable :=
  keeper_step_refines_durable_acceptor
    (DurableAcceptor.reachable_replies_cover_every_lower_vote
      (reachable_keeper_refines_durable_acceptor reached)) step

theorem durable_promised_le {a b : DurableAcceptor.State (Record Payload)}
    (step : DurableAcceptor.Step a b) : a.promised ≤ b.promised := by
  cases step with
  | accept vote above _ => exact above
  | prepare _ newer => exact Nat.le_of_lt newer
  | restart => exact Nat.le_refl _

theorem promised_mono {w : Writer Payload} {k k' : Keeper Payload} (reached : StreamJournal.Reachable w k)
    (step : Step w k k') : k.promised ≤ k'.promised :=
  durable_promised_le (durable_step reached step)

theorem votes_persist_step {w : Writer Payload} {k k' : Keeper Payload} (reached : StreamJournal.Reachable w k)
    (step : Step w k k') {v : Vote (Record Payload)} (voted : k.durable.votes v) : k'.durable.votes v :=
  durable_step_preserves_vote (durable_step reached step) voted

theorem durable_replies_persist {a b : DurableAcceptor.State (Record Payload)}
    (sound : DurableAcceptor.Sound a) (step : DurableAcceptor.Step a b) {e : Nat}
    {x : Option (Vote (Record Payload))} (saved : a.replies e = some x) : b.replies e = some x := by
  have below := (sound.repliesSound e x saved).1
  cases step with
  | accept => exact saved
  | prepare ballot newer =>
      change (if e = ballot then some a.latest else a.replies e) = some x
      have differs : e ≠ ballot := by omega
      simpa [differs] using saved
  | restart => exact saved

theorem replies_persist_step {w : Writer Payload} {k k' : Keeper Payload} (reached : StreamJournal.Reachable w k)
    (step : Step w k k') {e : Nat} {x : Option (Vote (Record Payload))}
    (saved : k.durable.replies e = some x) : k'.durable.replies e = some x :=
  durable_replies_persist (DurableAcceptor.reachable_replies_cover_every_lower_vote
    (reachable_keeper_refines_durable_acceptor reached)) (durable_step reached step) saved

/-- Accepts set the promise to the vote's ballot, so a reference step that leaves a keeper
    promised to `e` and unsynced at `e` changed neither its visible history nor, unless it
    staged, its staging. -/
theorem quiet_step {w : Writer Payload} {k k' : Keeper Payload} (step : Step w k k') {e : Nat}
    (atLeast : e ≤ k.promised) (promised : k'.promised = e) (unsynced : k'.synced ≠ e) :
    k.promised = e ∧ k'.latest = k.latest ∧
      (k'.staging = k.staging ∨ ∃ staged, k'.staging = some staged) := by
  cases step with
  | @sealKeeper epoch identity _ allowed =>
      by_cases same : k.promised = epoch
      · have unchanged : sealKeeper k epoch identity = k := by simp [sealKeeper, same]
        rw [unchanged] at promised ⊢
        exact ⟨promised, rfl, Or.inl rfl⟩
      · have changed : (sealKeeper k epoch identity).promised = epoch := by
          have differs : ¬ k.durable.promised = epoch := same
          simp [sealKeeper, differs, Keeper.promised, DurableAcceptor.promise]
        rw [changed] at promised
        rcases allowed with higher | tied
        · omega
        · exact absurd tied.1 same
  | syncPart => exact ⟨promised, rfl, Or.inr ⟨_, rfl⟩⟩
  | sync => exact (unsynced promised).elim
  | installFloor => exact (unsynced promised).elim
  | append => exact (unsynced promised).elim
  | delete =>
      unfold deleteKeeper at promised ⊢
      exact ⟨promised, rfl, Or.inl rfl⟩
  | _ => exact ⟨promised, rfl, Or.inl rfl⟩

theorem latest_some {w : Writer Payload} {k : Keeper Payload} (reached : StreamJournal.Reachable w k) :
    k.durable.latest = some k.latest := by
  induction reached with
  | initial => rfl
  | @extend before after _ step ih =>
      cases step with
      | sealKeeper _ _ =>
          unfold sealKeeper
          split
          · exact ih
          · exact ih
      | delete =>
          unfold deleteKeeper
          exact ih
      | sync => rfl
      | installFloor => rfl
      | append => rfl
      | _ => exact ih

/-- A staged history and its agreement with the seed. -/
theorem staged_image_is_seed_prefix {k : Keeper Payload} {seed records : History Payload}
    {e floor start : Nat} (promised : k.promised = e) (unsynced : k.synced ≠ e)
    (agrees : Agrees k e seed floor start) (valid : SyncAdmitted k floor start)
    (slice : records <+: seed.drop (start - 1)) :
    syncImage k seed floor start records <+: seed := by
  have joined : seed.take (start - 1) ++ records <+: seed := by
    obtain ⟨rest, eq⟩ := slice
    exact ⟨rest, by rw [List.append_assoc, eq, List.take_append_drop]⟩
  unfold syncImage
  split
  · exact joined
  · rename_i kept
    rw [agrees promised unsynced (valid.2.2.2.2.resolve_right kept) kept]
    exact joined

/-- Agreement below `start` holds for any seed prefix. -/
theorem agrees_of_prefix {k : Keeper Payload} {e floor start : Nat} {seed : History Payload}
    (prefixed : k.image <+: seed) : Agrees k e seed floor start := by
  intro _ _ fits _
  exact take_of_prefix prefixed (by omega)

/-- An in-flight Sync's agreement survives every reference step of its keeper. -/
theorem agrees_persists {w : Writer Payload} {k k' : Keeper Payload} {e floor start : Nat}
    {seed : History Payload} (step : Step w k k' ∨ k' = k) (atLeast : e ≤ k.promised)
    (stagedPrefix : ∀ f img, k'.promised = e → k'.synced ≠ e → k'.staging = some (f, img) → img <+: seed)
    (agrees : Agrees k e seed floor start) : Agrees k' e seed floor start := by
  intro promised unsynced fits kept
  rcases step with step | rfl
  · cases staging : k'.staging with
    | some staged =>
        obtain ⟨f, img⟩ := staged
        have prefixed := stagedPrefix f img promised unsynced staging
        have image : k'.image = img := by simp [Keeper.image, staging]
        exact agrees_of_prefix (image ▸ prefixed) promised unsynced fits kept
    | none =>
        obtain ⟨before, latest, unchanged⟩ := quiet_step step atLeast promised unsynced
        have stays : k.staging = none := by
          rcases unchanged with same | ⟨_, staged⟩
          · exact same ▸ staging
          · simp [staging] at staged
        have history : k'.history = k.history := congrArg Vote.history latest
        have synced : k'.synced = k.synced := congrArg Vote.ballot latest
        have image : k'.image = k.image := by simp [Keeper.image, staging, stays, history]
        rw [image] at fits ⊢
        exact agrees before (synced ▸ unsynced) fits
          (by simpa [Keeper.syncFloor, staging, stays] using kept)
  · exact agrees promised unsynced fits kept

def StagedPrefix (w : Writer Payload) (k : Keeper Payload) : Prop :=
  ∀ e r f img, k.promised = e → w.round e = some r → k.synced ≠ e → k.staging = some (f, img) →
    img <+: w.seed e

/-- What the writer guaranteed when it sent a request still holds after a keeper step and
    writer growth. -/
theorem sendable_persists {w w' : Writer Payload} (grows : Grows w w') {k k' : Keeper Payload}
    (reached : StreamJournal.Reachable w k) (step : Step w k k' ∨ k' = k)
    (stagedPrefix : StagedPrefix w k') {i : Nat} {req : Request Payload}
    (sendable : Sendable w k i req) : Sendable w' k' i req := by
  have elected : ∀ {e}, Elected w e i → Elected w' e i ∧ w'.seed e = w.seed e := by
    intro e ⟨r, round, owner⟩
    refine ⟨⟨r, grows.round e r round, owner⟩, ?_⟩
    simp [Writer.seed, round, grows.round e r round]
  have promised : k.promised ≤ k'.promised := by
    rcases step with step | rfl
    · exact promised_mono reached step
    · exact Nat.le_refl _
  have prefixes : ∀ {e} {r : Round Payload}, w.round e = some r →
      ∀ f img, k'.promised = e → k'.synced ≠ e → k'.staging = some (f, img) → img <+: w.seed e :=
    fun round f img p u st => stagedPrefix _ _ f img p round u st
  have issued : ∀ {e n}, n ≤ (w.issued e).length → (w'.issued e).take n = (w.issued e).take n :=
    fun within => grows.take within
  cases req with
  | create | observe | delete | promise => exact sendable
  | stage e floor start records =>
      obtain ⟨own, atLeast, slice, agrees⟩ := sendable
      have ⟨r, round, _⟩ := own
      obtain ⟨own', seed⟩ := elected own
      show Elected w' e i ∧ e ≤ k'.promised ∧ records <+: (w'.seed e).drop (start - 1) ∧
        Agrees k' e (w'.seed e) floor start
      rw [seed]
      exact ⟨own', Nat.le_trans atLeast promised, slice,
        agrees_persists step atLeast (prefixes round) agrees⟩
  | sync e floor start records head =>
      obtain ⟨own, atLeast, exact, agrees, within, advertised⟩ := sendable
      have ⟨r, round, _⟩ := own
      obtain ⟨own', seed⟩ := elected own
      show Elected w' e i ∧ e ≤ k'.promised ∧ records = (w'.seed e).drop (start - 1) ∧
        Agrees k' e (w'.seed e) floor start ∧ head ≤ (w'.seed e).length ∧
        w'.advertised ((w'.seed e).take head)
      rw [seed]
      exact ⟨own', Nat.le_trans atLeast promised, exact,
        agrees_persists step atLeast (prefixes round) agrees, within, grows.advertised _ advertised⟩
  | installFloor e head =>
      obtain ⟨own, within, advertised⟩ := sendable
      exact ⟨(elected own).1, Nat.le_trans within (grows.issued e).length_le,
        (issued within).symm ▸ grows.advertised _ advertised⟩
  | append e position payloads head =>
      obtain ⟨own, fits, exact, within, advertised⟩ := sendable
      refine ⟨(elected own).1, Nat.le_trans fits (grows.issued e).length_le, ?_,
        Nat.le_trans within (grows.issued e).length_le,
        (issued within).symm ▸ grows.advertised _ advertised⟩
      rw [exact]
      obtain ⟨rest, eq⟩ := grows.issued e
      rw [← eq, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  | publish e head =>
      obtain ⟨own, within, advertised⟩ := sendable
      exact ⟨(elected own).1, Nat.le_trans within (grows.issued e).length_le,
        (issued within).symm ▸ grows.advertised _ advertised⟩
  | trim e through => exact (elected sendable).1

inductive Reachable : State Payload → Prop
  | initial : Reachable State.initial
  | extend {s a s'} : Reachable s → Next s a s' → Reachable s'


/-! ## The invariant -/

/-- The durable fact a reply witnesses at its keeper. -/
def ReplyInv (w : Writer Payload) (k : Keeper Payload) : Reply Payload → Prop
  | .sealed e _ v => w.round e = none → k.durable.replies e = some (some v)
  | .voted e h => k.durable.votes ⟨e, h⟩
  | .done => True

def PacketInv (s : State Payload) : Packet Payload → Prop
  | .call k i req => Sendable s.writer (s.keeper k) i req
  | .reply k r => ReplyInv s.writer (s.keeper k) r

def Quiet (w : Writer Payload) (k : Keeper Payload) : Prop :=
  ∀ e, 0 < e → k.promised = e → w.round e = none → k.durable.replies e = some (some k.latest)

def StagedElected (w : Writer Payload) (k : Keeper Payload) : Prop :=
  ∀ f img, k.staging = some (f, img) → ∃ r, w.round k.promised = some r

structure Inv (s : State Payload) : Prop where
  reached : ∀ k, StreamJournal.Reachable s.writer (s.keeper k)
  reserved : s.writer.round 0 = none
  unelected : ∀ e, s.writer.round e = none → s.writer.issued e = []
  seeded : ∀ e, s.writer.seed e <+: s.writer.issued e
  emptyAdvertised : s.writer.advertised []
  chosen : ∀ h, s.writer.advertised h → ∃ e, QuorumAccepted s.keeper e h
  captured : ∀ e r, s.writer.round e = some r → ∀ k, r.sealed k = true →
    (s.keeper k).durable.replies e = some (some (r.report k))
  seals : ∀ e k i v, s.seals e k = some (i, v) → (s.keeper k).durable.replies e = some (some v)
  votes : ∀ e k h, s.votes e k = some h → (s.keeper k).durable.votes ⟨e, h⟩
  /-- Before its election fixes a round, a promised keeper still reports its saved snapshot. -/
  quiet : ∀ k, Quiet s.writer (s.keeper k)
  /-- Staging exists only under an elected promise, and builds a prefix of the seed. -/
  stagedElected : ∀ k, StagedElected s.writer (s.keeper k)
  stagedPrefix : ∀ k, StagedPrefix s.writer (s.keeper k)
  packets : ∀ p ∈ s.net, PacketInv s p

theorem quorum_persists {keepers keepers' : KeeperId → Keeper Payload}
    (persist : ∀ k v, (keepers k).durable.votes v → (keepers' k).durable.votes v) {e : Nat}
    {h : History Payload} (accepted : QuorumAccepted keepers e h) : QuorumAccepted keepers' e h :=
  let ⟨ack, majority, held⟩ := accepted
  ⟨ack, majority, fun k member acked =>
    let ⟨history, voted, prefixed⟩ := held k member acked
    ⟨history, persist k _ voted, prefixed⟩⟩

theorem initial_inv : Inv (State.initial : State Payload) where
  reached _ := .initial
  reserved := rfl
  unelected _ _ := rfl
  seeded _ := List.nil_prefix
  emptyAdvertised := rfl
  chosen h advertised := by
    change h = [] at advertised
    subst h
    refine ⟨0, fun _ => true, by decide, fun k _ _ => ⟨[], Or.inr rfl, List.prefix_rfl⟩⟩
  captured _ _ elected := by simp [State.initial] at elected
  seals _ _ _ _ collected := by simp [State.initial] at collected
  votes _ _ _ collected := by simp [State.initial] at collected
  quiet _ e positive promised _ := by
    change 0 = e at promised
    omega
  stagedElected _ _ _ staged := by simp [State.initial, StreamJournal.initial] at staged
  stagedPrefix _ _ _ _ _ _ _ _ staged := by simp [State.initial, StreamJournal.initial] at staged
  packets _ inFlight := by simp [State.initial] at inFlight


/-- The keeper-local part of the invariant survives a delivered request, and its reply
    carries the evidence the writer relies on. -/
theorem deliver_local {w : Writer Payload} {K : Keeper Payload} {i : Nat} {req : Request Payload}
    (reached : StreamJournal.Reachable w K)
    (sendable : Sendable w K i req) (admitted : Admitted K i req) (quiet : Quiet w K)
    (stagedElected : StagedElected w K) (stagedPrefix : StagedPrefix w K) :
    Quiet w (effect w i K req) ∧ StagedElected w (effect w i K req) ∧
      StagedPrefix w (effect w i K req) := by
  have present := latest_some reached
  cases req with
  | promise e =>
      by_cases same : K.promised = e
      · have unchanged : effect w i K (.promise e) = K := by
          simp [effect, sealKeeper, same]
        rw [unchanged]
        exact ⟨quiet, stagedElected, stagedPrefix⟩
      · have fresh : effect w i K (.promise e) =
            { K with durable := DurableAcceptor.promise K.durable e, identity := i, staging := none } := by
          simp [effect, sealKeeper, same]
        rw [fresh]
        refine ⟨?_, fun _ _ staged => by simp at staged, fun _ _ _ _ _ _ _ staged => by simp at staged⟩
        intro e' _ promised _
        change e = e' at promised
        subst promised
        change (if e = e then some K.durable.latest else K.durable.replies e) = _
        simp [present]
        rfl
  | stage e floor start records =>
      obtain ⟨_, promised, _, unsynced, valid⟩ := admitted
      obtain ⟨⟨r, round, _⟩, _, slice, agrees⟩ := sendable
      refine ⟨quiet, fun _ _ _ => ⟨r, promised ▸ round⟩, ?_⟩
      intro e' r' f img promised' _ _ staged
      change K.promised = e' at promised'
      change some (K.syncFloor floor, syncImage K (w.seed e) floor start records) = some (f, img) at staged
      have := (Prod.mk.inj (Option.some.inj staged)).2
      subst this
      have same : e = e' := promised.symm.trans promised'
      subst same
      exact staged_image_is_seed_prefix promised unsynced agrees valid slice
  | sync e =>
      obtain ⟨_, promised, _, _, _, _⟩ := admitted
      obtain ⟨⟨r, round, _⟩, _⟩ := sendable
      refine ⟨?_, fun _ _ staged => by simp [effect, accept] at staged,
        fun _ _ _ _ _ _ _ staged => by simp [effect, accept] at staged⟩
      intro e' _ promised' none
      change e = e' at promised'
      subst promised'
      simp [round] at none
  | installFloor e =>
      obtain ⟨_, synced, _, _⟩ := admitted
      obtain ⟨⟨r, round, _⟩, _⟩ := sendable
      refine ⟨?_, fun _ _ staged => by simp [effect, accept] at staged,
        fun _ _ _ _ _ _ _ staged => by simp [effect, accept] at staged⟩
      intro e' _ promised' none
      change e = e' at promised'
      subst promised'
      simp [round] at none
  | append e =>
      obtain ⟨_, synced, _, _⟩ := admitted
      obtain ⟨⟨r, round, _⟩, _⟩ := sendable
      refine ⟨?_, fun _ _ staged => by simp [effect, accept] at staged,
        fun _ _ _ _ _ _ _ staged => by simp [effect, accept] at staged⟩
      intro e' _ promised' none
      change e = e' at promised'
      subst promised'
      simp [round] at none
  | create | publish | trim | observe =>
      exact ⟨quiet, stagedElected, stagedPrefix⟩
  | delete =>
      simp only [effect, deleteKeeper]
      exact ⟨quiet, stagedElected, stagedPrefix⟩


/-- The reply to a delivered request witnesses a durable fact of the keeper's new state. -/
theorem reply_evidence {w : Writer Payload} {K : Keeper Payload} {i : Nat} {req : Request Payload}
    (reached : StreamJournal.Reachable w (effect w i K req)) (sendable : Sendable w K i req)
    (admitted : Admitted K i req) (quiet : Quiet w (effect w i K req)) :
    ReplyInv w (effect w i K req) (reply (effect w i K req) req) := by
  cases req with
  | promise e =>
      intro none
      refine quiet e sendable ?_ none
      by_cases same : K.promised = e
      · simp [effect, sealKeeper, same]
      · have differs : ¬ K.durable.promised = e := same
        simp [effect, sealKeeper, differs, Keeper.promised, DurableAcceptor.promise]
  | sync e | installFloor e | append e =>
      have voted := latest_voted reached
      exact voted
  | publish e head =>
      have voted := latest_voted reached
      have synced : (effect w i K (.publish e head)).synced = e := admitted.2.1.2
      rw [latest_eta, synced] at voted
      exact voted
  | create | stage | trim | observe | delete => trivial


@[simp] theorem update_self {α : Type} (f : KeeperId → α) (k : KeeperId) (value : α) :
    update f k value k = value := by simp [update]

@[simp] theorem update_other {α : Type} (f : KeeperId → α) {k j : KeeperId} (value : α)
    (differs : j ≠ k) : update f k value j = f j := by simp [update, differs]

/-- Each keeper either took a reference step or kept its state. -/
def Refines (w : Writer Payload) (before after : KeeperId → Keeper Payload) : Prop :=
  ∀ j, StreamJournal.Reachable w (before j) ∧ (Step w (before j) (after j) ∨ after j = before j)

theorem Refines.votes {w : Writer Payload} {before after : KeeperId → Keeper Payload}
    (refines : Refines w before after) (j : KeeperId) {v : Vote (Record Payload)}
    (voted : (before j).durable.votes v) : (after j).durable.votes v := by
  rcases (refines j).2 with step | same
  · exact votes_persist_step (refines j).1 step voted
  · exact same ▸ voted

theorem Refines.replies {w : Writer Payload} {before after : KeeperId → Keeper Payload}
    (refines : Refines w before after) (j : KeeperId) {e : Nat} {x : Option (Vote (Record Payload))}
    (saved : (before j).durable.replies e = some x) : (after j).durable.replies e = some x := by
  rcases (refines j).2 with step | same
  · exact replies_persist_step (refines j).1 step saved
  · exact same ▸ saved

theorem Refines.reached {w : Writer Payload} {before after : KeeperId → Keeper Payload}
    (refines : Refines w before after) (j : KeeperId) : StreamJournal.Reachable w (after j) := by
  rcases (refines j).2 with step | same
  · exact .extend (refines j).1 step
  · exact same ▸ (refines j).1

theorem reply_persists {w : Writer Payload} {k k' : Keeper Payload} (reached : StreamJournal.Reachable w k)
    (step : Step w k k' ∨ k' = k) {r : Reply Payload} (evidence : ReplyInv w k r) :
    ReplyInv w k' r := by
  rcases step with step | rfl
  · cases r with
    | sealed e _ v => exact fun none => replies_persist_step reached step (evidence none)
    | voted e h => exact votes_persist_step reached step evidence
    | done => trivial
  · exact evidence

@[simp] theorem apply_writer (s : State Payload) (k : KeeperId) (i : Nat) (req : Request Payload) :
    (s.apply k i req).writer = s.writer := rfl

@[simp] theorem apply_seals (s : State Payload) (k : KeeperId) (i : Nat) (req : Request Payload) :
    (s.apply k i req).seals = s.seals := rfl

theorem deliver_inv {s : State Payload} (inv : Inv s) {k : KeeperId} {i : Nat} {req : Request Payload}
    (inFlight : .call k i req ∈ s.net) (admitted : Admitted (s.keeper k) i req) :
    Inv (s.apply k i req) ∧ Refines s.writer s.keeper (s.apply k i req).keeper := by
  have sendable : Sendable s.writer (s.keeper k) i req := inv.packets _ inFlight
  have step := deliver_refines (inv.reached k) inv.reserved (inv.unelected 0 inv.reserved) inv.seeded
    sendable admitted
  obtain ⟨quiet, stagedElected, stagedPrefix⟩ := deliver_local (inv.reached k) sendable admitted
    (inv.quiet k) (inv.stagedElected k) (inv.stagedPrefix k)
  have refines : Refines s.writer s.keeper (s.apply k i req).keeper := by
    intro j
    refine ⟨inv.reached j, ?_⟩
    by_cases same : j = k
    · subst same
      simpa [State.apply] using step
    · exact Or.inr (by simp [State.apply, same])
  have keeperAt : ∀ j, (s.apply k i req).keeper j =
      if j = k then effect s.writer i (s.keeper k) req else s.keeper j := fun j => rfl
  refine ⟨⟨refines.reached, inv.reserved, inv.unelected, inv.seeded, inv.emptyAdvertised,
    fun h advertised => ?_, fun e r elected j signed => refines.replies j (inv.captured e r elected j signed),
    fun e j i' v collected => refines.replies j (inv.seals e j i' v collected),
    fun e j h collected => refines.votes j (inv.votes e j h collected), ?_, ?_, ?_, ?_⟩, refines⟩
  · obtain ⟨e, accepted⟩ := inv.chosen h advertised
    exact ⟨e, quorum_persists (fun j _ voted => refines.votes j voted) accepted⟩
  · intro j
    by_cases same : j = k
    · subst same; simpa [keeperAt] using quiet
    · simpa [keeperAt, same] using inv.quiet j
  · intro j
    by_cases same : j = k
    · subst same; simpa [keeperAt] using stagedElected
    · simpa [keeperAt, same] using inv.stagedElected j
  · intro j
    by_cases same : j = k
    · subst same; simpa [keeperAt] using stagedPrefix
    · simpa [keeperAt, same] using inv.stagedPrefix j
  · intro p member
    simp only [State.apply, List.mem_cons] at member
    have reachedNew : StreamJournal.Reachable s.writer (effect s.writer i (s.keeper k) req) := by
      simpa [keeperAt] using refines.reached k
    rcases member with rfl | old
    · change ReplyInv s.writer ((s.apply k i req).keeper k) _
      simp only [keeperAt, ite_true]
      exact reply_evidence reachedNew sendable admitted quiet
    · cases p with
      | call j i' req' =>
          change Sendable s.writer ((s.apply k i req).keeper j) i' req'
          have before : Sendable s.writer (s.keeper j) i' req' := inv.packets _ old
          by_cases same : j = k
          · subst same
            simp only [keeperAt, ite_true]
            exact sendable_persists (Grows.refl _) (inv.reached j) step stagedPrefix before
          · simpa [keeperAt, same] using before
      | reply j r =>
          change ReplyInv s.writer ((s.apply k i req).keeper j) r
          have before : ReplyInv s.writer (s.keeper j) r := inv.packets _ old
          exact reply_persists (inv.reached j) (refines j).2 before


theorem Refines.refl (w : Writer Payload) (keepers : KeeperId → Keeper Payload)
    (reached : ∀ j, StreamJournal.Reachable w (keepers j)) : Refines w keepers keepers :=
  fun j => ⟨reached j, Or.inr rfl⟩

/-- A writer action that only grows the ghost writer keeps every in-flight request sendable. -/
theorem packets_grow {s : State Payload} (inv : Inv s) {w' : Writer Payload} (grows : Grows s.writer w')
    (sealed : ∀ e, w'.round e = none → s.writer.round e = none) :
    ∀ p ∈ s.net, PacketInv { s with writer := w' } p := by
  intro p member
  cases p with
  | call k i req =>
      exact sendable_persists grows (inv.reached k) (Or.inr rfl) (inv.stagedPrefix k) (inv.packets _ member)
  | reply k r =>
      have before : ReplyInv s.writer (s.keeper k) r := inv.packets _ member
      cases r with
      | sealed e _ v => exact fun unchosen => before (sealed e unchosen)
      | voted => exact before
      | done => trivial

theorem round_of_grows {w w' : Writer Payload} (grows : Grows w w') {e : Nat}
    (unchosen : w'.round e = none) : w.round e = none := by
  cases old : w.round e with
  | none => rfl
  | some r => simp [grows.round e r old] at unchosen

theorem elect_grows {w : Writer Payload} {e : Nat} {r : Round Payload} (unchosen : w.round e = none)
    (empty : w.issued e = []) : Grows w (elect w e r) := by
  refine ⟨fun x r' round => ?_, fun x => ?_, fun _ advertised => advertised⟩
  · by_cases same : x = e
    · subst same; simp [unchosen] at round
    · simpa [elect, same] using round
  · by_cases same : x = e
    · subst same; simp [elect, empty]
    · simp [elect, same]

theorem next_inv {s s' : State Payload} {a : Action Payload} (inv : Inv s) (next : Next s a s') :
    Inv s' ∧ Refines s.writer s.keeper s'.keeper ∧ Grows s.writer s'.writer := by
  have unchanged := Refines.refl s.writer s.keeper inv.reached
  cases next with
  | @send k i req sendable =>
      refine ⟨{ inv with packets := ?_ }, unchanged, Grows.refl _⟩
      intro p member
      rcases List.mem_cons.mp member with rfl | old
      · exact sendable
      · exact inv.packets p old
  | deliver inFlight admitted =>
      obtain ⟨inv', refines⟩ := deliver_inv inv inFlight admitted
      exact ⟨inv', refines, Grows.refl _⟩
  | refuse => exact ⟨inv, unchanged, Grows.refl _⟩
  | restart => exact ⟨inv, unchanged, Grows.refl _⟩
  | drop sublist =>
      exact ⟨{ inv with packets := fun p member => inv.packets p (sublist.subset member) },
        unchanged, Grows.refl _⟩
  | @collectSeal e k i v inFlight unchosen =>
      refine ⟨{ inv with seals := ?_ }, unchanged, Grows.refl _⟩
      intro x j i' v' collected
      simp only [State.withSeal] at collected
      split at collected
      · rename_i hit
        obtain ⟨rfl, rfl⟩ := hit
        cases collected
        exact (inv.packets _ inFlight : ReplyInv s.writer (s.keeper j) (.sealed x i v)) unchosen
      · exact inv.seals x j i' v' collected
  | @collectVote e k h inFlight =>
      refine ⟨{ inv with votes := ?_ }, unchanged, Grows.refl _⟩
      intro x j h' collected
      simp only [State.withVote] at collected
      split at collected
      · rename_i hit
        obtain ⟨rfl, rfl⟩ := hit
        cases collected
        exact (inv.packets _ inFlight : ReplyInv s.writer (s.keeper j) (.voted x h))
      · exact inv.votes x j h' collected
  | @choose e r positive unchosen first second =>
      have grows := elect_grows (r := r) unchosen (inv.unelected e unchosen)
      have roundAt : ∀ x, (elect s.writer e r).round x = if x = e then some r else s.writer.round x :=
        fun _ => rfl
      have seedAt : ∀ x, x ≠ e → (elect s.writer e r).seed x = s.writer.seed x := by
        intro x differs
        simp [Writer.seed, roundAt, differs]
      have stagedPrefix : ∀ k, StagedPrefix (elect s.writer e r) (s.keeper k) := by
        intro k x r' f img promised round unsynced staged
        by_cases same : x = e
        · subst same
          obtain ⟨r0, old⟩ := inv.stagedElected k f img staged
          rw [promised, unchosen] at old
          cases old
        · rw [seedAt x same]
          exact inv.stagedPrefix k x r' f img promised (by simpa [roundAt, same] using round) unsynced staged
      refine ⟨⟨fun k => reachable_mono grows (inv.reached k), ?_, ?_, ?_, inv.emptyAdvertised,
        inv.chosen, ?_, inv.seals, inv.votes, ?_, ?_, stagedPrefix,
        packets_grow inv grows (fun _ => round_of_grows grows)⟩,
        unchanged, grows⟩
      · simp [roundAt, Nat.ne_of_lt positive, inv.reserved]
      · intro x round
        by_cases same : x = e
        · subst same; simp [roundAt] at round
        · simpa [elect, same] using inv.unelected x (by simpa [roundAt, same] using round)
      · intro x
        by_cases same : x = e
        · subst same
          simp [Writer.seed, elect]
        · rw [seedAt x same]
          simpa [elect, same] using inv.seeded x
      · intro x r' round k signed
        by_cases same : x = e
        · subst same
          simp only [roundAt, ite_true] at round
          cases round
          simp only [Round.sealed, decide_eq_true_eq] at signed
          rcases signed with rfl | rfl
          · exact inv.seals x _ _ _ first
          · exact inv.seals x _ _ _ second
        · exact inv.captured x r' (by simpa [roundAt, same] using round) k signed
      · intro k x positive' promised round
        exact inv.quiet k x positive' promised (round_of_grows grows round)
      · intro k f img staged
        obtain ⟨r0, old⟩ := inv.stagedElected k f img staged
        exact ⟨r0, grows.round _ r0 old⟩
  | @certify e h a b ha hb distinct first second inA inB =>
      have grows : Grows s.writer (advertise s.writer h) :=
        ⟨fun _ _ round => round, fun _ => List.prefix_rfl, fun _ old => Or.inl old⟩
      refine ⟨{ inv with
        reached := fun k => reachable_mono grows (inv.reached k)
        emptyAdvertised := Or.inl inv.emptyAdvertised
        chosen := ?_
        packets := packets_grow inv grows (fun _ unchosen => unchosen) }, unchanged, grows⟩
      intro x advertised
      rcases advertised with old | rfl
      · exact inv.chosen x old
      · refine ⟨e, fun j => decide (j = a ∨ j = b), two_of_three_is_majority a b distinct, ?_⟩
        intro j _ acked
        simp only [decide_eq_true_eq] at acked
        rcases acked with rfl | rfl
        · exact ⟨ha, inv.votes e j ha first, inA⟩
        · exact ⟨hb, inv.votes e j hb second, inB⟩
  | assign | loseAppend | rejectCapacity | discard =>
      exact ⟨{ inv with reached := inv.reached }, unchanged, Grows.refl _⟩
  | @issue e payloads rest r elected _ =>
      have grows : Grows s.writer (extend s.writer e payloads) := by
        refine ⟨fun _ _ round => round, fun x => ?_, fun _ old => old⟩
        by_cases same : x = e
        · subst same; simp [extend]
        · simp [extend, same]
      refine ⟨{ inv with
        reached := fun k => reachable_mono grows (inv.reached k)
        unelected := ?_
        seeded := ?_
        packets := packets_grow inv grows (fun _ unchosen => unchosen) }, unchanged, grows⟩
      · intro x unchosen
        by_cases same : x = e
        · subst same; simp [extend, elected] at unchosen
        · simpa [extend, same] using inv.unelected x unchosen
      · intro x
        exact (inv.seeded x).trans (grows.issued x)

theorem reachable_inv {s : State Payload} (reached : Reachable s) : Inv s := by
  induction reached with
  | initial => exact initial_inv
  | extend _ next ih => exact (next_inv ih next).1

/-- Every action of the automaton is a Study 119 step or stutter at each keeper, under a ghost
    writer that only grows. -/
theorem every_action_refines {s s' : State Payload} {a : Action Payload} (reached : Reachable s)
    (next : Next s a s') : Grows s.writer s'.writer ∧
      ∀ k, Step s'.writer (s.keeper k) (s'.keeper k) ∨ s'.keeper k = s.keeper k := by
  obtain ⟨_, refines, grows⟩ := next_inv (reachable_inv reached) next
  refine ⟨grows, fun k => ?_⟩
  rcases (refines k).2 with step | same
  · exact Or.inl (step_mono grows step)
  · exact Or.inr same


/-! ## The contract for every execution -/

/-- Every reachable state is a Study 119 execution. -/
def execution {s : State Payload} (reached : Reachable s) : Execution Payload :=
  let inv := reachable_inv reached
  { writer := s.writer, keeper := s.keeper, reached := inv.reached, reserved := inv.reserved,
    initiallyEmpty := inv.unelected 0 inv.reserved, emptyAdvertised := inv.emptyAdvertised,
    advertisedChosen := inv.chosen, captured := inv.captured }

/-- Every cut a writer certified is chosen, and any two are prefixes of one another. -/
theorem certified_cuts_agree {s : State Payload} (reached : Reachable s) {left right : History Payload}
    (first : s.writer.advertised left) (second : s.writer.advertised right) :
    left <+: right ∨ right <+: left := by
  obtain ⟨e, accepted⟩ := (reachable_inv reached).chosen left first
  obtain ⟨e', accepted'⟩ := (reachable_inv reached).chosen right second
  exact every_chosen_prefix_agrees (execution_refines_prefix_agreement (execution reached))
    (quorum_acknowledgements_choose (execution reached) accepted)
    (quorum_acknowledgements_choose (execution reached) accepted')

/-- Committed records are contiguous and irrevocable, also below any floor. -/
theorem committed_contiguous {s : State Payload} (reached : Reachable s) {old current : History Payload}
    {e e' floor : Nat} (oldCut : QuorumAccepted s.keeper e old) (currentCut : QuorumAccepted s.keeper e' current)
    (grows : old.length ≤ current.length) :
    (retained current floor).length = current.length + 1 - max floor 1 ∧
      retained old floor <+: retained current floor :=
  committed_contiguous_and_irrevocable (execution reached)
    (quorum_acknowledgements_choose (execution reached) oldCut)
    (quorum_acknowledgements_choose (execution reached) currentCut) grows

/-- A seal's adopted history covers every append acknowledged at a lower epoch. -/
theorem seal_covers_acknowledged {s : State Payload} (reached : Reachable s) {e old : Nat}
    {r : Round Payload} {h : History Payload} (elected : s.writer.round e = some r) (lower : old < e)
    (acknowledged : QuorumAccepted s.keeper old h) : h <+: r.winner.history :=
  seal_fences_and_covers_acknowledged_appends (execution reached) elected lower acknowledged

/-- A Read served by any keeper returns exactly the committed records it asks for. -/
theorem read_exact {s : State Payload} (reached : Reachable s) (keeper : KeeperId) {e start count : Nat}
    {current : History Payload} (committed : QuorumAccepted s.keeper e current)
    (known : (s.keeper keeper).head ≤ current.length) (retainedFrom : (s.keeper keeper).floor ≤ start) :
    readPage (s.keeper keeper) start count = some ⟨(s.keeper keeper).floor, (s.keeper keeper).head,
      ((current.take (s.keeper keeper).head).drop (start - 1)).take count⟩ :=
  read_returns_exact_committed_records (execution reached) keeper
    (quorum_acknowledgements_choose (execution reached) committed) known retainedFrom

/-- An acknowledged append is durable on two keepers, so it survives the loss of any one
    keeper's disk on another keeper's durable vote. -/
theorem acknowledged_survives_one_disk_loss {s : State Payload} {e : Nat} {h : History Payload}
    (acknowledged : QuorumAccepted s.keeper e h) (lost : KeeperId) :
    ∃ k, k ≠ lost ∧ ∃ held, (s.keeper k).durable.votes ⟨e, held⟩ ∧ h <+: held := by
  obtain ⟨ack, majority, held⟩ := acknowledged
  have two : ∃ a b : KeeperId, a ≠ b ∧ ack a = true ∧ ack b = true := by
    unfold JournalRefinement.Majority at majority
    cases h0 : ack 0 <;> cases h1 : ack 1 <;> cases h2 : ack 2 <;>
      simp [ensemble, h0, h1, h2] at majority
    · exact ⟨1, 2, by decide, h1, h2⟩
    · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 1, by decide, h0, h1⟩
  obtain ⟨a, b, distinct, inA, inB⟩ := two
  have all : ∀ k : KeeperId, k ∈ ensemble := by decide
  by_cases same : a = lost
  · subst same
    exact ⟨b, distinct.symm, held b (all b) inB⟩
  · exact ⟨a, same, held a (all a) inA⟩

/-- A finite run of the automaton, newest state first. -/
inductive Run : List (State Payload) → Prop
  | single {s} : Reachable s → Run [s]
  | extend {s s' : State Payload} {a states} : Run (s :: states) → Next s a s' → Run (s' :: s :: states)

theorem Run.reachable {s : State Payload} {states : List (State Payload)} (run : Run (s :: states)) :
    Reachable s := by
  cases run with
  | single reached => exact reached
  | extend run next => exact .extend run.reachable next

/-- Between any two adjacent states of a run, each keeper takes a Study 119 step or stays
    still, under the run's final ghost writer. This is Study 119's `KeeperTrace` premise. -/
theorem run_refines {states : List (State Payload)} (run : Run states) :
    ∀ (last : State Payload) (pre post : List (State Payload)) (after before : State Payload),
      states.head? = some last → states = pre ++ after :: before :: post → ∀ k,
      StreamJournal.Reachable last.writer (before.keeper k) ∧
        (Step last.writer (before.keeper k) (after.keeper k) ∨ after.keeper k = before.keeper k) := by
  induction run with
  | single =>
      intro last pre post after before _ split
      cases pre with
      | nil => simp at split
      | cons _ rest => cases rest <;> simp at split
  | @extend s s' a states run next ih =>
      intro last pre post after before head split k
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      obtain ⟨_, refines, grows⟩ := next_inv (reachable_inv run.reachable) next
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl, _⟩ := split
          refine ⟨reachable_mono grows (refines k).1, ?_⟩
          rcases (refines k).2 with step | same
          · exact Or.inl (step_mono grows step)
          · exact Or.inr same
      | cons first rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨_, tail⟩ := split
          obtain ⟨reached, moved⟩ := ih s rest post after before rfl tail k
          refine ⟨reachable_mono grows reached, ?_⟩
          rcases moved with step | same
          · exact Or.inl (step_mono grows step)
          · exact Or.inr same


/-- Send a request and deliver it at once. -/
theorem Reachable.call {s : State Payload} (reached : Reachable s) {k : KeeperId} {i : Nat}
    {req : Request Payload} (sendable : Sendable s.writer (s.keeper k) i req)
    (admitted : Admitted (s.keeper k) i req) :
    Reachable (({ s with net := .call k i req :: s.net } : State Payload).apply k i req) :=
  .extend (.extend reached (.send sendable)) (.deliver List.mem_cons_self admitted)

theorem wire_append_head_is_issued {s : State Payload} {k : KeeperId}
    {caller epoch position head : Nat} {payloads : List Payload}
    (sent : WireSendable s k caller (.append epoch position payloads head)) :
    head ≤ (s.writer.issued epoch).length :=
  sent.2

/-- Issuing the front of the assigned suffix preserves the view of the
    assignments used by other in-flight appends. -/
theorem wire_append_after_issue {s next : State Payload} {k : KeeperId}
    {caller epoch position head : Nat} {payloads frozen : List Payload}
    (sent : WireSendable s k caller (.append epoch position payloads head))
    (issued : Next s (.issue epoch frozen) next) :
    WireSendable next k caller (.append epoch position payloads head) := by
  obtain ⟨⟨elected, within, exactBytes, headWithin, certified⟩, headIssued⟩ := sent
  cases issued with
  | @issue _ _ rest _ _ split =>
    have same : ((extend (extend s.writer epoch frozen) epoch rest).issued epoch) =
        ((extend s.writer epoch (s.pending epoch).payloads).issued epoch) := by
      simp [extend, split, stamp, List.append_assoc]
    refine ⟨⟨elected, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [State.withPending, Pending.reset, same] using within
    · simpa [State.withPending, Pending.reset, same] using exactBytes
    · simpa [State.withPending, Pending.reset, same] using headWithin
    · simp [State.withPending, Pending.reset, same]
      change s.writer.advertised (((extend s.writer epoch (s.pending epoch).payloads).issued epoch).take head)
      exact certified
    · have grew : (s.writer.issued epoch).length ≤ ((extend s.writer epoch frozen).issued epoch).length := by
        simp [extend]
      exact Nat.le_trans headIssued grew

/-- Freeze exactly the pending prefix needed by an Append that can reach a
    durable decision. A definitive refusal can leave the assignment pending. -/
theorem issue_for_wire_append {s : State Payload} {k : KeeperId}
    {caller epoch position head : Nat} {payloads : List Payload}
    (sendable : WireSendable s k caller (.append epoch position payloads head)) :
    let count := position - 1 + payloads.length - (s.writer.issued epoch).length
    let frozen := (s.pending epoch).payloads.take count
    ∃ next, Next s (.issue epoch frozen) next ∧
      Sendable next.writer (next.keeper k) caller (.append epoch position payloads head) := by
  intro count frozen
  obtain ⟨⟨⟨round, elected, owner⟩, within, exactBytes, _, certified⟩, headIssued⟩ := sendable
  have electedBefore : s.writer.round epoch = some round := elected
  let rest := (s.pending epoch).payloads.drop count
  have split : (s.pending epoch).payloads = frozen ++ rest := (List.take_append_drop ..).symm
  let next := { s.withPending epoch ((s.pending epoch).reset rest) with
                writer := extend s.writer epoch frozen }
  have assignedLength : ((extend s.writer epoch (s.pending epoch).payloads).issued epoch).length =
      (s.writer.issued epoch).length + (s.pending epoch).payloads.length := by
    simp [extend, stamp]
  have enough : count ≤ (s.pending epoch).payloads.length := by
    rw [assignedLength] at within
    dsimp only [count]
    omega
  have frozenLength : frozen.length = count := by simp [frozen, Nat.min_eq_left enough]
  have issuedLength : (next.writer.issued epoch).length = (s.writer.issued epoch).length + count := by
    simp [next, extend, stamp, frozenLength]
  have covered : position - 1 + payloads.length ≤ (next.writer.issued epoch).length := by
    rw [issuedLength]
    dsimp only [count]
    omega
  have headCovered : head ≤ (next.writer.issued epoch).length := by omega
  have prefixed : next.writer.issued epoch <+: (extend s.writer epoch (s.pending epoch).payloads).issued epoch := by
    have stamped : stamp epoch (s.pending epoch).payloads = stamp epoch frozen ++ stamp epoch rest := by
      simpa only [stamp, List.map_append] using congrArg (stamp epoch) split
    simp only [next, extend, stamped, ← List.append_assoc]
    exact ⟨stamp epoch rest, rfl⟩
  refine ⟨next, .issue electedBefore split, ⟨round, electedBefore, owner⟩, covered, ?_, headCovered, ?_⟩
  · rw [exactBytes, List.take_drop, List.take_drop, take_of_prefix prefixed covered]
  · rw [take_of_prefix prefixed headCovered]
    exact certified

/-- A new Append that reaches an admitted durable decision projects to an
    issue, ordinary send, and delivery of the exact wire request. -/
theorem wire_append_delivery {s : State Payload} {keeper : KeeperId}
    {caller epoch position head : Nat} {payloads : List Payload}
    (sent : WireSendable s keeper caller (.append epoch position payloads head))
    (admitted : Admitted (s.keeper keeper) caller (.append epoch position payloads head)) :
    let request := Request.append epoch position payloads head
    let packet := Packet.call keeper caller request
    ∃ frozen afterIssue afterSend,
      Next s (.issue epoch frozen) afterIssue ∧
      Next afterIssue (.send packet) afterSend ∧
      Next afterSend (.deliver packet) (afterSend.apply keeper caller request) := by
  intro request packet
  obtain ⟨afterIssue, issue, ready⟩ := issue_for_wire_append sent
  have unchanged : afterIssue.keeper = s.keeper := by cases issue; rfl
  let afterSend := { afterIssue with net := packet :: afterIssue.net }
  have send : Next afterIssue (.send packet) afterSend := .send ready
  have deliver : Next afterSend (.deliver packet) (afterSend.apply keeper caller request) := by
    refine .deliver (.head _) ?_
    change Admitted (afterIssue.keeper keeper) caller request
    rw [unchanged]
    exact admitted
  exact ⟨_, afterIssue, afterSend, issue, send, deliver⟩

#print axioms wire_append_delivery
#print axioms wire_append_head_is_issued
#print axioms wire_append_after_issue
#print axioms issue_for_wire_append
#print axioms capacity_refusal_excludes_retry
#print axioms discard_preserves_pending_evidence
#print axioms step_mono
#print axioms complete_sync_head_within_request
#print axioms complete_sync_uses_request_records
#print axioms deliver_refines
#print axioms sendable_persists
#print axioms reply_evidence
#print axioms next_inv
#print axioms reachable_inv
#print axioms every_action_refines
#print axioms certified_cuts_agree
#print axioms committed_contiguous
#print axioms seal_covers_acknowledged
#print axioms read_exact
#print axioms acknowledged_survives_one_disk_loss
#print axioms run_refines

end Logkeeper.StreamIO
