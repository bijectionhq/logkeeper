import EnvelopeCodec
import WorkerRoster

set_option warningAsError true

namespace WorkerRosterCodec

open EnvelopeCodec
open JointSource (WorkerChange Workers)

variable {width capacity lastEnrollment : Nat}

def MemberFits (width issued : Nat) (member : Nat × Nat) : Prop :=
  member.1 < wordLimit width ∧ 0 < member.2 ∧ member.2 ≤ issued

def Precedes (first second : Nat × Nat) : Prop :=
  second.2 < first.2 ∧ first.1 ≠ second.1

structure WellFormed (width capacity lastEnrollment : Nat) (workers : Workers) : Prop where
  representable : workers.issuedThrough < wordLimit width
  withinIssuance : workers.issuedThrough ≤ lastEnrollment
  withinRows : workers.members.length ≤ capacity
  ordered : workers.members.Pairwise Precedes
  membersFit : ∀ member ∈ workers.members, MemberFits width workers.issuedThrough member

def FitsCommand (width : Nat) : WorkerChange → Prop
  | .enroll holder _ => holder < wordLimit width
  | .withdraw _ _ => True

theorem accepted_edits_keep_the_roster_encodable
    {before next : Workers} {change : WorkerChange}
    (valid : WellFormed width capacity lastEnrollment before)
    (issuanceFits : lastEnrollment < wordLimit width)
    (commandFits : FitsCommand width change)
    (edited : before.change capacity lastEnrollment change = some next) :
    WellFormed width capacity lastEnrollment next := by
  cases change with
  | enroll holder expected =>
      simp only [Workers.change] at edited
      split at edited
      next allowed =>
        cases edited
        have issued := Nat.succ_le_of_lt allowed.2.1
        have free := Nat.succ_le_of_lt allowed.2.2.2
        have absent : before.members.find? (fun member => member.1 == holder) = none := by
          have known := allowed.2.2.1
          cases found : before.members.find? (fun member => member.1 == holder) <;>
            simp_all [Workers.enrollment]
        refine ⟨Nat.lt_of_le_of_lt issued issuanceFits, issued, free, List.pairwise_cons.mpr ⟨?_, valid.ordered⟩, ?_⟩
        · intro member present
          have fits := valid.membersFit member present
          have different : member.1 ≠ holder := by
            simpa using (List.find?_eq_none.mp absent member present)
          exact ⟨Nat.lt_succ_of_le fits.2.2, Ne.symm different⟩
        · intro member present
          rcases List.mem_cons.mp present with rfl | existed
          · exact ⟨commandFits, Nat.zero_lt_succ _, Nat.le_refl _⟩
          · obtain ⟨holderFits, positive, within⟩ := valid.membersFit member existed
            exact ⟨holderFits, positive, Nat.le_trans within (Nat.le_succ _)⟩
      next => contradiction
  | withdraw holder enrollment =>
      simp only [Workers.change] at edited
      split at edited
      · cases edited
        refine ⟨valid.representable, valid.withinIssuance, Nat.le_trans (List.length_filter_le _ _) valid.withinRows,
          valid.ordered.filter _, ?_⟩
        intro member present
        exact valid.membersFit member (List.mem_filter.mp present).1
      · contradiction

def rowWords (width : Nat) (member : Nat × Nat) : List (Field width) :=
  [word width member.1, word width member.2]

def words (width : Nat) (workers : Workers) : List (Field width) :=
  word width workers.issuedThrough :: workers.members.flatMap (rowWords width)

def readRows : List (Field width) → Option (List (Nat × Nat))
  | [] => some []
  | holder :: serial :: remaining =>
      (readRows remaining).map ((readWord holder.val, readWord serial.val) :: ·)
  | _ => none

private theorem readRows_on_words {workers : Workers}
    (fits : ∀ member ∈ workers.members, MemberFits width workers.issuedThrough member)
    (issued : workers.issuedThrough < wordLimit width) :
    readRows (workers.members.flatMap (rowWords width)) = some workers.members := by
  obtain ⟨through, members⟩ := workers
  induction members with
  | nil => rfl
  | cons head tail prior =>
      have headFits := fits head (by simp)
      have tailFits := prior (fun member live => fits member (List.mem_cons_of_mem _ live)) issued
      have serialFits : head.2 < wordLimit width := Nat.lt_of_le_of_lt headFits.2.2 issued
      simp [rowWords, readRows, word, tailFits,
        fixed_width_words_roundtrip headFits.1, fixed_width_words_roundtrip serialFits]

private theorem readRows_keeps_exact_words {input : List (Field width)} {members : List (Nat × Nat)}
    (parsed : readRows input = some members) : members.flatMap (rowWords width) = input := by
  induction input using readRows.induct generalizing members with
  | case1 =>
      cases parsed
      rfl
  | case2 holder serial tail prior =>
      cases found : readRows tail with
      | none => simp [readRows, found] at parsed
      | some rows =>
          simp [readRows, found] at parsed
          subst members
          simp [rowWords, readField_recovers_the_exact_word, prior found]
  | case3 _ _ => simp [readRows] at parsed

def domain : UInt8 := 3

def encode (width : Nat) (workers : Workers) : Bytes :=
  domain :: flattenFields (words width workers)

def maxBytes (width capacity : Nat) : Nat := 1 + (1 + 2 * capacity) * width

private theorem words_count (workers : Workers) : (words width workers).length = 1 + 2 * workers.members.length := by
  have count (members : List (Nat × Nat)) : (members.flatMap (rowWords width)).length = 2 * members.length := by
    induction members with
    | nil => rfl
    | cons head tail prior =>
        simp [rowWords, prior, Nat.mul_add]
  simp [words, count, Nat.add_comm]

def readBook : List (Field width) → Option Workers
  | [] => none
  | issued :: members => (readRows members).map (fun rows => ⟨readWord issued.val, rows⟩)

def parse (width capacity : Nat) (wire : Bytes) : Option Workers :=
  match wire with
  | tag :: raw =>
      if tag = domain ∧ 0 < width ∧ raw.length ≤ (1 + 2 * capacity) * width then
        (readFields width (raw.length / width) raw).bind readBook
      else none
  | [] => none

noncomputable def decode (width capacity lastEnrollment : Nat) (wire : Bytes) : Option Workers := by
  classical
  exact match parse width capacity wire with
  | none => none
  | some workers =>
      if WellFormed width capacity lastEnrollment workers then some workers else none

theorem a_valid_roster_roundtrips {workers : Workers}
    (positive : 0 < width) (valid : WellFormed width capacity lastEnrollment workers) :
    decode width capacity lastEnrollment (encode width workers) = some workers := by
  have count : (flattenFields (words width workers)).length / width = (words width workers).length := by
    rw [flattenFields_size]
    exact Nat.mul_div_cancel _ positive
  have bounded : (flattenFields (words width workers)).length ≤ (1 + 2 * capacity) * width := by
    rw [flattenFields_size, words_count]
    exact Nat.mul_le_mul_right width (by have := valid.withinRows; omega)
  have permitted : domain = domain ∧ 0 < width ∧
      (flattenFields (words width workers)).length ≤ (1 + 2 * capacity) * width := ⟨rfl, positive, bounded⟩
  have book : readBook (words width workers) = some workers := by
    have issued : readWord (word width workers.issuedThrough).val = workers.issuedThrough :=
      fixed_width_words_roundtrip valid.representable
    simp only [words, readBook, readRows_on_words valid.membersFit valid.representable, issued, Option.map_some]
  have parsed : parse width capacity (encode width workers) = some workers := by
    simp [parse, encode, permitted, count, readFields_after_flatten, book]
  simp [decode, parsed, valid]

private theorem parsed_roster_keeps_the_exact_wire {workers : Workers} {wire : Bytes}
    (parsed : parse width capacity wire = some workers) :
    encode width workers = wire := by
  cases wire with
  | nil => simp [parse] at parsed
  | cons tag raw =>
      simp only [parse] at parsed
      split at parsed
      next accepted =>
        cases fields : readFields width (raw.length / width) raw with
        | none => simp [fields] at parsed
        | some available =>
            cases available with
            | nil => simp [fields, readBook] at parsed
            | cons issued members =>
                cases rows : readRows members with
                | none => simp [fields, readBook, rows] at parsed
                | some found =>
                    simp [fields, readBook, rows] at parsed
                    subst workers
                    simp [encode, words, accepted.1, readField_recovers_the_exact_word,
                      readRows_keeps_exact_words rows, readFields_recovers_the_exact_wire fields]
      next => simp at parsed

theorem an_opened_roster_names_its_exact_bytes {workers : Workers} {wire : Bytes}
    (opened : decode width capacity lastEnrollment wire = some workers) :
    encode width workers = wire ∧ WellFormed width capacity lastEnrollment workers := by
  cases parsed : parse width capacity wire with
  | none => simp [decode, parsed] at opened
  | some found =>
      simp only [decode, parsed] at opened
      split at opened
      next valid =>
        cases opened
        exact ⟨parsed_roster_keeps_the_exact_wire parsed, valid⟩
      next => simp at opened

theorem roster_bytes_have_a_bounded_footprint {workers : Workers}
    (valid : WellFormed width capacity lastEnrollment workers) :
    (encode width workers).length ≤ maxBytes width capacity := by
  simp only [encode, List.length_cons, flattenFields_size, words_count, maxBytes]
  have scaled := Nat.mul_le_mul_right width (show 1 + 2 * workers.members.length ≤ 1 + 2 * capacity by
    have := valid.withinRows
    omega)
  omega

end WorkerRosterCodec
