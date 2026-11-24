import Witness

set_option warningAsError true

namespace Logkeeper.DecisionKernel

def Action.original : Action → Prop
  | .fund _ | .fence _ _ | .dispose _ _ => False
  | _ => True

private def Footprint (s t : State) : Prop :=
  t.window = s.window ∧ t.objects.fence = s.objects.fence

private theorem framed {writes : Reducer.Writes}
    (frame : frame writes s t) (budget : writes.budget = false) (objects : writes.objects = false) :
    Footprint s t := by
  obtain ⟨_, budgetFrame, _, _, _, _, _, _, objectFrame, _⟩ := frame
  exact ⟨(budgetFrame budget).2, congrArg ObjectWithdrawal.State.fence (objectFrame objects)⟩

private theorem framed_window {writes : Reducer.Writes}
    (frame : frame writes s t) (budget : writes.budget = false) : t.window = s.window :=
  (frame.2.1 budget).2

private theorem registering_keeps_fences (s : ObjectWithdrawal.State Nat Nat)
    (names : Option (List Nat)) (role : ObjectWithdrawal.Role) (owner : Nat) :
    (Reducer.registerReferences s names role owner).fence = s.fence := by
  cases names <;> rfl

private theorem dropping_keeps_fences
    (drop : Reducer.dropReferences s t keep) : t.fence = s.fence := by
  obtain ⟨_, _, rfl⟩ := drop
  rfl

private theorem original_effect_keeps_window_and_fences
    (original : r.action.original) (applied : effect limits s r out t) : Footprint s t := by
  cases action : r.action
  case fund | fence | dispose => simp [action, Action.original] at original
  case append grant expected lane payload bytes refs =>
    cases out <;> simp only [effect, action] at applied
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, window, _⟩, references⟩ := applied
    exact ⟨window, references ▸ registering_keeps_fences _ _ _ _⟩
  case lease change =>
    cases change with
    | acquire =>
      simp only [effect, action] at applied
      obtain ⟨_, _, frame, _⟩ := applied
      exact framed frame rfl rfl
    | release target =>
      cases target <;> cases out <;> simp only [effect, action] at applied <;>
        exact framed applied.1 rfl rfl
    | renew scope =>
      cases scope <;> cases out <;> simp only [effect, action] at applied <;>
        exact framed applied.1 rfl rfl
  case reconfigure change =>
    cases change <;> cases out <;> simp only [effect, action] at applied
    case rotate.granted =>
      obtain ⟨frame, _, _, _, _, _, _, _, _, _, _, _, _, _, _, drop⟩ := applied
      exact ⟨framed_window frame rfl, dropping_keeps_fences drop⟩
    all_goals exact framed applied.1 rfl rfl
  case checkpoint change =>
    cases change <;> cases out <;> simp only [effect, action] at applied
    case prepare.checkpointPrepared =>
      obtain ⟨frame, _, _, variants⟩ := applied
      refine ⟨framed_window frame rfl, ?_⟩
      rcases variants with already | fresh
      · rw [already.2.2]
      · obtain ⟨_, _, _, _, _, _, _, _, _, references⟩ := fresh
        exact references ▸ registering_keeps_fences _ _ _ _
    case select.published =>
      obtain ⟨frame, _, _, variants⟩ := applied
      refine ⟨framed_window frame rfl, ?_⟩
      rcases variants with already | successor
      · rw [already.2.2]
      · exact dropping_keeps_fences successor.2.2.2
    case close.checkpointClosed =>
      obtain ⟨frame, _, _, _, _, _, _, drop⟩ := applied
      exact ⟨framed_window frame rfl, dropping_keeps_fences drop⟩
  case collect target =>
    cases target <;> cases out <;> simp only [effect, action] at applied
    case prefix.trimmed =>
      obtain ⟨_, _, _, _, _, _, _, _, _, window, _, _, _, _, _, _, drop⟩ := applied
      exact ⟨window, dropping_keeps_fences drop⟩
    case root.checkpointSettled =>
      obtain ⟨frame, _, _, _, _, _, _, _, _, drop⟩ := applied
      exact ⟨framed_window frame rfl, dropping_keeps_fences drop⟩

theorem original_step_keeps_window_and_fences
    (original : r.action.original) (step : Step limits position time r s out t) :
    t.window = s.window ∧ t.objects.fence = s.objects.fence := by
  cases step with
  | rejected => exact ⟨rfl, rfl⟩
  | chosen _ request =>
    cases request with
    | @applied target _ _ applied =>
      exact original_effect_keeps_window_and_fences (s := advance limits s position time r)
        (t := target) original applied.commandEffect
    | _ => exact ⟨rfl, rfl⟩

inductive OriginalTrace (bounds : Reducer.Limits) : State → State → Prop
  | same (s : State) : OriginalTrace bounds s s
  | next (earlier : OriginalTrace bounds s m) (original : r.action.original)
      (step : Step bounds position time r m out t) : OriginalTrace bounds s t

theorem original_trace_keeps_window_and_fences (trace : OriginalTrace limits s t) :
    t.window = s.window ∧ t.objects.fence = s.objects.fence := by
  induction trace with
  | same => exact ⟨rfl, rfl⟩
  | next _ original step earlier =>
    obtain ⟨window, fences⟩ := original_step_keeps_window_and_fences original step
    exact ⟨window.trans earlier.1, fences.trans earlier.2⟩

theorem original_five_cannot_install_a_fence :
    ∃ bounds s t name version, Inv bounds s ∧ Trace bounds s t ∧
      s.objects.fence name = none ∧ t.objects.fence name = some version ∧
      ¬ OriginalTrace bounds s t := by
  obtain ⟨s, _, installed, inv, _, trace, _, fresh, _, fenced⟩ := fence_is_not_graph_determined
  refine ⟨_, s, installed, 1, 7, inv, trace, fresh, fenced, ?_⟩
  intro original
  have same := congrFun (original_trace_keeps_window_and_fences original).2 1
  rw [fenced, fresh] at same
  contradiction

theorem original_five_cannot_fund_a_successor :
    ∃ bounds s t, Inv bounds s ∧ Trace bounds s t ∧
      s.window.serial = 1 ∧ t.window.serial = 2 ∧ ¬ OriginalTrace bounds s t := by
  obtain ⟨bounds, s, t, inv, trace, oldSerial, _, newSerial, _⟩ := reachable_funding
  refine ⟨bounds, s, t, inv, trace, oldSerial, newSerial, ?_⟩
  intro original
  have same := congrArg Reducer.Window.serial (original_trace_keeps_window_and_fences original).1
  rw [oldSerial, newSerial] at same
  contradiction

theorem disposal_success_requires_dispose
    (applied : Applied limits s r (.workerDisposed owner) t) :
    ∃ basis, r.action = .dispose owner basis := by
  have writes := applied.commandEffect
  cases action : r.action with
  | dispose target basis =>
    simp only [effect, action] at writes
    exact ⟨basis, by rw [writes.2.1]⟩
  | lease change =>
    cases change with
    | acquire basis =>
      simp only [effect, action] at writes
      obtain ⟨_, generated, _⟩ := writes
      cases basis <;> cases generated
    | release target => cases target <;> simp [effect, action] at writes
    | renew scope => cases scope <;> simp [effect, action] at writes
  | reconfigure change => cases change <;> simp [effect, action] at writes
  | checkpoint change => cases change <;> simp [effect, action] at writes
  | collect target => cases target <;> simp [effect, action] at writes
  | append | fund | fence => simp [effect, action] at writes

end Logkeeper.DecisionKernel
