------------------------------ MODULE Cadence -------------------------------
EXTENDS Naturals
CONSTANTS Mode, C, Observe, Work, PinLife
VARIABLES phase, attempt, age, stale
vars == <<phase, attempt, age, stale>>

\* Time to the next publication is cyclic; stale is sticky within an
\* attempt, so returning to a clock phase does not reuse a root identity.
Init == phase = 0 /\ attempt = "waiting" /\ age = 0 /\ stale = FALSE

Advance ==
  /\ attempt # "done"
  /\ ~(attempt = "waiting" /\ phase = Observe)
  /\ attempt # "running" \/ age < Work
  /\ phase' = (phase + 1) % C
  /\ age' = IF attempt = "running" /\ age < Work THEN age + 1 ELSE age
  /\ stale' = (stale \/ (attempt = "running" /\ phase' = 0))
  /\ UNCHANGED attempt

Admit ==
  /\ attempt = "waiting" /\ phase = Observe
  /\ attempt' = "running" /\ age' = 0
  /\ stale' = FALSE
  /\ UNCHANGED phase

Complete ==
  /\ attempt = "running" /\ age = Work
  /\ IF Mode = "A" \/ (Mode = "pin" /\ age < PinLife) \/ ~stale
       THEN /\ attempt' = "done" /\ UNCHANGED <<phase, age, stale>>
       ELSE /\ attempt' = "waiting" /\ age' = 0 /\ UNCHANGED <<phase, stale>>

Next == Advance \/ Admit \/ Complete
Spec == Init /\ [][Next]_vars /\ WF_vars(Advance) /\ WF_vars(Admit) /\ WF_vars(Complete)
EventuallyServed == <>(attempt = "done")
SawCompletion == ~(attempt = "done")
SawOvertakeAndFinish == ~(attempt = "done" /\ stale)
=============================================================================
