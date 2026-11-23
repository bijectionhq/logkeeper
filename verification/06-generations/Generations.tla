----------------------------- MODULE Generations -----------------------------
EXTENDS Naturals, Sequences
CONSTANTS Groups, MaxGeneration, MaxLsn, Design, Mutation
VARIABLE state

NoReservation == [source |-> 0, from_generation |-> 0, nonce |-> 0]

Init ==
    state = [
        groups |-> [group \in Groups |->
            [generation |-> IF group = 1 THEN 1 ELSE 0,
             mode |-> IF group = 1 THEN "serving" ELSE "inactive",
             history |-> <<>>]],
        reservations |-> [group \in Groups |-> NoReservation],
        nonce_counters |-> [group \in Groups |-> 0],
        certificates |-> {},
        receipts |-> {},
        retired |-> FALSE
    ]

CanWrite(group) == state.groups[group].mode = "serving"

Prepare(target, source, from_generation) ==
    /\ Design = "reservation"
    /\ target # source
    /\ ~CanWrite(target)
    /\ state.groups[target].mode # "retired"
    /\ state.reservations[target] = NoReservation
    /\ state.nonce_counters[target] < MaxGeneration
    /\ LET nonce == state.nonce_counters[target] + 1
       IN state' = [state EXCEPT
          !.reservations[target] = [source |-> source, from_generation |-> from_generation, nonce |-> nonce],
          !.nonce_counters[target] = IF Mutation = "reuse_nonce" THEN @ ELSE nonce]

Seal(source, successor) ==
    /\ source # successor
    /\ CanWrite(source)
    /\ state.groups[source].generation < MaxGeneration
    /\ LET previous == state.groups[source]
           reservation == state.reservations[successor]
           certificate == [source |-> source, successor |-> successor,
                           generation |-> previous.generation + 1, cut |-> previous.history,
                           nonce |-> reservation.nonce]
       IN /\ (Design = "floor" \/
              (reservation.source = source /\ reservation.from_generation = previous.generation))
          /\ state' = [state EXCEPT
                 !.groups[source].mode = "sealed",
                 !.certificates = @ \cup {certificate}]

MatchesReservation(target, certificate) ==
    state.reservations[target] =
        [source |-> certificate.source, from_generation |-> certificate.generation - 1,
         nonce |-> certificate.nonce]

Install(target, certificate) ==
    /\ state.groups[target].mode \in {"sealed", "inactive"}
    /\ certificate.successor = target \/ Mutation = "wrong_target"
    /\ IF Design = "floor"
       THEN LET previous == state.groups[target].generation
            IN previous < certificate.generation \/
               (Mutation = "accept_equal" /\ previous = certificate.generation)
       ELSE MatchesReservation(target, certificate)
    /\ state' = [state EXCEPT
        !.reservations[target] = NoReservation,
        !.groups[target] =
            [generation |-> certificate.generation, mode |-> "serving", history |-> certificate.cut]]

AppendEntry(group, payload) ==
    /\ CanWrite(group)
    /\ Len(state.groups[group].history) < MaxLsn
    /\ LET entry == [lsn |-> Len(state.groups[group].history) + 1, bytes |-> payload]
       IN state' = [state EXCEPT
           !.groups[group].history = Append(@, payload), !.receipts = @ \cup {entry}]

Retire(group) ==
    /\ CanWrite(group)
    /\ state' = [state EXCEPT !.groups[group].mode = "retired", !.retired = TRUE]

Forget(group) ==
    /\ Design = "reservation" \/ Mutation = "forget_generation"
    /\ state.groups[group].mode = "sealed"
    /\ state.groups[group].generation > 0
    /\ state' = [state EXCEPT !.groups[group].generation = 0]

Expire(target) ==
    /\ Mutation = "expire_slot"
    /\ state.reservations[target] # NoReservation
    /\ state' = [state EXCEPT !.reservations[target] = NoReservation]

Next ==
    \/ \E group \in Groups :
       \/ Retire(group) \/ Forget(group) \/ Expire(group)
       \/ \E source \in Groups, generation \in 1..(MaxGeneration - 1) :
            Prepare(group, source, generation)
       \/ \E successor \in Groups : Seal(group, successor)
       \/ \E certificate \in state.certificates : Install(group, certificate)
       \/ \E payload \in {"A", "B"} : AppendEntry(group, payload)

Spec == Init /\ [][Next]_state

OneAuthority == \A group, other \in Groups :
    (CanWrite(group) /\ CanWrite(other)) => group = other

ReceiptsPreserved ==
    \A group \in Groups :
        CanWrite(group) => \A entry \in state.receipts :
            IF entry.lsn <= Len(state.groups[group].history)
            THEN state.groups[group].history[entry.lsn] = entry.bytes
            ELSE FALSE

RetirementIsTerminal == state.retired => \A group \in Groups : ~CanWrite(group)

NoStrandedTransfer ==
    (Design = "reservation" /\ ~state.retired /\ \A group \in Groups : ~CanWrite(group)) =>
        \E certificate \in state.certificates :
            MatchesReservation(certificate.successor, certificate)

NeverReturnsAndCommits ==
    ~(CanWrite(1) /\ state.groups[1].generation = 3 /\
      Len(state.groups[1].history) = 2 /\
      \E certificate \in state.certificates : certificate.generation = 3 /\
            certificate.successor = 1 /\ Len(certificate.cut) = 1)
=============================================================================
