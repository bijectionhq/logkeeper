------------------------------ MODULE ClosureCertificate ------------------------------
CONSTANTS Scenario, Policy
VARIABLES generation, grantGeneration, tableBody, checked, admitted

vars == <<generation, grantGeneration, tableBody, checked, admitted>>
Base == {"root", "table", "current", "nascent", "retained-L0", "group-artefact"}
CurrentDemand == Base \cup {"oversized-suffix"}
OldDemand == CurrentDemand \cup {"old-selector-only"}
UploadsInTail == Scenario \in {"inline-upload", "oversized-upload"}
Demand == OldDemand \cup (IF UploadsInTail THEN {"adopted-catalog"} ELSE {})
Omitted ==
  CASE Scenario = "suffix" -> {"oversized-suffix"}
    [] Scenario = "retained" -> {"retained-L0"}
    [] Scenario = "artefact" -> {"group-artefact"}
    [] Scenario = "other-selector" -> {"old-selector-only"}
    [] UploadsInTail -> {"adopted-catalog"}
    [] OTHER -> {}
Held == Demand \ Omitted
CheckedDemand ==
  CASE Policy = "base-only" -> Demand \ {"oversized-suffix", "adopted-catalog"}
    [] Policy = "exclude-retained-L0" -> Demand \ {"retained-L0"}
    [] Policy = "exclude-artefacts" -> Demand \ {"group-artefact"}
    [] Policy = "visible-only" -> CurrentDemand
    [] Policy = "payloads-only" -> Demand \ {"adopted-catalog"}
    [] OTHER -> Demand

Init ==
  /\ generation = 1
  /\ grantGeneration = 1
  /\ tableBody = "named"
  /\ checked = FALSE
  /\ admitted = FALSE

ChangeReality ==
  /\ ~checked
  /\ IF Scenario = "relocation" THEN /\ generation = 1
                                       /\ generation' = 2
                                       /\ tableBody' = tableBody
       ELSE /\ Scenario = "legacy"
            /\ tableBody = "named"
            /\ tableBody' = "substituted"
            /\ generation' = generation
  /\ UNCHANGED <<grantGeneration, checked, admitted>>

AcquireReplacement ==
  /\ Scenario = "relocation"
  /\ generation = 2
  /\ grantGeneration = 1
  /\ grantGeneration' = 2
  /\ UNCHANGED <<generation, tableBody, checked, admitted>>

Check ==
  /\ ~checked
  /\ CheckedDemand \subseteq Held
  /\ generation = grantGeneration \/ Policy = "logical-path-only"
  /\ tableBody = "named" \/ Policy = "legacy-root-alone"
  /\ Scenario # "pack" \/ Policy = "count-logical-members"
  /\ checked' = TRUE
  /\ UNCHANGED <<generation, grantGeneration, tableBody, admitted>>

Serve ==
  /\ checked
  /\ ~admitted
  /\ admitted' = TRUE
  /\ UNCHANGED <<generation, grantGeneration, tableBody, checked>>

Next == ChangeReality \/ AcquireReplacement \/ Check \/ Serve
Spec == Init /\ [][Next]_vars
CompleteReadSet == admitted => Demand \subseteq Held
ExactCarrier == admitted => generation = grantGeneration
ExactChildren == admitted => tableBody = "named"
DistinctDomains == admitted => Scenario # "pack"
NeverServesRelocatedVersion == ~(admitted /\ generation = 2)
======================================================================================
