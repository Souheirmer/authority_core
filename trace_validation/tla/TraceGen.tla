------------------------------ MODULE TraceGen ------------------------------
(***************************************************************************)
(* Trace generator for conformance testing. EXTENDS the unmodified model    *)
(* and adds two auxiliary variables that do not influence any original      *)
(* variable (a conservative extension):                                     *)
(*   act      the action taken in the step and its parameters               *)
(*   allowed  [d |-> AllowRule(d)] evaluated by TLC in the reached state    *)
(* Each disjunct of TGNext is one disjunct of Provisioning!Next             *)
(* (Provisioning.tla lines 359-371), in the same order.                     *)
(***************************************************************************)
EXTENDS Provisioning

VARIABLES act, allowed

AllowView == [d \in DEVICES |-> AllowRule(d)]

TGInit == Init /\ act = <<"Init">> /\ allowed = AllowView

TGNext ==
  /\ \/ \E d \in DEVICES, to \in RegStates : RegChange(d, to) /\ act' = <<"RegChange", d, to>>
     \/ \E d \in DEVICES : PushNotify(d) /\ act' = <<"PushNotify", d>>
     \/ \E m \in net : DeliverNotify(m) /\ act' = <<"DeliverNotify", m>>
     \/ \E m \in net : DropNotify(m) /\ act' = <<"DropNotify", m>>
     \/ \E d \in DEVICES : PdpPoll(d) /\ act' = <<"PdpPoll", d>>
     \/ \E d \in DEVICES : SyncFromRegistry(d) /\ act' = <<"SyncFromRegistry", d>>
     \/ \E d \in DEVICES, e \in EVENTTYPES : ObserveEvent(d, e) /\ act' = <<"ObserveEvent", d, e>>
     \/ \E d \in DEVICES, e \in EVENTTYPES : ClearEvent(d, e) /\ act' = <<"ClearEvent", d, e>>
     \/ \E d \in DEVICES : RecordAccess(d) /\ act' = <<"RecordAccess", d>>
     \/ Tick /\ act' = <<"Tick">>
     \/ Partition /\ act' = <<"Partition">>
     \/ Heal /\ act' = <<"Heal">>
  /\ allowed' = AllowView'

TGSpec == TGInit /\ [][TGNext]_<<vars, act, allowed>>
=============================================================================
