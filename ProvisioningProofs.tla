------------------------- MODULE ProvisioningProofs -------------------------
(***************************************************************************)
(* Machine-checked proof (TLAPS) that the origin-timed lease A8 satisfies   *)
(* bounded revocation S3 whenever its assumed skew bound covers the actual  *)
(* clock error (SKEWBOUND >= SKEW).                                         *)
(*                                                                         *)
(* The proof holds for EVERY value of the constants allowed by              *)
(* ConstAssumptions: any finite or infinite set of devices, and any         *)
(* LEASE, MAXT, MAXVER, MAXNET, MAXAGE, SKEW. It is therefore not tied to   *)
(* the bounded configurations TLC explores. It mechanizes Propositions 2    *)
(* and 3 of the paper.                                                      *)
(*                                                                         *)
(* Check:  tlapm --threads 8 ProvisioningProofs.tla                         *)
(***************************************************************************)
EXTENDS Provisioning, TLAPS

\* Hypotheses of the theorem, beyond ConstAssumptions.
A8Hyp == RULE = "A8_OriginLease" /\ SKEWBOUND >= SKEW

\* A type invariant without the finite bounds TLC needs. The bounds in the
\* specification still hold, but nothing below depends on them.
Msg == [dv : DEVICES, st : RegStates, ver : Nat, orig : Nat]

TypeInv ==
  /\ reg       \in [DEVICES -> RegStates]
  /\ regVer    \in [DEVICES -> Nat]
  /\ dev       \in [DEVICES -> DevStates]
  /\ pdpSt     \in [DEVICES -> RegStates]
  /\ pdpVer    \in [DEVICES -> Nat]
  /\ pdpAge    \in [DEVICES -> Nat]
  /\ pdpOrig   \in [DEVICES -> Nat]
  /\ sinceRev  \in [DEVICES -> Nat]
  /\ now       \in Nat
  /\ useCnt    \in [DEVICES -> Nat]
  /\ badGrants \in [DEVICES -> Nat]
  /\ link      \in LinkStates
  /\ net       \subseteq Msg
  /\ activeEv  \in [DEVICES -> SUBSET EVENTTYPES]

\* Proposition 2 (a): no origin stamp lies more than SKEW ahead of the clock.
OrigBound ==
  /\ \A d \in DEVICES : pdpOrig[d] <= now + SKEW
  /\ \A m \in net : m.orig <= now + SKEW

\* Proposition 2 (b): a cached enrollment of a revoked device was observed
\* no later than (SKEW before) the revocation.
CacheOPR ==
  \A d \in DEVICES :
    (pdpSt[d] = "Enrolled" /\ reg[d] = "Revoked")
      => now - pdpOrig[d] + SKEW >= sinceRev[d]

\* Proposition 2 (c): the same for enrollments still in flight.
NetOPR ==
  \A m \in net :
    (m.st = "Enrolled" /\ reg[m.dv] = "Revoked")
      => now - m.orig + SKEW >= sinceRev[m.dv]

Inv == TypeInv /\ OrigBound /\ CacheOPR /\ NetOPR

-----------------------------------------------------------------------------

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv
  OBVIOUS
<1> USE ConstAssumptions DEF Init, RegStates, DevStates, LinkStates
<1>1. /\ reg       \in [DEVICES -> RegStates]
      /\ regVer    \in [DEVICES -> Nat]
      /\ dev       \in [DEVICES -> DevStates]
      /\ pdpSt     \in [DEVICES -> RegStates]
      /\ pdpVer    \in [DEVICES -> Nat]
      /\ pdpAge    \in [DEVICES -> Nat]
      /\ pdpOrig   \in [DEVICES -> Nat]
      /\ sinceRev  \in [DEVICES -> Nat]
      /\ now       \in Nat
      /\ useCnt    \in [DEVICES -> Nat]
      /\ badGrants \in [DEVICES -> Nat]
      /\ link      \in LinkStates
  OBVIOUS
<1>2. net \subseteq Msg
  BY DEF Msg
<1>3. activeEv \in [DEVICES -> SUBSET EVENTTYPES]
  OBVIOUS
<1>4. TypeInv
  BY <1>1, <1>2, <1>3 DEF TypeInv
<1>5. OrigBound /\ CacheOPR /\ NetOPR
  BY DEF OrigBound, CacheOPR, NetOPR
<1>. QED  BY <1>4, <1>5 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
  OBVIOUS
<1> USE ConstAssumptions DEF Inv, TypeInv, OrigBound, CacheOPR, NetOPR,
                             Msg, RegStates, DevStates, LinkStates
<1>1. ASSUME NEW d \in DEVICES, NEW to \in RegStates, RegChange(d, to)
      PROVE Inv'
  <2>1. reg[d] # "Revoked"
    BY <1>1 DEF RegChange, RegTransition
  <2>2. CacheOPR'
    BY <1>1, <2>1 DEF RegChange
  <2>3. NetOPR'
    BY <1>1, <2>1 DEF RegChange
  <2>4. TypeInv' /\ OrigBound'
    BY <1>1 DEF RegChange
  <2>. QED  BY <2>2, <2>3, <2>4
<1>2. ASSUME NEW d \in DEVICES, PushNotify(d) PROVE Inv'
  <2>1. PICK t \in 0..MAXT :
          /\ t - now <= SKEW /\ now - t <= SKEW
          /\ net' = net \cup {[dv |-> d, st |-> reg[d], ver |-> regVer[d],
                               orig |-> t]}
    BY <1>2 DEF PushNotify
  <2>2. UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig,
                     sinceRev, now, useCnt, badGrants, link, activeEv >>
    BY <1>2 DEF PushNotify
  <2>. QED  BY <2>1, <2>2
<1>3. ASSUME NEW m \in net, DeliverNotify(m) PROVE Inv'
  <2>1. m \in Msg  OBVIOUS
  <2>2. CASE m.ver > pdpVer[m.dv]
    <3>1. /\ pdpSt'   = [pdpSt   EXCEPT ![m.dv] = m.st]
          /\ pdpVer'  = [pdpVer  EXCEPT ![m.dv] = m.ver]
          /\ pdpAge'  = [pdpAge  EXCEPT ![m.dv] = 0]
          /\ pdpOrig' = [pdpOrig EXCEPT ![m.dv] = m.orig]
          /\ useCnt'  = [useCnt  EXCEPT ![m.dv] = 0]
          /\ net' = net \ {m}
          /\ UNCHANGED << reg, regVer, dev, badGrants, sinceRev, now, link,
                          activeEv >>
      BY <1>3, <2>2 DEF DeliverNotify
    <3>. QED  BY <2>1, <3>1
  <2>3. CASE ~(m.ver > pdpVer[m.dv])
    <3>1. /\ UNCHANGED << pdpSt, pdpVer, pdpAge, pdpOrig, useCnt >>
          /\ net' = net \ {m}
          /\ UNCHANGED << reg, regVer, dev, badGrants, sinceRev, now, link,
                          activeEv >>
      BY <1>3, <2>3 DEF DeliverNotify
    <3>. QED  BY <3>1
  <2>. QED  BY <2>2, <2>3
<1>4. ASSUME NEW m \in net, DropNotify(m) PROVE Inv'
  BY <1>4 DEF DropNotify
<1>5. ASSUME NEW d \in DEVICES, PdpPoll(d) PROVE Inv'
  BY <1>5 DEF PdpPoll
<1>6. ASSUME NEW d \in DEVICES, SyncFromRegistry(d) PROVE Inv'
  <2>1. DevViewOf(reg[d]) \in DevStates
    BY DEF DevViewOf
  <2>. QED  BY <1>6, <2>1 DEF SyncFromRegistry
<1>7. ASSUME NEW d \in DEVICES, NEW e \in EVENTTYPES, ObserveEvent(d, e)
      PROVE Inv'
  BY <1>7 DEF ObserveEvent
<1>8. ASSUME NEW d \in DEVICES, NEW e \in EVENTTYPES, ClearEvent(d, e)
      PROVE Inv'
  BY <1>8 DEF ClearEvent
<1>9. ASSUME NEW d \in DEVICES, RecordAccess(d) PROVE Inv'
  BY <1>9 DEF RecordAccess
<1>10. ASSUME Tick PROVE Inv'
  <2>1. /\ now < MAXT /\ now' = now + 1
        /\ pdpAge' = [d \in DEVICES |->
                        IF pdpAge[d] + 1 > MAXAGE THEN MAXAGE ELSE pdpAge[d] + 1]
        /\ sinceRev' = [d \in DEVICES |->
                          IF reg[d] # "Revoked" THEN sinceRev[d]
                          ELSE IF sinceRev[d] + 1 > MAXAGE THEN MAXAGE
                          ELSE sinceRev[d] + 1]
        /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpOrig, useCnt,
                        badGrants, link, net, activeEv >>
    BY <1>10 DEF Tick
  <2>2. \A d \in DEVICES : sinceRev'[d] \in Nat /\ sinceRev'[d] <= sinceRev[d] + 1
    BY <2>1
  <2>3. TypeInv'  BY <2>1, <2>2
  <2>4. OrigBound'  BY <2>1
  <2>5. CacheOPR'  BY <2>1, <2>2
  <2>6. NetOPR'  BY <2>1, <2>2
  <2>. QED  BY <2>3, <2>4, <2>5, <2>6
<1>11. ASSUME Partition PROVE Inv'
  BY <1>11 DEF Partition
<1>12. ASSUME Heal PROVE Inv'
  BY <1>12 DEF Heal
<1>13. ASSUME UNCHANGED vars PROVE Inv'
  BY <1>13 DEF vars
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
     <1>12, <1>13 DEF Next

\* Under the hypotheses, the rule in force is A8.
LEMMA AllowIsA8 ==
  ASSUME A8Hyp, NEW d \in DEVICES
  PROVE  AllowRule(d) = A8_OriginLease(d)
<1>1. /\ RULE # "A1_Local"      /\ RULE # "A2_PdpCache"
      /\ RULE # "A3_Lease"      /\ RULE # "A4_FailClosed"
      /\ RULE # "A5_LeaseCtx"   /\ RULE # "A6_FailClosedCtx"
      /\ RULE # "A7_CountLease"
  BY DEF A8Hyp
<1>. QED  BY <1>1 DEF AllowRule

\* Proposition 3: the invariant implies bounded revocation under A8.
LEMMA InvS3 == A8Hyp /\ Inv => S3_BoundedRevocation
<1> SUFFICES ASSUME A8Hyp, Inv, NEW d \in DEVICES,
                    reg[d] = "Revoked", sinceRev[d] > LEASE, AllowRule(d)
             PROVE  FALSE
  BY DEF S3_BoundedRevocation
<1>1. A8_OriginLease(d)  BY AllowIsA8
<1>2. pdpSt[d] = "Enrolled" /\ now - pdpOrig[d] <= LEASE - SKEWBOUND
  BY <1>1 DEF A8_OriginLease, RuleHorizon
<1>3. now - pdpOrig[d] + SKEW >= sinceRev[d]
  BY <1>2 DEF Inv, CacheOPR
<1>4. /\ now \in Nat /\ pdpOrig[d] \in Nat /\ sinceRev[d] \in Nat
      /\ LEASE \in Nat /\ SKEW \in Nat /\ SKEWBOUND \in Nat
      /\ SKEWBOUND >= SKEW
  BY ConstAssumptions DEF A8Hyp, Inv, TypeInv
<1>5. sinceRev[d] <= LEASE - SKEWBOUND + SKEW
  BY <1>2, <1>3, <1>4
<1>6. LEASE - SKEWBOUND + SKEW <= LEASE
  BY <1>4
<1>. QED
  BY <1>4, <1>5, <1>6

\* Context denial holds by the definition of A8.
LEMMA InvS5 == A8Hyp /\ Inv => S5_ContextDenial
  BY AllowIsA8 DEF S5_ContextDenial, A8_OriginLease, NoCritical

THEOREM A8BoundedRevocation ==
  A8Hyp => (Spec => [](S3_BoundedRevocation /\ S5_ContextDenial))
<1> SUFFICES ASSUME A8Hyp PROVE Spec => [](S3_BoundedRevocation /\ S5_ContextDenial)
  OBVIOUS
<1>1. Inv => S3_BoundedRevocation /\ S5_ContextDenial
  BY InvS3, InvS5
<1>. QED
  BY InitInv, NextInv, <1>1, PTL DEF Spec
=============================================================================
