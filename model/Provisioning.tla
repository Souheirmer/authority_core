------------------------------- MODULE Provisioning -------------------------------
(***************************************************************************)
(* Decision-time authorization for IoT provisioning.                       *)
(*                                                                         *)
(* Merged replacement for ProvisioningBaseline.tla, Provisioning_Refined_C  *)
(* and Provisioning_EventRefined.tla. ONE module, ONE state space, the      *)
(* authorization rule selected by the RULE constant. This is what makes the *)
(* paper's claim true -- that observed differences arise solely from the    *)
(* structure of the rules.                                                  *)
(*                                                                         *)
(* WHAT CHANGED FROM V1, AND WHY                                           *)
(*                                                                         *)
(* 1. The decision point has its own cache (pdpSt/pdpVer/pdpAge).           *)
(*    V1's AllowRef read reg[d] atomically, which assumes the decision      *)
(*    point can always consult the authoritative registry -- the very       *)
(*    assumption the paper argues is unrealistic. That is why every V1      *)
(*    property turned out logically valid under its own rule.               *)
(*                                                                         *)
(* 2. Properties are stated over reg[d], the ground truth, never over what  *)
(*    the rule observed. This is what makes them falsifiable.               *)
(*                                                                         *)
(* 3. No lastAcc / hasAcc. AllowRule is a pure function of the state, so    *)
(*    correctness is an ordinary state invariant. Removing the decision     *)
(*    record cuts the reachable state space by roughly 50x.                 *)
(*                                                                         *)
(* 4. Propagation can fail, the link can partition, and an adversary acts   *)
(*    at the system level. Cryptography and protocol-level authentication   *)
(*    are assumed sound.                                                    *)
(*                                                                         *)
(* 5. Suspended added to the lifecycle; it catches rules that special-case  *)
(*    only revocation.                                                      *)
(*                                                                         *)
(* WHAT CHANGED IN V3                                                      *)
(*                                                                         *)
(* 6. The `compromised` variable is removed: no rule or property read it.   *)
(*    T3 is expressed by RecordAccess, which fires at adversary-chosen      *)
(*    times while the rule grants. State counts halve as a result.          *)
(*                                                                         *)
(* 7. Bounded clock skew. Notification stamps may err by up to SKEW; polls  *)
(*    are stamped with the decision point's own clock. A8 subtracts the     *)
(*    assumed bound SKEWBOUND from its horizon (RuleHorizon). With          *)
(*    SKEW = SKEWBOUND = 0 the model is the V2 model minus `compromised`.   *)
(*                                                                         *)
(* 8. AVPD, bounded availability under partition, separates lease rules     *)
(*    from fail-closed and count-bounded rules.                             *)
(*                                                                         *)
(* 9. RuleHorizonPlus1 lets a cfg substitute a one-tick-longer horizon      *)
(*    (RuleHorizon <- RuleHorizonPlus1) to check tightness.                 *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  DEVICES,        \* finite set of device identities
  EVENTTYPES,     \* runtime security event types
  CRITICAL,       \* CRITICAL \subseteq EVENTTYPES
  RULE,           \* which authorization rule is under verification
  LEASE,          \* freshness horizon Delta, in ticks
  MAXAGE,         \* saturation bound on the staleness counter
  MAXVER,         \* bound on registry version (keeps the model finite)
  MAXNET,         \* bound on notifications in flight
  MAXUSE,         \* grant budget per cached view (rule A7 only)
  MAXBAD,         \* saturation bound on the damage counter
  MAXT,           \* bound on the global logical clock
  SKEW,           \* actual bound on registry-clock error in a notification stamp
  SKEWBOUND       \* skew bound ASSUMED by the origin-lease rule A8

RuleNames == {"A1_Local", "A2_PdpCache", "A3_Lease", "A4_FailClosed",
              "A5_LeaseCtx", "A6_FailClosedCtx", "A7_CountLease",
              "A8_OriginLease"}

ASSUME ConstAssumptions ==
       /\ DEVICES # {}
       /\ EVENTTYPES # {}
       /\ CRITICAL \subseteq EVENTTYPES
       /\ RULE \in RuleNames
       /\ LEASE \in Nat /\ MAXAGE \in Nat /\ MAXAGE > LEASE
       /\ MAXVER \in Nat /\ MAXNET \in Nat
       /\ MAXUSE \in Nat /\ MAXBAD \in Nat
       /\ MAXT \in Nat /\ MAXT >= MAXAGE
       /\ SKEW \in Nat /\ SKEWBOUND \in Nat /\ SKEWBOUND <= LEASE

RegStates  == {"Absent", "Enrolled", "Suspended", "Revoked"}
DevStates  == {"Unprov", "Prov", "Inv"}
LinkStates == {"Up", "Down"}

VARIABLES
  reg,          \* reg[d]       authoritative registry state -- GROUND TRUTH
  regVer,       \* regVer[d]    monotone version, bumped on every reg change
  dev,          \* dev[d]       device-local cached view
  pdpSt,        \* pdpSt[d]     decision point's cached registry state
  pdpVer,       \* pdpVer[d]    version that cache was derived from
  pdpAge,       \* pdpAge[d]    ticks since that cache was WRITTEN
  pdpOrig,      \* pdpOrig[d]   clock value at which that data was OBSERVED
                \*              at the registry -- not the same thing
  sinceRev,     \* sinceRev[d]  ticks since reg[d] became Revoked
  now,          \* global logical clock
  useCnt,       \* useCnt[d]    grants issued against the current cached view
  badGrants,    \* badGrants[d] grants issued while NOT legitimately enrolled
  link,         \* decision point <-> registry reachability
  net,          \* revocation notifications in flight
  activeEv      \* activeEv[d]  active runtime events

vars == << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
           useCnt, badGrants, link, net, activeEv >>

\* A notification carries the time its content was observed.
Notification == [dv: DEVICES, st: RegStates, ver: 0..MAXVER, orig: 0..MAXT]

\* The set of channel states, enumerated directly.
\*
\* Writing this as  net \in SUBSET Notification /\ Cardinality(net) <= MAXNET
\* is equivalent, but TLC evaluates the conjuncts left to right: it builds the
\* full powerset and only then applies the cardinality filter. With 24 possible
\* notifications that is 2^24 subsets enumerated for every candidate state,
\* which makes INIT IndInv infeasible. Enumerating the valid channel states
\* directly reduces it to |Notification| + 1.
\*
\* This form assumes MAXNET = 1. Raising it requires adding the corresponding
\* pair-set term, which grows quadratically but remains tractable.
NetStates == {{}} \cup {{m} : m \in Notification}

TypeOK ==
  /\ reg         \in [DEVICES -> RegStates]
  /\ regVer      \in [DEVICES -> 0..MAXVER]
  /\ dev         \in [DEVICES -> DevStates]
  /\ pdpSt       \in [DEVICES -> RegStates]
  /\ pdpVer      \in [DEVICES -> 0..MAXVER]
  /\ pdpAge      \in [DEVICES -> 0..MAXAGE]
  /\ pdpOrig     \in [DEVICES -> 0..MAXT]
  /\ sinceRev    \in [DEVICES -> 0..MAXAGE]
  /\ now         \in 0..MAXT
  /\ useCnt      \in [DEVICES -> 0..MAXUSE]
  /\ badGrants   \in [DEVICES -> 0..MAXBAD]
  /\ link        \in LinkStates
  \* NetStates rather than SUBSET Notification: see the comment on NetStates.
  \* This is what makes INIT IndInv feasible at all.
  /\ net         \in NetStates
  /\ activeEv    \in [DEVICES -> SUBSET EVENTTYPES]

Init ==
  /\ reg         = [d \in DEVICES |-> "Absent"]
  /\ regVer      = [d \in DEVICES |-> 0]
  /\ dev         = [d \in DEVICES |-> "Unprov"]
  /\ pdpSt       = [d \in DEVICES |-> "Absent"]
  /\ pdpVer      = [d \in DEVICES |-> 0]
  /\ pdpAge      = [d \in DEVICES |-> 0]
  /\ pdpOrig     = [d \in DEVICES |-> 0]
  /\ sinceRev    = [d \in DEVICES |-> 0]
  /\ now         = 0
  /\ useCnt      = [d \in DEVICES |-> 0]
  /\ badGrants   = [d \in DEVICES |-> 0]
  /\ link        = "Up"
  /\ net         = {}
  /\ activeEv    = [d \in DEVICES |-> {}]

(***************************************************************************)
(* AUTHORIZATION RULES                                                     *)
(*                                                                         *)
(* Each is a pure function of the current state. A1 is the V1 baseline;     *)
(* A4 is the V1 "refined" rule, retained not as a solution but as the       *)
(* safety-maximal extreme whose availability cost Theorem 1 makes explicit. *)
(***************************************************************************)

NoCritical(d) == (activeEv[d] \cap CRITICAL) = {}

A1_Local(d)         == dev[d] = "Prov"
A2_PdpCache(d)      == pdpSt[d] = "Enrolled"
A3_Lease(d)         == pdpSt[d] = "Enrolled" /\ pdpAge[d] <= LEASE
A4_FailClosed(d)    == link = "Up" /\ reg[d] = "Enrolled"
A5_LeaseCtx(d)      == A3_Lease(d) /\ NoCritical(d)
A6_FailClosedCtx(d) == A4_FailClosed(d) /\ NoCritical(d)

\* Count-bounded lease: staleness bounded by number of grants, not by time.
\* Damage is then independent of request rate -- unlike A3, whose exposure
\* grows with request velocity within the same window.
A7_CountLease(d)    == /\ pdpSt[d] = "Enrolled"
                       /\ useCnt[d] < MAXUSE
                       /\ NoCritical(d)

\* A8  Origin-based lease. Freshness is measured from the time the cached
\*     data was OBSERVED AT THE REGISTRY, not from the time it was written
\*     into the cache. A3 gets this wrong: a delayed notification renews the
\*     lease while carrying obsolete content. See DISCOVERY in V2_NOTES.md --
\*     this was found by the model checker, not by inspection.
\*
\*     With bounded clock skew the registry's stamp may run up to SKEW ticks
\*     ahead of the decision point's clock, so the rule must subtract the skew
\*     bound it assumes. RuleHorizon is a separate definition so that a model
\*     configuration can substitute RuleHorizonPlus1 and test tightness.
RuleHorizon      == LEASE - SKEWBOUND
RuleHorizonPlus1 == LEASE - SKEWBOUND + 1

A8_OriginLease(d)   == /\ pdpSt[d] = "Enrolled"
                       /\ (now - pdpOrig[d]) <= RuleHorizon
                       /\ NoCritical(d)

AllowRule(d) ==
  CASE RULE = "A1_Local"         -> A1_Local(d)
    [] RULE = "A2_PdpCache"      -> A2_PdpCache(d)
    [] RULE = "A3_Lease"         -> A3_Lease(d)
    [] RULE = "A4_FailClosed"    -> A4_FailClosed(d)
    [] RULE = "A5_LeaseCtx"      -> A5_LeaseCtx(d)
    [] RULE = "A6_FailClosedCtx" -> A6_FailClosedCtx(d)
    [] RULE = "A7_CountLease"    -> A7_CountLease(d)
    [] OTHER                     -> A8_OriginLease(d)

(***************************************************************************)
(* REGISTRY LIFECYCLE                                                      *)
(***************************************************************************)

RegTransition(from, to) ==
  \/ (from = "Absent"    /\ to = "Enrolled")
  \/ (from = "Enrolled"  /\ to \in {"Suspended", "Revoked"})
  \/ (from = "Suspended" /\ to \in {"Enrolled", "Revoked"})

RegChange(d, to) ==
  /\ regVer[d] < MAXVER
  /\ RegTransition(reg[d], to)
  /\ reg'    = [reg    EXCEPT ![d] = to]
  /\ regVer' = [regVer EXCEPT ![d] = regVer[d] + 1]
  /\ sinceRev' = [sinceRev EXCEPT ![d] = IF to = "Revoked" THEN 0 ELSE @]
  /\ UNCHANGED << dev, pdpSt, pdpVer, pdpAge, pdpOrig, useCnt,
                  badGrants, link, net, activeEv, now >>

Enroll(d) == RegChange(d, "Enrolled")
Suspend(d) == RegChange(d, "Suspended")
Revoke(d) == RegChange(d, "Revoked")

(***************************************************************************)
(* PROPAGATION TO THE DECISION POINT                                       *)
(***************************************************************************)

PushNotify(d) ==
  /\ link = "Up"
  /\ Cardinality(net) < MAXNET
  \* The stamp is set by the registry's clock, which may differ from the
  \* decision point's clock (now) by up to SKEW ticks in either direction.
  /\ \E t \in 0..MAXT :
       /\ t - now <= SKEW /\ now - t <= SKEW
       /\ net' = net \cup {[dv |-> d, st |-> reg[d], ver |-> regVer[d],
                            orig |-> t]}
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  useCnt, badGrants, link, activeEv >>

\* Monotonic reads: a notification older than the cache is discarded.
DeliverNotify(m) ==
  /\ m \in net
  /\ net' = net \ {m}
  /\ IF m.ver > pdpVer[m.dv]
       THEN /\ pdpSt'  = [pdpSt  EXCEPT ![m.dv] = m.st]
            /\ pdpVer' = [pdpVer EXCEPT ![m.dv] = m.ver]
            /\ pdpAge' = [pdpAge EXCEPT ![m.dv] = 0]
            \* the ORIGIN travels with the data; it is not reset on write
            /\ pdpOrig' = [pdpOrig EXCEPT ![m.dv] = m.orig]
            /\ useCnt' = [useCnt EXCEPT ![m.dv] = 0]
       ELSE UNCHANGED << pdpSt, pdpVer, pdpAge, pdpOrig, useCnt >>
  /\ UNCHANGED << reg, regVer, dev, badGrants, sinceRev, now, link, activeEv >>

\* ADVERSARY: silently drop a revocation notification.
DropNotify(m) ==
  /\ m \in net
  /\ net' = net \ {m}
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  useCnt, badGrants, link, activeEv >>

\* Synchronous query. Requires reachability -- this is the crucial constraint.
PdpPoll(d) ==
  /\ link = "Up"
  /\ pdpSt'  = [pdpSt  EXCEPT ![d] = reg[d]]
  /\ pdpVer' = [pdpVer EXCEPT ![d] = regVer[d]]
  /\ pdpAge' = [pdpAge EXCEPT ![d] = 0]
  \* Stamped with the decision point's OWN clock at the moment it issues the
  \* query. This needs no clock synchronization: the answer reflects registry
  \* state no older than the send time.
  /\ pdpOrig' = [pdpOrig EXCEPT ![d] = now]
  /\ useCnt' = [useCnt EXCEPT ![d] = 0]
  /\ UNCHANGED << reg, regVer, dev, badGrants, sinceRev, now, link, net,
                  activeEv >>

(***************************************************************************)
(* DEVICE CACHE, EVENTS, CLOCK, PARTITION, COMPROMISE                      *)
(***************************************************************************)

DevViewOf(r) ==
  CASE r = "Enrolled"  -> "Prov"
    [] r = "Revoked"   -> "Inv"
    [] r = "Suspended" -> "Inv"
    [] OTHER           -> "Unprov"

SyncFromRegistry(d) ==
  /\ dev' = [dev EXCEPT ![d] = DevViewOf(reg[d])]
  /\ UNCHANGED << reg, regVer, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  useCnt, badGrants, link, net, activeEv >>

ObserveEvent(d, e) ==
  /\ e \in EVENTTYPES
  /\ e \notin activeEv[d]
  /\ activeEv' = [activeEv EXCEPT ![d] = @ \cup {e}]
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  useCnt, badGrants, link, net >>

ClearEvent(d, e) ==
  /\ e \in activeEv[d]
  /\ activeEv' = [activeEv EXCEPT ![d] = @ \ {e}]
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  useCnt, badGrants, link, net >>

\* Logical clock. Cached views age; the counter saturates.
Tick ==
  /\ now < MAXT
  /\ now' = now + 1
  /\ pdpAge' = [d \in DEVICES |->
                  IF pdpAge[d] + 1 > MAXAGE THEN MAXAGE ELSE pdpAge[d] + 1]
  /\ sinceRev' = [d \in DEVICES |->
                    IF reg[d] # "Revoked" THEN sinceRev[d]
                    ELSE IF sinceRev[d] + 1 > MAXAGE THEN MAXAGE
                    ELSE sinceRev[d] + 1]
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpOrig, useCnt, badGrants,
                  link, net, activeEv >>

\* ADVERSARY: partition the decision point from the registry, and heal.
Partition ==
  /\ link = "Up" /\ link' = "Down"
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  useCnt, badGrants, net, activeEv >>

Heal ==
  /\ link = "Down" /\ link' = "Up"
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  useCnt, badGrants, net, activeEv >>

\* Post-enrollment compromise (threat T3) needs no state variable. A device
\* under adversary control holds valid credentials and follows the protocol, so
\* no rule can observe the takeover; the adversary's control is expressed by
\* RecordAccess, which may fire at any time and at any rate while the rule
\* grants. An earlier version carried a set of taken-over devices that no rule
\* or property ever read; it has been removed.

(***************************************************************************)
(* ACCESS                                                                  *)
(*                                                                         *)
(* Authorization itself is a state function and needs no action. This       *)
(* transition models an access being PERFORMED, which consumes grant budget *)
(* and, when the device is not legitimately enrolled, accrues damage.       *)
(* Only rule A7 and property S7 depend on it.                              *)
(***************************************************************************)

RecordAccess(d) ==
  /\ AllowRule(d)
  /\ useCnt' = [useCnt EXCEPT ![d] =
                  IF useCnt[d] + 1 > MAXUSE THEN MAXUSE ELSE useCnt[d] + 1]
  /\ badGrants' = [badGrants EXCEPT ![d] =
                     IF reg[d] = "Enrolled" \/ badGrants[d] = MAXBAD
                       THEN badGrants[d] ELSE badGrants[d] + 1]
  /\ UNCHANGED << reg, regVer, dev, pdpSt, pdpVer, pdpAge, pdpOrig, sinceRev, now,
                  link, net, activeEv >>

Next ==
  \/ \E d \in DEVICES, to \in RegStates : RegChange(d, to)
  \/ \E d \in DEVICES : PushNotify(d)
  \/ \E m \in net      : DeliverNotify(m)
  \/ \E m \in net      : DropNotify(m)
  \/ \E d \in DEVICES : PdpPoll(d)
  \/ \E d \in DEVICES : SyncFromRegistry(d)
  \/ \E d \in DEVICES, e \in EVENTTYPES : ObserveEvent(d, e)
  \/ \E d \in DEVICES, e \in EVENTTYPES : ClearEvent(d, e)
  \/ \E d \in DEVICES : RecordAccess(d)
  \/ Tick
  \/ Partition
  \/ Heal

\* Fairness. Each conjunct is an assumption about the environment, and the
\* first two were missing from an earlier version of this specification: TLC
\* returned a behaviour in which the registry emitted a revocation, the
\* adversary partitioned the link and dropped the notification, healed, and
\* repeated forever, while the clock stood still and the lease never expired.
\*
\*   WF_vars(Tick)      time passes. Physically trivial, but it is an
\*                      assumption and the lease argument depends on it.
\*   SF_vars(PdpPoll)   a poll eventually succeeds if the link is up
\*                      INFINITELY OFTEN. Weak fairness is insufficient: it
\*                      fires only when an action is CONTINUOUSLY enabled, and
\*                      an adversary alternating Partition and Heal keeps
\*                      PdpPoll perpetually enabled-then-disabled. "The link
\*                      eventually heals" does not suffice for bounded
\*                      revocation; "the link is repeatedly up, and a poll
\*                      eventually completes when it is" does.
Fairness ==
  /\ WF_vars(Tick)
  /\ \A d \in DEVICES : SF_vars(PdpPoll(d))
  /\ \A d \in DEVICES : WF_vars(SyncFromRegistry(d))
  /\ WF_vars(Heal)

\* Device identities are interchangeable, so TLC may reduce by permutation.
\* Sound for the safety invariants only; never use it for liveness checking.
DeviceSymmetry == Permutations(DEVICES)

Spec     == Init /\ [][Next]_vars
FairSpec == Init /\ [][Next]_vars /\ Fairness

\* Fairness ablations.
\*
\* That L1 holds under Fairness is less informative than knowing WHICH conjunct
\* carries it. Each variant below weakens exactly one assumption, so a pass/fail
\* pair isolates its contribution. Expected outcomes are stated; they are
\* predictions to be checked, not results.
\*
\*   WeakPoll  poll fairness demoted SF -> WF.  Expect L1 to FAIL: an adversary
\*             alternating Partition and Heal keeps PdpPoll enabled infinitely
\*             often but never continuously, and weak fairness never fires.
\*
\*   NoTick    clock fairness removed.  Expect L1 to HOLD, which is the point:
\*             revocation binds in this model because a poll eventually
\*             succeeds, not because a lease expires.
\*
\*   NoHeal    link-recovery fairness removed.  Expect L1 to FAIL. With the link
\*             down forever no poll is possible, so only lease expiry could
\*             deny -- and a bounded clock cannot supply it. The counterexample
\*             should sit at now = MAXT. This is a bound of the model, not a
\*             defect of the rule, and it marks the limit of what bounded
\*             model checking can say about the lease argument.
\*
\*   Clearing  adds fairness on ClearEvent. Needed for L2: nothing otherwise
\*             compels a critical condition to end, and a device held in a
\*             tamper state is correctly never re-authorized.

FairSpec_WeakPoll ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(Tick)
  /\ \A d \in DEVICES : WF_vars(PdpPoll(d))
  /\ \A d \in DEVICES : WF_vars(SyncFromRegistry(d))
  /\ WF_vars(Heal)

FairSpec_NoTick ==
  /\ Init /\ [][Next]_vars
  /\ \A d \in DEVICES : SF_vars(PdpPoll(d))
  /\ \A d \in DEVICES : WF_vars(SyncFromRegistry(d))
  /\ WF_vars(Heal)

FairSpec_NoHeal ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(Tick)
  /\ \A d \in DEVICES : SF_vars(PdpPoll(d))
  /\ \A d \in DEVICES : WF_vars(SyncFromRegistry(d))

FairSpec_Clearing ==
  /\ FairSpec
  /\ \A d \in DEVICES, e \in EVENTTYPES : WF_vars(ClearEvent(d, e))

(***************************************************************************)
(* SECURITY REQUIREMENTS                                                   *)
(*                                                                         *)
(* Every property below is stated over reg[d] -- the authoritative state.   *)
(* None is stated over what the rule observed. Run mutation testing (swap   *)
(* RULE) to confirm each can fail.                                          *)
(***************************************************************************)

\* S1  A grant implies the device really is enrolled.
S1_AuthoritativeSoundness ==
  \A d \in DEVICES : AllowRule(d) => (reg[d] = "Enrolled")

\* S2  Immediate revocation. Theorem 1: unachievable together with AVP.
S2_ImmediateRevocation ==
  \A d \in DEVICES : (reg[d] = "Revoked") => ~AllowRule(d)

\* S3  Bounded revocation, horizon LEASE. The achievable weakening of S2.
\* Stated over time since REVOCATION, not over cache age. Phrasing it in
\* terms of pdpAge would make it valid by construction for any lease rule --
\* the V1 mistake in miniature.
S3_BoundedRevocation ==
  \A d \in DEVICES :
    ((reg[d] = "Revoked") /\ (sinceRev[d] > LEASE)) => ~AllowRule(d)

S4_DenyAbsent ==
  \A d \in DEVICES : (reg[d] = "Absent") => ~AllowRule(d)

S5_ContextDenial ==
  \A d \in DEVICES : ((activeEv[d] \cap CRITICAL) # {}) => ~AllowRule(d)

S6_DenySuspended ==
  \A d \in DEVICES : (reg[d] = "Suspended") => ~AllowRule(d)

\* S7  Damage bound: how many grants can be issued while not legitimately
\*     enrolled. Holds for A7 with bound MAXUSE, independent of request rate.
\*     Fails for the time-bounded rules, whose exposure grows with velocity.
S7_DamageBounded ==
  \A d \in DEVICES : badGrants[d] < MAXBAD

\* Fixed-threshold variants, used to measure how the damage A7 admits grows
\* with the number of cache rewrites the bounds permit (MAXVER, MAXNET).
DamageBelow2 == \A d \in DEVICES : badGrants[d] < 2
DamageBelow3 == \A d \in DEVICES : badGrants[d] < 3

(***************************************************************************)
(* AVAILABILITY                                                            *)
(*                                                                         *)
(* Without these, every safety property is satisfied by a rule that denies  *)
(* everything, and the analysis is degenerate.                             *)
(***************************************************************************)

AV_Availability ==
  \A d \in DEVICES :
    ((link = "Up") /\ (reg[d] = "Enrolled") /\ NoCritical(d)) => AllowRule(d)

\* AVP  S2 /\ AVP is unsatisfiable. This is Theorem 1.
AVP_AvailUnderPartition ==
  \A d \in DEVICES :
    ((reg[d] = "Enrolled") /\ NoCritical(d)) => AllowRule(d)

\* AVPD  Bounded availability under partition. If the decision point holds the
\*       CURRENT authoritative state of an enrolled device, observed within
\*       the guaranteed horizon, it must grant -- whether or not the link is up.
\*       This is the availability a lease buys and a fail-closed rule gives up.
\*       The horizon shrinks by the assumed skew bound: that is the
\*       availability cost of tolerating unsynchronized clocks.
AVPD_BoundedAvailUnderPartition ==
  \A d \in DEVICES :
    (/\ reg[d] = "Enrolled" /\ NoCritical(d)
     /\ pdpVer[d] = regVer[d]
     /\ (now - pdpOrig[d]) <= LEASE - SKEWBOUND) => AllowRule(d)

\* The safety properties the origin-lease rule A8 attains. S1 and S6 are
\* deliberately excluded: A8 violates both, and necessarily so.
\*   S1 fails because any cache-based rule may grant while the authoritative
\*      state has already changed -- that is what bounded revocation weakens.
\*   S6 fails because sinceRev tracks only revocation, so suspension has no
\*      corresponding horizon. Adding sinceSusp would let S6 be weakened the
\*      same way S3 weakens S2; we have not done so.
Safety == S3_BoundedRevocation /\ S4_DenyAbsent /\ S5_ContextDenial

(***************************************************************************)
(* LIVENESS  (require FairSpec, and disable SYMMETRY -- TLC's symmetry     *)
(* reduction is unsound for liveness checking)                             *)
(***************************************************************************)

L1_RevocationEventuallyBinds ==
  \A d \in DEVICES : (reg[d] = "Revoked") ~> [](~AllowRule(d))

L2_AvailabilityRestored ==
  \A d \in DEVICES :
    ((reg[d] = "Enrolled") /\ NoCritical(d)) ~> AllowRule(d)

(***************************************************************************)
(* INDUCTIVE INVARIANT                                                     *)
(*                                                                         *)
(* Checked with  INIT IndInv / NEXT Next / INVARIANT IndInv  (see           *)
(* IndInv.cfg). With Init => IndInv and IndInv => Safety this establishes   *)
(* Safety for an ARBITRARY number of devices, replacing V1's bounded        *)
(* |DEVICES| = 4 argument.                                                  *)
(*                                                                         *)
(* Expect TLC to reject the first version and hand back a two-state trace   *)
(* showing which conjunct is too weak. Strengthening in that loop is the    *)
(* normal way to find the invariant.                                        *)
(***************************************************************************)

CacheNotAheadOfRegistry ==
  \A d \in DEVICES : pdpVer[d] <= regVer[d]

\* Each lifecycle state implies a minimum version, because the version counts
\* transitions and the lifecycle is Absent -> Enrolled -> {Suspended, Revoked}.
\* Pinning only version 0 is not enough: TLC found a state with reg = Suspended
\* at version 1, from which DeliverNotify broke FreshCacheSound.
LifecycleVersion(st, v) ==
  /\ (st = "Absent")    <=> (v = 0)
  /\ (st = "Enrolled")  => (v >= 1)
  /\ (st = "Suspended") => (v >= 2)
  /\ (st = "Revoked")   => (v >= 2)

RegistryVersionConsistent ==
  \A d \in DEVICES : LifecycleVersion(reg[d], regVer[d])

\* The cache holds a state the registry once held, so the same relation binds.
CacheVersionConsistent ==
  \A d \in DEVICES : LifecycleVersion(pdpSt[d], pdpVer[d])

\* And so does data still in flight.
NotificationVersionConsistent ==
  \A m \in net : LifecycleVersion(m.st, m.ver)

\* A version bound alone is too weak. TLC found a message reporting
\* <<Enrolled, v2>> while the registry stood at <<Suspended, v2>>: version 2 is
\* reached BY LEAVING Enrolled, so no artifact stamped v2 can report it.
\* The relation that captures this without reconstructing history is that
\* anything stamped with the CURRENT version must report the CURRENT state.
\* Older stamps are unconstrained by the present, which is exactly the
\* staleness the model is about.
CacheMatchesCurrentVersion ==
  \A d \in DEVICES : (pdpVer[d] = regVer[d]) => (pdpSt[d] = reg[d])

NotificationMatchesCurrentVersion ==
  \A m \in net : (m.ver = regVer[m.dv]) => (m.st = reg[m.dv])

\* Nothing was observed in the future, and nothing has been ageing for longer
\* than the clock has run. Omitting this admits a cache stamped pdpOrig = 1
\* while now = 0, which makes now - pdpOrig negative and breaks the origin
\* ordering below. That was the second counterexample TLC returned.
ClockCoherence ==
  /\ \A d \in DEVICES : pdpOrig[d]  <= now + SKEW
  /\ \A d \in DEVICES : pdpAge[d]   <= now
  /\ \A d \in DEVICES : sinceRev[d] <= now

\* The same discipline for data still in flight.
NotificationOriginBounded ==
  \A m \in net : m.orig <= now + SKEW

\* A message reporting enrollment was created before any revocation of that
\* device, so its age already exceeds the time since revocation. This is the
\* in-flight analogue of OriginPrecedesRevocation, and is what preserves that
\* conjunct across DeliverNotify.
NotificationPrecedesRevocation ==
  \A m \in net :
    (m.st = "Enrolled" /\ reg[m.dv] = "Revoked")
      => (now - m.orig) + SKEW >= sinceRev[m.dv]

NotificationsWellFormed ==
  \A m \in net : m.ver <= regVer[m.dv]

FreshCacheSound ==
  \A d \in DEVICES :
    (pdpSt[d] = "Enrolled" /\ pdpAge[d] <= LEASE)
      => (reg[d] = "Enrolled" \/ regVer[d] > pdpVer[d])

\* The key fact A8 depends on: if the cache says Enrolled, the data was
\* observed no later than the moment of revocation.
OriginPrecedesRevocation ==
  \A d \in DEVICES :
    (pdpSt[d] = "Enrolled" /\ reg[d] = "Revoked")
      => (now - pdpOrig[d]) + SKEW >= sinceRev[d]

IndInv ==
  /\ TypeOK
  /\ CacheNotAheadOfRegistry
  /\ RegistryVersionConsistent
  /\ CacheVersionConsistent
  /\ NotificationVersionConsistent
  /\ CacheMatchesCurrentVersion
  /\ NotificationMatchesCurrentVersion
  /\ ClockCoherence
  /\ NotificationsWellFormed
  /\ NotificationOriginBounded
  /\ NotificationPrecedesRevocation
  /\ FreshCacheSound
  /\ OriginPrecedesRevocation

===================================================================================
