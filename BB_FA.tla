--------------------------------- MODULE BB_FA ---------------------------------
EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems

(***************************************************************************
    SPECIFICATION
  ***************************************************************************)
--------------------------------------------------------------------------------
(* *** Set up *)
CONSTANT W,            \* Uninterpreted set of BB contents, except that it contains a phase, see below
         B0,           \* A fixed, initial BB content in W
         extendsB(_,_),\* Extension relation (will be axiomatized, could be interpretted as \subseteq)
         peersH,       \* Set of Honest BB peers
         peersD,       \* Set of Dishonest (malicious) BB peers
         readers,      \* Set of readers
         threshold,    \* threshold \gamma
         n,            \* total number of peers (in peersH \cup peersD)
         nh,           \* number of honest peers (in peersH)
         pf            \* final phase (in Nat)

VARIABLE fr,    \* [readers -> SUBSET(W)]: For each reader, set of BB contents that have been read through Read-nonFinal
         nfr,   \* [readers -> SUBSET(W)]: For each reader, set of BB contents that have been read through Read-Final 
         Pv,    \* [peersH -> W]: For each honest BB peer, its curent view (BB content)
         signed \* [peers -> SUBSET W]: Set of BB contents that have been signed by each peer

(* *** Assumptions *)
Phases == 1..pf        \* Set of all the phases
Wb == {B[1] : B \in W} \* We eventually assume that elements in W are in Wb \times Phases
peers == peersH \cup peersD
\* We assume that extends(.,.) is transitive, reflexive, and anti-symmetric.            
ExtendsOK == /\ \A B1,B2,B3 \in Wb: extendsB(B1,B2) /\ extendsB(B2,B3) => extendsB(B1,B3)
             /\ \A B \in Wb: extendsB(B,B)
             /\ \A B1,B2 \in Wb: extendsB(B1,B2) /\ extendsB(B2,B1) => B1 = B2
\* We assume threshold meets the conditions of \gamma, see the paper
ThresholdOK == /\ threshold \in Nat     \* threshold is a natural number
               /\ nh > 2*(n-threshold)  \* \gamma requirement (sanity check: TLC finds an attack without this)
               /\ threshold <= n        \* thereshold cannot be greater than the number of peers
WOK == /\ W \subseteq Wb \X Phases      \* BB contents are represented as a content in Wb with a phase in Phases
       /\ B0 \in W                      \* the initial BB content is in W
       /\ B0[2] = 1                     \* and has 1 as phase: the initial phase
       /\ \A B1,B2 \in W: B1[1] = B2[1] => B1 = B2 \* equally of BB contents implies equality of their phases
PeersOK == /\ n \in Nat /\ nh \in Nat
           /\ IsFiniteSet(peersD) /\ IsFiniteSet(peersH)
           /\ nh = Cardinality(peersH)  \* nh is the number of honest peers (in peersH)
           /\ n = Cardinality(peers)    \* n is the number of all peers (in peersH \cup peersD)
           /\ peersH \cap peersD = {}   \* a peers is honest XOR dishonest (malicious)
PhasesOK == /\ pf \in Nat               \* there is a final phase
            /\ pf > 1                   \* which is not the initial phase (1)
ASSUME ExtendsOK
ASSUME ThresholdOK
ASSUME WOK
ASSUME PeersOK
ASSUME PhasesOK

(* *** Type correctness invariant *)
TypeOK == /\ fr  \in [readers -> SUBSET W]
          /\ nfr \in [readers -> SUBSET W]
          /\ Pv \in [peersH -> W]
          /\ signed \in [peers -> SUBSET W]

(* *** Helping functions *)
phase(B) == B[2]                          \* Phase of a BB content
extends(B1, B2) == extendsB(B1[1], B2[1]) \* Lift extendsB to W

     --------------------

(* *** Inital states specification *)
Init == /\ fr  = [r \in readers |-> {} ]
        /\ nfr = [r \in readers |-> {} ]
        /\ Pv  = [P \in peersH |-> B0]  \* the initial honest peers's view is B0
        /\ signed = [P \in peers |-> {} ]
                     
(* *** Guards *)
\* The GuR guard expresses the main condition that readers check when reading BB contents
GuR(B) == \E peersS \in SUBSET peers:
              /\ Cardinality(peersS) >= threshold
              /\ \A P \in peersS: B \in signed[P]

(* *** Events *)
\* UpdatePH: An honest BB peer updates his view (to bu) and must follow the specification
UpdatePH == \E P \in peersH: \E bu \in W:   
                 /\ extends(Pv[P], bu)      \* this encodes the restriction on \cup_B; i.e., extends(B,B \union B') 
                 /\ phase(Pv[P]) # pf       \* no more update once a final BB content has been reached
                 /\ Pv' = [Pv EXCEPT ![P] = bu ]
                 /\ UNCHANGED << fr,nfr,signed >>

\* SignPH: An honest BB peer signs a content (bs) computed from partial() and his view. He must follow the specification.
SignPH == \E P \in peersH: \E bs \in W:
 \* The following conjunct encodes the restrictions on partial: e.g., \A b' \in partial(b): extends(b',b). It is a strict generalization.
                /\ extends(bs, Pv[P]) /\ phase(bs) = phase(Pv[P])
                /\ (phase(Pv[P]) = pf => bs = Pv[P])
                /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
                /\ UNCHANGED << fr,nfr,Pv>>

\* SignPD: An dishonest BB peer can sign ANY content (bs) since he does not have to follow the specification.
SignPD == \E P \in peersD: \E bs \in W:
                /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
                /\ UNCHANGED << fr,nfr,Pv>>
                               
\* ReadNonFinal: A reader reads through Read-NonFinal and obtains bu. There is no explicit label w.l.o.g. (see above).
ReadNonFinal == \E bu \in W: \E R \in readers: \E p \in Nat:
                 /\ GuR(bu)               \* this is the test that each reader performs when reading
                 /\ p = phase(bu)         \* additionally, the reader checks that the read BB contents has the requested phase p
                 /\ nfr' = [nfr EXCEPT ![R] = nfr[R] \union {bu}]
                 /\ UNCHANGED << fr,Pv,signed >>

\* ReadFinal: A reader reads through Read-Final.
ReadFinal == \E bu \in W: \E R \in readers:
                 /\ GuR(bu)               \* this is the test that each reader performs when reading
                 /\ phase(bu) = pf        \* additionally, the reader checks that the read BB contents has the phase pf
                 /\ fr' = [fr EXCEPT ![R] = fr[R] \union {bu}]
                 /\ UNCHANGED << nfr,Pv,signed >>

(* *** State evolutions specification *)
Next == \/ UpdatePH
        \/ SignPH
        \/ SignPD
        \/ ReadNonFinal
        \/ ReadFinal
         
(* *** The protocol is defined with Init describing initial states and with Next describing state evolutions (plus stuttering steps). *)
Protocol == Init /\ [][Next]_<<fr,nfr,Pv,signed>>

(* *** We prove below that final-agreement (FA) is an invariant of Spec. FA is encoded as follows (see FA). *)
BSfr == UNION {fr[R]: R \in readers}                   \* set of all final read BB contents
BSnfr == UNION {nfr[R]: R \in readers}                 \* set of all read BB contents
FA == /\ (BSfr = {}  \/  \E Bf \in BSfr: BSfr = {Bf})  \* FA (i)
      /\ \A Bf \in BSfr: \A B \in BSnfr: extends(B,Bf) \* FA (ii)


--------------------------------------------------------------------------------
\*                          PROOFS                                                                                                     .                      
--------------------------------------------------------------------------------

(***************************************************************************
PROPERTY STATEMENTS
 ***************************************************************************)
 --------------------------------------------------------------------------------
(* Parametrized FA (will help w.r.t. modularity) *)
FA_param(FR,NFR) == /\ (FR = {}  \/  \E Bf \in FR: FR = {Bf})
                    /\ \A Bf \in FR: \A B \in NFR: extends(B,Bf)
FinalW == {B \in W: phase(B) = pf}     \* BB contents having the final phase pf
NFRP(P) == signed[P] \cup { Pv[P] }    \* non-final content from a peer's perspective (P)
FRP(P) == NFRP(P) \cap FinalW          \* final content from a peer's perspective (P)

(* *** Key invariants and properties for the final proof *)
(* (for LEMMA 2) [Invariant] Honest peers locally enforce FC *)
PeersLocalFC ==
  \A P \in peersH: /\ \A B \in signed[P]: extends(B,Pv[P])
                   /\ \A B \in FRP(P): B = Pv[P]
                   
(* (for LEMMA 3) [Invariant] Honest peers locally enforce FA *)
PeersLocalFA ==
  \A P \in peersH: FA_param(FRP(P),
                            NFRP(P))

(* (for LEMMA 4,7) [Invariant] Any reader's read enforces GuR and phase restriction *)
ReadersLocalGu ==
  \A R \in readers: /\ \A B \in nfr[R]: GuR(B)
                    /\ \A B \in fr[R]: GuR(B) /\ phase(B) = pf

(* (for LEMMA 1) Threshold asumptions make it so that there always is an honest peer in two valid sets of peers *)
IntersecPeers ==
  \A peersS1, peersS2 \in SUBSET peers:
      (/\ Cardinality(peersS1) >= threshold
       /\ Cardinality(peersS2) >= threshold
      ) => \E Ph \in (peersS1 \cap peersS2 \cap peersH): TRUE  \* this gives us some honest peer Ph in the intersection

(* (for LEMMA 5-7) [Invariant] Any final BB read content extends any other read BB content. *)
ReaderAgreement ==
  \A R1, R2 \in readers:
      \A B1 \in (BSfr \cup BSnfr):
      \A B2 \in BSfr: extends(B1, B2)

(* *** Basic and simple invariants *)
Inv1 == TypeOK
InvGuPreservation == \A B \in W: (Inv1 /\ GuR(B) /\ [Next]_<<fr,nfr,Pv,signed>> => GuR(B)')


(***************************************************************************
                    CLAIMS AND PROOFS
 ***************************************************************************)   
 --------------------------------------------------------------------------------
(*** Basic properties *)
PROPOSITION eqSingleton == ASSUME NEW S1 \in SUBSET W, NEW S2 \in SUBSET W, NEW B1 \in S1, NEW B2 \in S2 PROVE (\E Bf \in W: S1 = {Bf} /\ S2 = {Bf}) => B1 = B2
    OBVIOUS
PROPOSITION antiSymEx == ASSUME NEW B1 \in W, NEW B2 \in W, extends(B1,B2), extends(B2,B1) PROVE B1 = B2
 BY ExtendsOK, WOK DEF ExtendsOK, extends, Wb, WOK
PROPOSITION equSets == ASSUME NEW BS1 \in SUBSET W, NEW BS2 \in SUBSET W PROVE (BS1 # {} /\ BS2 # {} /\ \A B1 \in BS1: \A B2 \in BS2: B1 = B2) => BS1 = BS2
  <1> SUFFICES ASSUME BS1 # {} /\ BS2 # {} /\ \A B1 \in BS1: \A B2 \in BS2: B1 = B2
               PROVE  BS1 = BS2
    OBVIOUS 
 <1>1 \A B1 \in BS1: B1 \in BS2 OBVIOUS
 <1>2 \A B1 \in BS1: B1 \in BS2 OBVIOUS
 <1>f QED BY <1>1, <1>2            
PROPOSITION CardPeers == IsFiniteSet(peers) /\ Cardinality(peers) = n
  <1>1. IsFiniteSet(peers)
    BY PeersOK, FS_Union DEF PeersOK, peers
  <1>2. Cardinality(peers) = n
    BY ThresholdOK, PeersOK DEF ThresholdOK, PeersOK, peers
  <1>3. QED
    BY <1>1, <1>2
PROPOSITION ExtendsRefl == ASSUME NEW B \in W PROVE extends(B,B)
 BY ExtendsOK, WOK  DEF ExtendsOK, extends, Wb, WOK
PROPOSITION ExtendsRefl2 == ASSUME NEW B1 \in W, NEW B2 \in W PROVE B1 = B2 => extends(B2,B1)
 BY ExtendsOK, WOK  DEF ExtendsOK, extends, Wb, WOK
PROPOSITION ExtendsTrans == ASSUME NEW B1 \in W, NEW B2 \in W, NEW B3 \in W, extends(B1,B2), extends(B2,B3) PROVE extends(B1,B3)
 BY ExtendsOK  DEF ExtendsOK, extends, Wb
PROPOSITION TExistsPeer == \E P \in peersH: TRUE
  <1>1 nh>0
     <2> n >= threshold 
       BY ThresholdOK, PeersOK DEF ThresholdOK, PeersOK
     <2>f QED
       BY ThresholdOK, PeersOK DEF ThresholdOK, PeersOK
  <1>f QED
    BY <1>1, PeersOK, FS_EmptySet DEF ThresholdOK, PeersOK

PROPOSITION Invariance1 == Protocol => []Inv1
<1> USE DEF Inv1, TypeOK
<1>init Init => TypeOK BY WOK DEF Init, WOK
<1>induction TypeOK /\ [Next]_<<fr,nfr,Pv,signed>> => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_<<fr,nfr,Pv,signed>>
               PROVE  TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW P \in peersH,
               NEW bu \in W,
               /\ extends(Pv[P], bu)
               /\ phase(Pv[P]) # pf
               /\ Pv' = [Pv EXCEPT ![P] = bu ]
               /\ UNCHANGED << fr,nfr,signed >>
        PROVE  TypeOK'
    BY <2>1, WOK DEF Init, WOK
  <2>2. ASSUME NEW P \in peersH,
               NEW bs \in W,
               /\ extends(bs, Pv[P])
               /\ (phase(Pv[P]) = pf => bs = Pv[P])
               /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
               /\ UNCHANGED << fr,nfr,Pv>>
        PROVE  TypeOK'
    BY <2>2, WOK DEF Init, WOK
  <2>3. ASSUME NEW P \in peersD,
               NEW bs \in W,
               /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
               /\ UNCHANGED << fr,nfr,Pv>>
        PROVE  TypeOK'
    BY <2>3, WOK DEF Init, WOK
  <2>4. ASSUME NEW bu \in W,
               NEW R \in readers,
               /\ GuR(bu)
               /\ nfr' = [nfr EXCEPT ![R] = nfr[R] \union {bu}]
               /\ UNCHANGED << fr,Pv,signed >>
        PROVE  TypeOK'
    BY <2>4, WOK DEF Init, WOK
  <2>5. ASSUME NEW bu \in W,
               NEW R \in readers,
               /\ GuR(bu) /\ phase(bu) = pf
               /\ fr' = [fr EXCEPT ![R] = fr[R] \union {bu}]
               /\ UNCHANGED << nfr,Pv,signed >>
        PROVE  TypeOK'
    BY <2>5, WOK DEF Init, WOK
  <2>6. CASE UNCHANGED <<fr,nfr,Pv,signed>>
    BY <2>6, WOK DEF Init, WOK
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, ReadFinal, ReadNonFinal, SignPD, SignPH, UpdatePH
<1> QED BY <1>init, <1>induction, PTL DEF Protocol

PROPOSITION GuPreservation == \A B \in W: (Inv1 /\ GuR(B) /\ [Next]_<<fr,nfr,Pv,signed>> => GuR(B)')
<1> USE DEF Inv1, TypeOK, GuR
<1> QED 
  <2> SUFFICES ASSUME NEW B \in W,
                      Inv1,
                      NEW peersS \in SUBSET peers,
                      /\ Cardinality(peersS) >= threshold
                      /\ \A P \in peersS: B \in signed[P],
                      [Next]_<<fr,nfr,Pv,signed>>
               PROVE  GuR(B)'
    BY DEF GuR
  <2>1. ASSUME NEW P \in peersH,
               NEW bu \in W,
               /\ extends(Pv[P], bu)
               /\ phase(Pv[P]) # pf
               /\ Pv' = [Pv EXCEPT ![P] = bu ]
               /\ UNCHANGED << fr,nfr,signed >>
        PROVE  GuR(B)'
    BY <2>1
  <2>2. ASSUME NEW P \in peersH,
               NEW bs \in W,
               /\ extends(bs, Pv[P])
               /\ (phase(Pv[P]) = pf => bs = Pv[P])
               /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
               /\ UNCHANGED << fr,nfr,Pv>>
        PROVE  GuR(B)'
    BY <2>2
  <2>3. ASSUME NEW P \in peersD,
               NEW bs \in W,
               /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
               /\ UNCHANGED << fr,nfr,Pv>>
        PROVE  GuR(B)'
    BY <2>3
  <2>4. ASSUME NEW bu \in W,
               NEW R \in readers,
               /\ GuR(bu)
               /\ nfr' = [nfr EXCEPT ![R] = nfr[R] \union {bu}]
               /\ UNCHANGED << fr,Pv,signed >>
        PROVE  GuR(B)'
    BY <2>4
  <2>5. ASSUME NEW bu \in W,
               NEW R \in readers,
               /\ GuR(bu) /\ phase(bu) = pf
               /\ fr' = [fr EXCEPT ![R] = fr[R] \union {bu}]
               /\ UNCHANGED << nfr,Pv,signed >>
        PROVE  GuR(B)'
    BY <2>5
  <2>6. CASE UNCHANGED <<fr,nfr,Pv,signed>>
    BY <2>6
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, ReadFinal, ReadNonFinal, SignPD, SignPH, UpdatePH

(*** Key invariants and properties *)
(* Two sets of peers satisfying the guard GuR do have an honest peer in common *)
LEMMA TIntersecPeers == IntersecPeers
  <1>2. (threshold < 0) \/ (threshold >= 0) BY ThresholdOK DEF ThresholdOK
  <1>a. CASE (threshold < 0)  \* This case quickly leads to a contradiction
      BY <1>a, ThresholdOK, PeersOK DEF ThresholdOK, PeersOK
  <1>b. CASE (threshold >= 0)  \* This is the interesting case
    <2>00 SUFFICES ASSUME NEW peersS1 \in SUBSET peers, NEW peersS2 \in SUBSET peers,
                        /\ Cardinality(peersS1) >= threshold
                        /\ Cardinality(peersS2) >= threshold
                 PROVE  \E P \in (peersS1 \cap peersS2 \cap peersH): TRUE
        BY DEF IntersecPeers
\* Proof strategy: 1. We first prove that the intersection between peersS1 and peersS2 has at least threshold-2n peers
    <2>0. n \in Nat /\ threshold \in Nat /\ nh \in Nat
              BY ThresholdOK, PeersOK  DEF ThresholdOK, PeersOK
    <2>1. Cardinality(peersS1 \cap peersS2) >= (2*threshold - n)
       <3>0 IsFiniteSet(peersH \cup peersD) BY FS_Union, FS_Intersection, ThresholdOK, PeersOK DEF ThresholdOK, PeersOK, peers
       <3>00 IsFiniteSet(peersS1) /\ IsFiniteSet(peersS2) BY <3>0, FS_Subset DEF peers
       <3> IsFiniteSet(peersS1) /\ IsFiniteSet(peersS2) /\ IsFiniteSet(peersS1 \cup peersS2) /\ IsFiniteSet(peersS1 \cap peersS2) /\ IsFiniteSet(peers)
          BY <3>00, <3>0, FS_Union, FS_Intersection, ThresholdOK, PeersOK DEF ThresholdOK, PeersOK, peers
       <3> n \in Nat /\ threshold \in Nat /\ Cardinality(peersS1 \cup peersS2) \in Nat /\ Cardinality(peersS1) \in Nat /\ Cardinality(peersS2) \in Nat /\ Cardinality(peersS1 \cap peersS2) \in Nat 
          BY ThresholdOK, PeersOK, FS_CardinalityType DEF ThresholdOK, PeersOK, FS_CardinalityType, peers
       <3>1 Cardinality(peersS1 \cup peersS2) = Cardinality(peersS1) + Cardinality(peersS2) - Cardinality(peersS1 \cap peersS2) BY FS_Union
       <3>2 Cardinality(peersS1 \cup peersS2) <= Cardinality(peers)
          <4>1 peersS1 \cup peersS2 \subseteq peers BY DEF peers
          <4> QED BY <4>1, FS_Subset
       <3>3 Cardinality(peersS1) >= threshold /\ Cardinality(peersS2) >= threshold BY <2>00
       <3>4 Cardinality(peersS1 \cap peersS2) >= 2*threshold - n  BY <3>3, <3>2, <3>1, PeersOK DEF PeersOK
       <3> QED BY <3>4, ThresholdOK, PeersOK DEF ThresholdOK, PeersOK
\* Proof strategy: 2. We now use <2>1 and assuptions about the threshold, n, and nh to conclude
    <2>2 /\ IsFiniteSet(peersS1 \cap peersS2) /\ IsFiniteSet(peersS1 \cap peersS2 \cap peersH) /\ IsFiniteSet(peers) /\ IsFiniteSet(peersH)
        <3>1 IsFiniteSet(peersH) /\ IsFiniteSet(peersD) BY PeersOK DEF PeersOK
        <3>2 IsFiniteSet(peers) BY <3>1, FS_Union DEF peers
        <3>3 IsFiniteSet(peersS1) /\ IsFiniteSet(peersS2) BY <3>2, FS_Subset
        <3>f. QED BY FS_Intersection, <3>3, <3>2, <3>1
    <2>3. Cardinality(peersS1 \cap peersS2) > n - nh
      <3> (2*threshold - n) > n - nh
          BY ThresholdOK, PeersOK  DEF ThresholdOK, PeersOK  
      <3> Cardinality(peersS1 \cap peersS2) \in Nat BY FS_CardinalityType, <2>2
      <3> threshold \in Nat /\ n \in Nat /\ nh \in Nat BY ThresholdOK, PeersOK DEF ThresholdOK, PeersOK
         <3>f QED  BY <2>1
    <2>4. (peersS1 \cap peersS2) \cap peersH # {}
        <3>0 (peersS1 \cap peersS2) \subseteq peers /\ peersH \subseteq peers BY PeersOK, ThresholdOK DEF peers, PeersOK, ThresholdOK
        <3>1 Cardinality(peers) = n /\ Cardinality(peersH) = nh BY PeersOK DEF PeersOK
        <3>2 Cardinality(peersS1 \cap peersS2) \in Nat /\ Cardinality(peersH) \in Nat /\ Cardinality(peers) \in Nat BY <2>2, FS_CardinalityType
        <3>3 Cardinality(peersS1 \cap peersS2) + Cardinality(peersH) > Cardinality(peers) BY <3>1, <2>3, <3>2
        <3>f QED
           BY <3>0, <2>0, <3>3, <3>1, FS_MajoritiesIntersect, CardPeers
    <2>f. QED
      BY <2>2, <2>4, FS_EmptySet
  <1>f. QED
      BY <1>a, <1>b, <1>2 DEF Cardinality

(* Peers locally enforce FC *)
LEMMA TPeersLocalFC == Protocol => []PeersLocalFC
<1> USE DEF PeersLocalFC, Inv1, TypeOK
<1>b. Init /\ TypeOK => PeersLocalFC
  <2> SUFFICES ASSUME Init /\ TypeOK,
                      NEW P \in peersH
               PROVE  /\ \A B \in signed[P]: extends(B,Pv[P])
                      /\ \A B \in FRP(P): B = Pv[P]
    BY DEF PeersLocalFC
  <2> P \in peers BY DEF peers
  <2> signed[P] = {} /\ (FRP(P) \cap FinalW) = {} 
    <3>1. signed[P] = {}
      BY DEF Init
    <3>2. FRP(P) = {}
      <4>1 (signed[P] \cup {Pv[P]}) = {B0} BY DEF Init 
      <4>qed QED BY <4>1, PhasesOK, WOK DEF Init, FinalW, FRP, PhasesOK, WOK, NFRP, phase
    <3>3. QED
      BY <3>1, <3>2
  <2>1. \A B \in signed[P]: extends(B,Pv[P])
    BY ExtendsRefl DEF Init, FRP, NFRP, FinalW
  <2>2. \A B \in FRP(P): B = Pv[P]
    BY ExtendsRefl DEF Init, FRP, NFRP, FinalW
  <2>3. QED
    BY <2>1, <2>2 
<1>i. TypeOK /\ PeersLocalFC /\ [Next]_<<fr,nfr,Pv,signed>> => PeersLocalFC'
 <2> USE DEF PeersLocalFC
 <2>qed QED 
   <3> SUFFICES ASSUME TypeOK /\ PeersLocalFC /\ [Next]_<<fr,nfr,Pv,signed>>,
                       NEW P \in peersH'
                PROVE  (/\ \A B \in signed[P]: extends(B,Pv[P])
                        /\ \A B \in FRP(P): B = Pv[P])'
     BY DEF PeersLocalFC
   <3> P \in peersH /\ P \in peers BY DEF peers
   <3> QED
     <4>1. ASSUME NEW P_1 \in peersH,
                  NEW bu \in W,
                    /\ extends(Pv[P_1], bu)
                  /\ phase(Pv[P_1]) # pf
                  /\ Pv' = [Pv EXCEPT ![P_1] = bu ]
                  /\ UNCHANGED << fr,nfr,signed >>
           PROVE  (/\ \A B \in signed[P]: extends(B,Pv[P])
                   /\ \A B \in FRP(P): B = Pv[P])'
       <5> P_1 \in peers BY DEF peers
       <5> CASE P_1 = P
         <6> CASE FRP(P) = {}
           <7> CASE phase(bu) = pf
             <8> FRP(P)' = {bu} BY <4>1 DEF FRP, FinalW, NFRP
             <8>qed QED 
               <9>1. (\A B \in signed[P]: extends(B,Pv[P]))'
                 BY <4>1, ExtendsTrans DEF FRP, FinalW, NFRP
               <9>2. (\A B \in FRP(P): B = Pv[P])'
                 BY <4>1 DEF FRP, FinalW, NFRP
               <9>3. QED
                 BY <9>1, <9>2
           <7> CASE phase(bu) # pf
             <8> FRP(P)' = {} BY <4>1 DEF FRP, FinalW, NFRP
             <8>qed QED 
               <9>1. (\A B \in signed[P]: extends(B,Pv[P]))'
                 BY <4>1, ExtendsTrans DEF FRP, FinalW, NFRP
               <9>2. (\A B \in FRP(P): B = Pv[P])'
                 BY <4>1 DEF FRP, FinalW, NFRP
               <9>3. QED
                 BY <9>1, <9>2
           <7>qed QED OBVIOUS
         <6> CASE FRP(P) # {}
           <7> \E B \in FRP(P): TRUE OBVIOUS
           <7> \E B \in FRP(P): B = Pv[P] /\ phase(Pv[P]) = pf BY DEF FRP, FinalW
           <7>qed QED BY <4>1
         <6>qed QED BY DEF FRP, NFRP, FinalW
       <5>qed QED BY <4>1 DEF FRP, NFRP, FinalW
     <4>2. ASSUME NEW P_1 \in peersH,
                  NEW bs \in W,
                    /\ extends(bs, Pv[P_1]) /\ phase(bs) = phase(Pv[P_1])
                  /\ (phase(Pv[P_1]) = pf => bs = Pv[P_1])
                  /\ signed' = [signed EXCEPT ![P_1] = signed[P_1] \union {bs}]
                  /\ UNCHANGED << fr,nfr,Pv>>
           PROVE  (/\ \A B \in signed[P]: extends(B,Pv[P])
                   /\ \A B \in FRP(P): B = Pv[P])'   
       <5> P_1 \in peers BY DEF peers
       <5> CASE P_1 # P
         <6>1 signed[P] = signed[P]' BY <4>2 DEF FRP, FinalW, NFRP
         <6> FRP(P) = FRP(P)' /\ signed[P] = signed[P]' /\ Pv[P] = Pv[P]' BY <4>2, <6>1 DEF FRP, FinalW, NFRP
         <6> QED BY <4>2
       <5> CASE P_1 = P
         <6> CASE FRP(P) = {}
           <7> CASE phase(Pv[P_1]) = pf
             <8> phase(bs) = pf  BY <4>2
             <8> bs = Pv[P_1] BY <4>2
             <8> FRP(P)' = {bs} BY <4>1 DEF FRP, FinalW, NFRP
             <8>qed QED 
               <9>1. (\A B \in signed[P]: extends(B,Pv[P]))'
                 BY <4>2, ExtendsTrans DEF FRP, FinalW, NFRP
               <9>2. (\A B \in FRP(P): B = Pv[P])'
                 BY <4>2 DEF FRP, FinalW, NFRP
               <9>3. QED
                 BY <9>2, <4>2
           <7> CASE phase(Pv[P_1]) # pf
             <8> phase(bs) # pf BY <4>2
             <8> FRP(P)' = {} BY <4>2 DEF FRP, FinalW, NFRP
             <8>qed QED 
               <9>1. (\A B \in signed[P]: extends(B,Pv[P]))'
                 BY <4>2, ExtendsTrans DEF FRP, FinalW, NFRP
               <9>2. (\A B \in FRP(P): B = Pv[P])'
                 BY <4>2 DEF FRP, FinalW, NFRP
               <9>3. QED
                 BY <9>1, <4>2
           <7>qed QED OBVIOUS
         <6> CASE FRP(P) # {}
           <7> Pv[P] = Pv[P]' BY <4>2
           <7> \E B \in FRP(P): \A Bf \in FRP(P): B = Bf /\ B = Pv[P] /\ phase(Pv[P]) = pf /\ phase(bs) = pf /\ bs = Pv[P_1] /\ bs = Pv[P_1]' BY <4>2 DEF FRP, FinalW
           <7> extends(bs,Pv[P]') BY <4>2
           <7> signed[P]' = signed[P] \cup {bs} BY <4>2
           <7>qed QED 
             <8>1. (\A B \in signed[P]: extends(B,Pv[P]))'
               <9> SUFFICES ASSUME NEW B \in (signed[P])'
                            PROVE  extends(B,Pv[P])'
                 OBVIOUS
               <9> QED
                 BY <4>2
             <8>2. (\A B \in FRP(P): B = Pv[P])'
               <9> SUFFICES ASSUME NEW B \in FRP(P)'
                            PROVE  (B = Pv[P])'
                 OBVIOUS
               <9> B = Pv[P] BY <4>2 DEF FRP, FinalW, NFRP
               <9> QED
                 BY <4>2 
             <8>3. QED
               BY <8>1, <8>2
         <6>qed QED BY DEF FRP, NFRP, FinalW
       <5>qed QED BY <4>2 DEF FRP, NFRP, FinalW
     <4>3. ASSUME NEW P_1 \in peersD,
                  NEW bs \in W,
                    /\ signed' = [signed EXCEPT ![P_1] = signed[P_1] \union {bs}]
                  /\ UNCHANGED << fr,nfr,Pv>>
           PROVE  (/\ \A B \in signed[P]: extends(B,Pv[P])
                   /\ \A B \in FRP(P): B = Pv[P])'
       <5> P_1 \notin peersH BY PeersOK DEF PeersOK
       <5>qed QED BY <4>3 DEF FRP, NFRP, FinalW
     <4>4. ASSUME NEW bu \in W,
                  NEW R \in readers,
                  /\ GuR(bu)
                  /\ nfr' = [nfr EXCEPT ![R] = nfr[R] \union {bu}]
                  /\ UNCHANGED << fr,Pv,signed >>
           PROVE  (/\ \A B \in signed[P]: extends(B,Pv[P])
                   /\ \A B \in FRP(P): B = Pv[P])'
       BY <4>4 DEF FRP, NFRP, FinalW
     <4>5. ASSUME NEW bu \in W,
                  NEW R \in readers,
                  /\ GuR(bu) /\ phase(bu) = pf
                  /\ fr' = [fr EXCEPT ![R] = fr[R] \union {bu}]
                  /\ UNCHANGED << nfr,Pv,signed >>
           PROVE  (/\ \A B \in signed[P]: extends(B,Pv[P])
                   /\ \A B \in FRP(P): B = Pv[P])'
       BY <4>5 DEF FRP, NFRP, FinalW
     <4>6. CASE UNCHANGED <<fr,nfr,Pv,signed>>
       BY <4>6 DEF FRP, NFRP, FinalW
     <4>7. QED
       BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF Next, ReadFinal, ReadNonFinal, SignPD, SignPH, UpdatePH
<1>qed QED BY <1>b, <1>i, Invariance1, PTL DEF Protocol, Inv1, TypeOK

(* Peers locally enforce FA *)
LEMMA TPeersLocalFA == Protocol => []PeersLocalFA
<1> USE DEF PeersLocalFA, Inv1, TypeOK
<1>b. Init /\ TypeOK => PeersLocalFA
  <2> SUFFICES ASSUME Init /\ TypeOK,
                      NEW P \in peersH
               PROVE  FA_param(FRP(P),
                               NFRP(P))
    BY DEF PeersLocalFA
   <2> USE DEF FRP, NFRP
   <2> P \in peers BY PeersOK DEF PeersOK, peers
   <2> signed[P] = {} BY DEF Init
   <2> signed[P] \cap {B \in W : phase(B) = pf} = {} BY DEF Init
  <2>1. (signed[P] \cap {B \in W: phase(B) = pf}) = {}  \/  \E Bf \in (signed[P] \cap {B \in W: phase(B) = pf}): (signed[P] \cap {B \in W: phase(B) = pf}) = {Bf}
    <3> QED BY DEF Init, FA_param
  <2>2. \A Bf \in (signed[P] \cap {B \in W: phase(B) = pf}): \A B \in (signed[P]): extends(B,Bf)
    <3> QED BY DEF Init, FA_param
  <2>11. FRP(P) = {}  \/  \E Bf \in FRP(P): FRP(P) = {Bf}
    BY DEF FA_param
  <2>21. \A Bf \in FRP(P): \A B \in NFRP(P): extends(B,Bf)
    BY ExtendsRefl DEF FA_param, ExtendsRefl
  <2>3. QED
    BY <2>11, <2>21 DEF FA_param
<1>i. TypeOK /\ PeersLocalFA /\ PeersLocalFC /\ [Next]_<<fr,nfr,Pv,signed>> => PeersLocalFA'
  <2> SUFFICES ASSUME TypeOK /\ PeersLocalFA /\ PeersLocalFC /\ [Next]_<<fr,nfr,Pv,signed>>,
                      NEW P \in peersH'
               PROVE  FA_param(FRP(P),
                               NFRP(P))'
    BY DEF PeersLocalFA
  <2> P \in peersH /\ P \in peers BY DEF peers
  <2> USE DEF PeersLocalFC
  <2>qed. QED 
    <3>1. ASSUME NEW P_1 \in peersH,
                 NEW bu \in W,
                   /\ extends(Pv[P_1], bu)
                 /\ phase(Pv[P_1]) # pf
                 /\ Pv' = [Pv EXCEPT ![P_1] = bu ]
                 /\ UNCHANGED << fr,nfr,signed >>
          PROVE  FA_param(FRP(P),
                          NFRP(P))'
      <5> P_1 \in peers BY DEF peers
       <5> CASE P_1 = P
         <6> CASE FRP(P) = {}
           <7> CASE phase(bu) = pf
             <8> FRP(P)' = {bu} BY <3>1 DEF FRP, FinalW, NFRP
             <8>qed QED 
               <9>1. (\A B \in signed[P]: extends(B,Pv[P]))'
                 BY <3>1, ExtendsTrans DEF FRP, FinalW, NFRP
               <9>2. (\A B \in FRP(P): B = Pv[P])'
                 BY <3>1 DEF FRP, FinalW, NFRP
               <9> FRP(P)' = {bu} BY <9>1, <9>2, <3>1
               <9> \A B \in NFRP(P)' : extends(B, bu)
                 <10> NFRP(P)' \subseteq NFRP(P) \cup {bu} BY <3>1 DEF NFRP, FRP, FinalW
                 <10> \A B \in NFRP(P) : extends(B, bu) 
                   <11> SUFFICES ASSUME NEW B \in NFRP(P)
                                 PROVE  extends(B, bu)
                     OBVIOUS
                   <11> B \in W /\ Pv[P] \in W BY DEF NFRP
                   <11> extends(B,Pv[P])
                     <12> CASE B = Pv[P] BY ExtendsRefl
                     <12> CASE B \in NFRP(P) BY DEF NFRP
                     <12> QED BY DEF PeersLocalFA, ExtendsTrans, FA_param
                   <11> QED BY ExtendsTrans, <3>1
                 <10> extends(bu, bu) BY ExtendsRefl
                 <10>qed QED BY <9>1, <9>2, <3>1 DEF PeersLocalFC
               <9>3. QED
                 BY <9>1, <9>2 DEF FA_param
           <7> CASE phase(bu) # pf
             <8> FRP(P)' = {} BY <3>1 DEF FRP, FinalW, NFRP
             <8>qed QED 
               <9>1. (\A B \in signed[P]: extends(B,Pv[P]))'
                 BY <3>1, ExtendsTrans DEF FRP, FinalW, NFRP
               <9>2. (\A B \in FRP(P): B = Pv[P])'
                 BY <3>1 DEF FRP, FinalW, NFRP
               <9>3. QED
                 BY <9>1, <9>2 DEF FA_param
           <7>qed QED OBVIOUS
         <6> CASE FRP(P) # {}
           <7> \E B \in FRP(P): TRUE OBVIOUS
           <7> \E B \in FRP(P): B = Pv[P] /\ phase(Pv[P]) = pf BY DEF FRP, FinalW
           <7>qed QED BY <3>1
         <6>qed QED BY DEF FRP, NFRP, FinalW
       <5>qed QED BY <3>1 DEF FRP, NFRP, FinalW
    <3>2. ASSUME NEW P_1 \in peersH,
                 NEW bs \in W,
                   /\ extends(bs, Pv[P_1]) /\ phase(bs) = phase(Pv[P_1])    
                 /\ (phase(Pv[P_1]) = pf => bs = Pv[P_1])
                 /\ signed' = [signed EXCEPT ![P_1] = signed[P_1] \union {bs}]
                 /\ UNCHANGED << fr,nfr,Pv>>
          PROVE  FA_param(FRP(P),
                          NFRP(P))'
      BY <3>2 DEF FRP, NFRP, FinalW, FA_param
    <3>3. ASSUME NEW P_1 \in peersD,
                 NEW bs \in W,
                   /\ signed' = [signed EXCEPT ![P_1] = signed[P_1] \union {bs}]
                 /\ UNCHANGED << fr,nfr,Pv>>
          PROVE  FA_param(FRP(P),
                          NFRP(P))'
       <4> P_1 \notin peersH BY PeersOK DEF PeersOK
       <4>qed QED BY <3>3 DEF FRP, NFRP, FinalW
    <3>4. ASSUME NEW bu \in W,
                 NEW R \in readers,
                 /\ GuR(bu)
                 /\ nfr' = [nfr EXCEPT ![R] = nfr[R] \union {bu}]
                 /\ UNCHANGED << fr,Pv,signed >>
          PROVE  FA_param(FRP(P),
                          NFRP(P))'
      BY <3>4 DEF FRP, NFRP, FinalW, FA_param
    <3>5. ASSUME NEW bu \in W,
                 NEW R \in readers,
                 /\ GuR(bu) /\ phase(bu) = pf
                 /\ fr' = [fr EXCEPT ![R] = fr[R] \union {bu}]
                 /\ UNCHANGED << nfr,Pv,signed >>
          PROVE  FA_param(FRP(P),
                          NFRP(P))'
      BY <3>5 DEF FRP, NFRP, FinalW, FA_param
    <3>6. CASE UNCHANGED <<fr,nfr,Pv,signed>>
      BY <3>6 DEF FRP, NFRP, FinalW, FA_param
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Next, ReadFinal, ReadNonFinal, SignPD, SignPH, UpdatePH
<1>f.QED BY <1>b, <1>i, Invariance1, PTL, TPeersLocalFC DEF Protocol, Inv1, TypeOK

(* Preservation of Gu for all read contents and final contents have phase pf *)
LEMMA TReadersLocalGu == Protocol => []ReadersLocalGu
<1> USE DEF ReadersLocalGu, Inv1, TypeOK
<1>b. Init /\ TypeOK => ReadersLocalGu BY DEF Init
<1>i. TypeOK /\ ReadersLocalGu /\ [Next]_<<fr,nfr,Pv,signed>> => ReadersLocalGu'
  <2> SUFFICES ASSUME TypeOK,
                      ReadersLocalGu,
                      NEW R \in readers',
                      [Next]_<<fr,nfr,Pv,signed>>
               PROVE  (/\ \A B \in nfr[R]: GuR(B)
                       /\ \A B \in fr[R]: GuR(B) /\ phase(B) = pf)'
    BY DEF ReadersLocalGu
  <2>1. ASSUME NEW P \in peersH,
                           \E bu \in W:
               /\ extends(Pv[P], bu) 
               /\ phase(Pv[P]) # pf
               /\ Pv' = [Pv EXCEPT ![P] = bu ]
               /\ UNCHANGED << fr,nfr,signed >>
        PROVE  (/\ \A B \in nfr[R]: GuR(B)
                /\ \A B \in fr[R]: GuR(B) /\ phase(B) = pf)'
    BY <2>1 DEF GuR
  <2>2. ASSUME NEW P \in peersH,
                          \E bs \in W:
               /\ extends(bs, Pv[P]) /\ phase(bs) = phase(Pv[P])   
               /\ (phase(Pv[P]) = pf => bs = Pv[P])
               /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
               /\ UNCHANGED << fr,nfr,Pv>>
        PROVE  (/\ \A B \in nfr[R]: GuR(B)
                /\ \A B \in fr[R]: GuR(B) /\ phase(B) = pf)'
    BY <2>2 DEF GuR
  <2>3. ASSUME NEW P \in peersD,
                          \E bs \in W:
               /\ signed' = [signed EXCEPT ![P] = signed[P] \union {bs}]
               /\ UNCHANGED << fr,nfr,Pv>>
        PROVE  (/\ \A B \in nfr[R]: GuR(B)
                /\ \A B \in fr[R]: GuR(B) /\ phase(B) = pf)'
    BY <2>3 DEF GuR
  <2>4. ASSUME NEW bu \in W,
               NEW R_1 \in readers,
               /\ GuR(bu)
               /\ nfr' = [nfr EXCEPT ![R_1] = nfr[R_1] \union {bu}]
               /\ UNCHANGED << fr,Pv,signed >>
        PROVE  (/\ \A B \in nfr[R]: GuR(B)
                /\ \A B \in fr[R]: GuR(B) /\ phase(B) = pf)'
    BY <2>4 DEF GuR
  <2>5. ASSUME NEW bu \in W,
               NEW R_1 \in readers,
               /\ GuR(bu) /\ phase(bu) = pf
               /\ fr' = [fr EXCEPT ![R_1] = fr[R_1] \union {bu}]
               /\ UNCHANGED << nfr,Pv,signed >>
        PROVE  (/\ \A B \in nfr[R]: GuR(B)
                /\ \A B \in fr[R]: GuR(B) /\ phase(B) = pf)'
    BY <2>5 DEF GuR
  <2>6. CASE UNCHANGED <<fr,nfr,Pv,signed>>
    BY <2>6 DEF GuR
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, ReadFinal, ReadNonFinal, SignPD, SignPH, UpdatePH
<1>f.QED BY <1>b, <1>i, Invariance1, PTL, TPeersLocalFC DEF Protocol, Inv1, TypeOK

(* The previous properties imply ReaderAgreement that boils down to FA applied between two readers *)
LEMMA soundReaderAgreement == TypeOK /\ ReadersLocalGu /\ PeersLocalFC /\ PeersLocalFA => ReaderAgreement
<1> USE DEF ReaderAgreement, TypeOK, BSfr, BSnfr
<1>qed QED 
  <2> SUFFICES ASSUME TypeOK /\ ReadersLocalGu /\ PeersLocalFC /\ PeersLocalFA,
                      NEW R1 \in readers, NEW R2 \in readers,
                      NEW B1 \in BSfr \cup BSnfr,
                      NEW B2 \in BSfr
               PROVE  extends(B1, B2)
    BY DEF ReaderAgreement
  <2>1 GuR(B1) /\ GuR(B2) BY DEF ReadersLocalGu
  <2>2 (B1 \in fr[R1] => phase(B1) = pf) /\ (B2 \in fr[R2] => phase(B2) = pf) BY DEF ReadersLocalGu
  <2> B1 \in W /\ B2 \in W BY DEF TypeOK
  <2> QED
    <3> SUFFICES ASSUME NEW PS1 \in SUBSET peers,
                        /\ Cardinality(PS1) >= threshold
                        /\ \A P1 \in PS1: B1 \in signed[P1],
                        NEW PS2 \in SUBSET peers,
                        /\ Cardinality(PS2) >= threshold
                        /\ \A P2 \in PS2: B2 \in signed[P2]
                 PROVE  extends(B1, B2)
      BY <2>1 DEF GuR
    <3> \E Ph \in peersH: Ph \in PS1 /\ Ph \in PS2 BY TIntersecPeers DEF IntersecPeers
    <3>qed QED 
      <4> SUFFICES ASSUME NEW Ph \in peersH,
                          Ph \in PS1 /\ Ph \in PS2
                   PROVE  extends(B1, B2)
        OBVIOUS
      <4> Ph \in peers BY DEF peers
      <4> B1 \in signed[Ph] /\ B2 \in signed[Ph] OBVIOUS
      <4> phase(B2) = pf BY DEF ReadersLocalGu
      <4> QED BY DEF PeersLocalFA, FA_param, FRP, NFRP, FinalW

(* Therefore, ReaderAgreement is an invariant of Protocol. *)
LEMMA TReaderAgreement == Protocol => []ReaderAgreement
BY Invariance1, PTL, TPeersLocalFC, TPeersLocalFA, TReadersLocalGu, soundReaderAgreement DEF Protocol, Inv1, TypeOK

(* ReaderAgreement and some previous invariants imply FA. *)
LEMMA soundFA == ReaderAgreement /\ ReadersLocalGu /\ TypeOK => FA
  <1> USE DEF BSfr, BSnfr
  <1> SUFFICES ASSUME ReaderAgreement /\ ReadersLocalGu /\ TypeOK
               PROVE  FA
    OBVIOUS
  <1>1 UNION {fr[R]: R \in readers} = {} \/ UNION {fr[R]: R \in readers} # {} OBVIOUS
  <1>2 CASE UNION {fr[R]: R \in readers} = {}
    <2>1. BSfr = {}  \/  \E Bf \in BSfr: BSfr = {Bf}
      BY <1>2 DEF FA
    <2>2. \A Bf \in BSfr: \A B \in BSnfr: extends(B,Bf)
      BY <1>2 DEF FA
    <2>3. QED
      BY <2>1, <2>2 DEF FA
  <1>3 CASE UNION {fr[R]: R \in readers} # {}
     <2>1 \E Bf \in UNION {fr[R]: R \in readers}:
               /\ \A B \in UNION {nfr[R]: R  \in readers}: extends(B, Bf)   \* FA (ii)
               /\ UNION {fr[R]: R \in readers} = {Bf}    
          <3>1 ASSUME NEW Bf \in UNION {fr[R]: R \in readers}
               PROVE /\ \A B \in UNION {nfr[R]: R  \in readers}: extends(B, Bf)   \* FA (ii)
                     /\ UNION {fr[R]: R \in readers} = {Bf}                      \* FA (i) 
              <4>qed QED 
                <5>1. \A B \in UNION {nfr[R]: R  \in readers}: extends(B, Bf)
                  BY <1>3 DEF ReaderAgreement, FA, TypeOK, ReadersLocalGu
                <5>2. UNION {fr[R]: R \in readers} = {Bf}
                   <6> \E R \in readers: Bf \in fr[R] OBVIOUS
                   <6> ASSUME NEW B\in UNION {fr[R]: R \in readers} PROVE B=Bf
                      <7> \E R2 \in readers: B \in fr[R2] OBVIOUS
                      <7>qed QED
                        <8> SUFFICES ASSUME NEW R2 \in readers,
                                            B \in fr[R2],
                                            NEW R \in readers,
                                            Bf \in fr[R]
                                     PROVE  B=Bf
                          OBVIOUS
                        <8> phase(Bf) = pf BY DEF ReadersLocalGu
                        <8> phase(B) = pf BY DEF ReadersLocalGu
                        <8> extends(B, Bf) /\ extends(Bf, B)  
                          BY antiSymEx DEF ReaderAgreement                 
                        <8> QED BY antiSymEx DEF TypeOK
                   <6> QED
                  BY <1>3 DEF  FA, TypeOK
                <5>3. QED
                  BY <5>1, <5>2
          <3>2 \E Bf \in UNION {fr[R]: R \in readers}: TRUE BY <1>3
          <3>qed QED BY <1>3, <3>1, <3>2 DEF FA, TypeOK
     <2>f QED BY <2>1, <1>3 DEF FA
  <1> QED
    BY <1>1, <1>2, <1>3

(*** Final theorem: final-agreement (FA) is an invariant of our protocol, specified as Spec. *)
THEOREM TFA == Protocol => []FA
  BY soundFA, PTL, TReaderAgreement, TReadersLocalGu, Invariance1 DEF TReaderAgreement, TReadersLocalGu,  Invariance1, Inv1

=============================================================================

\* Modification History
\* Last modified Tue Oct 22 19:06:22 CEST 2019 by anonymous
\* Created Thu Apr 04 11:50:05 CEST 2019 by anonymous
