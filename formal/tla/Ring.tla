-------------------------------- MODULE Ring --------------------------------
(***************************************************************************)
(* Dijkstra 1974 K-state self-stabilizing ring (Comm. ACM 17(11), 643-644),*)
(* Construction 1 -- model-checked with TLC.                               *)
(*                                                                         *)
(* SCORE traceability:                                                     *)
(*   - Lean  : formal/Formal/Score/SelfStabilization.lean  (SS2)           *)
(*             This TLC model discharges, for bounded (N,K), the reference *)
(*             case Lean states as the axiom `dijkstraRingSelfStabilizes`. *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md          *)
(*             obsidian/SCORE/emergence/mechanism/AgentHomogeneityFragility *)
(*             obsidian/sources/Dijkstra-Edsger.md                         *)
(*                                                                         *)
(* Two rings are modelled to exhibit Dijkstra's CRUCIAL FINDING            *)
(* (identical machines cannot self-stabilize):                            *)
(*   - the HETEROGENEOUS ring (distinguished "bottom" machine)  self-      *)
(*     stabilizes: Ring.cfg checks  ConvergesHet  and it holds.           *)
(*   - the HOMOGENEOUS ring (every machine identical) does NOT: RingHom.cfg*)
(*     finds a reachable illegitimate configuration with no way out.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, K            \* N+1 machines at positions 0..N; values in 0..K-1
ASSUME NKAssumption == (N \in Nat) /\ (K \in Nat) /\ (N < K)   \* Dijkstra Note 1: K > N

Pos == 0 .. N
Val == 0 .. (K - 1)

VARIABLE s                \* s \in [Pos -> Val] : the ring configuration

TypeOK == s \in [Pos -> Val]

Init == s \in [Pos -> Val]      \* ANY initial configuration (adversarial start)

Left(i) == IF i = 0 THEN N ELSE i - 1   \* left neighbour on the ring

(***************************************************************************)
(* HETEROGENEOUS ring -- Dijkstra Construction 1.                          *)
(*   bottom  (position 0): privileged iff its left neighbour (top, N)      *)
(*                         EQUALS it; fires  s[0] := (s[0]+1) % K.          *)
(*   interior(position i>0): privileged iff its left neighbour DIFFERS;     *)
(*                         fires  s[i] := s[i-1]  (copy left).              *)
(* The bottom's rule differs from the interior's -- the symmetry break.    *)
(***************************************************************************)
PrivHet(i) == IF i = 0 THEN s[N] = s[0] ELSE s[Left(i)] # s[i]

FireHet(i) ==
    /\ PrivHet(i)
    /\ s' = [s EXCEPT ![i] = IF i = 0 THEN (s[0] + 1) % K ELSE s[Left(i)]]

NextHet == \E i \in Pos : FireHet(i)

NumPrivHet   == Cardinality({ i \in Pos : PrivHet(i) })
LegitimateHet == NumPrivHet = 1          \* Dijkstra's legitimacy: exactly one privilege

(***************************************************************************)
(* HOMOGENEOUS ring -- every machine (including position 0) uses the same  *)
(* interior copy-left rule. No distinguished bottom => no symmetry break.  *)
(***************************************************************************)
PrivHom(i) == s[Left(i)] # s[i]

FireHom(i) ==
    /\ PrivHom(i)
    /\ s' = [s EXCEPT ![i] = s[Left(i)]]

NextHom == \E i \in Pos : FireHom(i)

NumPrivHom    == Cardinality({ i \in Pos : PrivHom(i) })
LegitimateHom == NumPrivHom = 1

(***************************************************************************)
(* Specifications and the self-stabilization property.                     *)
(* Strong fairness on each machine models a central daemon that does not    *)
(* starve a continuously-privileged machine.                               *)
(***************************************************************************)
SpecHet == Init /\ [][NextHet]_s /\ (\A i \in Pos : SF_s(FireHet(i)))
SpecHom == Init /\ [][NextHom]_s /\ (\A i \in Pos : SF_s(FireHom(i)))

\* Self-stabilization: from ANY start, eventually the ring is always legitimate.
ConvergesHet == <>[]LegitimateHet
ConvergesHom == <>[]LegitimateHom
=============================================================================
