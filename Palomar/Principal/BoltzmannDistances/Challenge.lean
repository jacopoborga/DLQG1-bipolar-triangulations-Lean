/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FinCases
/-!
# Finite Boltzmann directed distances (Theorem 1.11)

For each error probability delta in (0,1), one constant A(delta)>1 works for every
positive right boundary length r. Under the actual Boltzmann law with a marked
LEFT boundary vertex, one event simultaneously bounds the source-to-sink LDP
between A inverse times r^(3/2) and A times r^(3/2), bounds the source-to-sink SDP
above by A times r^(3/4), and supplies a right-boundary vertex at SDP at least
A inverse times r^(3/4).

All measurable spaces below are discrete: every subset is measurable.
The definitions below specify finite dart rotation systems, orientation,
boundary paths, boundary-preserving isomorphism classes, and the marked atomic
law. Parallel edges retain their dart identities. The general boundary carrier
retains shared boundary edges and the one-edge map. Each marked class with n
edges has weight 3^(-n), normalized over ALL marked classes; marking therefore
does not mean sampling the unmarked law and then adding a uniform mark.

LDP is the attained finite maximum of simple directed path lengths on the
acyclic map. SDP is the infimum of lengths of all present-dart paths, with
infinity for unreachable endpoints. Original public definition names are
retained intentionally. No project module is imported, no law or identification
is assumed, and no definition value is left unspecified.

The compared auxiliary theorems are already proved here. The four
SimpleDirectedDartPath._proof_2/4/6/8 theorems justify the indices 0, n, i.val
and i.val+1 from the recorded list lengths. rightBoundaryVertex._proof_2
justifies an index in Fin(r+1) on the actual right boundary.
mem_sourceSinkPathLengthsBase identifies length-set membership with existence
of a simple source-to-sink path. These are well-formedness results, not extra
hypotheses of Theorem 1.11. Their compiler-generated names are bound to this
exact source and pinned toolchain.

The sole terminal proof hole is the deliberate Comparator Challenge for the
full theorem. The separate Solution uses the accepted complete source-facing
proof. The manuscript is identified in CORRESPONDENCE.json.
-/

public section
noncomputable section
open MeasureTheory Quiver
open scoped ENNReal BigOperators
namespace DirectedDistances.PlanarMap
/-- Finite darts with an edge-pairing involution and oriented vertex rotations. -/
structure CombinatorialMap (D : Type*) [Fintype D] [DecidableEq D] where
  edgeInv : Equiv.Perm D
  edgeInv_invol : ∀ d, edgeInv (edgeInv d) = d
  edgeInv_ne : ∀ d, edgeInv d ≠ d
  rot : Equiv.Perm D
namespace CombinatorialMap
variable {D : Type*} [Fintype D] [DecidableEq D]
/-- The face permutation is inverse rotation followed by edge inversion. -/
@[expose] def faceSucc (M : CombinatorialMap D) : Equiv.Perm D :=
  M.rot⁻¹ * M.edgeInv
/-- Membership in the distinguished face orbit. -/
@[expose] def IsOuter (M : CombinatorialMap D) (outer d : D) : Prop :=
  Equiv.Perm.SameCycle M.faceSucc outer d
/-- Two darts represent one vertex exactly when they share a rotation orbit. -/
def VertexRel (M : CombinatorialMap D) : D → D → Prop :=
  Equiv.Perm.SameCycle M.rot
/-- Two darts represent one geometric edge exactly when paired by edge inversion. -/
def EdgeRel (M : CombinatorialMap D) : D → D → Prop :=
  Equiv.Perm.SameCycle M.edgeInv
/-- Two darts represent one face exactly when they share a face-successor orbit. -/
def FaceRel (M : CombinatorialMap D) : D → D → Prop :=
  Equiv.Perm.SameCycle M.faceSucc
/-- Vertices are rotation-cycle classes of darts. -/
abbrev VertexQuotient (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.rot)
/-- Edges are edge-involution classes; parallel edges remain distinct. -/
abbrev EdgeQuotient (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.edgeInv)
/-- Faces are face-successor classes of darts. -/
abbrev FaceQuotient (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.faceSucc)
/-- The finite number of rotation-cycle vertices. -/
@[expose] noncomputable def numVertices (M : CombinatorialMap D) : ℕ := by
  classical
  exact Fintype.card (VertexQuotient M)
/-- The finite number of geometric edge orbits. -/
@[expose] noncomputable def numEdges (M : CombinatorialMap D) : ℕ := by
  classical
  exact Fintype.card (EdgeQuotient M)
/-- The finite number of face orbits. -/
@[expose] noncomputable def numFaces (M : CombinatorialMap D) : ℕ := by
  classical
  exact Fintype.card (FaceQuotient M)
/-- Connectedness by rotations, inverse rotations and edge inversion. -/
@[expose] def IsConnected (M : CombinatorialMap D) : Prop :=
  ∀ d e, Relation.ReflTransGen
    (fun x y : D => y = M.rot x ∨ y = M.rot.symm x ∨
      y = M.edgeInv x ∨ y = M.edgeInv.symm x) d e
/-- Euler characteristic V-E+F of the rotation system. -/
@[expose] noncomputable def eulerChar (M : CombinatorialMap D) : ℤ :=
  (M.numVertices : ℤ) - M.numEdges + M.numFaces
/-- The existing connected genus-zero combinatorial-map predicate. -/
@[expose] def IsPlanar (M : CombinatorialMap D) : Prop :=
  M.IsConnected ∧ M.eulerChar = 2
end CombinatorialMap
/-- Oriented present edges and unoriented missing geometric edges, with an outer face. -/
structure DirectedMapWithMissing (D : Type*) [Fintype D] [DecidableEq D]
    extends CombinatorialMap D where
  missing : D → Prop
  missing_edgeInv : ∀ d, missing d ↔ missing (edgeInv d)
  tail : D → Prop
  tail_iff : ∀ d, ¬ missing d → (tail d ↔ ¬ tail (edgeInv d))
  tail_missing : ∀ d, missing d → ¬ tail d
  outer : D
  missing_outer : ∀ d, missing d →
    CombinatorialMap.IsOuter toCombinatorialMap outer d ∨
      CombinatorialMap.IsOuter toCombinatorialMap outer (edgeInv d)
namespace DirectedMapWithMissing
variable {D : Type*} [Fintype D] [DecidableEq D]
/-- The marked external face as a face orbit, independent of its naming dart. -/
@[expose] def IsOuter (M : DirectedMapWithMissing D) (d : D) : Prop :=
  CombinatorialMap.IsOuter M.toCombinatorialMap M.outer d
/-- Existence of a present oriented dart from one rotation-cycle vertex to another. -/
@[expose] def directedStep (M : DirectedMapWithMissing D)
    (v w : CombinatorialMap.VertexQuotient M.toCombinatorialMap) : Prop :=
  ∃ d, ¬ M.missing d ∧ M.tail d ∧
    Quotient.mk (Equiv.Perm.SameCycle.setoid M.rot) d = v ∧
    Quotient.mk (Equiv.Perm.SameCycle.setoid M.rot) (M.edgeInv d) = w
/-- No nonempty directed path returns to its initial vertex. -/
@[expose] def IsAcyclic (M : DirectedMapWithMissing D) : Prop :=
  ∀ v : CombinatorialMap.VertexQuotient M.toCombinatorialMap,
    ¬ Relation.TransGen (directedStep M) v v
/-- Tail darts on the external face. -/
@[expose] def ulDarts (M : DirectedMapWithMissing D) : Set D :=
  {d | ¬ M.missing d ∧ M.tail d ∧ M.IsOuter d}
/-- Non-tail present darts on the external face. -/
@[expose] def lrDarts (M : DirectedMapWithMissing D) : Set D :=
  {d | ¬ M.missing d ∧ ¬ M.tail d ∧ M.IsOuter d}
end DirectedMapWithMissing
open Equiv List
section BoundaryPrimitives
variable {D : Type*} [Fintype D] [DecidableEq D]
/-- A nonempty duplicate-free list representing a cyclic boundary word. -/
structure NonemptyWord (D : Type*) where
  letters : List D
  nonempty : letters ≠ []
  nodup : letters.Nodup
/-- An exact cyclic enumeration of the external face, in its face-successor order. -/
@[expose] def IsOuterCycle (M : DirectedMapWithMissing D) (B : NonemptyWord D) : Prop :=
  (∀ d ∈ B.letters, M.IsOuter d) ∧
  (∀ d, M.IsOuter d → d ∈ B.letters) ∧
  (∀ d ∈ B.letters,
    M.toCombinatorialMap.faceSucc d = B.letters.formPerm d)
/-- List membership agrees exactly with membership in the specified dart set. -/
@[expose]
def EnumeratesSet (xs : List D) (s : Set D) : Prop :=
  ∀ d, d ∈ xs ↔ d ∈ s
/-- Every dart of this list is a missing geometric edge dart. -/
@[expose]
def MissingRun (M : DirectedMapWithMissing D) (xs : List D) : Prop :=
  ∀ d ∈ xs, M.missing d
/-- The exact cyclic external boundary split into its four ordered present/missing arcs. -/
@[expose]
def FourArcsWitness (M : DirectedMapWithMissing D) (B : NonemptyWord D)
    (ul ur lr ll : List D) : Prop :=
  IsOuterCycle M B ∧
  B.letters ~r (ul ++ ur ++ lr ++ ll) ∧
  EnumeratesSet ul M.ulDarts ∧
  EnumeratesSet lr M.lrDarts ∧
  MissingRun M ur ∧
  MissingRun M ll
/-- The map vertex is its underlying rotation-cycle quotient class. -/
abbrev MapVertex (M : DirectedMapWithMissing D) :=
  CombinatorialMap.VertexQuotient M.toCombinatorialMap
/-- The initial rotation-cycle vertex of this dart. -/
@[expose] def dartTailVertex (M : DirectedMapWithMissing D) (d : D) : MapVertex M :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot) d
/-- The terminal vertex is the rotation class of the opposite dart. -/
@[expose] def dartHeadVertex (M : DirectedMapWithMissing D) (d : D) : MapVertex M :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot)
    (M.toCombinatorialMap.edgeInv d)
/-- An incidence-correct list of present directed darts with distinct successive vertices. -/
structure SimpleDirectedDartPath (M : DirectedMapWithMissing D)
    (s t : MapVertex M) (n : ℕ) where
  darts : List D
  vertices : List (MapVertex M)
  darts_length : darts.length = n
  vertices_length : vertices.length = n + 1
  vertices_nodup : vertices.Nodup
  start_vertex : vertices.get ⟨0, by omega⟩ = s
  end_vertex : vertices.get ⟨n, by omega⟩ = t
  edge_step : ∀ i : Fin darts.length,
    ¬ M.missing (darts.get i) ∧ M.tail (darts.get i) ∧
      vertices.get ⟨i.val, by omega⟩ = dartTailVertex M (darts.get i) ∧
      vertices.get ⟨i.val + 1, by omega⟩ = dartHeadVertex M (darts.get i)
/-- A finite acyclic oriented triangulation with unique poles and its two directed outer paths. -/
structure BipolarTriangulationWithBoundaryBase (D : Type*) [Fintype D]
    [DecidableEq D] (ℓ r : ℕ) where
  map : DirectedMapWithMissing D
  noMissingDarts : ∀ d, ¬ map.missing d
  planar : map.toCombinatorialMap.IsPlanar
  innerFacesDegreeThree : ∀ d, ¬ map.IsOuter d →
    map.toCombinatorialMap.faceSucc
        (map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d)) = d ∧
      map.toCombinatorialMap.faceSucc d ≠ d ∧
      map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d) ≠ d
  acyclic : map.IsAcyclic
  source : MapVertex map
  sink : MapVertex map
  isSource : ¬ ∃ u, map.directedStep u source
  source_unique : ∀ v, (¬ ∃ u, map.directedStep u v) → v = source
  isSink : ¬ ∃ w, map.directedStep sink w
  sink_unique : ∀ v, (¬ ∃ w, map.directedStep v w) → v = sink
  left_length_pos : 1 ≤ ℓ
  right_length_pos : 1 ≤ r
  outerWord : NonemptyWord D
  leftPath : SimpleDirectedDartPath map source sink ℓ
  rightPath : SimpleDirectedDartPath map source sink r
  outerSplit : FourArcsWitness map outerWord leftPath.darts []
    (rightPath.darts.reverse.map map.toCombinatorialMap.edgeInv) []
end BoundaryPrimitives
section BoundaryIsomorphisms
variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D'] {ℓ r : ℕ}
/-- A plane orientation-preserving dart isomorphism retaining poles and ordered boundary paths. -/
structure BipolarBoundaryBaseIso
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (B' : BipolarTriangulationWithBoundaryBase D' ℓ r) where
  toEquiv : D ≃ D'
  rot_comm : ∀ d,
    toEquiv (B.map.toCombinatorialMap.rot d) =
      B'.map.toCombinatorialMap.rot (toEquiv d)
  edgeInv_comm : ∀ d,
    toEquiv (B.map.toCombinatorialMap.edgeInv d) =
      B'.map.toCombinatorialMap.edgeInv (toEquiv d)
  missing_iff : ∀ d, B'.map.missing (toEquiv d) ↔ B.map.missing d
  tail_iff : ∀ d, B'.map.tail (toEquiv d) ↔ B.map.tail d
  outer_iff : ∀ d, B'.map.IsOuter (toEquiv d) ↔ B.map.IsOuter d
  source_map : ∀ d, (dartTailVertex B.map d = B.source) ↔
    (dartTailVertex B'.map (toEquiv d) = B'.source)
  sink_map : ∀ d, (dartTailVertex B.map d = B.sink) ↔
    (dartTailVertex B'.map (toEquiv d) = B'.sink)
  leftDarts : B.leftPath.darts.map toEquiv = B'.leftPath.darts
  rightDarts : B.rightPath.darts.map toEquiv = B'.rightPath.darts
namespace BipolarBoundaryBaseIso
variable {B : BipolarTriangulationWithBoundaryBase D ℓ r}
  {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
/-- The inverse boundary-preserving dart isomorphism. -/
@[expose] def symm (I : BipolarBoundaryBaseIso B B') :
    BipolarBoundaryBaseIso B' B where
  toEquiv := I.toEquiv.symm
  rot_comm := by
    intro d
    simpa using (congrArg I.toEquiv.symm
      (I.rot_comm (I.toEquiv.symm d))).symm
  edgeInv_comm := by
    intro d
    simpa using (congrArg I.toEquiv.symm
      (I.edgeInv_comm (I.toEquiv.symm d))).symm
  missing_iff := by
    intro d
    simpa using (I.missing_iff (I.toEquiv.symm d)).symm
  tail_iff := by
    intro d
    simpa using (I.tail_iff (I.toEquiv.symm d)).symm
  outer_iff := by
    intro d
    simpa using (I.outer_iff (I.toEquiv.symm d)).symm
  source_map := by
    intro d
    simpa using (I.source_map (I.toEquiv.symm d)).symm
  sink_map := by
    intro d
    simpa using (I.sink_map (I.toEquiv.symm d)).symm
  leftDarts := by
    calc
      B'.leftPath.darts.map I.toEquiv.symm =
          (B.leftPath.darts.map I.toEquiv).map I.toEquiv.symm :=
        congrArg (List.map I.toEquiv.symm) I.leftDarts.symm
      _ = B.leftPath.darts := by simp
  rightDarts := by
    calc
      B'.rightPath.darts.map I.toEquiv.symm =
          (B.rightPath.darts.map I.toEquiv).map I.toEquiv.symm :=
        congrArg (List.map I.toEquiv.symm) I.rightDarts.symm
      _ = B.rightPath.darts := by simp
/-- Composition of boundary-preserving dart isomorphisms. -/
@[expose] def trans {D'' : Type*} [Fintype D''] [DecidableEq D'']
    {B'' : BipolarTriangulationWithBoundaryBase D'' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (J : BipolarBoundaryBaseIso B' B'') :
    BipolarBoundaryBaseIso B B'' where
  toEquiv := I.toEquiv.trans J.toEquiv
  rot_comm := by
    intro d
    simp only [Equiv.trans_apply]
    rw [I.rot_comm, J.rot_comm]
  edgeInv_comm := by
    intro d
    simp only [Equiv.trans_apply]
    rw [I.edgeInv_comm, J.edgeInv_comm]
  missing_iff := by
    intro d
    exact (J.missing_iff (I.toEquiv d)).trans (I.missing_iff d)
  tail_iff := by
    intro d
    exact (J.tail_iff (I.toEquiv d)).trans (I.tail_iff d)
  outer_iff := by
    intro d
    exact (J.outer_iff (I.toEquiv d)).trans (I.outer_iff d)
  source_map := by
    intro d
    exact (I.source_map d).trans (J.source_map (I.toEquiv d))
  sink_map := by
    intro d
    exact (I.sink_map d).trans (J.sink_map (I.toEquiv d))
  leftDarts := by
    calc
      B.leftPath.darts.map (I.toEquiv.trans J.toEquiv) =
          (B.leftPath.darts.map I.toEquiv).map J.toEquiv := by simp
      _ = B''.leftPath.darts := by rw [I.leftDarts, J.leftDarts]
  rightDarts := by
    calc
      B.rightPath.darts.map (I.toEquiv.trans J.toEquiv) =
          (B.rightPath.darts.map I.toEquiv).map J.toEquiv := by simp
      _ = B''.rightPath.darts := by rw [I.rightDarts, J.rightDarts]
/-- The identity boundary-preserving dart isomorphism. -/
@[expose] def refl (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    BipolarBoundaryBaseIso B B where
  toEquiv := Equiv.refl D
  rot_comm := by intro d; rfl
  edgeInv_comm := by intro d; rfl
  missing_iff := by intro d; rfl
  tail_iff := by intro d; rfl
  outer_iff := by intro d; rfl
  source_map := by intro d; rfl
  sink_map := by intro d; rfl
  leftDarts := by simp
  rightDarts := by simp
end BipolarBoundaryBaseIso
end BoundaryIsomorphisms
/-- A finite dart-labelled map representative with its exact total edge count. -/
structure KMSWMapRep (ℓ r n : ℕ) where
  dartCount : ℕ
  B : BipolarTriangulationWithBoundaryBase (Fin dartCount) ℓ r
  edges : B.map.toCombinatorialMap.numEdges = n
namespace KMSWMapRep
/-- Representatives are equivalent exactly when a boundary-preserving map isomorphism exists. -/
@[expose] def isoSetoid (ℓ r n : ℕ) : Setoid (KMSWMapRep ℓ r n) where
  r R R' := Nonempty (BipolarBoundaryBaseIso R.B R'.B)
  iseqv := by
    constructor
    · intro R
      exact ⟨BipolarBoundaryBaseIso.refl R.B⟩
    · intro R R' h
      exact h.elim fun I => ⟨I.symm⟩
    · intro R R' R'' h₁ h₂
      exact h₁.elim fun I => h₂.elim fun J => ⟨I.trans J⟩
end KMSWMapRep
/-- The full quotient of representatives by the stated map isomorphisms. -/
@[expose] def KMSWMapIsoClass (ℓ r n : ℕ) :=
  Quotient (KMSWMapRep.isoSetoid ℓ r n)
section GeneralLDP
variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
private theorem simplePath_length_lt_cardBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    n < B.map.toCombinatorialMap.numVertices := by
  classical
  have hlen := P.vertices_nodup.length_le_card
  rw [P.vertices_length] at hlen
  have hcard : n + 1 ≤ B.map.toCombinatorialMap.numVertices := by
    simpa [CombinatorialMap.numVertices] using hlen
  omega
/-- Exactly realized simple source-to-sink path lengths, stored in a finite bounded set. -/
@[expose] noncomputable def sourceSinkPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Finset ℕ := by
  classical
  exact (Finset.range B.map.toCombinatorialMap.numVertices).filter fun n =>
    ∃ _P : SimpleDirectedDartPath B.map B.source B.sink n, True
theorem mem_sourceSinkPathLengthsBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (n : ℕ) :
    n ∈ sourceSinkPathLengthsBase B ↔
      ∃ _P : SimpleDirectedDartPath B.map B.source B.sink n, True := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨P, _⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (simplePath_length_lt_cardBase B P), ⟨P, trivial⟩⟩
theorem sourceSinkPathLengthsBase_nonempty
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (sourceSinkPathLengthsBase B).Nonempty := by
  refine ⟨ℓ, ?_⟩
  exact (mem_sourceSinkPathLengthsBase B ℓ).2 ⟨B.leftPath, trivial⟩
/-- The attained maximum of this nonempty finite path-length set. -/
@[expose] noncomputable def ldpLengthBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : ℕ :=
  (sourceSinkPathLengthsBase B).max' (sourceSinkPathLengthsBase_nonempty B)
end GeneralLDP
/-- All total edge counts of map classes with these two fixed boundary lengths. -/
@[expose] noncomputable def BoltzmannSpace (ℓ r : ℕ) :=
  Σ n : ℕ, KMSWMapIsoClass ℓ r n
/-- The discrete measurable space: all subsets of these map classes are measurable. -/
noncomputable instance (ℓ r : ℕ) : MeasurableSpace (BoltzmannSpace ℓ r) := ⊤
/-- An n-edge map has Boltzmann weight (1/3)^n. -/
@[expose] noncomputable def boltzmannWeight {ℓ r : ℕ}
    (ω : BoltzmannSpace ℓ r) : ℝ≥0∞ :=
  (1 / 3 : ℝ≥0∞) ^ ω.1
end DirectedDistances.PlanarMap
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap
/-- All left boundary lengths with the fixed right boundary length. -/
@[expose] noncomputable def AllBoltzmannSpace (r : ℕ) :=
  Σ ell : ℕ, BoltzmannSpace ell r
/-- The discrete measurable space: all subsets of these map classes are measurable. -/
noncomputable instance (r : ℕ) : MeasurableSpace (AllBoltzmannSpace r) := ⊤
/-- The underlying map's exact Boltzmann edge-count weight. -/
@[expose] noncomputable def allBoltzmannWeight {r : ℕ}
    (q : AllBoltzmannSpace r) : ENNReal := boltzmannWeight q.2
/-- A map with fixed RIGHT boundary length and a marked LEFT boundary vertex position. -/
@[expose] noncomputable def RightVertexMarkedBoltzmannSpace (r : ℕ) :=
  Σ q : AllBoltzmannSpace r, Fin (q.1 + 1)
/-- The discrete measurable space: all subsets of these map classes are measurable. -/
noncomputable instance (r : ℕ) :
    MeasurableSpace (RightVertexMarkedBoltzmannSpace r) := ⊤
/-- Each marked class retains its underlying map's weight (1/3)^n. -/
@[expose] noncomputable def rightVertexMarkedWeight {r : ℕ}
    (p : RightVertexMarkedBoltzmannSpace r) : ENNReal :=
  allBoltzmannWeight p.1
/-- The sum of weights over all marked map classes. -/
@[expose] noncomputable def rightVertexMarkedPartition (r : ℕ) : ENNReal :=
  ∑' p : RightVertexMarkedBoltzmannSpace r, rightVertexMarkedWeight p
/-- The exact normalized sum of weighted atoms; a probability law for positive r. -/
@[expose] noncomputable def rightVertexMarkedBoltzmannLaw (r : ℕ) :
    Measure (RightVertexMarkedBoltzmannSpace r) :=
  (rightVertexMarkedPartition r)⁻¹ •
    Measure.sum (fun p : RightVertexMarkedBoltzmannSpace r =>
      rightVertexMarkedWeight p • Measure.dirac p)
end DirectedDistances.KMSW
namespace DirectedDistances
universe u v
variable {V : Type u} [Quiver.{v} V]
/-- Infimum of all quiver path lengths in ENat, including infinity when unreachable. -/
@[expose] noncomputable def sdp (a b : V) : ℕ∞ :=
  ⨅ p : Path a b, (p.length : ℕ∞)
end DirectedDistances
namespace DirectedDistances.PaperProofs.Section7
open DirectedDistances.KMSW DirectedDistances.PlanarMap
/-- One arrow per present oriented dart; geometric parallel edges are preserved. -/
instance presentDartQuiver {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) : Quiver (MapVertex M) where
  Hom v w :=
    {d : D // ¬ M.missing d ∧ M.tail d ∧
      dartTailVertex M d = v ∧ dartHeadVertex M d = w}
/-- Shortest directed distance in that actual present-dart quiver. -/
@[expose] noncomputable def presentDartSDP {D : Type*} [Fintype D]
    [DecidableEq D] (M : DirectedMapWithMissing D) (v w : MapVertex M) : ℕ∞ := by
  exact DirectedDistances.sdp v w
/-- The source-to-sink indexed vertex of the representative's actual right boundary. -/
@[expose] noncomputable def rightBoundaryVertex {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) (i : Fin (r + 1)) :
    MapVertex q.1.2.2.out.B.map :=
  q.1.2.2.out.B.rightPath.vertices.get ⟨i.val, by
    rw [q.1.2.2.out.B.rightPath.vertices_length]
    omega⟩
end DirectedDistances.PaperProofs.Section7
end

namespace DLQG1.Palomar.Principal
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section7
/-- Theorem 1.11: one A(delta) gives all three simultaneous Boltzmann distance bounds
for every positive r. -/
theorem boltzmann_distances (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q : RightVertexMarkedBoltzmannSpace r |
          (A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (ldpLengthBase q.1.2.2.out.B : ℝ) ∧
            (ldpLengthBase q.1.2.2.out.B : ℝ) ≤ A * (r : ℝ) ^ (3 / 2 : ℝ)) ∧
          ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
              ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ)) ∧
          ∃ i : Fin (r + 1),
            ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ (3 / 4 : ℝ)) ≤
              ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
                q.1.2.2.out.B.source (rightBoundaryVertex q i))} := by
  sorry
end DLQG1.Palomar.Principal
