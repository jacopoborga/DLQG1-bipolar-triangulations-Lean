/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic

import Mathlib.Tactic.FinCases

/-! # Finite combinatorial planar maps

Rotation systems on darts, with faces represented by cycles of the face
permutation. The convention below takes `rot⁻¹ * edgeInv` as the permutation
whose cycles are faces; `rot d` is the next dart counter-clockwise around the
vertex of `d`, and the face-successor orbit of `d` is the face on its left as
`d` runs from its own vertex to the vertex of `edgeInv d`. Planarity is the
combinatorial connectedness and Euler characteristic condition. Only the
upper-left and lower-right boundary dart sets are defined so far; upper-right
and lower-left runs require a separate four-arcs hypothesis. -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- A finite combinatorial map: `edgeInv` exchanges the two darts of each
edge, and `rot` advances counter-clockwise around a vertex. This is the
combinatorial carrier for the planar maps in `sec-kmsw` -/
structure CombinatorialMap (D : Type*) [Fintype D] [DecidableEq D] where
  edgeInv : Equiv.Perm D
  edgeInv_invol : ∀ d, edgeInv (edgeInv d) = d
  edgeInv_ne : ∀ d, edgeInv d ≠ d
  rot : Equiv.Perm D

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The face permutation `rot⁻¹ * edgeInv`; thus
`faceSucc d = rot⁻¹ (edgeInv d)`. Here `rot d` is the next dart
counter-clockwise around the vertex of `d`, and the `faceSucc`-orbit of `d`
is the face on its left when `d` runs from its own vertex to the vertex of -/
@[expose] def faceSucc (M : CombinatorialMap D) : Equiv.Perm D :=
  M.rot⁻¹ * M.edgeInv

/-- A dart lies in the marked face cycle of a combinatorial map. The marked
dart represents the face only through its face-permutation orbit -/
@[expose] def IsOuter (M : CombinatorialMap D) (outer d : D) : Prop :=
  Equiv.Perm.SameCycle M.faceSucc outer d

/-- Darts belong to the same vertex when they lie in one rotation cycle -/
def VertexRel (M : CombinatorialMap D) : D → D → Prop :=
  Equiv.Perm.SameCycle M.rot

/-- Darts belong to the same edge when they lie in one edge-involution cycle -/
def EdgeRel (M : CombinatorialMap D) : D → D → Prop :=
  Equiv.Perm.SameCycle M.edgeInv

/-- Darts belong to the same face when they lie in one face-permutation cycle -/
def FaceRel (M : CombinatorialMap D) : D → D → Prop :=
  Equiv.Perm.SameCycle M.faceSucc

/-- The quotient whose elements are the vertices of `M` -/
abbrev VertexQuotient (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.rot)

/-- The quotient whose elements are the edges of `M` -/
abbrev EdgeQuotient (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.edgeInv)

/-- The quotient whose elements are the faces of `M` -/
abbrev FaceQuotient (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.faceSucc)

/-- Number of vertices, including singleton rotation cycles -/
@[expose] noncomputable def numVertices (M : CombinatorialMap D) : ℕ := by
  classical
  exact Fintype.card (VertexQuotient M)

/-- Number of edges, including loops and parallel edges as separate orbits -/
@[expose] noncomputable def numEdges (M : CombinatorialMap D) : ℕ := by
  classical
  exact Fintype.card (EdgeQuotient M)

/-- Number of faces, including singleton face cycles -/
@[expose] noncomputable def numFaces (M : CombinatorialMap D) : ℕ := by
  classical
  exact Fintype.card (FaceQuotient M)

/-- Reachability through rotations, inverse rotations, and edge involutions;
used for the finite combinatorial connectedness condition on planar maps -/
@[expose] def IsConnected (M : CombinatorialMap D) : Prop :=
  ∀ d e, Relation.ReflTransGen
    (fun x y : D => y = M.rot x ∨ y = M.rot.symm x ∨
      y = M.edgeInv x ∨ y = M.edgeInv.symm x) d e

/-- The combinatorial Euler characteristic `V - E + F` of the carrier -/
@[expose] noncomputable def eulerChar (M : CombinatorialMap D) : ℤ :=
  (M.numVertices : ℤ) - M.numEdges + M.numFaces

/-- Genus-zero combinatorial planarity: connectedness and Euler characteristic -/
@[expose] def IsPlanar (M : CombinatorialMap D) : Prop :=
  M.IsConnected ∧ M.eulerChar = 2

private def edgeFiber (M : CombinatorialMap D) (q : EdgeQuotient M) :=
  {d : D // Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) d = q}

/-- The edge orbit of a dart consists of it and its opposite dart. -/
theorem edgeInv_sameCycle_iff (M : CombinatorialMap D) (d e : D) :
    M.edgeInv.SameCycle d e ↔ e = d ∨ e = M.edgeInv d := by
  constructor
  · intro h
    have hpow : M.edgeInv ^ 2 = 1 := by
      ext x
      simp [pow_two, M.edgeInv_invol]
    have hle : orderOf M.edgeInv ≤ 2 :=
      orderOf_le_of_pow_eq_one (by decide) hpow
    have hpos : 0 < orderOf M.edgeInv := orderOf_pos M.edgeInv
    have hne : orderOf M.edgeInv ≠ 1 := by
      intro hone
      have hid := pow_orderOf_eq_one M.edgeInv
      rw [hone] at hid
      have heq : M.edgeInv = 1 := by simpa using hid
      exact M.edgeInv_ne d (by simp [heq])
    have hord : orderOf M.edgeInv = 2 := by omega
    obtain ⟨i, hi, hde⟩ := h.exists_pow_eq'
    rw [hord] at hi
    cases i with
    | zero =>
        left
        simpa using hde.symm
    | succ i =>
        have hi0 : i = 0 := by omega
        subst i
        right
        simpa using hde.symm
  · intro h
    rcases h with h | h
    · subst e
      exact Equiv.Perm.SameCycle.rfl
    · subst e
      exact ⟨1, by simp⟩

private noncomputable def edgeFiberEquiv (M : CombinatorialMap D) (d : D) :
    Fin 2 ≃ edgeFiber M (Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) d) := by
  classical
  let f : Fin 2 → edgeFiber M (Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) d) :=
    fun i => ⟨(if i = 0 then d else M.edgeInv d), by
      apply Quotient.sound
      by_cases hi : i = 0
      · simp [hi]
      · simp only [hi, ↓reduceIte]
        exact ⟨1, by simp [M.edgeInv_invol]⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hv := congrArg Subtype.val hij
      simp [f] at hv
      exact False.elim (M.edgeInv_ne d hv.symm)
    · have hv := congrArg Subtype.val hij
      simp [f] at hv
      exact False.elim (M.edgeInv_ne d hv)
    · rfl
  · intro x
    have hrel : M.edgeInv.SameCycle d x.1 := (Quotient.exact x.2).symm
    rcases (edgeInv_sameCycle_iff M d x.1).mp hrel with h | h
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [f, h]
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      simp [f, h]

private noncomputable def edgeFiberEquiv' (M : CombinatorialMap D) (q : EdgeQuotient M) :
    Fin 2 ≃ edgeFiber M q := by
  classical
  let d := Quotient.out q
  have hd : Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) d = q :=
    Quotient.out_eq' q
  let transport : edgeFiber M (Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) d) ≃
      edgeFiber M q :=
    { toFun := fun x => ⟨x.1, x.2.trans hd⟩
      invFun := fun x => ⟨x.1, x.2.trans hd.symm⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  exact (edgeFiberEquiv M d).trans transport

/-- Every edge orbit contains exactly two darts, so twice the number of edges -/
theorem two_mul_numEdges (M : CombinatorialMap D) :
    2 * M.numEdges = Fintype.card D := by
  classical
  let fiber := fun q : EdgeQuotient M => edgeFiber M q
  let fiberFintype : ∀ q : EdgeQuotient M, Fintype (fiber q) := fun q =>
    Fintype.ofEquiv (Fin 2) (edgeFiberEquiv' M q)
  let sigmaFintype : Fintype (Σ q : EdgeQuotient M, fiber q) :=
    @Sigma.instFintype (EdgeQuotient M) fiber fiberFintype inferInstance
  let e : D ≃ Σ q : EdgeQuotient M, fiber q :=
    { toFun := fun d => ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) d,
        ⟨d, rfl⟩⟩
      invFun := fun q => q.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨q, d, rfl⟩
        rfl }
  have hcard : Fintype.card D = 2 * Fintype.card (EdgeQuotient M) := by
    calc
      Fintype.card D = @Fintype.card (Σ q : EdgeQuotient M, fiber q) sigmaFintype :=
        @Fintype.card_congr D (Σ q : EdgeQuotient M, fiber q) inferInstance sigmaFintype e
      _ = ∑ q : EdgeQuotient M, @Fintype.card (fiber q) (fiberFintype q) :=
        @Fintype.card_sigma (EdgeQuotient M) fiber inferInstance fiberFintype
      _ = ∑ _q : EdgeQuotient M, 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        simpa using
          (@Fintype.card_congr (Fin 2) (fiber q) inferInstance (fiberFintype q)
            (edgeFiberEquiv' M q)).symm
      _ = 2 * Fintype.card (EdgeQuotient M) := by simp [Finset.sum_const, mul_comm]
  simpa [numEdges, EdgeQuotient] using hcard.symm

end CombinatorialMap

/-- A directed combinatorial map with missing edges. Present edges are
oriented by designating exactly one of their two darts as the initial dart;
missing edges remain unoriented and lie on the distinguished outer face.
This is the carrier for Definition `defn:planar-map-with-missing-edges` -/
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

/-- Darts in the distinguished external face are identified by the orbit of
`outer`; the particular marked dart is not otherwise used -/
@[expose] def IsOuter (M : DirectedMapWithMissing D) (d : D) : Prop :=
  CombinatorialMap.IsOuter M.toCombinatorialMap M.outer d

/-- One oriented present edge as a step between rotation-cycle vertices. -/
@[expose] def directedStep (M : DirectedMapWithMissing D)
    (v w : CombinatorialMap.VertexQuotient M.toCombinatorialMap) : Prop :=
  ∃ d, ¬ M.missing d ∧ M.tail d ∧
    Quotient.mk (Equiv.Perm.SameCycle.setoid M.rot) d = v ∧
    Quotient.mk (Equiv.Perm.SameCycle.setoid M.rot) (M.edgeInv d) = w

/-- The orientation is acyclic when no nonempty directed path in the rotation
quotient returns to its starting vertex (`defn:planar-map-with-missing-edges`, -/
@[expose] def IsAcyclic (M : DirectedMapWithMissing D) : Prop :=
  ∀ v : CombinatorialMap.VertexQuotient M.toCombinatorialMap,
    ¬ Relation.TransGen (directedStep M) v v

/-- Initial darts of present edges on the outer face with the outer face to -/
@[expose] def ulDarts (M : DirectedMapWithMissing D) : Set D :=
  {d | ¬ M.missing d ∧ M.tail d ∧ M.IsOuter d}

/-- Non-tail darts of present edges on the external face. An edge is on the
lower-right boundary exactly when its non-tail dart is in this set -/
@[expose] def lrDarts (M : DirectedMapWithMissing D) : Set D :=
  {d | ¬ M.missing d ∧ ¬ M.tail d ∧ M.IsOuter d}

/-- An edge orbit is upper-left when it has a tail dart in `ulDarts` -/
@[expose] def IsUpperLeftEdge (M : DirectedMapWithMissing D)
    (e : CombinatorialMap.EdgeQuotient M.toCombinatorialMap) : Prop :=
  ∃ d, Quotient.mk
      (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.edgeInv) d = e ∧
    d ∈ M.ulDarts

/-- An edge orbit is lower-right when its non-tail dart is in `lrDarts`,
equivalently when the external face lies to the right of its tail dart -/
@[expose] def IsLowerRightEdge (M : DirectedMapWithMissing D)
    (e : CombinatorialMap.EdgeQuotient M.toCombinatorialMap) : Prop :=
  ∃ d, Quotient.mk
      (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.edgeInv) d = e ∧
    d ∈ M.lrDarts

/-- For a tail representative, upper-left edge membership is exactly tail-dart
membership in `ulDarts` (`defn:bound-edges`, -/
theorem isUpperLeftEdge_iff_tail_mem_ulDarts (M : DirectedMapWithMissing D)
    (d : D) (htail : M.tail d) :
    M.IsUpperLeftEdge
      (Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.edgeInv) d) ↔
        d ∈ M.ulDarts := by
  constructor
  · rintro ⟨e, he, heul⟩
    have hrel : M.toCombinatorialMap.edgeInv.SameCycle d e :=
      (Quotient.exact he).symm
    rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap d e).mp hrel with
      hde | hde
    · simpa [hde] using heul
    · subst e
      have hpresent : ¬ M.missing d := by
        intro hmiss
        exact (M.tail_missing d hmiss) htail
      have hnotTail : ¬ M.tail (M.toCombinatorialMap.edgeInv d) :=
        (M.tail_iff d hpresent).mp htail
      exact False.elim (hnotTail heul.2.1)
  · intro hd
    exact ⟨d, rfl, hd⟩

/-- For a tail representative, lower-right edge membership is exactly
membership of its non-tail dart in `lrDarts` (`defn:bound-edges`, -/
theorem isLowerRightEdge_iff_nontail_mem_lrDarts (M : DirectedMapWithMissing D)
    (d : D) (htail : M.tail d) :
    M.IsLowerRightEdge
      (Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.edgeInv) d) ↔
        M.toCombinatorialMap.edgeInv d ∈ M.lrDarts := by
  constructor
  · rintro ⟨e, he, helr⟩
    have hrel : M.toCombinatorialMap.edgeInv.SameCycle d e :=
      (Quotient.exact he).symm
    rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap d e).mp hrel with
      hde | hde
    · subst e
      exact False.elim (helr.2.1 htail)
    · simpa [hde] using helr
  · intro hd
    refine ⟨M.toCombinatorialMap.edgeInv d, ?_, hd⟩
    apply Quotient.sound
    exact ⟨1, by simp [M.toCombinatorialMap.edgeInv_invol]⟩

/-- Number of present edge orbits; the paper's `𝓔(m)` excludes missing edges -/
@[expose] noncomputable def numPresentEdges (M : DirectedMapWithMissing D) : ℕ := by
  classical
  exact Fintype.card
    {e : CombinatorialMap.EdgeQuotient M.toCombinatorialMap //
      ∃ d, Quotient.mk
        (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.edgeInv) d = e ∧
        ¬ M.missing d}

/-- Number of inner faces, excluding the marked external face; this is the
paper's `𝓕(m)` (`defn:planar-map-with-missing-edges`, -/
@[expose] noncomputable def numInnerFaces (M : DirectedMapWithMissing D) : ℕ :=
  M.toCombinatorialMap.numFaces - 1

end DirectedMapWithMissing

/-! ## KMSW initial map -/

namespace CombinatorialMap

/-- The KMSW initial map `m₀`: one edge with two darts, two vertices, and one -/
@[expose] def singleEdge : CombinatorialMap (Fin 2) where
  edgeInv := Equiv.swap 0 1
  edgeInv_invol := by
    intro d
    fin_cases d <;> simp
  edgeInv_ne := by
    intro d
    fin_cases d <;> simp
  rot := 1

/-- The one-edge map with dart `0` as its unique initial dart, no missing
edges, and its unique face marked external (`def-kmsw`, -/
@[expose] def singleEdgeDirected : DirectedMapWithMissing (Fin 2) where
  toCombinatorialMap := singleEdge
  missing := fun _ => False
  missing_edgeInv := by
    intro d
    simp
  tail := fun d => d = 0
  tail_iff := by
    intro d hd
    fin_cases d <;> simp [singleEdge]
  tail_missing := by
    intro d hd
    exact False.elim hd
  outer := 0
  missing_outer := by
    intro d hd
    exact False.elim hd

private theorem singleEdge_face_related (d e : Fin 2) :
    (singleEdge.faceSucc).SameCycle d e := by
  fin_cases d <;> fin_cases e
  · exact Equiv.Perm.SameCycle.rfl
  · exact ⟨1, by simp [singleEdge, faceSucc]⟩
  · exact ⟨1, by simp [singleEdge, faceSucc]⟩
  · exact Equiv.Perm.SameCycle.rfl

/-- The initial map has two vertices (`def-kmsw`, -/
theorem numVertices_singleEdge : singleEdge.numVertices = 2 := by
  classical
  let e : VertexQuotient singleEdge ≃ Fin 2 :=
    { toFun := Quotient.lift (fun d : Fin 2 => d) (by
        intro a b hab
        have hab' : (1 : Equiv.Perm (Fin 2)).SameCycle a b := by
          change singleEdge.rot.SameCycle a b
          exact hab
        exact Equiv.Perm.sameCycle_one.mp hab')
      invFun := fun d => Quotient.mk (Equiv.Perm.SameCycle.setoid singleEdge.rot) d
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        rfl
      right_inv := by intro d; rfl }
  calc
    singleEdge.numVertices = Fintype.card (VertexQuotient singleEdge) := rfl
    _ = Fintype.card (Fin 2) := Fintype.card_congr e
    _ = 2 := Fintype.card_fin 2

/-- The initial map has one edge (`def-kmsw`, -/
theorem numEdges_singleEdge : singleEdge.numEdges = 1 := by
  have h := two_mul_numEdges singleEdge
  simp only [Fintype.card_fin] at h
  omega

/-- The initial map has one face (`def-kmsw`, -/
theorem numFaces_singleEdge : singleEdge.numFaces = 1 := by
  classical
  let e : FaceQuotient singleEdge ≃ Unit :=
    { toFun := fun _ => Unit.unit
      invFun := fun _ => Quotient.mk (Equiv.Perm.SameCycle.setoid singleEdge.faceSucc) 0
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro d
        apply Quotient.sound
        exact (singleEdge_face_related d 0).symm
      right_inv := by intro x; cases x; rfl }
  calc
    singleEdge.numFaces = Fintype.card (FaceQuotient singleEdge) := rfl
    _ = Fintype.card Unit := Fintype.card_congr e
    _ = 1 := Fintype.card_unit

/-- In the directed initial map, the one edge is both upper-left and
lower-right; both darts lie in its unique face cycle -/
theorem singleEdge_both_boundary_edges :
    DirectedMapWithMissing.IsUpperLeftEdge singleEdgeDirected
        (Quotient.mk
          (Equiv.Perm.SameCycle.setoid singleEdgeDirected.toCombinatorialMap.edgeInv) 0) ∧
      DirectedMapWithMissing.IsLowerRightEdge singleEdgeDirected
        (Quotient.mk
          (Equiv.Perm.SameCycle.setoid singleEdgeDirected.toCombinatorialMap.edgeInv) 0) := by
  have htail : singleEdgeDirected.tail (0 : Fin 2) := by
    simp [singleEdgeDirected]
  have houter0 : singleEdgeDirected.IsOuter (0 : Fin 2) := by
    change singleEdge.faceSucc.SameCycle 0 0
    exact Equiv.Perm.SameCycle.rfl
  have houter1 : singleEdgeDirected.IsOuter (1 : Fin 2) := by
    change singleEdge.faceSucc.SameCycle 0 1
    exact singleEdge_face_related 0 1
  have hul : (0 : Fin 2) ∈ singleEdgeDirected.ulDarts := by
    change ¬ singleEdgeDirected.missing 0 ∧
      singleEdgeDirected.tail 0 ∧ singleEdgeDirected.IsOuter 0
    exact ⟨by simp [singleEdgeDirected], htail, houter0⟩
  have hlr : (1 : Fin 2) ∈ singleEdgeDirected.lrDarts := by
    change ¬ singleEdgeDirected.missing 1 ∧
      ¬ singleEdgeDirected.tail 1 ∧ singleEdgeDirected.IsOuter 1
    exact ⟨by simp [singleEdgeDirected], by simp [singleEdgeDirected], houter1⟩
  constructor
  · exact (DirectedMapWithMissing.isUpperLeftEdge_iff_tail_mem_ulDarts
      singleEdgeDirected 0 htail).2 hul
  · have hnonTail : singleEdgeDirected.toCombinatorialMap.edgeInv 0 = 1 := by
      simp [singleEdgeDirected, singleEdge]
    rw [DirectedMapWithMissing.isLowerRightEdge_iff_nontail_mem_lrDarts
      singleEdgeDirected 0 htail, hnonTail]
    exact hlr

/-- The one-edge initial map is connected (`def-kmsw`, -/
theorem singleEdge_connected : singleEdge.IsConnected := by
  intro d e
  fin_cases d <;> fin_cases e
  · exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.single
    simp [singleEdge]
  · apply Relation.ReflTransGen.single
    simp [singleEdge]
  · exact Relation.ReflTransGen.refl

/-- The KMSW initial map is combinatorially planar (`def-kmsw`, -/
theorem singleEdge_isPlanar : singleEdge.IsPlanar := by
  constructor
  · exact singleEdge_connected
  · simp [eulerChar, numVertices_singleEdge, numEdges_singleEdge,
      numFaces_singleEdge]

end CombinatorialMap

end DirectedDistances.PlanarMap
