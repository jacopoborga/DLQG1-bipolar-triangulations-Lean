/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BdyReverseRelabelCarrier
public import DirectedDistances.PlanarMap.BdyReverseBijective
public import DirectedDistances.PlanarMap.BdyReverseLeftEndpoint
public import DirectedDistances.PlanarMap.BdyReverseSizedSlices

/-! # Equivariance of restricted boundary reversal under relabelling

Helpers toward `lem-bdy-reverse`
declarations here are helpers only and are not counted as the paper result. -/

public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

open BipolarTriangulationWithBoundary

private theorem rightPrefixReversal_leftPath_vertices
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal B k hk hkr hbc).leftPath.vertices =
      (B.rightPath.vertices.take (k + 1)).reverse ++ B.leftPath.vertices.drop 1 := by
  exact (Classical.choice (rightPrefixBoundaryPaths_exists B k hk hkr)).leftPath_vertices

private theorem rightPrefixReversal_rightPath_vertices
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal B k hk hkr hbc).rightPath.vertices =
      B.rightPath.vertices.drop k := by
  exact (Classical.choice (rightPrefixBoundaryPaths_exists B k hk hkr)).rightPath_vertices

private theorem simplePath_vertices_eq_of_darts_eq
    {M : DirectedMapWithMissing D} {s t s' t' : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n)
    (Q : SimpleDirectedDartPath M s' t' n)
    (hs : s = s') (hd : P.darts = Q.darts) : P.vertices = Q.vertices := by
  apply List.ext_getElem
  · rw [P.vertices_length, Q.vertices_length]
  · intro i hiP hiQ
    by_cases hzero : i = 0
    · subst i
      simpa only [List.get_eq_getElem] using
        P.start_vertex.trans (hs.trans Q.start_vertex.symm)
    · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
      have hin : i ≤ n := by rw [P.vertices_length] at hiP; omega
      have hdiP : i - 1 < P.darts.length := by rw [P.darts_length]; omega
      have hdiQ : i - 1 < Q.darts.length := by rw [Q.darts_length]; omega
      let jP : Fin P.darts.length := ⟨i - 1, hdiP⟩
      let jQ : Fin Q.darts.length := ⟨i - 1, hdiQ⟩
      have hP := P.edge_step jP
      have hQ := Q.edge_step jQ
      have hPhead : P.vertices[i]'hiP =
          dartHeadVertex M (P.darts[i - 1]'hdiP) := by
        have hidx : jP.val + 1 = i := by dsimp [jP]; omega
        simpa only [List.get_eq_getElem, jP, hidx] using hP.2.2.2
      have hQhead : Q.vertices[i]'hiQ =
          dartHeadVertex M (Q.darts[i - 1]'hdiQ) := by
        have hidx : jQ.val + 1 = i := by dsimp [jQ]; omega
        simpa only [List.get_eq_getElem, jQ, hidx] using hQ.2.2.2
      have hQhead' : Q.vertices[i]'hiQ =
          dartHeadVertex M (P.darts[i - 1]'hdiP) := by
        simpa only [hd] using hQhead
      exact hPhead.trans hQhead'.symm

private theorem simpleDirectedDartPath_hext
    {M N : DirectedMapWithMissing D} {s t : MapVertex M} {s' t' : MapVertex N}
    {n : ℕ} (P : SimpleDirectedDartPath M s t n)
    (Q : SimpleDirectedDartPath N s' t' n)
    (hM : M = N) (hs : HEq s s') (ht : HEq t t')
    (hd : P.darts = Q.darts) : HEq P Q := by
  subst N
  have hs' : s = s' := eq_of_heq hs
  subst s'
  have ht' : t = t' := eq_of_heq ht
  subst t'
  have hv : P.vertices = Q.vertices :=
    simplePath_vertices_eq_of_darts_eq P Q rfl hd
  cases P with
  | mk pd pv pdl pvl pnod pstart pend pstep =>
    cases Q with
    | mk qd qv qdl qvl qnod qstart qend qstep =>
      dsimp at hd hv
      subst qd
      subst qv
      rfl

/-- The whole restricted right-prefix reversal commutes with dart relabelling -/
theorem rightPrefixReversal_relabel {ℓ r : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D ℓ r)
    (k : ℕ) (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    rightPrefixReversal (B.relabel σ) k hk hkr
      ((B.relabel_InMbc_iff σ).2 hbc) =
    (rightPrefixReversal B k hk hkr hbc).relabel σ := by
  have hbc0 : InMbc ℓ r B := hbc
  have hbc' : (B.relabel σ).IsBoundaryChanneled :=
    (B.relabel_InMbc_iff σ).2 hbc0
  have hmap := rightPrefixReversal_relabel_map σ B k hk hkr hbc
  apply BipolarTriangulationWithBoundary.hext_fields
  · exact hmap
  · change HEq (rightBoundaryVertexAt (B.relabel σ) k (Nat.le_of_lt hkr))
      (DirectedMapWithMissing.relabelVertexEquiv σ
        (rightPrefixReversal B k hk hkr hbc).map
        (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)))
    have hv : DirectedMapWithMissing.relabelVertexEquiv σ B.map
        (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) =
          rightBoundaryVertexAt (B.relabel σ) k (Nat.le_of_lt hkr) := by
      simp [rightBoundaryVertexAt, BipolarTriangulationWithBoundary.relabel,
        SimpleDirectedDartPath.relabel_vertices]
    exact heq_of_eq hv.symm
  · simp only [rightPrefixReversal_sink, BipolarTriangulationWithBoundary.relabel]
    exact HEq.rfl
  · simp only [rightPrefixReversal_outerWord, BipolarTriangulationWithBoundary.relabel]
  · apply simpleDirectedDartPath_hext
        (P := (rightPrefixReversal (B.relabel σ) k hk hkr
          hbc').leftPath)
        (Q := SimpleDirectedDartPath.relabel σ
          (rightPrefixReversal B k hk hkr hbc).leftPath)
    · exact rightPrefixReversal_relabel_map σ B k hk hkr hbc
    · change HEq (rightBoundaryVertexAt (B.relabel σ) k (Nat.le_of_lt hkr))
        (DirectedMapWithMissing.relabelVertexEquiv σ
          (rightPrefixReversal B k hk hkr hbc).map
          (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)))
      have hv : DirectedMapWithMissing.relabelVertexEquiv σ B.map
          (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) =
            rightBoundaryVertexAt (B.relabel σ) k (Nat.le_of_lt hkr) := by
        simp [rightBoundaryVertexAt, BipolarTriangulationWithBoundary.relabel,
          SimpleDirectedDartPath.relabel_vertices]
      exact heq_of_eq hv.symm
    · simp only [rightPrefixReversal_sink, BipolarTriangulationWithBoundary.relabel]
      exact HEq.rfl
    · rw [rightPrefixReversal_relabel_leftPath_darts]
      rfl
  · apply simpleDirectedDartPath_hext
        (P := (rightPrefixReversal (B.relabel σ) k hk hkr
          hbc').rightPath)
        (Q := SimpleDirectedDartPath.relabel σ
          (rightPrefixReversal B k hk hkr hbc).rightPath)
    · exact rightPrefixReversal_relabel_map σ B k hk hkr hbc
    · change HEq (rightBoundaryVertexAt (B.relabel σ) k (Nat.le_of_lt hkr))
        (DirectedMapWithMissing.relabelVertexEquiv σ
          (rightPrefixReversal B k hk hkr hbc).map
          (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)))
      have hv : DirectedMapWithMissing.relabelVertexEquiv σ B.map
          (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) =
            rightBoundaryVertexAt (B.relabel σ) k (Nat.le_of_lt hkr) := by
        simp [rightBoundaryVertexAt, BipolarTriangulationWithBoundary.relabel,
          SimpleDirectedDartPath.relabel_vertices]
      exact heq_of_eq hv.symm
    · simp only [rightPrefixReversal_sink, BipolarTriangulationWithBoundary.relabel]
      exact HEq.rfl
    · rw [rightPrefixReversal_relabel_rightPath_darts]
      rfl

/-- The restricted right-prefix reversal map on boundary-channeled classes
commutes with dart relabelling (`lem-bdy-reverse`,
`lem-bdy-reverse`, not the paper result. -/
theorem rightPrefixReversalMbc_relabel {ℓ r : ℕ}
    (σ : Equiv.Perm D) (k : ℕ) (hk : 1 ≤ k) (hkr : k < r)
    (B : BoundaryMbcClass D ℓ r) :
    rightPrefixReversalMbc (D := D) (ℓ := ℓ) (r := r) k hk hkr
      (relabelBoundaryMbcClass σ B) =
    relabelBoundaryMbcClass σ
      (rightPrefixReversalMbc (D := D) (ℓ := ℓ) (r := r) k hk hkr B) := by
  apply Subtype.ext
  exact rightPrefixReversal_relabel σ B.val k hk hkr B.property

/-- Relabelling on a fixed inner-edge size slice of boundary-channeled -/
@[expose] noncomputable def relabelBoundaryMbcSize {ℓ r : ℕ}
    (σ : Equiv.Perm D) (n : ℕ) :
    {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B ∧ innerEdgeCount B = n} →
    {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B ∧ innerEdgeCount B = n} := fun B =>
  ⟨B.val.relabel σ, (B.val.relabel_InMbc_iff σ).2 B.property.1,
    (B.val.relabel_innerEdgeCount σ).trans B.property.2⟩

/-- The fixed-size right-prefix reversal map commutes with dart relabelling -/
theorem rightPrefixReversalSize_relabel {ℓ r : ℕ}
    (σ : Equiv.Perm D) (k : ℕ) (hk : 1 ≤ k) (hkr : k < r) (n : ℕ)
    (B : {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B ∧ innerEdgeCount B = n}) :
    rightPrefixReversalSize (D := D) (ℓ := ℓ) k hk hkr n
      (relabelBoundaryMbcSize σ n B) =
    relabelBoundaryMbcSize σ n
      (rightPrefixReversalSize (D := D) (ℓ := ℓ) k hk hkr n B) := by
  apply Subtype.ext
  exact rightPrefixReversal_relabel σ B.val k hk hkr B.property.1

end DirectedDistances.PlanarMap
