/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable4

/-! # Quotient transport for the nonpositive right-side code

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. A marked isomorphism sends a vertex cell to a
vertex cell. -/
theorem rMinus_rightSideMarkedIso_vertex
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (v : M.vertices) :
    ∃ v' : N.vertices, phi.equiv (.inl v) = .inl v' := by
  cases h : phi.equiv (.inl v) with
  | inl w => exact ⟨w, rfl⟩
  | inr d =>
      have hv := (phi.relation_iff .vertex (.inl v) (.inl v)).mp (by
        simp [geometricSideRelation])
      simp [geometricSideRelation, h] at hv

/-- Helper toward Lemma 5.5. A marked isomorphism sends a dart cell to a
dart cell. -/
theorem rMinus_rightSideMarkedIso_dart
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    ∃ d' : {z : ℕ × Bool // z.1 ∈ N.edges}, phi.equiv (.inr d) = .inr d' := by
  cases h : phi.equiv (.inr d) with
  | inl v =>
      have hd := (phi.relation_iff .vertex (.inr d) (.inr d)).mpr (by
        simp [geometricSideRelation, h])
      simp [geometricSideRelation] at hd
  | inr e => exact ⟨e, rfl⟩

/-- Helper toward Lemma 5.5. The dart map induced by a marked isomorphism. -/
noncomputable def rMinus_rightSideMarkedIso_dartMap
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N) :
    {z : ℕ × Bool // z.1 ∈ M.edges} → {z : ℕ × Bool // z.1 ∈ N.edges} :=
  fun d => Classical.choose (rMinus_rightSideMarkedIso_dart phi d)

/-- Helper toward Lemma 5.5. The dart map is the action of the marked
isomorphism on geometric-side cells. -/
theorem rMinus_rightSideMarkedIso_dartMap_cell
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    phi.equiv (.inr d) = .inr (rMinus_rightSideMarkedIso_dartMap phi d) := by
  exact Classical.choose_spec (rMinus_rightSideMarkedIso_dart phi d)

/-- Helper toward Lemma 5.5. The marked isomorphism preserves directed
presence and the distinguished false endpoint bit. -/
theorem rMinus_rightSideMarkedIso_oriented
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    (d.val.1 ∈ M.present ∧ d.val.2 = false) ↔
      ((rMinus_rightSideMarkedIso_dartMap phi d).val.1 ∈ N.present ∧
        (rMinus_rightSideMarkedIso_dartMap phi d).val.2 = false) := by
  simpa [geometricSideRelation, rMinus_rightSideMarkedIso_dartMap_cell] using
    (phi.relation_iff .oriented (.inr d) (.inr d))

/-- Helper toward Lemma 5.5. The marked isomorphism preserves retained-face
succession on the induced hatted darts. -/
theorem rMinus_rightSideMarkedIso_faceNext
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (d e : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    M.faceNext d.val e.val ↔
      N.faceNext (rMinus_rightSideMarkedIso_dartMap phi d).val
        (rMinus_rightSideMarkedIso_dartMap phi e).val := by
  simpa [geometricSideRelation, rMinus_rightSideMarkedIso_dartMap_cell] using
    (phi.relation_iff .faceNext (.inr d) (.inr e))

/-- Helper toward Lemma 5.5. A marked isomorphism sends a marked root
vertex to the marked root vertex. -/
theorem rMinus_rightSideMarkedIso_root
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (v : M.vertices) (hv : v.val = M.root) :
    ∃ v' : N.vertices, phi.equiv (.inl v) = .inl v' ∧ v'.val = N.root := by
  obtain ⟨v', h⟩ := rMinus_rightSideMarkedIso_vertex phi v
  have hr := (phi.relation_iff .root (.inl v) (.inl v)).mp (by
    simp [geometricSideRelation, hv])
  refine ⟨v', h, ?_⟩
  simpa [geometricSideRelation, h] using hr

/-- Helper toward Lemma 5.5. The indexed boundary dart is preserved by the
marked isomorphism, including its endpoint bit. -/
theorem rMinus_rightSideMarkedIso_boundary_transport
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) (i : ℕ) :
    phi.equiv
        (Sum.inr ⟨(rMinusCoherentRightSide x q).boundary i,
          rMinus_hatted_boundary_mem x q i⟩) =
      Sum.inr ⟨(rMinusCoherentRightSide x q').boundary i,
        rMinus_hatted_boundary_mem x q' i⟩ :=
  rMinus_rightSideMarkedIso_boundary x q q' phi i

/-- Helper toward Lemma 5.5. The indexed seam dart is preserved by the
marked isomorphism, including its endpoint bit. -/
theorem rMinus_rightSideMarkedIso_seam_transport
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) (i : ℕ) :
    phi.equiv
        (Sum.inr ⟨(rMinusCoherentRightSide x q).seam i,
          by
            change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
              renewalTime_positiveSuccessTime .right q j
            rw [iUnion_geometricAncestorEdges]
            exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩) =
      Sum.inr ⟨(rMinusCoherentRightSide x q').seam i,
        by
          change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
            renewalTime_positiveSuccessTime .right q' j
          rw [iUnion_geometricAncestorEdges]
          exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩ :=
  rMinus_rightSideMarkedIso_seam x q q' phi i


























end DirectedDistances.PaperProofs.Section5
