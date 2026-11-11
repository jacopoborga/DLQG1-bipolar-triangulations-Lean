/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable3

/-! # Boundary and seam transport for the nonpositive right-side code

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The coherent hatted right-side submap used by
the code-level boundary and seam transport lemmas. -/
noncomputable abbrev rMinusCoherentRightSide (x : XDP) (q : Coherent x) :=
  geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime ThinMapSide.right q

/-- Helper toward Lemma 5.5. A marked isomorphism between coherent hatted
right sides sends every indexed boundary dart to the dart with the same
boundary index, including its endpoint bit. -/
theorem rMinus_rightSideMarkedIso_boundary
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) (i : ℕ) :
    phi.equiv
        (Sum.inr ⟨(rMinusCoherentRightSide x q).boundary i,
          rMinus_hatted_boundary_mem x q i⟩) =
      Sum.inr ⟨(rMinusCoherentRightSide x q').boundary i,
        rMinus_hatted_boundary_mem x q' i⟩ := by
  let z : GeometricSideCell (rMinusCoherentRightSide x q) :=
    Sum.inr ⟨(rMinusCoherentRightSide x q).boundary i,
      rMinus_hatted_boundary_mem x q i⟩
  have hz : geometricSideRelation (rMinusCoherentRightSide x q) (.boundary i) z z := by
    simp [z, geometricSideRelation]
  have h := (phi.relation_iff (.boundary i) z z).mp hz
  cases hz' : phi.equiv z with
  | inl v => simp [geometricSideRelation, hz'] at h
  | inr d =>
      have hval : (rMinusCoherentRightSide x q').boundary i = d.val := by
        simpa [geometricSideRelation, hz'] using h
      change Sum.inr d =
        Sum.inr ⟨(rMinusCoherentRightSide x q').boundary i,
          rMinus_hatted_boundary_mem x q' i⟩
      congr 1
      exact Subtype.ext hval.symm

/-- Helper toward Lemma 5.5. A marked isomorphism between coherent hatted
right sides sends every indexed seam dart to the dart with the same seam
index, including its endpoint bit. -/
theorem rMinus_rightSideMarkedIso_seam
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
          exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩ := by
  let hq : ((rMinusCoherentRightSide x q).seam i).1 ∈
      (rMinusCoherentRightSide x q).edges := by
    change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
      renewalTime_positiveSuccessTime .right q j
    rw [iUnion_geometricAncestorEdges]
    exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i
  have hq' : ((rMinusCoherentRightSide x q').seam i).1 ∈
      (rMinusCoherentRightSide x q').edges := by
    change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
      renewalTime_positiveSuccessTime ThinMapSide.right q' j
    rw [iUnion_geometricAncestorEdges]
    exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i
  let z : GeometricSideCell (rMinusCoherentRightSide x q) :=
    Sum.inr ⟨(rMinusCoherentRightSide x q).seam i, hq⟩
  have hz : geometricSideRelation (rMinusCoherentRightSide x q) (.seam i) z z := by
    simp [z, geometricSideRelation]
  have h := (phi.relation_iff (.seam i) z z).mp hz
  cases hz' : phi.equiv z with
  | inl v => simp [geometricSideRelation, hz'] at h
  | inr d =>
      have hval : (rMinusCoherentRightSide x q').seam i = d.val := by
        simpa [geometricSideRelation, hz'] using h
      change Sum.inr d = Sum.inr ⟨(rMinusCoherentRightSide x q').seam i, hq'⟩
      congr 1
      exact Subtype.ext hval.symm






























end DirectedDistances.PaperProofs.Section5
