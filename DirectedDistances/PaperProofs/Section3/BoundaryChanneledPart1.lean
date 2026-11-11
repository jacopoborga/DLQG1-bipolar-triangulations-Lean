/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry22
public import DirectedDistances.PlanarMap.D39BallOrbitComponents3

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the geometric frontier condition for a
quotient edge is exactly bordering the marked outer face in either direction. -/
theorem boundaryChanneled_externalFrontier_iff_border_part1
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (d : Fin R.dartCount) :
    ExternalFrontierEdge (boundaryChanneledPlaneMap R G) (Quotient.mk G.edgeSetoid d) ↔
      G.dartBorders d (boundaryChanneledMarkedOuterFace R G) ∨
        G.dartBorders (R.B.map.toCombinatorialMap.edgeInv d)
          (boundaryChanneledMarkedOuterFace R G) := by
  let U := boundaryChanneledMarkedOuterFace R G
  have hvert := boundaryChanneled_dartTailVertex_surjective R
  rw [externalFrontierEdge_iff]
  constructor
  · rintro ⟨F, hF, hfront⟩
    let F' := G.toPlaneGraphDrawingFaceEquiv F
    have hFU : F' = U := boundaryChanneled_unboundedFace_eq_markedOuterFace
      R G hOuterUnbounded F' ((G.toPlaneGraphDrawing_isExternal_iff F).mp hF)
    have hval : F.val = U.val := congrArg Subtype.val hFU
    have hi : 0 + 1 < (G.arc d).points.length := by
      have hlen := G.arc_length d
      omega
    let q := AffineMap.lineMap ((G.arc d).point 0) ((G.arc d).point 1) (1 / 2 : ℝ)
    have hq : q ∈ openSegment ℝ ((G.arc d).point 0) ((G.arc d).point 1) :=
      lineMap_mem_openSegment ℝ _ _ (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    have hqimage : q ∈ (G.arc d).image :=
      (G.arc d).segmentAt_subset_image hi (openSegment_subset_segment ℝ _ _ hq)
    have hqfront : q ∈ frontier U.val := by
      rw [← hval]
      apply hfront
      change q ∈ Set.range (G.toPlaneGraphDrawing.arc (Quotient.mk G.edgeSetoid d))
      rw [G.toPlaneGraphDrawing_arc_range]
      exact hqimage
    exact (G.mem_closure_face_openSegment_iff_dartBorders hvert d U hi hq).mp
      (frontier_subset_closure hqfront)
  · intro hborder
    refine ⟨G.toPlaneGraphDrawingFaceEquiv.symm U, ?_, ?_⟩
    · exact (G.toPlaneGraphDrawing_isExternal_iff _).mpr hOuterUnbounded
    · change Set.range (G.toPlaneGraphDrawing.arc (Quotient.mk G.edgeSetoid d)) ⊆
        frontier U.val
      rw [G.toPlaneGraphDrawing_arc_range]
      rcases hborder with hd | hd
      · exact G.dartBorders_arc_subset_frontier hvert d U hd
      · simpa only [G.arc_image_flip] using
          G.dartBorders_arc_subset_frontier hvert _ U hd

/-- Helper toward Definition 3.2: the listed geometric edges are exactly the
external frontier edges, retaining both dart occurrences of a bridge. -/
theorem boundaryChanneledPresentation_edgeCoverage_part1
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∀ e, (∃ i : InfiniteBoundaryDartIndex
        (boundaryChanneledPresentationWithJunctions R G).presentation,
      (InfiniteBoundaryDartIndex.dart
        (boundaryChanneledPresentationWithJunctions R G).presentation i).1 = e) ↔
      ExternalFrontierEdge (boundaryChanneledPlaneMap R G) e := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let E := boundaryChanneledDartPairEquiv19 G
  have hborder (d : Fin R.dartCount) :
      G.dartBorders d (boundaryChanneledMarkedOuterFace R G) ↔
        ∃ i : InfiniteBoundaryDartIndex P, InfiniteBoundaryDartIndex.dart P i = E d := by
    simpa only [E, Equiv.symm_apply_apply] using
      (boundaryChanneled_markedOuterFace_borders_iff_indexed20 R G (E d)).trans
        (boundaryChanneledPresentation_indexRange_iff_leftRight16 R G (E d)).symm
  intro q
  constructor
  · rintro ⟨i, hi⟩
    let d := E.symm (InfiniteBoundaryDartIndex.dart P i)
    have hd : G.dartBorders d (boundaryChanneledMarkedOuterFace R G) :=
      (hborder d).mpr ⟨i, (E.apply_symm_apply _).symm⟩
    have hq : Quotient.mk G.edgeSetoid d = q := by
      change (E d).1 = q
      rw [E.apply_symm_apply]
      exact hi
    rw [← hq]
    exact (boundaryChanneled_externalFrontier_iff_border_part1 R G hOuterUnbounded d).mpr
      (Or.inl hd)
  · intro hq
    have hq' : ExternalFrontierEdge (boundaryChanneledPlaneMap R G)
        (Quotient.mk G.edgeSetoid q.out) := by
      simpa only [Quotient.out_eq] using hq
    rcases (boundaryChanneled_externalFrontier_iff_border_part1 R G hOuterUnbounded q.out).mp
        hq' with hd | hd
    · obtain ⟨i, hi⟩ := (hborder q.out).mp hd
      exact ⟨i, (congrArg Prod.fst hi).trans (Quotient.out_eq q)⟩
    · obtain ⟨i, hi⟩ := (hborder _).mp hd
      refine ⟨i, (congrArg Prod.fst hi).trans ?_⟩
      change Quotient.mk G.edgeSetoid (R.B.map.toCombinatorialMap.edgeInv q.out) = q
      rw [G.geometricEdge_flip, Quotient.out_eq]

/-- Helper toward Definition 3.2: each map vertex is the initial vertex of
one of the encoded darts. -/
theorem boundaryChanneled_boundaryDartInitial_surjective_part1
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R) :
    Function.Surjective (boundaryDartInitial (boundaryChanneledPlaneMap R G)) := by
  intro v
  obtain ⟨d, hd⟩ := boundaryChanneled_dartTailVertex_surjective R v
  exact ⟨boundaryChanneledDartPairEquiv19 G d,
    (boundaryChanneledDartPairEquiv19_initial R G d).trans hd⟩

/-- Helper toward Definition 3.2: every compatible finite dart drawing
preserves the unbounded face under its geometric face successor. -/
theorem boundaryChanneled_geometricSuccessor_part1
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (U : H.Face) (hU : H.IsUnbounded U) :
    IsGeometricExternalFaceSucc H U (fun d => rot.symm (d.1, !d.2)) := by
  classical
  have boundaryChanneledPart1FiniteDarts : Finite (G.GeometricEdge × Bool) :=
    Finite.of_equiv (Fin R.dartCount) (boundaryChanneledDartPairEquiv19 G)
  have hvert := boundaryChanneled_boundaryDartInitial_surjective_part1 R G
  refine ⟨hU, ?_⟩
  intro d hd
  refine ⟨rfl, ?_⟩
  let s := rot.symm (d.1, !d.2)
  obtain ⟨F, hF⟩ := H.dartBorders_exists_of_wedge_compl s
    (H.wedgeIn_compl_image hvert (H.arc s).start
      (H.arc s).initialDirection (H.initial_nonzero s))
  have hstep := H.dartBorders_flip_rot hvert s F hF
  have heq : ((rot s).1, !(rot s).2) = d := by
    simp only [s, Equiv.apply_symm_apply, Bool.not_not]
  rw [heq] at hstep
  have hFU := H.dartBorders_face_unique d F U hstep hd
  exact hFU ▸ hF

/-- Helper toward Definition 3.2: the presentation satisfies exact frontier
coverage and the permitted multiplicity and two-sided bridge conditions. -/
theorem boundaryChanneledPresentation_boundaryOrder_part1
    {l r n : Nat} (R : KMSWMapRep l r n) (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    IsBoundaryOrderOfInf (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation := by
  let M := boundaryChanneledPlaneMap R G
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let D := InfiniteBoundaryDartIndex.dart P
  have hinj := boundaryChanneledPresentation_dart_injective R G
  have heq {i j : InfiniteBoundaryDartIndex P}
      (hfirst : (D i).1 = (D j).1) (hsecond : (D i).2 = (D j).2) : i = j :=
    hinj (Prod.ext hfirst hsecond)
  have hul := (ULOkInf_iff P).mp
    (boundaryChanneledPresentation_ULOkInf22 R G hOuterUnbounded)
  have hlr := (LROkInf_iff P).mp
    (boundaryChanneledPresentation_LROkInf22 R G hOuterUnbounded)
  apply (IsBoundaryOrderOfInf_iff P).mpr
  refine ⟨boundaryChanneledPresentation_edgeCoverage_part1 R G hOuterUnbounded, ?_, ?_⟩
  · intro e i j k hi hj hk
    by_cases hij : (D i).2 = (D j).2
    · exact Or.inl (heq (hi.trans hj.symm) hij)
    by_cases hik : (D i).2 = (D k).2
    · exact Or.inr (Or.inl (heq (hi.trans hk.symm) hik))
    have hjk : (D j).2 = (D k).2 := by
      cases hbi : (D i).2 <;> cases hbj : (D j).2 <;> cases hbk : (D k).2 <;>
        simp_all
    exact Or.inr (Or.inr (heq (hj.trans hk.symm) hjk))
  · intro e i j hne hi hj
    cases i <;> cases j <;> rename_i a b
    all_goals try { first
      | (change Empty at a; cases a)
      | (change Empty at b; cases b) }
    all_goals simp only [InfiniteBoundaryDartIndex.dart_eq] at hi hj
    case upperLeft.upperLeft =>
      obtain ⟨hpa, hfa, _⟩ := hul.1 a
      obtain ⟨hpb, hfb, _⟩ := hul.1 b
      apply False.elim
      apply hne
      apply heq (by simpa only [D, InfiniteBoundaryDartIndex.dart_eq] using hi.trans hj.symm)
      simp only [D, InfiniteBoundaryDartIndex.dart_eq]
      rw [hfa, hfb]
      apply congrArg M.forward
      exact Subtype.ext (hi.trans hj.symm)
    case lowerRight.lowerRight =>
      obtain ⟨hpa, hfa, _⟩ := hlr.1 a
      obtain ⟨hpb, hfb, _⟩ := hlr.1 b
      apply False.elim
      apply hne
      apply heq (by simpa only [D, InfiniteBoundaryDartIndex.dart_eq] using hi.trans hj.symm)
      simp only [D, InfiniteBoundaryDartIndex.dart_eq]
      rw [hfa, hfb]
      congr 1
      apply congrArg M.forward
      exact Subtype.ext (hi.trans hj.symm)
    case upperLeft.lowerRight =>
      obtain ⟨hpa, _, F, hF, hleft⟩ := hul.1 a
      obtain ⟨hpb, _, H, hH, hright⟩ := hlr.1 b
      refine ⟨boundaryChanneledPlaneMap_noMissing R G e, F, H, hF, hH, ?_, ?_⟩
      · simpa only [show (P.upperLeft.darts a).1 = e from hi] using hleft
      · simpa only [show (P.lowerRight.darts b).1 = e from hj] using hright
    case lowerRight.upperLeft =>
      obtain ⟨hpa, _, F, hF, hright⟩ := hlr.1 a
      obtain ⟨hpb, _, H, hH, hleft⟩ := hul.1 b
      refine ⟨boundaryChanneledPlaneMap_noMissing R G e, H, F, hH, hF, ?_, ?_⟩
      · simpa only [show (P.upperLeft.darts b).1 = e from hj] using hleft
      · simpa only [show (P.lowerRight.darts a).1 = e from hi] using hright

end DirectedDistances.PaperProofs.Section3

end
