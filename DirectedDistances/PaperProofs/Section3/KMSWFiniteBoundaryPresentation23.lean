/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation20
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation21
import DirectedDistances.PlanarMap.D39BallOrbitComponents3
import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation15

/-! integration belong to the sole coordinator. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open unitInterval Set
open scoped Topology

private theorem stageVertex23_surjective (w : ℕ → Fin 3) (n : ℕ) :
    Function.Surjective (stageVertex w n) := by
  intro v
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
  exact ⟨d, Fin.ext (by simpa only [stageVertex] using hd)⟩

private theorem realization23_external_face_eq
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (F : (Drawing M).Face) (hF : (Drawing M).IsExternal F) : F.val = U.val := by
  let F' : P.Face := ⟨F.val, by
    simpa only [kmswStageFiniteBoundaryPresentation16_image_eq w n P M hreal]
      using F.property⟩
  have hF' : P.IsUnbounded F' := by
    intro R
    by_contra h
    push Not at h
    exact hF (isBounded_iff_forall_norm_le.mpr ⟨R, h⟩)
  obtain ⟨G, _, huniq⟩ := P.existsUnique_unbounded_face
  exact congrArg Subtype.val ((huniq F' hF').trans (huniq U hU).symm)

/-- Helper toward Definition 3.2: the whole realized arc is on the external
frontier exactly when one of its two stage darts borders the unbounded face.
This statement retains both orientations. -/
theorem kmswStageFiniteBoundaryPresentation23_frontier_iff
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (e : Fin (kmswStage w n).nextEdge) :
    ExternalFrontierEdge M e ↔
      P.dartBorders (e, false) U ∨ P.dartBorders (e, true) U := by
  have hvert := stageVertex23_surjective w n
  rw [externalFrontierEdge_iff]
  constructor
  · rintro ⟨F, hF, harc⟩
    have hFU := realization23_external_face_eq w n P U hU M hreal F hF
    let s : I := ⟨1 / 4, by norm_num⟩
    have hi : 0 + 1 < (P.arc (e, false)).points.length := by
      have := P.arc_length (e, false)
      omega
    have hq := Polyline.toPath_mem_openSegment_of_parameter
      (P.arc (e, false)) hi s (by norm_num [s, Polyline.segmentParameterStart_zero])
      (by dsimp [s, Polyline.segmentParameterEnd]; split_ifs <;> norm_num)
    apply (P.mem_closure_face_openSegment_iff_dartBorders hvert (e, false) U hi hq).mp
    apply frontier_subset_closure
    rw [← hFU]
    apply harc
    rw [hreal.2.2.1 (e, false)]
    exact Set.mem_range_self s
  · intro hb
    obtain ⟨F, hFU, hF⟩ :=
      kmswStageFiniteBoundaryPresentation16_externalFace w n P U hU M hreal
    refine ⟨F, hF, ?_⟩
    rw [hFU, hreal.2.2.1 (e, false), Polyline.range_toPath]
    rcases hb with hb | hb
    · exact P.dartBorders_arc_subset_frontier hvert (e, false) U hb
    · have h := P.dartBorders_arc_subset_frontier hvert (e, true) U hb
      have heq : (P.arc (e, true)).image = (P.arc (e, false)).image :=
        P.arc_image_flip (e, false)
      rwa [heq] at h

/-- Helper toward Definition 3.2: the listed-edge clause of finite boundary
order follows from unsigned frontier incidence; no winding converse is assumed. -/
theorem kmswStageFiniteBoundaryPresentation23_listed_iff_frontier
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (e : Fin (kmswStage w n).nextEdge) :
    (∃ i : InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J),
      (InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i).1 = e) ↔
      ExternalFrontierEdge M e := by
  obtain ⟨G, _, huniq⟩ := P.existsUnique_unbounded_face
  have hcoverage := kmswStageFiniteBoundaryPresentation12_dart_coverage
    w n P U (fun F hF => (huniq F hF).trans (huniq U hU).symm)
    hborder M J U hU
  rw [kmswStageFiniteBoundaryPresentation23_frontier_iff w n P U hU M hreal e]
  constructor
  · rintro ⟨i, hi⟩
    have hb := (hcoverage _).mpr ⟨i, rfl⟩
    generalize hd : InfiniteBoundaryDartIndex.dart
      (kmswStageFiniteBoundaryPresentation w n M J) i = d at hi hb
    rcases d with ⟨f, b⟩
    dsimp only at hi
    subst f
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (hb | hb)
    · obtain ⟨i, hi⟩ := (hcoverage (e, false)).mp hb
      exact ⟨i, congrArg Prod.fst hi⟩
    · obtain ⟨i, hi⟩ := (hcoverage (e, true)).mp hb
      exact ⟨i, congrArg Prod.fst hi⟩

/-- Helper toward Definition 3.2: an external winding-side witness detects
one of the two stage borders. The orientation is deliberately retained as a
disjunction, since closure incidence alone does not select the signed side. -/
theorem kmswStageFiniteBoundaryPresentation23_border_or_flip_of_external_side
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (e : Fin (kmswStage w n).nextEdge)
    (hp : ¬ M.toPlaneMapWithMissing.missing e)
    (F : (Drawing M).Face) (hF : (Drawing M).IsExternal F)
    (hside : LeftOf M F ⟨e, hp⟩ ∨ RightOf M F ⟨e, hp⟩) :
    P.dartBorders (e, false) U ∨ P.dartBorders (e, true) U := by
  have hFU := realization23_external_face_eq w n P U hU M hreal F hF
  have htransfer := kmswStageFiniteBoundaryPresentation16_orientedArc_sides
    w n P M hreal e hp F.val
  let s : {t : I // t ∈ openParams} := ⟨⟨1 / 4, by norm_num⟩, by
    change 0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1
    norm_num⟩
  have hi : 0 + 1 < (P.arc (e, false)).points.length := by
    have := P.arc_length (e, false)
    omega
  have hq := Polyline.toPath_mem_openSegment_of_parameter
    (P.arc (e, false)) hi s.val
    (by norm_num [s, Polyline.segmentParameterStart_zero])
    (by dsimp [s, Polyline.segmentParameterEnd]; split_ifs <;> norm_num)
  apply (P.mem_closure_face_openSegment_iff_dartBorders
    (stageVertex23_surjective w n) (e, false) U hi hq).mp
  rw [← hFU]
  rcases hside with hleft | hright
  · have h := htransfer.1.mpr hleft s
    obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩ := h
    apply closure_mono _ hcl
    intro z hz
    exact hz.1
  · have h := htransfer.2.mpr hright s
    obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩ := h
    apply closure_mono _ hcl
    intro z hz
    exact hz.1

/-- Helper toward Definition 3.2: either external winding-side witness
puts the entire present edge on the external frontier of the finite drawing. -/
theorem kmswStageFiniteBoundaryPresentation23_frontier_of_external_side
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (e : Fin (kmswStage w n).nextEdge)
    (hp : ¬ M.toPlaneMapWithMissing.missing e)
    (F : (Drawing M).Face) (hF : (Drawing M).IsExternal F)
    (hside : LeftOf M F ⟨e, hp⟩ ∨ RightOf M F ⟨e, hp⟩) :
    ExternalFrontierEdge M e :=
  (kmswStageFiniteBoundaryPresentation23_frontier_iff w n P U hU M hreal e).mpr
    (kmswStageFiniteBoundaryPresentation23_border_or_flip_of_external_side
      w n P U hU M hreal e hp F hF hside)

/-- Helper toward Definition 3.2: injective dart enumeration permits at most
two occurrences of any edge ID, since a dart has just two orientation bits. -/
theorem kmswStageFiniteBoundaryPresentation23_at_most_two
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (e : Fin (kmswStage w n).nextEdge)
    (i j k : InfiniteBoundaryDartIndex (kmswStageFiniteBoundaryPresentation w n M J))
    (hi : (InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i).1 = e)
    (hj : (InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) j).1 = e)
    (hk : (InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) k).1 = e) :
    i = j ∨ i = k ∨ j = k := by
  let d := InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J)
  have hinj := kmswStageFiniteBoundaryPresentation_dart_injective w n M J
  have heq {a b} (hab : (d a).1 = (d b).1) (hbit : (d a).2 = (d b).2) : a = b :=
    hinj (Prod.ext hab hbit)
  have hbits : (d i).2 = (d j).2 ∨ (d i).2 = (d k).2 ∨ (d j).2 = (d k).2 := by
    cases (d i).2 <;> cases (d j).2 <;> cases (d k).2 <;> decide
  exact hbits.imp (heq (hi.trans hj.symm))
    (Or.imp (heq (hi.trans hk.symm)) (heq (hj.trans hk.symm)))

private theorem stage23_both_outer_present
    (w : ℕ → Fin 3) (n : ℕ) (e : Fin (kmswStage w n).nextEdge)
    (hf : (kmswStageDirectedMap w n).IsOuter (e, false))
    (ht : (kmswStageDirectedMap w n).IsOuter (e, true)) :
    e.val ∈ (kmswStage w n).UL ∧ e.val ∈ (kmswStage w n).LR := by
  have ha : e.val ∈ (kmswStage w n).UL ∨ e.val ∈ (kmswStage w n).UR := by
    simpa using
      (stageOuterWord_mem_iff w n (e, false)).mp ((kmsw_stage_outer_face_exact w n _).mp hf)
  have hb : e.val ∈ (kmswStage w n).LR ∨ e.val ∈ (kmswStage w n).LL := by
    simpa using
      (stageOuterWord_mem_iff w n (e, true)).mp ((kmsw_stage_outer_face_exact w n _).mp ht)
  have hs := kmswStage_status w n
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ⟨ha, hb⟩
  · have hp := hs.2.1 _ ha
    have hm := (hs.1 _ e.isLt).mpr (Or.inr hb)
    rw [hp] at hm
    cases hm
  · have hp := hs.2.2.1 _ hb
    have hm := (hs.1 _ e.isLt).mpr (Or.inl ha)
    rw [hp] at hm
    cases hm
  · exact (hs.2.2.2.2.2 _ ha hb).elim

/-- Helper toward Definition 3.2: if both dart orientations are outer, the
edge is present and has external faces on both directed sides. -/
theorem kmswStageFiniteBoundaryPresentation23_both_outer_sides
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (e : Fin (kmswStage w n).nextEdge)
    (hf : (kmswStageDirectedMap w n).IsOuter (e, false))
    (ht : (kmswStageDirectedMap w n).IsOuter (e, true)) :
    ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      ∃ F G : (Drawing M).Face,
        (Drawing M).IsExternal F ∧ (Drawing M).IsExternal G ∧
          LeftOf M F ⟨e, hp⟩ ∧ RightOf M G ⟨e, hp⟩ := by
  obtain ⟨ha, hb⟩ := stage23_both_outer_present w n e hf ht
  have hma : (e, false) ∈ kmswStageULDartRun w n := by
    have h := (kmswStageULDartsFinset_mem w n (e, false)).mpr ⟨rfl, ha⟩
    simpa only [kmswStageULDartsFinset, List.mem_toFinset] using h
  have hmb : (e, true) ∈ kmswStageLRDartRun w n := by
    have h := (kmswStageLRDartsFinset_mem w n (e, true)).mpr ⟨rfl, hb⟩
    simpa only [kmswStageLRDartsFinset, List.mem_toFinset] using h
  obtain ⟨a, hia, hgetA⟩ := List.getElem_of_mem hma
  obtain ⟨b, hib, hgetB⟩ := List.getElem_of_mem hmb
  have hs := kmswStageFiniteBoundaryPresentation20_present_run_side_witnesses
    w n P U hU hborder M J hreal
  have hA := hs.1 ⟨a, hia⟩
  have hB := hs.2 ⟨b, hib⟩
  have hdA : (kmswStageFiniteBoundaryPresentation w n M J).upperLeft.darts ⟨a, hia⟩ =
      (e, false) := hgetA
  have hdB : (kmswStageFiniteBoundaryPresentation w n M J).lowerRight.darts ⟨b, hib⟩ =
      (e, true) := hgetB
  rw [hdA] at hA
  rw [hdB] at hB
  obtain ⟨hp, _, F, hF, hleft⟩ := hA
  obtain ⟨_, _, G, hG, hright⟩ := hB
  exact ⟨hp, F, G, hF, hG, hleft, hright⟩

/-- Helper toward Definition 3.2: the finite stage presentation satisfies
all boundary-order clauses, including the repeated-edge clause. -/
theorem kmswStageFiniteBoundaryPresentation17_boundary_order
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J) := by
  apply (IsBoundaryOrderOfInf_iff _).mpr
  refine ⟨kmswStageFiniteBoundaryPresentation23_listed_iff_frontier
    w n P U hU hborder M J hreal,
    kmswStageFiniteBoundaryPresentation23_at_most_two w n M J, ?_⟩
  intro e i j hne hi hj
  let d := InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J)
  have hbits : (d i).2 ≠ (d j).2 := by
    intro h
    exact hne (kmswStageFiniteBoundaryPresentation_dart_injective w n M J
      (Prod.ext (hi.trans hj.symm) h))
  have houter (a) : (kmswStageDirectedMap w n).IsOuter (d a) := by
    apply (kmsw_stage_outer_face_exact w n _).mpr
    dsimp only [d]
    rw [← kmswStageFiniteBoundaryPresentation21_get_position w n M J a]
    exact List.get_mem _ _
  have hi' : d i = (e, (d i).2) := Prod.ext hi rfl
  have hj' : d j = (e, (d j).2) := Prod.ext hj rfl
  have hoi := houter i
  have hoj := houter j
  rw [hi'] at hoi
  rw [hj'] at hoj
  have hboth : (kmswStageDirectedMap w n).IsOuter (e, false) ∧
      (kmswStageDirectedMap w n).IsOuter (e, true) := by
    cases hbi : (d i).2 <;> cases hbj : (d j).2
    · exact (hbits (hbi.trans hbj.symm)).elim
    · exact ⟨by simpa only [hbi] using hoi, by simpa only [hbj] using hoj⟩
    · exact ⟨by simpa only [hbj] using hoj, by simpa only [hbi] using hoi⟩
    · exact (hbits (hbi.trans hbj.symm)).elim
  exact kmswStageFiniteBoundaryPresentation23_both_outer_sides
    w n P U hU hborder M J hreal e hboth.1 hboth.2

/-- Helper toward Definition 3.2: the finite stage package needs only its
remaining join-label clause. Boundary order, all four side predicates, and
finite cyclic position order are discharged by checked helpers. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses23
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (_hU : P.IsUnbounded U)
      (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
      RequiredFiniteBoundaryJoinEndpointLabels7
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
      (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (Fin (kmswStage w n).nextEdge × Bool))
      (G : PLDrawing (Fin (kmswStage w n).nextEdge × Bool)
        (Fin (kmswStage w n).nextVertex) (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M)) (U : G.Face)
      (S : Fin (kmswStage w n).nextEdge × Bool → Fin (kmswStage w n).nextEdge × Bool),
      kmsw_stage_map_realization32 w n P M ∧
      B = kmswStageFiniteBoundaryPresentationWithJunctions w n M J ∧
      G.image = P.image ∧ IsBoundEdges32 M B G U S := by
  obtain ⟨P, U, hU, hborder, hpackage⟩ :=
    exists_kmswStage_bound_edges32_of_open_clauses21 w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro hjoin
  exact hpackage
    (kmswStageFiniteBoundaryPresentation17_boundary_order w n P U hU hborder)
    (kmswStageFiniteBoundaryPresentation16_upperLeft_ok w n P U hU hborder)
    (kmswStageFiniteBoundaryPresentation15_upperRight w n P U hU hborder)
    (kmswStageFiniteBoundaryPresentation16_lowerRight_ok w n P U hU hborder)
    (kmswStageFiniteBoundaryPresentation15_lowerLeft w n P U hU hborder)
    hjoin
























































































end DirectedDistances.PaperProofs.Section3

end
