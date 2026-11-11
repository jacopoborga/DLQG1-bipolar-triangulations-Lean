/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation14

/-! Transfer of the two present boundary sides to every realized stage map. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Definition 3.2: a realization preserves the complete
drawing image, including vertex positions and missing geometric edges. -/
theorem kmswStageFiniteBoundaryPresentation16_image_eq
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    (Drawing M).image = P.image := by
  change (Set.range M.toPlaneMapWithMissing.pos ∪
    ⋃ e, Set.range (M.toPlaneMapWithMissing.arc e)) =
    (Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image})
  apply congrArg₂ (fun A B : Set ℂ => A ∪ B) (congrArg Set.range hreal.1)
  ext z
  constructor
  · intro hz
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
    exact ⟨(e, false), by
      rw [← Polyline.range_toPath, ← hreal.2.2.1 (e, false)]
      exact he⟩
  · rintro ⟨d, hd⟩
    apply Set.mem_iUnion.mpr
    refine ⟨d.1, ?_⟩
    rw [hreal.2.2.1 d, Polyline.range_toPath]
    exact hd

/-- Helper toward Definition 3.2: distinct endpoints upgrade the carrier's
open-arc injectivity to injectivity on the whole parameter interval. -/
private theorem kmswStageFiniteBoundaryPresentation16_arc_injective
    {V E : Type*} (D : PlaneGraphDrawing V E) (e : E)
    (hne : D.src e ≠ D.tgt e) : Function.Injective (D.arc e) := by
  intro s t hst
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc s.property with hs | hs | hs
  · have hs0 : s = 0 := Subtype.ext hs
    subst s
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with ht | ht | ht
    · exact (Subtype.ext ht).symm
    · have ht1 : t = 1 := Subtype.ext ht
      subst t
      exact (hne (D.pos_injective ((D.arc e).source.symm.trans
        (hst.trans (D.arc e).target)))).elim
    · exact (D.openArc_avoids e (D.src e)
        ⟨t, ht, hst.symm.trans (D.arc e).source⟩).elim
  · have hs1 : s = 1 := Subtype.ext hs
    subst s
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with ht | ht | ht
    · have ht0 : t = 0 := Subtype.ext ht
      subst t
      exact (hne (D.pos_injective ((D.arc e).source.symm.trans
        (hst.symm.trans (D.arc e).target)))).elim
    · exact (Subtype.ext ht).symm
    · exact (D.openArc_avoids e (D.tgt e)
        ⟨t, ht, hst.symm.trans (D.arc e).target⟩).elim
  · exact ((D.arc_eq_at_interior_iff e s t hs).mp hst.symm).symm

/-- Helper toward Definition 3.2: endpoint equality casts preserve path functions. -/
private theorem kmswStageFiniteBoundaryPresentation16_path_coe_cast
    {a b a' b' : ℂ} (ha : a = a') (hb : b = b')
    (h : Path a b = Path a' b') (γ : Path a b) :
    ⇑(cast h γ : Path a' b') = γ := by
  subst a'
  subst b'
  cases h
  rfl

/-- Helper toward Definition 3.2: all-parameter winding tests transfer
from a stage's forward dart to the realized directed edge. -/
theorem kmswStageFiniteBoundaryPresentation16_orientedArc_sides
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (e : Fin (kmswStage w n).nextEdge)
    (hp : ¬ M.toPlaneMapWithMissing.missing e) (F : Set ℂ) :
    ((∀ s, LeftAtOn F (P.arc (e, false)).toPath s) ↔
      ∀ s, LeftAtOn F (orientedArc M ⟨e, hp⟩) s) ∧
    ((∀ s, RightAtOn F (P.arc (e, false)).toPath s) ↔
      ∀ s, RightAtOn F (orientedArc M ⟨e, hp⟩) s) := by
  have hf := hreal.2.2.2.2 e hp
  have htail : M.tail ⟨e, hp⟩ = stageVertex w n (e, false) := by
    simpa only [DirectedPlaneMapWithMissing.tail, hf, Bool.false_eq_true,
      ↓reduceIte, boundaryDartInitial_eq] using hreal.2.1 (e, false)
  have hhead : M.head ⟨e, hp⟩ = stageVertex w n (e, true) := by
    simpa only [DirectedPlaneMapWithMissing.head, hf, Bool.false_eq_true,
      ↓reduceIte, boundaryDartInitial_eq] using hreal.2.1 (e, true)
  have hs : M.toPlaneMapWithMissing.pos (M.tail ⟨e, hp⟩) =
      (P.arc (e, false)).start := by
    rw [hreal.1, htail]
    exact (P.arc_start _).symm
  have ht : M.toPlaneMapWithMissing.pos (M.head ⟨e, hp⟩) =
      (P.arc (e, false)).finish := by
    rw [hreal.1, hhead]
    exact (P.arc_finish (e, false)).symm
  let γ := (P.arc (e, false)).toPath.cast hs ht
  let δ := orientedArc M ⟨e, hp⟩
  have hδeq : ⇑δ = ⇑(M.toPlaneMapWithMissing.arc e).symm := by
    dsimp only [δ]
    simp only [orientedArc, hf, Bool.false_eq_true, ↓reduceDIte, eq_mpr_eq_cast]
    apply kmswStageFiniteBoundaryPresentation16_path_coe_cast
      (by simp only [DirectedPlaneMapWithMissing.tail, hf, Bool.false_eq_true, ↓reduceIte])
      (by simp only [DirectedPlaneMapWithMissing.head, hf, Bool.false_eq_true, ↓reduceIte])
  have hγ : Function.Injective γ :=
    (P.arc (e, false)).toPath_injective (P.arc_length _) (P.arc_simple _)
  have hends : M.tail ⟨e, hp⟩ ≠ M.head ⟨e, hp⟩ := by
    intro heq
    have hz : γ 0 = γ 1 := by
      rw [γ.source, γ.target, heq]
    exact zero_ne_one (hγ hz)
  have hne : (Drawing M).src e ≠ (Drawing M).tgt e := by
    intro heq
    apply hends
    simpa only [DirectedPlaneMapWithMissing.tail, DirectedPlaneMapWithMissing.head,
      hf, Bool.false_eq_true, ↓reduceIte] using heq.symm
  have hδ : Function.Injective δ := by
    have hi := kmswStageFiniteBoundaryPresentation16_arc_injective (Drawing M) e hne
    rw [hδeq]
    exact hi.comp unitInterval.symm_bijective.injective
  have hrange : Set.range δ = Set.range γ := by
    rw [hδeq, Path.symm_range]
    change Set.range (M.toPlaneMapWithMissing.arc e) = Set.range (P.arc (e, false)).toPath
    exact hreal.2.2.1 (e, false)
  have hl := forall_leftAtOn_iff_of_injective_range_eq F γ δ hγ hδ hrange
  have hr := forall_leftAtOn_iff_of_injective_range_eq F γ.symm δ.symm
    (hγ.comp unitInterval.symm_bijective.injective)
    (hδ.comp unitInterval.symm_bijective.injective)
    (by simpa only [Path.symm_range] using hrange)
  have hc : (∀ s, LeftAtOn F γ s) ↔
      ∀ s, LeftAtOn F (P.arc (e, false)).toPath s :=
    forall_congr' (fun s => leftAtOn_congr_fun F _ _ s (fun _ => rfl))
  have hc' : (∀ s, RightAtOn F γ s) ↔
      ∀ s, RightAtOn F (P.arc (e, false)).toPath s :=
    forall_congr' (fun s => rightAtOn_congr_fun F _ _ s (fun _ => rfl))
  exact ⟨(hl.trans hc).symm,
    ((forall_leftAtOn_symm_iff F δ).symm.trans
      (hr.trans (forall_leftAtOn_symm_iff F γ))).trans hc' |>.symm⟩

/-- Helper toward Definition 3.2: the stage's unbounded complementary
component is also an external face of every realized map. -/
theorem kmswStageFiniteBoundaryPresentation16_externalFace
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    ∃ F : (Drawing M).Face, F.val = U.val ∧ (Drawing M).IsExternal F := by
  let F : (Drawing M).Face := ⟨U.val, by
    simpa only [kmswStageFiniteBoundaryPresentation16_image_eq w n P M hreal]
      using U.property⟩
  refine ⟨F, rfl, ?_⟩
  have h := (P.toPlaneGraphDrawing_isExternal_iff
    (P.toPlaneGraphDrawingFaceEquiv.symm U)).mpr hU
  exact h

/-- Helper toward Definition 3.2: all allocated stage vertices are dart
initial vertices; no isolated-vertex assumption is added. -/
private theorem kmswStageFiniteBoundaryPresentation16_vertex_surjective
    (w : ℕ → Fin 3) (n : ℕ) : Function.Surjective (stageVertex w n) := by
  intro v
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v.val v.isLt
  exact ⟨d, Fin.ext (by simpa only [stageVertex] using hd)⟩

/-- Helper toward Definition 3.2: a combinatorial stage face successor
starts where the preceding dart ends. -/
private theorem kmswStageFiniteBoundaryPresentation16_successor_vertex
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageVertex w n ((kmswMap w n).faceSucc d) =
      stageVertex w n (edgeFlip _ d) := by
  have h := P.vert_rotation ((stageRot w n).symm (edgeFlip _ d))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Helper toward Definition 3.2: the realized upper-left run consists
of present forward edges with the external face on their left, and joins. -/
theorem kmswStageFiniteBoundaryPresentation16_upperLeft_ok
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    ULOkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  apply (ULOkInf_iff _).mpr
  constructor
  · intro i
    let d := (kmswStageULDartRun w n)[i.val]'i.isLt
    have hmem : d ∈ kmswStageULDartsFinset w n := by
      simpa only [kmswStageULDartsFinset, List.mem_toFinset] using List.getElem_mem i.isLt
    have hside := ((kmswStageULDartsFinset_mem w n d).mp hmem).1
    have hmap := (kmswStageULDartsFinset_map_mem w n d).mp hmem
    have hd : d = (d.1, false) := Prod.ext rfl hside
    have hp : ¬ M.toPlaneMapWithMissing.missing d.1 := by
      rw [hreal.2.2.2.1 d.1]
      change ¬ (kmswStage w n).present d.1.val = false
      exact hmap.1
    refine ⟨hp, ?_, ?_⟩
    · change d.2 = M.forward ⟨d.1, hp⟩
      exact hside.trans (hreal.2.2.2.2 _ hp).symm
    · obtain ⟨F, hF, hExt⟩ :=
        kmswStageFiniteBoundaryPresentation16_externalFace w n P U hU M hreal
      refine ⟨F, hExt, ?_⟩
      change ∀ s, LeftAtOn F.val (orientedArc M ⟨d.1, hp⟩) s
      apply (kmswStageFiniteBoundaryPresentation16_orientedArc_sides
        w n P M hreal d.1 hp F.val).1.mp
      intro s
      rw [hF, ← hd]
      exact P.dartBorders_toPath_leftAtOn
        (kmswStageFiniteBoundaryPresentation16_vertex_surjective w n) d U
        ((hborder d).mpr hmap.2.2) s
  · intro i j hij
    change kmswFiniteRunNext i = some j at hij
    unfold kmswFiniteRunNext at hij
    split at hij
    next hi =>
      injection hij with heq
      subst j
      change boundaryDartTerminal M ((kmswStageULDartRun w n)[i.val]) =
        boundaryDartInitial M ((kmswStageULDartRun w n)[i.val + 1])
      rw [kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal,
        kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal]
      rw [← kmswStageFiniteBoundaryPresentation4_upperLeft_faceSucc w n i hi]
      exact (kmswStageFiniteBoundaryPresentation16_successor_vertex w n P _).symm
    next => cases hij

/-- Helper toward Definition 3.2: the realized reversed lower-right run
consists of present reverse darts with the external face on the right, and joins. -/
theorem kmswStageFiniteBoundaryPresentation16_lowerRight_ok
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    LROkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  apply (LROkInf_iff _).mpr
  constructor
  · intro i
    let d := (kmswStageLRDartRun w n)[i.val]'i.isLt
    have hmem : d ∈ kmswStageLRDartsFinset w n := by
      simpa only [kmswStageLRDartsFinset, List.mem_toFinset] using List.getElem_mem i.isLt
    have hside := ((kmswStageLRDartsFinset_mem w n d).mp hmem).1
    have hmap := (kmswStageLRDartsFinset_map_mem w n d).mp hmem
    have hp : ¬ M.toPlaneMapWithMissing.missing d.1 := by
      rw [hreal.2.2.2.1 d.1]
      change ¬ (kmswStage w n).present d.1.val = false
      exact hmap.1
    refine ⟨hp, ?_, ?_⟩
    · change d.2 = !(M.forward ⟨d.1, hp⟩)
      rw [hreal.2.2.2.2 _ hp]
      exact hside
    · obtain ⟨F, hF, hExt⟩ :=
        kmswStageFiniteBoundaryPresentation16_externalFace w n P U hU M hreal
      refine ⟨F, hExt, ?_⟩
      change ∀ s, RightAtOn F.val (orientedArc M ⟨d.1, hp⟩) s
      apply (kmswStageFiniteBoundaryPresentation16_orientedArc_sides
        w n P M hreal d.1 hp F.val).2.mp
      intro s
      rw [hF]
      apply P.dartBorders_flip_toPath_rightAtOn
        (kmswStageFiniteBoundaryPresentation16_vertex_surjective w n) (d.1, false) U
      apply (hborder _).mpr
      have hd : edgeFlip (kmswStage w n).nextEdge (d.1, false) = d :=
        Prod.ext rfl hside.symm
      rw [hd]
      exact hmap.2.2
  · intro i j hij
    change kmswFiniteRunNext i = some j at hij
    unfold kmswFiniteRunNext at hij
    split at hij
    next hi =>
      injection hij with heq
      subst j
      change boundaryDartTerminal M ((kmswStageLRDartRun w n)[i.val]) =
        boundaryDartInitial M ((kmswStageLRDartRun w n)[i.val + 1])
      rw [kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal,
        kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal]
      rw [← kmswStageFiniteBoundaryPresentation4_lowerRight_faceSucc w n i hi]
      exact (kmswStageFiniteBoundaryPresentation16_successor_vertex w n P _).symm
    next => cases hij

/-- Helper toward Definition 3.2: the finite-stage package with both
present-side orientation premises discharged. The five other premises
retain their exact Presentation14 binders. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses16
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (_hU : P.IsUnbounded U)
      (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      UROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LLOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge)),
      ∀ (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      FiniteBoundaryPositionOrder4 (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
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
    exists_kmswStage_bound_edges32_of_open_clauses14 w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro hboundary hUR hLL hposition hjoin
  exact hpackage hboundary
    (kmswStageFiniteBoundaryPresentation16_upperLeft_ok w n P U hU hborder)
    hUR (kmswStageFiniteBoundaryPresentation16_lowerRight_ok w n P U hU hborder)
    hLL hposition hjoin

end DirectedDistances.PaperProofs.Section3
