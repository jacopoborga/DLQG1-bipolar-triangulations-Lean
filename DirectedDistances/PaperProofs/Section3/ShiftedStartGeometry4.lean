/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry3
public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation6
public import DirectedDistances.PlanarMap.PLDrawingBoundedFaces

/-! Helper toward Proposition 3.9: exhaustion of shifted bounded faces. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open Set Topology

private theorem locally_finite_vertex_segments
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert) (v : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball (P.pos v) r,
      (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0) := by
  classical
  let S (d : D) (i : Fin ((P.arc d).points.length - 1)) : Set ℂ :=
    if P.pos v ∈ (P.arc d).segmentAt i.val then ∅ else (P.arc d).segmentAt i.val
  let B (d : D) := ⋃ i, S d i
  have hsub (d : D) : B d ⊆ (P.arc d).image := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    dsimp only [S] at hi
    split_ifs at hi
    · exact hi.elim
    · exact (P.arc d).segmentAt_subset_image (by have := i.isLt; omega) hi
  have hlf : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (Metric.ball z 1) Metric.isBounded_ball
  have hclosed : IsClosed (⋃ d, B d) := (hlf.subset hsub).isClosed_iUnion (by
    intro d
    apply isClosed_iUnion_of_finite
    intro i
    dsimp only [S]
    split_ifs
    · exact isClosed_empty
    · change IsClosed (segment ℝ _ _)
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed)
  have hnot : P.pos v ∉ ⋃ d, B d := by
    intro hmem
    obtain ⟨d, hd⟩ := mem_iUnion.mp hmem
    obtain ⟨i, hi⟩ := mem_iUnion.mp hd
    dsimp only [S] at hi
    split_ifs at hi with h
    · exact hi
    · exact h hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  refine ⟨r, hr, ?_⟩
  intro y hyr
  constructor
  · intro hy
    have harc : ∃ d, y ∈ (P.arc d).image := by
      rcases hy with ⟨w, rfl⟩ | ⟨d, hd⟩
      · obtain ⟨d, rfl⟩ := hv w
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact ⟨d, hd⟩
    obtain ⟨d, hd⟩ := harc
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        y ∈ (P.arc d).segmentAt i := by
      rcases hd with hd | ⟨i, hi, hd⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [mem_singleton_iff] at hd
        rw [hd, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hd⟩
    obtain ⟨i, hi, hyi⟩ := hseg
    have hvi : P.pos v ∈ (P.arc d).segmentAt i := by
      by_contra hn
      apply hball hyr
      exact mem_iUnion.mpr ⟨d, mem_iUnion.mpr
        ⟨⟨i, by omega⟩, by simpa only [S, ite_eq_right hn] using hyi⟩⟩
    have him := (P.arc d).segmentAt_subset_image hi hvi
    have hend : P.pos v = (P.arc d).start ∨ P.pos v = (P.arc d).finish := by
      by_contra hn
      exact P.interior_avoids_vertices d v ⟨him, by
        simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    rcases hend with hs | ht
    · have hi0 := (P.arc d).segmentAt_index_eq_zero_of_start_mem
        (P.arc_simple d) (P.arc_length d) hi (hs ▸ hvi)
      exact ⟨d, P.pos_injective (hs.trans (P.arc_start d)).symm, hi0 ▸ hyi⟩
    · have hilast := (P.arc d).segmentAt_index_last_of_finish_mem
        (P.arc_simple d) (P.arc_length d) hi (ht ▸ hvi)
      refine ⟨flip d, P.pos_injective (ht.trans (P.arc_finish d)).symm, ?_⟩
      rw [P.arc_flip, Polyline.segmentAt_reverse_transfer _ (by
        have := P.arc_length d; omega)]
      have hind : (P.arc d).points.length - 2 - 0 = i := by omega
      simpa only [hind] using hyi
  · rintro ⟨d, _, hd⟩
    exact Or.inr ⟨d, (P.arc d).segmentAt_subset_image (by
      have := P.arc_length d; omega) hd⟩

private theorem locally_finite_border_predecessor
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (d : D) (F : P.Face) (hd : P.dartBorders d F) :
    P.dartBorders (flip (rot d)) F := by
  obtain ⟨r, hr, hlocal⟩ := locally_finite_vertex_segments P hv (vert d)
  have hsafe : P.initialSector d r ⊆ P.imageᶜ := by
    intro z hz hzim
    obtain ⟨e, he, hze⟩ := (hlocal z (P.initialSector_subset_ball d r hz)).mp hzim
    exact Set.disjoint_left.mp (P.initialSector_disjoint_initial_segment d e r he) hz hze
  have hc := P.isConnected_initialSector d hr
  obtain ⟨z, hz⟩ := hc.nonempty
  obtain ⟨K, hzK⟩ := (P.faces_cover_compl z).mpr (hsafe hz)
  have hsub : P.initialSector d r ⊆ K.val := by
    obtain ⟨w, _, hK⟩ := K.property
    rw [hK] at hzK ⊢
    rw [connectedComponentIn_eq hzK]
    exact hc.isPreconnected.subset_connectedComponentIn hz hsafe
  have hKF := P.dartBorders_face_unique d K F
    (P.dartBorders_of_initialSector_subset hv d hr K hsub) hd
  exact hKF ▸ P.dartBorders_flip_rot_of_initialSector_subset hv d hr K hsub

private theorem bounded_face_has_nondecreasing_dart
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (d₀ : D) (F : P.Face) (hF : Bornology.IsBounded F.val) (r : V → ℝ) :
    ∃ d, P.dartBorders d F ∧ r (vert d) ≤ r (vert (flip d)) := by
  classical
  obtain ⟨d, hd, hmin⟩ := Set.exists_min_image {d | P.dartBorders d F}
    (fun d => -r (vert d)) (P.finite_borderDarts_of_bounded F hF)
    (P.face_has_bordering_dart hv d₀ F)
  let e := flip (rot d)
  have he : P.dartBorders e F := locally_finite_border_predecessor P hv d F hd
  refine ⟨e, he, ?_⟩
  have hh := hmin e he
  have hve : vert (flip e) = vert d := by
    dsimp only [e]
    rw [P.flip_involutive, P.vert_rotation]
  rw [hve]
  linarith only [hh]

private theorem run_edge_rank_lt (u : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence u) (e : ℕ) :
    ((monotoneFamilyDrawing u hfin (monotone_family_all u)).pos (edgeWest u e)).re <
      ((monotoneFamilyDrawing u hfin (monotone_family_all u)).pos (edgeEast u e)).re := by
  have he := kmsw_edge_allocated_by_self u e
  have hv := kmswStage_endpoints_lt_nextVertex u e e he
  have hend := edge_endpoints_eq u he
  have hpos (v : ℕ) (hv : v < (kmswStage u e).nextVertex) :
      (monotoneFamilyDrawing u hfin (monotone_family_all u)).pos v = layoutPos u e v :=
    monotoneLimitDrawing_pos_layout u hfin _ e v hv
  rw [← hend.1, ← hend.2, hpos _ hv.1, hpos _ hv.2]
  change (kmswStageRank u e ((kmswStage u e).west e) : ℝ) <
    (kmswStageRank u e ((kmswStage u e).east e) : ℝ)
  exact_mod_cast kmswStageRank_strict u e e he

private theorem forward_dart_creation (u : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence u) (h : BoundaryHitWitnesses u) (e : ℕ) :
    ∃ j : TriangleCreationTime u, (e, false) ∈ stageTriangleDartList u j := by
  have hL : ∀ a : ℤ, ∃ n, L u n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, R u n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    have hh := le_max_left (-a) 1
    exact ⟨n, by omega⟩
  rcases kmswRunInfDart_partition u hfin hL hR (e, false) with
    ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨j, hj, _⟩
  · exact (Bool.false_ne_true (congrArg Prod.snd he)).elim
  · exact (Bool.false_ne_true (congrArg Prod.snd he)).elim
  · exact ⟨j, hj⟩

/-- Helper toward Proposition 3.9: every bounded face of the inherited
shifted drawing has a forward bordering dart. The proof uses a strictly
increasing vertex rank and finite boundary incidence, not an ambient map. -/
theorem inherited_bounded_face_forward_dart (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let Q := inheritedDrawing W H G n univ
    ∀ F : Q.Face, ¬ Q.IsUnbounded F →
      ∃ (d : retainedDarts W n univ), Q.dartBorders d F ∧ d.val.2 = false := by
  intro Q F hF
  let u := shiftedStream (shiftWordInt W n) 0
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  obtain ⟨Φ, hv, _⟩ := exists_drawing_image_homeomorph W H G n J hfin
  let D (a : ℕ × Bool) : retainedDarts W n univ :=
    ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), by
      rw [retained_darts_eq_image W n J univ]
      exact ⟨a, mem_univ _, rfl⟩⟩
  have hsurj : Function.Surjective D := by
    intro d
    have hd := (Set.ext_iff.mp (retained_darts_eq_image W n J univ) d.val).mp d.property
    obtain ⟨a, _, ha⟩ := hd
    exact ⟨a, Subtype.ext ha⟩
  have hvert : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  let r (v : RestrictedVertex G (retainedDarts W n univ)) : ℝ :=
    (Φ.symm ⟨Q.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ).re
  have hr (a : ℕ × Bool) :
      r (restrictedVertex G (retainedDarts W n univ) (D a)) =
        (P.pos (kmswLimitDartVertex u a)).re := by
    have hh : Φ ⟨P.pos (kmswLimitDartVertex u a), Or.inl ⟨_, rfl⟩⟩ =
        ⟨Q.pos (restrictedVertex G (retainedDarts W n univ) (D a)),
          Or.inl ⟨_, rfl⟩⟩ := by
      apply Subtype.ext
      rw [hv]
      change G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0
        (kmswLimitDartVertex u a))) = G.pos
          (wholePlaneDartVertex W (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)))
      erw [start_iso_dart_vertex, wholePlaneDartVertex_ι]
    change (Φ.symm _ : ℂ).re = _
    rw [← hh, Φ.symm_apply_apply]
  have hflip (a : ℕ × Bool) :
      restrictedFlip G (retainedDarts W n univ) (fun _ => Iff.rfl) (D a) =
        D (a.1, !a.2) := by
    apply Subtype.ext
    change wholePlaneDartFlip W (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)) =
      J.dart (wholePlaneDartι (shiftWordInt W n) 0 (a.1, !a.2))
    erw [J.dart_apply, J.dart_apply]
    rfl
  have hbound : Bornology.IsBounded F.val := by
    by_contra hn
    exact hF ((Q.isUnbounded_iff_not_isBounded F).mpr hn)
  obtain ⟨d, hd, hrank⟩ := bounded_face_has_nondecreasing_dart Q hvert (D (0, false)) F hbound r
  obtain ⟨a, rfl⟩ := hsurj d
  rw [hflip, hr, hr] at hrank
  have ha : a.2 = false := by
    cases he : a.2
    · rfl
    · have hlt := run_edge_rank_lt u hfin a.1
      simp only [kmswLimitDartVertex, he, Bool.not_true, Bool.false_eq_true,
        ite_true, ite_false] at hrank
      exact (not_le_of_gt hlt hrank).elim
  refine ⟨D a, hd, ?_⟩
  change (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)).2 = false
  erw [J.dart_apply]
  exact ha

/-- Helper toward Proposition 3.9: every bounded inherited face is an
actual glued face of a shifted creation triangle, with its complete oriented
dart boundary. Thus no additional bounded target region is omitted. -/
theorem inherited_bounded_face_creation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∀ F : Q.Face, ¬ Q.IsUnbounded F →
      ∃ (j : TriangleCreationTime u) (B : G.Face),
        F.val = B.val ∧
        {d | G.dartBorders d B} =
          (fun a => J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)) ''
            {a | a ∈ stageTriangleDartList u j} ∧
        ∀ d : retainedDarts W n univ, Q.dartBorders d F ↔ G.dartBorders d.val B := by
  intro u G Q F hF
  obtain ⟨d, hd, hd0⟩ := inherited_bounded_face_forward_dart W H G n J hfin F hF
  have hret := (Set.ext_iff.mp (retained_darts_eq_image W n J univ) d.val).mp d.property
  obtain ⟨a, _, ha⟩ := hret
  have ha0 : a.2 = false := by
    have hh := congrArg Prod.snd ha
    change (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)).2 = d.val.2 at hh
    erw [J.dart_apply] at hh
    exact hh.trans hd0
  obtain ⟨j, hj⟩ := forward_dart_creation u hfin (start_boundary_hits W h n) a.1
  have hj' : a ∈ stageTriangleDartList u j := by
    have he : a = (a.1, false) := Prod.ext rfl ha0
    exact he.symm ▸ hj
  obtain ⟨F', B, hFB, hB, hinc⟩ := start_triangle_inherited_face W H h hpast n J j
  have hdB : G.dartBorders d.val B := by
    change d.val ∈ {d | G.dartBorders d B}
    rw [hB]
    exact ⟨a, hj', ha⟩
  have hFF : F = F' := Q.dartBorders_face_unique d F F' hd ((hinc d).mpr hdB)
  subst F'
  exact ⟨j, B, hFB, hB, hinc⟩

private theorem closure_homeomorph_bounded (S T : Set ℂ)
    (hS : Bornology.IsBounded S) (E : closure S ≃ₜ closure T) :
    Bornology.IsBounded T := by
  let shiftedStartGeometry4CompactClosure : CompactSpace (closure S) :=
    isCompact_iff_compactSpace.mp hS.isCompact_closure
  have hc := isCompact_range (continuous_subtype_val.comp E.continuous)
  have hr : Set.range (fun x : closure S => (E x : ℂ)) = closure T := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (E x).property
    · intro hy
      obtain ⟨x, hx⟩ := E.surjective ⟨y, hy⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  change IsCompact (Set.range (fun x : closure S => (E x : ℂ))) at hc
  rw [hr] at hc
  exact hc.isBounded.subset subset_closure

/-- Helper toward Proposition 3.9: the compatible closed-cell maps have
an exhaustive equivalence between all bounded source and target faces.
The same graph map, boundary incidences and cross-cell injectivity persist. -/
theorem exists_bounded_face_equiv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let B := {F : P.Face // ¬ P.IsUnbounded F}
    let C := {F : Q.Face // ¬ Q.IsUnbounded F}
    ∃ (Φ : P.image ≃ₜ Q.image) (τ : B ≃ C)
      (E : ∀ F : B, closure F.val.val ≃ₜ closure (τ F).val.val),
      (∀ v, (Φ ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (Φ ⟨(P.arc d).toPath t,
            Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      (∀ (F : B) (x : P.image) (hx : (x : ℂ) ∈ frontier F.val.val),
        (E F ⟨x, frontier_subset_closure hx⟩ : ℂ) = (Φ x : ℂ)) ∧
      (∀ (F : B) (x : closure F.val.val),
        (E F x : ℂ) ∈ frontier (τ F).val.val ↔ (x : ℂ) ∈ frontier F.val.val) ∧
      (∀ (F : B) (d : retainedDarts W n univ), Q.dartBorders d (τ F).val ↔
        ∃ a : ℕ × Bool, P.dartBorders a F.val ∧
          J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) ∧
      ∀ (F K : B) (x : closure F.val.val) (y : closure K.val.val),
        (E F x : ℂ) = (E K y : ℂ) ↔ (x : ℂ) = (y : ℂ) := by
  classical
  intro u P G Q B C
  obtain ⟨Φ, τ, E, hv, ha, he, hb, hd, hcollision⟩ :=
    exists_compatible_bounded_face_extensions W H h hpast n J hfin
  have hbounded (F : B) : ¬ Q.IsUnbounded (τ F) := by
    have hF : Bornology.IsBounded F.val.val := by
      by_contra hn
      exact F.property ((P.isUnbounded_iff_not_isBounded F.val).mpr hn)
    have hT := closure_homeomorph_bounded F.val.val (τ F).val hF (E F)
    exact fun hn => (Q.isUnbounded_iff_not_isBounded (τ F)).mp hn hT
  let f : B → C := fun F => ⟨τ F, hbounded F⟩
  have hfi : Function.Injective f := fun F K heq => τ.injective (congrArg Subtype.val heq)
  have hfs : Function.Surjective f := by
    intro F
    obtain ⟨j, K, hFK, hK, hinc⟩ :=
      inherited_bounded_face_creation W H h hpast n J hfin F.val F.property
    let A : B := ⟨capFace u hfin j, capFace_not_unbounded u hfin j⟩
    let a := (stageTriangleDartTriple u j).1
    have hja : a ∈ stageTriangleDartList u j := by simp [a, stageTriangleDartList]
    let d : retainedDarts W n univ :=
      ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), by
        rw [retained_darts_eq_image W n J univ]
        exact ⟨a, mem_univ _, rfl⟩⟩
    have hdA : Q.dartBorders d (τ A) := (hd A d).mpr
      ⟨a, (cap_border_iff u hfin j a).mpr hja, rfl⟩
    have hdF : Q.dartBorders d F.val := (hinc d).mpr (by
      change d.val ∈ {d | G.dartBorders d K}
      rw [hK]
      exact ⟨a, hja, rfl⟩)
    exact ⟨A, Subtype.ext (Q.dartBorders_face_unique d (τ A) F.val hdA hdF)⟩
  exact ⟨Φ, Equiv.ofBijective f ⟨hfi, hfs⟩, E, hv, ha, he, hb, hd, hcollision⟩

/-- Helper toward Proposition 3.9: every point of the run drawing,
including all missing geometric edges, lies on a bounded face frontier. -/
theorem drawing_image_covered_by_bounded_frontiers (u : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence u) (h : BoundaryHitWitnesses u) :
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    ∀ x ∈ P.image, ∃ F : P.Face, ¬ P.IsUnbounded F ∧ x ∈ frontier F.val := by
  intro P x hx
  have hv := kmswLimitDartVertex_surjective u hfin
  have harc : ∃ d, x ∈ (P.arc d).image := by
    rcases hx with ⟨v, rfl⟩ | ⟨d, hd⟩
    · obtain ⟨d, rfl⟩ := hv v
      exact ⟨d, Or.inl (P.arc_start d).symm⟩
    · exact ⟨d, hd⟩
  obtain ⟨⟨e, b⟩, hd⟩ := harc
  have he : x ∈ (P.arc (e, false)).image := by
    cases b
    · exact hd
    · have hflip := P.arc_image_flip (e, false)
      exact hflip ▸ hd
  obtain ⟨j, hj⟩ := forward_dart_creation u hfin h e
  exact ⟨capFace u hfin j, capFace_not_unbounded u hfin j,
    P.dartBorders_arc_subset_frontier hv (e, false) (capFace u hfin j)
      ((cap_border_iff u hfin j (e, false)).mpr hj) he⟩

private theorem paste_closed_region_cells {ι : Type*} (S T : ι → Set ℂ)
    (hS : LocallyFinite S) (hT : LocallyFinite T)
    (hclS : ∀ i, IsClosed (S i)) (hclT : ∀ i, IsClosed (T i))
    (E : ∀ i, S i ≃ₜ T i)
    (heq : ∀ i j (x : S i) (y : S j),
      (E i x : ℂ) = (E j y : ℂ) ↔ (x : ℂ) = (y : ℂ)) :
    ∃ g : (⋃ i, S i) ≃ₜ (⋃ i, T i),
      ∀ i (x : S i),
        (g ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) := by
  classical
  let A := ⋃ i, S i
  let B := ⋃ i, T i
  have hmem (x : A) : ∃ i, (x : ℂ) ∈ S i := mem_iUnion.mp x.property
  let idx (x : A) := (hmem x).choose
  have hx (x : A) : (x : ℂ) ∈ S (idx x) := (hmem x).choose_spec
  let f (x : A) : B :=
    ⟨E (idx x) ⟨x, hx x⟩, mem_iUnion.mpr ⟨idx x, (E (idx x) _).property⟩⟩
  have hf (i : ι) (x : S i) :
      (f ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) :=
    (heq _ _ _ _).mpr rfl
  have hfi : Function.Injective f := by
    intro x y h
    have hh : (E (idx x) ⟨x, hx x⟩ : ℂ) = (E (idx y) ⟨y, hx y⟩ : ℂ) :=
      congrArg Subtype.val h
    exact Subtype.ext ((heq _ _ _ _).mp hh)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp y.property
    refine ⟨⟨(E i).symm ⟨y, hi⟩, mem_iUnion.mpr
      ⟨i, ((E i).symm ⟨y, hi⟩).property⟩⟩, ?_⟩
    exact Subtype.ext ((hf i _).trans
      (congrArg Subtype.val ((E i).apply_symm_apply _)))
  let a : ι → Set A := fun i => Subtype.val ⁻¹' S i
  let b : ι → Set B := fun i => Subtype.val ⁻¹' T i
  have ha : LocallyFinite a := hS.preimage_continuous continuous_subtype_val
  have hb : LocallyFinite b := hT.preimage_continuous continuous_subtype_val
  have hac : ⋃ i, a i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hbc : ⋃ i, b i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hfc : Continuous f := ha.continuous hac
      (fun i => (hclS i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun x : a i => (f x.val : ℂ)) =
        fun x => (E i ⟨x.val.val, x.property⟩ : ℂ) :=
      funext fun x => hf i ⟨x.val.val, x.property⟩
    rw [he]
    exact continuous_subtype_val.comp ((E i).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  have hinv (i : ι) (y : T i) :
      (e.symm ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ : ℂ) =
        ((E i).symm y : ℂ) := by
    have hh : e ⟨(E i).symm y,
        mem_iUnion.mpr ⟨i, ((E i).symm y).property⟩⟩ =
        ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ :=
      Subtype.ext ((hf i _).trans (congrArg Subtype.val ((E i).apply_symm_apply y)))
    exact congrArg Subtype.val ((congrArg e.symm hh).symm.trans (e.symm_apply_apply _))
  have hic : Continuous e.symm := hb.continuous hbc
      (fun i => (hclT i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun y : b i => (e.symm y.val : ℂ)) =
        fun y => ((E i).symm ⟨y.val.val, y.property⟩ : ℂ) :=
      funext fun y => hinv i ⟨y.val.val, y.property⟩
    change Continuous (fun y : b i => (e.symm y.val : ℂ))
    erw [he]
    exact continuous_subtype_val.comp ((E i).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  exact ⟨{ toEquiv := e, continuous_toFun := hfc, continuous_invFun := hic }, hf⟩

private theorem closed_region_nearby_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d₀ : D) (F : P.Face) (z : ℂ) (hz : z ∈ F.val) :
    ∃ (d : D) (x : ℂ), x ∈ (P.arc d).image ∧ P.dartBorders d F ∧
      dist x z < dist z (P.pos (vert d₀)) + 1 := by
  obtain ⟨q, d, i, hi, hqi, hqfront, _, _, hmin⟩ :=
    P.face_nearest_segment_contact hvert d₀ F z hz
  have hdist := hmin (P.pos (vert d₀)) (Or.inl ⟨vert d₀, rfl⟩)
  by_cases hend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
  · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
      hvert F q d hi hend (frontier_subset_closure hqfront) zero_lt_one
    obtain ⟨e, hxe, he⟩ := P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
    refine ⟨e, x, hxe, he, ?_⟩
    have hnear : dist x q < 1 := Metric.mem_ball.mp hxball
    have htri := dist_triangle x q z
    rw [dist_comm q z] at htri
    linarith only [hnear, htri, hdist]
  · have hopen := mem_openSegment_of_ne_left_right
      (fun he => hend (Or.inl he.symm)) (fun he => hend (Or.inr he.symm)) hqi
    have hqnear : dist q z < dist z (P.pos (vert d₀)) + 1 := by
      rw [dist_comm]
      linarith only [hdist]
    rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hopen).mp
      (frontier_subset_closure hqfront) with hd | hd
    · exact ⟨d, q, (P.arc d).segmentAt_subset_image hi hqi, hd, hqnear⟩
    · refine ⟨flip d, q, ?_, hd, hqnear⟩
      rw [P.arc_image_flip]
      exact (P.arc d).segmentAt_subset_image hi hqi

private theorem closed_region_faces_locallyFinite
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert) (d₀ : D) :
    LocallyFinite (fun F : P.Face => closure F.val) := by
  classical
  have hu := P.dartBorders_existsUnique_of_locallyFiniteVertexImage32
    (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective P hv)
  let f := fun d => (hu d).choose
  have hf (d : D) (F : P.Face) (hd : P.dartBorders d F) : f d = F :=
    ((hu d).choose_spec.2 F hd).symm
  intro z
  let p₀ := P.pos (vert d₀)
  let R := dist z p₀ + 5
  have hdarts := P.locally_finite (Metric.ball z R) Metric.isBounded_ball
  have hfinite := hdarts.image f
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, hfinite.subset ?_⟩
  rintro F ⟨y, hyF, hyz⟩
  obtain ⟨w, hwF, hyw⟩ := Metric.mem_closure_iff.mp hyF 1 zero_lt_one
  have hwz : dist w z < 2 := by
    have ht := dist_triangle w y z
    rw [dist_comm w y] at ht
    have hyz' := Metric.mem_ball.mp hyz
    linarith only [ht, hyw, hyz']
  obtain ⟨d, x, hxd, hdF, hxw⟩ := closed_region_nearby_arc P hv d₀ F w hwF
  have hxz : x ∈ Metric.ball z R := by
    have ht := dist_triangle x w z
    have ht' := dist_triangle w z p₀
    change dist x w < dist w p₀ + 1 at hxw
    change dist x z < dist z p₀ + 5
    linarith only [ht, ht', hxw, hwz]
  exact ⟨d, ⟨x, hxz, hxd⟩, hf d F hdF⟩

/-- Helper toward Proposition 3.9: the entire run drawing and every
bounded closed face paste to the complete corresponding closed region of the
inherited drawing. Both maps are continuous; every bounded target face is hit,
including its interior, and the original vertex and edge formulas hold. -/
theorem exists_closed_region_homeomorph (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let B := {F : P.Face // ¬ P.IsUnbounded F}
    let C := {F : Q.Face // ¬ Q.IsUnbounded F}
    let X := ⋃ F : B, closure F.val.val
    let Y := ⋃ F : C, closure F.val.val
    ∃ (hP : P.image ⊆ X) (_hQ : Q.image ⊆ Y)
      (g : X ≃ₜ Y) (τ : B ≃ C),
      (∀ v, (g ⟨P.pos v, hP (Or.inl ⟨v, rfl⟩)⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (g ⟨(P.arc d).toPath t,
            hP (Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      (∀ F : B, g '' {x : X | (x : ℂ) ∈ closure F.val.val} =
        {y : Y | (y : ℂ) ∈ closure (τ F).val.val}) ∧
      (∀ F : B, g '' {x : X | (x : ℂ) ∈ F.val.val} =
        {y : Y | (y : ℂ) ∈ (τ F).val.val}) ∧
      (∀ x : X, (g x : ℂ) ∈ Q.image ↔ (x : ℂ) ∈ P.image) ∧
      IsClosed X ∧ IsClosed Y := by
  intro u P G Q B C X Y
  obtain ⟨Φ, τ, E, hv, ha, he, hb, _hd, hcollision⟩ :=
    exists_bounded_face_equiv W H h hpast n J hfin
  have hPv := kmswLimitDartVertex_surjective u hfin
  have hQv : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  let a := J.dart (wholePlaneDartι (shiftWordInt W n) 0 (0, false))
  have haret : a ∈ retainedDarts W n univ := by
    rw [retained_darts_eq_image W n J univ]
    exact ⟨(0, false), mem_univ _, rfl⟩
  have hs : LocallyFinite (fun F : B => closure F.val.val) :=
    (closed_region_faces_locallyFinite P hPv (0, false)).comp_injective Subtype.val_injective
  have ht : LocallyFinite (fun F : C => closure F.val.val) :=
    (closed_region_faces_locallyFinite Q hQv ⟨a, haret⟩).comp_injective Subtype.val_injective
  obtain ⟨g₀, hg₀⟩ := paste_closed_region_cells (fun F : B => closure F.val.val)
    (fun F : B => closure (τ F).val.val) hs (ht.comp_injective τ.injective)
    (fun _ => isClosed_closure) (fun _ => isClosed_closure) E hcollision
  have hY : (⋃ F : B, closure (τ F).val.val) = Y := by
    ext y
    constructor
    · intro hy
      obtain ⟨F, hF⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨τ F, hF⟩
    · intro hy
      obtain ⟨F, hF⟩ := mem_iUnion.mp hy
      refine mem_iUnion.mpr ⟨τ.symm F, ?_⟩
      rwa [τ.apply_symm_apply]
  let g : X ≃ₜ Y := g₀.trans (Homeomorph.setCongr hY)
  have hg (F : B) (x : closure F.val.val) :
      (g ⟨x, mem_iUnion.mpr ⟨F, x.property⟩⟩ : ℂ) = (E F x : ℂ) := hg₀ F x
  have hP : P.image ⊆ X := by
    intro x hx
    obtain ⟨F, hF, hxf⟩ := drawing_image_covered_by_bounded_frontiers u hfin
      (start_boundary_hits W h n) x hx
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, frontier_subset_closure hxf⟩
  have hgraph (x : P.image) : (g ⟨x, hP x.property⟩ : ℂ) = (Φ x : ℂ) := by
    obtain ⟨F, hF, hx⟩ := drawing_image_covered_by_bounded_frontiers u hfin
      (start_boundary_hits W h n) x x.property
    exact (hg ⟨F, hF⟩ ⟨x, frontier_subset_closure hx⟩).trans (he ⟨F, hF⟩ x hx)
  have hQ : Q.image ⊆ Y := by
    intro y hy
    obtain ⟨x, hx⟩ := Φ.surjective ⟨y, hy⟩
    have heq := (hgraph x).trans (congrArg Subtype.val hx)
    change (g ⟨x, hP x.property⟩ : ℂ) = y at heq
    exact heq ▸ (g ⟨x, hP x.property⟩).property
  have hcell (F : B) : g '' {x : X | (x : ℂ) ∈ closure F.val.val} =
      {y : Y | (y : ℂ) ∈ closure (τ F).val.val} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (g x : ℂ) ∈ closure (τ F).val.val
      rw [hg F ⟨x, hx⟩]
      exact (E F ⟨x, hx⟩).property
    · intro hy
      let x := (E F).symm ⟨y, hy⟩
      refine ⟨⟨x, mem_iUnion.mpr ⟨F, x.property⟩⟩, x.property, ?_⟩
      exact Subtype.ext ((hg F x).trans (congrArg Subtype.val ((E F).apply_symm_apply _)))
  have hinterior (F : B) (x : closure F.val.val) :
      (E F x : ℂ) ∈ (τ F).val.val ↔ (x : ℂ) ∈ F.val.val := by
    have hpopen := (P.face_open_frontier_subset_image hPv F.val).1
    have hqopen := (Q.face_open_frontier_subset_image hQv (τ F).val).1
    have hh := hb F x
    rw [frontier, frontier, hpopen.interior_eq, hqopen.interior_eq] at hh
    have hx := x.property
    have hy := (E F x).property
    change ((E F x : ℂ) ∈ closure (τ F).val.val ∧
        (E F x : ℂ) ∉ (τ F).val.val) ↔
      ((x : ℂ) ∈ closure F.val.val ∧ (x : ℂ) ∉ F.val.val) at hh
    tauto
  refine ⟨hP, hQ, g, τ, ?_, ?_, hcell, ?_, ?_,
    hs.isClosed_iUnion (fun _ => isClosed_closure),
    ht.isClosed_iUnion (fun _ => isClosed_closure)⟩
  · intro v
    exact (hgraph ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩).trans (hv v)
  · intro d
    obtain ⟨φ, hm, hφ⟩ := ha d
    exact ⟨φ, hm, fun t => (hgraph ⟨(P.arc d).toPath t,
      Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩).trans (hφ t)⟩
  · intro F
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (g x : ℂ) ∈ (τ F).val.val
      rw [hg F ⟨x, subset_closure hx⟩]
      exact (hinterior F _).mpr hx
    · intro hy
      let x := (E F).symm ⟨y, subset_closure hy⟩
      have hEx : (E F x : ℂ) = (y : ℂ) := congrArg Subtype.val ((E F).apply_symm_apply _)
      refine ⟨⟨x, mem_iUnion.mpr ⟨F, x.property⟩⟩, (hinterior F x).mp (hEx.symm ▸ hy), ?_⟩
      exact Subtype.ext ((hg F x).trans hEx)
  · intro x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := Φ.surjective ⟨g x, hx⟩
      have heq : g ⟨z, hP z.property⟩ = g x :=
        Subtype.ext ((hgraph z).trans (congrArg Subtype.val hz))
      exact congrArg Subtype.val (g.injective heq) ▸ z.property
    · intro hx
      exact (hgraph ⟨x, hx⟩).symm ▸ (Φ ⟨x, hx⟩).property

private theorem closed_bounded_region_complement
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (hgraph : P.image ⊆ ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val) :
    (⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val)ᶜ =
      ⋃ F : {F : P.Face // P.IsUnbounded F}, F.val.val := by
  classical
  ext z
  constructor
  · intro hz
    have hzP : z ∉ P.image := fun h => hz (hgraph h)
    obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr hzP
    have hF : P.IsUnbounded F := by
      by_contra hn
      exact hz (mem_iUnion.mpr ⟨⟨F, hn⟩, subset_closure hzF⟩)
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, hzF⟩
  · intro hz hclosed
    obtain ⟨F, hzF⟩ := mem_iUnion.mp hz
    obtain ⟨K, hzK⟩ := mem_iUnion.mp hclosed
    have hne : F.val ≠ K.val := fun he => K.property (he ▸ F.property)
    exact Set.disjoint_left.mp
      ((P.faces_disjoint hne).closure_right (P.face_open_frontier_subset_image hv F.val).1)
      hzF hzK

/-- Helper toward Proposition 3.9: the source of the closed-region
homeomorphism is exactly the complement of the unique unbounded run face.
The exterior itself is not part of that homeomorphism's domain. -/
theorem closed_region_eq_compl_exterior (u : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence u) (h : BoundaryHitWitnesses u) :
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    ∃ U : P.Face, P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      (⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val) = U.valᶜ := by
  intro P
  obtain ⟨U, hU, huniq, _⟩ := monotoneFamilyDrawing_realized_boundary_twoSided u hfin h
  have hgraph : P.image ⊆ ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val := by
    intro x hx
    obtain ⟨F, hF, hxF⟩ := drawing_image_covered_by_bounded_frontiers u hfin h x hx
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, frontier_subset_closure hxF⟩
  have hc := closed_bounded_region_complement P (kmswLimitDartVertex_surjective u hfin) hgraph
  have he : (⋃ F : {F : P.Face // P.IsUnbounded F}, F.val.val) = U.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨F, hxF⟩ := mem_iUnion.mp hx
      exact huniq F.val F.property ▸ hxF
    · intro hx
      exact mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩
  rw [he] at hc
  refine ⟨U, hU, huniq, ?_⟩
  exact compl_injective (by rw [compl_compl]; exact hc)























































































































































































































end DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry
end
