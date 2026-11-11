/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.PrimedFaceOrbitEquiv
public import DirectedDistances.KMSW.PrimedDeletedComponentUnbounded

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology




theorem primedExteriorRoot_ambientExternal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    limitExternalDart w (primedLimitDartMap w h futureMapOuterDart) := by
  have hmap : primedLimitDartMap w h futureMapOuterDart =
      (primedLimitEdgeMap w h 0, true) := by
    change (primedLimitEdgeMap w h 0, true ^^ primedLimitSideFlip w h 0) = _
    rw [primedLimitSideFlip_zero]
    rfl
  rw [hmap]
  have hLL := (primedAll_sim_zero w h).1.missing_root.2.2
  have hzero := (primedLimit_maps_eq_of_allocated w h 0).1 0
    (by change 0 < 1; decide)
  rw [← hzero] at hLL
  refine ⟨primedStageTime w h 0, fun n hn => ?_⟩
  have hLLn := (primedCrossing_LL_persistent w hn hLL).1
  have ha := (kmswStage_boundary_ids_lt_nextEdge w n).2
    (primedLimitEdgeMap w h 0) (by
      simp only [List.mem_append]
      exact Or.inl (Or.inr hLLn))
  refine ⟨ha, (kmswStage_isOuter_iff_boundary w n _).mpr ?_⟩
  exact Or.inr ⟨rfl, List.mem_append_left _ hLLn⟩





theorem primedExteriorRoot_contains_ambientExterior (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (E : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hE : (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded E) :
    E.val ⊆ (primedDartFace w h hfin hb futureMapOuterDart).val := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  let H := primedGeometricDartEquiv w h hfin hb
  obtain ⟨A, _, huniq, hborder⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  have hdE : P.dartBorders (H futureMapOuterDart).val E := by
    rw [huniq E hE]
    exact (hborder _).mpr (primedExteriorRoot_ambientExternal w h)
  obtain ⟨z, hz, hEset⟩ := E.property
  have hsub : Q.image ⊆ P.image :=
    mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)
  have hzQ : z ∉ Q.image := fun hzQ => hz (hsub hzQ)
  let U : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  have hEU : E.val ⊆ U.val := by
    rw [hEset]
    exact connectedComponentIn_mono z (compl_subset_compl.mpr hsub)
  have hdU : Q.dartBorders (H futureMapOuterDart) U := by
    obtain ⟨δ, hδ, hw⟩ := hdE
    exact ⟨δ, hδ, fun t ε ht htδ hε hεδ => hEU (hw t ε ht htδ hε hεδ)⟩
  have hroot : primedDartFace w h hfin hb futureMapOuterDart = U :=
    (primedDartFace_eq_iff w h hfin hb futureMapOuterDart U).mpr hdU
  rw [hroot]
  exact hEU



theorem primedExteriorRoot_unbounded (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded
      (primedDartFace w h hfin hb futureMapOuterDart) := by
  obtain ⟨E, hE, _, _⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  intro R
  obtain ⟨z, hz, hR⟩ := hE R
  exact ⟨z, primedExteriorRoot_contains_ambientExterior w h hfin hb E hE hz, hR⟩





theorem primedUnboundedFace_eq_root_of_avoids_ambientImage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face)
    (hF : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded F)
    (havoid : Disjoint F.val
      (monotoneFamilyDrawing w hfin (monotone_family_all w)).image) :
    F = primedDartFace w h hfin hb futureMapOuterDart := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨z, hzQ, hFset⟩ := F.property
  have hzF : z ∈ F.val := hFset ▸ mem_connectedComponentIn hzQ
  have hsub : F.val ⊆ P.imageᶜ := fun a ha => disjoint_left.mp havoid ha
  have hzP : z ∉ P.image := hsub hzF
  let A : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hzP, rfl⟩
  have hFA : F.val ⊆ A.val := by
    have hconn : IsPreconnected F.val := by
      rw [hFset]
      exact isPreconnected_connectedComponentIn
    exact hconn.subset_connectedComponentIn hzF hsub
  have hA : P.IsUnbounded A := by
    intro R
    obtain ⟨a, ha, hRa⟩ := hF R
    exact ⟨a, hFA ha, hRa⟩
  exact Q.faces_eq_of_mem hzF
    (primedExteriorRoot_contains_ambientExterior w h hfin hb A hA (hFA hzF))




theorem primedUnboundedFace_ne_root_meets_deletedGeometry (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face)
    (hF : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded F)
    (hne : F ≠ primedDartFace w h hfin hb futureMapOuterDart) :
    ∃ z ∈ F.val, z ∈
      (monotoneFamilyDrawing w hfin (monotone_family_all w)).image \
        (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image := by
  classical
  by_contra hnot
  apply hne
  apply primedUnboundedFace_eq_root_of_avoids_ambientImage w h hfin hb F hF
  apply disjoint_left.mpr
  intro z hzF hzP
  exact hnot ⟨z, hzF, hzP,
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).face_subset_compl F hzF⟩



private theorem exterior_face_eq_component {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (Q : PLDrawing D V flip rot vert)
    (F : Q.Face) {a : ℂ} (ha : a ∈ F.val) :
    F.val = connectedComponentIn Q.imageᶜ a := by
  obtain ⟨z, _, hF⟩ := F.property
  exact hF.trans (connectedComponentIn_eq (hF ▸ ha))




theorem primedDeletedArc_component_eq_root_of_incident_ambientExterior
    (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e)
    (E : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hE : (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded E)
    (hcontact : (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (e, false)).interior ∩ closure E.val).Nonempty) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      connectedComponentIn Q.imageᶜ a =
        (primedDartFace w h hfin hb futureMapOuterDart).val := by
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  dsimp only
  intro a ha
  obtain ⟨z, hz, hEset⟩ := E.property
  have hzE : z ∈ E.val := hEset ▸ mem_connectedComponentIn hz
  have hzroot := primedExteriorRoot_contains_ambientExterior w h hfin hb E hE hzE
  have hzcomp := primedAmbientFace_subset_deletedArc_component w hfin hb e he E
    hcontact a ha hzE
  exact (connectedComponentIn_eq hzcomp).trans
    (exterior_face_eq_component Q (primedDartFace w h hfin hb futureMapOuterDart)
      hzroot).symm




theorem primedDeletedBoundaryVertex_component_eq_root (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (k : ℤ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
      (boundaryVertex w hb k) ∉ (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    connectedComponentIn Q.imageᶜ (P.pos (boundaryVertex w hb k)) =
      (primedDartFace w h hfin hb futureMapOuterDart).val := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨E, hE, _, _⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  obtain ⟨q, hq, γ, hγ⟩ :=
    primedDeletedBoundaryVertex_joins_ambientExterior w hfin hb E hE k hv
  have hqroot := primedExteriorRoot_contains_ambientExterior w h hfin hb E hE hq
  have hqcomp : q ∈ connectedComponentIn Q.imageᶜ (P.pos (boundaryVertex w hb k)) :=
    (isPreconnected_range γ.continuous).subset_connectedComponentIn
      (show P.pos (boundaryVertex w hb k) ∈ range γ from ⟨0, γ.source⟩)
      (by rintro z ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩
  exact (connectedComponentIn_eq hqcomp).trans
    (exterior_face_eq_component Q (primedDartFace w h hfin hb futureMapOuterDart)
      hqroot).symm





theorem primedUnboundedFace_ne_root_deletedArc_obstruction (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face)
    (hF : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded F)
    (hne : F ≠ primedDartFace w h hfin hb futureMapOuterDart) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∃ e, MhatGeometricEdge w e ∧ ¬ primeBetaEdge w hfin hb e ∧
      ∃ a ∈ (P.arc (e, false)).interior,
        F.val = connectedComponentIn Q.imageᶜ a ∧
        ∀ E : P.Face, P.IsUnbounded E →
          ¬ ((P.arc (e, false)).interior ∩ closure E.val).Nonempty := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨z, hzF, hzP, hzQ⟩ :=
    primedUnboundedFace_ne_root_meets_deletedGeometry w h hfin hb F hF hne
  obtain ⟨e, he, a, ha, γ, hγ⟩ :=
    primedDeletedGeometryPoint_joins_deletedArcInterior w hfin hb z hzP hzQ
  obtain ⟨hm, hbeta⟩ := (primedDeletedEdge_iff w hfin hb e).mp he
  have hFz := exterior_face_eq_component Q F hzF
  have haF : a ∈ F.val := by
    rw [hFz]
    exact (isPreconnected_range γ.continuous).subset_connectedComponentIn
      (show z ∈ range γ from ⟨0, γ.source⟩)
      (by rintro b ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩
  have hFa := exterior_face_eq_component Q F haF
  refine ⟨e, hm, hbeta, a, ha, hFa, ?_⟩
  intro E hE hcontact
  apply hne
  apply Subtype.ext
  exact hFa.trans
    (primedDeletedArc_component_eq_root_of_incident_ambientExterior w h hfin hb e he
      E hE hcontact a ha)




theorem iidCodes_ae_primedExteriorRoot :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w),
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
        Q.IsUnbounded (primedDartFace w h hfin hb futureMapOuterDart) ∧
        (∀ E : P.Face, P.IsUnbounded E →
          E.val ⊆ (primedDartFace w h hfin hb futureMapOuterDart).val) ∧
        ∀ k : ℤ, P.pos (boundaryVertex w hb k) ∉ Q.image →
          connectedComponentIn Q.imageᶜ (P.pos (boundaryVertex w hb k)) =
            (primedDartFace w h hfin hb futureMapOuterDart).val := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hflow hfin hb
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa only [Nat.zero_add] using hflow 0
  exact ⟨h, hfin, hb, primedExteriorRoot_unbounded _ h hfin hb,
    primedExteriorRoot_contains_ambientExterior _ h hfin hb,
    primedDeletedBoundaryVertex_component_eq_root _ h hfin hb⟩


 
private theorem exterior_finish_mem_polyline_image (p : Polyline) : p.finish ∈ p.image := by
  rw [← p.point_last_eq_finish]
  by_cases hlen : 2 ≤ p.points.length
  · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
    rw [Polyline.segmentAt,
      show p.points.length - 2 + 1 = p.points.length - 1 by omega]
    exact right_mem_segment ℝ _ _
  · have hlen1 : p.points.length = 1 := by
      have := List.length_pos_iff.mpr p.nonempty
      omega
    simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
    exact Or.inl rfl


private theorem exterior_reverse_image_subset (p : Polyline) :
    p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ exterior_finish_mem_polyline_image p
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    have hrev : ∀ j, j < p.points.length →
        p.reverse.point j = p.point (p.points.length - 1 - j) := by
      intro j hj
      have hj' : p.points.length - 1 - j < p.points.length := by omega
      change p.points.reverse.getD j p.reverse.start =
        p.points.getD (p.points.length - 1 - j) p.start
      rw [List.getD_reverse j hj]
      rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj']
      rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj']
    have hidx : p.points.length - 1 - (i + 1) + 1 = p.points.length - 1 - i := by
      omega
    refine Or.inr ⟨p.points.length - 1 - (i + 1), by omega, ?_⟩
    simp only [Polyline.segmentAt, hrev i (by omega), hrev (i + 1) hi'] at hz
    simpa only [Polyline.segmentAt, hidx, segment_symm] using hz



private theorem exterior_reverse_interior (p : Polyline) :
    p.reverse.interior = p.interior := by
  have himage : p.reverse.image = p.image := by
    apply Subset.antisymm (exterior_reverse_image_subset p)
    simpa only [Polyline.reverse_reverse] using exterior_reverse_image_subset p.reverse
  simp only [Polyline.interior, himage, Polyline.start_reverse,
    Polyline.finish_reverse, pair_comm]

/-- Helper toward Lemma 5.13 (`lem-quad-kmsw`); not a paper result.
A short point on a polyline's first segment lies in its interior. -/
private theorem exterior_exists_small_interior_point (p : Polyline) (hlen : 2 ≤ p.points.length)
    (hne : p.initialDirection ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ p.start + t • p.initialDirection ∈ p.interior := by
  let q : ℝ → ℂ := fun t => p.start + t • p.initialDirection
  have hp0 : p.point 0 = p.start := by
    cases p with
    | mk points hpoints =>
      cases points with
      | nil => exact False.elim (hpoints rfl)
      | cons a rest => rfl
  have hline (t : ℝ) : q t = AffineMap.lineMap p.start (p.point 1) t := by
    rw [AffineMap.lineMap_apply_module']
    dsimp [q]
    simp only [Polyline.initialDirection]
    abel
  have hseg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : q t ∈ p.segmentAt 0 := by
    change q t ∈ segment ℝ (p.point 0) (p.point 1)
    rw [hp0, hline]
    exact lineMap_mem_segment ℝ p.start (p.point 1) ⟨ht0, ht1⟩
  have himage (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : q t ∈ p.image := by
    change q t ∈ {p.start} ∪ {z | ∃ i, i + 1 < p.points.length ∧
      z ∈ p.segmentAt i}
    right
    exact ⟨0, by omega, hseg t ht0 ht1⟩
  have hneStart (t : ℝ) (ht : 0 < t) : q t ≠ p.start := by
    intro h
    have hmul : (t : ℂ) * p.initialDirection = 0 := by
      dsimp [q] at h
      have h' : p.start + (t : ℂ) * p.initialDirection = p.start + 0 := by
        simpa using h
      exact add_left_cancel h'
    have htne : t ≠ 0 := ne_of_gt ht
    have hct : (t : ℂ) ≠ 0 := by exact_mod_cast htne
    exact (mul_ne_zero hct hne) hmul
  let m := min δ 1
  have hm : 0 < m := lt_min hδ zero_lt_one
  let a := m / 2
  let b := m / 4
  have ha : 0 < a ∧ a < δ ∧ a < 1 := by
    dsimp [a, m]
    constructor
    · exact half_pos hm
    constructor
    · exact (half_lt_self hm).trans_le (min_le_left _ _)
    · exact (half_lt_self hm).trans_le (min_le_right _ _)
  have hb : 0 < b ∧ b < δ ∧ b < 1 := by
    dsimp [b, m]
    constructor
    · positivity
    constructor
    · have hlt : min δ 1 / 4 < min δ 1 / 2 := by nlinarith [hm]
      exact hlt.trans ha.2.1
    · have hlt : min δ 1 / 4 < min δ 1 / 2 := by nlinarith [hm]
      exact hlt.trans ha.2.2
  have hab : q a ≠ q b := by
    intro h
    have hmul : (a : ℂ) * p.initialDirection = (b : ℂ) * p.initialDirection := by
      have h' := congrArg (fun z : ℂ => z - p.start) h
      dsimp [q] at h'
      simpa only [add_sub_cancel_left] using h'
    have hneab : a - b ≠ 0 := by
      dsimp [a, b]
      nlinarith [hm]
    have hcast : (a : ℂ) = b := mul_right_cancel₀ hne hmul
    have hab' : a = b := by exact_mod_cast hcast
    exact hneab (sub_eq_zero.mpr hab')
  by_cases hfinish : q a = p.finish
  · refine ⟨b, hb.1, hb.2.1, ?_⟩
    rw [Polyline.interior, Set.mem_sdiff]
    refine ⟨himage b (le_of_lt hb.1) (le_of_lt hb.2.2), ?_⟩
    intro h
    rcases Set.mem_insert_iff.mp h with hs | hf
    · exact (hneStart b hb.1) hs
    · exact hab (hfinish.trans hf.symm)
  · refine ⟨a, ha.1, ha.2.1, ?_⟩
    rw [Polyline.interior, Set.mem_sdiff]
    refine ⟨himage a (le_of_lt ha.1) (le_of_lt ha.2.2), ?_⟩
    intro h
    rcases Set.mem_insert_iff.mp h with hs | hf
    · exact (hneStart a ha.1) hs
    · exact hfinish hf

/-- Helper toward Lemma 5.13 (`lem-quad-kmsw`); not a paper result.
If a dart borders a face, the closure of that face meets the arc interior. -/
private theorem exterior_dartBorders_arcInterior_closure {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) :
    ((P.arc d).interior ∩ closure F.val).Nonempty := by
  obtain ⟨δ, hδ, hw⟩ := hF
  obtain ⟨t, ht, htδ, hinterior⟩ :=
    exterior_exists_small_interior_point (P.arc d) (P.arc_length d) (P.initial_nonzero d) hδ
  let g : ℝ → ℂ := fun ε => (P.arc d).start + (t : ℂ) *
    ((P.arc d).initialDirection + (ε : ℂ) * Complex.I * (P.arc d).initialDirection)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hzero : (0 : ℝ) ∈ closure (Ioo 0 δ) := by
    rw [closure_Ioo (ne_of_lt hδ)]
    exact ⟨le_rfl, hδ.le⟩
  have hsub : g '' Ioo 0 δ ⊆ F.val := by
    rintro z ⟨ε, hε, rfl⟩
    exact hw t ε ht htδ hε.1 hε.2
  have hz := closure_mono hsub (mem_closure_image hg.continuousAt hzero)
  have hz' : (P.arc d).start + (t : ℂ) * (P.arc d).initialDirection ∈ closure F.val := by
    simpa [g] using hz
  exact ⟨(P.arc d).start + (t : ℂ) * (P.arc d).initialDirection,
    hinterior, hz'⟩




private noncomputable def exterior_ambientFace (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face :=
  (dart_borders_unique w hfin hb d).exists.choose



private theorem exterior_ambientFace_borders (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
      (exterior_ambientFace w hfin hb d) :=
  (dart_borders_unique w hfin hb d).exists.choose_spec



private theorem exterior_ambientFace_lift_unique (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (A : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face) :
    ∃! U : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face,
      A.val ⊆ U.val := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨z, hz, hA⟩ := A.property
  have hzA : z ∈ A.val := hA ▸ mem_connectedComponentIn hz
  have hsub : Q.image ⊆ P.image :=
    mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)
  have hzQ : z ∉ Q.image := fun hzQ => hz (hsub hzQ)
  let U : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  have hAU : A.val ⊆ U.val := by
    rw [hA]
    exact connectedComponentIn_mono z (compl_subset_compl.mpr hsub)
  exact ⟨U, hAU, fun V hAV => Q.faces_eq_of_mem (hAV hzA) (hAU hzA)⟩



private noncomputable def exterior_lift (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face :=
  (exterior_ambientFace_lift_unique w hfin hb (exterior_ambientFace w hfin hb d)).exists.choose



private theorem exterior_lift_eq_iff (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) (U : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face) :
    exterior_lift w hfin hb d = U ↔ (exterior_ambientFace w hfin hb d).val ⊆ U.val := by
  have hu := exterior_ambientFace_lift_unique w hfin hb (exterior_ambientFace w hfin hb d)
  have hs : (exterior_ambientFace w hfin hb d).val ⊆ (exterior_lift w hfin hb d).val :=
    hu.exists.choose_spec
  exact ⟨fun he => he ▸ hs, fun hU => (hu.unique hs hU)⟩



private theorem exterior_lift_sameCycle (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d e : ℕ × Bool) (hde : (kmswInfFaceSucc w hfin).SameCycle d e) :
    exterior_lift w hfin hb d = exterior_lift w hfin hb e := by
  obtain ⟨F, hd, he⟩ := (faceOrbit_iff_common_face w hfin hb d e).mp hde
  have hAd : exterior_ambientFace w hfin hb d = F :=
    (dart_borders_unique w hfin hb d).unique (exterior_ambientFace_borders w hfin hb d) hd
  have hAe : exterior_ambientFace w hfin hb e = F :=
    (dart_borders_unique w hfin hb e).unique (exterior_ambientFace_borders w hfin hb e) he
  apply (exterior_lift_eq_iff w hfin hb d _).mpr
  rw [hAd, ← hAe]
  exact (exterior_lift_eq_iff w hfin hb e _).mp rfl




private theorem exterior_lift_flip_of_deleted (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) (hd : ¬ primeGeomEdge w hfin hb d.1) :
    exterior_lift w hfin hb (futureMapEdgeInv d) = exterior_lift w hfin hb d := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  have hcontact (b : Bool) :
      ((P.arc (d.1, false)).interior ∩
        closure (exterior_ambientFace w hfin hb (d.1, b)).val).Nonempty := by
    have hc := exterior_dartBorders_arcInterior_closure P (d.1, b)
      (exterior_ambientFace w hfin hb (d.1, b))
      (exterior_ambientFace_borders w hfin hb (d.1, b))
    cases b
    · exact hc
    · have hr : P.arc (d.1, true) = (P.arc (d.1, false)).reverse :=
        P.arc_flip (d.1, false)
      rwa [hr, exterior_reverse_interior] at hc
  obtain ⟨a, ha, _⟩ := hcontact false
  have haQ := primedDeletedArc_interior_avoids w hfin hb d.1 hd ha
  let U : Q.Face := ⟨connectedComponentIn Q.imageᶜ a, a, haQ, rfl⟩
  have hlift (b : Bool) : exterior_lift w hfin hb (d.1, b) = U :=
    (exterior_lift_eq_iff w hfin hb (d.1, b) U).mpr
      (primedAmbientFace_subset_deletedArc_component w hfin hb d.1 hd _ (hcontact b) a ha)
  exact (hlift (!d.2)).trans (hlift d.2).symm



private theorem exterior_lift_retained (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) :
    exterior_lift w hfin hb (primedGeometricDartEquiv w h hfin hb d).val =
      primedDartFace w h hfin hb d := by
  let H := primedGeometricDartEquiv w h hfin hb
  have hs := (exterior_lift_eq_iff w hfin hb (H d).val _).mp rfl
  have hd := exterior_ambientFace_borders w hfin hb (H d).val
  apply Eq.symm
  apply (primedDartFace_eq_iff w h hfin hb d _).mpr
  obtain ⟨δ, hδ, hw⟩ := hd
  exact ⟨δ, hδ, fun t ε ht htδ hε hεδ => hs (hw t ε ht htδ hε hεδ)⟩



private theorem exterior_lift_rotation_step (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (a : ℕ × Bool) :
    exterior_lift w hfin hb (futureMapEdgeInv (kmswInfRot w hfin a)) =
      exterior_lift w hfin hb a := by
  apply exterior_lift_sameCycle w hfin hb
  refine ⟨1, ?_⟩
  rw [zpow_one]
  change (kmswInfRot w hfin).symm
    (futureMapEdgeInv (futureMapEdgeInv (kmswInfRot w hfin a))) = a
  rw [futureMapEdgeInv_invol, Equiv.symm_apply_apply]





theorem primedDartFace_faceSucc (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) :
    primedDartFace w h hfin hb
        (kmswInfFaceSucc (primedCode (primedSimInput w) h)
          (primedCode_finiteIncidence w h hfin) d) =
      primedDartFace w h hfin hb d := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let S := primeDartSet w hfin hb
  let H := primedGeometricDartEquiv w h hfin hb
  let f := kmswInfFaceSucc (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin)
  let σ := kmswInfRot w hfin
  let τ := drawingFirstReturnPerm P S
  let x := H (f d)
  let k := subsetFirstReturnTime σ S (drawingPositiveReturn P S) x
  let t := fun j : ℕ => (σ : (ℕ × Bool) → ℕ × Bool)^[j] x.val
  have hk := subsetFirstReturnTime_spec σ S (drawingPositiveReturn P S) x
  have hτ : τ x = restrictedFlip P S (primeDartSet_flip_closed w hfin hb) (H d) := by
    have hr := primedGeometricDartEquiv_faceSuccessor w h hfin hb d
    change x = τ.symm _ at hr
    rw [hr, Equiv.apply_symm_apply]
  have htk : t k = futureMapEdgeInv (H d).val := by
    exact (subsetFirstReturnPerm_apply σ S (drawingPositiveReturn P S)
      (drawingPositiveReturnInv P S) x).symm.trans (congrArg Subtype.val hτ)
  have hiter (j : ℕ) : t (j + 1) = σ (t j) :=
    Function.iterate_succ_apply' _ _ _
  have hscan : ∀ j, j < k →
      exterior_lift w hfin hb (t j) = exterior_lift w hfin hb x.val := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hdel : ¬ primeGeomEdge w hfin hb (t (j + 1)).1 :=
        hk.2.2 (j + 1) (by omega) hj
      have hstep := exterior_lift_rotation_step w hfin hb (t j)
      change exterior_lift w hfin hb (futureMapEdgeInv (σ (t j))) = _ at hstep
      rw [← hiter] at hstep
      exact (exterior_lift_flip_of_deleted w hfin hb (t (j + 1)) hdel).symm.trans
        (hstep.trans (ih hjk))
  have hlast : k - 1 < k := by
    have hkpos : 0 < k := hk.1
    omega
  have hlaststep := exterior_lift_rotation_step w hfin hb (t (k - 1))
  change exterior_lift w hfin hb (futureMapEdgeInv (σ (t (k - 1)))) = _ at hlaststep
  rw [← hiter, show k - 1 + 1 = k by omega, htk,
    futureMapEdgeInv_invol] at hlaststep
  have heq : exterior_lift w hfin hb (H d).val =
      exterior_lift w hfin hb (H (f d)).val := hlaststep.trans (hscan _ hlast)
  exact (exterior_lift_retained w h hfin hb (f d)).symm.trans
    (heq.symm.trans (exterior_lift_retained w h hfin hb d))



theorem primedDartFace_eq_of_sameCycle (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d e : ℕ × Bool)
    (hde : (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle d e) :
    primedDartFace w h hfin hb d = primedDartFace w h hfin hb e := by
  let f := kmswInfFaceSucc (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin)
  obtain ⟨n, rfl⟩ := hde
  have hinv (a : ℕ × Bool) : primedDartFace w h hfin hb (f.symm a) =
      primedDartFace w h hfin hb a := by
    have hh := (primedDartFace_faceSucc w h hfin hb (f.symm a)).symm
    change primedDartFace w h hfin hb (f.symm a) =
      primedDartFace w h hfin hb (f (f.symm a)) at hh
    rwa [Equiv.apply_symm_apply] at hh
  symm
  induction n using Int.induction_on with
  | zero => rfl
  | succ n ih =>
    rw [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply,
      primedDartFace_faceSucc, ih]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega, zpow_add, zpow_neg_one,
      Equiv.Perm.mul_apply]
    exact (hinv _).trans ih




theorem primedRootFaceOrbit_borders_root (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool)
    (hd : (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d) :
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
      (primedGeometricDartEquiv w h hfin hb d)
      (primedDartFace w h hfin hb futureMapOuterDart) := by
  apply (primedDartFace_eq_iff w h hfin hb d _).mp
  exact (primedDartFace_eq_of_sameCycle w h hfin hb futureMapOuterDart d hd).symm





private theorem exterior_lift_surjective (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    Function.Surjective (exterior_lift w hfin hb) := by
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  intro F
  obtain ⟨z, hzQ, hF⟩ := F.property
  have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hzQ
  by_cases hzP : z ∈ P.image
  · obtain ⟨e, he, a, ha, γ, hγ⟩ :=
      primedDeletedGeometryPoint_joins_deletedArcInterior w hfin hb z hzP hzQ
    have haF : a ∈ F.val := by
      rw [hF]
      exact (isPreconnected_range γ.continuous).subset_connectedComponentIn
        (show z ∈ range γ from ⟨0, γ.source⟩)
        (by rintro b ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩
    have hFa := exterior_face_eq_component Q F haF
    have hcontact := exterior_dartBorders_arcInterior_closure P (e, false)
      (exterior_ambientFace w hfin hb (e, false))
      (exterior_ambientFace_borders w hfin hb (e, false))
    refine ⟨(e, false), (exterior_lift_eq_iff w hfin hb (e, false) F).mpr ?_⟩
    rw [hFa]
    exact primedAmbientFace_subset_deletedArc_component w hfin hb e he _ hcontact a ha
  · let A : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hzP, rfl⟩
    have hAF : A.val ⊆ F.val := by
      rw [hF]
      exact connectedComponentIn_mono z (compl_subset_compl.mpr
        (mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)))
    obtain ⟨d, hd⟩ := face_bordered w hfin hb A
    have hAd : exterior_ambientFace w hfin hb d = A :=
      (dart_borders_unique w hfin hb d).unique (exterior_ambientFace_borders w hfin hb d) hd
    refine ⟨d, (exterior_lift_eq_iff w hfin hb d F).mpr ?_⟩
    rw [hAd]
    exact hAF





theorem primedRealizedFace_bordered (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face) :
    ∃ d, (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
      (primedGeometricDartEquiv w h hfin hb d) F := by
  classical
  let H := primedGeometricDartEquiv w h hfin hb
  by_contra hn
  have hnotret (a : ℕ × Bool) (ha : exterior_lift w hfin hb a = F) :
      ¬ primeGeomEdge w hfin hb a.1 := by
    intro hret
    let b : {d // d ∈ primeDartSet w hfin hb} := ⟨a, hret⟩
    let d := H.symm b
    have heq : (H d).val = a := congrArg Subtype.val (H.apply_symm_apply b)
    have hdF : primedDartFace w h hfin hb d = F := by
      rw [← exterior_lift_retained, heq]
      exact ha
    exact hn ⟨d, (primedDartFace_eq_iff w h hfin hb d F).mp hdF⟩
  obtain ⟨a, ha⟩ := exterior_lift_surjective w hfin hb F
  have hflip (b : ℕ × Bool) (hbF : exterior_lift w hfin hb b = F) :
      exterior_lift w hfin hb (futureMapEdgeInv b) = F :=
    (exterior_lift_flip_of_deleted w hfin hb b (hnotret b hbF)).trans hbF
  have hrot (b : ℕ × Bool) (hbF : exterior_lift w hfin hb b = F) :
      exterior_lift w hfin hb (kmswInfRot w hfin b) = F := by
    have hs := (exterior_lift_rotation_step w hfin hb b).trans hbF
    have hd := hnotret (futureMapEdgeInv (kmswInfRot w hfin b)) hs
    exact (exterior_lift_flip_of_deleted w hfin hb (kmswInfRot w hfin b) hd).symm.trans hs
  have hrotInv (b : ℕ × Bool) (hbF : exterior_lift w hfin hb b = F) :
      exterior_lift w hfin hb ((kmswInfRot w hfin).symm b) = F := by
    have hs := exterior_lift_rotation_step w hfin hb ((kmswInfRot w hfin).symm b)
    rw [Equiv.apply_symm_apply] at hs
    exact hs.symm.trans (hflip b hbF)
  have hall (b : ℕ × Bool) : exterior_lift w hfin hb b = F := by
    have hp := futureMap_connected w hfin a b
    induction hp with
    | refl => exact ha
    | @tail b c hp hbc ih =>
      rcases hbc with rfl | rfl | rfl | rfl
      · exact hrot _ ih
      · exact hrotInv _ ih
      · exact hflip _ ih
      · exact hflip _ ih
  exact hnotret (H futureMapOuterDart).val (hall _) (H futureMapOuterDart).property





theorem primedUnboundedFace_border_external (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face)
    (hF : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded F)
    (d : ℕ × Bool)
    (hd : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
      (primedGeometricDartEquiv w h hfin hb d) F) :
    limitExternalDart (primedCode (primedSimInput w) h) d := by
  classical
  by_contra hext
  have hfinite := (finiteFaceOrbit_iff_not_external
    (primedCode (primedSimInput w) h) (primedCode_finiteIncidence w h hfin) d).mpr hext
  have hbdd := (primedDartFace_bounded_iff_finite w h hfin hb hex d).mpr hfinite
  have heq := (primedDartFace_eq_iff w h hfin hb d F).mpr hd
  rw [heq] at hbdd
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ℂ)
  obtain ⟨z, hz, hzR⟩ := hF R
  have hle : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  exact (not_lt_of_ge hle) hzR



theorem primedExternalDart_face_unbounded (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (d : ℕ × Bool) (hd : limitExternalDart (primedCode (primedSimInput w) h) d) :
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded
      (primedDartFace w h hfin hb d) := by
  classical
  by_contra hnot
  change ¬ ∀ R : ℝ, ∃ z ∈ (primedDartFace w h hfin hb d).val, R < ‖z‖ at hnot
  push Not at hnot
  obtain ⟨R, hR⟩ := hnot
  have hbdd : Bornology.IsBounded (primedDartFace w h hfin hb d).val := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
    exact ⟨R, fun z hz => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR z hz⟩
  exact ((finiteFaceOrbit_iff_not_external (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin) d).mp
      ((primedDartFace_bounded_iff_finite w h hfin hb hex d).mp hbdd)) hd





theorem primedUnboundedFace_ne_root_externalCycle_obstruction (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face)
    (hF : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded F)
    (hne : F ≠ primedDartFace w h hfin hb futureMapOuterDart) :
    ∃ d, limitExternalDart (primedCode (primedSimInput w) h) d ∧
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb d) F ∧
      ¬ (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d := by
  obtain ⟨d, hd⟩ := primedRealizedFace_bordered w h hfin hb F
  refine ⟨d, primedUnboundedFace_border_external w h hfin hb hex F hF d hd, hd, ?_⟩
  intro hroot
  apply hne
  have hFd := (primedDartFace_eq_iff w h hfin hb d F).mpr hd
  exact hFd.symm.trans
    (primedDartFace_eq_of_sameCycle w h hfin hb futureMapOuterDart d hroot).symm




theorem primedExternalOrbitBordersGoal_iff_externalRootCycle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) :
    primedExternalOrbitBordersGoal w h hfin hb ↔
      ∀ d, limitExternalDart (primedCode (primedSimInput w) h) d →
        (kmswInfFaceSucc (primedCode (primedSimInput w) h)
          (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d := by
  constructor
  · rintro ⟨U, _, huniq, hborder⟩ d hd
    have hU := huniq (primedDartFace w h hfin hb d)
      (primedExternalDart_face_unbounded w h hfin hb hex d hd)
    apply (hborder d).mp
    apply (primedDartFace_eq_iff w h hfin hb d U).mp hU
  · intro hclass
    refine ⟨primedDartFace w h hfin hb futureMapOuterDart,
      primedExteriorRoot_unbounded w h hfin hb, ?_, ?_⟩
    · intro F hF
      obtain ⟨d, hd⟩ := primedRealizedFace_bordered w h hfin hb F
      have hroot := hclass d
        (primedUnboundedFace_border_external w h hfin hb hex F hF d hd)
      exact ((primedDartFace_eq_iff w h hfin hb d F).mpr hd).symm.trans
        (primedDartFace_eq_of_sameCycle w h hfin hb futureMapOuterDart d hroot).symm
    · intro d
      constructor
      · intro hd
        exact hclass d (primedUnboundedFace_border_external w h hfin hb hex _
          (primedExteriorRoot_unbounded w h hfin hb) d hd)
      · exact primedRootFaceOrbit_borders_root w h hfin hb d

end DirectedDistances.KMSW
