module

public import DirectedDistances.KMSW.PrimedDeletedGeometryExclusion
import DirectedDistances.KMSW.HatDeletedGeometryVertical

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Complementary components through deleted primed arcs

Helpers toward Lemma 5.13 (`lem-quad-kmsw`), with source
The exterior-incident subclass is proved below. Escape for arbitrary interior
deleted arcs is not asserted. Retained beta-zero endpoints are never crossed. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

 
private theorem component_layoutArc_continuous_graph (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (layoutArc w n e).image =
      graphOver (layoutArc w n e).start.re (layoutArc w n e).finish.re f := by
  induction n with
  | zero =>
    have hab : (layoutPos w 0 0).re < (layoutPos w 0 1).re := by
      norm_num [layoutPos, kmswStageRank]
    refine ⟨segmentHeight (layoutPos w 0 0) (layoutPos w 0 1), ?_, ?_⟩
    · unfold segmentHeight
      fun_prop
    · simpa only [layoutArc, segmentArc_start, segmentArc_finish, graphOver]
        using segmentArc_image hab
  | succ n ih =>
    by_cases ho : e < (kmswStage w n).nextEdge
    · rw [layoutArc_old w n e ho]
      exact ih ho
    · have hf : e ∈ freshEdges w n := Finset.mem_Ico.mpr ⟨by omega, he⟩
      rw [(layoutArc_endpoints w (n + 1) e he).1,
        (layoutArc_endpoints w (n + 1) e he).2]
      let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
      let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
      by_cases hm : isFreshLeftMissing w n e
      · refine ⟨segmentHeight a b, ?_, ?_⟩
        · unfold segmentHeight
          fun_prop
        · simpa only [hm, ↓reduceIte, graphOver] using layoutArc_image_fresh w n e hf
      · refine ⟨roofHeight a b (n + 1) (rampSlope w n), continuous_roofHeight _ _ _ _, ?_⟩
        simpa only [hm, ↓reduceIte, graphOver] using layoutArc_image_fresh w n e hf

 
private theorem component_finish_mem_polyline_image (p : Polyline) : p.finish ∈ p.image := by
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

 
private theorem component_graph_interior (p : Polyline) (f : ℝ → ℝ)
    (hf : Continuous f) (hab : p.start.re < p.finish.re)
    (hgraph : p.image = graphOver p.start.re p.finish.re f) :
    IsPathConnected p.interior ∧ p.image ⊆ closure p.interior := by
  let g := graphParam f
  have hg : Continuous g := by
    change Continuous (fun x : ℝ => (x : ℂ) + (f x : ℂ) * Complex.I)
    fun_prop
  have ha : p.start.im = f p.start.re :=
    (show p.start ∈ graphOver p.start.re p.finish.re f from hgraph ▸ Or.inl rfl).2.2
  have hb : p.finish.im = f p.finish.re :=
    (show p.finish ∈ graphOver p.start.re p.finish.re f from
      hgraph ▸ component_finish_mem_polyline_image p).2.2
  have hga : g p.start.re = p.start := by
    apply Complex.ext <;> simp [g, graphParam, ha]
  have hgb : g p.finish.re = p.finish := by
    apply Complex.ext <;> simp [g, graphParam, hb]
  have heq : p.interior = g '' Ioo p.start.re p.finish.re := by
    ext z
    constructor
    · rintro ⟨hz, hne⟩
      have hz' : z ∈ graphOver p.start.re p.finish.re f := hgraph ▸ hz
      have hza : p.start.re < z.re := by
        apply lt_of_le_of_ne hz'.1
        intro hx
        apply hne
        left
        exact Complex.ext hx.symm (hz'.2.2.trans ((congrArg f hx.symm).trans ha.symm))
      have hzb : z.re < p.finish.re := by
        apply lt_of_le_of_ne hz'.2.1
        intro hx
        apply hne
        right
        exact Complex.ext hx (hz'.2.2.trans ((congrArg f hx).trans hb.symm))
      refine ⟨z.re, ⟨hza, hzb⟩, ?_⟩
      apply Complex.ext <;> simp [g, graphParam, hz'.2.2]
    · rintro ⟨x, hx, rfl⟩
      constructor
      · rw [hgraph]
        simpa [g, graphParam, graphOver] using And.intro hx.1.le hx.2.le
      · simp only [mem_insert_iff, mem_singleton_iff, not_or]
        constructor
        · intro h
          have hh := congrArg Complex.re h
          have hh' : x = p.start.re := by simpa [g, graphParam] using hh
          exact (ne_of_gt hx.1) hh'
        · intro h
          have hh := congrArg Complex.re h
          have hh' : x = p.finish.re := by simpa [g, graphParam] using hh
          exact (ne_of_lt hx.2) hh'
  constructor
  · rw [heq]
    exact ((convex_Ioo p.start.re p.finish.re).isPathConnected
      (nonempty_Ioo.mpr hab)).image hg
  · intro z hz
    by_cases hi : z ∈ p.interior
    · exact subset_closure hi
    have hend : z = p.start ∨ z = p.finish := by
      by_contra hn
      exact hi ⟨hz, by simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    have hcl : closure (Ioo p.start.re p.finish.re) =
        Icc p.start.re p.finish.re := closure_Ioo (ne_of_lt hab)
    rw [heq]
    rcases hend with rfl | rfl
    · have hc : p.start.re ∈ closure (Ioo p.start.re p.finish.re) := by
        rw [hcl]
        exact ⟨le_rfl, hab.le⟩
      have hc' := mem_closure_image hg.continuousAt hc
      rw [hga] at hc'
      exact hc'
    · have hc : p.finish.re ∈ closure (Ioo p.start.re p.finish.re) := by
        rw [hcl]
        exact ⟨hab.le, le_rfl⟩
      have hc' := mem_closure_image hg.continuousAt hc
      rw [hgb] at hc'
      exact hc'

 
private theorem component_arc_interior_geometry (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (e : ℕ) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    IsPathConnected (P.arc (e, false)).interior ∧
      (P.arc (e, false)).image ⊆ closure (P.arc (e, false)).interior := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have he := kmsw_edge_allocated_by_self w e
  have harc : P.arc (e, false) = layoutArc w e e := by
    rw [familyDrawing_arc w hfin (monotone_family_all w) e (⟨e, he⟩, false)]
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      (familyG w (monotone_family_all w) e).arc_layout (⟨e, he⟩, false)
  obtain ⟨f, hf, hgraph⟩ := component_layoutArc_continuous_graph w e e he
  have hab : (layoutArc w e e).start.re < (layoutArc w e e).finish.re := by
    rw [(layoutArc_endpoints w e e he).1, (layoutArc_endpoints w e e he).2]
    change (kmswStageRank w e ((kmswStage w e).west e) : ℝ) <
      (kmswStageRank w e ((kmswStage w e).east e) : ℝ)
    exact_mod_cast kmswStageRank_strict w e e he
  change IsPathConnected (P.arc (e, false)).interior ∧
    (P.arc (e, false)).image ⊆ closure (P.arc (e, false)).interior
  rw [harc]
  exact component_graph_interior _ f hf hab hgraph



private theorem component_of_closure_contact {K S : Set ℂ} (hS : IsPreconnected S)
    (hSK : S ⊆ Kᶜ) {a : ℂ} (haK : a ∉ K) (haS : a ∈ closure S) :
    S ⊆ connectedComponentIn Kᶜ a := by
  have hconn : IsPreconnected (insert a S) :=
    hS.subset_closure (subset_insert a S) (insert_subset haS subset_closure)
  exact (subset_insert a S).trans (hconn.subset_connectedComponentIn
    (mem_insert a S) (insert_subset haK hSK))




theorem primedDeletedArc_interior_subset_component (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      (P.arc (e, false)).interior ⊆ connectedComponentIn Q.imageᶜ a := by
  dsimp only
  intro a ha
  exact (component_arc_interior_geometry w hfin e).1.isConnected.isPreconnected
    |>.subset_connectedComponentIn ha (primedDeletedArc_interior_avoids w hfin hb e he)



theorem primedDeletedArc_component_eq (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior, ∀ b ∈ (P.arc (e, false)).interior,
      connectedComponentIn Q.imageᶜ a = connectedComponentIn Q.imageᶜ b := by
  dsimp only
  intro a ha b hb'
  exact connectedComponentIn_eq
    (primedDeletedArc_interior_subset_component w hfin hb e he a ha hb')



theorem primedAmbientFace_subset_deletedArc_component (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hF : (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (e, false)).interior ∩ closure F.val).Nonempty) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior, F.val ⊆ connectedComponentIn Q.imageᶜ a := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  dsimp only
  intro a ha
  obtain ⟨b, hbArc, hbF⟩ := hF
  have hconn : IsPreconnected F.val := by
    obtain ⟨x, _, hx⟩ := F.property
    rw [hx]
    exact isPreconnected_connectedComponentIn
  have havoid : F.val ⊆ Q.imageᶜ := fun z hz hzQ =>
    P.face_subset_compl F hz (mhatPrimeDrawing_image_subset w hfin hb
      (monotone_family_all w) hzQ)
  rw [primedDeletedArc_component_eq w hfin hb e he a ha b hbArc]
  exact component_of_closure_contact hconn havoid
    (primedDeletedArc_interior_avoids w hfin hb e he hbArc) hbF




theorem primedDeletedArc_component_unbounded_of_incident_unboundedFace
    (w : ℕ → Fin 3) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ)
    (he : ¬ primeGeomEdge w hfin hb e)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hF : (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (e, false)).interior ∩ closure F.val).Nonempty)
    (hU : (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded F) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  dsimp only
  intro a ha R
  obtain ⟨z, hz, hR⟩ := hU R
  exact ⟨z, primedAmbientFace_subset_deletedArc_component w hfin hb e he F hF a ha hz, hR⟩




private theorem component_reverse_image_subset (p : Polyline) :
    p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · rw [Polyline.start_reverse] at hz
    exact hz ▸ component_finish_mem_polyline_image p
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



private theorem component_reverse_interior (p : Polyline) :
    p.reverse.interior = p.interior := by
  have himage : p.reverse.image = p.image := by
    apply Subset.antisymm (component_reverse_image_subset p)
    simpa only [Polyline.reverse_reverse] using component_reverse_image_subset p.reverse
  simp only [Polyline.interior, himage, Polyline.start_reverse,
    Polyline.finish_reverse, pair_comm]

/-- Helper toward Lemma 5.13 (`lem-quad-kmsw`); not a paper result.
A short point on a polyline's first segment lies in its interior. -/
private theorem component_exists_small_interior_point (p : Polyline) (hlen : 2 ≤ p.points.length)
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
private theorem component_dartBorders_arcInterior_closure {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) :
    ((P.arc d).interior ∩ closure F.val).Nonempty := by
  obtain ⟨δ, hδ, hw⟩ := hF
  obtain ⟨t, ht, htδ, hinterior⟩ :=
    component_exists_small_interior_point (P.arc d) (P.arc_length d) (P.initial_nonzero d) hδ
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





theorem primedDeletedArc_component_unbounded_of_externalDart
    (w : ℕ → Fin 3) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ)
    (hm : MhatGeometricEdge w e) (hbeta : ¬ primeBetaEdge w hfin hb e)
    (hext : limitExternalDart w (e, false) ∨ limitExternalDart w (e, true)) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨U, hU, _, hborder⟩ := monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  have hcontact : ((P.arc (e, false)).interior ∩ closure U.val).Nonempty := by
    rcases hext with hext | hext
    · exact component_dartBorders_arcInterior_closure P (e, false) U
        ((hborder _).mpr hext)
    · have hc := component_dartBorders_arcInterior_closure P (e, true) U
        ((hborder _).mpr hext)
      have hrev : P.arc (e, true) = (P.arc (e, false)).reverse := P.arc_flip (e, false)
      rwa [hrev, component_reverse_interior] at hc
  exact primedDeletedArc_component_unbounded_of_incident_unboundedFace w hfin hb e
    ((primedDeletedEdge_iff w hfin hb e).mpr ⟨hm, hbeta⟩) U hcontact hU





theorem primedBoundedHatFace_avoids_primedImage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (F : PlaneFaces (hatRealizedDrawing w hfin)) :
    Disjoint F.val.val (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image := by
  exact (hatBoundedFaceDeletedGeometryExclusionGoal_holds w h hfin F).mono_right
    (mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w))





theorem primedBoundedHatFace_subset_deletedArc_component (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ)
    (he : ¬ primeGeomEdge w hfin hb e) (F : PlaneFaces (hatRealizedDrawing w hfin))
    (hF : (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (e, false)).interior ∩ closure F.val.val).Nonempty) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior, F.val.val ⊆ connectedComponentIn Q.imageᶜ a := by
  dsimp only
  intro a ha
  obtain ⟨b, hbArc, hbF⟩ := hF
  have hconn : IsPreconnected F.val.val := by
    obtain ⟨x, _, hx⟩ := F.val.property
    rw [hx]
    exact isPreconnected_connectedComponentIn
  have havoid : F.val.val ⊆
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).imageᶜ :=
    fun z hz => disjoint_left.mp (primedBoundedHatFace_avoids_primedImage w h hfin hb F) hz
  rw [primedDeletedArc_component_eq w hfin hb e he a ha b hbArc]
  exact component_of_closure_contact hconn havoid
    (primedDeletedArc_interior_avoids w hfin hb e he hbArc) hbF





theorem primedDeletedArc_component_eq_of_common_boundedHatFace (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e f : ℕ)
    (he : ¬ primeGeomEdge w hfin hb e) (hf : ¬ primeGeomEdge w hfin hb f)
    (F : PlaneFaces (hatRealizedDrawing w hfin))
    (hFe : (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (e, false)).interior ∩ closure F.val.val).Nonempty)
    (hFf : (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (f, false)).interior ∩ closure F.val.val).Nonempty) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior, ∀ b ∈ (P.arc (f, false)).interior,
      connectedComponentIn Q.imageᶜ a = connectedComponentIn Q.imageᶜ b := by
  dsimp only
  intro a ha b hb'
  obtain ⟨z, hz, hF⟩ := F.val.property
  have hzF : z ∈ F.val.val := hF ▸ mem_connectedComponentIn hz
  exact (connectedComponentIn_eq
    (primedBoundedHatFace_subset_deletedArc_component w h hfin hb e he F hFe a ha hzF)).trans
      (connectedComponentIn_eq
        (primedBoundedHatFace_subset_deletedArc_component w h hfin hb f hf F hFf b hb' hzF)).symm





theorem primedDeletedBoundaryVertex_component_unbounded (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (k : ℤ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
      (boundaryVertex w hb k) ∉ (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ (P.pos (boundaryVertex w hb k)),
      R < ‖z‖ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  dsimp only
  obtain ⟨E, hE, _, _⟩ := monotoneFamilyDrawing_faceClassification_twoSided w hfin hb
  obtain ⟨q, hqE, hjoin⟩ :=
    primedDeletedBoundaryVertex_joins_ambientExterior w hfin hb E hE k hv
  have hq : q ∈ connectedComponentIn Q.imageᶜ (P.pos (boundaryVertex w hb k)) := by
    obtain ⟨γ, hγ⟩ := hjoin
    exact (isPreconnected_range γ.continuous).subset_connectedComponentIn
      (show P.pos (boundaryVertex w hb k) ∈ range γ from ⟨0, γ.source⟩)
      (by rintro b ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩
  have hconn : IsPreconnected E.val := by
    obtain ⟨x, _, hx⟩ := E.property
    rw [hx]
    exact isPreconnected_connectedComponentIn
  have havoid : E.val ⊆ Q.imageᶜ := fun z hz hzQ =>
    P.face_subset_compl E hz (mhatPrimeDrawing_image_subset w hfin hb
      (monotone_family_all w) hzQ)
  have hsub : E.val ⊆ connectedComponentIn Q.imageᶜ (P.pos (boundaryVertex w hb k)) := by
    rw [connectedComponentIn_eq hq]
    exact hconn.subset_connectedComponentIn hqE havoid
  intro R
  obtain ⟨z, hz, hR⟩ := hE R
  exact ⟨z, hsub hz, hR⟩





theorem primedDeletedArc_component_unbounded_of_deletedBoundaryEndpoint
    (w : ℕ → Fin 3) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e)
    (k : ℤ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
      (boundaryVertex w hb k) ∉ (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image)
    (hend : edgeWest w e = boundaryVertex w hb k ∨ edgeEast w e = boundaryVertex w hb k) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  dsimp only
  intro a ha
  have hvArc : P.pos (boundaryVertex w hb k) ∈ (P.arc (e, false)).image := by
    rcases hend with hw | ht
    · have hs : (P.arc (e, false)).start = P.pos (boundaryVertex w hb k) := by
        simpa only [kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte, hw]
          using P.arc_start (e, false)
      exact hs ▸ Or.inl rfl
    · have hs : (P.arc (e, false)).finish = P.pos (boundaryVertex w hb k) := by
        simpa only [kmswLimitDartVertex, Bool.not_false, ↓reduceIte, ht]
          using P.arc_finish (e, false)
      exact hs ▸ component_finish_mem_polyline_image (P.arc (e, false))
  have hacomp : a ∈ connectedComponentIn Q.imageᶜ (P.pos (boundaryVertex w hb k)) :=
    component_of_closure_contact
      (component_arc_interior_geometry w hfin e).1.isConnected.isPreconnected
      (primedDeletedArc_interior_avoids w hfin hb e he) hv
      ((component_arc_interior_geometry w hfin e).2 hvArc) ha
  rw [← connectedComponentIn_eq hacomp]
  exact primedDeletedBoundaryVertex_component_unbounded w hfin hb k hv





theorem primedBoundedFace_arcIntersections_finite (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w))) :
    {e : ℕ | (F.val.val ∩
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
        (e, false)).interior).Nonempty}.Finite := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  apply ((P.locally_finite F.val.val F.property).image Prod.fst).subset
  rintro e ⟨z, hzF, hzArc⟩
  exact ⟨(e, false), ⟨z, hzF, hzArc.1⟩, rfl⟩





theorem iidCodes_ae_primedDeletedArc_component_unbounded_of_externalDart :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w),
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
        ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
          (limitExternalDart w (e, false) ∨ limitExternalDart w (e, true)) →
          ∀ a ∈ (P.arc (e, false)).interior,
            ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  filter_upwards [iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hfin hb
  exact ⟨hfin, hb, fun e hm hbeta hext =>
    primedDeletedArc_component_unbounded_of_externalDart _ hfin hb e hm hbeta hext⟩





theorem primedDeletedGeometryExclusion_iff_interiorArcComponents_unbounded
    (w : ℕ → Fin 3) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedBoundedFace_deletedGeometryExclusionGoal w hfin hb ↔
      let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
      let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
      ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
        (¬ limitExternalDart w (e, false) ∧ ¬ limitExternalDart w (e, true)) →
        (∀ k : ℤ, (edgeWest w e = boundaryVertex w hb k ∨
          edgeEast w e = boundaryVertex w hb k) → P.pos (boundaryVertex w hb k) ∈ Q.image) →
        ∀ a ∈ (P.arc (e, false)).interior,
          ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  classical
  rw [primedDeletedGeometryExclusion_iff_arcComponents_unbounded]
  dsimp only
  constructor
  · intro hall e hm hbeta _ _
    exact hall e hm hbeta
  · intro hinternal e hm hbeta
    by_cases hext : limitExternalDart w (e, false) ∨ limitExternalDart w (e, true)
    · exact primedDeletedArc_component_unbounded_of_externalDart w hfin hb e hm hbeta hext
    by_cases hbdy : ∃ k : ℤ,
        (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos (boundaryVertex w hb k) ∉
          (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image ∧
        (edgeWest w e = boundaryVertex w hb k ∨ edgeEast w e = boundaryVertex w hb k)
    · obtain ⟨k, hk, hend⟩ := hbdy
      exact primedDeletedArc_component_unbounded_of_deletedBoundaryEndpoint w hfin hb e
        ((primedDeletedEdge_iff w hfin hb e).mpr ⟨hm, hbeta⟩) k hk hend
    · apply hinternal e hm hbeta
      · exact not_or.mp hext
      · intro k hk
        by_contra hv
        exact hbdy ⟨k, hv, hk⟩





theorem iidCodes_ae_primedBoundedHatFace_subset_deletedArc_component :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (_h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w),
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
        ∀ e, ¬ primeGeomEdge w hfin hb e →
          ∀ F : PlaneFaces (hatRealizedDrawing w hfin),
            ((P.arc (e, false)).interior ∩ closure F.val.val).Nonempty →
            ∀ a ∈ (P.arc (e, false)).interior,
              F.val.val ⊆ connectedComponentIn Q.imageᶜ a := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hflow hfin hb
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa only [Nat.zero_add] using hflow 0
  exact ⟨h, hfin, hb, fun e he F hF =>
    primedBoundedHatFace_subset_deletedArc_component _ h hfin hb e he F hF⟩

end DirectedDistances.KMSW
