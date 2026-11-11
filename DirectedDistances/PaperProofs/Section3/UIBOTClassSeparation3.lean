/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation2
public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart2
public import DirectedDistances.PlanarMap.GraphRegionClosure
public import DirectedDistances.PlanarMap.D39BallOrbitComponents3
import Mathlib.Topology.Compactness.LocallyFinite








public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.RandomWalk
open Set Topology
open scoped Topology

private theorem cap_low_le_high (C : GraphCap) (x : ℝ) (hx : x ∈ Icc C.a C.b) :
    C.low x ≤ C.high x := by
  rcases hx.1.eq_or_lt with ha | ha
  · rw [← ha, C.left_join]
  rcases hx.2.eq_or_lt with hb | hb
  · rw [hb, C.right_join]
  exact (C.separated x ⟨ha, hb⟩).le

private def capParam (C : GraphCap) (p : Icc C.a C.b × unitInterval) : ℂ :=
  ⟨p.1, C.low p.1 + (p.2 : ℝ) * (C.high p.1 - C.low p.1)⟩

private theorem capParam_continuous (C : GraphCap) : Continuous (capParam C) := by
  have hl : Continuous (fun p : Icc C.a C.b × unitInterval => C.low p.1) :=
    (continuousOn_iff_continuous_domRestrict.mp C.low_continuous).comp continuous_fst
  have hh : Continuous (fun p : Icc C.a C.b × unitInterval => C.high p.1) :=
    (continuousOn_iff_continuous_domRestrict.mp C.high_continuous).comp continuous_fst
  have hform : capParam C = fun p : Icc C.a C.b × unitInterval =>
      ((p.1 : ℝ) : ℂ) +
        ((C.low p.1 + (p.2 : ℝ) * (C.high p.1 - C.low p.1) : ℝ) : ℂ) * Complex.I := by
    funext p
    apply Complex.ext <;> simp [capParam]
  rw [hform]
  apply Continuous.add
  · exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  · exact (Complex.continuous_ofReal.comp
      (hl.add ((continuous_subtype_val.comp continuous_snd).mul (hh.sub hl)))).mul
        continuous_const

private theorem capParam_mem (C : GraphCap) (p : Icc C.a C.b × unitInterval) :
    capParam C p ∈ closure C.region := by
  rw [show closure C.region = closedGraphRegion C.a C.b C.low C.high from
    closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous C.high_continuous
      C.separated C.left_join C.right_join]
  have hg := cap_low_le_high C p.1 p.1.property
  have ht : 0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 := p.2.property
  refine ⟨p.1.property.1, p.1.property.2, ?_, ?_⟩ <;>
    dsimp [capParam] <;> nlinarith

private theorem capParam_surjective (C : GraphCap) :
    ∀ z ∈ closure C.region, ∃ p : Icc C.a C.b × unitInterval, capParam C p = z := by
  intro z hz
  rw [show closure C.region = closedGraphRegion C.a C.b C.low C.high from
    closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous C.high_continuous
      C.separated C.left_join C.right_join] at hz
  have hx : z.re ∈ Icc C.a C.b := ⟨hz.1, hz.2.1⟩
  by_cases hg : C.low z.re = C.high z.re
  · refine ⟨(⟨z.re, hx⟩, 0), ?_⟩
    apply Complex.ext
    · rfl
    · dsimp [capParam]
      have he : z.im = C.low z.re := by
        exact le_antisymm (hg ▸ hz.2.2.2) hz.2.2.1
      simp only [he, zero_mul, add_zero]
  · have hd : 0 < C.high z.re - C.low z.re :=
      sub_pos.mpr (lt_of_le_of_ne (cap_low_le_high C z.re hx) hg)
    let t : unitInterval := ⟨(z.im - C.low z.re) / (C.high z.re - C.low z.re),
      (div_nonneg (sub_nonneg.mpr hz.2.2.1) hd.le),
      (div_le_one hd).mpr (by linarith only [hz.2.2.2])⟩
    refine ⟨(⟨z.re, hx⟩, t), ?_⟩
    apply Complex.ext
    · rfl
    · dsimp [capParam, t]
      rw [div_mul_cancel₀ _ hd.ne']
      ring

private theorem capParam_eq_iff (C : GraphCap)
    (p q : Icc C.a C.b × unitInterval) :
    capParam C p = capParam C q ↔
      p.1 = q.1 ∧ ((p.1 : ℝ) = C.a ∨ (p.1 : ℝ) = C.b ∨ p.2 = q.2) := by
  constructor
  · intro he
    have hx : p.1 = q.1 := Subtype.ext (congrArg Complex.re he)
    refine ⟨hx, ?_⟩
    by_cases ha : (p.1 : ℝ) = C.a
    · exact Or.inl ha
    by_cases hb : (p.1 : ℝ) = C.b
    · exact Or.inr (Or.inl hb)
    right; right
    have hd := C.separated p.1
      ⟨lt_of_le_of_ne p.1.property.1 (Ne.symm ha), lt_of_le_of_ne p.1.property.2 hb⟩
    have hy := congrArg Complex.im he
    change C.low p.1 + (p.2 : ℝ) * (C.high p.1 - C.low p.1) =
      C.low q.1 + (q.2 : ℝ) * (C.high q.1 - C.low q.1) at hy
    rw [← hx] at hy
    exact Subtype.ext (mul_right_cancel₀ (sub_pos.mpr hd).ne' (add_left_cancel hy))
  · rintro ⟨hx, h⟩
    apply Complex.ext
    · exact congrArg Subtype.val hx
    · change C.low p.1 + (p.2 : ℝ) * (C.high p.1 - C.low p.1) =
        C.low q.1 + (q.2 : ℝ) * (C.high q.1 - C.low q.1)
      rw [← hx]
      rcases h with ha | hb | ht
      · rw [ha, C.left_join, sub_self, mul_zero, mul_zero]
      · rw [hb, C.right_join, sub_self, mul_zero, mul_zero]
      · rw [ht]

private theorem capParam_frontier (C : GraphCap)
    (p : Icc C.a C.b × unitInterval) :
    capParam C p ∈ frontier C.region ↔
      (p.1 : ℝ) = C.a ∨ (p.1 : ℝ) = C.b ∨ (p.2 : ℝ) = 0 ∨ (p.2 : ℝ) = 1 := by
  have hopen : IsOpen C.region := isOpen_graphRegion C.low_continuous C.high_continuous
  rw [frontier, hopen.interior_eq]
  have hm := capParam_mem C p
  simp only [mem_sdiff, hm, true_and]
  have ht : 0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 := p.2.property
  constructor
  · intro hn
    by_contra he
    simp only [not_or] at he
    have hx : C.a < (p.1 : ℝ) ∧ (p.1 : ℝ) < C.b :=
      ⟨lt_of_le_of_ne p.1.property.1 (Ne.symm he.1),
        lt_of_le_of_ne p.1.property.2 he.2.1⟩
    have hd := C.separated p.1 hx
    have ht' : 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm he.2.2.1), lt_of_le_of_ne ht.2 he.2.2.2⟩
    apply hn
    refine ⟨hx.1, hx.2, ?_, ?_⟩ <;> dsimp [capParam] <;> nlinarith
  · intro he hz
    change C.a < (p.1 : ℝ) ∧ (p.1 : ℝ) < C.b ∧
      C.low p.1 < C.low p.1 + (p.2 : ℝ) * (C.high p.1 - C.low p.1) ∧
      C.low p.1 + (p.2 : ℝ) * (C.high p.1 - C.low p.1) < C.high p.1 at hz
    rcases he with ha | hb | ht0 | ht1
    · exact (ne_of_gt hz.1) ha
    · exact (ne_of_lt hz.2.1) hb
    · rw [ht0, zero_mul, add_zero] at hz
      exact (lt_irrefl _ hz.2.2.1)
    · rw [ht1, one_mul] at hz
      linarith only [hz.2.2.2]

private theorem homeomorph_of_same_fibres
    {X Y Z : Type*}
    [uibotClassSeparation3TopologyX : TopologicalSpace X]
    [uibotClassSeparation3CompactX : CompactSpace X]
    [uibotClassSeparation3TopologyY : TopologicalSpace Y]
    [uibotClassSeparation3T2Y : T2Space Y]
    [uibotClassSeparation3TopologyZ : TopologicalSpace Z]
    [uibotClassSeparation3T2Z : T2Space Z]
    (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (heq : ∀ x y, f x = f y ↔ g x = g y) :
    ∃ H : Y ≃ₜ Z, ∀ x, H (f x) = g x := by
  classical
  let s : Y → X := fun y => (hfs y).choose
  have hs (y : Y) : f (s y) = y := (hfs y).choose_spec
  let F : Y → Z := fun y => g (s y)
  have hF (x : X) : F (f x) = g x := (heq _ _).mp (hs (f x))
  have hq := hf.isClosedMap.isQuotientMap hf hfs
  have hFc : Continuous F := hq.continuous_iff.mpr (by
    have he : F ∘ f = g := funext hF
    rw [he]
    exact hg)
  have hFi : Function.Injective F := by
    intro x y hxy
    have h := (heq (s x) (s y)).mpr hxy
    simpa only [hs] using h
  have hFs : Function.Surjective F := by
    intro z
    obtain ⟨x, rfl⟩ := hgs z
    exact ⟨f x, hF x⟩
  let uibotClassSeparation3CompactY : CompactSpace Y :=
    ⟨by simpa only [image_univ, hfs.range_eq] using (isCompact_univ.image hf)⟩
  exact ⟨hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩), hF⟩

private def tentCap (C : GraphCap) : GraphCap where
  a := C.a
  b := C.b
  low := fun _ => 0
  high := fun x => min (x - C.a) (C.b - x)
  ab := C.ab
  low_continuous := continuousOn_const
  high_continuous := ((continuous_id.sub continuous_const).min
    (continuous_const.sub continuous_id)).continuousOn
  separated := by
    intro x hx
    exact lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  left_join := by simp only [sub_self, min_eq_left (sub_nonneg.mpr C.ab.le)]
  right_join := by simp only [sub_self, min_eq_right (sub_nonneg.mpr C.ab.le)]

private theorem tentCap_convex (C : GraphCap) : Convex ℝ (tentCap C).region := by
  intro x hx y hy s t hs ht hst
  change C.a < x.re ∧ x.re < C.b ∧ 0 < x.im ∧
    x.im < min (x.re - C.a) (C.b - x.re) at hx
  change C.a < y.re ∧ y.re < C.b ∧ 0 < y.im ∧
    y.im < min (y.re - C.a) (C.b - y.re) at hy
  simp only [lt_min_iff] at hx hy
  change C.a < (s • x + t • y).re ∧ (s • x + t • y).re < C.b ∧
    0 < (s • x + t • y).im ∧
      (s • x + t • y).im < min ((s • x + t • y).re - C.a)
        (C.b - (s • x + t • y).re)
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul, lt_min_iff]
  rcases eq_or_lt_of_le hs with rfl | hs'
  · simp only [zero_add] at hst
    subst t
    simpa only [zero_mul, one_mul, zero_add] using hy
  · have combine {a b c : ℝ} (ha : a < b) (hc : a < c) : a < s * b + t * c := by
      have hsa : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_pos hs' (sub_pos.mpr ha), mul_nonneg ht (sub_nonneg.mpr hc.le)]
    have hsa : s * C.a + t * C.a = C.a := by rw [← add_mul, hst, one_mul]
    have hsb : s * C.b + t * C.b = C.b := by rw [← add_mul, hst, one_mul]
    refine ⟨combine hx.1 hy.1, ?_, ?_, ?_, ?_⟩
    · nlinarith [mul_pos hs' (sub_pos.mpr hx.2.1),
        mul_nonneg ht (sub_nonneg.mpr hy.2.1.le)]
    · simpa only [mul_zero, add_zero] using combine hx.2.2.1 hy.2.2.1
    · nlinarith [mul_pos hs' (sub_pos.mpr hx.2.2.2.1),
        mul_nonneg ht (sub_nonneg.mpr hy.2.2.2.1.le)]
    · nlinarith [mul_pos hs' (sub_pos.mpr hx.2.2.2.2),
        mul_nonneg ht (sub_nonneg.mpr hy.2.2.2.2.le)]

/-- Helper toward Proposition 3.9: vertical interpolation, collapsing exactly
the two endpoint fibres, gives every graph cap a closed-disk chart with its
entire frontier corresponding to the unit circle. -/
theorem uibotClassSeparation3_graphCap_disk_chart (C : GraphCap) :
    ∃ c : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure C.region,
      ∀ z, ((c z : ℂ) ∈ frontier C.region ↔ ‖(z : ℂ)‖ = 1) := by
  let D := tentCap C
  let f : Icc C.a C.b × unitInterval → closure D.region :=
    fun p => ⟨capParam D p, capParam_mem D p⟩
  let g : Icc C.a C.b × unitInterval → closure C.region :=
    fun p => ⟨capParam C p, capParam_mem C p⟩
  have hf : Continuous f := (capParam_continuous D).subtype_mk _
  have hg : Continuous g := (capParam_continuous C).subtype_mk _
  have hfs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨p, hp⟩ := capParam_surjective D z hz
    exact ⟨p, Subtype.ext hp⟩
  have hgs : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨p, hp⟩ := capParam_surjective C z hz
    exact ⟨p, Subtype.ext hp⟩
  have heq (p q : Icc C.a C.b × unitInterval) : f p = f q ↔ g p = g q := by
    change (⟨capParam D p, _⟩ : closure D.region) = ⟨capParam D q, _⟩ ↔
      (⟨capParam C p, _⟩ : closure C.region) = ⟨capParam C q, _⟩
    simp only [Subtype.mk.injEq]
    exact (capParam_eq_iff D p q).trans (capParam_eq_iff C p q).symm
  obtain ⟨E, hE⟩ := homeomorph_of_same_fibres f g hf hg hfs hgs heq
  have hboundary (x : closure D.region) :
      (E x : ℂ) ∈ frontier C.region ↔ (x : ℂ) ∈ frontier D.region := by
    obtain ⟨p, rfl⟩ := hfs x
    rw [hE]
    exact (capParam_frontier C p).trans (capParam_frontier D p).symm
  have hopen : IsOpen D.region := isOpen_graphRegion D.low_continuous D.high_continuous
  have hne : (interior D.region).Nonempty := by
    rw [hopen.interior_eq]
    refine ⟨⟨(C.a + C.b) / 2, (C.b - C.a) / 4⟩, ?_⟩
    change C.a < (C.a + C.b) / 2 ∧ (C.a + C.b) / 2 < C.b ∧
      0 < (C.b - C.a) / 4 ∧
      (C.b - C.a) / 4 < min ((C.a + C.b) / 2 - C.a) (C.b - (C.a + C.b) / 2)
    rw [lt_min_iff]
    have hab := C.ab
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hb : Bornology.IsBounded D.region :=
    isBounded_graphRegion D.low_continuous D.high_continuous (cap_low_le_high D)
  obtain ⟨H, hclosed, hfront⟩ := exists_convex_plane_chart D.region (tentCap_convex C) hne hb
  let K : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure D.region :=
    (H.image _).trans (Homeomorph.setCongr hclosed)
  refine ⟨K.trans E, ?_⟩
  intro z
  change (E (K z) : ℂ) ∈ frontier C.region ↔ _
  rw [hboundary]
  change H (z : ℂ) ∈ frontier D.region ↔ _
  rw [← hfront, H.injective.mem_set_image]
  exact Metric.mem_sphere.trans (by rw [dist_zero_right])

/-- Helper toward Proposition 3.9: each actual glued source face has a
closed-disk chart carrying the unit circle exactly onto its face frontier.
The past faces use the construction's ambient transfer homeomorphism. -/
theorem uibotClassSeparation3_source_face_disk_chart
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ c : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure F.val,
        ∀ z, ((c z : ℂ) ∈ frontier F.val ↔ ‖(z : ℂ)‖ = 1) := by
  intro G M F
  let I := uibotWholePlaneSourceIso W H G hp
  let Fg := I.faceEquiv F
  have hval : Fg.val = F.val := by
    rw [show Fg.val = I.h '' F.val from I.faceEquiv_val F]
    exact Set.image_id _
  have hcap : ∃ (C : GraphCap) (T : ℂ ≃ₜ ℂ), F.val = T '' C.region := by
    rcases WholePlanePastGlueDrawing.glueDrawing_faces W h0 hpast H
      (G.toPlaneGraphDrawingFaceEquiv Fg) with ⟨F0, hb, he⟩ | ⟨Fp, hb, he⟩
    · obtain ⟨n, i, hi⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided
        (shiftedStream W 0) (H.1 0) h0 F0 hb
      refine ⟨(familyG (shiftedStream W 0) (monotone_family_all _) n).cap i,
        Homeomorph.refl ℂ, ?_⟩
      change F.val = id '' _
      rw [Set.image_id]
      exact hval.symm.trans (he.trans hi)
    · obtain ⟨n, i, hi⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided
        (kmswPastCode W) (WholePlanePastGlueData.past_finiteIncidence W H) hpast Fp hb
      refine ⟨(familyG (kmswPastCode W) (monotone_family_all _) n).cap i,
        PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W)
        h0 hpast (H.1 0) (WholePlanePastGlueData.past_finiteIncidence W H), ?_⟩
      exact hval.symm.trans (he.trans (congrArg (fun s => _ '' s) hi))
  obtain ⟨C, T, hF⟩ := hcap
  obtain ⟨c, hc⟩ := uibotClassSeparation3_graphCap_disk_chart C
  have hcl : T '' closure C.region = closure F.val := by rw [T.image_closure, ← hF]
  let E : closure C.region ≃ₜ closure F.val :=
    (T.image _).trans (Homeomorph.setCongr hcl)
  refine ⟨c.trans E, ?_⟩
  intro z
  change T (c z : ℂ) ∈ frontier F.val ↔ _
  rw [hF, ← T.image_frontier, T.injective.mem_set_image]
  exact hc z

/-- Helper toward Proposition 3.9: the closed source faces cover the whole
plane, including vertices and the interiors of all individual geometric edges. -/
theorem uibotClassSeparation3_source_closed_faces_cover
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    (⋃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face, closure F.val) = Set.univ := by
  intro G M
  apply Set.eq_univ_of_forall
  intro z
  have hz : ∃ F : G.Face, z ∈ closure F.val := by
    by_cases him : z ∈ G.image
    · rw [G.image_eq_union_arcs (uibhbot_faceOrbit_dartVertex_surjective W H)] at him
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp him
      obtain ⟨F, hF⟩ := WholePlaneGlueFaceCorrespondenceFull.dart_borders_exists W h0 hpast H d
      exact ⟨F, G.dartBorders_arc_subset_closure
        (uibhbot_faceOrbit_dartVertex_surjective W H) d F hF hd⟩
    · obtain ⟨F, hF⟩ := (G.faces_cover_compl z).mpr him
      exact ⟨F, subset_closure hF⟩
  obtain ⟨F, hzF⟩ := hz
  let I := uibotWholePlaneSourceIso W H G hp
  let Fg := G.toPlaneGraphDrawingFaceEquiv.symm F
  let Fs := I.faceEquiv.symm Fg
  have hval : Fs.val = Fg.val := by
    have h := I.faceEquiv_val Fs
    rw [show I.faceEquiv Fs = Fg from I.faceEquiv.apply_symm_apply Fg] at h
    exact (Set.image_id _).symm.trans h.symm
  refine Set.mem_iUnion.mpr ⟨Fs, ?_⟩
  rw [hval]
  exact hzF

private theorem nearby_bordering_arc
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

private theorem glued_closed_faces_locallyFinite
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W)) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    LocallyFinite (fun F : G.Face => closure F.val) := by
  intro G z
  let d₀ := wholePlaneDartι W 0 (0, false)
  let p₀ := G.pos (wholePlaneDartVertex W d₀)
  let R := dist z p₀ + 5
  have hdarts := G.locally_finite (Metric.ball z R) Metric.isBounded_ball
  have hfinite := hdarts.image (WholePlaneGlueFaceCorrespondenceFull.dartFace W h0 hpast H)
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, hfinite.subset ?_⟩
  rintro F ⟨y, hyF, hyz⟩
  obtain ⟨w, hwF, hyw⟩ := Metric.mem_closure_iff.mp hyF 1 zero_lt_one
  have hwz : dist w z < 2 := by
    have ht := dist_triangle w y z
    rw [dist_comm w y] at ht
    have hyz' := Metric.mem_ball.mp hyz
    linarith only [ht, hyw, hyz']
  obtain ⟨d, x, hxd, hdF, hxw⟩ := nearby_bordering_arc G
    (uibhbot_faceOrbit_dartVertex_surjective W H) d₀ F w hwF
  have hxz : x ∈ Metric.ball z R := by
    have ht := dist_triangle x w z
    have ht' := dist_triangle w z p₀
    change dist x w < dist w p₀ + 1 at hxw
    change dist x z < dist z p₀ + 5
    linarith only [ht, ht', hxw, hwz]
  exact ⟨d, ⟨x, hxz, hxd⟩,
    (WholePlaneGlueFaceCorrespondenceFull.dartFace_eq_iff W h0 hpast H d F).mpr hdF⟩

/-- Helper toward Proposition 3.9: the actual source face closures are
locally finite in the plane. Nearest frontier contacts reduce a neighborhood's
faces to finitely many individual glued darts. -/
theorem uibotClassSeparation3_source_closed_faces_locallyFinite
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    LocallyFinite (fun F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face =>
      closure F.val) := by
  intro G M
  let I := uibotWholePlaneSourceIso W H G hp
  let e := I.faceEquiv.trans G.toPlaneGraphDrawingFaceEquiv
  have he (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) : (e F).val = F.val := by
    change (I.faceEquiv F).val = F.val
    rw [I.faceEquiv_val]
    exact Set.image_id _
  have h := (glued_closed_faces_locallyFinite W H h0 hpast).comp_injective e.injective
  change LocallyFinite (fun F => closure (e F).val) at h
  simpa only [he] using h

/-- Helper toward Proposition 3.9: every source vertex has a finite star
of incident closed faces, with incidence understood as membership in closure. -/
theorem uibotClassSeparation3_source_finite_vertex_star
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ v : WholePlaneVertex W,
      {F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face |
        M.toPlaneMapWithMissing.pos v ∈ closure F.val}.Finite := by
  intro G M v
  exact (uibotClassSeparation3_source_closed_faces_locallyFinite W H h0 hpast hp).point_finite _

/-- Helper toward Proposition 3.9: every prescribed boundary homeomorphism
from a retained source face to its target face extends over the closed faces.
The target chart is obtained from the genuine ambient ball isomorphism. -/
theorem uibotClassSeparation3_retained_face_boundary_extension
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ (r : ℕ) (J : D39GeomBallIsoV2 r M ρ A.map A.root)
      (F : {F // F ∈ d39GeomRetainedFaces M ρ r})
      (f : frontier F.val.val ≃ₜ frontier (J.faceEquiv F).val.val),
      ∃ E : closure F.val.val ≃ₜ closure (J.faceEquiv F).val.val,
        ∀ x : frontier F.val.val,
          (E ⟨x, frontier_subset_closure x.property⟩ : ℂ) = (f x : ℂ) := by
  intro G M ρ r J F f
  obtain ⟨c, hc⟩ := uibotClassSeparation3_source_face_disk_chart W H h0 hpast hp F.val
  have hcl : J.h '' closure F.val.val = closure (J.faceEquiv F).val.val := by
    rw [J.h.image_closure, J.face_image_map F]
  let E : closure F.val.val ≃ₜ closure (J.faceEquiv F).val.val :=
    (J.h.image _).trans (Homeomorph.setCongr hcl)
  let k := c.trans E
  have hk (z : Metric.closedBall (0 : ℂ) 1) :
      (k z : ℂ) ∈ frontier (J.faceEquiv F).val.val ↔ ‖(z : ℂ)‖ = 1 := by
    change J.h (c z : ℂ) ∈ frontier (J.faceEquiv F).val.val ↔ _
    rw [← J.face_image_map F, ← J.h.image_frontier, J.h.injective.mem_set_image]
    exact hc z
  exact exists_disk_homeomorph_extending_boundary
    (closure F.val.val) (frontier F.val.val)
    (closure (J.faceEquiv F).val.val) (frontier (J.faceEquiv F).val.val)
    frontier_subset_closure frontier_subset_closure c k hc hk f

/-- Helper toward Proposition 3.9: all source faces meeting a compact set
are retained simultaneously at one positive radius. In particular this captures
every closed face incident to a given vertex or geometric edge at once. -/
theorem uibotClassSeparation3_source_compact_faces_eventually_retained
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (K : Set ℂ) (hK : IsCompact K) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∃ r : ℕ, 0 < r ∧
      ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        (closure F.val ∩ K).Nonempty → F ∈ d39GeomRetainedFaces M ρ r := by
  classical
  intro G M ρ
  have hfinite :=
    (uibotClassSeparation3_source_closed_faces_locallyFinite W H h0 hpast hp).finite_nonempty_inter_compact hK
  have hex := uibotClassSeparation2_source_face_eventually_retained W H h0 hpast hp
  choose n hnpos hn using hex
  refine ⟨hfinite.toFinset.sup n + 1, Nat.succ_pos _, ?_⟩
  intro F hF v hv
  exact D39GeomBallIsoV2.vertexBall_mono
    ((Finset.le_sup (f := n) (hfinite.mem_toFinset.mpr hF)).trans (Nat.le_succ _))
    (hn F v hv)

/-- Helper toward Proposition 3.9: one global choice of edge parameters
respects every storage flip and agrees with the vertex map at both endpoints.
This supplies endpoint compatibility; face-boundary assembly remains separate. -/
theorem uibotClassSeparation3_compatible_edge_params
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E} {ρ : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {σ : E' × Bool}
    (I : D39CombDartIso M ρ N σ) :
    ∃ p : E → (unitInterval ≃ₜ unitInterval),
      (∀ e, I.flip e = false → StrictMono (p e)) ∧
      (∀ e, I.flip e = true → StrictAnti (p e)) ∧
      (∀ e, N.toPlaneMapWithMissing.arc (I.edgeEquiv e) (p e 0) =
        N.toPlaneMapWithMissing.pos (I.vertexEquiv (M.toPlaneMapWithMissing.src e))) ∧
      (∀ e, N.toPlaneMapWithMissing.arc (I.edgeEquiv e) (p e 1) =
        N.toPlaneMapWithMissing.pos (I.vertexEquiv (M.toPlaneMapWithMissing.tgt e))) := by
  let p : E → (unitInterval ≃ₜ unitInterval) := fun e =>
    if I.flip e then unitInterval.symmHomeomorph else Homeomorph.refl _
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro e he a b hab
    simpa [p, he] using hab
  · intro e he a b hab
    simpa [p, he] using unitInterval.strictAnti_symm hab
  · intro e
    rw [I.src_map e]
    cases he : I.flip e <;> simp [p, he]
  · intro e
    rw [I.tgt_map e]
    cases he : I.flip e <;> simp [p, he]

/-- Helper toward Proposition 3.9: the full source chart-and-cover statement
in step (1), with exact frontier identification and no additional hypotheses. -/
theorem uibotClassSeparation3_source_closed_cell_cover
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    LocallyFinite (fun F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face =>
      closure F.val) ∧
    (⋃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face, closure F.val) = Set.univ ∧
    ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ c : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure F.val,
        ∀ z, ((c z : ℂ) ∈ frontier F.val ↔ ‖(z : ℂ)‖ = 1) := by
  exact ⟨uibotClassSeparation3_source_closed_faces_locallyFinite W H h0 hpast hp,
    uibotClassSeparation3_source_closed_faces_cover W H h0 hpast hp,
    uibotClassSeparation3_source_face_disk_chart W H h0 hpast hp⟩










































































end DirectedDistances.PaperProofs.Section3
end
