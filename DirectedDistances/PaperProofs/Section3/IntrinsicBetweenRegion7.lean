/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57Final
import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmostTransport

/-! # Positive incidence for bands between source rays

These geometric helpers do not remove the intrinsic-object qualifier. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set Filter
open DirectedDistances.PaperProofs.Section5
open scoped Topology

private theorem intrinsicBetween7_leftAtOn_mono {F U : Set ℂ} (hFU : F ⊆ U)
    {x y : ℂ} {γ : Path x y} {s : {t : unitInterval // t ∈ openParams}}
    (hs : LeftAtOn F γ s) : LeftAtOn U γ s := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩ := hs
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, fun t ht => hFU (hq t ht), ?_⟩
  apply closure_mono (s := {w : ℂ | w ∈ F ∧
    HasWinding ((edgeSubarc γ a b (has.trans hsb).le).trans q) w 1}) ?_ hcl
  exact fun _ hz => ⟨hFU hz.1, hz.2⟩

private theorem intrinsicBetween7_face_subset_component
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (M : PLDrawing D V flip rot vert) (F : M.Face)
    {T : Set ℂ} (hT : T ⊆ M.image) {z w : ℂ}
    (hwF : w ∈ F.val) (hwC : w ∈ connectedComponentIn Tᶜ z) :
    F.val ⊆ connectedComponentIn Tᶜ z := by
  have hconn : IsPreconnected F.val := by
    obtain ⟨a, _, heq⟩ := F.property
    rw [heq]
    exact isPreconnected_connectedComponentIn
  rw [connectedComponentIn_eq hwC]
  exact hconn.subset_connectedComponentIn hwF
    (fun a ha ht => M.face_subset_compl F ha (hT ht))

/-- Helper toward Proposition 3.9: a left bordering face supplies every
parameter of the winding test on a lower band boundary. The positive
determinant is proved by moving vertically upward at one open segment
point, using the west-to-east dart orientation. -/
theorem intrinsicBetween7_lower_band_leftAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (M : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : M.Face) (hborder : M.dartBorders d F)
    {T : Set ℂ} (hT : T ⊆ M.image) {z : ℂ}
    {J : Set ℝ} {fP fR : ℝ → ℝ}
    (hC : {w : ℂ | w.re ∈ J ∧ fR w.re < w.im ∧ w.im < fP w.re} ⊆
      connectedComponentIn Tᶜ z)
    {i : ℕ} (hi : i + 1 < (M.arc d).points.length)
    (heast : ((M.arc d).point i).re < ((M.arc d).point (i + 1)).re)
    {q : ℂ} (hq : q ∈ openSegment ℝ ((M.arc d).point i)
      ((M.arc d).point (i + 1)))
    (hqJ : q.re ∈ J) (hqR : q.im = fR q.re) (hgap : fR q.re < fP q.re) :
    ∀ s, LeftAtOn (connectedComponentIn Tᶜ z) (M.arc d).toPath s := by
  obtain ⟨r, hr, hhalf⟩ :=
    M.dartBorders_openSegment_left_halfDisk hvert d F hborder hi q hq
  let δ := min r (fP q.re - fR q.re) / 2
  have hδ : 0 < δ := half_pos (lt_min hr (sub_pos.mpr hgap))
  have hδr : δ < r := by
    have hh := min_le_left r (fP q.re - fR q.re)
    dsimp only [δ]
    linarith only [hh, hr]
  have hδgap : δ < fP q.re - fR q.re := by
    have hh := min_le_right r (fP q.re - fR q.re)
    dsimp only [δ]
    linarith only [hh, hgap]
  let w : ℂ := ⟨q.re, q.im + δ⟩
  have hdist : dist w q = δ := by
    rw [Complex.dist_eq]
    have heq : w - q = (δ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [w]
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
      Complex.norm_I, mul_one]
  have hwF : w ∈ F.val := by
    apply hhalf w (by simpa only [Metric.mem_ball, hdist] using hδr)
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    change 0 < _ * (q.im + δ - q.im) + _ * (q.re - q.re)
    simpa only [add_sub_cancel_left, sub_self, mul_zero, add_zero] using
      mul_pos (sub_pos.mpr heast) hδ
  have hwC : w ∈ connectedComponentIn Tᶜ z := by
    apply hC
    change q.re ∈ J ∧ fR q.re < q.im + δ ∧ q.im + δ < fP q.re
    rw [hqR]
    exact ⟨hqJ, lt_add_of_pos_right _ hδ, by linarith only [hδgap]⟩
  intro s
  exact intrinsicBetween7_leftAtOn_mono
    (intrinsicBetween7_face_subset_component M F hT hwF hwC)
    (M.dartBorders_toPath_leftAtOn hvert d F hborder s)

/-- Helper toward Proposition 3.9: the reversed upper boundary has
positive left incidence on its band. A vertical displacement downward
gives positive determinant for the westward traversal of the upper dart. -/
theorem intrinsicBetween7_upper_band_leftAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (M : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : M.Face) (hborder : M.dartBorders d F)
    {T : Set ℂ} (hT : T ⊆ M.image) {z : ℂ}
    {J : Set ℝ} {fP fR : ℝ → ℝ}
    (hC : {w : ℂ | w.re ∈ J ∧ fR w.re < w.im ∧ w.im < fP w.re} ⊆
      connectedComponentIn Tᶜ z)
    {i : ℕ} (hi : i + 1 < (M.arc d).points.length)
    (hwest : ((M.arc d).point (i + 1)).re < ((M.arc d).point i).re)
    {q : ℂ} (hq : q ∈ openSegment ℝ ((M.arc d).point i)
      ((M.arc d).point (i + 1)))
    (hqJ : q.re ∈ J) (hqP : q.im = fP q.re) (hgap : fR q.re < fP q.re) :
    ∀ s, LeftAtOn (connectedComponentIn Tᶜ z) (M.arc d).toPath s := by
  obtain ⟨r, hr, hhalf⟩ :=
    M.dartBorders_openSegment_left_halfDisk hvert d F hborder hi q hq
  let δ := min r (fP q.re - fR q.re) / 2
  have hδ : 0 < δ := half_pos (lt_min hr (sub_pos.mpr hgap))
  have hδr : δ < r := by
    have hh := min_le_left r (fP q.re - fR q.re)
    dsimp only [δ]
    linarith only [hh, hr]
  have hδgap : δ < fP q.re - fR q.re := by
    have hh := min_le_right r (fP q.re - fR q.re)
    dsimp only [δ]
    linarith only [hh, hgap]
  let w : ℂ := ⟨q.re, q.im - δ⟩
  have hdist : dist w q = δ := by
    rw [Complex.dist_eq]
    have heq : w - q = (-δ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [w]
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
      Complex.norm_I, mul_one]
  have hwF : w ∈ F.val := by
    apply hhalf w (by simpa only [Metric.mem_ball, hdist] using hδr)
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    change 0 < _ * (q.im - δ - q.im) + _ * (q.re - q.re)
    have hp := mul_pos (sub_pos.mpr hwest) hδ
    nlinarith only [hp]
  have hwC : w ∈ connectedComponentIn Tᶜ z := by
    apply hC
    change q.re ∈ J ∧ fR q.re < q.im - δ ∧ q.im - δ < fP q.re
    rw [hqP]
    exact ⟨hqJ, by linarith only [hδgap], sub_lt_self _ hδ⟩
  intro s
  exact intrinsicBetween7_leftAtOn_mono
    (intrinsicBetween7_face_subset_component M F hT hwF hwC)
    (M.dartBorders_toPath_leftAtOn hvert d F hborder s)

/-- Helper toward Proposition 3.9: an arc meeting an open set of
abscissas has an open segment point with abscissa in that set. This
avoids imposing a nonvertex condition on a source boundary point. -/
theorem intrinsicBetween7_exists_openSegment_in_open_abscissas
    (p : Polyline) (hlen : 2 ≤ p.points.length) {J : Set ℝ}
    (hJ : IsOpen J) {q : ℂ} (hq : q ∈ p.image) (hqJ : q.re ∈ J) :
    ∃ (i : ℕ) (_ : i + 1 < p.points.length) (w : ℂ),
      w ∈ openSegment ℝ (p.point i) (p.point (i + 1)) ∧ w.re ∈ J := by
  have hseg : ∃ (i : ℕ) (_ : i + 1 < p.points.length),
      q ∈ segment ℝ (p.point i) (p.point (i + 1)) := by
    rcases hq with hq | ⟨i, hi, hqi⟩
    · refine ⟨0, by omega, ?_⟩
      change q = p.start at hq
      rw [hq, ← p.point_zero_eq_start]
      exact left_mem_segment ℝ _ _
    · exact ⟨i, hi, hqi⟩
  obtain ⟨i, hi, hqi⟩ := hseg
  have hcl := (segment_subset_closure_openSegment (𝕜 := ℝ)) hqi
  obtain ⟨w, hwJ, hwseg⟩ := mem_closure_iff.mp hcl
    (Complex.re ⁻¹' J) (hJ.preimage Complex.continuous_re) hqJ
  exact ⟨i, hi, w, hwseg, hwJ⟩

/-- Helper toward Proposition 3.9: the common-domain positive gap set
is open even when the two proper graph rays have different finite
limiting abscissas. -/
theorem intrinsicBetween7_isOpen_gap
    {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR)) :
    IsOpen {x : ℝ | x₀ < x ∧ x ∈ rayDomain x₀ XP ∧
      x ∈ rayDomain x₀ XR ∧ fR x < fP x} := by
  let U : Set ℝ := {x | x₀ < x ∧ (x : WithTop ℝ) < XP ∧ (x : WithTop ℝ) < XR}
  have hopen (X : WithTop ℝ) : IsOpen {x : ℝ | (x : WithTop ℝ) < X} := by
    induction X using WithTop.recTopCoe with
    | top => simp only [WithTop.coe_lt_top, ofPred_true]; exact isOpen_univ
    | coe b =>
      simp only [WithTop.coe_lt_coe]
      exact isOpen_lt continuous_id continuous_const
  have hU : IsOpen U := isOpen_Ioi.inter ((hopen XP).inter (hopen XR))
  have hdomP : U ⊆ rayDomain x₀ XP := fun _ hx => ⟨hx.1.le, hx.2.1⟩
  have hdomR : U ⊆ rayDomain x₀ XR := fun _ hx => ⟨hx.1.le, hx.2.2⟩
  have hh := ((hcR.mono hdomR).prodMk (hcP.mono hdomP)).isOpen_inter_preimage hU
    (isOpen_lt continuous_fst continuous_snd : IsOpen {p : ℝ × ℝ | p.1 < p.2})
  convert hh using 1
  ext x
  change (_ ∧ _ ∧ _ ∧ _) ↔ ((x₀ < x ∧ _ ∧ _) ∧ _)
  constructor
  · rintro ⟨hx, hp, hr, hg⟩
    exact ⟨⟨hx, hp.2, hr.2⟩, hg⟩
  · rintro ⟨⟨hx, hp, hr⟩, hg⟩
    exact ⟨hx, ⟨hx.le, hp⟩, ⟨hx.le, hr⟩, hg⟩

private theorem intrinsicBetween7_source_band_side
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (Q : InfinitePresentPath (shiftedStream W 0) v)
    (T : Set ℂ) (z : ℂ) (J : Set ℝ) (hJ : IsOpen J)
    (fP fR : ℝ → ℝ) (upper : Bool)
    (hT : T ⊆ (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).image)
    (hband : {w : ℂ | w.re ∈ J ∧ fR w.re < w.im ∧ w.im < fP w.re} ⊆
      connectedComponentIn Tᶜ z)
    (hgap : ∀ x ∈ J, fR x < fP x)
    (hgraph : ∀ x ∈ J, (⟨x, if upper then fP x else fR x⟩ : ℂ) ∈
      intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (Q.edge n)))
    (hheight : ∀ w ∈ intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (Q.edge n)),
      w.re ∈ J → w.im = if upper then fP w.re else fR w.re)
    (x : ℝ) (hx : x ∈ J) :
    intrinsicRayTouchesSide (uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (Q.edge n))
      (connectedComponentIn Tᶜ z) upper := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hpath := hgraph x hx
  rw [intrinsicGeodesicSource_trace W H G hp] at hpath
  obtain ⟨n, hn⟩ := mem_iUnion.mp hpath
  change (⟨x, if upper then fP x else fR x⟩ : ℂ) ∈
    (G.arc (wholePlaneDartι W 0 (Q.edge n, false))).image at hn
  rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H] at hn
  let d := (Q.edge n, upper)
  have harc : G.arc (wholePlaneDartι W 0 d) = M.arc d :=
    WholePlanePastGlueM0Restriction.restrict_arc W h hpast H d
  have himage : (M.arc d).image = (M.arc (Q.edge n, false)).image := by
    cases upper
    · rfl
    · rw [show M.arc (Q.edge n, true) = (M.arc (Q.edge n, false)).reverse from
        M.arc_flip (Q.edge n, false), Polyline.image_reverse_transfer]
  have hn' : (⟨x, if upper then fP x else fR x⟩ : ℂ) ∈ (M.arc d).image := by
    rw [himage]
    exact hn
  obtain ⟨i, hi, q, hq, hqJ⟩ :=
    intrinsicBetween7_exists_openSegment_in_open_abscissas
      (M.arc d) (M.arc_length d) hJ hn' hx
  have hqtrace : q ∈ intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H G hp)
      (fun n => wholePlaneEdgeι W 0 (Q.edge n)) := by
    rw [intrinsicGeodesicSource_trace W H G hp]
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change q ∈ (G.arc (wholePlaneDartι W 0 (Q.edge n, false))).image
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H]
    rw [← himage]
    exact Or.inr ⟨i, hi, openSegment_subset_segment ℝ _ _ hq⟩
  have hqheight := hheight q hqtrace hqJ
  let F := futureMapDartFace W H h d
  have hb : M.dartBorders d F := (futureMap_dart_face_eq_iff W H h d F).mp rfl
  have hmono : (M.arc (Q.edge n, false)).XMonotone :=
    infinitePresentPath_arc_xMonotone (H.1 0)
      (fun j => ⟨monotoneLayoutDrawing (shiftedStream W 0) j
        ((monotone_family_all (shiftedStream W 0)) j).choose,
        ((monotone_family_all (shiftedStream W 0)) j).choose_spec⟩) Q n
  apply (intrinsicBetween_source_ray_touches_side_iff W H h hpast hp Q _ upper).mpr
  refine ⟨n, ?_⟩
  rw [harc]
  cases upper
  · exact intrinsicBetween7_lower_band_leftAtOn M
      (kmswLimitDartVertex_surjective _ (H.1 0)) d F hb hT hband hi
      (Polyline.point_re_lt hmono (by omega) hi) hq hqJ hqheight (hgap q.re hqJ)
  · have hrev : M.arc d = (M.arc (Q.edge n, false)).reverse :=
      M.arc_flip (Q.edge n, false)
    have hlen : (M.arc d).points.length = (M.arc (Q.edge n, false)).points.length := by
      rw [hrev]
      exact List.length_reverse
    have hwest : ((M.arc d).point (i + 1)).re < ((M.arc d).point i).re := by
      rw [hrev, Polyline.point_reverse_transfer _ (by omega),
        Polyline.point_reverse_transfer _ (by omega)]
      exact Polyline.point_re_lt hmono (by omega) (by omega)
    exact intrinsicBetween7_upper_band_leftAtOn M
      (kmswLimitDartVertex_surjective _ (H.1 0)) d F hb hT hband hi
      hwest hq hqJ hqheight (hgap q.re hqJ)

/-- Helper toward Proposition 3.9: every source complementary component
meeting the strict band on the common graph domain has positive right
incidence on the upper ray and positive left incidence on the lower ray.
The two limiting abscissas may differ; points beyond the upper endpoint
are a separate obligation. -/
theorem intrinsicBetween7_source_component_positive_on_common_domain
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P R : InfinitePresentPath (shiftedStream W 0) v)
    {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (P.edge n)) =
      {w : ℂ | w.re ∈ rayDomain x₀ XP ∧ w.im = fP w.re})
    (hR : intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (R.edge n)) =
      {w : ℂ | w.re ∈ rayDomain x₀ XR ∧ w.im = fR w.re})
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    {z : ℂ} (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ XP ∧
      z.re ∈ rayDomain x₀ XR ∧ fR z.re < z.im ∧ z.im < fP z.re) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
    let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
    let C := connectedComponentIn (intrinsicEdgeRayTrace A pe ∪
      intrinsicEdgeRayTrace A re)ᶜ z
    intrinsicRayTouchesSide A pe C true ∧ intrinsicRayTouchesSide A re C false := by
  dsimp only
  let A := uibotWholePlaneSourceDomain W H
    (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
  let PT := intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (P.edge n))
  let RT := intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (R.edge n))
  let T := PT ∪ RT
  let K : Set ℝ := {x | x₀ < x ∧ x ∈ rayDomain x₀ XP ∧
    x ∈ rayDomain x₀ XR ∧ fR x < fP x}
  let J := connectedComponentIn K z.re
  have hzK : z.re ∈ K := ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1.trans hz.2.2.2.2⟩
  have hJ : IsOpen J := (intrinsicBetween7_isOpen_gap hcP hcR).connectedComponentIn
  have hsub : J ⊆ K := connectedComponentIn_subset K z.re
  have hg : ∀ x ∈ J, fR x < fP x := fun _ hx => (hsub hx).2.2.2
  have hband : {w : ℂ | w.re ∈ J ∧ fR w.re < w.im ∧ w.im < fP w.re} ⊆
      connectedComponentIn Tᶜ z := by
    apply (intrinsicBetween5_isPreconnected_band isPreconnected_connectedComponentIn
      (hcP.mono (fun _ hx => (hsub hx).2.1))
      (hcR.mono (fun _ hx => (hsub hx).2.2.1)) hg).subset_connectedComponentIn
      ⟨mem_connectedComponentIn hzK, hz.2.2.2⟩
    rintro w ⟨hw, hlo, hhi⟩
    change w ∉ PT ∪ RT
    rw [show PT = _ from hP, show RT = _ from hR]
    rintro (⟨_, he⟩ | ⟨_, he⟩)
    · exact hhi.ne he
    · exact hlo.ne' he
  have hT : T ⊆ (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).image := by
    have hQ (Q : InfinitePresentPath (shiftedStream W 0) v) :
        intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (Q.edge n)) ⊆
        (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
          (monotone_family_all (shiftedStream W 0))).image := by
      rw [intrinsicGeodesicSource_trace W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp]
      intro w hw
      obtain ⟨n, hn⟩ := mem_iUnion.mp hw
      change w ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hpast H).arc
        (wholePlaneDartι W 0 (Q.edge n, false))).image at hn
      rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H] at hn
      exact Or.inr ⟨(Q.edge n, false), hn⟩
    exact union_subset (hQ P) (hQ R)
  constructor
  · apply intrinsicBetween7_source_band_side W H h hpast hp P T z J hJ fP fR true
      hT hband hg
    · intro x hx
      rw [hP]
      exact ⟨(hsub hx).2.1, rfl⟩
    · intro w hw _
      exact (hP ▸ hw).2
    · exact mem_connectedComponentIn hzK
  · apply intrinsicBetween7_source_band_side W H h hpast hp R T z J hJ fP fR false
      hT hband hg
    · intro x hx
      rw [hR]
      exact ⟨(hsub hx).2.2.1, rfl⟩
    · intro w hw _
      exact (hR ▸ hw).2
    · exact mem_connectedComponentIn hzK

/-- Helper toward Proposition 3.9: a strict-region component beyond a
finite upper endpoint also meets the common domain. A horizontal segment
above a compact lower graph and below the escaping upper graph, followed
by a vertical segment, supplies the connection. -/
theorem intrinsicBetween7_component_meets_common_domain
    {PT RT : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : PT = {w : ℂ | w.re ∈ rayDomain x₀ XP ∧ w.im = fP w.re})
    (hR : RT = {w : ℂ | w.re ∈ rayDomain x₀ XR ∧ w.im = fR w.re})
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    {z : ℂ} (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)) :
    ∃ w ∈ connectedComponentIn (PT ∪ RT)ᶜ z,
      x₀ < w.re ∧ w.re ∈ rayDomain x₀ XP ∧ w.re ∈ rayDomain x₀ XR ∧
      fR w.re < w.im ∧ w.im < fP w.re := by
  by_cases hzP : z.re ∈ rayDomain x₀ XP
  · refine ⟨z, mem_connectedComponentIn ?_, hz.1, hzP, hz.2.1, hz.2.2.1, hz.2.2.2 hzP⟩
    rw [hP, hR]
    rintro (⟨_, he⟩ | ⟨_, he⟩)
    · exact (hz.2.2.2 hzP).ne he
    · exact hz.2.2.1.ne' he
  induction XP using WithTop.recTopCoe with
  | top => exact False.elim (hzP ⟨hz.1.le, WithTop.coe_lt_top _⟩)
  | coe b =>
    have hbz : b ≤ z.re := le_of_not_gt (fun hb => hzP ⟨hz.1.le, WithTop.coe_lt_coe.mpr hb⟩)
    have hdomR : Icc x₀ z.re ⊆ rayDomain x₀ XR :=
      fun _ ht => ⟨ht.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht.2) hz.2.1.2⟩
    obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image (hcR.mono hdomR)
    have hbound (t : ℝ) (ht : t ∈ Icc x₀ z.re) : fR t ≤ M :=
      hM (mem_image_of_mem fR ht)
    obtain ⟨a₀, ha₀, hbig⟩ := hescP (M + 2)
    have ha₀b : a₀ < b := WithTop.coe_lt_coe.mp ha₀.2
    let a := (a₀ + b) / 2
    have ha₀a : a₀ < a := by dsimp only [a]; linarith only [ha₀b]
    have hab : a < b := by dsimp only [a]; linarith only [ha₀b]
    have hxa : x₀ < a := ha₀.1.trans_lt ha₀a
    have haz : a < z.re := hab.trans_le hbz
    let w : ℂ := ⟨a, M + 1⟩
    let u : ℂ := ⟨z.re, M + 1⟩
    have hwstrict : x₀ < w.re ∧ w.re ∈ rayDomain x₀ (b : WithTop ℝ) ∧
        w.re ∈ rayDomain x₀ XR ∧ fR w.re < w.im ∧ w.im < fP w.re := by
      have hd : a ∈ rayDomain x₀ (b : WithTop ℝ) := ⟨hxa.le, WithTop.coe_lt_coe.mpr hab⟩
      have hlo := hbound a ⟨hxa.le, haz.le⟩
      have hhi := hbig a hd ha₀a.le
      exact ⟨hxa, hd, hdomR ⟨hxa.le, haz.le⟩, by change fR a < M + 1; linarith,
        by change M + 1 < fP a; linarith⟩
    have hsafeH : segment ℝ w u ⊆ (PT ∪ RT)ᶜ := by
      intro q hq
      have hbox := ((convex_halfSpace_re_ge a).inter
        ((convex_halfSpace_re_le z.re).inter
          ((convex_halfSpace_im_ge (M + 1)).inter (convex_halfSpace_im_le (M + 1))))).segment_subset
        (show w.re ∈ Ici a ∧ w.re ≤ z.re ∧ M + 1 ≤ w.im ∧ w.im ≤ M + 1 from
          ⟨le_rfl, haz.le, le_rfl, le_rfl⟩)
        (show a ≤ u.re ∧ u.re ≤ z.re ∧ M + 1 ≤ u.im ∧ u.im ≤ M + 1 from
          ⟨haz.le, le_rfl, le_rfl, le_rfl⟩) hq
      have hqi : q.im = M + 1 := le_antisymm hbox.2.2.2 hbox.2.2.1
      have hqr := hbound q.re ⟨hxa.le.trans hbox.1, hbox.2.1⟩
      rw [hP, hR]
      rintro (⟨hd, he⟩ | ⟨_, he⟩)
      · have hp := hbig q.re hd (ha₀a.le.trans hbox.1)
        linarith only [hp, he, hqi]
      · linarith only [hqr, he, hqi]
    have hsafeV : segment ℝ u z ⊆ (PT ∪ RT)ᶜ := by
      intro q hq
      have hlo : fR z.re < M + 1 := by
        have hh := hbound z.re ⟨hz.1.le, le_rfl⟩
        linarith only [hh]
      have hbox := ((convex_halfSpace_re_ge z.re).inter
        ((convex_halfSpace_re_le z.re).inter (convex_halfSpace_im_gt (fR z.re)))).segment_subset
        (show z.re ≤ u.re ∧ u.re ≤ z.re ∧ fR z.re < u.im from
          ⟨le_rfl, le_rfl, hlo⟩)
        (show z.re ≤ z.re ∧ z.re ≤ z.re ∧ fR z.re < z.im from
          ⟨le_rfl, le_rfl, hz.2.2.1⟩) hq
      have hqr : q.re = z.re := le_antisymm hbox.2.1 hbox.1
      rw [hP, hR]
      rintro (⟨hd, _⟩ | ⟨_, he⟩)
      · exact hzP (hqr ▸ hd)
      · exact hbox.2.2.ne' (he.trans (congrArg fR hqr))
    have hconn : IsPreconnected (segment ℝ w u ∪ segment ℝ u z) :=
      (convex_segment w u).isPreconnected.union u
        (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
        (convex_segment u z).isPreconnected
    have hsub := hconn.subset_connectedComponentIn
      (Or.inr (right_mem_segment ℝ u z)) (union_subset hsafeH hsafeV)
    exact ⟨w, hsub (Or.inl (left_mem_segment ℝ w u)), hwstrict⟩

/-- Helper toward Proposition 3.9: every actual source complementary
component meeting the vertical-fiber region off its traces has positive
right incidence on its upper ray and positive left incidence on its lower
ray. Finite and unequal limiting abscissas are included. -/
theorem intrinsicBetween7_source_region_component_positive
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P R : InfinitePresentPath (shiftedStream W 0) v) (z : ℂ) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
    let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
    let PT := intrinsicEdgeRayTrace A pe
    let RT := intrinsicEdgeRayTrace A re
    z ∈ closedBetween PT RT \ (PT ∪ RT) →
    let C := connectedComponentIn (PT ∪ RT)ᶜ z
    intrinsicRayTouchesSide A pe C true ∧ intrinsicRayTouchesSide A re C false := by
  dsimp only
  intro hz
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hwest (Q : InfinitePresentPath (shiftedStream W 0) v) :
      edgeWest (shiftedStream W 0) (Q.edge 0) = v.id := by
    have hzero := (Q.initial 0).2.eq_of_length_zero (Q.prefix_length 0)
    exact (Q.edge_outgoing_at_initial (shiftedStream W 0) 0).2.trans
      (congrArg PresentVertex.id hzero.symm)
  have hstartarc : (M.arc (P.edge 0, false)).start =
      (M.arc (R.edge 0, false)).start := by
    rw [M.arc_start, M.arc_start]
    change M.pos (edgeWest (shiftedStream W 0) (P.edge 0)) =
      M.pos (edgeWest (shiftedStream W 0) (R.edge 0))
    rw [hwest P, hwest R]
  have hproperP := intrinsicBetween_source_trace_properGraphRay W H h hpast hp P
  have hproperR := intrinsicBetween_source_trace_properGraphRay W H h hpast hp R
  change ProperGraphRay _ (M.arc (P.edge 0, false)).start.re at hproperP
  change ProperGraphRay _ (M.arc (R.edge 0, false)).start.re at hproperR
  rw [← hstartarc] at hproperR
  obtain ⟨XP, fP, hXP, hcP, hP, hescP⟩ := hproperP
  obtain ⟨XR, fR, _hXR, hcR, hR, _hescR⟩ := hproperR
  have hmem (Q : InfinitePresentPath (shiftedStream W 0) v) :
      (M.arc (Q.edge 0, false)).start ∈ intrinsicEdgeRayTrace
        (uibotWholePlaneSourceDomain W H G hp)
        (fun n => wholePlaneEdgeι W 0 (Q.edge n)) := by
    rw [intrinsicGeodesicSource_trace W H G hp]
    apply mem_iUnion.mpr
    refine ⟨0, ?_⟩
    change (M.arc (Q.edge 0, false)).start ∈
      (G.arc (wholePlaneDartι W 0 (Q.edge 0, false))).image
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H]
    exact Or.inl rfl
  have hpmem := hmem P
  have hrmem := hmem R
  rw [hP] at hpmem
  rw [hR, ← hstartarc] at hrmem
  have hstart : fP (M.arc (P.edge 0, false)).start.re =
      fR (M.arc (P.edge 0, false)).start.re := hpmem.2.symm.trans hrmem.2
  have hstrict := intrinsicBetween5_closedBetween_diff_traces hP hR hXP hstart
  obtain ⟨w, hwC, hw⟩ := intrinsicBetween7_component_meets_common_domain
    hP hR hcR hescP (hstrict ▸ hz)
  have hpos := intrinsicBetween7_source_component_positive_on_common_domain
    W H h hpast hp P R hP hR hcP hcR hw
  dsimp only at hpos
  rw [← connectedComponentIn_eq hwC] at hpos
  exact hpos

private theorem intrinsicBetween7_source_between_isClosed
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P R : InfinitePresentPath (shiftedStream W 0) v) :
    IsClosed (closedBetween
      (intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (P.edge n)))
      (intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (R.edge n)))) := by
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hproper (Q : InfinitePresentPath (shiftedStream W 0) v) :
      ProperGraphRay (intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
        (fun n => wholePlaneEdgeι W 0 (Q.edge n))) (M.pos v.id).re := by
    have hh := intrinsicBetween_source_trace_properGraphRay W H h hpast hp Q
    change ProperGraphRay _ (M.arc (Q.edge 0, false)).start.re at hh
    have hzero := (Q.initial 0).2.eq_of_length_zero (Q.prefix_length 0)
    have hw := (Q.edge_outgoing_at_initial (shiftedStream W 0) 0).2.trans
      (congrArg PresentVertex.id hzero.symm)
    rw [M.arc_start] at hh
    change ProperGraphRay _ (M.pos (edgeWest (shiftedStream W 0) (Q.edge 0))).re at hh
    rwa [hw] at hh
  exact isClosed_closedBetween (hproper P) (hproper R)





theorem intrinsicBetween7_source_native_eq_between_union_traces
    (hExterior : ∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
      (h : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
      (v : PresentVertex (shiftedStream W 0))
      (P R : InfinitePresentPath (shiftedStream W 0) v) (z : ℂ),
      let A := uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
      let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
      let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
      let PT := intrinsicEdgeRayTrace A pe
      let RT := intrinsicEdgeRayTrace A re
      z ∉ PT ∪ RT →
      let C := connectedComponentIn (PT ∪ RT)ᶜ z
      intrinsicRayTouchesSide A pe C true → intrinsicRayTouchesSide A re C false →
      ¬ intrinsicRayTouchesSide A pe C false → ¬ intrinsicRayTouchesSide A re C true →
      z ∈ closedBetween PT RT)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P R : InfinitePresentPath (shiftedStream W 0) v) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
    let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
    let PT := intrinsicEdgeRayTrace A pe
    let RT := intrinsicEdgeRayTrace A re
    nativeBetween A pe re = closedBetween PT RT ∪ (PT ∪ RT) := by
  dsimp only
  let A := uibotWholePlaneSourceDomain W H
    (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
  let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
  let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
  let PT := intrinsicEdgeRayTrace A pe
  let RT := intrinsicEdgeRayTrace A re
  have hclosed := (intrinsicBetween7_source_between_isClosed W H h hpast hp P R).union
    ((intrinsicBetween_source_trace_isClosed W H h hpast hp P).union
      (intrinsicBetween_source_trace_isClosed W H h hpast hp R))
  apply subset_antisymm
  · apply closure_minimal ?_ hclosed
    rintro z (⟨w, hw, hzC, hPr, hRl, hnPl, hnRr⟩ | hz)
    · have hznot : z ∉ PT ∪ RT := connectedComponentIn_subset _ _ hzC
      have heq := connectedComponentIn_eq hzC
      rw [heq] at hPr hRl hnPl hnRr
      exact Or.inl (hExterior W H h hpast hp v P R z hznot hPr hRl hnPl hnRr)
    · exact Or.inr hz
  · rintro z (hz | hz)
    · by_cases ht : z ∈ PT ∪ RT
      · exact subset_closure (Or.inr ht)
      · have hpos := intrinsicBetween7_source_region_component_positive W H h hpast hp P R z ⟨hz, ht⟩
        have hneg := intrinsicConsumersFinal_source_region_component_wrong_sides W H h hpast hp P R z ⟨hz, ht⟩
        exact subset_closure (Or.inl ⟨z, ht, mem_connectedComponentIn ht,
          hpos.1, hpos.2, hneg.1, hneg.2⟩)
    · exact subset_closure (Or.inr hz)

/-- Helper toward Proposition 3.9: both complete source traces lie in
the upper-first vertical-fiber region when the second source path is
rightmost at every departure. This uses the proved angular comparison,
including its endpoint-domain containment. -/
theorem intrinsicBetween7_source_traces_subset_between_of_rightmost
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P T : InfinitePresentPath (shiftedStream W 0) v)
    (hmost : ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
      (T.initial n).1.id (T.edge n)) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    let PT := intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (P.edge n))
    let RT := intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (T.edge n))
    PT ∪ RT ⊆ closedBetween PT RT := by
  dsimp only
  let fam : ∀ n, ∃ Q : StageDrawing (shiftedStream W 0) n,
      Nonempty (MonotoneStageInvariant (shiftedStream W 0) n Q) :=
    fun n => ⟨monotoneLayoutDrawing (shiftedStream W 0) n
    ((monotone_family_all (shiftedStream W 0)) n).choose,
    ((monotone_family_all (shiftedStream W 0)) n).choose_spec⟩
  let M := monotoneLimitDrawing (shiftedStream W 0) (H.1 0) fam
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  have htrace (Q : InfinitePresentPath (shiftedStream W 0) v) :
      intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H G hp)
        (fun n => wholePlaneEdgeι W 0 (Q.edge n)) =
      pathTrace M (fun n => (Q.edge n, false)) := by
    rw [intrinsicGeodesicSource_trace W H G hp]
    change pathTrace G (fun n => wholePlaneDartι W 0 (Q.edge n, false)) = _
    exact m0Cut_pathTrace_eq W H h hpast Q.edge
  rw [htrace P, htrace T]
  have hself (Q : InfinitePresentPath (shiftedStream W 0) v) :
      LeftmostTransport.SharedDepartureArgRightOf (shiftedStream W 0) (H.1 0) fam Q Q := by
    intro i j hs
    have hij : i = j := by
      apply infinitePresentPath_west_injective (H.1 0) fam Q
      change edgeWest (shiftedStream W 0) (Q.edge i) =
        edgeWest (shiftedStream W 0) (Q.edge j)
      rw [(Q.edge_outgoing_at_initial (shiftedStream W 0) i).2,
        (Q.edge_outgoing_at_initial (shiftedStream W 0) j).2]
      exact congrArg PresentVertex.id hs
    subst j
    exact le_rfl
  have hright := LeftmostTransport.sharedDepartureArgRightOf_rightmost
    (shiftedStream W 0) (H.1 0) fam h P T hmost
  exact union_subset
    (LeftmostTransport.trace_subset_closedBetween_of_departureArgs
      (shiftedStream W 0) (H.1 0) fam v.id P T P ⟨hself P, hright⟩)
    (LeftmostTransport.trace_subset_closedBetween_of_departureArgs
      (shiftedStream W 0) (H.1 0) fam v.id P T T ⟨hright, hself T⟩)

/-- Helper toward Proposition 3.9: native-region equality in every
representative, conditional only on the named exterior-exclusion lemma
with precisely the source binders recorded at the previous file's line 397.
This conditional theorem does not discharge that exterior obligation. -/
theorem intrinsicBetween7_native_eq_closedBetween
    (hExterior : ∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
      (h : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
      (v : PresentVertex (shiftedStream W 0))
      (P R : InfinitePresentPath (shiftedStream W 0) v) (z : ℂ),
      let A := uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
      let pe := fun n => wholePlaneEdgeι W 0 (P.edge n)
      let re := fun n => wholePlaneEdgeι W 0 (R.edge n)
      let PT := intrinsicEdgeRayTrace A pe
      let RT := intrinsicEdgeRayTrace A re
      z ∉ PT ∪ RT →
      let C := connectedComponentIn (PT ∪ RT)ᶜ z
      intrinsicRayTouchesSide A pe C true → intrinsicRayTouchesSide A re C false →
      ¬ intrinsicRayTouchesSide A pe C false → ¬ intrinsicRayTouchesSide A re C true →
      z ∈ closedBetween PT RT)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ (I : D39GeomRootedMapIsoV2
        (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
        A.map A.root)
      (longest : Bool) (k : ℤ)
      (P : M0CutInfiniteGeodesic W H h hLL k longest)
      (T : InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k))
      (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
      (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
      (_ : T.edge = R.edge),
    nativeBetween A
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) =
    I.h '' closedBetween
      (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
      (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))) := by
  dsimp only
  intro I longest k P T R _hstart hedge
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let S := uibotWholePlaneSourceDomain W H G hp
  let pe := fun n => wholePlaneEdgeι W 0 (P.codePath.edge n)
  let re := fun n => wholePlaneEdgeι W 0 (T.edge n)
  have hmost : ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
      (T.initial n).1.id (T.edge n) := by
    intro n
    have he := R.rightmost n
    rw [← hedge] at he
    have hv : R.vertex n = (T.initial n).1.id :=
      he.2.1.symm.trans (T.edge_outgoing_at_initial (shiftedStream W 0) n).2
    exact hv ▸ he
  have hboundary := intrinsicBetween7_source_traces_subset_between_of_rightmost
    W H h hpast hp P.codePath T hmost
  have hsource := intrinsicBetween7_source_native_eq_between_union_traces
    hExterior W H h hpast hp P.codePath T
  dsimp only at hboundary hsource
  rw [union_eq_self_of_subset_right hboundary] at hsource
  calc
    _ = I.h '' nativeBetween S pe re := (nativeBetween_map (A := S) (B := A) I pe re).symm
    _ = I.h '' closedBetween (intrinsicEdgeRayTrace S pe) (intrinsicEdgeRayTrace S re) :=
      congrArg (fun U : Set ℂ => I.h '' U) hsource
    _ = _ := congrArg (fun U : Set ℂ => I.h '' U)
      (congrArg₂ closedBetween (intrinsicGeodesicSource_trace W H G hp pe)
        (intrinsicGeodesicSource_trace W H G hp re))




























end DirectedDistances.PaperProofs.Section3
end
