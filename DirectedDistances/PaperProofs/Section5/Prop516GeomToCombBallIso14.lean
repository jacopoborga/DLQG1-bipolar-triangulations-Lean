/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso13

/-! Helper toward Proposition 5.16. This file proves nonconstancy of positive
proper dart-arc prefixes and the shrinking radial-segment comparison for
continuous injective arc parametrizations. The full-star rotation comparison
is retained below with its exact binders. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. An injective path has nonconstant image
on every prefix with positive endpoint. -/
theorem d39_injective_path_prefix_nonconstant
    {α : Type*} (f : I → α) (hf : Function.Injective f)
    {c : I} (hc : 0 < (c : ℝ)) :
    ∃ t ∈ Set.Icc (0 : I) c, f t ≠ f 0 := by
  have hcI : (0 : I) < c := by exact_mod_cast hc
  refine ⟨c, ⟨hcI.le, le_rfl⟩, ?_⟩
  intro h
  exact (ne_of_gt hcI) (hf h)

/-- Helper toward Proposition 5.16. In a PL drawing, a dart arc cannot return
to its initial vertex at an interior parameter, so every positive proper
prefix has a value different from its start. The open-arc injectivity and
vertex-avoidance fields preserve this conclusion for loop edges as well. -/
theorem d39DrawingDartArc_prefix_nonconstant
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (d : M.core.D)
    {c : I} (hc0 : 0 < (c : ℝ)) (hc1 : (c : ℝ) < 1) :
    d39DrawingDartArc B x.toD39DrawingRepresentationData d c ≠
      d39DrawingDartArc B x.toD39DrawingRepresentationData d 0 := by
  let D := B.map.toPlaneMapWithMissing.toPlaneGraphDrawing
  let a := (x.dartEquiv d).1
  have hopen (t : I) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
      t ∈ openParams := ⟨ht0, ht1⟩
  by_cases hb : (x.dartEquiv d).2
  · have hcopen : c ∈ openParams := hopen c hc0 hc1
    unfold d39DrawingDartArc
    rw [hb]
    change D.arc a c ≠ D.arc a 0
    intro heq
    have hstart : D.arc a 0 = D.pos (D.src a) := by simp
    have hmem : D.pos (D.src a) ∈ D.arc a '' openParams :=
      ⟨c, hcopen, heq.trans hstart⟩
    exact D.openArc_avoids a (D.src a) hmem
  · have hcopen : c ∈ openParams := hopen c hc0 hc1
    have hc' : unitInterval.symm c ∈ openParams :=
      symm_mem_openParams_iff.mpr hcopen
    unfold d39DrawingDartArc
    rw [if_neg hb]
    change (D.arc a).symm c ≠ (D.arc a).symm 0
    intro heq
    have hstart : (D.arc a).symm 0 = D.pos (D.tgt a) := by simp
    have hmem : D.pos (D.tgt a) ∈ D.arc a '' openParams :=
      ⟨unitInterval.symm c, hc', by simpa using heq.trans hstart⟩
    exact D.openArc_avoids a (D.tgt a) hmem

/-- Helper toward Proposition 5.16. Every represented dart arc is continuous,
including when its parameter direction reverses the stored edge path. -/
theorem d39DrawingDartArc_continuous
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (d : M.core.D) :
    Continuous (d39DrawingDartArc B x.toD39DrawingRepresentationData d) := by
  unfold d39DrawingDartArc
  split <;> fun_prop

/-- Helper toward Proposition 5.16. If a plane homeomorphism straightens a
common set and a second homeomorphism straightens its image under another
homeomorphism, their composite maps the first radial segment exactly to the
second, with the radii retained. -/
theorem d39_composite_straightener_maps_matched_radial_segments
    {A B : Set ℂ} (H K R : ℂ ≃ₜ ℂ)
    (u v : ℂ) (r s : ℝ)
    (hA : H '' A = {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u})
    (hB : K '' B = {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v})
    (hR : R '' A = B) :
    (H.symm.trans R |>.trans K) ''
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwA : H.symm w ∈ A := by
      have hw' : w ∈ H '' A := hA ▸ hw
      rcases hw' with ⟨a, ha, haw⟩
      have : H.symm w = a := by
        calc
          H.symm w = H.symm (H a) := congrArg H.symm haw.symm
          _ = a := H.symm_apply_apply a
      simpa [this] using ha
    have hRwB : R (H.symm w) ∈ B := by
      rw [← hR]
      exact ⟨H.symm w, hwA, rfl⟩
    rw [← hB]
    exact ⟨R (H.symm w), hRwB, rfl⟩
  · intro hz
    have hzB : K.symm z ∈ B := by
      have hz' : z ∈ K '' B := hB ▸ hz
      rcases hz' with ⟨b, hb, hbz⟩
      have : K.symm z = b := by
        calc
          K.symm z = K.symm (K b) := congrArg K.symm hbz.symm
          _ = b := K.symm_apply_apply b
      simpa [this] using hb
    have hzA : K.symm z ∈ R '' A := by simpa [hR] using hzB
    rcases hzA with ⟨a, ha, hRa⟩
    have hHa : H a ∈ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} :=
      (hA ▸ ⟨a, ha, rfl⟩)
    refine ⟨H a, hHa, ?_⟩
    change K (R (H.symm (H a))) = z
    rw [H.symm_apply_apply, hRa, K.apply_symm_apply]

/-- Helper toward Proposition 5.16. Independent continuous arc straighteners
with nonconstant positive prefixes have matching radial restrictions on some
positive common prefix. The PL drawing fields supply these prefix properties;
the common-prefix and radial-image steps are the proved Iso13 helpers. -/
theorem d39_shrinking_radial_segments_of_continuous_injective_arcs
    {D : Type*} {star : Set D} {arc arc' : D → I → ℂ}
    {dir dir' : D → ℂ}
    (Hx Hy R : ℂ ≃ₜ ℂ)
    (hstraightx : ∀ x ∈ star, ∃ tx : I, 0 < (tx : ℝ) ∧ (tx : ℝ) < 1 ∧
      Hx '' (arc x '' Set.Icc (0 : I) tx) =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t : ℂ) * dir x})
    (hstraighty : ∀ x ∈ star, ∃ ty : I, 0 < (ty : ℝ) ∧ (ty : ℝ) < 1 ∧
      Hy '' (arc' x '' Set.Icc (0 : I) ty) =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t : ℂ) * dir' x})
    (hmap : ∀ x ∈ star, ∃ φ : I ≃ₜ I, StrictMono φ ∧
      ∀ t, R (arc x t) = arc' x (φ t))
    (hstart : ∀ x ∈ star, Hx (arc x 0) = 0 ∧ Hy (arc' x 0) = 0)
    (hcont : ∀ x ∈ star, Continuous (arc x) ∧ Continuous (arc' x))
    (harcPrefix : ∀ x ∈ star, ∀ c : I, 0 < (c : ℝ) → (c : ℝ) < 1 →
      ∃ q ∈ Set.Icc (0 : I) c, arc x q ≠ arc x 0)
    (harcPrefix' : ∀ x ∈ star, ∀ c : I, 0 < (c : ℝ) → (c : ℝ) < 1 →
      ∃ q ∈ Set.Icc (0 : I) c, arc' x q ≠ arc' x 0) :
    ∀ x ∈ star, ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      (Hx.symm.trans R |>.trans Hy) ''
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * dir x} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * dir' x} := by
  intro x hx
  obtain ⟨tx, htx0, htx1, hstraightx'⟩ := hstraightx x hx
  obtain ⟨ty, hty0, hty1, hstraighty'⟩ := hstraighty x hx
  obtain ⟨φ, hφ, hmap'⟩ := hmap x hx
  obtain ⟨t, ht0, ht1, hφt0, hφt1, hprefix, htle, hφtle⟩ :=
    d39_common_prefix_of_increasing_reparam arc arc' R φ hφ x tx ty
      htx0 htx1 hty0 hty1 hmap'
  have hfcont : Continuous (fun q => Hx (arc x q)) :=
    Hx.continuous.comp (hcont x hx).1
  have hgcont : Continuous (fun q => Hy (arc' x q)) :=
    Hy.continuous.comp (hcont x hx).2
  have hfstart : Hx (arc x 0) = 0 := (hstart x hx).1
  have hgstart : Hy (arc' x 0) = 0 := (hstart x hx).2
  have hfcontained : ∀ q ∈ Set.Icc (0 : I) t,
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ Hx (arc x q) = (a : ℂ) * dir x := by
    intro q hq
    have hqtx : q ≤ tx := hq.2.trans htle
    have hmem : Hx (arc x q) ∈
        Hx '' (arc x '' Set.Icc (0 : I) tx) := by
      exact ⟨arc x q, ⟨q, ⟨hq.1, hqtx⟩, rfl⟩, rfl⟩
    rw [hstraightx'] at hmem
    exact hmem
  have hgcontained : ∀ q ∈ Set.Icc (0 : I) (φ t),
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ Hy (arc' x q) = (a : ℂ) * dir' x := by
    intro q hq
    have hqty : q ≤ ty := hq.2.trans hφtle
    have hmem : Hy (arc' x q) ∈
        Hy '' (arc' x '' Set.Icc (0 : I) ty) := by
      exact ⟨arc' x q, ⟨q, ⟨hq.1, hqty⟩, rfl⟩, rfl⟩
    rw [hstraighty'] at hmem
    exact hmem
  have hfnc : ∃ q ∈ Set.Icc (0 : I) t, Hx (arc x q) ≠ 0 := by
    obtain ⟨q, hq, hqne⟩ := harcPrefix x hx t ht0 ht1
    refine ⟨q, hq, ?_⟩
    intro heq
    apply hqne
    exact Hx.injective (heq.trans hfstart.symm)
  have hgnc : ∃ q ∈ Set.Icc (0 : I) (φ t), Hy (arc' x q) ≠ 0 := by
    obtain ⟨q, hq, hqne⟩ := harcPrefix' x hx (φ t) hφt0 hφt1
    refine ⟨q, hq, ?_⟩
    intro heq
    apply hqne
    exact Hy.injective (heq.trans hgstart.symm)
  obtain ⟨r, hr, hradx⟩ := d39_continuous_radial_prefix_is_initial_segment
    (fun q => Hx (arc x q)) (dir x) hfcont (by
      intro hu
      rcases hfnc with ⟨q, hq, hqne⟩
      obtain ⟨a, ha0, ha1, hval⟩ := hfcontained q hq
      rw [hu] at hval
      simp at hval
      exact hqne hval) hfstart hfcontained hfnc
  obtain ⟨s, hs, hrady⟩ := d39_continuous_radial_prefix_is_initial_segment
    (fun q => Hy (arc' x q)) (dir' x) hgcont (by
      intro hu
      rcases hgnc with ⟨q, hq, hqne⟩
      obtain ⟨a, ha0, ha1, hval⟩ := hgcontained q hq
      rw [hu] at hval
      simp at hval
      exact hqne hval) hgstart hgcontained hgnc
  have hRprefix :
      R '' (arc x '' Set.Icc (0 : I) t) =
        arc' x '' Set.Icc (0 : I) (φ t) := by
    calc
      R '' (arc x '' Set.Icc (0 : I) t) =
          R '' (R.symm '' (arc' x '' Set.Icc (0 : I) (φ t))) := by
        rw [hprefix]
      _ = arc' x '' Set.Icc (0 : I) (φ t) := by
        simp [Set.image_image]
  have hradx' : Hx '' (arc x '' Set.Icc (0 : I) t) =
      {z : ℂ | ∃ a : ℝ, 0 ≤ a ∧ a ≤ r ∧ z = (a : ℂ) * dir x} := by
    simpa only [Set.image_image] using hradx
  have hrady' : Hy '' (arc' x '' Set.Icc (0 : I) (φ t)) =
      {z : ℂ | ∃ a : ℝ, 0 ≤ a ∧ a ≤ s ∧ z = (a : ℂ) * dir' x} := by
    simpa only [Set.image_image] using hrady
  exact ⟨r, s, hr, hs,
    d39_composite_straightener_maps_matched_radial_segments Hx Hy R
      (dir x) (dir' x) r s hradx' hrady' hRprefix⟩

/-- Helper toward Proposition 5.16. Two counterclockwise-successor witnesses
agree after transporting one direction system by matching radial segments. -/
theorem d39_CcwSuccessor_eq_of_radial_segment_transport
    {D : Type*} {star : Set D} {dir dir' : D → ℂ} {d e f : D}
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (hdir : ∀ x ∈ star, dir x ≠ 0 ∧ dir' x ≠ 0)
    (harg : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (harg' : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir' x) = Complex.arg (dir' y) → x = y)
    (hsegments : ∀ x ∈ star, ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * dir x} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * dir' x})
    (hsucc : CcwSuccessor star dir d e)
    (hsucc' : CcwSuccessor star dir' d f) : e = f := by
  have htransport := d39_CcwSuccessor_transport_of_radial_segments_unconditionally
    K hK hK0 hdir harg hsegments hsucc
  exact d39_CcwSuccessor_unique harg' htransport hsucc'































end DirectedDistances.PaperProofs.Section5

end
