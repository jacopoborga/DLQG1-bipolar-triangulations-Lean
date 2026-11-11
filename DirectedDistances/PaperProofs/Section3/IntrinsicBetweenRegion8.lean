/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion6
public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion7
import Mathlib.Analysis.Complex.ReImTopology

/-! # Components between proper graph rays

Finite limiting abscissas and terminal half-line fibers are retained. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set Filter
open scoped Topology

private theorem intrinsicBetween8_preconnected_of_fibers
    {S : Set ℂ} (hS : IsOpen S) (hproj : IsPreconnected (Complex.re '' S))
    (hfib : ∀ x : ℝ, IsPreconnected {z : ℂ | z ∈ S ∧ z.re = x}) :
    IsPreconnected S := by
  intro U V hU hV hcover hSU hSV
  obtain ⟨x, _, ⟨u, ⟨huS, huU⟩, hux⟩, ⟨v, ⟨hvS, hvV⟩, hvx⟩⟩ :=
    hproj (Complex.re '' (S ∩ U)) (Complex.re '' (S ∩ V))
      (Complex.isOpenMap_re _ (hS.inter hU))
      (Complex.isOpenMap_re _ (hS.inter hV))
      (by
        rintro _ ⟨z, hz, rfl⟩
        rcases hcover hz with h | h
        · exact Or.inl ⟨z, ⟨hz, h⟩, rfl⟩
        · exact Or.inr ⟨z, ⟨hz, h⟩, rfl⟩)
      (by
        obtain ⟨z, hz, hu⟩ := hSU
        exact ⟨z.re, ⟨z, hz, rfl⟩, ⟨z, ⟨hz, hu⟩, rfl⟩⟩)
      (by
        obtain ⟨z, hz, hv⟩ := hSV
        exact ⟨z.re, ⟨z, hz, rfl⟩, ⟨z, ⟨hz, hv⟩, rfl⟩⟩)
  obtain ⟨z, ⟨hz, _⟩, hzU, hzV⟩ := hfib x U V hU hV
    (fun _ hz => hcover hz.1) ⟨u, ⟨huS, hux⟩, huU⟩ ⟨v, ⟨hvS, hvx⟩, hvV⟩
  exact ⟨z, hz, hzU, hzV⟩

private theorem intrinsicBetween8_vertical_image {S : Set ℂ} (x : ℝ) :
    (fun y : ℝ => (⟨x, y⟩ : ℂ)) '' {y : ℝ | (⟨x, y⟩ : ℂ) ∈ S} =
      {z : ℂ | z ∈ S ∧ z.re = x} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨hz, hx⟩
    have he : (⟨x, z.im⟩ : ℂ) = z := Complex.ext hx.symm rfl
    exact ⟨z.im, he.symm ▸ hz, he⟩

private theorem intrinsicBetween8_vertical_preconnected {S : Set ℂ} (x : ℝ)
    (h : IsPreconnected {y : ℝ | (⟨x, y⟩ : ℂ) ∈ S}) :
    IsPreconnected {z : ℂ | z ∈ S ∧ z.re = x} := by
  rw [← intrinsicBetween8_vertical_image]
  exact h.image _ (Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_const.prodMk continuous_id)).continuousOn

/-- Helper toward Proposition 3.9: the abscissa projection of the strict
region includes the terminal half-line fibers after the upper endpoint. -/
theorem intrinsicBetween8_strictRegion_projection
    (x₀ : ℝ) (XP XR : WithTop ℝ) (fP fR : ℝ → ℝ) :
    Complex.re '' {z : ℂ | x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)} =
      {x : ℝ | x₀ < x ∧ x ∈ rayDomain x₀ XR ∧
        (x ∈ rayDomain x₀ XP → fR x < fP x)} := by
  ext x
  constructor
  · rintro ⟨z, ⟨hx, hd, hlo, hhi⟩, rfl⟩
    exact ⟨hx, hd, fun hp => hlo.trans (hhi hp)⟩
  · rintro ⟨hx, hd, hg⟩
    by_cases hp : x ∈ rayDomain x₀ XP
    · refine ⟨⟨x, (fR x + fP x) / 2⟩, ⟨hx, hd, ?_, ?_⟩, rfl⟩
      · change fR x < (fR x + fP x) / 2
        linarith only [hg hp]
      · intro _
        change (fR x + fP x) / 2 < fP x
        linarith only [hg hp]
    · exact ⟨⟨x, fR x + 1⟩, ⟨hx, hd, lt_add_one _, fun h => (hp h).elim⟩, rfl⟩

/-- Helper toward Proposition 3.9: bands over components of the extended
gap set are preconnected, including fibers with no upper bound. -/
theorem intrinsicBetween8_isPreconnected_extendedBand
    {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    (x : ℝ) :
    let J : Set ℝ := {t | x₀ < t ∧ t ∈ rayDomain x₀ XR ∧
      (t ∈ rayDomain x₀ XP → fR t < fP t)}
    IsPreconnected {z : ℂ | z.re ∈ connectedComponentIn J x ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)} := by
  dsimp only
  let V : Set ℂ := {z | x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
    fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)}
  let J : Set ℝ := {t | x₀ < t ∧ t ∈ rayDomain x₀ XR ∧
    (t ∈ rayDomain x₀ XP → fR t < fP t)}
  let K := connectedComponentIn J x
  let B : Set ℂ := {z | z.re ∈ K ∧ fR z.re < z.im ∧
    (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)}
  have hV : IsOpen V := intrinsicBetween5_isOpen_strictRegion hcP hcR hescP
  have hproj : Complex.re '' V = J :=
    intrinsicBetween8_strictRegion_projection x₀ XP XR fP fR
  have hK : IsOpen K := (hproj ▸ Complex.isOpenMap_re V hV).connectedComponentIn
  have hB : B = V ∩ Complex.re ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨hz, hlo, hhi⟩
      have hj := connectedComponentIn_subset J x hz
      exact ⟨⟨hj.1, hj.2.1, hlo, hhi⟩, hz⟩
    · rintro ⟨⟨_, _, hlo, hhi⟩, hz⟩
      exact ⟨hz, hlo, hhi⟩
  have hprojB : Complex.re '' B = K := by
    rw [hB, image_inter_preimage, hproj]
    exact inter_eq_right.mpr (connectedComponentIn_subset J x)
  change IsPreconnected B
  apply intrinsicBetween8_preconnected_of_fibers
    (hB.symm ▸ hV.inter (hK.preimage Complex.continuous_re))
    (hprojB.symm ▸ isPreconnected_connectedComponentIn)
  intro t
  apply intrinsicBetween8_vertical_preconnected
  by_cases ht : t ∈ K
  · by_cases hd : t ∈ rayDomain x₀ XP
    · change IsPreconnected {y : ℝ | t ∈ K ∧ fR t < y ∧
        (t ∈ rayDomain x₀ XP → y < fP t)}
      simpa only [ht, hd, true_implies, true_and, ← mem_Ioo, ofPred_mem_eq] using
        (isPreconnected_Ioo : IsPreconnected (Ioo (fR t) (fP t)))
    · change IsPreconnected {y : ℝ | t ∈ K ∧ fR t < y ∧
        (t ∈ rayDomain x₀ XP → y < fP t)}
      simpa only [ht, hd, false_implies, true_and, and_true, ← mem_Ioi, ofPred_mem_eq] using
        (isPreconnected_Ioi : IsPreconnected (Ioi (fR t)))
  · change IsPreconnected {y : ℝ | t ∈ K ∧ _}
    simpa only [ht, false_and, ofPred_false] using
      (isPreconnected_empty : IsPreconnected (∅ : Set ℝ))

/-- Helper toward Proposition 3.9: every interior component is exactly
the band over its extended gap component. Terminal fibers are upper
half-lines when the upper ray has ended. -/
theorem intrinsicBetween8_component_eq_extendedBand
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP) (hXR : (x₀ : WithTop ℝ) < XR)
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
    (hstart : fP x₀ = fR x₀) {z : ℂ}
    (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)) :
    let J : Set ℝ := {x | x₀ < x ∧ x ∈ rayDomain x₀ XR ∧
      (x ∈ rayDomain x₀ XP → fR x < fP x)}
    connectedComponentIn (P ∪ R)ᶜ z =
      {q : ℂ | q.re ∈ connectedComponentIn J z.re ∧
        fR q.re < q.im ∧ (q.re ∈ rayDomain x₀ XP → q.im < fP q.re)} := by
  dsimp only
  let J : Set ℝ := {x | x₀ < x ∧ x ∈ rayDomain x₀ XR ∧
    (x ∈ rayDomain x₀ XP → fR x < fP x)}
  have hzJ : z.re ∈ J := ⟨hz.1, hz.2.1, fun hd => hz.2.2.1.trans (hz.2.2.2 hd)⟩
  have hC := intrinsicBetween5_component_subset_strictRegion hP hR hXP hcP hcR
    hescP ⟨XR, fR, hXR, hcR, hR, hescR⟩ hstart hz
  have hn : z ∈ (P ∪ R)ᶜ := by
    rw [hP, hR]
    rintro (⟨hd, he⟩ | ⟨_, he⟩)
    · exact (hz.2.2.2 hd).ne he
    · exact hz.2.2.1.ne' he
  have himage : Complex.re '' connectedComponentIn (P ∪ R)ᶜ z ⊆
      connectedComponentIn J z.re := by
    apply (isPreconnected_connectedComponentIn.image Complex.re
      Complex.continuous_re.continuousOn).subset_connectedComponentIn
      ⟨z, mem_connectedComponentIn hn, rfl⟩
    rintro _ ⟨q, hq, rfl⟩
    have hh := hC hq
    exact ⟨hh.1, hh.2.1, fun hd => hh.2.2.1.trans (hh.2.2.2 hd)⟩
  apply subset_antisymm
  · intro q hq
    exact ⟨himage ⟨q, hq, rfl⟩, (hC hq).2.2⟩
  · apply (intrinsicBetween8_isPreconnected_extendedBand hcP hcR hescP z.re).subset_connectedComponentIn
      ⟨mem_connectedComponentIn hzJ, hz.2.2⟩
    rintro q ⟨_, hlo, hhi⟩
    rw [hP, hR]
    rintro (⟨hd, he⟩ | ⟨_, he⟩)
    · exact (hhi hd).ne he
    · exact hlo.ne' he

/-- Helper toward Proposition 3.9: the exterior remains connected for
independently varying finite or infinite ray endpoints. -/
theorem intrinsicBetween8_exterior_isConnected
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP)
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t) :
    IsConnected (closedBetween P R)ᶜ := by
  let U : Set ℂ := {z | x₀ ≤ z.re ∧
    (z.re ∈ rayDomain x₀ XP → z.im ≤ fP z.re)}ᶜ
  let B : Set ℂ := {z | z.re ∈ rayDomain x₀ XR ∧ fR z.re ≤ z.im}ᶜ
  have hU : IsOpen U := (intrinsicBetween5_isClosed_extendedHypograph hcP).isOpen_compl
  have hB : IsOpen B := (intrinsicBetween5_isClosed_epigraph hcR hescR).isOpen_compl
  have hprojU : Complex.re '' U = {x : ℝ | (x : WithTop ℝ) < XP} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hx : x₀ ≤ z.re
      · by_contra hd
        exact hz ⟨hx, fun ht => (hd ht.2).elim⟩
      · exact (WithTop.coe_lt_coe.mpr (lt_of_not_ge hx)).trans hXP
    · intro hx
      refine ⟨⟨x, fP x + 1⟩, ?_, rfl⟩
      rintro ⟨hstart, hle⟩
      exact (lt_add_one (fP x)).not_ge (hle ⟨hstart, hx⟩)
  have hprojB : Complex.re '' B = univ := by
    apply eq_univ_of_forall
    intro x
    refine ⟨⟨x, fR x - 1⟩, ?_, rfl⟩
    rintro ⟨_, hle⟩
    change fR x ≤ fR x - 1 at hle
    linarith only [hle]
  have hcU : IsPreconnected U := by
    apply intrinsicBetween8_preconnected_of_fibers hU
    · rw [hprojU]
      induction XP using WithTop.recTopCoe with
      | top => simpa only [WithTop.coe_lt_top, ofPred_true] using
          (isPreconnected_univ : IsPreconnected (univ : Set ℝ))
      | coe b =>
          have he : {x : ℝ | (x : WithTop ℝ) < (b : WithTop ℝ)} = Iio b := by
            ext x
            exact WithTop.coe_lt_coe
          rw [he]
          exact isPreconnected_Iio
    · intro x
      apply intrinsicBetween8_vertical_preconnected
      by_cases hx : x₀ ≤ x
      · by_cases hd : x ∈ rayDomain x₀ XP
        · change IsPreconnected {y : ℝ | ¬ (x₀ ≤ x ∧ (x ∈ rayDomain x₀ XP → y ≤ fP x))}
          simpa only [hx, hd, true_implies, true_and, not_le, ← mem_Ioi, ofPred_mem_eq]
            using (isPreconnected_Ioi : IsPreconnected (Ioi (fP x)))
        · change IsPreconnected {y : ℝ | ¬ (x₀ ≤ x ∧ (x ∈ rayDomain x₀ XP → y ≤ fP x))}
          simpa only [hx, hd, false_implies, and_self, not_true, ofPred_false]
            using (isPreconnected_empty : IsPreconnected (∅ : Set ℝ))
      · change IsPreconnected {y : ℝ | ¬ (x₀ ≤ x ∧ (x ∈ rayDomain x₀ XP → y ≤ fP x))}
        simpa only [hx, false_and, not_false_eq_true, ofPred_true]
          using (isPreconnected_univ : IsPreconnected (univ : Set ℝ))
  have hcB : IsPreconnected B := by
    apply intrinsicBetween8_preconnected_of_fibers hB (hprojB.symm ▸ isPreconnected_univ)
    intro x
    apply intrinsicBetween8_vertical_preconnected
    by_cases hd : x ∈ rayDomain x₀ XR
    · change IsPreconnected {y : ℝ | ¬ (x ∈ rayDomain x₀ XR ∧ fR x ≤ y)}
      simpa only [hd, true_and, not_le, ← mem_Iio, ofPred_mem_eq] using
        (isPreconnected_Iio : IsPreconnected (Iio (fR x)))
    · change IsPreconnected {y : ℝ | ¬ (x ∈ rayDomain x₀ XR ∧ fR x ≤ y)}
      simpa only [hd, false_and, not_false_eq_true, ofPred_true] using
        (isPreconnected_univ : IsPreconnected (univ : Set ℝ))
  let q : ℂ := ⟨x₀ - 1, 0⟩
  have hqU : q ∈ U := by
    rintro ⟨hx, _⟩
    change x₀ ≤ x₀ - 1 at hx
    linarith only [hx]
  have hqB : q ∈ B := by
    rintro ⟨hx, _⟩
    have hh := hx.1
    change x₀ ≤ x₀ - 1 at hh
    linarith only [hh]
  have heq : (closedBetween P R)ᶜ = U ∪ B := by
    ext z
    rw [mem_compl_iff, mem_closedBetween_iff hP hR]
    change (¬ (_ ∧ _ ∧ _)) ↔ (¬ (_ ∧ _)) ∨ ¬ (_ ∧ _)
    constructor
    · intro hz
      by_cases hb : z.re ∈ rayDomain x₀ XR ∧ fR z.re ≤ z.im
      · exact Or.inl (fun hu => hz ⟨hb.1, hb.2, hu.2⟩)
      · exact Or.inr hb
    · rintro (hu | hb) ⟨hd, hlo, hhi⟩
      · exact hu ⟨hd.1, hhi⟩
      · exact hb ⟨hd, hlo⟩
  rw [heq]
  exact ⟨⟨q, Or.inl hqU⟩, hcU.union q hqU hqB hcB⟩

/-- Helper toward Proposition 3.9: ordered proper rays have nested
abscissa domains; the lower ray cannot end before the upper ray. -/
theorem intrinsicBetween8_rayDomain_subset
    {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
    (horder : ∀ x ∈ rayDomain x₀ XP ∩ rayDomain x₀ XR, fR x ≤ fP x) :
    rayDomain x₀ XP ⊆ rayDomain x₀ XR := by
  intro x hx
  by_contra hn
  have hXR : XR ≤ (x : WithTop ℝ) := le_of_not_gt (fun h => hn ⟨hx.1, h⟩)
  have hsub : Icc x₀ x ⊆ rayDomain x₀ XP := fun t ht =>
    ⟨ht.1, (WithTop.coe_le_coe.mpr ht.2).trans_lt hx.2⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image (hcP.mono hsub)
  obtain ⟨a, ha, hbig⟩ := hescR (M + 1)
  have hax : a ≤ x := (WithTop.coe_lt_coe.mp (ha.2.trans_le hXR)).le
  have haP := hsub ⟨ha.1, hax⟩
  have hbound := hM (mem_image_of_mem fP (show a ∈ Icc x₀ x from ⟨ha.1, hax⟩))
  have hle := horder a ⟨haP, ha⟩
  have hlarge := hbig a ha (le_refl _)
  linarith only [hbound, hle, hlarge]

/-- Helper toward Proposition 3.9: both whole traces belong to the
fiber region under the order of the source rays. -/
theorem intrinsicBetween8_traces_subset_closedBetween
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
    (horder : ∀ x ∈ rayDomain x₀ XP ∩ rayDomain x₀ XR, fR x ≤ fP x) :
    P ∪ R ⊆ closedBetween P R := by
  intro z hz
  rw [mem_closedBetween_iff hP hR]
  rcases hz with hz | hz
  · have hh := hP ▸ hz
    have hd := intrinsicBetween8_rayDomain_subset hcP hescR horder hh.1
    exact ⟨hd, hh.2 ▸ horder z.re ⟨hh.1, hd⟩, fun _ => hh.2.le⟩
  · have hh := hR ▸ hz
    exact ⟨hh.1, hh.2.ge, fun hd => hh.2 ▸ horder z.re ⟨hd, hh.1⟩⟩

/-- Helper toward Proposition 3.9: the exterior is one complementary
component for ordered proper rays, also with unequal endpoints. -/
theorem intrinsicBetween8_component_eq_exterior
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP) (hXR : (x₀ : WithTop ℝ) < XR)
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
    (hstart : fP x₀ = fR x₀)
    (horder : ∀ x ∈ rayDomain x₀ XP ∩ rayDomain x₀ XR, fR x ≤ fP x)
    {z : ℂ} (hz : z ∉ closedBetween P R) :
    connectedComponentIn (P ∪ R)ᶜ z = (closedBetween P R)ᶜ := by
  let V : Set ℂ := {q | x₀ < q.re ∧ q.re ∈ rayDomain x₀ XR ∧
    fR q.re < q.im ∧ (q.re ∈ rayDomain x₀ XP → q.im < fP q.re)}
  have heq : closedBetween P R \ (P ∪ R) = V :=
    intrinsicBetween5_closedBetween_diff_traces hP hR hXP hstart
  have hclosed : IsClosed (closedBetween P R) := isClosed_closedBetween
    ⟨XP, fP, hXP, hcP, hP, hescP⟩ ⟨XR, fR, hXR, hcR, hR, hescR⟩
  have hsub : (closedBetween P R)ᶜ ⊆ (P ∪ R)ᶜ :=
    fun _ hq ht => hq (intrinsicBetween8_traces_subset_closedBetween hP hR hcP hescR horder ht)
  apply subset_antisymm
  · apply isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hclosed.isOpen_compl (intrinsicBetween5_isOpen_strictRegion hcP hcR hescP)
    · apply disjoint_left.mpr
      intro q hq hv
      exact hq ((heq.symm ▸ hv : q ∈ closedBetween P R \ (P ∪ R)).1)
    · intro q hq
      by_cases hb : q ∈ closedBetween P R
      · apply Or.inr
        change q ∈ V
        exact heq ▸ (show q ∈ closedBetween P R \ (P ∪ R) from
          ⟨hb, connectedComponentIn_subset _ _ hq⟩)
      · exact Or.inl hb
    · exact ⟨z, mem_connectedComponentIn (hsub hz), hz⟩
  · exact (intrinsicBetween8_exterior_isConnected hP hR hXP hcP hcR hescR).isPreconnected.subset_connectedComponentIn hz hsub

/-- Helper toward Proposition 3.9: every complementary component is
either the exterior or a band over a component of the extended gap set.
This retains all terminal half-line fibers when the endpoints differ. -/
theorem intrinsicBetween8_component_cases
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP) (hXR : (x₀ : WithTop ℝ) < XR)
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
    (hstart : fP x₀ = fR x₀)
    (horder : ∀ x ∈ rayDomain x₀ XP ∩ rayDomain x₀ XR, fR x ≤ fP x) :
    let J : Set ℝ := {x | x₀ < x ∧ x ∈ rayDomain x₀ XR ∧
      (x ∈ rayDomain x₀ XP → fR x < fP x)}
    ∀ z : ℂ, z ∉ P ∪ R →
      (z ∉ closedBetween P R ∧
        connectedComponentIn (P ∪ R)ᶜ z = (closedBetween P R)ᶜ) ∨
      (z.re ∈ J ∧ fR z.re < z.im ∧
        (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)) ∧
        connectedComponentIn (P ∪ R)ᶜ z =
          {q : ℂ | q.re ∈ connectedComponentIn J z.re ∧
            fR q.re < q.im ∧ (q.re ∈ rayDomain x₀ XP → q.im < fP q.re)} := by
  dsimp only
  intro z hz
  by_cases hb : z ∈ closedBetween P R
  · have hs := intrinsicBetween5_closedBetween_diff_traces hP hR hXP hstart
    have hh := hs ▸ (show z ∈ closedBetween P R \ (P ∪ R) from ⟨hb, hz⟩)
    exact Or.inr ⟨⟨⟨hh.1, hh.2.1, fun hd => hh.2.2.1.trans (hh.2.2.2 hd)⟩,
      hh.2.2⟩, intrinsicBetween8_component_eq_extendedBand hP hR hXP hXR hcP hcR
        hescP hescR hstart hh⟩
  · exact Or.inl ⟨hb, intrinsicBetween8_component_eq_exterior hP hR hXP hXR hcP hcR
      hescP hescR hstart horder hb⟩

/-- Helper toward Proposition 3.9: even a terminal component meets a
strict finite band in the common domain of the two rays. -/
theorem intrinsicBetween8_component_meets_common_domain
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP) (hXR : (x₀ : WithTop ℝ) < XR)
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
      ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
    (hstart : fP x₀ = fR x₀) {z : ℂ}
    (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)) :
    ∃ q ∈ connectedComponentIn (P ∪ R)ᶜ z,
      x₀ < q.re ∧ q.re ∈ rayDomain x₀ XP ∧ q.re ∈ rayDomain x₀ XR ∧
        fR q.re < q.im ∧ q.im < fP q.re := by
  by_cases hd : z.re ∈ rayDomain x₀ XP
  · have hn : z ∉ P ∪ R := by
      rw [hP, hR]
      rintro (⟨hp, he⟩ | ⟨_, he⟩)
      · exact (hz.2.2.2 hp).ne he
      · exact hz.2.2.1.ne' he
    exact ⟨z, mem_connectedComponentIn hn, hz.1, hd, hz.2.1,
      hz.2.2.1, hz.2.2.2 hd⟩
  have hfinite : XP ≠ ⊤ := by
    intro he
    exact hd ⟨hz.1.le, he ▸ WithTop.coe_lt_top z.re⟩
  obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hbz : b ≤ z.re := le_of_not_gt (fun hh => hd ⟨hz.1.le, WithTop.coe_lt_coe.mpr hh⟩)
  let J : Set ℝ := {x | x₀ < x ∧ x ∈ rayDomain x₀ XR ∧
    (x ∈ rayDomain x₀ (b : WithTop ℝ) → fR x < fP x)}
  let K := connectedComponentIn J z.re
  have hJ : IsOpen J := by
    rw [show J = _ from (intrinsicBetween8_strictRegion_projection x₀
      (b : WithTop ℝ) XR fP fR).symm]
    exact Complex.isOpenMap_re _ (intrinsicBetween5_isOpen_strictRegion hcP hcR hescP)
  have hK : IsOpen K := hJ.connectedComponentIn
  have hI : Icc b z.re ⊆ J := by
    intro t ht
    refine ⟨(WithTop.coe_lt_coe.mp hXP).trans_le ht.1,
      ⟨(WithTop.coe_lt_coe.mp hXP).le.trans ht.1,
        (WithTop.coe_le_coe.mpr ht.2).trans_lt hz.2.1.2⟩, ?_⟩
    intro htd
    exact False.elim ((WithTop.coe_lt_coe.mp htd.2).not_ge ht.1)
  have hbK : b ∈ K := (isPreconnected_Icc.subset_connectedComponentIn
    (show z.re ∈ Icc b z.re from ⟨hbz, le_refl _⟩) hI) ⟨le_refl _, hbz⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK b hbK
  let t := b - ε / 2
  have htK : t ∈ K := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have he : t - b = -(ε / 2) := by dsimp only [t]; ring
    rw [he, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have htJ := connectedComponentIn_subset J z.re htK
  have htP : t ∈ rayDomain x₀ (b : WithTop ℝ) :=
    ⟨htJ.1.le, WithTop.coe_lt_coe.mpr (sub_lt_self b (half_pos hε))⟩
  have hgap := htJ.2.2 htP
  let q : ℂ := ⟨t, (fR t + fP t) / 2⟩
  have hlo : fR t < q.im := by change fR t < (fR t + fP t) / 2; linarith only [hgap]
  have hhi : q.im < fP t := by change (fR t + fP t) / 2 < fP t; linarith only [hgap]
  refine ⟨q, ?_, htJ.1, htP, htJ.2.1, hlo, hhi⟩
  rw [intrinsicBetween8_component_eq_extendedBand hP hR hXP hXR hcP hcR hescP hescR hstart hz]
  exact ⟨htK, hlo, fun _ => hhi⟩

section Source

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  {v : PresentVertex (shiftedStream W 0)}
  (P R : InfinitePresentPath (shiftedStream W 0) v)

local notation "A₈" => uibotWholePlaneSourceDomain W H
  (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
local notation "p₈" => (fun n => wholePlaneEdgeι W 0 (P.edge n))
local notation "r₈" => (fun n => wholePlaneEdgeι W 0 (R.edge n))
local notation "TP₈" => intrinsicEdgeRayTrace A₈ p₈
local notation "TR₈" => intrinsicEdgeRayTrace A₈ r₈

variable {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
  (hP : intrinsicEdgeRayTrace
    (uibotWholePlaneSourceDomain W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
    (fun n => wholePlaneEdgeι W 0 (P.edge n)) =
      {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
  (hR : intrinsicEdgeRayTrace
    (uibotWholePlaneSourceDomain W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
    (fun n => wholePlaneEdgeι W 0 (R.edge n)) =
      {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
  (hXP : (x₀ : WithTop ℝ) < XP) (hXR : (x₀ : WithTop ℝ) < XR)
  (hcP : ContinuousOn fP (rayDomain x₀ XP))
  (hcR : ContinuousOn fR (rayDomain x₀ XR))
  (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
    ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
  (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XR,
    ∀ t ∈ rayDomain x₀ XR, a ≤ t → M ≤ fR t)
  (hstart : fP x₀ = fR x₀)
  (horder : ∀ x ∈ rayDomain x₀ XP ∩ rayDomain x₀ XR, fR x ≤ fP x)

include hP hR hXP hXR hcP hcR hescP hescR hstart horder

/-- Helper toward Proposition 3.9: the exterior touches the left side
of the upper source ray, including when the two rays coincide. -/
theorem intrinsicBetween8_source_exterior_touches_left {z : ℂ}
    (hz : z ∉ closedBetween TP₈ TR₈) :
    intrinsicRayTouchesSide A₈ p₈ (connectedComponentIn (TP₈ ∪ TR₈)ᶜ z) false := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  let J : Set ℝ := {x | x₀ < x ∧ x ∈ rayDomain x₀ XP ∧
    x ∈ rayDomain x₀ XP ∧ fP x < fP x + 1}
  have hJ : IsOpen J := intrinsicBetween7_isOpen_gap
    (hcP.add continuousOn_const) hcP
  obtain ⟨a, ha, hlarge⟩ := hescP (fP x₀ + 1)
  have hax : x₀ < a := by
    by_contra hn
    have hh := hlarge x₀ ⟨le_refl _, hXP⟩ (le_of_not_gt hn)
    linarith only [hh]
  have haJ : a ∈ J := ⟨hax, ha, ha, lt_add_one _⟩
  have hpath : (⟨a, fP a⟩ : ℂ) ∈ TP₈ := hP.symm ▸ ⟨ha, rfl⟩
  rw [intrinsicGeodesicSource_trace W H G hp] at hpath
  obtain ⟨n, hn⟩ := mem_iUnion.mp hpath
  change (⟨a, fP a⟩ : ℂ) ∈
    (G.arc (wholePlaneDartι W 0 (P.edge n, false))).image at hn
  rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H] at hn
  let d := (P.edge n, false)
  obtain ⟨i, hi, q, hq, hqJ⟩ := intrinsicBetween7_exists_openSegment_in_open_abscissas
    (M.arc d) (M.arc_length d) hJ hn haJ
  have hqtrace : q ∈ TP₈ := by
    rw [intrinsicGeodesicSource_trace W H G hp]
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change q ∈ (G.arc (wholePlaneDartι W 0 d)).image
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H]
    exact Or.inr ⟨i, hi, openSegment_subset_segment ℝ _ _ hq⟩
  have hqheight : q.im = fP q.re := (hP ▸ hqtrace).2
  have hT : TP₈ ∪ TR₈ ⊆ M.image := by
    have hQ (Q : InfinitePresentPath (shiftedStream W 0) v) :
        intrinsicEdgeRayTrace A₈ (fun j => wholePlaneEdgeι W 0 (Q.edge j)) ⊆ M.image := by
      rw [intrinsicGeodesicSource_trace W H G hp]
      intro w hw
      obtain ⟨j, hj⟩ := mem_iUnion.mp hw
      change w ∈ (G.arc (wholePlaneDartι W 0 (Q.edge j, false))).image at hj
      rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H] at hj
      exact Or.inr ⟨(Q.edge j, false), hj⟩
    exact union_subset (hQ P) (hQ R)
  have hband : {w : ℂ | w.re ∈ J ∧ fP w.re < w.im ∧ w.im < fP w.re + 1} ⊆
      connectedComponentIn (TP₈ ∪ TR₈)ᶜ z := by
    rw [intrinsicBetween8_component_eq_exterior hP hR hXP hXR hcP hcR
      hescP hescR hstart horder hz]
    intro w hw hb
    exact hw.2.1.not_ge (((mem_closedBetween_iff hP hR w).mp hb).2.2 hw.1.2.1)
  let F := futureMapDartFace W H h d
  have hb : M.dartBorders d F := (futureMap_dart_face_eq_iff W H h d F).mp rfl
  have hmono : (M.arc d).XMonotone := infinitePresentPath_arc_xMonotone (H.1 0)
    (fun j => ⟨monotoneLayoutDrawing (shiftedStream W 0) j
      ((monotone_family_all (shiftedStream W 0)) j).choose,
      ((monotone_family_all (shiftedStream W 0)) j).choose_spec⟩) P n
  apply (intrinsicBetween_source_ray_touches_side_iff W H h hpast hp P _ false).mpr
  refine ⟨n, ?_⟩
  rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H]
  exact intrinsicBetween7_lower_band_leftAtOn (fP := fun t => fP t + 1) (fR := fP) M
    (kmswLimitDartVertex_surjective _ (H.1 0)) d F hb hT hband hi
    (Polyline.point_re_lt hmono (by omega) hi) hq hqJ hqheight (lt_add_one _)

/-- Helper toward Proposition 3.9: the conjunction of all four tests
rejects the exterior; no desired incidence is denied on coincident rays. -/
theorem intrinsicBetween8_source_exterior_rejected {z : ℂ}
    (hz : z ∉ closedBetween TP₈ TR₈) :
    let C := connectedComponentIn (TP₈ ∪ TR₈)ᶜ z
    ¬ (intrinsicRayTouchesSide A₈ p₈ C true ∧
      intrinsicRayTouchesSide A₈ r₈ C false ∧
      ¬ intrinsicRayTouchesSide A₈ p₈ C false ∧
      ¬ intrinsicRayTouchesSide A₈ r₈ C true) := by
  dsimp only
  intro hs
  exact hs.2.2.1 (intrinsicBetween8_source_exterior_touches_left W H h hpast hp P R
    hP hR hXP hXR hcP hcR hescP hescR hstart horder hz)

omit horder in
/-- Helper toward Proposition 3.9: every strict-region component has
both desired incidences, including the terminal half-line components. -/
theorem intrinsicBetween8_source_component_positive {z : ℂ}
    (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)) :
    let C := connectedComponentIn (TP₈ ∪ TR₈)ᶜ z
    intrinsicRayTouchesSide A₈ p₈ C true ∧ intrinsicRayTouchesSide A₈ r₈ C false := by
  obtain ⟨q, hq, hqc⟩ := intrinsicBetween8_component_meets_common_domain
    hP hR hXP hXR hcP hcR hescP hescR hstart hz
  dsimp only
  rw [connectedComponentIn_eq hq]
  exact intrinsicBetween7_source_component_positive_on_common_domain
    W H h hpast hp P R hP hR hcP hcR hqc

/-- Helper toward Proposition 3.9: the four winding tests select exactly
the complementary components inside the fiber region. -/
theorem intrinsicBetween8_source_component_selected_iff {z : ℂ}
    (hz : z ∉ TP₈ ∪ TR₈) :
    let C := connectedComponentIn (TP₈ ∪ TR₈)ᶜ z
    (intrinsicRayTouchesSide A₈ p₈ C true ∧
      intrinsicRayTouchesSide A₈ r₈ C false ∧
      ¬ intrinsicRayTouchesSide A₈ p₈ C false ∧
      ¬ intrinsicRayTouchesSide A₈ r₈ C true) ↔ z ∈ closedBetween TP₈ TR₈ := by
  constructor
  · intro hs
    by_contra hb
    exact intrinsicBetween8_source_exterior_rejected W H h hpast hp P R
      hP hR hXP hXR hcP hcR hescP hescR hstart horder hb hs
  · intro hb
    have hstrict := intrinsicBetween5_closedBetween_diff_traces hP hR hXP hstart
    have hs := hstrict ▸ (show z ∈ closedBetween TP₈ TR₈ \ (TP₈ ∪ TR₈) from ⟨hb, hz⟩)
    have hpos := intrinsicBetween8_source_component_positive W H h hpast hp P R
      hP hR hXP hXR hcP hcR hescP hescR hstart hs
    have hneg := intrinsicConsumersFinal_source_component_wrong_sides W H h hpast hp P R
      hP hR hXP hXR hcP hcR hescP hescR hstart hs
    exact ⟨hpos.1, hpos.2, hneg⟩

/-- Helper toward Proposition 3.9: the native region equals the closed
fiber region for ordered source rays, with both traces and all terminal
fibers included. The four winding tests are proved, not assumed. -/
theorem intrinsicBetween8_source_native_eq_closedBetween_of_graphs :
    nativeBetween A₈ p₈ r₈ = closedBetween TP₈ TR₈ := by
  have hclosed : IsClosed (closedBetween TP₈ TR₈) := isClosed_closedBetween
    ⟨XP, fP, hXP, hcP, hP, hescP⟩ ⟨XR, fR, hXR, hcR, hR, hescR⟩
  apply subset_antisymm
  · apply closure_minimal ?_ hclosed
    rintro z (⟨w, hw, hzC, hPr, hRl, hnPl, hnRr⟩ | hz)
    · have hznot : z ∉ TP₈ ∪ TR₈ := connectedComponentIn_subset _ _ hzC
      rw [connectedComponentIn_eq hzC] at hPr hRl hnPl hnRr
      exact (intrinsicBetween8_source_component_selected_iff W H h hpast hp P R
        hP hR hXP hXR hcP hcR hescP hescR hstart horder hznot).mp
          ⟨hPr, hRl, hnPl, hnRr⟩
    · exact intrinsicBetween8_traces_subset_closedBetween hP hR hcP hescR horder hz
  · intro z hz
    by_cases ht : z ∈ TP₈ ∪ TR₈
    · exact subset_closure (Or.inr ht)
    · have hs := (intrinsicBetween8_source_component_selected_iff W H h hpast hp P R
        hP hR hXP hXR hcP hcR hescP hescR hstart horder ht).mpr hz
      exact subset_closure (Or.inl ⟨z, ht, mem_connectedComponentIn ht, hs⟩)

end Source

/-- Helper toward Proposition 3.9: native-region equality for actual
source rays with a rightmost second ray. Properness, common start, graph
order and all four winding tests are derived from the source objects. -/
theorem intrinsicBetween8_source_native_eq_closedBetween
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P R : InfinitePresentPath (shiftedStream W 0) v)
    (hmost : ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
      (R.initial n).1.id (R.edge n)) :
    let A := uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
    nativeBetween A (fun n => wholePlaneEdgeι W 0 (P.edge n))
      (fun n => wholePlaneEdgeι W 0 (R.edge n)) =
    closedBetween (intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (P.edge n)))
      (intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (R.edge n))) := by
  dsimp only
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let A := uibotWholePlaneSourceDomain W H G hp
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hwest (Q : InfinitePresentPath (shiftedStream W 0) v) :
      edgeWest (shiftedStream W 0) (Q.edge 0) = v.id := by
    have hzero := (Q.initial 0).2.eq_of_length_zero (Q.prefix_length 0)
    exact (Q.edge_outgoing_at_initial (shiftedStream W 0) 0).2.trans
      (congrArg PresentVertex.id hzero.symm)
  have hproper (Q : InfinitePresentPath (shiftedStream W 0) v) :
      ProperGraphRay (intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (Q.edge n)))
        (M.pos v.id).re := by
    have hh := intrinsicBetween_source_trace_properGraphRay W H h hpast hp Q
    change ProperGraphRay _ (M.arc (Q.edge 0, false)).start.re at hh
    rw [M.arc_start] at hh
    change ProperGraphRay _ (M.pos (edgeWest (shiftedStream W 0) (Q.edge 0))).re at hh
    rwa [hwest Q] at hh
  obtain ⟨XP, fP, hXP, hcP, hP, hescP⟩ := hproper P
  obtain ⟨XR, fR, hXR, hcR, hR, hescR⟩ := hproper R
  have hmem (Q : InfinitePresentPath (shiftedStream W 0) v) :
      M.pos v.id ∈ intrinsicEdgeRayTrace A (fun n => wholePlaneEdgeι W 0 (Q.edge n)) := by
    rw [intrinsicGeodesicSource_trace W H G hp]
    apply mem_iUnion.mpr
    refine ⟨0, ?_⟩
    change M.pos v.id ∈ (G.arc (wholePlaneDartι W 0 (Q.edge 0, false))).image
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hpast H]
    apply Or.inl
    rw [M.arc_start]
    change M.pos v.id = M.pos (edgeWest (shiftedStream W 0) (Q.edge 0))
    rw [hwest Q]
  have hpmem := hP ▸ hmem P
  have hrmem := hR ▸ hmem R
  have hstart : fP (M.pos v.id).re = fR (M.pos v.id).re :=
    hpmem.2.symm.trans hrmem.2
  have hboundary := intrinsicBetween7_source_traces_subset_between_of_rightmost
    W H h hpast hp P R hmost
  have horder : ∀ x ∈ rayDomain (M.pos v.id).re XP ∩ rayDomain (M.pos v.id).re XR,
      fR x ≤ fP x := by
    intro x hx
    have hq : (⟨x, fP x⟩ : ℂ) ∈ intrinsicEdgeRayTrace A
        (fun n => wholePlaneEdgeι W 0 (P.edge n)) := hP.symm ▸ ⟨hx.1, rfl⟩
    exact ((mem_closedBetween_iff hP hR _).mp (hboundary (Or.inl hq))).2.1
  exact intrinsicBetween8_source_native_eq_closedBetween_of_graphs W H h hpast hp P R
    hP hR hXP hXR hcP hcR hescP hescR hstart horder

/-- Helper toward Proposition 3.9: native-region equality transports to
every geometric source representative for the source geodesic and its
rightmost reference path. No exterior-exclusion premise is required. -/
theorem intrinsicBetween8_native_eq_closedBetween
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
      (P : DirectedDistances.PaperProofs.Section5.M0CutInfiniteGeodesic W H h hLL k longest)
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
  have hsource := intrinsicBetween8_source_native_eq_closedBetween W H h hpast hp P.codePath T hmost
  calc
    _ = I.h '' nativeBetween S pe re := (nativeBetween_map (A := S) (B := A) I pe re).symm
    _ = I.h '' closedBetween (intrinsicEdgeRayTrace S pe) (intrinsicEdgeRayTrace S re) :=
      congrArg (fun U : Set ℂ => I.h '' U) hsource
    _ = _ := congrArg (fun U : Set ℂ => I.h '' U)
      (congrArg₂ closedBetween (intrinsicGeodesicSource_trace W H G hp pe)
        (intrinsicGeodesicSource_trace W H G hp re))

end DirectedDistances.PaperProofs.Section3
end
