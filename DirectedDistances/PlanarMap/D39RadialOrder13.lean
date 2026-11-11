/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder12

/-! # Image argument order helpers toward Proposition 5.16 -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

/-- Helper toward Proposition 5.16: a continuous real lift with total
increment one turn visits two distinct interior angular classes in the order
of their representatives in that turn. -/
theorem d39_continuous_lift_lattice_hits_order
    (L : C(unitInterval, ℝ)) (a b aRep bRep period : ℝ)
    (ta tb : unitInterval)
    (hperiod : 0 < period)
    (hrepA : ∃ m : ℤ, aRep = a + period * (m : ℝ))
    (hrepB : ∃ m : ℤ, bRep = b + period * (m : ℝ))
    (hwindow : L 0 < aRep ∧ aRep < bRep ∧ bRep < L 0 + period)
    (hend : L 1 = L 0 + period)
    (haUnique : ∀ t : unitInterval,
      (∃ k : ℤ, L t = a + period * (k : ℝ)) ↔ t = ta)
    (hbUnique : ∀ t : unitInterval,
      (∃ k : ℤ, L t = b + period * (k : ℝ)) ↔ t = tb) :
    (ta : ℝ) < (tb : ℝ) := by
  have hclassA (t : unitInterval) :
      (∃ k : ℤ, L t = aRep + period * (k : ℝ)) ↔
        ∃ k : ℤ, L t = a + period * (k : ℝ) := by
    constructor
    · rintro ⟨k, hk⟩
      rcases hrepA with ⟨m, hm⟩
      refine ⟨m + k, ?_⟩
      rw [hk, hm]
      push_cast
      ring
    · rintro ⟨k, hk⟩
      rcases hrepA with ⟨m, hm⟩
      refine ⟨k - m, ?_⟩
      rw [hk, hm]
      push_cast
      ring
  have hclassB (t : unitInterval) :
      (∃ k : ℤ, L t = bRep + period * (k : ℝ)) ↔
        ∃ k : ℤ, L t = b + period * (k : ℝ) := by
    constructor
    · rintro ⟨k, hk⟩
      rcases hrepB with ⟨m, hm⟩
      refine ⟨m + k, ?_⟩
      rw [hk, hm]
      push_cast
      ring
    · rintro ⟨k, hk⟩
      rcases hrepB with ⟨m, hm⟩
      refine ⟨k - m, ?_⟩
      rw [hk, hm]
      push_cast
      ring
  have haRepUnique (t : unitInterval) :
      (∃ k : ℤ, L t = aRep + period * (k : ℝ)) ↔ t = ta :=
    (hclassA t).trans (haUnique t)
  have hbRepUnique (t : unitInterval) :
      (∃ k : ℤ, L t = bRep + period * (k : ℝ)) ↔ t = tb :=
    (hclassB t).trans (hbUnique t)
  have align (c : ℝ) (tc : unitInterval)
      (hc0 : L 0 < c) (hc1 : c < L 0 + period)
      (hunique : ∀ t : unitInterval,
        (∃ k : ℤ, L t = c + period * (k : ℝ)) ↔ t = tc) :
      L tc = c := by
    obtain ⟨k, hk⟩ := (hunique tc).2 rfl
    by_cases hk0 : k = 0
    · simpa [hk0] using hk
    · by_cases hkpos : 0 < k
      · have hkposR : 0 < (k : ℝ) := by exact_mod_cast hkpos
        have hval : c ∈ Set.Icc (L 0) (L tc) := by
          constructor
          · exact hc0.le
          · rw [hk]
            nlinarith [hperiod]
        obtain ⟨s, hs⟩ := (intermediate_value_univ 0 tc L.continuous) hval
        have hst : s = tc := (hunique s).1 ⟨0, by simpa using hs⟩
        rw [hst, hk] at hs
        have hfalse : False := by nlinarith [hs, hperiod, hkposR]
        exact hfalse.elim
      · have hkneg : k < 0 := lt_of_le_of_ne (le_of_not_gt hkpos) hk0
        have hknegR : (k : ℝ) < 0 := by exact_mod_cast hkneg
        have hcEnd : c < L 1 := by rw [hend]; exact hc1
        have hval : c ∈ Set.Icc (L tc) (L 1) := by
          constructor
          · rw [hk]
            nlinarith [hperiod]
          · exact hcEnd.le
        obtain ⟨s, hs⟩ := (intermediate_value_univ tc 1 L.continuous) hval
        have hst : s = tc := (hunique s).1 ⟨0, by simpa using hs⟩
        rw [hst, hk] at hs
        have hfalse : False := by nlinarith [hs, hperiod, hknegR]
        exact hfalse.elim
  have haValue : L ta = aRep :=
    align aRep ta hwindow.1 (lt_trans hwindow.2.1 hwindow.2.2) haRepUnique
  have hbValue : L tb = bRep :=
    align bRep tb (lt_trans hwindow.1 hwindow.2.1) hwindow.2.2 hbRepUnique
  let q : C(unitInterval, unitInterval) := ⟨fun s =>
    ⟨(tb : ℝ) * (s : ℝ),
      mul_nonneg tb.property.1 s.property.1,
      le_trans
        (by
          have hmul := mul_le_mul_of_nonneg_left s.property.2 tb.property.1
          nlinarith)
        tb.property.2⟩, by continuity⟩
  let F : C(unitInterval, ℝ) := L.comp q
  have hF0 : F 0 = L 0 := by
    apply congrArg L
    apply Subtype.ext
    simp [q]
  have hF1 : F 1 = L tb := by
    apply congrArg L
    apply Subtype.ext
    simp [q]
  have hval : aRep ∈ Set.Icc (F 0) (F 1) := by
    rw [hF0, hF1, hbValue]
    exact ⟨hwindow.1.le, hwindow.2.1.le⟩
  obtain ⟨s, hs⟩ := (intermediate_value_univ 0 1 F.continuous) hval
  have hs' : L (q s) = aRep := by simpa [F] using hs
  have hqHit : ∃ k : ℤ, L (q s) = aRep + period * (k : ℝ) := by
    exact ⟨0, by rw [hs']; ring⟩
  have hqTime : q s = ta := (haRepUnique (q s)).1 hqHit
  have hqle : (q s : ℝ) ≤ (tb : ℝ) := by
    dsimp [q]
    have hmul := mul_le_mul_of_nonneg_left s.property.2 tb.property.1
    nlinarith
  have hle : (ta : ℝ) ≤ (tb : ℝ) := by
    calc
      (ta : ℝ) = (q s : ℝ) := congrArg Subtype.val hqTime.symm
      _ ≤ (tb : ℝ) := hqle
  have hne : (ta : ℝ) ≠ (tb : ℝ) := by
    intro h
    have hsub : ta = tb := Subtype.ext h
    have heq := congrArg L hsub
    rw [haValue, hbValue] at heq
    exact (ne_of_lt hwindow.2.1) heq
  exact lt_of_le_of_ne hle hne

/-- Helper toward Proposition 5.16: one circle radius can lie inside each
source germ segment while its image lies inside all three target germ disks. -/
theorem d39_small_radius_for_three_image_germs
    (K : ℂ ≃ₜ ℂ) (hK0 : K 0 = 0)
    (u v w u' v' w' : ℂ) (rU rV rW sU sV sW : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
    (hrU : 0 < rU) (hrV : 0 < rV) (hrW : 0 < rW)
    (hsU : 0 < sU) (hsV : 0 < sV) (hsW : 0 < sW) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < rU * ‖u‖ ∧ ρ < rV * ‖v‖ ∧
      ρ < rW * ‖w‖ ∧ ∀ z : ℂ, ‖z‖ ≤ ρ →
        ‖K z‖ < min (sU * ‖u'‖) (min (sV * ‖v'‖) (sW * ‖w'‖)) := by
  have hu'Norm : 0 < ‖u'‖ := norm_pos_iff.mpr hu'
  have hv'Norm : 0 < ‖v'‖ := norm_pos_iff.mpr hv'
  have hw'Norm : 0 < ‖w'‖ := norm_pos_iff.mpr hw'
  have hR : 0 < min (sU * ‖u'‖) (min (sV * ‖v'‖) (sW * ‖w'‖)) := by
    positivity
  exact d39_small_radius_for_three_germs K hK0 u v w rU rV rW _
    hu hv hw hrU hrV hrW hR

/-- Helper toward Proposition 5.16: the image of a rotated circle under an
orientation-preserving homeomorphism has a continuous logarithm lift whose
imaginary endpoint increment is `2π`. -/
theorem d39_oriented_image_rotatedCirclePath_has_lift_increment
    {K : ℂ ≃ₜ ℂ} (hK : OrientationPreserving K) {ρ α : ℝ}
    (hρ : 0 < ρ) :
    ∃ φ : C(unitInterval, ℂ),
      (∀ t, Complex.exp (φ t) =
        ((d39RotatedCirclePath ρ α).map K.continuous) t - K 0) ∧
        (φ 1).im - (φ 0).im = 2 * Real.pi := by
  exact d39_hasWinding_one_lift_imaginary_increment
    (d39_oriented_image_rotatedCirclePath_hasWinding_one hK hρ)

/-- Helper toward Proposition 5.16: along a winding lift of a small image
circle, the target argument lattice of a radial germ is hit exactly at the
source circle's unique intersection with that germ. -/
theorem d39_image_lift_ray_argument_has_unique_time
    (K : ℂ ≃ₜ ℂ) (hK0 : K 0 = 0)
    (u u' : ℂ) (r s ρ α : ℝ)
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hρ : 0 < ρ)
    (hρr : ρ < r * ‖u‖)
    (hKball : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖K z‖ < s * ‖u'‖)
    (himage : K '' {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ r ∧
        z = (q : ℂ) * u} =
      {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'})
    (hmiss : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (φ : C(unitInterval, ℂ))
    (hφ : ∀ t, Complex.exp (φ t) =
      ((d39RotatedCirclePath ρ α).map K.continuous) t - K 0)
    (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (∃ k : ℤ, (φ t).im = u'.arg + 2 * Real.pi * (k : ℝ)) ↔
      (t : ℝ) = d39RotatedCircleRayHitTime α u := by
  have hφ' : Complex.exp (φ t) = K (d39RotatedCirclePath ρ α t) := by
    simpa [hK0] using hφ t
  have hcircleNorm := d39_rotatedCirclePath_norm (α := α) hρ t
  have hKcircle : ‖K (d39RotatedCirclePath ρ α t)‖ < s * ‖u'‖ :=
    hKball _ (by rw [hcircleNorm])
  have hhitIff := d39_imageRotatedCirclePath_image_germ_hit_iff
    K u u' r s ρ α hu hu' hρ hρr himage hmiss t ht0 ht1
  constructor
  · rintro ⟨k, harg⟩
    obtain ⟨q, hq, hexp⟩ :=
      d39_exp_argument_congruent_to_ray_lies_on_ray (φ t) u' hu' k harg
    have hpoint : K (d39RotatedCirclePath ρ α t) = (q : ℂ) * u' :=
      hφ'.symm.trans hexp
    have hKcircle' := hKcircle
    rw [hpoint, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq] at hKcircle'
    have hqs : q ≤ s := by nlinarith [norm_pos_iff.mpr hu']
    have hsegment :
        ((d39RotatedCirclePath ρ α).map K.continuous) t ∈
          {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'} := by
      exact ⟨q, hq.le, hqs, hpoint⟩
    exact hhitIff.mp hsegment
  · intro htime
    have hsegment := hhitIff.mpr htime
    rcases hsegment with ⟨q, hq0, hqs, hpoint⟩
    have hsourceNe : d39RotatedCirclePath ρ α t ≠ 0 := by
      intro hz
      have hnorm := d39_rotatedCirclePath_norm (α := α) hρ t
      rw [hz] at hnorm
      exact (ne_of_gt hρ) (by simpa using hnorm.symm)
    have himageNe : K (d39RotatedCirclePath ρ α t) ≠ 0 := by
      intro hz
      apply hsourceNe
      apply K.injective
      calc
        K (d39RotatedCirclePath ρ α t) = 0 := hz
        _ = K 0 := hK0.symm
    have hqpos : 0 < q := by
      by_contra hnot
      have hqzero : q = 0 := le_antisymm (le_of_not_gt hnot) hq0
      apply himageNe
      change K (d39RotatedCirclePath ρ α t) = (q : ℂ) * u' at hpoint
      rw [hpoint, hqzero]
      simp
    obtain ⟨k, harg⟩ := d39_exp_positive_ray_argument_lift
      (φ t) u' q hu' hqpos (hφ'.trans hpoint)
    exact ⟨k, harg⟩



































end DirectedDistances.PlanarMap

end
