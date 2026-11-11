module

public import DirectedDistances.PlanarMap.PlaneRealization
public import Mathlib.Data.List.Pairwise
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring






public section
namespace DirectedDistances.PlanarMap

open Set

noncomputable section



@[expose] def segmentArc (a b : ℂ) : Polyline := ⟨[a, b], by simp⟩



@[expose] def roofArc (a b : ℂ) (H M : ℝ) : Polyline :=
  ⟨[a] ++ (if a.im = H then [] else
    [⟨a.re + (H - a.im) / M, H⟩]) ++
      (if b.im = H then [] else
        [⟨b.re - (H - b.im) / M, H⟩]) ++ [b], by simp⟩



@[expose] def roofHeight (a b : ℂ) (H M x : ℝ) : ℝ :=
  min H (min (a.im + M * (x - a.re)) (b.im + M * (b.re - x)))



@[expose] def segmentHeight (a b : ℂ) (x : ℝ) : ℝ :=
  a.im + ((b.im - a.im) / (b.re - a.re)) * (x - a.re)



theorem roofArc_start (a b : ℂ) (H M : ℝ) : (roofArc a b H M).start = a := by
  simp [roofArc, Polyline.start]



theorem roofArc_finish (a b : ℂ) (H M : ℝ) : (roofArc a b H M).finish = b := by
  simp [roofArc, Polyline.finish]



theorem roofArc_length (a b : ℂ) (H M : ℝ) : 2 ≤ (roofArc a b H M).points.length := by
  by_cases ha : a.im = H <;> by_cases hb : b.im = H <;>
    simp [roofArc, ha, hb]



private theorem pairwise_three {a b c : ℂ} (hab : a.re < b.re)
    (hbc : b.re < c.re) :
    List.Pairwise (fun z w : ℂ => z.re < w.re) [a, b, c] := by
  have hac := lt_trans hab hbc
  simp [List.pairwise_cons, hab, hbc, hac]



private theorem pairwise_four {a b c d : ℂ} (hab : a.re < b.re)
    (hbc : b.re < c.re) (hcd : c.re < d.re) :
    List.Pairwise (fun z w : ℂ => z.re < w.re) [a, b, c, d] := by
  have hac := lt_trans hab hbc
  have hbd := lt_trans hbc hcd
  have had := lt_trans hac hcd
  simp [List.pairwise_cons, hab, hbc, hcd, hac, hbd, had]



theorem roofArc_points_pairwise {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    List.Pairwise (fun z w : ℂ => z.re < w.re) (roofArc a b H M).points := by
  let u := (H - a.im) / M
  let v := (H - b.im) / M
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr ha) hM.le
  have hv0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr hb) hM.le
  have huv : u + v < b.re - a.re := by simpa [u, v] using hfit
  have hab : a.re < b.re := by linarith
  have hleftRight : a.re + u < b.re - v := by linarith
  by_cases haH : a.im = H <;> by_cases hbH : b.im = H
  · simpa [roofArc, haH, hbH] using
      (show List.Pairwise (fun z w : ℂ => z.re < w.re) [a, b] by simp [hab])
  · have hbLt : b.im < H := lt_of_le_of_ne hb hbH
    have hv : 0 < v := div_pos (sub_pos.mpr hbLt) hM
    have haB : a.re < b.re - v := by simpa [u, haH] using hleftRight
    have hBb : b.re - v < b.re := by linarith
    have hp := pairwise_three (a := a) (b := ⟨b.re - v, H⟩) (c := b) haB hBb
    simpa [roofArc, haH, hbH] using hp
  · have haLt : a.im < H := lt_of_le_of_ne ha haH
    have hu : 0 < u := div_pos (sub_pos.mpr haLt) hM
    have hAa : a.re < a.re + u := by linarith
    have hAb : a.re + u < b.re := by simpa [v, hbH] using hleftRight
    have hp := pairwise_three (a := a) (b := ⟨a.re + u, H⟩) (c := b) hAa hAb
    simpa [roofArc, haH, hbH] using hp
  · have haLt : a.im < H := lt_of_le_of_ne ha haH
    have hbLt : b.im < H := lt_of_le_of_ne hb hbH
    have hu : 0 < u := div_pos (sub_pos.mpr haLt) hM
    have hv : 0 < v := div_pos (sub_pos.mpr hbLt) hM
    have hAa : a.re < a.re + u := by linarith
    have hAB : a.re + u < b.re - v := hleftRight
    have hBb : b.re - v < b.re := by linarith
    have hp := pairwise_four (a := a) (b := ⟨a.re + u, H⟩)
      (c := ⟨b.re - v, H⟩) (d := b) hAa hAB hBb
    simpa [roofArc, haH, hbH] using hp



theorem roofArc_initialSlope {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im < H) :
    ((roofArc a b H M).initialDirection.im /
      (roofArc a b H M).initialDirection.re) = M := by
  have hsecond : (roofArc a b H M).point 1 =
      ⟨a.re + (H - a.im) / M, H⟩ := by
    simp [Polyline.point, roofArc, ne_of_lt ha]
  rw [Polyline.initialDirection, roofArc_start, hsecond]
  simp only [Complex.sub_im, Complex.sub_re]
  have hnum : H - a.im ≠ 0 := ne_of_gt (sub_pos.mpr ha)
  have hMne : M ≠ 0 := ne_of_gt hM
  field_simp [hnum, hMne]
  ring



theorem roofArc_initialSlope_top {a b : ℂ} {H M : ℝ}
    (ha : a.im = H) :
    ((roofArc a b H M).initialDirection.im /
      (roofArc a b H M).initialDirection.re) = 0 := by
  have hsecond : (roofArc a b H M).point 1 =
      ⟨b.re - (H - b.im) / M, H⟩ := by
    by_cases hbH : b.im = H
    · have hbval : b = (⟨b.re, H⟩ : ℂ) := by
        apply Complex.ext <;> simp [hbH]
      simpa [Polyline.point, roofArc, ha, hbH] using hbval
    · simp [Polyline.point, roofArc, ha, hbH]
  rw [Polyline.initialDirection, roofArc_start, hsecond, Complex.sub_im,
    Complex.sub_re]
  simp [ha]



theorem roofArc_reverse_initialSlope {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (hb : b.im < H) :
    ((roofArc a b H M).reverse.initialDirection.im /
      (roofArc a b H M).reverse.initialDirection.re) = -M := by
  have hsecond : (roofArc a b H M).reverse.point 1 =
      ⟨b.re - (H - b.im) / M, H⟩ := by
    simp [Polyline.point, Polyline.reverse, roofArc, ne_of_lt hb]
  rw [Polyline.initialDirection, Polyline.start_reverse, roofArc_finish,
    hsecond, Complex.sub_im, Complex.sub_re]
  have hnum : H - b.im ≠ 0 := ne_of_gt (sub_pos.mpr hb)
  have hMne : M ≠ 0 := ne_of_gt hM
  field_simp [hnum, hMne]
  rw [show b.re * M - (H - b.im) - b.re * M = -(H - b.im) by ring]
  rw [div_eq_mul_inv, inv_neg, mul_neg, mul_inv_cancel₀ hnum]



theorem roofArc_initialDirection_re_pos {a b : ℂ} {H M : ℝ}
    (hM : 0 < M) (ha : a.im < H) :
    0 < (roofArc a b H M).initialDirection.re := by
  have hsecond : (roofArc a b H M).point 1 =
      ⟨a.re + (H - a.im) / M, H⟩ := by
    simp [Polyline.point, roofArc, ne_of_lt ha]
  rw [Polyline.initialDirection, roofArc_start, hsecond, Complex.sub_re]
  have hpos : 0 < (H - a.im) / M := div_pos (sub_pos.mpr ha) hM
  linarith



theorem roofArc_initialDirection_re_pos_top {a b : ℂ} {H M : ℝ}
    (ha : a.im = H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    0 < (roofArc a b H M).initialDirection.re := by
  have hsecond : (roofArc a b H M).point 1 =
      ⟨b.re - (H - b.im) / M, H⟩ := by
    by_cases hbH : b.im = H
    · have hbval : b = (⟨b.re, H⟩ : ℂ) := by
        apply Complex.ext <;> simp [hbH]
      simpa [Polyline.point, roofArc, ha, hbH] using hbval
    · simp [Polyline.point, roofArc, ha, hbH]
  have hfit' : (H - b.im) / M < b.re - a.re := by
    simpa [ha] using hfit
  rw [Polyline.initialDirection, roofArc_start, hsecond, Complex.sub_re]
  linarith



theorem roofArc_initialDirection_re_pos_of_bounds {a b : ℂ} {H M : ℝ}
    (hM : 0 < M) (ha : a.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    0 < (roofArc a b H M).initialDirection.re := by
  rcases eq_or_lt_of_le ha with heq | hlt
  · exact roofArc_initialDirection_re_pos_top heq hfit
  · exact roofArc_initialDirection_re_pos hM hlt



theorem roofArc_initialDirection_geom {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im < H) :
    0 < (roofArc a b H M).initialDirection.re ∧
      (roofArc a b H M).initialDirection.im =
        M * (roofArc a b H M).initialDirection.re := by
  have hsecond : (roofArc a b H M).point 1 =
      ⟨a.re + (H - a.im) / M, H⟩ := by
    simp [Polyline.point, roofArc, ne_of_lt ha]
  have hre : 0 < (roofArc a b H M).initialDirection.re :=
    roofArc_initialDirection_re_pos hM ha
  have hre' : (roofArc a b H M).initialDirection.re = (H - a.im) / M := by
    rw [Polyline.initialDirection, roofArc_start, hsecond, Complex.sub_re]
    simp
  have him' : (roofArc a b H M).initialDirection.im = H - a.im := by
    rw [Polyline.initialDirection, roofArc_start, hsecond, Complex.sub_im]
  have him : (roofArc a b H M).initialDirection.im =
      M * (roofArc a b H M).initialDirection.re := by
    rw [him', hre']
    field_simp [ne_of_gt hM]
  exact ⟨hre, him⟩



theorem roofArc_reverse_initialDirection_geom {a b : ℂ} {H M : ℝ}
    (hM : 0 < M) (hb : b.im < H) :
    (roofArc a b H M).reverse.initialDirection.re < 0 ∧
      (roofArc a b H M).reverse.initialDirection.im =
        M * (-(roofArc a b H M).reverse.initialDirection.re) := by
  have hsecond : (roofArc a b H M).reverse.point 1 =
      ⟨b.re - (H - b.im) / M, H⟩ := by
    simp [Polyline.point, Polyline.reverse, roofArc, ne_of_lt hb]
  have hre : (roofArc a b H M).reverse.initialDirection.re =
      -((H - b.im) / M) := by
    rw [Polyline.initialDirection, Polyline.start_reverse, roofArc_finish,
      hsecond, Complex.sub_re]
    simp
  have hneg : (roofArc a b H M).reverse.initialDirection.re < 0 := by
    have hv := div_pos (sub_pos.mpr hb) hM
    rw [hre]
    linarith
  have him' : (roofArc a b H M).reverse.initialDirection.im = H - b.im := by
    rw [Polyline.initialDirection, Polyline.start_reverse, roofArc_finish,
      hsecond, Complex.sub_im]
  have him : (roofArc a b H M).reverse.initialDirection.im =
      M * (-(roofArc a b H M).reverse.initialDirection.re) := by
    rw [him', hre]
    simp
    field_simp [ne_of_gt hM]
  exact ⟨hneg, him⟩



theorem roofArc_initialDirection_top_geom {a b : ℂ} {H M : ℝ}
    (_hM : 0 < M) (ha : a.im = H) (_hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    0 < (roofArc a b H M).initialDirection.re ∧
      (roofArc a b H M).initialDirection.im = 0 := by
  have hsecond : (roofArc a b H M).point 1 =
      ⟨b.re - (H - b.im) / M, H⟩ := by
    by_cases hbH : b.im = H
    · have hbval : b = (⟨b.re, H⟩ : ℂ) := by
        apply Complex.ext <;> simp [hbH]
      simpa [Polyline.point, roofArc, ha, hbH] using hbval
    · simp [Polyline.point, roofArc, ha, hbH]
  have hre : 0 < (roofArc a b H M).initialDirection.re :=
    roofArc_initialDirection_re_pos_top ha hfit
  have him : (roofArc a b H M).initialDirection.im = 0 := by
    rw [Polyline.initialDirection, roofArc_start, hsecond, Complex.sub_im]
    simp [ha]
  exact ⟨hre, him⟩



theorem roofArc_reverse_initialDirection_top_geom {a b : ℂ} {H M : ℝ}
    (_hM : 0 < M) (_ha : a.im ≤ H) (hb : b.im = H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    (roofArc a b H M).reverse.initialDirection.re < 0 ∧
      (roofArc a b H M).reverse.initialDirection.im = 0 := by
  have hsecond : (roofArc a b H M).reverse.point 1 =
      ⟨a.re + (H - a.im) / M, H⟩ := by
    by_cases haH : a.im = H
    · have haval : a = (⟨a.re, H⟩ : ℂ) := by
        apply Complex.ext <;> simp [haH]
      simpa [Polyline.point, Polyline.reverse, roofArc, haH, hb] using haval
    · simp [Polyline.point, Polyline.reverse, roofArc, haH, hb]
  have hfit' : (H - a.im) / M < b.re - a.re := by
    simpa [hb] using hfit
  have hneg : (roofArc a b H M).reverse.initialDirection.re < 0 := by
    rw [Polyline.initialDirection, Polyline.start_reverse, roofArc_finish,
      hsecond, Complex.sub_re]
    simp
    linarith
  have him : (roofArc a b H M).reverse.initialDirection.im = 0 := by
    rw [Polyline.initialDirection, Polyline.start_reverse, roofArc_finish,
      hsecond, Complex.sub_im]
    simp [hb]
  exact ⟨hneg, him⟩



theorem segmentArc_start (a b : ℂ) : (segmentArc a b).start = a := by
  simp [segmentArc, Polyline.start]



theorem segmentArc_finish (a b : ℂ) : (segmentArc a b).finish = b := by
  simp [segmentArc, Polyline.finish]



theorem segmentArc_length (a b : ℂ) : 2 ≤ (segmentArc a b).points.length := by
  simp [segmentArc]



theorem segmentArc_points_pairwise {a b : ℂ} (hab : a.re < b.re) :
    List.Pairwise (fun z w : ℂ => z.re < w.re) (segmentArc a b).points := by
  simp [segmentArc, hab]



theorem segmentArc_initialDirection_re_pos {a b : ℂ} (hab : a.re < b.re) :
    0 < (segmentArc a b).initialDirection.re := by
  simp [segmentArc, Polyline.initialDirection, Polyline.point, Polyline.start,
    Complex.sub_re]
  exact hab



theorem mem_segment_iff_height {a b z : ℂ} (hab : a.re < b.re) :
    z ∈ segment ℝ a b ↔
      a.re ≤ z.re ∧ z.re ≤ b.re ∧ z.im = segmentHeight a b z.re := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hre : (((1 - t) • a + t • b : ℂ).re) =
        (1 - t) * a.re + t * b.re := by simp [Complex.real_smul]
    have him : (((1 - t) • a + t • b : ℂ).im) =
        (1 - t) * a.im + t * b.im := by simp
    rw [hre, him]
    refine ⟨?_, ?_⟩
    · nlinarith [ht.1, ht.2, hab]
    · refine ⟨?_, ?_⟩
      · nlinarith [ht.1, ht.2, hab]
      · unfold segmentHeight
        have hden : b.re - a.re ≠ 0 := ne_of_gt (sub_pos.mpr hab)
        field_simp [hden]
        ring
  · rintro ⟨hleft, hright, him⟩
    let t := (z.re - a.re) / (b.re - a.re)
    have hden : 0 < b.re - a.re := sub_pos.mpr hab
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hleft) hden.le
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one hden]
      linarith
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    apply Complex.ext
    · have hre : (((1 - t) • a + t • b : ℂ).re) =
          (1 - t) * a.re + t * b.re := by
        simp [Complex.real_smul]
      rw [hre]
      dsimp [t]
      field_simp [ne_of_gt hden]
      ; ring
    · have him' : (((1 - t) • a + t • b : ℂ).im) =
          (1 - t) * a.im + t * b.im := by simp
      rw [him', him]
      unfold segmentHeight
      dsimp [t]
      field_simp [ne_of_gt hden]
      ; ring



theorem segmentArc_image {a b : ℂ} (hab : a.re < b.re) :
    (segmentArc a b).image =
      {z | a.re ≤ z.re ∧ z.re ≤ b.re ∧ z.im = segmentHeight a b z.re} := by
  ext z
  simp only [Polyline.image, segmentArc, Polyline.start, List.head_cons,
    mem_union, mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨i, hi, hz⟩)
    · exact ⟨le_rfl, hab.le, by simp [segmentHeight]⟩
    · have hi' : i + 1 < 2 := by simpa using hi
      have hi0 : i = 0 := by omega
      subst i
      change z ∈ segment ℝ a b at hz
      exact (mem_segment_iff_height hab).mp hz
  · rintro ⟨hleft, hright, hh⟩
    exact Or.inr ⟨0, by simp,
      (mem_segment_iff_height hab).mpr ⟨hleft, hright, hh⟩⟩



theorem roofHeight_le_top (a b : ℂ) (H M x : ℝ) : roofHeight a b H M x ≤ H :=
  min_le_left _ _



theorem continuous_roofHeight (a b : ℂ) (H M : ℝ) :
    Continuous (roofHeight a b H M) := by
  unfold roofHeight
  exact continuous_const.min
    ((continuous_const.add (continuous_const.mul
      (continuous_id.sub continuous_const))).min
      (continuous_const.add (continuous_const.mul
        (continuous_const.sub continuous_id))))



theorem segmentHeight_separation {a b : ℂ} {H M M' : ℝ}
    (hM' : M' < M) (g : ℝ → ℝ)
    (hleft : ∀ x ∈ Icc a.re b.re,
      g x ≤ a.im + M' * (x - a.re) ∧
      g x ≤ b.im + M' * (b.re - x))
    (hbelow : ∀ x ∈ Ioo a.re b.re, g x < H) :
    ∀ x ∈ Ioo a.re b.re, g x < roofHeight a b H M x := by
  intro x hx
  have hxL : 0 < x - a.re := sub_pos.mpr hx.1
  have hxR : 0 < b.re - x := sub_pos.mpr hx.2
  have hxIcc : x ∈ Icc a.re b.re := ⟨hx.1.le, hx.2.le⟩
  obtain ⟨hgL, hgR⟩ := hleft x hxIcc
  have hML : M' * (x - a.re) < M * (x - a.re) :=
    mul_lt_mul_of_pos_right hM' hxL
  have hMR : M' * (b.re - x) < M * (b.re - x) :=
    mul_lt_mul_of_pos_right hM' hxR
  have hleft' : g x < a.im + M * (x - a.re) := by linarith
  have hright' : g x < b.im + M * (b.re - x) := by linarith
  exact lt_min (hbelow x hx) (lt_min hleft' hright')



theorem segmentHeight_lt_roofHeight_of_slope {a b : ℂ} {H M M' : ℝ}
    (hab : a.re < b.re) (ha : a.im < H) (hb : b.im ≤ H)
    (hMM' : M' < M)
    (hslope : |(b.im - a.im) / (b.re - a.re)| ≤ M') :
    ∀ x ∈ Ioo a.re b.re, segmentHeight a b x < roofHeight a b H M x := by
  let s := (b.im - a.im) / (b.re - a.re)
  have hden : 0 < b.re - a.re := sub_pos.mpr hab
  have hsbounds : -M' ≤ s ∧ s ≤ M' := by
    dsimp [s]
    exact abs_le.mp hslope
  have hright (x : ℝ) :
      segmentHeight a b x = b.im + s * (x - b.re) := by
    unfold segmentHeight
    dsimp [s]
    field_simp [ne_of_gt hden]
    ring
  have hleft (x : ℝ) (hx : x ∈ Icc a.re b.re) :
      segmentHeight a b x ≤ a.im + M' * (x - a.re) := by
    have hx0 : 0 ≤ x - a.re := sub_nonneg.mpr hx.1
    change a.im + s * (x - a.re) ≤ a.im + M' * (x - a.re)
    nlinarith [mul_le_mul_of_nonneg_right hsbounds.2 hx0]
  have hrightBound (x : ℝ) (hx : x ∈ Icc a.re b.re) :
      segmentHeight a b x ≤ b.im + M' * (b.re - x) := by
    rw [hright]
    have hx0 : 0 ≤ b.re - x := sub_nonneg.mpr hx.2
    have hsneg : -s ≤ M' := by linarith [hsbounds.1]
    nlinarith [mul_le_mul_of_nonneg_right hsneg hx0]
  have hbelow (x : ℝ) (hx : x ∈ Ioo a.re b.re) :
      segmentHeight a b x < H := by
    let t := (x - a.re) / (b.re - a.re)
    have ht0 : 0 < t := by
      dsimp [t]
      exact div_pos (sub_pos.mpr hx.1) hden
    have ht1 : t < 1 := by
      dsimp [t]
      rw [div_lt_one hden]
      linarith [hx.2]
    have heq : segmentHeight a b x = (1 - t) * a.im + t * b.im := by
      unfold segmentHeight
      dsimp [t]
      field_simp [ne_of_gt hden]
      ring
    have hleftWeight : (1 - t) * a.im < (1 - t) * H :=
      mul_lt_mul_of_pos_left ha (sub_pos.mpr ht1)
    have hrightWeight : t * b.im ≤ t * H :=
      mul_le_mul_of_nonneg_left hb ht0.le
    rw [heq]
    nlinarith [hleftWeight, hrightWeight]
  exact segmentHeight_separation hMM' (segmentHeight a b)
    (fun x hx => ⟨hleft x hx, hrightBound x hx⟩) hbelow



theorem roofHeight_start {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    roofHeight a b H M a.re = a.im := by
  have hsum : H - a.im + (H - b.im) < M * (b.re - a.re) := by
    rw [← add_div] at hfit
    simpa [mul_comm] using (div_lt_iff₀ hM).mp hfit
  have ha0 : 0 ≤ H - a.im := sub_nonneg.mpr ha
  have hb0 : 0 ≤ H - b.im := sub_nonneg.mpr hb
  unfold roofHeight
  rw [sub_self, mul_zero, add_zero]
  have hright : a.im ≤ b.im + M * (b.re - a.re) := by
    nlinarith [hsum, ha0, hb0]
  apply le_antisymm
  · calc
      min H (min a.im (b.im + M * (b.re - a.re))) ≤
          min a.im (b.im + M * (b.re - a.re)) := min_le_right _ _
      _ ≤ a.im := min_le_left _ _
  · apply le_min
    · exact ha
    · exact le_min le_rfl hright



theorem roofHeight_finish {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    roofHeight a b H M b.re = b.im := by
  have hsum : H - a.im + (H - b.im) < M * (b.re - a.re) := by
    rw [← add_div] at hfit
    simpa [mul_comm] using (div_lt_iff₀ hM).mp hfit
  have ha0 : 0 ≤ H - a.im := sub_nonneg.mpr ha
  have hb0 : 0 ≤ H - b.im := sub_nonneg.mpr hb
  unfold roofHeight
  rw [sub_self, mul_zero, add_zero]
  have hleft : b.im ≤ a.im + M * (b.re - a.re) := by
    nlinarith [hsum, ha0, hb0]
  apply le_antisymm
  · calc
      min H (min (a.im + M * (b.re - a.re)) b.im) ≤
          min (a.im + M * (b.re - a.re)) b.im := min_le_right _ _
      _ ≤ b.im := min_le_right _ _
  · apply le_min
    · exact hb
    · exact le_min hleft le_rfl

private theorem roofHeight_eq_rising {a b : ℂ} {H M x : ℝ}
    (hM : 0 < M) (_ha : a.im ≤ H) (_hb : b.im ≤ H)
    (_hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re)
    (_hleft : a.re ≤ x)
    (hright : x ≤ a.re + (H - a.im) / M) :
    roofHeight a b H M x = a.im + M * (x - a.re) := by
  have hMne : M ≠ 0 := ne_of_gt hM
  have hmulA : M * ((H - a.im) / M) = H - a.im := by
    field_simp [hMne]
  have hmulB : M * ((H - b.im) / M) = H - b.im := by
    field_simp [hMne]
  have hLR : a.re + (H - a.im) / M ≤ b.re - (H - b.im) / M := by
    linarith
  have hMx : M * (x - a.re) ≤ M * ((H - a.im) / M) :=
    mul_le_mul_of_nonneg_left (by linarith) hM.le
  have hA : a.im + M * (x - a.re) ≤ H := by
    nlinarith [hMx, hmulA]
  have hMLR := mul_le_mul_of_nonneg_left hLR hM.le
  have hBAtL : H ≤ b.im + M * (b.re -
      (a.re + (H - a.im) / M)) := by
    nlinarith [hMLR, hmulA, hmulB]
  have hBMono := mul_le_mul_of_nonneg_left
    (show b.re - (a.re + (H - a.im) / M) ≤ b.re - x by linarith) hM.le
  have hB : H ≤ b.im + M * (b.re - x) := by
    linarith
  unfold roofHeight
  rw [min_eq_left (show a.im + M * (x - a.re) ≤
    b.im + M * (b.re - x) by linarith)]
  exact min_eq_right hA

private theorem roofHeight_eq_top {a b : ℂ} {H M x : ℝ}
    (hM : 0 < M) (_ha : a.im ≤ H) (_hb : b.im ≤ H)
    (_hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re)
    (hleft : a.re + (H - a.im) / M ≤ x)
    (_hright : x ≤ b.re - (H - b.im) / M) :
    roofHeight a b H M x = H := by
  have hMne : M ≠ 0 := ne_of_gt hM
  have hmulA : M * ((H - a.im) / M) = H - a.im := by
    field_simp [hMne]
  have hmulB : M * ((H - b.im) / M) = H - b.im := by
    field_simp [hMne]
  have hMx := mul_le_mul_of_nonneg_left
    (show (H - a.im) / M ≤ x - a.re by linarith) hM.le
  have hA : H ≤ a.im + M * (x - a.re) := by
    nlinarith [hmulA, hMx]
  have hMx' := mul_le_mul_of_nonneg_left
    (show (H - b.im) / M ≤ b.re - x by linarith) hM.le
  have hB : H ≤ b.im + M * (b.re - x) := by
    nlinarith [hmulB, hMx']
  unfold roofHeight
  rw [min_eq_left (le_min hA hB)]

private theorem roofHeight_eq_falling {a b : ℂ} {H M x : ℝ}
    (hM : 0 < M) (_ha : a.im ≤ H) (_hb : b.im ≤ H)
    (_hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re)
    (hleft : b.re - (H - b.im) / M ≤ x) (_hright : x ≤ b.re) :
    roofHeight a b H M x = b.im + M * (b.re - x) := by
  have hMne : M ≠ 0 := ne_of_gt hM
  have hmulA : M * ((H - a.im) / M) = H - a.im := by
    field_simp [hMne]
  have hmulB : M * ((H - b.im) / M) = H - b.im := by
    field_simp [hMne]
  have hLR : a.re + (H - a.im) / M ≤ b.re - (H - b.im) / M := by
    linarith
  have hMx := mul_le_mul_of_nonneg_left
    (show b.re - x ≤ (H - b.im) / M by linarith) hM.le
  have hB : b.im + M * (b.re - x) ≤ H := by
    nlinarith [hmulB, hMx]
  have hleft' : a.re + (H - a.im) / M ≤ x := by linarith
  have hMx' := mul_le_mul_of_nonneg_left
    (show (H - a.im) / M ≤ x - a.re by linarith) hM.le
  have hA : H ≤ a.im + M * (x - a.re) := by
    nlinarith [hmulA, hMx']
  unfold roofHeight
  rw [min_eq_right (show b.im + M * (b.re - x) ≤
    a.im + M * (x - a.re) by linarith [hA, hB])]
  exact min_eq_right hB

private theorem segmentHeight_rising {a : ℂ} {H M x : ℝ}
    (hM : 0 < M) (ha : a.im < H) :
    segmentHeight a (⟨a.re + (H - a.im) / M, H⟩ : ℂ) x =
      a.im + M * (x - a.re) := by
  change a.im + ((H - a.im) /
    (a.re + (H - a.im) / M - a.re)) * (x - a.re) = _
  have hnum : H - a.im ≠ 0 := ne_of_gt (sub_pos.mpr ha)
  have hMne : M ≠ 0 := ne_of_gt hM
  rw [show a.re + (H - a.im) / M - a.re = (H - a.im) / M by ring]
  have hcoef : (H - a.im) / ((H - a.im) / M) = M := by
    field_simp [hnum, hMne]
  rw [hcoef]

private theorem segmentHeight_falling {b : ℂ} {H M x : ℝ}
    (hM : 0 < M) (hb : b.im < H) :
    segmentHeight (⟨b.re - (H - b.im) / M, H⟩ : ℂ) b x =
      b.im + M * (b.re - x) := by
  let v := (H - b.im) / M
  change H + ((b.im - H) / (b.re - (b.re - v))) *
    (x - (b.re - v)) = _
  have hnum : H - b.im ≠ 0 := ne_of_gt (sub_pos.mpr hb)
  have hMne : M ≠ 0 := ne_of_gt hM
  have hden : b.re - (b.re - v) = v := by dsimp [v]; ring
  rw [hden]
  have hcoef : (b.im - H) / v = -M := by
    dsimp [v]
    field_simp [hnum, hMne]
    ring
  rw [hcoef]
  have hmul : M * v = H - b.im := by
    dsimp [v]
    field_simp [hMne]
  rw [show H = b.im + M * v by linarith [hmul]]
  ring

private theorem segmentHeight_top (l r H x : ℝ) :
    segmentHeight (⟨l, H⟩ : ℂ) ⟨r, H⟩ x = H := by
  unfold segmentHeight
  simp

private theorem mem_segment_iff_roofGraph {a b c d z : ℂ} {H M : ℝ}
    (hcd : c.re < d.re)
    (hbranch : ∀ x, c.re ≤ x → x ≤ d.re →
      segmentHeight c d x = roofHeight a b H M x) :
    z ∈ segment ℝ c d ↔
      c.re ≤ z.re ∧ z.re ≤ d.re ∧ z.im = roofHeight a b H M z.re := by
  rw [mem_segment_iff_height hcd]
  constructor
  · rintro ⟨hl, hr, him⟩
    exact ⟨hl, hr, him.trans (hbranch z.re hl hr)⟩
  · rintro ⟨hl, hr, him⟩
    exact ⟨hl, hr, him.trans (hbranch z.re hl hr).symm⟩

private theorem polyline_image_two (a b : ℂ) :
    (⟨[a, b], by simp⟩ : Polyline).image = {a} ∪ segment ℝ a b := by
  ext z
  simp only [Polyline.image, Polyline.start, List.head_cons, mem_union,
    mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨i, hi, hz⟩)
    · simp
    · have hi' : i + 1 < 2 := by simpa using hi
      have hi0 : i = 0 := by omega
      subst i
      exact Or.inr (by simpa [Polyline.point, Polyline.segmentAt] using hz)
  · rintro (rfl | hz)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, by simp,
        by simpa [Polyline.point, Polyline.segmentAt] using hz⟩

private theorem polyline_image_three (a b c : ℂ) :
    (⟨[a, b, c], by simp⟩ : Polyline).image =
      ({a} ∪ segment ℝ a b) ∪ segment ℝ b c := by
  ext z
  simp only [Polyline.image, Polyline.start, List.head_cons, mem_union,
    mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨i, hi, hz⟩)
    · simp
    · have hi' : i + 1 < 3 := by simpa using hi
      have hi0 : i = 0 ∨ i = 1 := by omega
      rcases hi0 with hi0 | hi0
      · subst i
        exact Or.inl (Or.inr
          (by simpa [Polyline.point, Polyline.segmentAt] using hz))
      · subst i
        exact Or.inr (by simpa [Polyline.point, Polyline.segmentAt] using hz)
  · rintro ((rfl | hz) | hz)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, by simp,
        by simpa [Polyline.point, Polyline.segmentAt] using hz⟩
    · exact Or.inr ⟨1, by simp,
        by simpa [Polyline.point, Polyline.segmentAt] using hz⟩

private theorem polyline_image_four (a b c d : ℂ) :
    (⟨[a, b, c, d], by simp⟩ : Polyline).image =
      (({a} ∪ segment ℝ a b) ∪ segment ℝ b c) ∪ segment ℝ c d := by
  ext z
  simp only [Polyline.image, Polyline.start, List.head_cons, mem_union,
    mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨i, hi, hz⟩)
    · simp
    · have hi' : i + 1 < 4 := by simpa using hi
      have hi0 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi0 with hi0 | hi0 | hi0
      · subst i
        exact Or.inl (Or.inl (Or.inr
          (by simpa [Polyline.point, Polyline.segmentAt] using hz)))
      · subst i
        exact Or.inl (Or.inr
          (by simpa [Polyline.point, Polyline.segmentAt] using hz))
      · subst i
        exact Or.inr (by simpa [Polyline.point, Polyline.segmentAt] using hz)
  · rintro (((rfl | hz) | hz) | hz)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, by simp,
        by simpa [Polyline.point, Polyline.segmentAt] using hz⟩
    · exact Or.inr ⟨1, by simp,
        by simpa [Polyline.point, Polyline.segmentAt] using hz⟩
    · exact Or.inr ⟨2, by simp,
        by simpa [Polyline.point, Polyline.segmentAt] using hz⟩



theorem roofArc_image {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    (roofArc a b H M).image =
      {z | a.re ≤ z.re ∧ z.re ≤ b.re ∧
        z.im = roofHeight a b H M z.re} := by
  let p : ℂ := ⟨a.re + (H - a.im) / M, H⟩
  let q : ℂ := ⟨b.re - (H - b.im) / M, H⟩
  have hpRe : p.re = a.re + (H - a.im) / M := by simp [p]
  have hqRe : q.re = b.re - (H - b.im) / M := by simp [q]
  have hpa : a.re ≤ p.re := by
    rw [hpRe]
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr ha) hM.le)
  have hqb : q.re ≤ b.re := by
    rw [hqRe]
    exact sub_le_self _ (div_nonneg (sub_nonneg.mpr hb) hM.le)
  have hpq : p.re < q.re := by
    rw [hpRe, hqRe]
    linarith
  have hab : a.re < b.re := lt_of_le_of_lt hpa (lt_of_lt_of_le hpq hqb)
  have hstart := roofHeight_start hM ha hb hfit
  have hpEq (haH : a.im = H) : p = a := by
    apply Complex.ext <;> simp [p, haH]
  have hqEq (hbH : b.im = H) : q = b := by
    apply Complex.ext <;> simp [q, hbH]
  have hTopGraph : ∀ z, z ∈ segment ℝ p q ↔
      p.re ≤ z.re ∧ z.re ≤ q.re ∧
        z.im = roofHeight a b H M z.re := by
    intro z
    apply mem_segment_iff_roofGraph hpq
    intro x hl hr
    rw [hpRe] at hl
    rw [hqRe] at hr
    calc
      segmentHeight p q x = H := by
        simpa [p, q] using segmentHeight_top p.re q.re H x
      _ = roofHeight a b H M x :=
        (roofHeight_eq_top hM ha hb hfit hl hr).symm
  have hRiseGraph (haLt : a.im < H) :
      ∀ z, z ∈ segment ℝ a p ↔
        a.re ≤ z.re ∧ z.re ≤ p.re ∧
          z.im = roofHeight a b H M z.re := by
    intro z
    have hstrict : a.re < p.re := by
      rw [hpRe]
      linarith [div_pos (sub_pos.mpr haLt) hM]
    apply mem_segment_iff_roofGraph hstrict
    intro x hl hr
    rw [hpRe] at hr
    calc
      segmentHeight a p x = a.im + M * (x - a.re) := by
        simpa [p] using segmentHeight_rising hM haLt (x := x)
      _ = roofHeight a b H M x :=
        (roofHeight_eq_rising hM ha hb hfit hl hr).symm
  have hFallGraph (hbLt : b.im < H) :
      ∀ z, z ∈ segment ℝ q b ↔
        q.re ≤ z.re ∧ z.re ≤ b.re ∧
          z.im = roofHeight a b H M z.re := by
    intro z
    have hstrict : q.re < b.re := by
      rw [hqRe]
      linarith [div_pos (sub_pos.mpr hbLt) hM]
    apply mem_segment_iff_roofGraph hstrict
    intro x hl hr
    rw [hqRe] at hl
    calc
      segmentHeight q b x = b.im + M * (b.re - x) := by
        simpa [q] using segmentHeight_falling hM hbLt (x := x)
      _ = roofHeight a b H M x :=
        (roofHeight_eq_falling hM ha hb hfit hl hr).symm
  by_cases haH : a.im = H
  · have hpEq' := hpEq haH
    by_cases hbH : b.im = H
    · have hqEq' := hqEq hbH
      have himage : (roofArc a b H M).image = {a} ∪ segment ℝ a b := by
        simpa [roofArc, haH, hbH] using polyline_image_two a b
      have hgraph : ∀ z, z ∈ segment ℝ a b ↔
          a.re ≤ z.re ∧ z.re ≤ b.re ∧
            z.im = roofHeight a b H M z.re := by
        intro z
        simpa [hpEq', hqEq'] using hTopGraph z
      ext z
      rw [himage]
      simp only [mem_union, mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (rfl | hz)
        · exact ⟨le_rfl, hab.le, hstart.symm⟩
        · exact (hgraph z).mp hz
      · intro hz
        exact Or.inr ((hgraph z).mpr hz)
    · have hbLt : b.im < H := lt_of_le_of_ne hb hbH
      have hsegTop : ∀ z, z ∈ segment ℝ a q ↔
          a.re ≤ z.re ∧ z.re ≤ q.re ∧
            z.im = roofHeight a b H M z.re := by
        intro z
        simpa [hpEq'] using hTopGraph z
      have hfall := hFallGraph hbLt
      have himage : (roofArc a b H M).image =
          ({a} ∪ segment ℝ a q) ∪ segment ℝ q b := by
        simpa [roofArc, haH, hbH, q] using polyline_image_three a q b
      ext z
      rw [himage]
      simp only [mem_union, mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ((rfl | hz) | hz)
        · exact ⟨le_rfl, hab.le, hstart.symm⟩
        · obtain ⟨hl, hr, hh⟩ := hsegTop z |>.mp hz
          exact ⟨hl, le_trans hr hqb, hh⟩
        · obtain ⟨hl, hr, hh⟩ := hfall z |>.mp hz
          exact ⟨le_trans hpa (le_trans (le_of_lt hpq) hl), hr, hh⟩
      · rintro ⟨hl, hr, hh⟩
        rcases le_total z.re q.re with h | h
        · exact Or.inl (Or.inr (hsegTop z |>.mpr ⟨hl, h, hh⟩))
        · exact Or.inr (hfall z |>.mpr ⟨h, hr, hh⟩)
  · have haLt : a.im < H := lt_of_le_of_ne ha haH
    have hRise := hRiseGraph haLt
    by_cases hbH : b.im = H
    · have hqEq' := hqEq hbH
      have hsegTop : ∀ z, z ∈ segment ℝ p b ↔
          p.re ≤ z.re ∧ z.re ≤ b.re ∧
            z.im = roofHeight a b H M z.re := by
        intro z
        simpa [hqEq'] using hTopGraph z
      have himage : (roofArc a b H M).image =
          ({a} ∪ segment ℝ a p) ∪ segment ℝ p b := by
        simpa [roofArc, haH, hbH, p] using polyline_image_three a p b
      ext z
      rw [himage]
      simp only [mem_union, mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ((rfl | hz) | hz)
        · exact ⟨le_rfl, hab.le, hstart.symm⟩
        · obtain ⟨hl, hr, hh⟩ := hRise z |>.mp hz
          exact ⟨hl, le_trans hr (le_of_lt (hpq.trans_le hqb)), hh⟩
        · obtain ⟨hl, hr, hh⟩ := hsegTop z |>.mp hz
          exact ⟨le_trans hpa hl, hr, hh⟩
      · rintro ⟨hl, hr, hh⟩
        rcases le_total z.re p.re with h | h
        · exact Or.inl (Or.inr ((hRise z).mpr ⟨hl, h, hh⟩))
        · exact Or.inr ((hsegTop z).mpr ⟨h, hr, hh⟩)
    · have hbLt : b.im < H := lt_of_le_of_ne hb hbH
      have hfall := hFallGraph hbLt
      have himage : (roofArc a b H M).image =
          (({a} ∪ segment ℝ a p) ∪ segment ℝ p q) ∪ segment ℝ q b := by
        simpa [roofArc, haH, hbH, p, q] using polyline_image_four a p q b
      ext z
      rw [himage]
      simp only [mem_union, mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (((rfl | hz) | hz) | hz)
        · exact ⟨le_rfl, hab.le, hstart.symm⟩
        · obtain ⟨hl, hr, hh⟩ := hRise z |>.mp hz
          exact ⟨hl, le_trans hr (le_of_lt (hpq.trans_le hqb)), hh⟩
        · obtain ⟨hl, hr, hh⟩ := hTopGraph z |>.mp hz
          exact ⟨le_trans hpa hl, le_trans hr hqb, hh⟩
        · obtain ⟨hl, hr, hh⟩ := hfall z |>.mp hz
          exact ⟨le_trans hpa (le_trans (le_of_lt hpq) hl), hr, hh⟩
      · rintro ⟨hl, hr, hh⟩
        rcases le_total z.re p.re with h | h
        · exact Or.inl (Or.inl (Or.inr (hRise z |>.mpr ⟨hl, h, hh⟩)))
        · rcases le_total z.re q.re with h' | h'
          · exact Or.inl (Or.inr (hTopGraph z |>.mpr ⟨h, h', hh⟩))
          · exact Or.inr (hfall z |>.mpr ⟨h', hr, hh⟩)



theorem roofArc_interior {a b : ℂ} {H M : ℝ} (hM : 0 < M)
    (ha : a.im ≤ H) (hb : b.im ≤ H)
    (hfit : (H - a.im) / M + (H - b.im) / M < b.re - a.re) :
    (roofArc a b H M).interior =
      {z | a.re < z.re ∧ z.re < b.re ∧
        z.im = roofHeight a b H M z.re} := by
  have hstart := roofHeight_start hM ha hb hfit
  have hfinish := roofHeight_finish hM ha hb hfit
  rw [Polyline.interior, roofArc_start, roofArc_finish,
    roofArc_image hM ha hb hfit]
  ext z
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨⟨hl, hr, hh⟩, hza, hzb⟩
    refine ⟨?_, ?_, hh⟩
    · by_contra hnot
      have hzre : z.re = a.re := le_antisymm (not_lt.mp hnot) hl
      apply hza
      apply Complex.ext
      · exact hzre
      · rw [hh, hzre, hstart]
    · by_contra hnot
      have hzre : z.re = b.re := le_antisymm hr (not_lt.mp hnot)
      apply hzb
      apply Complex.ext
      · exact hzre
      · rw [hh, hzre, hfinish]
  · rintro ⟨hl, hr, hh⟩
    refine ⟨⟨hl.le, hr.le, hh⟩, ?_, ?_⟩
    · intro hza
      exact (ne_of_lt hl) (congrArg Complex.re hza).symm
    · intro hzb
      exact (ne_of_lt hr) (congrArg Complex.re hzb)

end
end DirectedDistances.PlanarMap
