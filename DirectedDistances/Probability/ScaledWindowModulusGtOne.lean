module

public import DirectedDistances.Probability.ScaledWindowSeparatedCuts
public import DirectedDistances.Probability.ScaledWindowModulusTight
public import DirectedDistances.Probability.ScaledSmallJumpRemainder
public import DirectedDistances.Probability.SkorokhodJ1WindowBorel
public import DirectedDistances.Probability.PowerTailBounds

/-! # Centered scaled-window modulus helpers

These helpers are not the paper result. -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- the canonical Borel laws of iid scaled windows are tight below index one
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_isTight_lt_one' {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν)) (hT : 0 < T) :
    IsTightMeasureSet
      (Set.range fun n : ℕ => P.map (scaledPartialSumWindow X ν n hT)) :=
  scaledPartialSumWindow_isTight_lt_one P X hX hind hident hν0 hν1 hC hTail hT
    (fun n => aemeasurable_scaledPartialSumWindow P X hX ν n hT)

/-- refine separated cuts by a half-length grid while bounding every consecutive gap
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem exists_separated_cuts_refinement {T δ L0 : ℝ} (hT : 0 < T)
    (hδ : 0 < δ) (hL : 4 * δ ≤ L0) (s : Finset (J1Window T))
    (h0 : ⟨0, le_rfl, hT.le⟩ ∈ s) (hTs : ⟨T, hT.le, le_rfl⟩ ∈ s)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) :
    ∃ s' : Finset (J1Window T), s ⊆ s' ∧
      ⟨0, le_rfl, hT.le⟩ ∈ s' ∧ ⟨T, hT.le, le_rfl⟩ ∈ s' ∧
      (∀ u ∈ s', ∀ v ∈ s', (u : ℝ) < v → δ < (v : ℝ) - u) ∧
      (∀ u ∈ s', ∀ v ∈ s', (u : ℝ) < v →
        (∀ c ∈ s', ¬ ((u : ℝ) < c ∧ (c : ℝ) < v)) → (v : ℝ) - u ≤ L0) := by
  classical
  let h : ℝ := L0 / 2
  have hh : 0 < h := by dsimp [h]; linarith
  have hδh : 2 * δ ≤ h := by dsimp [h]; linarith
  let K : ℕ := ⌊T / h⌋₊
  let c : Fin (K + 1) → J1Window T := fun i => ⟨(i.val : ℝ) * h, by
    constructor
    · positivity
    · have hi : (i.val : ℝ) ≤ K := by exact_mod_cast (by omega : i.val ≤ K)
      have hfloor : (K : ℝ) ≤ T / h := Nat.floor_le (div_nonneg hT.le hh.le)
      exact (le_div_iff₀ hh).mp (hi.trans hfloor)⟩
  let g := Finset.univ.filter fun i : Fin (K + 1) =>
    ∀ u ∈ s, δ < |(c i : ℝ) - u|
  let s' := s ∪ g.image c
  have hsub : s ⊆ s' := Finset.subset_union_left
  have hgood {i : Fin (K + 1)} (hi : i ∈ g) :
      ∀ u ∈ s, δ < |(c i : ℝ) - u| := (Finset.mem_filter.mp hi).2
  refine ⟨s', hsub, hsub h0, hsub hTs, ?_, ?_⟩
  · intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact hsep u hu v hv huv
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        simpa only [abs_of_pos (sub_pos.mpr huv)] using hgood hj u hu
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      rcases Finset.mem_union.mp hv with hv | hv
      · have hb := hgood hi v hv
        simpa only [abs_of_neg (sub_neg.mpr huv), neg_sub] using hb
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        have hij : i.val < j.val := by
          have hm : (i.val : ℝ) < j.val := (mul_lt_mul_iff_left₀ hh).mp huv
          exact_mod_cast hm
        have hcast : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
        have hm := mul_le_mul_of_nonneg_right hcast hh.le
        change δ < (j.val : ℝ) * h - (i.val : ℝ) * h
        nlinarith only [hm, hδh, hδ]
  · intro u hu v hv huv hno
    by_contra hgap
    have hgap' : L0 < (v : ℝ) - u := lt_of_not_ge hgap
    let k : ℕ := ⌊((u : ℝ) + δ) / h⌋₊ + 1
    have hklo : (u : ℝ) + δ < (k : ℝ) * h := by
      apply (div_lt_iff₀ hh).mp
      simpa only [k, Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one (((u : ℝ) + δ) / h)
    have hkhi : (k : ℝ) * h ≤ (u : ℝ) + δ + h := by
      have hf := Nat.floor_le (div_nonneg
        (show 0 ≤ (u : ℝ) + δ by linarith [u.property.1]) hh.le)
      have hm := (le_div_iff₀ hh).mp hf
      dsimp [k]
      push_cast
      nlinarith only [hm]
    have hkv : (k : ℝ) * h < (v : ℝ) - δ := by dsimp [h] at *; linarith
    have hkT : (k : ℝ) * h ≤ T := by linarith [v.property.2]
    have hkK : k ≤ K := Nat.le_floor ((le_div_iff₀ hh).mpr hkT)
    let i : Fin (K + 1) := ⟨k, by omega⟩
    have hig : i ∈ g := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro z hz
      have hzno := hno z (hsub hz)
      change δ < |(k : ℝ) * h - (z : ℝ)|
      by_cases hzu : (z : ℝ) ≤ u
      · rw [abs_of_pos (by linarith : 0 < (k : ℝ) * h - (z : ℝ))]
        linarith
      · have hvz : (v : ℝ) ≤ z := by
          by_contra hzv
          exact hzno ⟨lt_of_not_ge hzu, lt_of_not_ge hzv⟩
        rw [abs_of_neg (by linarith : (k : ℝ) * h - (z : ℝ) < 0)]
        linarith
    have hci : c i ∈ s' := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hig, rfl⟩)
    apply hno (c i) hci
    constructor
    · change (u : ℝ) < (k : ℝ) * h
      linarith
    · change (k : ℝ) * h < (v : ℝ)
      linarith

private theorem centered_window_apply_nat {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ν : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : Ω) (t : J1Window T) :
    (scaledPartialSumWindow X ν n hT ω).path.1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        ∑ j ∈ Finset.range ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, X j ω := by
  have hnat (k : ℕ) : partialSumZ X ω (k : ℤ) =
      ∑ j ∈ Finset.range k, X j ω := by
    cases k with
    | zero => simp [partialSumZ]
    | succ k => simp [partialSumZ]
  rw [scaledPartialSumWindow_apply,
    ← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property.1), hnat]

/-- mean-zero windows split into centered small jumps, large jumps, and the negative
large-jump mean drift (Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_drift_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν : ℝ} (hν : 1 < ν) (hint : Integrable (X 0) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (ρ : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) (ω : Ω) (t : J1Window T) :
    (scaledPartialSumWindow X ν n hT ω).path.1 t =
      (scaledPartialSumWindow (scaledTruncatedIncrement P X ν ρ n) ν n hT ω).path.1 t +
      (scaledPartialSumWindow
        (fun j ω => if scaledSmallJumpLevel ν ρ n < |X j ω| then X j ω else 0)
        ν n hT ω).path.1 t -
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        (⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ) *
        (∫ ω, (if scaledSmallJumpLevel ν ρ n < |X 0 ω| then X 0 ω else 0) ∂P) := by
  let a := scaledSmallJumpLevel ν ρ n
  let low : ℕ → Ω → ℝ := fun j ω => if |X j ω| ≤ a then X j ω else 0
  let high : ℕ → Ω → ℝ := fun j ω => if a < |X j ω| then X j ω else 0
  have hlow (j : ℕ) : Integrable (low j) P := by
    have hj := (hident j).integrable_iff.mpr hint
    have hi : Integrable ({ω | |X j ω| ≤ a}.indicator (X j)) P :=
      hj.indicator (measurableSet_le
        (continuous_abs.measurable.comp (hX j)) measurable_const)
    apply hi.congr
    exact ae_of_all P fun ω => by simp only [Set.indicator_apply, low, Set.mem_ofPred_eq]
  have hhigh (j : ℕ) : Integrable (high j) P := by
    have hj := (hident j).integrable_iff.mpr hint
    have hi : Integrable ({ω | a < |X j ω|}.indicator (X j)) P :=
      hj.indicator (measurableSet_lt measurable_const
        (continuous_abs.measurable.comp (hX j)))
    apply hi.congr
    exact ae_of_all P fun ω => by simp only [Set.indicator_apply, high, Set.mem_ofPred_eq]
  have hhighmean (j : ℕ) : ∫ ω, high j ω ∂P = ∫ ω, high 0 ω ∂P := by
    exact ((hident j).comp (Measurable.ite
      (measurableSet_lt measurable_const continuous_abs.measurable)
      measurable_id measurable_const)).integral_eq
  have hsplit (j : ℕ) : X j = fun ω => low j ω + high j ω := by
    funext ω
    by_cases h : |X j ω| ≤ a
    · simp [low, high, h, not_lt.mpr h]
    · simp [low, high, h, lt_of_not_ge h]
  have hlowmean (j : ℕ) : ∫ ω, low j ω ∂P = -(∫ ω, high 0 ω ∂P) := by
    have hm : ∫ ω, X j ω ∂P = 0 := (hident j).integral_eq.trans hmean
    rw [hsplit j, integral_add (hlow j) (hhigh j), hhighmean j] at hm
    linarith only [hm]
  have hinc (j : ℕ) : scaledTruncatedIncrement P X ν ρ n j ω =
      low j ω + ∫ ω, high 0 ω ∂P := by
    have heq : (fun ω => X j ω * Set.indicator {ω | |X j ω| ≤ a}
        (fun _ => (1 : ℝ)) ω) = low j := by
      funext ω
      by_cases h : |X j ω| ≤ a <;> simp [low, h]
    unfold scaledTruncatedIncrement
    change (fun ω => X j ω * Set.indicator {ω | |X j ω| ≤ a}
      (fun _ => (1 : ℝ)) ω) ω - (if 1 < ν then ∫ ω, X j ω *
      Set.indicator {ω | |X j ω| ≤ a} (fun _ => (1 : ℝ)) ω ∂P else 0) = _
    rw [ite_eq_left hν, heq, hlowmean j, sub_neg_eq_add]
  rw [centered_window_apply_nat, centered_window_apply_nat, centered_window_apply_nat]
  simp_rw [hinc]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ j ∈ Finset.range ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, X j ω) =
      (∑ j ∈ Finset.range ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, low j ω) +
      ∑ j ∈ Finset.range ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, high j ω := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => congrFun (hsplit j) ω
  rw [hsum]
  change _ = _ + ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
    (∑ j ∈ Finset.range ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, high j ω) - _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- the tail-mean drift has slope bounded independently of the window size, with one
floor-step error (Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_tail_drift_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 0)) {ν C : ℝ} (hν : 1 < ν) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) (ha : 1 ≤ scaledSmallJumpLevel ν ρ n)
    {T : ℝ} (s t : J1Window T) (hst : (s : ℝ) ≤ t) :
    |(-((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        (⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℝ) *
        (∫ ω, (if scaledSmallJumpLevel ν ρ n < |X 0 ω| then X 0 ω else 0) ∂P)) -
      (-((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        (⌊((n + 1 : ℕ) : ℝ) * (s : ℝ)⌋₊ : ℝ) *
        (∫ ω, (if scaledSmallJumpLevel ν ρ n < |X 0 ω| then X 0 ω else 0) ∂P))| ≤
      (2 * C / (1 - (2 : ℝ) ^ (1 - ν))) * ρ ^ (1 - ν) *
        ((t : ℝ) - s + 1 / ((n + 1 : ℕ) : ℝ)) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let z : ℝ := N ^ (1 / ν)
  let a := scaledSmallJumpLevel ν ρ n
  let D : ℝ := 2 * C / (1 - (2 : ℝ) ^ (1 - ν))
  let m : ℝ := ∫ ω, (if a < |X 0 ω| then X 0 ω else 0) ∂P
  have hN : 0 < N := by dsimp [N]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hN _
  have hν0 : 0 < ν := by linarith
  have hq : (2 : ℝ) ^ (1 - ν) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have haz : a = ρ * z := by simp [a, scaledSmallJumpLevel, z, N]
  have hpow : z ^ ν = N := by
    dsimp [z]
    rw [← Real.rpow_mul hN.le, one_div, inv_mul_cancel₀ hν0.ne', Real.rpow_one]
  have hscale : N ^ (-(1 / ν)) = z⁻¹ := Real.rpow_neg hN.le _
  have hscalepow : z⁻¹ * N * a ^ (1 - ν) = ρ ^ (1 - ν) := by
    rw [haz, Real.mul_rpow hρ.le hz.le, ← hpow]
    have he : z ^ ν * z ^ (1 - ν) = z := by
      rw [← Real.rpow_add hz, show ν + (1 - ν) = 1 by ring, Real.rpow_one]
    calc z⁻¹ * z ^ ν * (ρ ^ (1 - ν) * z ^ (1 - ν)) =
        ρ ^ (1 - ν) * z⁻¹ * (z ^ ν * z ^ (1 - ν)) := by ring
      _ = ρ ^ (1 - ν) := by rw [he]; field_simp
  obtain ⟨hint, hmoment⟩ := tail_first_moment_power_tail_bound hX hν hC hTail
  have hm : |m| ≤ D * a ^ (1 - ν) := by
    calc |m| ≤ ∫ ω, |if a < |X 0 ω| then X 0 ω else 0| ∂P := by
          simpa only [m, Real.norm_eq_abs] using
            norm_integral_le_integral_norm
              (fun ω => if a < |X 0 ω| then X 0 ω else 0)
      _ = ∫ ω, (if a < |X 0 ω| then |X 0 ω| else 0) ∂P := by
        congr 1
        funext ω
        split_ifs <;> simp
      _ ≤ D * a ^ (1 - ν) := hmoment a ha
  have hslope : z⁻¹ * N * |m| ≤ D * ρ ^ (1 - ν) := by
    calc z⁻¹ * N * |m| ≤ z⁻¹ * N * (D * a ^ (1 - ν)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = D * ρ ^ (1 - ν) := by rw [← hscalepow]; ring
  let ks : ℝ := ⌊N * (s : ℝ)⌋₊
  let kt : ℝ := ⌊N * (t : ℝ)⌋₊
  have hk : ks ≤ kt := by
    dsimp [ks, kt]
    exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left hst hN.le)
  have hkdiff : kt - ks ≤ N * ((t : ℝ) - s) + 1 := by
    have ht := Nat.floor_le (mul_nonneg hN.le t.property.1)
    have hs := Nat.lt_floor_add_one (N * (s : ℝ))
    dsimp [ks, kt]
    nlinarith only [ht, hs]
  change |(-N ^ (-(1 / ν)) * kt * m) - (-N ^ (-(1 / ν)) * ks * m)| ≤ _
  rw [hscale]
  calc |(-z⁻¹ * kt * m) - (-z⁻¹ * ks * m)| = z⁻¹ * (kt - ks) * |m| := by
        rw [show (-z⁻¹ * kt * m) - (-z⁻¹ * ks * m) =
          -(z⁻¹ * (kt - ks) * m) by ring, abs_neg, abs_mul,
          abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hz.le) (sub_nonneg.mpr hk))]
    _ ≤ z⁻¹ * (N * ((t : ℝ) - s) + 1) * |m| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkdiff (by positivity))
        (abs_nonneg _)
    _ = (z⁻¹ * N * |m|) * ((t : ℝ) - s + 1 / N) := by field_simp
    _ ≤ (D * ρ ^ (1 - ν)) * ((t : ℝ) - s + 1 / N) :=
      mul_le_mul_of_nonneg_right hslope (by positivity)

private theorem centered_window_le_remainder {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (ν ρ : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) (ω : Ω) (t : J1Window T) :
    |(scaledPartialSumWindow (scaledTruncatedIncrement P X ν ρ n)
      ν n hT ω).path.1 t| ≤ scaledSmallJumpRemainder P X ν ρ T n ω := by
  rw [centered_window_apply_nat, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  unfold scaledSmallJumpRemainder
  simp only [Nat.cast_add, Nat.cast_one]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  apply (Finset.le_sup'_iff _).mpr
  refine ⟨⌊(n + 1 : ℝ) * (t : ℝ)⌋₊, ?_, le_rfl⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le
    (Nat.floor_mono (mul_le_mul_of_nonneg_left t.property.2 (by positivity))))

/-- on a block without large jumps, the centered remainder and bounded tail drift
control oscillation (Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_blockOscillation_gt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C : ℝ} (hν : 1 < ν) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    (hint : Integrable (X 0) P) (hmean : ∫ ω, X 0 ω ∂P = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) (ha : 1 ≤ scaledSmallJumpLevel ν ρ n)
    {T : ℝ} (hT : 0 < T) (ω : Ω) (a b : J1Window T) (hab : (a : ℝ) < b)
    (r : ℝ) (hRem : scaledSmallJumpRemainder P X ν ρ T n ω ≤ r)
    (hno : ∀ t : J1Window T, (a : ℝ) ≤ t → (t : ℝ) < b →
      ∀ j : ℕ, ⌊((n + 1 : ℕ) : ℝ) * (a : ℝ)⌋₊ ≤ j →
        j < ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ →
          |X j ω| ≤ scaledSmallJumpLevel ν ρ n) :
    blockOscillation (scaledPartialSumWindow X ν n hT ω).path a b ≤
      2 * r + (2 * C / (1 - (2 : ℝ) ^ (1 - ν))) * ρ ^ (1 - ν) *
        ((b : ℝ) - a + 1 / ((n + 1 : ℕ) : ℝ)) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let D : ℝ := 2 * C / (1 - (2 : ℝ) ^ (1 - ν)) * ρ ^ (1 - ν)
  let small := fun t : J1Window T =>
    (scaledPartialSumWindow (scaledTruncatedIncrement P X ν ρ n) ν n hT ω).path.1 t
  let large := fun t : J1Window T => (scaledPartialSumWindow
    (fun j ω => if scaledSmallJumpLevel ν ρ n < |X j ω| then X j ω else 0)
    ν n hT ω).path.1 t
  let drift := fun t : J1Window T => -N ^ (-(1 / ν)) * (⌊N * (t : ℝ)⌋₊ : ℝ) *
    (∫ ω, (if scaledSmallJumpLevel ν ρ n < |X 0 ω| then X 0 ω else 0) ∂P)
  have hD : 0 ≤ D := by
    have hq : (2 : ℝ) ^ (1 - ν) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    dsimp [D]
    positivity
  have hsplit (t : J1Window T) :
      (scaledPartialSumWindow X ν n hT ω).path.1 t = small t + large t + drift t := by
    have he := scaledPartialSumWindow_drift_decomposition
      P X hX hident hν hint hmean ρ n hT ω t
    change _ = small t + large t - _ at he
    dsimp [drift, N]
    rw [he]
    ring
  have hlarge (t : J1Window T) (hat : (a : ℝ) ≤ t) (htb : (t : ℝ) < b) :
      large t = large a :=
    scaledPartialSumWindow_large_eq_of_no_large_increment X ν
      (scaledSmallJumpLevel ν ρ n) n hT ω a t hat (hno t hat htb)
  have hsmall (t : J1Window T) : |small t| ≤ r :=
    (centered_window_le_remainder P X ν ρ n hT ω t).trans hRem
  have hpair (s t : J1Window T) (has : (a : ℝ) ≤ s) (hsb : (s : ℝ) < b)
      (hat : (a : ℝ) ≤ t) (htb : (t : ℝ) < b) (hst : (s : ℝ) ≤ t) :
      |(scaledPartialSumWindow X ν n hT ω).path.1 s -
        (scaledPartialSumWindow X ν n hT ω).path.1 t| ≤
          2 * r + D * ((b : ℝ) - a + 1 / N) := by
    have hd : |drift t - drift s| ≤ D * ((t : ℝ) - s + 1 / N) :=
      scaledPartialSumWindow_tail_drift_bound P X (hX 0) hν hC hTail hρ n ha s t hst
    have hd' : |drift s - drift t| ≤ D * ((b : ℝ) - a + 1 / N) := by
      rw [abs_sub_comm]
      exact hd.trans (mul_le_mul_of_nonneg_left (by linarith) hD)
    rw [hsplit s, hsplit t, hlarge s has hsb, hlarge t hat htb]
    calc |small s + large a + drift s - (small t + large a + drift t)| =
          |(small s - small t) + (drift s - drift t)| := by congr 1; ring
      _ ≤ |small s - small t| + |drift s - drift t| := abs_add_le _ _
      _ ≤ (|small s| + |small t|) + D * ((b : ℝ) - a + 1 / N) :=
        add_le_add (abs_sub _ _) hd'
      _ ≤ 2 * r + D * ((b : ℝ) - a + 1 / N) := by
        linarith only [hsmall s, hsmall t]
  unfold blockOscillation
  apply csSup_le
  · refine ⟨0, a, a, le_rfl, hab, le_rfl, hab, ?_⟩
    simp
  · rintro x ⟨s, t, has, hsb, hat, htb, rfl⟩
    rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · exact hpair s t has hsb hat htb hst
    · rw [abs_sub_comm]
      exact hpair t s hat htb has hsb hts

private theorem iid_large_pair_prob {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    (a : ℝ) {i j : ℕ} (hij : i ≠ j) :
    P.real {ω | a < |X i ω| ∧ a < |X j ω|} =
      (P.real {ω | a < |X 0 ω|}) ^ 2 := by
  have hA : MeasurableSet {x : ℝ | a < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hp := (hind.indepFun hij).measure_inter_preimage_eq_mul
    {x : ℝ | a < |x|} {x : ℝ | a < |x|} hA hA
  have hi := (hident i).measure_mem_eq hA
  have hj := (hident j).measure_mem_eq hA
  change P ({ω | a < |X i ω|} ∩ {ω | a < |X j ω|}) = _ at hp
  simp only [measureReal_def, pow_two]
  change (P ({ω | a < |X i ω|} ∩ {ω | a < |X j ω|})).toReal =
    (P (X 0 ⁻¹' {x : ℝ | a < |x|})).toReal *
      (P (X 0 ⁻¹' {x : ℝ | a < |x|})).toReal
  rw [hp, hi, hj, ENNReal.toReal_mul]

private theorem exists_small_positive_gap (s : Finset ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ < b ∧ ∀ x ∈ s, 0 < x → δ < x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨b / 2, by positivity, by linarith, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hδb, hδs⟩ := ih
    by_cases hapos : 0 < a
    · refine ⟨min δ (a / 2), lt_min hδ (by positivity),
        (min_le_left _ _).trans_lt hδb, ?_⟩
      intro x hx hxpos
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (min_le_right _ _).trans_lt (by linarith)
      · exact (min_le_left _ _).trans_lt (hδs x hx hxpos)
    · refine ⟨δ, hδ, hδb, ?_⟩
      intro x hx hxpos
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (hapos hxpos).elim
      · exact hδs x hx hxpos

private theorem exists_cuts_of_gap_bounds {Ω : Type*} (X : ℕ → Ω → ℝ)
    (a : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T) (ω : Ω) {δ : ℝ} (hδT : δ < T)
    (hleft : ∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
      δ < (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))
    (hright : ∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
      (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ) < T →
      δ < T - (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))
    (hpair : ∀ i j : ℕ, i < j → j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ →
      a < |X i ω| → a < |X j ω| →
      δ < (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ) -
        (i + 1 : ℝ) / ((n + 1 : ℕ) : ℝ)) :
    ∃ s : Finset (J1Window T),
      ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
      (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
      (∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
        ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  classical
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let K : ℕ := ⌊N * T⌋₊
  have hN : 0 < N := by dsimp [N]; positivity
  let c : Fin K → J1Window T := fun j => ⟨(j.val + 1 : ℝ) / N, by
    constructor
    · positivity
    · apply (div_le_iff₀ hN).mpr
      have hj : (j.val + 1 : ℝ) ≤ K := by exact_mod_cast j.isLt
      have hfloor : (K : ℝ) ≤ N * T := Nat.floor_le (mul_nonneg hN.le hT.le)
      exact hj.trans (hfloor.trans_eq (mul_comm N T))⟩
  let z : J1Window T := ⟨0, le_rfl, hT.le⟩
  let e : J1Window T := ⟨T, hT.le, le_rfl⟩
  let s := insert z (insert e ((Finset.univ.filter fun j : Fin K =>
    a < |X j.val ω|).image c))
  have hmem (u : J1Window T) (hu : u ∈ s) :
      u = z ∨ u = e ∨ ∃ j : Fin K, a < |X j.val ω| ∧ u = c j := by
    simp only [s, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hu
    rcases hu with h | h | ⟨j, hj, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, hj, h.symm⟩)
  refine ⟨s, by simp [s, z], by simp [s, e], ?_, ?_⟩
  · intro u hu v hv huv
    rcases hmem u hu with rfl | rfl | ⟨i, hi, rfl⟩
    · rcases hmem v hv with rfl | rfl | ⟨j, hj, rfl⟩
      · exact (lt_irrefl (0 : ℝ) huv).elim
      · simpa [z, e] using hδT
      · simpa [z, c, N] using hleft j.val j.isLt hj
    · exact (not_lt_of_ge v.property.2 huv).elim
    · rcases hmem v hv with rfl | rfl | ⟨j, hj, rfl⟩
      · exact (not_lt_of_ge (c i).property.1 huv).elim
      · exact hright i.val i.isLt hi huv
      · have hij : i.val < j.val := by
          have h := (div_lt_div_iff_of_pos_right hN).mp huv
          exact_mod_cast (show (i.val : ℝ) < j.val by linarith)
        exact hpair i.val j.val hij j.isLt hi hj
  · intro j hj hbig
    refine ⟨c ⟨j, hj⟩, ?_, rfl⟩
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp [hbig], rfl⟩

private theorem prob_exists_finset_le {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : Finset ι) (E : ι → Set Ω)
    (p : ℝ) (h : ∀ i ∈ s, P.real (E i) ≤ p) :
    P.real {ω | ∃ i ∈ s, ω ∈ E i} ≤ (s.card : ℝ) * p := by
  have heq : {ω | ∃ i ∈ s, ω ∈ E i} = ⋃ i ∈ s, E i := by ext; simp
  rw [heq]
  calc P.real (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, P.real (E i) :=
      measureReal_biUnion_finset_le s E
    _ ≤ ∑ _i ∈ s, p := Finset.sum_le_sum h
    _ = (s.card : ℝ) * p := by simp

private theorem gap_failure_prob_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    (a : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T) {δ : ℝ} (_hδ : 0 ≤ δ) (hδT : δ < T) :
    P.real {ω | ¬ ∃ s : Finset (J1Window T),
      ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
      (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
      (∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
        ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))} ≤
      (⌊((n + 1 : ℕ) : ℝ) * T⌋₊ : ℝ) *
          (⌊δ * ((n + 1 : ℕ) : ℝ)⌋₊ + 1 : ℝ) *
          (P.real {ω | a < |X 0 ω|}) ^ 2 +
        2 * (⌊δ * ((n + 1 : ℕ) : ℝ)⌋₊ + 1 : ℝ) *
          P.real {ω | a < |X 0 ω|} := by
  classical
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let K : ℕ := ⌊N * T⌋₊
  let L : ℕ := ⌊δ * N⌋₊
  let q := P.real {ω | a < |X 0 ω|}
  let A : Set Ω := {ω | ∃ i ∈ Finset.range K, ∃ d ∈ Finset.range (L + 1),
    a < |X i ω| ∧ a < |X (i + d + 1) ω|}
  let B : Set Ω := {ω | ∃ d ∈ Finset.range (L + 1), a < |X d ω|}
  let D : Set Ω := {ω | ∃ d ∈ Finset.range (L + 1), a < |X (K - 1 - d) ω|}
  have hN : 0 < N := by dsimp [N]; positivity
  have hK : (K : ℝ) ≤ N * T := Nat.floor_le (mul_nonneg hN.le hT.le)
  have hdist (j : ℕ) (hj : (j : ℝ) ≤ δ * N) : j ∈ Finset.range (L + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hj))
  have hsub : {ω | ¬ ∃ s : Finset (J1Window T),
      ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
      (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
      (∀ j : ℕ, j < ⌊N * T⌋₊ → a < |X j ω| →
        ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / N)} ⊆ A ∪ (B ∪ D) := by
    intro ω hω
    by_contra hnot
    have hA : ω ∉ A := fun h => hnot (Or.inl h)
    have hB : ω ∉ B := fun h => hnot (Or.inr (Or.inl h))
    have hD : ω ∉ D := fun h => hnot (Or.inr (Or.inr h))
    apply hω
    apply exists_cuts_of_gap_bounds X a n hT ω hδT
    · intro j hj hbig
      by_contra hclose
      have hc : (j + 1 : ℝ) ≤ δ * N :=
        (div_le_iff₀ hN).mp (le_of_not_gt hclose)
      exact hB ⟨j, hdist j (by linarith), hbig⟩
    · intro j hj hbig hjT
      change j < K at hj
      by_contra hclose
      have hc : T - (j + 1 : ℝ) / N ≤ δ := le_of_not_gt hclose
      let d := K - 1 - j
      have hindex : K = d + j + 1 := by dsimp [d]; omega
      have hcast : (K : ℝ) = d + j + 1 := by exact_mod_cast hindex
      have hmul := mul_le_mul_of_nonneg_right hc hN.le
      have hcancel : (T - (j + 1 : ℝ) / N) * N = T * N - (j + 1) := by
        field_simp
      rw [hcancel] at hmul
      have hd : d ∈ Finset.range (L + 1) := hdist d (by nlinarith only [hK, hcast, hmul])
      have hjEq : K - 1 - d = j := by omega
      exact hD ⟨d, hd, by simpa only [hjEq] using hbig⟩
    · intro i j hij hj hbi hbj
      change j < K at hj
      by_contra hclose
      have hc : (j + 1 : ℝ) / N - (i + 1 : ℝ) / N ≤ δ := le_of_not_gt hclose
      let d := j - i - 1
      have hindex : i + d + 1 = j := by dsimp [d]; omega
      have hcast : (i : ℝ) + d + 1 = j := by exact_mod_cast hindex
      have hmul := mul_le_mul_of_nonneg_right hc hN.le
      have hcancel : ((j + 1 : ℝ) / N - (i + 1 : ℝ) / N) * N = j - i := by
        field_simp
        ring
      rw [hcancel] at hmul
      have hd : d ∈ Finset.range (L + 1) := hdist d (by linarith only [hcast, hmul])
      exact hA ⟨i, Finset.mem_range.mpr (hij.trans hj), d, hd, hbi,
        by simpa only [hindex] using hbj⟩
  have hsingle (j : ℕ) : P.real {ω | a < |X j ω|} = q := by
    have h := (hident j).measure_mem_eq
      (measurableSet_lt measurable_const continuous_abs.measurable :
        MeasurableSet {x : ℝ | a < |x|})
    exact congrArg ENNReal.toReal h
  have hB : P.real B ≤ (L + 1 : ℕ) * q := by
    exact (prob_exists_finset_le P (Finset.range (L + 1))
      (fun d => {ω | a < |X d ω|}) q (fun d _ => (hsingle d).le)).trans_eq (by simp)
  have hD : P.real D ≤ (L + 1 : ℕ) * q := by
    exact (prob_exists_finset_le P (Finset.range (L + 1))
      (fun d => {ω | a < |X (K - 1 - d) ω|}) q
      (fun d _ => (hsingle _).le)).trans_eq (by simp)
  have hA : P.real A ≤ (K : ℝ) * ((L + 1 : ℕ) * q ^ 2) := by
    apply (prob_exists_finset_le P (Finset.range K)
      (fun i => {ω | ∃ d ∈ Finset.range (L + 1),
        a < |X i ω| ∧ a < |X (i + d + 1) ω|})
      (((L + 1 : ℕ) : ℝ) * q ^ 2) ?_).trans_eq (by simp)
    intro i hi
    apply (prob_exists_finset_le P (Finset.range (L + 1))
      (fun d => {ω | a < |X i ω| ∧ a < |X (i + d + 1) ω|}) (q ^ 2) ?_).trans_eq
      (by simp)
    intro d hd
    exact (iid_large_pair_prob P X hind hident a (by omega : i ≠ i + d + 1)).le
  calc P.real _ ≤ P.real (A ∪ (B ∪ D)) := measureReal_mono hsub
    _ ≤ P.real A + (P.real B + P.real D) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le B D))
    _ ≤ (K : ℝ) * ((L + 1 : ℕ) * q ^ 2) +
        (((L + 1 : ℕ) : ℝ) * q + ((L + 1 : ℕ) : ℝ) * q) :=
      add_le_add hA (add_le_add hB hD)
    _ = _ := by dsimp [K, L, N, q]; simp only [Nat.cast_add, Nat.cast_one]; ring

private theorem finite_grid_separation (N0 : ℕ) {T b : ℝ} (hT : 0 < T) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ δ < b ∧
      ∀ n < N0, ∀ {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω),
        ∃ s : Finset (J1Window T),
          ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
          (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
          (∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
            ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  classical
  let gaps := (Finset.range N0).biUnion fun n =>
    (Finset.range ⌊((n + 1 : ℕ) : ℝ) * T⌋₊).image fun j : ℕ =>
      T - (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ)
  obtain ⟨δ, hδ, hδb, hδgap⟩ := exists_small_positive_gap gaps
    (lt_min hT (lt_min hb (by positivity : 0 < 1 / (N0 + 1 : ℝ))))
  have hδT : δ < T := hδb.trans_le (min_le_left _ _)
  have hδb' : δ < b := hδb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδgrid : δ < 1 / (N0 + 1 : ℝ) :=
    hδb.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, hδT, hδb', ?_⟩
  intro n hn Ω X a ω
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hNle : N ≤ N0 + 1 := by dsimp [N]; exact_mod_cast (by omega : n + 1 ≤ N0 + 1)
  have hδN : δ < 1 / N := hδgrid.trans_le
    (div_le_div_of_nonneg_left (by norm_num) hN hNle)
  apply exists_cuts_of_gap_bounds X a n hT ω hδT
  · intro j hj hbig
    exact hδN.trans_le ((div_le_div_iff_of_pos_right hN).mpr
      (by linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
  · intro j hj hbig hjT
    apply hδgap _ ?_ (sub_pos.mpr hjT)
    apply Finset.mem_biUnion.mpr
    refine ⟨n, Finset.mem_range.mpr hn, ?_⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  · intro i j hij hj hbi hbj
    have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have hgap : 1 / N ≤ (j + 1 : ℝ) / N - (i + 1 : ℝ) / N := by
      rw [← sub_div, div_le_div_iff_of_pos_right hN]
      linarith
    exact hδN.trans_le hgap

/-- large iid increments have uniformly separated cuts for every positive tail index
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_separated_cuts_prob_gen {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (_hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P)
    (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν0 : 0 < ν) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    (hT : 0 < T) :
    ∀ ρ : ℝ, 0 < ρ → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∀ n : ℕ,
        P.real {ω | ¬ ∃ s : Finset (J1Window T),
          ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
          (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
          (∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ →
            ρ * ((n + 1 : ℕ) : ℝ) ^ (1 / ν) < |X j ω| →
            ∃ c ∈ s,
              (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))} ≤ η := by
  intro ρ hρ η hη
  let B : ℝ := C * ρ ^ (-ν)
  let D : ℝ := T * B ^ 2 + 2 * B
  have hB : 0 < B := mul_pos hC (Real.rpow_pos_of_pos hρ _)
  have hD : 0 < D := by dsimp [D]; positivity
  let b : ℝ := η / (4 * D)
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max ((ρ ^ ν)⁻¹) b⁻¹)
  obtain ⟨δ, hδ, hδT, hδb, hsmall⟩ := finite_grid_separation N0 hT hb
  refine ⟨δ, hδ, hδT, fun n => ?_⟩
  by_cases hn : n < N0
  · have he : {ω | ¬ ∃ s : Finset (J1Window T),
        ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
        (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
        (∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ →
          ρ * ((n + 1 : ℕ) : ℝ) ^ (1 / ν) < |X j ω| →
          ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      exact hω (hsmall n hn X _ ω)
    rw [he]
    simpa using hη.le
  · let N : ℝ := ((n + 1 : ℕ) : ℝ)
    let a := ρ * N ^ (1 / ν)
    let q := P.real {ω | a < |X 0 ω|}
    let K : ℝ := ⌊N * T⌋₊
    let L : ℝ := ⌊δ * N⌋₊ + 1
    have hN : 0 < N := by dsimp [N]; positivity
    have hN0N : (N0 : ℝ) < N := by dsimp [N]; exact_mod_cast (by omega : N0 < n + 1)
    have hlarge : (ρ ^ ν)⁻¹ < N :=
      (le_max_left _ _).trans_lt (hN0.trans hN0N)
    have hbN : b⁻¹ < N := (le_max_right _ _).trans_lt (hN0.trans hN0N)
    have hNb : 1 / N < b := by
      apply (div_lt_iff₀ hN).mpr
      have hmul := mul_lt_mul_of_pos_left hbN hb
      rw [mul_inv_cancel₀ hb.ne'] at hmul
      simpa only [mul_comm] using hmul
    have ha : 0 < a := mul_pos hρ (Real.rpow_pos_of_pos hN _)
    have hapow : a ^ ν = ρ ^ ν * N := by
      dsimp [a]
      rw [Real.mul_rpow hρ.le (Real.rpow_nonneg hN.le _),
        ← Real.rpow_mul hN.le, one_div, inv_mul_cancel₀ hν0.ne', Real.rpow_one]
    have ha1 : 1 ≤ a := by
      apply (Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 1) ha.le hν0).mp
      rw [Real.one_rpow, hapow]
      have hm := mul_lt_mul_of_pos_left hlarge (Real.rpow_pos_of_pos hρ ν)
      rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hρ ν).ne'] at hm
      exact hm.le
    have hpow : a ^ (-ν) = ρ ^ (-ν) / N := by
      rw [Real.rpow_neg ha.le, hapow, mul_inv, Real.rpow_neg hρ.le, div_eq_mul_inv]
    have hq : q ≤ B / N := by
      calc q ≤ C * a ^ (-ν) := hTail a ha1
        _ = B / N := by rw [hpow]; dsimp [B]; ring
    have hq0 : 0 ≤ q := measureReal_nonneg
    have hK : K ≤ N * T := Nat.floor_le (mul_nonneg hN.le hT.le)
    have hK0 : 0 ≤ K := by dsimp [K]; positivity
    have hL : L ≤ δ * N + 1 := by
      dsimp [L]
      linarith only [Nat.floor_le (mul_nonneg hδ.le hN.le)]
    have hL0 : 0 ≤ L := by dsimp [L]; positivity
    have hq2 : q ^ 2 ≤ (B / N) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    have hbound : K * L * q ^ 2 + 2 * L * q ≤ η := by
      calc K * L * q ^ 2 + 2 * L * q
          ≤ (N * T) * (δ * N + 1) * (B / N) ^ 2 +
              2 * (δ * N + 1) * (B / N) := by
            apply add_le_add
            · exact mul_le_mul (mul_le_mul hK hL hL0 (by positivity)) hq2
                (sq_nonneg _) (by positivity)
            · exact mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num)) hq
                hq0 (by positivity)
        _ = D * (δ + 1 / N) := by dsimp [D]; field_simp
        _ ≤ D * (b + b) := mul_le_mul_of_nonneg_left
          (add_le_add hδb.le hNb.le) hD.le
        _ ≤ η := by dsimp [b]; field_simp; nlinarith
    exact (gap_failure_prob_le P X hind hident a n hT hδ.le hδT).trans hbound

private theorem exists_partition_of_refined_cuts {T : ℝ} (hT : 0 < T)
    (s : Finset (J1Window T))
    (h0 : ⟨0, le_rfl, hT.le⟩ ∈ s) (hTs : ⟨T, hT.le, le_rfl⟩ ∈ s)
    {δ : ℝ} (hsep : ∀ a ∈ s, ∀ b ∈ s, (a : ℝ) < b → δ < (b : ℝ) - a) :
    ∃ p : WindowPartition T hT, p.IsSparse δ ∧
      (∀ i : Fin (p.n + 1), p.time i ∈ s) ∧
      ∀ i : Fin p.n, ∀ c ∈ s,
        ¬ ((p.time i.castSucc : ℝ) < c ∧ (c : ℝ) < p.time i.succ) := by
  classical
  let k := s.card
  have hk : 2 ≤ k := by
    apply Finset.one_lt_card.mpr
    refine ⟨_, h0, _, hTs, ?_⟩
    intro h
    have heq := congrArg Subtype.val h
    exact hT.ne' heq.symm
  have hlen : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  let e := s.orderEmbOfFin (show s.card = k from rfl)
  let p : WindowPartition T hT :=
    { n := k - 1
      n_pos := by omega
      time := fun i => e (Fin.cast hlen i)
      first := by
        apply Subtype.ext
        have hi : Fin.cast hlen (0 : Fin (k - 1 + 1)) = ⟨0, by omega⟩ := by
          ext
          rfl
        rw [hi, Finset.orderEmbOfFin_zero (show s.card = k from rfl) (by omega)]
        apply le_antisymm
        · exact Finset.min'_le _ _ h0
        · exact (s.min' ⟨_, h0⟩).property.1
      last := by
        apply Subtype.ext
        have hi : Fin.cast hlen (Fin.last (k - 1)) = ⟨k - 1, by omega⟩ := by
          ext
          rfl
        rw [hi, Finset.orderEmbOfFin_last (show s.card = k from rfl) (by omega)]
        apply le_antisymm
        · exact (s.max' ⟨_, hTs⟩).property.2
        · exact Finset.le_max' _ _ hTs
      strict := by
        intro i
        apply e.strictMono
        change Fin.cast hlen i.castSucc < Fin.cast hlen i.succ
        simp only [Fin.lt_def, Fin.val_cast]
        exact i.castSucc_lt_succ }
  have hmem (i : Fin (p.n + 1)) : p.time i ∈ s :=
    Finset.orderEmbOfFin_mem s _ _
  refine ⟨p, ?_, hmem, ?_⟩
  · intro i
    exact hsep _ (hmem i.castSucc) _ (hmem i.succ) (p.strict i)
  · intro i c hc hbetween
    have hc_range : c ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hc
    obtain ⟨j, rfl⟩ := hc_range
    have hleft : Fin.cast hlen i.castSucc < j := e.lt_iff_lt.mp hbetween.1
    have hright : j < Fin.cast hlen i.succ := e.lt_iff_lt.mp hbetween.2
    simp only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc, Fin.val_succ] at hleft hright
    omega

private theorem centered_modulus_le_of_refined_cuts {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C : ℝ} (hν : 1 < ν) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    (hint : Integrable (X 0) P) (hmean : ∫ ω, X 0 ω ∂P = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) (ha : 1 ≤ scaledSmallJumpLevel ν ρ n)
    {T : ℝ} (hT : 0 < T) (ω : Ω) {δ L0 r : ℝ} (hδ : 0 < δ) (hL : 4 * δ ≤ L0)
    (s : Finset (J1Window T))
    (h0 : ⟨0, le_rfl, hT.le⟩ ∈ s) (hTs : ⟨T, hT.le, le_rfl⟩ ∈ s)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u)
    (hcuts : ∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ →
      scaledSmallJumpLevel ν ρ n < |X j ω| →
        ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))
    (hRem : scaledSmallJumpRemainder P X ν ρ T n ω ≤ r) :
    cadlagModulus (hT := hT) (scaledPartialSumWindow X ν n hT ω).path δ ≤
      2 * r + (2 * C / (1 - (2 : ℝ) ^ (1 - ν))) * ρ ^ (1 - ν) *
        (L0 + 1 / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨s', hsub, hz, he, hs, hgap⟩ :=
    exists_separated_cuts_refinement hT hδ hL s h0 hTs hsep
  obtain ⟨p, hp, hmem, hbetween⟩ := exists_partition_of_refined_cuts hT s' hz he hs
  have hD : 0 ≤ 2 * C / (1 - (2 : ℝ) ^ (1 - ν)) * ρ ^ (1 - ν) := by
    have hq : (2 : ℝ) ^ (1 - ν) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    positivity
  apply cadlagModulus_le_of_sparse_partition _ p hp
  intro i
  have hno : ∀ t : J1Window T,
      (p.time i.castSucc : ℝ) ≤ t → (t : ℝ) < p.time i.succ →
      ∀ j : ℕ, ⌊((n + 1 : ℕ) : ℝ) * (p.time i.castSucc : ℝ)⌋₊ ≤ j →
        j < ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ →
          |X j ω| ≤ scaledSmallJumpLevel ν ρ n := by
    intro t hat htb j hjlo hjhi
    by_contra hnot
    have hbig : scaledSmallJumpLevel ν ρ n < |X j ω| := lt_of_not_ge hnot
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hjK : j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ :=
      hjhi.trans_le (Nat.floor_mono (mul_le_mul_of_nonneg_left t.property.2 hN.le))
    obtain ⟨c, hc, hctime⟩ := hcuts j hjK hbig
    apply hbetween i c (hsub hc)
    constructor
    · rw [hctime, lt_div_iff₀ hN]
      have hfloor := Nat.lt_floor_add_one (((n + 1 : ℕ) : ℝ) *
        (p.time i.castSucc : ℝ))
      have hcast : (⌊((n + 1 : ℕ) : ℝ) * (p.time i.castSucc : ℝ)⌋₊ : ℝ) ≤ j :=
        Nat.cast_le.mpr hjlo
      nlinarith only [hfloor, hcast]
    · have hcle : (c : ℝ) ≤ t := by
        rw [hctime, div_le_iff₀ hN]
        have hcast : (j + 1 : ℝ) ≤
            ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ := by exact_mod_cast hjhi
        have hfloor := Nat.floor_le (mul_nonneg hN.le t.property.1)
        nlinarith only [hcast, hfloor]
      exact hcle.trans_lt htb
  exact (scaledPartialSumWindow_blockOscillation_gt_one P X hX hident hν hC hTail
    hint hmean hρ n ha hT ω _ _ (p.strict i) r hRem hno).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add
        (hgap _ (hmem i.castSucc) _ (hmem i.succ) (p.strict i) (hbetween i)) le_rfl) hD))

/-- centered iid scaled windows have uniformly small sparse modulus above index one
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_modulus_prob_gt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν1 : 1 < ν) (hν2 : ν < 2) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    (hint : Integrable (X 0) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (hT : 0 < T) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∀ n : ℕ,
        P.real {ω | ε < cadlagModulus (hT := hT)
          (scaledPartialSumWindow X ν n hT ω).path δ} ≤ η := by
  intro ε hε η hη
  have hν0 : 0 < ν := by linarith
  obtain ⟨ρ, hρ, hRem⟩ := scaledSmallJumpRemainder_prob_gt_one P X hX hident hind
    hν1 hν2 hC hTail hint hmean hT (ε / 8) (by positivity) (η / 2) (by positivity)
  let D : ℝ := 2 * C / (1 - (2 : ℝ) ^ (1 - ν)) * ρ ^ (1 - ν)
  have hD : 0 < D := by
    have hq : (2 : ℝ) ^ (1 - ν) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    dsimp [D]
    positivity
  let L0 : ℝ := ε / (8 * D)
  have hL0 : 0 < L0 := by dsimp [L0]; positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max ((ρ ^ ν)⁻¹) L0⁻¹)
  obtain ⟨d, hd, hdT, hdL, hsmall⟩ := finite_grid_separation N0 hT
    (show 0 < L0 / 4 by positivity)
  obtain ⟨b, hb, hbT, hBad⟩ := scaledPartialSumWindow_separated_cuts_prob_gen
    P X hX hind hident hν0 hC hTail hT ρ hρ (η / 2) (by positivity)
  let δ : ℝ := min b d
  have hδ : 0 < δ := lt_min hb hd
  have hδT : δ < T := (min_le_left _ _).trans_lt hbT
  have hδL : 4 * δ ≤ L0 := by
    have hδd : δ ≤ d := min_le_right _ _
    linarith only [hδd, hdL]
  refine ⟨δ, hδ, hδT, fun n => ?_⟩
  by_cases hn : n < N0
  · have hmod (ω : Ω) :
        cadlagModulus (hT := hT) (scaledPartialSumWindow X ν n hT ω).path δ ≤ 0 := by
      obtain ⟨s, hs0, hsT, hssep, hscuts⟩ := hsmall n hn X (-1) ω
      have hzero : (fun j ω => if |X j ω| ≤ (-1 : ℝ) then X j ω else 0) =
          (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := by
        funext j ω
        have hnot : ¬ |X j ω| ≤ (-1 : ℝ) := by linarith [abs_nonneg (X j ω)]
        simp only [hnot, ite_false]
      have h := scaledPartialSumWindow_modulus_le_of_separated_cuts X ν (-1) n hT ω s
        hs0 hsT (fun u hu v hv huv =>
          (min_le_right b d).trans_lt (hssep u hu v hv huv)) hscuts
        (r := 0) (fun t => by rw [hzero, centered_window_apply_nat]; simp)
      simpa only [mul_zero] using h
    have he : {ω | ε < cadlagModulus (hT := hT)
        (scaledPartialSumWindow X ν n hT ω).path δ} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hω => (not_lt_of_ge ((hmod ω).trans hε.le)) hω
    rw [he]
    simpa using hη.le
  · let N : ℝ := ((n + 1 : ℕ) : ℝ)
    have hN : 0 < N := by dsimp [N]; positivity
    have hN0N : (N0 : ℝ) < N := by dsimp [N]; exact_mod_cast (by omega : N0 < n + 1)
    have hlarge : (ρ ^ ν)⁻¹ < N :=
      (le_max_left _ _).trans_lt (hN0.trans hN0N)
    have hNL : L0⁻¹ < N := (le_max_right _ _).trans_lt (hN0.trans hN0N)
    have hNinv : 1 / N < L0 := by
      apply (div_lt_iff₀ hN).mpr
      have hm := mul_lt_mul_of_pos_left hNL hL0
      rw [mul_inv_cancel₀ hL0.ne'] at hm
      simpa only [mul_comm] using hm
    have ha : 1 ≤ scaledSmallJumpLevel ν ρ n := by
      have hap : 0 < scaledSmallJumpLevel ν ρ n := by
        unfold scaledSmallJumpLevel
        positivity
      apply (Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 1) hap.le hν0).mp
      have he : (scaledSmallJumpLevel ν ρ n) ^ ν = ρ ^ ν * N := by
        unfold scaledSmallJumpLevel
        rw [Real.mul_rpow hρ.le (by positivity), ← Real.rpow_mul (by positivity),
          one_div, inv_mul_cancel₀ hν0.ne', Real.rpow_one]
        simp only [N, Nat.cast_add, Nat.cast_one]
      rw [Real.one_rpow, he]
      have hm := mul_lt_mul_of_pos_left hlarge (Real.rpow_pos_of_pos hρ ν)
      rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hρ ν).ne'] at hm
      exact hm.le
    let R : Set Ω := {ω | ε / 8 < scaledSmallJumpRemainder P X ν ρ T n ω}
    let B : Set Ω := {ω | ¬ ∃ s : Finset (J1Window T),
      ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
      (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → b < (v : ℝ) - u) ∧
      (∀ j : ℕ, j < ⌊N * T⌋₊ → scaledSmallJumpLevel ν ρ n < |X j ω| →
        ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / N)}
    have hBb : P.real B ≤ η / 2 := by
      simpa only [B, N, scaledSmallJumpLevel, Nat.cast_add, Nat.cast_one] using hBad n
    have hsub : {ω | ε < cadlagModulus (hT := hT)
        (scaledPartialSumWindow X ν n hT ω).path δ} ⊆ R ∪ B := by
      intro ω hω
      by_cases hr : ω ∈ R
      · exact Or.inl hr
      · right
        rintro ⟨s, hs0, hsT, hssep, hscuts⟩
        have hrem : scaledSmallJumpRemainder P X ν ρ T n ω ≤ ε / 8 :=
          le_of_not_gt hr
        have hdet := centered_modulus_le_of_refined_cuts P X hX hident hν1 hC hTail
          hint hmean hρ n ha hT ω hδ hδL s hs0 hsT
          (fun u hu v hv huv => (min_le_left b d).trans_lt (hssep u hu v hv huv))
          hscuts hrem
        have hbound : 2 * (ε / 8) + D * (L0 + 1 / N) ≤ ε := by
          calc 2 * (ε / 8) + D * (L0 + 1 / N)
              ≤ 2 * (ε / 8) + D * (L0 + L0) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left
                  (add_le_add le_rfl hNinv.le) hD.le)
            _ ≤ ε := by dsimp [L0]; field_simp; nlinarith
        exact (not_lt_of_ge (hdet.trans hbound)) hω
    calc P.real _ ≤ P.real (R ∪ B) := measureReal_mono hsub
      _ ≤ P.real R + P.real B := measureReal_union_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add (hRem n) hBb
      _ = η := by ring

private theorem window_value_le_sampleMax {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (ν : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T) (ω : Ω) (t : J1Window T) :
    |(scaledPartialSumWindow Y ν n hT ω).path.1 t| ≤
      scaledPartialSumWindow_sampleMax Y ν T n ω := by
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [scaledPartialSumWindow_apply,
    ← Int.natCast_floor_eq_floor (mul_nonneg hpos.le t.property.1)]
  have hnat (k : ℕ) : partialSumZ Y ω (k : ℤ) =
      ∑ j ∈ Finset.range k, Y j ω := by
    cases k with
    | zero => simp [partialSumZ]
    | succ k => simp [partialSumZ]
  rw [hnat]
  unfold scaledPartialSumWindow_sampleMax
  apply (Finset.le_sup'_iff _).mpr
  refine ⟨⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, ?_, le_rfl⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le
    (Nat.floor_mono (mul_le_mul_of_nonneg_left t.property.2 hpos.le)))

/-- the canonical Borel laws of centered iid scaled windows are tight above index one
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_isTight_gt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν1 : 1 < ν) (hν2 : ν < 2) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν))
    (hint : Integrable (X 0) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (hT : 0 < T) :
    MeasureTheory.IsTightMeasureSet
      (Set.range fun n : ℕ => P.map (scaledPartialSumWindow X ν n hT)) := by
  classical
  have hsup := scaledPartialSumWindow_sampleMax_tight X ν C T hT (by linarith)
    hν2 (by linarith : ν ≠ 1) hind hident hX hTail (Or.inr ⟨hν1, hint, hmean⟩)
  have hmod := scaledPartialSumWindow_modulus_prob_gt_one
    P X hX hind hident hν1 hν2 hC hTail hint hmean hT
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => htop ▸ le_top⟩
  let e : ℝ := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨M, hM⟩ := hsup (e / 2) (by positivity)
  have hchoices (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∀ n : ℕ,
      P.real {ω | 1 / (k + 1 : ℝ) < cadlagModulus (hT := hT)
        (scaledPartialSumWindow X ν n hT ω).path δ} ≤
          e / 4 * (1 / 2 : ℝ) ^ k :=
    hmod (1 / (k + 1 : ℝ)) (by positivity)
      (e / 4 * (1 / 2 : ℝ) ^ k) (by positivity)
  choose δ hδ hδT hδbound using hchoices
  let A : Set (J1WindowD T hT) := {f | (∀ t, |f.path.1 t| ≤ M) ∧
    ∀ k : ℕ, cadlagModulus (hT := hT) f.path (δ k) ≤ 1 / (k + 1 : ℝ)}
  have hcompact : IsCompact (closure A) := by
    apply isCompact_closure_of_bdd_sup_modulus hT A
    · exact ⟨M, fun f hf => hf.1⟩
    · intro r hr
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
      exact ⟨δ k, hδ k, hδT k, fun f hf => (hf.2 k).trans hk.le⟩
  have hsum : (∑' k : ℕ, ENNReal.ofReal (e / 4 * (1 / 2 : ℝ) ^ k)) =
      ENNReal.ofReal (e / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_two.mul_left (e / 4)), tsum_mul_left, tsum_geometric_two]
    congr 1
    ring
  refine ⟨closure A, hcompact, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_scaledPartialSumWindow P X hX ν n hT) hcompact.isClosed.measurableSet.compl]
  have hsubset : (scaledPartialSumWindow X ν n hT) ⁻¹' (closure A)ᶜ ⊆
      {ω | M < scaledPartialSumWindow_sampleMax X ν T n ω} ∪
        ⋃ k : ℕ, {ω | 1 / (k + 1 : ℝ) < cadlagModulus (hT := hT)
          (scaledPartialSumWindow X ν n hT ω).path (δ k)} := by
    intro ω hω
    by_cases hs : M < scaledPartialSumWindow_sampleMax X ν T n ω
    · exact Or.inl hs
    · right
      have hnot : scaledPartialSumWindow X ν n hT ω ∉ A :=
        fun h => hω (subset_closure h)
      have hb : ∀ t : J1Window T,
          |(scaledPartialSumWindow X ν n hT ω).path.1 t| ≤ M :=
        fun t => (window_value_le_sampleMax X ν n hT ω t).trans (le_of_not_gt hs)
      have hm : ¬ ∀ k : ℕ, cadlagModulus (hT := hT)
          (scaledPartialSumWindow X ν n hT ω).path (δ k) ≤ 1 / (k + 1 : ℝ) :=
        fun h => hnot ⟨hb, h⟩
      obtain ⟨k, hk⟩ := not_forall.mp hm
      exact Set.mem_iUnion.mpr ⟨k, lt_of_not_ge hk⟩
  have hMb : P {ω | M < scaledPartialSumWindow_sampleMax X ν T n ω} ≤
      ENNReal.ofReal (e / 2) := by
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hM n)
  have hdb (k : ℕ) : P {ω | 1 / (k + 1 : ℝ) < cadlagModulus (hT := hT)
      (scaledPartialSumWindow X ν n hT ω).path (δ k)} ≤
        ENNReal.ofReal (e / 4 * (1 / 2 : ℝ) ^ k) := by
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hδbound k n)
  calc P _ ≤ P ({ω | M < scaledPartialSumWindow_sampleMax X ν T n ω} ∪
        ⋃ k : ℕ, {ω | 1 / (k + 1 : ℝ) < cadlagModulus (hT := hT)
          (scaledPartialSumWindow X ν n hT ω).path (δ k)}) := measure_mono hsubset
    _ ≤ P {ω | M < scaledPartialSumWindow_sampleMax X ν T n ω} +
        P (⋃ k : ℕ, {ω | 1 / (k + 1 : ℝ) < cadlagModulus (hT := hT)
          (scaledPartialSumWindow X ν n hT ω).path (δ k)}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (e / 2) +
        ∑' k : ℕ, P {ω | 1 / (k + 1 : ℝ) < cadlagModulus (hT := hT)
          (scaledPartialSumWindow X ν n hT ω).path (δ k)} :=
      add_le_add hMb (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal (e / 2) +
        ∑' k : ℕ, ENNReal.ofReal (e / 4 * (1 / 2 : ℝ) ^ k) :=
      add_le_add le_rfl (tsum_le_tsum hdb)
    _ = ε := by
      rw [hsum, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have heq : e / 2 + e / 2 = e := by ring
      rw [heq]
      exact ENNReal.ofReal_toReal htop

end DirectedDistances.Probability
