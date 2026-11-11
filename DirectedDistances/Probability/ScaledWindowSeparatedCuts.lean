module

public import DirectedDistances.Probability.ScaledWindowModulusTight
public import DirectedDistances.Probability.ScaledSmallJumpRemainder
public import DirectedDistances.Probability.ScaledPartialSumWindow
public import DirectedDistances.Probability.SkorokhodJ1WindowTightness
public import DirectedDistances.Probability.PowerTailBounds

/-! # Small-jump identification and separated cuts for scaled windows

These helpers are not the paper result. -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- below index one, truncation has no centering and equals the window's small increment;
not the paper result. -/
theorem scaledTruncatedIncrement_eq_ite_lt_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) {ν : ℝ} (hν : ν < 1)
    (ρ : ℝ) (n j : ℕ) (ω : Ω) :
    scaledTruncatedIncrement P X ν ρ n j ω =
      if |X j ω| ≤ ρ * ((n + 1 : ℕ) : ℝ) ^ (1 / ν) then X j ω else 0 := by
  have hnot : ¬ 1 < ν := by linarith
  simp only [scaledTruncatedIncrement, scaledSmallJumpLevel, hnot, ite_false, sub_zero]
  simp only [Nat.cast_add, Nat.cast_one]
  by_cases h : |X j ω| ≤ ρ * (n + 1 : ℝ) ^ (1 / ν)
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h, ite_true, mul_one]
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h, ite_false, mul_zero]

/-- the uncentered small-jump remainder is exactly the finite sampled window maximum;
not the paper result. -/
theorem scaledSmallJumpRemainder_eq_sampleMax_lt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    {ν : ℝ} (hν : ν < 1) (ρ T : ℝ) (n : ℕ) (ω : Ω) :
    scaledSmallJumpRemainder P X ν ρ T n ω =
      scaledPartialSumWindow_sampleMax
        (fun j ω => if |X j ω| ≤ ρ * ((n + 1 : ℕ) : ℝ) ^ (1 / ν)
          then X j ω else 0) ν T n ω := by
  let c : ℝ := (n + 1 : ℝ) ^ (-(1 / ν))
  have hc : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  unfold scaledSmallJumpRemainder scaledPartialSumWindow_sampleMax
  simp_rw [scaledTruncatedIncrement_eq_ite_lt_one P X hν]
  simp only [Nat.cast_add, Nat.cast_one]
  change c * (Finset.range (⌊(n + 1 : ℝ) * T⌋₊ + 1)).sup'
    Finset.nonempty_range_add_one _ = _
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℝ => c * x)
    (fun x y => mul_max_of_nonneg _ _ hc)]
  apply Finset.sup'_congr _ rfl
  intro m hm
  change c * |_| = |c * _|
  rw [abs_mul, abs_of_nonneg hc]

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

/-- the small-window bad event has uniformly small probability below index one;
not the paper result. -/
theorem scaledPartialSumWindow_small_part_prob_lt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν)) (hT : 0 < T) :
    ∀ r : ℝ, 0 < r → ∀ η : ℝ, 0 < η →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ,
        P.real {ω | ∃ t : J1Window T,
          r < |(scaledPartialSumWindow
            (fun j ω => if |X j ω| ≤ ρ * ((n + 1 : ℕ) : ℝ) ^ (1 / ν)
              then X j ω else 0) ν n hT ω).path.1 t|} ≤ η := by
  intro r hr η hη
  obtain ⟨ρ, hρ, hbound⟩ := scaledSmallJumpRemainder_prob_lt_one P X hX hident hind
    hν0 hν1 hC hTail hT r hr η hη
  refine ⟨ρ, hρ, fun n => ?_⟩
  apply le_trans (measureReal_mono ?_) (hbound n)
  rintro ω ⟨t, ht⟩
  apply lt_of_lt_of_le ht
  rw [scaledSmallJumpRemainder_eq_sampleMax_lt_one P X hν1]
  exact window_value_le_sampleMax _ ν n hT ω t

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

/-- large iid increments admit uniformly separated cuts with high probability;
not the paper result. -/
theorem scaledPartialSumWindow_separated_cuts_prob {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (_hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P)
    (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν0 : 0 < ν) (_hν1 : ν < 1) (hC : 0 < C)
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

/-- the scaled iid window has uniformly small sparse modulus below index one;
not the paper result. -/
theorem scaledPartialSumWindow_modulus_prob_lt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν)) (hT : 0 < T) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∀ n : ℕ,
        P.real {ω | ε < cadlagModulus (hT := hT)
          (scaledPartialSumWindow X ν n hT ω).path δ} ≤ η := by
  intro ε hε η hη
  obtain ⟨ρ, hρ, hRem⟩ := scaledPartialSumWindow_small_part_prob_lt_one
    P X hX hind hident hν0 hν1 hC hTail hT (ε / 2) (by positivity)
      (η / 2) (by positivity)
  obtain ⟨δ, hδ, hδT, hBad⟩ := scaledPartialSumWindow_separated_cuts_prob
    P X hX hind hident hν0 hν1 hC hTail hT ρ hρ (η / 2) (by positivity)
  refine ⟨δ, hδ, hδT, fun n => ?_⟩
  have h := scaledPartialSumWindow_modulus_prob_le_of_bad_event_bounds P X ν
    (ρ * ((n + 1 : ℕ) : ℝ) ^ (1 / ν)) n hT δ (ε / 2) (η / 2) (η / 2)
      (hRem n) (hBad n)
  have he : 2 * (ε / 2) = ε := by ring
  have hηeq : η / 2 + η / 2 = η := by ring
  rwa [he, hηeq] at h

/-- the Borel laws of the scaled iid windows are tight below index one, assuming
the window maps are almost everywhere measurable; not the paper result. -/
theorem scaledPartialSumWindow_isTight_lt_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    {ν C T : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hC : 0 < C)
    (hTail : ∀ x : ℝ, 1 ≤ x →
      P.real {ω | x < |X 0 ω|} ≤ C * x ^ (-ν)) (hT : 0 < T)
    [MeasurableSpace (J1WindowD T hT)] [BorelSpace (J1WindowD T hT)]
    (hWmeas : ∀ n : ℕ, AEMeasurable (scaledPartialSumWindow X ν n hT) P) :
    MeasureTheory.IsTightMeasureSet
      (Set.range fun n : ℕ => P.map (scaledPartialSumWindow X ν n hT)) := by
  classical
  have hsup := scaledPartialSumWindow_sampleMax_tight X ν C T hT hν0
    (by linarith : ν < 2) (by linarith : ν ≠ 1) hind hident hX hTail (Or.inl hν1)
  have hmod := scaledPartialSumWindow_modulus_prob_lt_one
    P X hX hind hident hν0 hν1 hC hTail hT
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
  rw [Measure.map_apply_of_aemeasurable (hWmeas n) hcompact.isClosed.measurableSet.compl]
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
