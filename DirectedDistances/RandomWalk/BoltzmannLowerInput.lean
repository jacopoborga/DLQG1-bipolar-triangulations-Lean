module

public import DirectedDistances.RandomWalk.HittingTightness

/-! # Elementary height input for the Boltzmann lower bound

Helpers replacing the `lem-cond-walk-bm` input of `lem-boltzmann-ldp-lower`,
specifically `eqn-boltzmann-ldp-lower-half`, -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- First-coordinate survival, by twice rotating the iid codes. Helper replacing
`lem-cond-walk-bm` in `lem-boltzmann-ldp-lower` -/
theorem lazy_fst_survival_bound (r K N : ℕ) (hr : 1 ≤ r) (hK : r ≤ K)
    (hN : 0 < N) :
    iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).1} ≤
      (r : ℝ) / ((r : ℝ) + K) + (3 / 2 : ℝ) * ((K : ℝ) + 1) ^ 2 / N := by
  have hm : MeasurableSet {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (((measurable_pi_apply n).comp measurable_codeWalk).snd)
  have he : iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).1} =
      iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} := by
    have hmp := measurePreserving_codeRelabel.comp measurePreserving_codeRelabel
    have hh := map_measureReal_apply (μ := iidCodeMeasure) hmp.measurable hm
    rw [hmp.map_eq] at hh
    rw [hh]
    congr 1
    ext ω
    have hrot (n : ℕ) :
        (codeWalk (codeRelabel (codeRelabel ω)) n).2 = (codeWalk ω n).1 := by
      rw [codeWalk_codeRelabel, codeWalk_codeRelabel]
      dsimp only [stepRotate]
      omega
    change (∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).1) ↔
      (∀ n ≤ N, -(r : ℤ) < (codeWalk (codeRelabel (codeRelabel ω)) n).2)
    simp only [hrot]
  rw [he]
  exact lazy_survival_bound r K N hr hK hN

/-- Literal first-coordinate coupling formula, including the minimum with zero.
not a paper result. -/
theorem vectorPitman_codeWalk_fst (ω : ℕ → Fin 3) (n : ℕ) :
    (vectorPitman (codeWalk ω) n).1 = (codeWalk ω n).1 -
      2 * min 0 (globalLazyRunningMinimum (fun k => (codeWalk ω k).1) n) := by
  have hm := globalLazyRunningMinimum_le (fun k => (codeWalk ω k).1) (Nat.zero_le n)
  simp only [codeWalk_zero] at hm
  rw [min_eq_right hm]
  rfl

/-- A later coupled height dominates the negative running minimum at an earlier
time. Helper replacing `lem-cond-walk-bm` in `lem-boltzmann-ldp-lower` -/
theorem vectorPitman_codeWalk_fst_ge_neg_minimum (ω : ℕ → Fin 3)
    (m n : ℕ) (hmn : m ≤ n) :
    -globalLazyRunningMinimum (fun k => (codeWalk ω k).1) m ≤
      (vectorPitman (codeWalk ω) n).1 := by
  have hn := globalLazyRunningMinimum_le (fun k => (codeWalk ω k).1) (i := n) le_rfl
  have hmono : globalLazyRunningMinimum (fun k => (codeWalk ω k).1) n ≤
      globalLazyRunningMinimum (fun k => (codeWalk ω k).1) m := by
    apply le_globalLazyRunningMinimum
    intro k hk
    exact globalLazyRunningMinimum_le _ (hk.trans hmn)
  change _ ≤ (codeWalk ω n).1 - 2 * globalLazyRunningMinimum _ n
  omega

private theorem survival_scale_error (s B D : ℝ) (hs : 1 ≤ s)
    (hB : 1 ≤ B) (hD : 0 < D) :
    s / (s + s * B) + (3 / 2 : ℝ) * (s * B + 1) ^ 2 / (D * s ^ 2) ≤
      1 / B + 6 * B ^ 2 / D := by
  have hspos : 0 < s := by linarith
  have hBpos : 0 < B := by linarith
  have hfirst : s / (s + s * B) ≤ 1 / B := by
    apply (div_le_div_iff₀ (by positivity) hBpos).mpr
    nlinarith
  have hsB : 1 ≤ s * B := by nlinarith
  have hsq : (s * B + 1) ^ 2 ≤ 4 * s ^ 2 * B ^ 2 := by
    nlinarith [sq_nonneg (s * B - 1)]
  have hsecond : (3 / 2 : ℝ) * (s * B + 1) ^ 2 / (D * s ^ 2) ≤
      6 * B ^ 2 / D := by
    apply (div_le_div_iff₀ (by positivity) hD).mpr
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hsq)]
  exact add_le_add hfirst hsecond

private theorem measurable_boltzmann_coupling :
    Measurable (fun ω : ℕ → Fin 3 => vectorPitman (codeWalk ω)) := by
  have hL : Measurable (fun ω : ℕ → Fin 3 => fun k => (codeWalk ω k).1) := by
    exact Measurable.of_eval fun k => ((measurable_pi_apply k).comp measurable_codeWalk).fst
  apply Measurable.of_eval
  intro n
  exact ((((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hL).prodMk
    ((((measurable_pi_apply n).comp measurable_codeWalk).snd).add
      ((measurable_globalLazyRunningMinimum n).comp hL)))

private theorem measurableSet_first_hit_height (q : ℕ) (b : ℝ) :
    MeasurableSet {p : ℕ → ℤ × ℤ | ∃ n : ℕ,
      (p n).2 = -(q : ℤ) ∧ (∀ k < n, (p k).2 ≠ -(q : ℤ)) ∧
        b ≤ ((p n).1 : ℝ)} := by
  simp only [Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  refine (measurableSet_eq_fun ((measurable_pi_apply n).snd) measurable_const).inter ?_
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro _
    exact (measurableSet_eq_fun ((measurable_pi_apply k).snd) measurable_const).compl
  · exact measurableSet_le measurable_const (by fun_prop)

/-- Elementary replacement for the `lem-cond-walk-bm` input of
`lem-boltzmann-ldp-lower`, `eqn-boltzmann-ldp-lower-half`
hit of `-⌊r/2⌋`; this helper is not a numbered paper result. -/
theorem conditionedVectorPathLaw_first_hit_height_lower (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      1 - δ / 2 ≤ (conditionedVectorPathLaw 0 0).real
        {p | ∃ n : ℕ, (p n).2 = -((r / 2 : ℕ) : ℤ) ∧
          (∀ k < n, (p k).2 ≠ -((r / 2 : ℕ) : ℤ)) ∧
          c * (r : ℝ) ≤ ((p n).1 : ℝ)} := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (16 / δ) 1)
  have hB1 : (1 : ℝ) ≤ B := (le_max_right _ _).trans hB.le
  have hBpos : (0 : ℝ) < B := by linarith
  have hBn : 1 ≤ B := by exact_mod_cast hB1
  have hBδ : 16 < δ * B := by
    have := (div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hB)
    nlinarith
  obtain ⟨D, hD⟩ := exists_nat_gt (max (48 * (B : ℝ) ^ 2 / δ) 1)
  have hD1 : (1 : ℝ) ≤ D := (le_max_right _ _).trans hD.le
  have hDpos : (0 : ℝ) < D := by linarith
  have hDn : 1 ≤ D := by exact_mod_cast hD1
  have hDδ : 48 * (B : ℝ) ^ 2 < δ * D := by
    have := (div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hD)
    nlinarith
  let A : ℕ := 8 * B
  let H : ℕ := 6 * A * D
  have hAn : 1 ≤ A := by dsimp [A]; omega
  have hHn : 6 ≤ H := by dsimp [H]; nlinarith
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hearly : 4 * Real.exp (-(A : ℝ) / 8) ≤ δ / 4 := by
    have hexp : Real.exp (-(B : ℝ)) ≤ 1 / (B : ℝ) := by
      rw [Real.exp_neg, one_div]
      exact (inv_le_inv₀ (Real.exp_pos _) hBpos).mpr
        (by linarith [Real.add_one_le_exp (B : ℝ)])
    have heq : -(A : ℝ) / 8 = -(B : ℝ) := by dsimp [A]; push_cast; ring
    rw [heq]
    have hfrac : 4 / (B : ℝ) ≤ δ / 4 := by
      apply (div_le_iff₀ hBpos).mpr
      nlinarith
    calc
      4 * Real.exp (-(B : ℝ)) ≤ 4 * (1 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 / (B : ℝ) := by ring
      _ ≤ δ / 4 := hfrac
  refine ⟨1 / (H : ℝ), by positivity, H, ?_⟩
  intro r hr
  let q := r / 2
  let s := r / H + 1
  let N := D * s ^ 2
  have hs : 1 ≤ s := Nat.succ_le_succ (Nat.zero_le (r / H))
  have hN : 0 < N := by dsimp [N]; positivity
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hsH : s * H ≤ 2 * r := by
    have hd := Nat.div_mul_le_self r H
    dsimp [s]
    nlinarith
  have hrq : 2 * r ≤ 6 * q := by dsimp [q]; omega
  have hqbig : A * D * s ≤ q := by
    dsimp [H] at hsH
    nlinarith
  have htime : (N : ℝ) ≤ (q : ℝ) ^ 2 / A := by
    apply (le_div_iff₀ hApos).mpr
    have hbig : (A : ℝ) * D * s ≤ q := by exact_mod_cast hqbig
    have hAD : (1 : ℝ) ≤ (A : ℝ) * D := by
      exact_mod_cast (show 1 ≤ A * D by nlinarith)
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (A : ℝ) * D * s)
      (by positivity : 0 ≤ (q : ℝ))).mpr hbig
    have hmul := mul_nonneg (sub_nonneg.mpr hAD)
      (show 0 ≤ (A : ℝ) * D * (s : ℝ) ^ 2 by positivity)
    dsimp [N]
    push_cast
    nlinarith only [hsq, hmul]
  have hlevel : (r : ℝ) / H ≤ s := by
    have hlt : r < (r / H + 1) * H := by
      have := Nat.mod_lt r (show 0 < H by omega)
      have := Nat.mod_add_div r H
      nlinarith
    apply (div_le_iff₀ hHpos).mpr
    exact_mod_cast hlt.le
  have hsurv : iidCodeMeasure.real
      {ω | ∀ n ≤ N, -(s : ℤ) < (codeWalk ω n).1} ≤ δ / 4 := by
    have hb := lazy_fst_survival_bound s (s * B) N hs (by nlinarith) hN
    have he := survival_scale_error (s : ℝ) B D (by exact_mod_cast hs) hB1 hDpos
    have hf : 1 / (B : ℝ) ≤ δ / 8 := by
      apply (div_le_iff₀ hBpos).mpr
      nlinarith
    have hg : 6 * (B : ℝ) ^ 2 / D ≤ δ / 8 := by
      apply (div_le_iff₀ hDpos).mpr
      nlinarith
    dsimp [N] at hb
    push_cast at hb
    exact hb.trans (he.trans (by linarith))
  let E : Set (ℕ → ℤ × ℤ) := {p | ∃ n : ℕ,
    (p n).2 = -(q : ℤ) ∧ (∀ k < n, (p k).2 ≠ -(q : ℤ)) ∧
      (1 / (H : ℝ)) * r ≤ ((p n).1 : ℝ)}
  let F : Set (ℕ → Fin 3) := (fun ω => vectorPitman (codeWalk ω)) ⁻¹' E
  let S : Set (ℕ → Fin 3) := {ω | ∀ n ≤ N, -(s : ℤ) < (codeWalk ω n).1}
  let T : Set (ℕ → Fin 3) := {ω | ∃ n : ℕ, (n : ℝ) < (q : ℝ) ^ 2 / A ∧
    (vectorPitman (codeWalk ω) n).2 ≤ -(q : ℤ)}
  have hE : MeasurableSet E := measurableSet_first_hit_height q _
  have hF : MeasurableSet F := hE.preimage measurable_boltzmann_coupling
  have hsub : Fᶜ ≤ᵐ[iidCodeMeasure] S ∪ T := by
    filter_upwards [ae_vectorPitman_codeWalk_hits] with ω hω
    intro hbad
    by_cases hT : ω ∈ T
    · exact Or.inr hT
    · left
      by_contra hS
      have hlow : ∃ k ≤ N, (codeWalk ω k).1 ≤ -(s : ℤ) := by
        by_contra h
        apply hS
        intro k hk
        by_contra hv
        exact h ⟨k, hk, le_of_not_gt hv⟩
      obtain ⟨k, hk, hlow⟩ := hlow
      have hhit := hω q
      let n := Nat.find hhit
      have hn : (vectorPitman (codeWalk ω) n).2 = -(q : ℤ) := Nat.find_spec hhit
      have hnN : N ≤ n := by
        by_contra h
        apply hT
        exact ⟨n, (by exact_mod_cast (lt_of_lt_of_le
          (show (n : ℝ) < N by exact_mod_cast (show n < N by omega)) htime)), hn.le⟩
      apply hbad
      refine ⟨n, hn, ?_, ?_⟩
      · intro j hj
        exact Nat.find_min hhit hj
      · have hm := globalLazyRunningMinimum_le (fun j => (codeWalk ω j).1) hk
        have hp := vectorPitman_codeWalk_fst_ge_neg_minimum ω N n hnN
        have height : (s : ℤ) ≤ (vectorPitman (codeWalk ω) n).1 := by omega
        have heightr : (s : ℝ) ≤ ((vectorPitman (codeWalk ω) n).1 : ℝ) := by
          exact_mod_cast height
        calc
          (1 / (H : ℝ)) * r = (r : ℝ) / H := by ring
          _ ≤ s := hlevel
          _ ≤ _ := heightr
  have hbad : iidCodeMeasure.real Fᶜ ≤ δ / 2 := by
    calc
      iidCodeMeasure.real Fᶜ ≤ iidCodeMeasure.real (S ∪ T) :=
        ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
      _ ≤ iidCodeMeasure.real S + iidCodeMeasure.real T := measureReal_union_le _ _
      _ ≤ δ / 4 + 4 * Real.exp (-(A : ℝ) / 8) :=
        add_le_add hsurv (vectorPitman_codeWalk_early_hit_tail q hq A hApos)
      _ ≤ δ / 2 := by linarith
  have htotal := measureReal_add_measureReal_compl (μ := iidCodeMeasure) hF
  rw [probReal_univ] at htotal
  rw [← map_vectorPitman_codeWalk,
    map_measureReal_apply measurable_boltzmann_coupling hE]
  change 1 - δ / 2 ≤ iidCodeMeasure.real F
  linarith

end DirectedDistances.RandomWalk
