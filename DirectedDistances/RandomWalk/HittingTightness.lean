module

public import DirectedDistances.RandomWalk.IIDVectorWalk
public import DirectedDistances.RandomWalk.IIDWalkMaximalTailBound
public import DirectedDistances.RandomWalk.IIDCodeRelabel
import DirectedDistances.RandomWalk.LazySurvivalProbability

/-! # Elementary estimates for the Pitman-coupled hitting event

Helpers replacing the `lem-cond-walk-bm` input in the proof of
These are auxiliary estimates, not numbered paper results. Hitting events are
written explicitly; no paper stopping time is defined here. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- Coupling identity for the helper replacing the `lem-cond-walk-bm` input of -/
theorem vectorPitman_codeWalk_snd (ω : ℕ → Fin 3) (n : ℕ) :
    (vectorPitman (codeWalk ω) n).2 = (codeWalk ω n).2 +
      globalLazyRunningMinimum (fun k => (codeWalk ω k).1) n := rfl

/-- The coupled vertical path lies below the original path; helper replacing -/
theorem vectorPitman_codeWalk_snd_le (ω : ℕ → Fin 3) (n : ℕ) :
    (vectorPitman (codeWalk ω) n).2 ≤ (codeWalk ω n).2 := by
  have hm := globalLazyRunningMinimum_le (fun k => (codeWalk ω k).1) (Nat.zero_le n)
  rw [codeWalk_zero] at hm
  rw [vectorPitman_codeWalk_snd]
  dsimp at hm
  omega

private theorem runningMinimum_succ' (p : ℕ → ℤ) (n : ℕ) :
    globalLazyRunningMinimum p (n + 1) = min (globalLazyRunningMinimum p n) (p (n + 1)) := by
  have h := runningMinimum_succ (fun j : Fin (n + 1 + 1) => p j.val)
    (⟨n, by omega⟩ : Fin (n + 1))
  simpa only [runningMinimum_prefix_eq_global, Fin.val_succ, Fin.val_castSucc] using h

/-- Unit vertical steps of the coupled walk; helper replacing the Brownian-limit -/
theorem vectorPitman_codeWalk_snd_step (ω : ℕ → Fin 3) (n : ℕ) :
    |(vectorPitman (codeWalk ω) (n + 1)).2 -
      (vectorPitman (codeWalk ω) n).2| ≤ 1 := by
  have h := codeWalk_succ_sub ω n
  have hm := globalLazyRunningMinimum_le (fun k => (codeWalk ω k).1) (i := n) le_rfl
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [Prod.fst_sub, Prod.snd_sub] at h₁ h₂
  simp only [vectorPitman_codeWalk_snd, runningMinimum_succ']
  generalize ω (n + 1) = c at h₁ h₂
  fin_cases c <;> norm_num [lazyTwoDimensionalStep] at h₁ h₂
  all_goals rw [abs_le]; constructor <;> omega

/-- A coupled hit cannot occur before `r` steps; helper replacing the -/
theorem vectorPitman_codeWalk_snd_ge_neg_time (ω : ℕ → Fin 3) (n : ℕ) :
    -(n : ℤ) ≤ (vectorPitman (codeWalk ω) n).2 := by
  induction n with
  | zero => simp [vectorPitman, codeWalk_zero]
  | succ n ih =>
    have h := (abs_le.mp (vectorPitman_codeWalk_snd_step ω n)).1
    push_cast
    omega

private theorem runningMinimum_attained (p : ℕ → ℤ) (n : ℕ) :
    ∃ k ≤ n, globalLazyRunningMinimum p n = p k := by
  induction n with
  | zero => exact ⟨0, le_rfl, globalLazyRunningMinimum_zero p⟩
  | succ n ih =>
    rw [runningMinimum_succ']
    by_cases h : globalLazyRunningMinimum p n ≤ p (n + 1)
    · rw [min_eq_left h]
      obtain ⟨k, hk, he⟩ := ih
      exact ⟨k, by omega, he⟩
    · exact ⟨n + 1, le_rfl, min_eq_right (by omega)⟩

/-- Every coupled downward excursion forces a half-sized coordinate excursion
in the original walk; helper replacing `lem-cond-walk-bm` -/
theorem vectorPitman_codeWalk_downcrossing_subset (r : ℝ) (m : ℕ) :
    {ω | ∃ n ≤ m, ((vectorPitman (codeWalk ω) n).2 : ℝ) ≤ -r} ⊆
      {ω | ∃ k ≤ m, r / 2 ≤ |((codeWalk ω k).1 : ℝ)| ∨
        r / 2 ≤ |((codeWalk ω k).2 : ℝ)|} := by
  rintro ω ⟨n, hn, hhit⟩
  obtain ⟨k, hk, he⟩ := runningMinimum_attained (fun k => (codeWalk ω k).1) n
  rw [vectorPitman_codeWalk_snd, Int.cast_add, he] at hhit
  by_cases hR : r / 2 ≤ |((codeWalk ω n).2 : ℝ)|
  · exact ⟨n, hn, Or.inr hR⟩
  · refine ⟨k, hk.trans hn, Or.inl ?_⟩
    have h₁ := le_abs_self ((codeWalk ω k).1 : ℝ)
    have h₂ := neg_le_abs ((codeWalk ω k).1 : ℝ)
    have h₃ := neg_le_abs ((codeWalk ω n).2 : ℝ)
    linarith

/-- Finite-horizon lower-tail estimate for the coupled hit, jointly using both
coordinates. Helper replacing `lem-cond-walk-bm` in `lem-uiqbot-boltzmann` -/
theorem vectorPitman_codeWalk_downcrossing_tail (r : ℝ) (hr : 0 < r)
    (m : ℕ) (hm : 0 < m) :
    iidCodeMeasure.real
      {ω | ∃ n ≤ m, ((vectorPitman (codeWalk ω) n).2 : ℝ) ≤ -r} ≤
        4 * Real.exp (-(r ^ 2) / (8 * (m : ℝ))) := by
  have ht := iidCodeWalk_blockMax_tail 0 m hm (r / 2) (by linarith)
  simp only [Nat.zero_add, codeWalk_zero, Prod.fst_sub, Prod.snd_sub,
    sub_zero] at ht
  refine (measureReal_mono (vectorPitman_codeWalk_downcrossing_subset r m)).trans ?_
  convert ht using 1; congr 2; ring

private theorem measurable_coupled_codeWalk :
    Measurable (fun ω : ℕ → Fin 3 => vectorPitman (codeWalk ω)) := by
  apply Measurable.of_eval
  intro n
  have hL : Measurable (fun ω : ℕ → Fin 3 => fun k => (codeWalk ω k).1) := by
    exact Measurable.of_eval (fun k => ((measurable_pi_apply k).comp measurable_codeWalk).fst)
  exact ((((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hL).prodMk
    (((measurable_pi_apply n).comp measurable_codeWalk).snd.add
      ((measurable_globalLazyRunningMinimum n).comp hL)))

/-- Uniform lower tail, including a zero integer horizon. Helper replacing the -/
theorem vectorPitman_codeWalk_early_hit_tail (r : ℕ) (hr : 1 ≤ r)
    (A : ℝ) (hA : 0 < A) :
    iidCodeMeasure.real {ω | ∃ n : ℕ,
      (n : ℝ) < (r : ℝ) ^ 2 / A ∧
      (vectorPitman (codeWalk ω) n).2 ≤ -(r : ℤ)} ≤
        4 * Real.exp (-A / 8) := by
  let m : ℕ := ⌊(r : ℝ) ^ 2 / A⌋₊
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hsub : {ω | ∃ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A ∧
      (vectorPitman (codeWalk ω) n).2 ≤ -(r : ℤ)} ⊆
      {ω | ∃ n ≤ m, ((vectorPitman (codeWalk ω) n).2 : ℝ) ≤ -(r : ℝ)} := by
    rintro ω ⟨n, hn, hv⟩
    exact ⟨n, Nat.le_floor hn.le, by exact_mod_cast hv⟩
  by_cases hm : m = 0
  · have hempty : {ω | ∃ n ≤ m,
        ((vectorPitman (codeWalk ω) n).2 : ℝ) ≤ -(r : ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨n, hn, hv⟩
      have hn0 : n = 0 := by omega
      simp only [hn0, vectorPitman, globalLazyRunningMinimum_zero,
        codeWalk_zero, zero_add, Int.cast_zero] at hv
      linarith
    have hzero : iidCodeMeasure.real {ω | ∃ n : ℕ,
        (n : ℝ) < (r : ℝ) ^ 2 / A ∧
        (vectorPitman (codeWalk ω) n).2 ≤ -(r : ℤ)} ≤ 0 := by
      simpa only [hempty, measureReal_empty] using measureReal_mono hsub
    exact hzero.trans (by positivity)
  · have hmpos : 0 < m := by omega
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hmA : (m : ℝ) * A ≤ (r : ℝ) ^ 2 :=
      (le_div_iff₀ hA).mp (Nat.floor_le (by positivity))
    have hexp : -((r : ℝ) ^ 2) / (8 * (m : ℝ)) ≤ -A / 8 := by
      apply (div_le_iff₀ (by positivity : 0 < 8 * (m : ℝ))).mpr
      nlinarith
    exact (measureReal_mono hsub).trans
      ((vectorPitman_codeWalk_downcrossing_tail r hrpos m hmpos).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)))

private theorem exists_hit_of_unit_down_steps (q : ℕ → ℤ) (hq : q 0 = 0)
    (hs : ∀ n, q n - 1 ≤ q (n + 1)) (r n : ℕ) (hn : q n ≤ -(r : ℤ)) :
    ∃ k ≤ n, q k = -(r : ℤ) := by
  induction n with
  | zero => exact ⟨0, le_rfl, by rw [hq] at hn ⊢; omega⟩
  | succ n ih =>
    by_cases h : q n ≤ -(r : ℤ)
    · obtain ⟨k, hk, he⟩ := ih h
      exact ⟨k, by omega, he⟩
    · exact ⟨n + 1, le_rfl, by have := hs n; omega⟩

/-- Every unconditioned hit has a coupled hit at or before it. This is the
pathwise upper-tail comparison replacing the Brownian-limit input of -/
theorem vectorPitman_codeWalk_hit_before (ω : ℕ → Fin 3) (r n : ℕ)
    (hn : (codeWalk ω n).2 = -(r : ℤ)) :
    ∃ k ≤ n, (vectorPitman (codeWalk ω) k).2 = -(r : ℤ) := by
  apply exists_hit_of_unit_down_steps (fun k => (vectorPitman (codeWalk ω) k).2)
  · simp [vectorPitman, codeWalk_zero]
  · intro k
    have h := (abs_le.mp (vectorPitman_codeWalk_snd_step ω k)).1
    omega
  · exact (vectorPitman_codeWalk_snd_le ω n).trans hn.le

/-- Almost-sure existence of every coupled downward hit, simultaneously over
all natural levels. Helper replacing `lem-cond-walk-bm` -/
theorem ae_vectorPitman_codeWalk_hits :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ r : ℕ,
      ∃ n, (vectorPitman (codeWalk ω) n).2 = -(r : ℤ) := by
  apply ae_all_iff.mpr
  intro r
  filter_upwards [ae_exists_codeWalk_snd_eq_int (-(r : ℤ))] with ω hω
  obtain ⟨n, hn⟩ := hω
  obtain ⟨k, _, hk⟩ := vectorPitman_codeWalk_hit_before ω r n hn
  exact ⟨k, hk⟩

/-- Measurability of the explicit two-sided hitting event. Helper replacing the -/
theorem measurableSet_vector_hitting_window (r : ℕ) (A : ℝ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      (∃ n : ℕ, (n : ℝ) ≤ A * (r : ℝ) ^ 2 ∧ (p n).2 = -(r : ℤ)) ∧
      ∀ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A → -(r : ℤ) < (p n).2} := by
  simp only [Set.ofPred_and, Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iUnion
    intro n
    exact MeasurableSet.inter (by simp) (measurableSet_eq_fun (by fun_prop) measurable_const)
  · apply MeasurableSet.iInter
    intro n
    by_cases h : (n : ℝ) < (r : ℝ) ^ 2 / A
    · simpa [h] using
        (measurableSet_lt (f := fun _ : ℕ → ℤ × ℤ => -(r : ℤ))
          (g := fun p => (p n).2) measurable_const ((measurable_pi_apply n).snd))
    · simp [h]

/-- Exact transfer of the explicit hitting window to the conditioned law.
Helper replacing `lem-cond-walk-bm` in `lem-uiqbot-boltzmann` -/
theorem conditionedVectorPathLaw_hitting_window_eq (r : ℕ) (A : ℝ) :
    (conditionedVectorPathLaw 0 0)
      {p | (∃ n : ℕ, (n : ℝ) ≤ A * (r : ℝ) ^ 2 ∧ (p n).2 = -(r : ℤ)) ∧
        ∀ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A → -(r : ℤ) < (p n).2} =
    iidCodeMeasure {ω |
      (∃ n : ℕ, (n : ℝ) ≤ A * (r : ℝ) ^ 2 ∧
        (vectorPitman (codeWalk ω) n).2 = -(r : ℤ)) ∧
      ∀ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A →
        -(r : ℤ) < (vectorPitman (codeWalk ω) n).2} := by
  rw [← map_vectorPitman_codeWalk,
    Measure.map_apply measurable_coupled_codeWalk (measurableSet_vector_hitting_window r A)]
  rfl

private theorem measurableSet_vector_early_downcrossing (r : ℕ) (A : ℝ) :
    MeasurableSet {p : ℕ → ℤ × ℤ | ∃ n : ℕ,
      (n : ℝ) < (r : ℝ) ^ 2 / A ∧ (p n).2 ≤ -(r : ℤ)} := by
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro n
  exact (MeasurableSet.const _).inter
    (measurableSet_le ((measurable_pi_apply n).snd) measurable_const)

/-- Uniform early-hit estimate on the actual conditioned law, including every
natural radius `r ≥ 1`. Helper replacing the `lem-cond-walk-bm` input of -/
theorem conditionedVectorPathLaw_early_hit_tail (r : ℕ) (hr : 1 ≤ r)
    (A : ℝ) (hA : 0 < A) :
    (conditionedVectorPathLaw 0 0).real {p | ∃ n : ℕ,
      (n : ℝ) < (r : ℝ) ^ 2 / A ∧ (p n).2 ≤ -(r : ℤ)} ≤
        4 * Real.exp (-A / 8) := by
  rw [← map_vectorPitman_codeWalk,
    map_measureReal_apply measurable_coupled_codeWalk
      (measurableSet_vector_early_downcrossing r A)]
  exact vectorPitman_codeWalk_early_hit_tail r hr A hA

private theorem hitting_uniform_map_equiv' {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (e : α ≃ α) :
    (Measure.uniformOfFinset (Finset.univ : Finset α)).map e =
      Measure.uniformOfFinset Finset.univ := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : e ⁻¹' {a} = {e.symm a} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← Equiv.eq_symm_apply]
  rw [he]
  simp only [Measure.uniformOfFinset_apply_singleton, Finset.mem_univ, ite_true]

private def hitting_rotWord (n : ℕ) : (Fin n → Fin 3) ≃ (Fin n → Fin 3) where
  toFun w i := w i + 1
  invFun w i := w i - 1
  left_inv w := by funext i; exact add_sub_cancel_right (w i) 1
  right_inv w := by funext i; exact sub_add_cancel (w i) 1

/-- The tail word of the iid codes is uniform on words of length `N`. -/
private theorem hitting_map_tailWord (N : ℕ) :
    iidCodeMeasure.map (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1)) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3)) := by
  classical
  have hf : (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1)) =
      (fun q : Fin (N + 1) → Fin 3 => fun i : Fin N => q i.succ) ∘
        (fun ω : ℕ → Fin 3 => fun j : Fin (N + 1) => ω j.val) := by
    funext ω i; rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), iidCodeMeasure_map_prefix]
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (N + 1) => (if j.val = 0 then Measure.dirac (0 : Fin 3)
      else uniformCodeMeasure)) 0
  have hsnd : (fun q : Fin (N + 1) → Fin 3 => fun i : Fin N => q i.succ) =
      Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Fin 3) 0) := by
    funext q i
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [hsnd, ← Measure.map_map measurable_snd (MeasurableEquiv.measurable _), hmp.map_eq,
    Measure.map_snd_prod]
  simp only [Fin.val_zero, ite_true, measure_univ, one_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Fin.succAbove_zero]
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton, ENNReal.inv_pow]

private theorem hitting_step_snd_eq (c : Fin 3) :
    (lazyTwoDimensionalStep c).2 = (((c + 1 : Fin 3) : ℕ) : ℤ) - 1 := by
  fin_cases c <;> decide

private theorem hitting_codeWalk_snd_eq (ω : ℕ → Fin 3) (N : ℕ) (j : Fin (N + 1)) :
    (codeWalk ω j.val).2 =
      lazyWordValues (fun i : Fin N => ω (i.val + 1) + 1) j := by
  unfold codeWalk lazyWordValues
  rw [Prod.snd_sum]
  simp_rw [hitting_step_snd_eq]
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if i < j.val then ((((ω (i + 1) + 1 : Fin 3) : ℕ) : ℤ) - 1) else 0) N,
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- Under the relabelling `c ↦ c + 1` of the tail codes, the survival of the original second
coordinate above `-k` up to time `N` is the survival of a uniform lazy word started at `k` -/
private theorem hitting_map_rotTail (N : ℕ) :
    iidCodeMeasure.map (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1) + 1) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3)) := by
  have hf : (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1) + 1) =
      (hitting_rotWord N) ∘ (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1)) := rfl
  rw [hf, ← Measure.map_map (measurable_of_countable _) (by fun_prop), hitting_map_tailWord,
    hitting_uniform_map_equiv']


private theorem hitting_survival_potential (n L z : ℕ) (hL : 0 < L)
    (hz : z + 1 ≤ L) :
    (n : ℝ) * lazyKilledSurvival n z ≤
      (n : ℝ) * ((z : ℝ) + 1) / L +
        (3 / 2 : ℝ) * ((z : ℝ) + 1) * ((L : ℝ) - ((z : ℝ) + 1)) := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  induction n generalizing z with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, zero_div, zero_add]
      have hzreal : (z : ℝ) + 1 ≤ L := by exact_mod_cast hz
      positivity
  | succ n ih =>
      have hs := (lazyKilledSurvival_mem_unitInterval (n + 1) z).2
      by_cases he : z + 1 = L
      · have hereal : (z : ℝ) + 1 = L := by exact_mod_cast he
        rw [hereal, mul_div_cancel_right₀ _ (ne_of_gt hLreal), sub_self,
          mul_zero, add_zero]
        exact mul_le_of_le_one_right (by positivity) hs
      · have hzin : z + 1 < L := by omega
        cases z with
        | zero =>
            have h0 := ih 0 (by omega)
            have h1 := ih 1 (by omega)
            rw [lazyKilledSurvival_succ_zero] at hs ⊢
            norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, Nat.cast_add] at *
            have havg :
                ((n : ℝ) / L + (3 / 2 : ℝ) * ((L : ℝ) - 1) +
                  ((n : ℝ) * 2 / L + (3 / 2 : ℝ) * 2 * ((L : ℝ) - 2))) / 3 =
                (n : ℝ) / L + (3 / 2 : ℝ) * ((L : ℝ) - 1) - 1 := by ring
            have hinv := inv_nonneg.mpr hLreal.le
            simp only [div_eq_mul_inv] at *
            nlinarith
        | succ z =>
            have h0 := ih z (by omega)
            have h1 := ih (z + 1) (by omega)
            have h2 := ih (z + 2) (by omega)
            rw [lazyKilledSurvival_succ_succ] at hs ⊢
            push_cast at *
            have hinv := inv_nonneg.mpr hLreal.le
            simp only [div_eq_mul_inv] at *
            nlinarith

private theorem hitting_survival_eq (r N : ℕ) (hr : 1 ≤ r) :
    iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} =
      lazyKilledSurvival N (r - 1) := by
  rw [← uniform_lazyWordSurvives_real, ← hitting_map_rotTail N,
    map_measureReal_apply (by fun_prop) (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  constructor
  · intro h j
    have hj := h j.val (by omega)
    rw [hitting_codeWalk_snd_eq ω N j] at hj
    change 0 ≤ ((r - 1 : ℕ) : ℤ) + _
    dsimp only at hj ⊢
    omega
  · intro h n hn
    have hj := h ⟨n, by omega⟩
    rw [← hitting_codeWalk_snd_eq ω N ⟨n, by omega⟩] at hj
    change 0 ≤ ((r - 1 : ℕ) : ℤ) + (codeWalk ω n).2 at hj
    omega

/-- Finite-horizon survival estimate for the lazy second coordinate. Helper
replacing `lem-cond-walk-bm` in `lem-uiqbot-boltzmann` -/
theorem lazy_survival_bound (r K N : ℕ) (hr : 1 ≤ r) (hK : r ≤ K)
    (hN : 0 < N) :
    iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} ≤
      (r : ℝ) / ((r : ℝ) + K) + (3 / 2 : ℝ) * ((K : ℝ) + 1) ^ 2 / N := by
  rw [hitting_survival_eq r N hr]
  have hp := hitting_survival_potential N (r + K) (r - 1) (by omega) (by omega)
  have he : ((r - 1 : ℕ) : ℝ) + 1 = r := by
    exact_mod_cast (show r - 1 + 1 = r by omega)
  rw [he, Nat.cast_add] at hp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrK : (r : ℝ) ≤ K := by exact_mod_cast hK
  have hb : (3 / 2 : ℝ) * (r : ℝ) * ((r : ℝ) + K - r) ≤
      (3 / 2 : ℝ) * ((K : ℝ) + 1) ^ 2 := by nlinarith
  apply (mul_le_mul_iff_right₀ hNr).mp
  calc
    (N : ℝ) * lazyKilledSurvival N (r - 1) ≤
        (N : ℝ) * r / ((r : ℝ) + K) + (3 / 2 : ℝ) * ((K : ℝ) + 1) ^ 2 :=
      hp.trans (add_le_add_right hb _)
    _ = (N : ℝ) * ((r : ℝ) / ((r : ℝ) + K) +
        (3 / 2 : ℝ) * ((K : ℝ) + 1) ^ 2 / N) := by field_simp


private theorem hitting_window_error (r m : ℝ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    r / (r + r * m) + (3 / 2 : ℝ) * (r * m + 1) ^ 2 / (8 * m ^ 3 * r ^ 2) +
      4 * Real.exp (-(8 * m ^ 3) / 8) ≤ 6 / m := by
  have hrpos : 0 < r := by linarith
  have hmpos : 0 < m := by linarith
  have hfirst : r / (r + r * m) ≤ 1 / m := by
    apply (div_le_div_iff₀ (by positivity) hmpos).mpr
    nlinarith
  have hrm : 1 ≤ r * m := by nlinarith
  have hsq : (r * m + 1) ^ 2 ≤ 4 * r ^ 2 * m ^ 2 := by
    nlinarith [sq_nonneg (r * m - 1)]
  have hsecond : (3 / 2 : ℝ) * (r * m + 1) ^ 2 / (8 * m ^ 3 * r ^ 2) ≤ 1 / m := by
    apply (div_le_div_iff₀ (by positivity) hmpos).mpr
    calc
      (3 / 2 : ℝ) * (r * m + 1) ^ 2 * m ≤
          (3 / 2 : ℝ) * (4 * r ^ 2 * m ^ 2) * m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hmpos.le
      _ ≤ 1 * (8 * m ^ 3 * r ^ 2) := by
        nlinarith [mul_nonneg (sq_nonneg r) (pow_nonneg hmpos.le 3)]
  have hm2 : 1 ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 1)]
  have hm3 : m ≤ m ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hm2) hmpos.le]
  have he : Real.exp (-(8 * m ^ 3) / 8) ≤ 1 / m := by
    rw [show -(8 * m ^ 3) / 8 = -(m ^ 3) by ring, Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) hmpos).mpr
      (by linarith [Real.add_one_le_exp (m ^ 3)])
  simp only [div_eq_mul_inv] at hfirst hsecond he ⊢
  linarith

private theorem measurableSet_vector_downcrossing_window (r : ℕ) (A : ℝ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      (∃ n : ℕ, (n : ℝ) ≤ A * (r : ℝ) ^ 2 ∧ (p n).2 ≤ -(r : ℤ)) ∧
      ∀ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A → -(r : ℤ) < (p n).2} := by
  simp only [Set.ofPred_and, Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iUnion
    intro n
    exact (MeasurableSet.const _).inter
      (measurableSet_le ((measurable_pi_apply n).snd) measurable_const)
  · apply MeasurableSet.iInter
    intro n
    by_cases h : (n : ℝ) < (r : ℝ) ^ 2 / A
    · simpa [h] using
        (measurableSet_lt (f := fun _ : ℕ → ℤ × ℤ => -(r : ℤ))
          (g := fun p => (p n).2) measurable_const ((measurable_pi_apply n).snd))
    · simp [h]

/-- Uniform tightness of the explicit coupled hitting window under the
conditioned law. This supplies the hitting-time estimate used in
`lem-uiqbot-boltzmann` without its Brownian-limit input -/
theorem conditionedVectorPathLaw_hitting_window_tight (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - ε ≤ (conditionedVectorPathLaw 0 0).real
        {p | (∃ n : ℕ, (n : ℝ) ≤ A * (r : ℝ) ^ 2 ∧ (p n).2 ≤ -(r : ℤ)) ∧
          ∀ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A → -(r : ℤ) < (p n).2} := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (6 / ε) 1)
  have hmreal : (1 : ℝ) ≤ m := (le_max_right _ _).trans hm.le
  have hmpos : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hmε : 6 / (m : ℝ) < ε := by
    have h := (le_max_left (6 / ε) 1).trans_lt hm
    have h' := (div_lt_iff₀ hε).mp h
    apply (div_lt_iff₀ (show (0 : ℝ) < m by positivity)).mpr
    nlinarith
  let A : ℝ := 8 * (m : ℝ) ^ 3
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg ((m : ℝ) - 1)]
  refine ⟨A, hA, ?_⟩
  intro r hr
  have hrpos : 0 < r := by omega
  let N : ℕ := 8 * m ^ 3 * r ^ 2
  have hN : 0 < N := by dsimp [N]; positivity
  have hNr : (N : ℝ) = A * (r : ℝ) ^ 2 := by simp only [N, A, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  let E : Set (ℕ → Fin 3) := {ω |
    (∃ n : ℕ, (n : ℝ) ≤ A * (r : ℝ) ^ 2 ∧
      (vectorPitman (codeWalk ω) n).2 ≤ -(r : ℤ)) ∧
    ∀ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A →
      -(r : ℤ) < (vectorPitman (codeWalk ω) n).2}
  have hE : MeasurableSet E :=
    (measurableSet_vector_downcrossing_window r A).preimage measurable_coupled_codeWalk
  have hsub : Eᶜ ⊆
      {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} ∪
      {ω | ∃ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A ∧
        (vectorPitman (codeWalk ω) n).2 ≤ -(r : ℤ)} := by
    intro ω hω
    by_cases hhit : ∃ n ≤ N, (codeWalk ω n).2 ≤ -(r : ℤ)
    · right
      by_contra hearly
      apply hω
      obtain ⟨n, hn, hv⟩ := hhit
      refine ⟨⟨n, ?_, (vectorPitman_codeWalk_snd_le ω n).trans hv⟩, ?_⟩
      · rw [← hNr]
        exact_mod_cast hn
      · intro k hk
        by_contra hv'
        apply hearly
        exact ⟨k, hk, le_of_not_gt hv'⟩
    · left
      intro n hn
      by_contra hv
      exact hhit ⟨n, hn, le_of_not_gt hv⟩
  have hlate := lazy_survival_bound r (r * m) N hr (by nlinarith) hN
  have hearly := vectorPitman_codeWalk_early_hit_tail r hr A (by linarith)
  have hbad : iidCodeMeasure.real Eᶜ ≤ 6 / (m : ℝ) := by
    calc
      iidCodeMeasure.real Eᶜ ≤
          iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} +
          iidCodeMeasure.real {ω | ∃ n : ℕ, (n : ℝ) < (r : ℝ) ^ 2 / A ∧
            (vectorPitman (codeWalk ω) n).2 ≤ -(r : ℤ)} :=
        (measureReal_mono hsub).trans (measureReal_union_le _ _)
      _ ≤ (r : ℝ) / ((r : ℝ) + (r * m : ℕ)) +
          (3 / 2 : ℝ) * (((r * m : ℕ) : ℝ) + 1) ^ 2 / N + 4 * Real.exp (-A / 8) :=
        add_le_add hlate hearly
      _ ≤ 6 / (m : ℝ) := by
        rw [hNr]
        push_cast
        exact hitting_window_error r m (by exact_mod_cast hr) hmreal
  have htotal := measureReal_add_measureReal_compl (μ := iidCodeMeasure) hE
  rw [probReal_univ] at htotal
  rw [← map_vectorPitman_codeWalk,
    map_measureReal_apply measurable_coupled_codeWalk
      (measurableSet_vector_downcrossing_window r A)]
  change 1 - ε ≤ iidCodeMeasure.real E
  linarith

end DirectedDistances.RandomWalk
