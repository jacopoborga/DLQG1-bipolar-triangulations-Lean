module

public import DirectedDistances.RandomWalk.HittingTightness
import DirectedDistances.RandomWalk.LazySurvivalProbability

/-! # Sharp survival and hitting estimates for the lazy walk

Elementary random-walk estimates for the time-comparison step of
of the iid code walk hits `-m` before time `n` with probability at least
`1 - C m / √n`. The survival bound `C r / √N` sharpens `lazy_survival_bound` by
keeping the factor `r` in the exit-time estimate `(3/2) r K`. These are helper
estimates, not numbered paper results. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private theorem sharp_uniform_map_equiv {α : Type*} [Fintype α] [MeasurableSpace α]
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

private def sharp_rotWord (n : ℕ) : (Fin n → Fin 3) ≃ (Fin n → Fin 3) where
  toFun w i := w i + 1
  invFun w i := w i - 1
  left_inv w := by funext i; exact add_sub_cancel_right (w i) 1
  right_inv w := by funext i; exact sub_add_cancel (w i) 1

private theorem sharp_map_tailWord (N : ℕ) :
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

private theorem sharp_step_snd_eq (c : Fin 3) :
    (lazyTwoDimensionalStep c).2 = (((c + 1 : Fin 3) : ℕ) : ℤ) - 1 := by
  fin_cases c <;> decide

private theorem sharp_codeWalk_snd_eq (ω : ℕ → Fin 3) (N : ℕ) (j : Fin (N + 1)) :
    (codeWalk ω j.val).2 =
      lazyWordValues (fun i : Fin N => ω (i.val + 1) + 1) j := by
  unfold codeWalk lazyWordValues
  rw [Prod.snd_sum]
  simp_rw [sharp_step_snd_eq]
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if i < j.val then ((((ω (i + 1) + 1 : Fin 3) : ℕ) : ℤ) - 1) else 0) N,
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

private theorem sharp_map_rotTail (N : ℕ) :
    iidCodeMeasure.map (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1) + 1) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3)) := by
  have hf : (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1) + 1) =
      (sharp_rotWord N) ∘ (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1)) := rfl
  rw [hf, ← Measure.map_map (measurable_of_countable _) (by fun_prop), sharp_map_tailWord,
    sharp_uniform_map_equiv]

private theorem sharp_survival_potential (n L z : ℕ) (hL : 0 < L)
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

private theorem sharp_survival_eq (r N : ℕ) (hr : 1 ≤ r) :
    iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} =
      lazyKilledSurvival N (r - 1) := by
  rw [← uniform_lazyWordSurvives_real, ← sharp_map_rotTail N,
    map_measureReal_apply (by fun_prop) (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  constructor
  · intro h j
    have hj := h j.val (by omega)
    rw [sharp_codeWalk_snd_eq ω N j] at hj
    change 0 ≤ ((r - 1 : ℕ) : ℤ) + _
    dsimp only at hj ⊢
    omega
  · intro h n hn
    have hj := h ⟨n, by omega⟩
    rw [← sharp_codeWalk_snd_eq ω N ⟨n, by omega⟩] at hj
    change 0 ≤ ((r - 1 : ℕ) : ℤ) + (codeWalk ω n).2 at hj
    omega

/-- Sharp finite-horizon survival bound for the lazy second coordinate: the walk stays above
`-r` up to time `N` with probability at most `4 r / √N`. Helper for the time comparison in -/
theorem lazy_survival_sharp_bound (r N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} ≤
      4 * (r : ℝ) / Real.sqrt N := by
  rw [sharp_survival_eq r N hr]
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt N := ⟨_, rfl⟩
  rw [← hs]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hNr
  have hss : s * s = N := by rw [hs]; exact Real.mul_self_sqrt (by linarith)
  have hspos : 0 < s := by linarith
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hK1 : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hK2 : ((⌈s⌉₊ : ℕ) : ℝ) < s + 1 := Nat.ceil_lt_add_one hspos.le
  have hp := sharp_survival_potential N (r + ⌈s⌉₊) (r - 1) (by omega) (by omega)
  have he : ((r - 1 : ℕ) : ℝ) + 1 = r := by
    exact_mod_cast (show r - 1 + 1 = r by omega)
  rw [he, Nat.cast_add] at hp
  have hKle : ((⌈s⌉₊ : ℕ) : ℝ) ≤ 2 * s := by linarith
  have h1 : (N : ℝ) * r / ((r : ℝ) + (⌈s⌉₊ : ℕ)) ≤ r * s := by
    rw [div_le_iff₀ (by positivity)]
    have hprod : 0 ≤ (r : ℝ) * s * ((r : ℝ) + (⌈s⌉₊ : ℕ) - s) :=
      mul_nonneg (by positivity) (by linarith)
    have hNrs : (N : ℝ) * r = s * s * r := by rw [hss]
    nlinarith [hprod, hNrs]
  have h2 : (3 / 2 : ℝ) * (r : ℝ) * (((r : ℝ) + (⌈s⌉₊ : ℕ)) - r) ≤ 3 * r * s := by
    have := mul_le_mul_of_nonneg_left hKle (by positivity : (0 : ℝ) ≤ r)
    nlinarith
  have hNpos : (0 : ℝ) < N := by linarith
  apply (mul_le_mul_iff_right₀ hNpos).mp
  have heq : (N : ℝ) * (4 * r / s) = 4 * r * s := by
    rw [← hss]; field_simp
  rw [heq]
  linarith

private theorem sharp_codeWalk_fst_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).1 - 1 ≤ (codeWalk ω (n + 1)).1 := by
  have h := (abs_le.mp (codeWalk_succ_sub_coord_abs_le_one ω n).1).1
  change (-1 : ℤ) ≤ (codeWalk ω (n + 1)).1 - (codeWalk ω n).1 at h
  omega

private theorem sharp_fst_survival_of_no_hit (ω : ℕ → Fin 3) (k N : ℕ) (hk : 1 ≤ k)
    (hno : ∀ j ≤ N, (codeWalk ω j).1 ≠ -(k : ℤ)) :
    ∀ j ≤ N, -(k : ℤ) < (codeWalk ω j).1 := by
  intro j hj
  induction j with
  | zero => simp [codeWalk_zero]; omega
  | succ j ih =>
      have hprev := ih (by omega)
      have hstep := sharp_codeWalk_fst_succ_ge ω j
      have hneq := hno (j + 1) hj
      omega

private theorem sharp_measurableSet_snd_survival (r N : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).2} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (((measurable_pi_apply n).comp measurable_codeWalk).snd)

private theorem sharp_measurableSet_fst_survival (r N : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).1} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (((measurable_pi_apply n).comp measurable_codeWalk).fst)

/-- Sharp first-coordinate survival bound, transferred from the second coordinate by rotating
the iid code walk twice. Helper for `lem-cell-ldp-lower` -/
theorem iidCodeWalk_fst_survival_sharp_bound (r N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    iidCodeMeasure.real {ω | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).1} ≤
      4 * (r : ℝ) / Real.sqrt N := by
  have hm := sharp_measurableSet_snd_survival r N
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
  exact lazy_survival_sharp_bound r N hr hN

/-- Sharp hitting form: the first coordinate of the iid code walk hits `-r` at some time
`≤ N` with probability at least `1 - 4 r / √N`. Helper for `lem-cell-ldp-lower` -/
theorem iidCodeWalk_fst_hit_sharp_bound (r N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    1 - 4 * (r : ℝ) / Real.sqrt N ≤
      iidCodeMeasure.real {ω | ∃ n ≤ N, (codeWalk ω n).1 = -(r : ℤ)} := by
  have hset : {ω : ℕ → Fin 3 | ∃ n ≤ N, (codeWalk ω n).1 = -(r : ℤ)} =
      {ω : ℕ → Fin 3 | ∀ n ≤ N, -(r : ℤ) < (codeWalk ω n).1}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall]
    constructor
    · rintro ⟨n, hn, he⟩
      exact ⟨n, hn, by omega⟩
    · rintro ⟨n, hn, hlt⟩
      by_contra hno
      push_neg at hno
      exact hlt (sharp_fst_survival_of_no_hit ω r N hr (fun j hj => by
        by_contra hjeq
        exact hno j hj hjeq) n hn)
  have htotal := measureReal_add_measureReal_compl (μ := iidCodeMeasure)
    (sharp_measurableSet_fst_survival r N)
  rw [probReal_univ] at htotal
  rw [hset]
  have := iidCodeWalk_fst_survival_sharp_bound r N hr hN
  linarith

/-- Hitting estimate with a general scale `a > 0`: with `m = ⌊a √n⌋`, the first coordinate hits
`-m` at some time `≤ n` with probability at least `1 - 4 a`. The case `m = 0` is trivial, as the -/
theorem iidCodeWalk_fst_hit_scaled (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    1 - 4 * a ≤ iidCodeMeasure.real {ω | ∃ k ≤ n,
      (codeWalk ω k).1 = -((⌊a * Real.sqrt n⌋₊ : ℕ) : ℤ)} := by
  by_cases hm : ⌊a * Real.sqrt n⌋₊ = 0
  · have hall : {ω : ℕ → Fin 3 | ∃ k ≤ n,
        (codeWalk ω k).1 = -((⌊a * Real.sqrt n⌋₊ : ℕ) : ℤ)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨0, Nat.zero_le _, by simp [codeWalk_zero, hm]⟩
    rw [hall, probReal_univ]
    linarith
  · have hmpos : 1 ≤ ⌊a * Real.sqrt n⌋₊ := Nat.pos_of_ne_zero hm
    have hb := iidCodeWalk_fst_hit_sharp_bound _ n hmpos hn
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hfl : ((⌊a * Real.sqrt n⌋₊ : ℕ) : ℝ) ≤ a * Real.sqrt n := Nat.floor_le (by positivity)
    have hdiv : 4 * ((⌊a * Real.sqrt n⌋₊ : ℕ) : ℝ) / Real.sqrt n ≤ 4 * a := by
      rw [div_le_iff₀ hsq]
      nlinarith
    linarith

/-- Source form of the time comparison: for every `ε ∈ (0, 2/3)` there is a universal constant
`c₄` such that, for all `n ≥ 1` and `A > 1`, with `m = ⌊A^(-2/3+ε) √n⌋`, the first coordinate of
the iid code walk hits `-m` at some time `≤ n` with probability at least `1 - c₄ A^(-2/3+ε)`. -/
theorem iidCodeWalk_fst_hit_source_form (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 2 / 3) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
      1 - c₄ * A ^ (-(2 / 3 : ℝ) + ε) ≤ iidCodeMeasure.real {ω | ∃ k ≤ n,
        (codeWalk ω k).1 =
          -((⌊A ^ (-(2 / 3 : ℝ) + ε) * Real.sqrt n⌋₊ : ℕ) : ℤ)} := by
  refine ⟨4, by norm_num, fun n hn A hA => ?_⟩
  exact iidCodeWalk_fst_hit_scaled _ (Real.rpow_pos_of_pos (by linarith) _) n hn

end DirectedDistances.RandomWalk
