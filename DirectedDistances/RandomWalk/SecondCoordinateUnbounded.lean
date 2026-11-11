module

public import DirectedDistances.RandomWalk.PitmanCodes
public import DirectedDistances.RandomWalk.LazySurvivalProbability
import DirectedDistances.RandomWalk.RConditionedWalk

/-! # The second coordinate of the iid code walk is unbounded below

(Lemma 3.6 (i) and (iv)), second coordinate of the walk of `lem-quadrant-walk`, -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- Pathwise, the Pitman-flipped second coordinate is at most the original one, since the
running minimum of the first coordinate is at most its initial value `0` -/
theorem integrateCodes_pitmanCode_snd_le (c : ℕ → Fin 3) (n : ℕ) :
    (integrateCodes (pitmanCode c) n).2 ≤ (integrateCodes c n).2 := by
  rw [integrateCodes_pitmanCode]
  have h := globalLazyRunningMinimum_le (fun k => (integrateCodes c k).1) (Nat.zero_le n)
  have h0 : (integrateCodes c 0).1 = 0 := by simp [integrateCodes]
  simp only [vectorPitman]
  simp only [h0] at h
  omega

private theorem uniform_map_equiv' {α : Type*} [Fintype α] [MeasurableSpace α]
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

private def rotWord (n : ℕ) : (Fin n → Fin 3) ≃ (Fin n → Fin 3) where
  toFun w i := w i + 1
  invFun w i := w i - 1
  left_inv w := by funext i; exact add_sub_cancel_right (w i) 1
  right_inv w := by funext i; exact sub_add_cancel (w i) 1

/-- The tail word of the iid codes is uniform on words of length `N`. -/
private theorem map_tailWord (N : ℕ) :
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

private theorem step_snd_eq (c : Fin 3) :
    (lazyTwoDimensionalStep c).2 = (((c + 1 : Fin 3) : ℕ) : ℤ) - 1 := by
  fin_cases c <;> decide

private theorem codeWalk_snd_eq (ω : ℕ → Fin 3) (N : ℕ) (j : Fin (N + 1)) :
    (codeWalk ω j.val).2 =
      lazyWordValues (fun i : Fin N => ω (i.val + 1) + 1) j := by
  unfold codeWalk lazyWordValues
  rw [Prod.snd_sum]
  simp_rw [step_snd_eq]
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
private theorem map_rotTail (N : ℕ) :
    iidCodeMeasure.map (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1) + 1) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3)) := by
  have hf : (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1) + 1) =
      (rotWord N) ∘ (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1)) := rfl
  rw [hf, ← Measure.map_map (measurable_of_countable _) (by fun_prop), map_tailWord,
    uniform_map_equiv']

private theorem measure_second_coordinate_survives (k : ℕ) (N : ℕ) :
    iidCodeMeasure.real {ω : ℕ → Fin 3 | ∀ n, -(k : ℤ) ≤ (codeWalk ω n).2} ≤
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin N → Fin 3))).real
        {w | LazyWordSurvives k w} := by
  have hmeas : Measurable (fun ω : ℕ → Fin 3 => fun i : Fin N => ω (i.val + 1) + 1) := by
    fun_prop
  rw [← map_rotTail N, map_measureReal_apply hmeas (Set.to_countable _).measurableSet]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω j
  have h1 := hω j.val
  rw [codeWalk_snd_eq ω N j] at h1
  show 0 ≤ (k : ℤ) + lazyWordValues (fun i : Fin N => ω (i.val + 1) + 1) j
  omega

/-- The second coordinate of the iid code walk is a.s. unbounded below -/
theorem ae_codeWalk_snd_unbounded_below :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ a : ℤ, ∃ n, (codeWalk ω n).2 ≤ a := by
  have key (k : ℕ) :
      iidCodeMeasure {ω : ℕ → Fin 3 | ∀ n, -(k : ℤ) ≤ (codeWalk ω n).2} = 0 := by
    have hle : iidCodeMeasure.real {ω : ℕ → Fin 3 | ∀ n, -(k : ℤ) ≤ (codeWalk ω n).2} ≤ 0 :=
      ge_of_tendsto' (tendsto_uniform_lazyWordSurvives_real k)
        (fun N => measure_second_coordinate_survives k N)
    exact (measureReal_eq_zero_iff).1 (le_antisymm hle measureReal_nonneg)
  have hall : ∀ᵐ ω ∂iidCodeMeasure, ∀ k : ℕ, ω ∉
      {ω : ℕ → Fin 3 | ∀ n, -(k : ℤ) ≤ (codeWalk ω n).2} :=
    ae_all_iff.2 (fun k => measure_eq_zero_iff_ae_notMem.1 (key k))
  filter_upwards [hall] with ω hω a
  have h := hω a.natAbs
  simp only [not_forall, not_le] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩

/-- The Pitman-flipped second coordinate of the fallback-free iid code realization is a.s. -/
theorem pitmanCodes_ae_R_unbounded_below :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ a : ℤ, ∃ n,
      (integrateCodes (pitmanCode (fun i => ω (i + 1))) n).2 ≤ a := by
  filter_upwards [ae_codeWalk_snd_unbounded_below] with ω hω a
  obtain ⟨n, hn⟩ := hω a
  exact ⟨n, (integrateCodes_pitmanCode_snd_le _ n).trans hn⟩

end DirectedDistances.RandomWalk
