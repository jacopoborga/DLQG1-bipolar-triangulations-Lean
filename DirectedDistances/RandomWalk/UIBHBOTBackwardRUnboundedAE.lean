module

public import DirectedDistances.RandomWalk.UIBHBOTPastRUnbounded
public import DirectedDistances.Probability.UnboundedAboveOfUniformTail

/-! # Uniform-tail assembly for backward UIBHBOT R sums

Helper toward Proposition 5.16 (UIBHBOT M^♭: a.s. `liminf_{n→−∞} R^♭(n) = −∞`,
k140 steps 6–8); not the paper result. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory

/-- Helper toward Proposition 5.16 (UIBHBOT M^♭: a.s. `liminf_{n→−∞} R^♭(n) = −∞`,
k140 steps 6–8); not the paper result. -/
theorem uibhbotWordFamilyLaw_map_backwardBlocks (k : ℕ) :
    uibhbotWordFamilyLaw.map
        (fun w (j : Fin k) => w (-(j : ℤ) - 1)) =
      Measure.pi (fun _ : Fin k => excursionWordLaw) := by
  have hlaw :
      (Measure.infinitePi (fun _ : ℕ => excursionWordLaw)).map
          (fun u (j : Fin k) => u j.val) =
        Measure.pi (fun _ : Fin k => excursionWordLaw) := by
    let I : Finset ℕ := Finset.range k
    let e : Fin k ≃ {i : ℕ // i ∈ Finset.range k} :=
      { toFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
        invFun := fun i => ⟨i.val, Finset.mem_range.mp i.property⟩
        left_inv := fun i => by ext; rfl
        right_inv := fun i => by ext; rfl }
    calc
      (Measure.infinitePi (fun _ : ℕ => excursionWordLaw)).map
          (fun u (j : Fin k) => u j.val) =
        ((Measure.infinitePi (fun _ : ℕ => excursionWordLaw)).map
          (fun u => I.restrict u)).map (fun g j => g (e j)) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
      _ = (Measure.pi
          (fun _ : {i : ℕ // i ∈ Finset.range k} => excursionWordLaw)).map
          (fun g j => g (e j)) := by
            rw [Measure.infinitePi_map_restrict
              (μ := fun _ : ℕ => excursionWordLaw) (I := I)]
      _ = Measure.pi (fun _ : Fin k => excursionWordLaw) := by
            change (Measure.pi
              (fun _ : {i : ℕ // i ∈ Finset.range k} => excursionWordLaw)).map
                (MeasurableEquiv.piCongrLeft
                  (fun _ : Fin k => List (Fin 3)) e.symm) = _
            exact Measure.pi_map_piCongrLeft e.symm
              (fun _ : Fin k => excursionWordLaw)
  calc
    uibhbotWordFamilyLaw.map
        (fun w (j : Fin k) => w (-(j : ℤ) - 1)) =
      (uibhbotWordFamilyLaw.map uibhbotBackwardWordSequence).map
        (fun u (j : Fin k) => u j.val) := by
          rw [Measure.map_map (by fun_prop)
            measurable_uibhbotBackwardWordSequence]
          rfl
    _ = Measure.pi (fun _ : Fin k => excursionWordLaw) := by
          rw [uibhbotWordFamilyLaw_map_backwardWordSequence]
          exact hlaw

/-- Helper toward Proposition 5.16 (UIBHBOT M^♭: a.s. `liminf_{n→−∞} R^♭(n) = −∞`,
k140 steps 6–8); not the paper result. -/
theorem uibhbotBackwardRPartialSum_eq_fin_sum (w : ℤ → List (Fin 3)) (k : ℕ) :
    uibhbotBackwardRPartialSum w k =
      ∑ j : Fin k, uibhbotWordRDisplacement (w (-(j : ℤ) - 1)) := by
  have hsumRange : ∀ n (f : ℕ → ℤ),
      (∑ i ∈ Finset.range n, f i) = ∑ i : Fin n, f i.val := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
        intro f
        rw [Finset.sum_range_succ, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih]
  simpa [uibhbotBackwardRPartialSum] using
    hsumRange k (fun j => uibhbotWordRDisplacement (w (-(j : ℤ) - 1)))




theorem uibhbotWordFamilyLaw_backwardRUnbounded_of_uniformTail
    (hL5 : ∃ c : ℝ, 0 < c ∧ ∀ A k : ℕ, 1 ≤ k → 2 * A ≤ k →
      c ≤ (Measure.pi (fun _ : Fin k => excursionWordLaw)
        {w | (A : ℤ) < ∑ j, uibhbotWordRDisplacement (w j)}).toReal) :
    uibhbotWordFamilyLaw
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} = 1 := by
  obtain ⟨c, hc, htailInput⟩ := hL5
  let μ := uibhbotWordFamilyLaw
  let S : ℕ → (ℤ → List (Fin 3)) → ℤ :=
    fun k w => uibhbotBackwardRPartialSum w (k + 1)
  have hpartialMeas (k : ℕ) :
      Measurable (fun w : ℤ → List (Fin 3) => uibhbotBackwardRPartialSum w k) := by
    induction k with
    | zero =>
        simp [uibhbotBackwardRPartialSum]
    | succ k ih =>
        have heq : (fun w : ℤ → List (Fin 3) =>
            uibhbotBackwardRPartialSum w (k + 1)) =
          (fun w => uibhbotBackwardRPartialSum w k) +
            (fun w => uibhbotWordRDisplacement (w (-(k : ℤ) - 1))) := by
          funext w
          exact uibhbotBackwardRPartialSum_succ w k
        rw [heq]
        exact ih.add ((measurable_of_countable uibhbotWordRDisplacement).comp
          (measurable_pi_apply (-(k : ℤ) - 1)))
  have hS : ∀ k, Measurable (fun w => S k w) := by
    intro k
    exact hpartialMeas (k + 1)
  have hpiSumMeas (k : ℕ) :
      Measurable (fun v : Fin k → List (Fin 3) =>
        ∑ j : Fin k, uibhbotWordRDisplacement (v j)) := by
    fun_prop
  have hprobEq (A k : ℕ) :
      μ {w | (A : ℤ) < uibhbotBackwardRPartialSum w (k + 1)} =
        Measure.pi (fun _ : Fin (k + 1) => excursionWordLaw)
          {v | (A : ℤ) <
            ∑ j : Fin (k + 1), uibhbotWordRDisplacement (v j)} := by
    let F : (ℤ → List (Fin 3)) → (Fin (k + 1) → List (Fin 3)) :=
      fun w j => w (-(j : ℤ) - 1)
    let E : Set (Fin (k + 1) → List (Fin 3)) :=
      {v | (A : ℤ) < ∑ j : Fin (k + 1), uibhbotWordRDisplacement (v j)}
    have hE : MeasurableSet E :=
      measurableSet_lt measurable_const (hpiSumMeas (k + 1))
    have hpre : F ⁻¹' E =
        {w | (A : ℤ) < uibhbotBackwardRPartialSum w (k + 1)} := by
      ext w
      simp only [Set.mem_preimage, E, Set.mem_ofPred_eq, F]
      rw [uibhbotBackwardRPartialSum_eq_fin_sum]
    calc
      μ {w | (A : ℤ) < uibhbotBackwardRPartialSum w (k + 1)} = μ (F ⁻¹' E) := by
        rw [hpre]
      _ = (μ.map F) E := (Measure.map_apply (by fun_prop) hE).symm
      _ = Measure.pi (fun _ : Fin (k + 1) => excursionWordLaw) E := by
        rw [uibhbotWordFamilyLaw_map_backwardBlocks]

  have htail : ∀ A k : ℕ, 2 * A ≤ k → ENNReal.ofReal c ≤
      μ {w | (A : ℝ) < (S k w : ℝ)} := by
    intro A k hk
    have hk' : 1 ≤ k + 1 := by omega
    have htwo : 2 * A ≤ k + 1 := by omega
    have hinput := htailInput A (k + 1) hk' htwo
    have hcast : {w | (A : ℝ) < (S k w : ℝ)} =
        {w | (A : ℤ) < S k w} := by
      ext w
      simp only [Set.mem_ofPred_eq]
      simpa only [Int.cast_natCast] using
        (Int.cast_lt (R := ℝ) (m := (A : ℤ)) (n := S k w))
    have hprobReal : μ {w | (A : ℝ) < (S k w : ℝ)} =
        Measure.pi (fun _ : Fin (k + 1) => excursionWordLaw)
          {v | (A : ℤ) <
            ∑ j : Fin (k + 1), uibhbotWordRDisplacement (v j)} := by
      rw [hcast]
      simpa [S] using hprobEq A k
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
    rw [hprobReal]
    exact hinput
  have hge := DirectedDistances.Probability.prob_unbounded_above_ge_of_uniform_tail_int
    (μ := μ) (S := S) hS htail
  have hposShift : 0 < μ {w | ∀ A : ℤ, ∃ k : ℕ, A < S k w} :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc) hge
  have hsubset : {w | ∀ A : ℤ, ∃ k : ℕ, A < S k w} ⊆
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} := by
    intro w hw A
    obtain ⟨k, hk⟩ := hw A
    exact ⟨k + 1, by simpa [S] using hk⟩
  have hpos : 0 < μ
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} :=
    lt_of_lt_of_le hposShift (measure_mono hsubset)
  exact DirectedDistances.Probability.prob_eq_one_of_zero_one_of_pos
    uibhbotWordFamilyLaw_backwardRUnbounded_zero_one hpos

end DirectedDistances.RandomWalk
