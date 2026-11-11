module

public import DirectedDistances.RandomWalk.HittingTightness
public import DirectedDistances.RandomWalk.PitmanCodes
public import DirectedDistances.KMSW.CutEquivalenceConverse
public import DirectedDistances.KMSW.StageIncidence
import DirectedDistances.RandomWalk.PitmanPrefixCompatibility

/-! # Edge count at the first hit of level `-r`

Helpers for `lem-uiqbot-boltzmann` and `eq:edges-in-Mr`,
numbered paper result: they show that every edge allocated before the first
hit of `-r` is present, that the allocation count is between `n + 1` and
`2 n + 1`, and that the allocation count at the stage before the first hit of
the Pitman-coupled walk is of order `r ^ 2` with high probability. -/

public section
namespace DirectedDistances.KMSW
open MeasureTheory

private theorem step_snd_ge (c : Fin 3) :
    -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).2 := by
  fin_cases c <;> decide

private theorem R_zero (w : ℕ → Fin 3) : R w 0 = 0 := by simp [R]

private theorem L_zero (w : ℕ → Fin 3) : L w 0 = 0 := by simp [L]

/-- The vertical coordinate decreases by at most one per step -/
theorem R_sub_one_le_succ (w : ℕ → Fin 3) (n : ℕ) : R w n - 1 ≤ R w (n + 1) := by
  have h : R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
    Finset.sum_range_succ _ _
  have := step_snd_ge (w n)
  omega

private theorem lt_of_first_hit (q : ℕ → ℤ) (hq : q 0 = 0)
    (hs : ∀ n, q n - 1 ≤ q (n + 1)) (r t : ℕ) (hr : 1 ≤ r)
    (ht : ∀ j < t, q j ≠ -(r : ℤ)) : ∀ j < t, -(r : ℤ) < q j := by
  intro j
  induction j with
  | zero => intro _; rw [hq]; omega
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hs j
    have h3 := ht (j + 1) hj
    omega

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

/-- Before the first hit of `-r` by a walk with nonnegative horizontal
coordinate, both `UR` and `LL` are empty (`eqn-kmsw-bdy`, -/
theorem stage_UR_LL_eq_nil_of_hit (w : ℕ → Fin 3) (n r : ℕ)
    (hL : ∀ j, 0 ≤ L w j) (hhit : R w (n + 1) = -(r : ℤ))
    (hbef : ∀ j ≤ n, -(r : ℤ) < R w j) :
    (kmswStage w n).UR = [] ∧ (kmswStage w n).LL = [] := by
  have hRn := hbef n le_rfl
  have hstep := R_sub_one_le_succ w n
  obtain ⟨j, hj, hje⟩ := runningMin_attained (R w) n
  have hjb := hbef j hj
  have hle := runningMin_le (R w) n n le_rfl
  have hUR := kmswStage_UR_length w n
  unfold minR at hUR
  obtain ⟨k, hk, hke⟩ := runningMin_attained (L w) n
  have hkb := hL k
  have hle0 := runningMin_le (L w) n 0 (Nat.zero_le _)
  have h0 := L_zero w
  have hLL := kmswStage_LL_length w n
  unfold minL at hLL
  constructor
  · exact List.length_eq_zero_iff.mp (by omega)
  · exact List.length_eq_zero_iff.mp (by omega)

/-- With `L ≥ 0` and `R` first reaching `-r` at time `n + 1`, every allocated -/
theorem edges_present_of_hit (w : ℕ → Fin 3) (n r : ℕ)
    (hL : ∀ j, 0 ≤ L w j) (hhit : R w (n + 1) = -(r : ℤ))
    (hbef : ∀ j ≤ n, -(r : ℤ) < R w j) :
    ∀ e < (kmswStage w n).nextEdge, (kmswStage w n).present e = true := by
  obtain ⟨hUR, hLL⟩ := stage_UR_LL_eq_nil_of_hit w n r hL hhit hbef
  intro e he
  by_contra hne
  have hf : (kmswStage w n).present e = false := by simpa using hne
  rcases ((kmswStage_status w n).1 e he).mp hf with h | h
  · simp [hUR] at h
  · simp [hLL] at h

/-- First-time form: if `t` is the first time `R w` equals `-r` (`r ≥ 1`) and
`L w ≥ 0`, every edge allocated by stage `t - 1` is present
helper, not the lemma). -/
theorem edges_present_of_first_hit (w : ℕ → Fin 3) (t r : ℕ) (hr : 1 ≤ r)
    (hL : ∀ j, 0 ≤ L w j)
    (hfirst : R w t = -(r : ℤ) ∧ ∀ j < t, R w j ≠ -(r : ℤ)) :
    ∀ e < (kmswStage w (t - 1)).nextEdge, (kmswStage w (t - 1)).present e = true := by
  obtain ⟨hhit, hmin⟩ := hfirst
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [R_zero] at hhit
    omega
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine edges_present_of_hit w n r hL hhit ?_
  have := lt_of_first_hit (R w) (R_zero w) (R_sub_one_le_succ w) r (n + 1) hr hmin
  exact fun j hj => this j (by omega)



theorem stage_UR_add_LL_length_le (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UR.length + (kmswStage w n).LL.length ≤ n := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    change (kmswStep (kmswStage w n) (w n)).UR.length +
      (kmswStep (kmswStage w n) (w n)).LL.length ≤ n + 1
    unfold kmswStep
    cases kmswCodeStep (w n) with
    | down =>
      cases hs : (kmswStage w n).UR <;>
        simp only [kmswStepOfStep, hs, State.addEdge, List.length_cons,
          List.length_nil] at * <;> omega
    | left =>
      cases hs : (kmswStage w n).UL.dropLast.reverse <;>
        simp only [kmswStepOfStep, hs, State.addEdge, List.length_cons] <;> omega
    | up =>
      simp only [kmswStepOfStep, State.addEdge, List.length_cons]
      omega

/-- The allocation count at stage `n` lies in `[n + 1, 2 n + 1]` -/
theorem nextEdge_bounds (w : ℕ → Fin 3) (n : ℕ) :
    n + 1 ≤ (kmswStage w n).nextEdge ∧ (kmswStage w n).nextEdge ≤ 2 * n + 1 := by
  have h1 := CutConverse.allocation_count w n
  have h2 := stage_UR_add_LL_length_le w n
  omega

private theorem measurable_coupled :
    Measurable (fun ω : ℕ → Fin 3 => RandomWalk.vectorPitman (RandomWalk.codeWalk ω)) := by
  apply Measurable.of_eval
  intro n
  have hL : Measurable (fun ω : ℕ → Fin 3 => fun k => (RandomWalk.codeWalk ω k).1) :=
    Measurable.of_eval (fun k =>
      ((measurable_pi_apply k).comp RandomWalk.measurable_codeWalk).fst)
  exact ((((measurable_pi_apply n).comp RandomWalk.measurable_globalLazyPhi).comp hL).prodMk
    (((measurable_pi_apply n).comp RandomWalk.measurable_codeWalk).snd.add
      ((RandomWalk.measurable_globalLazyRunningMinimum n).comp hL)))

private theorem measurableSet_downcrossing_window (r : ℕ) (A : ℝ) :
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

/-- Tightness of the allocation count at the stage before the first hit of
`-r`, for the Pitman-flipped iid codes: with probability at least `1 - ε`, it
lies in `[A⁻¹ r², A r²]`. Helper for `lem-uiqbot-boltzmann` and
`conditionedVectorPathLaw_hitting_window_tight`; not the lemma itself. -/
theorem edges_in_Mr_window_tight (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - ε ≤ RandomWalk.iidCodeMeasure.real {ω : ℕ → Fin 3 | ∃ t : ℕ,
        ((RandomWalk.integrateCodes (RandomWalk.pitmanCode fun i => ω (i + 1)) t).2
            = -(r : ℤ) ∧
          ∀ j < t, (RandomWalk.integrateCodes
            (RandomWalk.pitmanCode fun i => ω (i + 1)) j).2 ≠ -(r : ℤ)) ∧
        (r : ℝ) ^ 2 / A ≤
          ((kmswStage (RandomWalk.pitmanCode fun i => ω (i + 1)) (t - 1)).nextEdge : ℝ) ∧
        ((kmswStage (RandomWalk.pitmanCode fun i => ω (i + 1)) (t - 1)).nextEdge : ℝ)
          ≤ A * (r : ℝ) ^ 2} := by
  classical
  obtain ⟨A0, hA0, hA0t⟩ := RandomWalk.conditionedVectorPathLaw_hitting_window_tight ε hε
  have hA0pos : 0 < A0 := by linarith
  refine ⟨2 * A0, by linarith, ?_⟩
  intro r hr
  have hmain := hA0t r hr
  rw [← RandomWalk.map_vectorPitman_codeWalk,
    map_measureReal_apply measurable_coupled (measurableSet_downcrossing_window r A0)]
    at hmain
  refine hmain.trans (measureReal_mono ?_)
  intro ω hω
  obtain ⟨⟨n, hn, hv⟩, hlow⟩ := hω
  have hV : ∀ k, (RandomWalk.vectorPitman (RandomWalk.codeWalk ω) k).2 =
      R (RandomWalk.pitmanCode fun i => ω (i + 1)) k := by
    intro k
    rw [RandomWalk.kmsw_R_eq, RandomWalk.integrateCodes_pitmanCode,
      show RandomWalk.codeWalk ω = RandomWalk.integrateCodes (fun i => ω (i + 1)) from
        funext (RandomWalk.codeWalk_eq_integrateCodes ω)]
  have hRk : ∀ k, (RandomWalk.integrateCodes (RandomWalk.pitmanCode fun i => ω (i + 1)) k).2 =
      R (RandomWalk.pitmanCode fun i => ω (i + 1)) k :=
    fun k => (RandomWalk.kmsw_R_eq _ k).symm
  set w : ℕ → Fin 3 := RandomWalk.pitmanCode fun i => ω (i + 1) with hw
  rw [hV] at hv
  obtain ⟨k, hkn, hk⟩ := exists_hit_of_unit_down_steps (R w) (R_zero w)
    (R_sub_one_le_succ w) r n hv
  have hex : ∃ k, R w k = -(r : ℤ) := ⟨k, hk⟩
  obtain ⟨t, ht, hmin⟩ : ∃ t, R w t = -(r : ℤ) ∧ ∀ j < t, R w j ≠ -(r : ℤ) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have htk : t ≤ k := by
    by_contra h
    exact hmin k (by omega) hk
  have htle : (t : ℝ) ≤ A0 * (r : ℝ) ^ 2 := by
    have : (t : ℝ) ≤ n := by exact_mod_cast htk.trans hkn
    linarith
  have htge : (r : ℝ) ^ 2 / A0 ≤ t := by
    by_contra h
    have := hlow t (not_le.mp h)
    rw [hV, ht] at this
    exact lt_irrefl _ this
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [R_zero] at ht
    omega
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hb := nextEdge_bounds w m
  have hb1 : ((m + 1 : ℕ) : ℝ) ≤ ((kmswStage w m).nextEdge : ℝ) := by exact_mod_cast hb.1
  have hb2 : ((kmswStage w m).nextEdge : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
    have : (kmswStage w m).nextEdge ≤ 2 * (m + 1) := by omega
    exact_mod_cast this
  have hdiv : (r : ℝ) ^ 2 / (2 * A0) = ((r : ℝ) ^ 2 / A0) / 2 := by
    field_simp
  have hnn : 0 ≤ (r : ℝ) ^ 2 / A0 := by positivity
  refine ⟨m + 1, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hRk]; exact ht
  · intro j hj; rw [hRk]; exact hmin j hj
  · rw [Nat.add_sub_cancel, hdiv]
    linarith
  · rw [Nat.add_sub_cancel]
    linarith

end DirectedDistances.KMSW
