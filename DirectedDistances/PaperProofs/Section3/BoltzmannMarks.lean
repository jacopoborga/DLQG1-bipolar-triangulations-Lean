module

public import DirectedDistances.PaperProofs.Section3.BoltzmannFinite
public import DirectedDistances.PaperProofs.Section3.KMSWBdy

/-! # Conditional weights and boundary marks for the Lemma 3.12 bridge

These helper bridges bind the numerical core to the conditional measure and
identify the left boundary observable on the first-hit KMSW prefix. They do
not prove the map law in Lemma 3.11 or the marked normalization. The legal-step convention -/

public section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped ENNReal

/-- The KMSW stream reads the iid code stream after its deterministic time-zero
code. -/
@[expose] def boltzmannKMSWStream (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => ω (i + 1)

/-- The real weight `L(tau)+1` used for the possible marks in Lemma 3.12.
left boundary vertex count is proved below on the conditioning event. -/
@[expose] noncomputable def boltzmannMarkWeight (r : ℕ) (ω : ℕ → Fin 3) : ℝ :=
  ((codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1

private theorem boltzmann_measure_event_ne_zero (r : ℕ) (hr : 1 ≤ r) :
    iidCodeMeasure (boltzmannEvent r) ≠ 0 := by
  have hp := boltzmann_event_positive r hr
  exact (measureReal_ne_zero_iff (by finiteness)).mp (ne_of_gt hp)



theorem boltzmann_cond_isProbabilityMeasure (r : ℕ) (hr : 1 ≤ r) :
    IsProbabilityMeasure (iidCodeMeasure[|boltzmannEvent r]) := by
  exact ProbabilityTheory.cond_isProbabilityMeasure
    (boltzmann_measure_event_ne_zero r hr)




theorem boltzmann_conditional_lintegral_eq_div (r : ℕ) (_hr : 1 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (boltzmannMarkWeight r ω)
      ∂(iidCodeMeasure[|boltzmannEvent r])) =
      (∫⁻ ω in boltzmannEvent r, ENNReal.ofReal (boltzmannMarkWeight r ω)
        ∂iidCodeMeasure) / iidCodeMeasure (boltzmannEvent r) := by
  rw [ProbabilityTheory.cond, MeasureTheory.lintegral_smul_measure, smul_eq_mul,
    ENNReal.div_eq_inv_mul]

/-- The conditional weight lintegral is finite, giving the integrability bridge -/
theorem boltzmann_conditional_measure_lintegral_lt_top (r : ℕ) (hr : 1 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (boltzmannMarkWeight r ω)
      ∂(iidCodeMeasure[|boltzmannEvent r])) < ⊤ := by
  rw [boltzmann_conditional_lintegral_eq_div r hr]
  simpa [boltzmannMarkWeight] using boltzmann_conditional_lintegral_lt_top r hr

private theorem boltzmann_measurable_select_countable
    {Ω ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [MeasurableSpace β]
    (f : ι → Ω → β) (hf : ∀ i, Measurable (f i))
    (g : Ω → ι) (hg : Measurable g) : Measurable (fun ω => f (g ω) ω) := by
  have h : Measurable (fun p : Ω × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

private theorem measurable_boltzmannTau_marks (r : ℕ) :
    Measurable (boltzmannTau r) := by
  classical
  let H : Set (ℕ → Fin 3) := {ω | ∃ n,
    (codeWalk ω n).2 = -(r : ℤ)}
  let hit : ℕ → (ℕ → Fin 3) → Prop := fun n ω =>
    (codeWalk ω n).2 = -(r : ℤ)
  let p : ℕ → (ℕ → Fin 3) → Prop := fun n ω =>
    (∃ k, hit k ω) → hit n ω
  have hhitMeas (n : ℕ) : MeasurableSet {ω | hit n ω} := by
    have hc : Measurable (fun ω : ℕ → Fin 3 => codeWalk ω n) :=
      (measurable_pi_apply n).comp measurable_codeWalk
    exact (measurable_snd.comp hc) (measurableSet_singleton (-(r : ℤ)))
  have hHmeas : MeasurableSet H := by
    rw [show H = ⋃ n, {ω | hit n ω} by
      ext ω
      simp [H, hit]]
    exact MeasurableSet.iUnion hhitMeas
  have hpMeas (n : ℕ) : MeasurableSet {ω | p n ω} := by
    rw [show {ω | p n ω} = Hᶜ ∪ {ω | hit n ω} by
      ext ω
      constructor
      · intro hp
        by_cases hH : ω ∈ H
        · right
          change ∃ k, hit k ω at hH
          obtain ⟨k, hk⟩ := hH
          exact hp ⟨k, hk⟩
        · exact Or.inl hH
      · rintro (hH | hn)
        · intro hex
          exact (hH hex).elim
        · intro _
          exact hn]
    exact MeasurableSet.union hHmeas.compl (hhitMeas n)
  have hp : ∀ ω, ∃ n, p n ω := by
    intro ω
    by_cases hω : ω ∈ H
    · change ∃ n, hit n ω at hω
      obtain ⟨n, hn⟩ := hω
      exact ⟨n, fun _ => hn⟩
    · refine ⟨0, ?_⟩
      intro h
      exact ((show ¬ ∃ n, hit n ω by simpa [H] using hω) h).elim
  have hfind : Measurable (fun ω => Nat.find (hp ω)) :=
    measurable_find hp hpMeas
  have heq : (fun ω => Nat.find (hp ω)) = boltzmannTau r := by
    funext ω
    by_cases hω : ∃ n, hit n ω
    · have hHω : ω ∈ H := by simpa [H, hit] using hω
      have hfindEq : Nat.find (hp ω) = Nat.find hω := by
        apply (Nat.find_eq_iff (hp ω)).2
        constructor
        · intro _
          exact Nat.find_spec hω
        · intro k hk hp
          exact (Nat.find_min hω hk) (hp hω)
      have hτ : boltzmannTau r ω = Nat.find hω := by
        simp [boltzmannTau, hit, hω]
      rw [hτ]
      exact hfindEq
    · have hHω : ω ∉ H := by simpa [H, hit] using hω
      have hno : ¬ ∃ n, hit n ω := by simpa [H] using hHω
      have hfindZero : Nat.find (hp ω) = 0 :=
        (Nat.find_eq_zero (hp ω)).2 (by
          intro h
          exact (hno h).elim)
      have hτ : boltzmannTau r ω = 0 := by
        simp [boltzmannTau, hit, hω]
      rw [hτ]
      exact hfindZero
  simpa only [← heq] using hfind

/-- The source weight is measurable, including the harmless zero totalization
of `tau` off paths with a hit. -/
theorem measurable_boltzmannMarkWeight (r : ℕ) :
    Measurable (boltzmannMarkWeight r) := by
  unfold boltzmannMarkWeight
  apply boltzmann_measurable_select_countable
    (fun n ω => ((codeWalk ω n).1 : ℝ) + 1)
  · intro n
    have hc : Measurable (fun ω : ℕ → Fin 3 => codeWalk ω n) :=
      (measurable_pi_apply n).comp measurable_codeWalk
    exact ((measurable_of_countable fun z : ℤ => (z : ℝ)).comp
      (measurable_fst.comp hc)).add_const 1
  · exact measurable_boltzmannTau_marks r




theorem boltzmann_conditional_weight_integrable_and_integral_le
    (r : ℕ) (hr : 1 ≤ r) :
    Integrable (boltzmannMarkWeight r) (iidCodeMeasure[|boltzmannEvent r]) ∧
      (∫ ω, boltzmannMarkWeight r ω
        ∂(iidCodeMeasure[|boltzmannEvent r])) ≤
          1 / iidCodeMeasure.real (boltzmannEvent r) := by
  let f : (ℕ → Fin 3) → ℝ := boltzmannMarkWeight r
  have hE0 : iidCodeMeasure (boltzmannEvent r) ≠ 0 :=
    boltzmann_measure_event_ne_zero r hr
  have hfin : iidCodeMeasure (boltzmannEvent r) ≠ ⊤ := by finiteness
  have hrestrict : Integrable f
      (iidCodeMeasure.restrict (boltzmannEvent r)) := by
    exact boltzmann_weight_integrableOn r hr
  have hint : Integrable f
      ((iidCodeMeasure (boltzmannEvent r))⁻¹ •
        iidCodeMeasure.restrict (boltzmannEvent r)) :=
    hrestrict.smul_measure (ENNReal.inv_ne_top.2 hE0)
  have hcondInt : Integrable f (iidCodeMeasure[|boltzmannEvent r]) := by
    simpa [ProbabilityTheory.cond, f] using hint
  refine ⟨hcondInt, ?_⟩
  have hcondEq :
      (∫ ω, f ω ∂(iidCodeMeasure[|boltzmannEvent r])) =
        (iidCodeMeasure.real (boltzmannEvent r))⁻¹ *
          ∫ ω in boltzmannEvent r, f ω ∂iidCodeMeasure := by
    rw [ProbabilityTheory.cond, MeasureTheory.integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_inv, MeasureTheory.measureReal_def]
  rw [hcondEq]
  have hratio := boltzmann_real_conditional_expectation_le r hr
  simpa [f, boltzmannMarkWeight, div_eq_mul_inv, mul_comm] using hratio

private theorem boltzmann_tau_no_prior_hit (r : ℕ) (ω : ℕ → Fin 3)
    (hE : ω ∈ boltzmannEvent r) :
    ∀ j < boltzmannTau r ω,
      (codeWalk ω j).2 ≠ -(r : ℤ) := by
  rcases hE with ⟨s, hs, _⟩
  let hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := ⟨s, hs⟩
  have hτ : boltzmannTau r ω = Nat.find hhit := by
    simp [boltzmannTau, hhit]
  intro j hj heq
  have hj' : j < Nat.find hhit := by simpa [hτ] using hj
  exact (Nat.find_min hhit hj') heq

private theorem boltzmann_codeWalk_snd_step_lower (ω : ℕ → Fin 3) (i : ℕ) :
    -1 ≤ (codeWalk ω (i + 1)).2 - (codeWalk ω i).2 := by
  have h : (codeWalk ω (i + 1)).2 - (codeWalk ω i).2 =
      (lazyTwoDimensionalStep (ω (i + 1))).2 := by
    simpa only [Prod.snd_sub] using congrArg Prod.snd (codeWalk_succ_sub ω i)
  rw [h]
  generalize hc : ω (i + 1) = c
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

private theorem boltzmann_R_strictly_above_before (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3)
    (hE : ω ∈ boltzmannEvent r) :
    ∀ j < boltzmannTau r ω,
      -(r : ℤ) < (codeWalk ω j).2 := by
  have hno := boltzmann_tau_no_prior_hit r ω hE
  intro j hj
  induction j with
  | zero =>
      rw [codeWalk_zero]
      omega
  | succ j ih =>
      have hjt : j < boltzmannTau r ω := by omega
      have hprev := ih hjt
      have hlowerStep := boltzmann_codeWalk_snd_step_lower ω j
      have hlower : -(r : ℤ) ≤ (codeWalk ω (j + 1)).2 := by omega
      have hnot := hno (j + 1) hj
      omega

private theorem boltzmann_stream_walk_eq (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).1 = L (boltzmannKMSWStream ω) n ∧
      (codeWalk ω n).2 = R (boltzmannKMSWStream ω) n := by
  constructor <;> simp [boltzmannKMSWStream, codeWalk, L, R,
    Prod.fst_sum, Prod.snd_sum]






theorem boltzmann_boundary_observable (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    1 ≤ t ∧ ω t = 2 ∧ minL w (t - 1) = 0 ∧
      ((Finset.card (kmswStageLLDartsFinset w (t - 1)) : ℤ) = 0) ∧
      ((Finset.card (kmswStageULDartsFinset w (t - 1)) : ℤ) =
        L w t) ∧
      ((Finset.card (kmswStageLRDartsFinset w (t - 1)) : ℤ) = r) ∧
      ((Finset.card (kmswStageURDartsFinset w (t - 1)) : ℤ) = 0) ∧
      ((Finset.card (kmswStageULDartsFinset w (t - 1)) : ℤ) + 1 =
        L w t + 1) := by
  dsimp only
  let t := boltzmannTau r ω
  let w := boltzmannKMSWStream ω
  rcases hE with ⟨s, hs, hLnonneg⟩
  have hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := ⟨s, hs⟩
  have hτhit : (codeWalk ω t).2 = -(r : ℤ) :=
    boltzmann_tau_spec r ω hhit
  have htpos : 1 ≤ t := by
    by_contra h
    have ht0 : t = 0 := by omega
    rw [ht0, codeWalk_zero] at hτhit
    omega
  let n := t - 1
  have htn : n + 1 = t := by dsimp [n]; omega
  have hnt : n < t := by omega
  have hRprior : -(r : ℤ) < (codeWalk ω n).2 :=
    boltzmann_R_strictly_above_before r hr ω ⟨s, hs, hLnonneg⟩ n hnt
  have hRpriorEq : (codeWalk ω n).2 = -(r : ℤ) + 1 := by
    have hstepLower := boltzmann_codeWalk_snd_step_lower ω n
    rw [← htn] at hτhit
    omega
  have hlastCode : ω t = 2 := by
    have hinc := congrArg Prod.snd (codeWalk_succ_sub ω n)
    change (codeWalk ω (n + 1)).2 - (codeWalk ω n).2 =
      (lazyTwoDimensionalStep (ω (n + 1))).2 at hinc
    rw [htn] at hinc
    have hdelta : (codeWalk ω t).2 - (codeWalk ω n).2 = -1 := by
      rw [hτhit, hRpriorEq]
      omega
    rw [hdelta] at hinc
    have hcodeStep : (lazyTwoDimensionalStep (ω t)).2 = -1 := hinc.symm
    generalize hcode : ω t = c
    fin_cases c <;> simp [lazyTwoDimensionalStep] at hcodeStep <;> simp_all
  have hnonnegPrefix : ∀ j ≤ t, 0 ≤ L w j := by
    intro j hj
    have hj' : j ≤ s := by
      have hle : t ≤ s := by
        have hτ : t = Nat.find hhit := by simp [t, boltzmannTau, hhit]
        rw [hτ]
        exact Nat.find_min' hhit hs
      exact le_trans hj hle
    have hL := hLnonneg j hj'
    rw [← (boltzmann_stream_walk_eq ω j).1]
    exact hL
  have hminL : minL w n = 0 := by
    apply le_antisymm
    · have := runningMin_le (L w) n 0 (by omega)
      change minL w n ≤ L w 0 at this
      simp [L] at this
      simpa using this
    · obtain ⟨j, hj, hval⟩ := runningMin_attained (L w) n
      change 0 ≤ runningMin (L w) n
      rw [hval]
      exact hnonnegPrefix j (by omega)
  have hprefixR : ∀ j ≤ n, -(r : ℤ) + 1 ≤ R w j := by
    intro j hj
    have hstrict := boltzmann_R_strictly_above_before r hr ω ⟨s, hs, hLnonneg⟩
      j (by omega)
    have hwalk := (boltzmann_stream_walk_eq ω j).2
    have hRstrict : -(r : ℤ) < R w j := by
      rw [← hwalk]
      exact hstrict
    omega
  have hRwalkPrev : R w n = -(r : ℤ) + 1 := by
    exact (boltzmann_stream_walk_eq ω n).2.symm.trans hRpriorEq
  have hminR : minR w n = -(r : ℤ) + 1 := by
    apply le_antisymm
    · have := runningMin_le (R w) n n le_rfl
      change minR w n ≤ R w n at this
      rw [hRwalkPrev] at this
      exact this
    · obtain ⟨j, hj, hval⟩ := runningMin_attained (R w) n
      change -(r : ℤ) + 1 ≤ runningMin (R w) n
      rw [hval]
      exact hprefixR j hj
  have hLsucc : L w (n + 1) = L w n + 1 := by
    rw [show L w (n + 1) = L w n +
      (lazyTwoDimensionalStep (w n)).1 by exact Finset.sum_range_succ _ _]
    rw [show w n = ω t by simp [w, boltzmannKMSWStream, n, htn]]
    simp [hlastCode, lazyTwoDimensionalStep_two]
  have hcards := kmsw_bdy_geometric_segment_cardinalities w n
  have hUL : (Finset.card (kmswStageULDartsFinset w n) : ℤ) =
      L w t := by
    rw [hcards.1, hminL]
    calc
      L w n - 0 + 1 = L w n + 1 := by omega
      _ = L w (n + 1) := hLsucc.symm
      _ = L w t := by
        rw [htn]
  have hLL : (Finset.card (kmswStageLLDartsFinset w n) : ℤ) = 0 := by
    rw [hcards.2.2.1, hminL]
    simp
  have hLR : (Finset.card (kmswStageLRDartsFinset w n) : ℤ) = r := by
    rw [hcards.2.2.2, hminR]
    simp
  have hUR : (Finset.card (kmswStageURDartsFinset w n) : ℤ) = 0 := by
    rw [hcards.2.1, hRwalkPrev, hminR]
    simp
  refine ⟨htpos, hlastCode, hminL, hLL, hUL, hLR, hUR, ?_⟩
  exact congrArg (fun z : ℤ => z + 1) hUL

/-- On the conditioning event, the measurable weight equals the possible-mark
count on the left boundary path. Here that vertex count is the left boundary
edge count plus one. This supplies the boundary-observable part of the
Lemma 3.12 bridge; it does not assert the marked map law or normalization. -/
theorem boltzmannMarkWeight_eq_leftBoundaryVertexCount
    (r : ℕ) (hr : 1 ≤ r) (ω : ℕ → Fin 3)
    (hE : ω ∈ boltzmannEvent r) :
    boltzmannMarkWeight r ω =
      (((Finset.card (kmswStageULDartsFinset
        (boltzmannKMSWStream ω) (boltzmannTau r ω - 1)) : ℤ) + 1 : ℤ) : ℝ) := by
  have hb := boltzmann_boundary_observable r hr ω hE
  rcases hb with ⟨_, _, _, _, hUL, _, _, _⟩
  have hmarks :
      (Finset.card (kmswStageULDartsFinset
        (boltzmannKMSWStream ω) (boltzmannTau r ω - 1)) : ℤ) + 1 =
        (codeWalk ω (boltzmannTau r ω)).1 + 1 := by
    calc
      _ = L (boltzmannKMSWStream ω) (boltzmannTau r ω) + 1 := by rw [hUL]
      _ = (codeWalk ω (boltzmannTau r ω)).1 + 1 := by
        rw [(boltzmann_stream_walk_eq ω (boltzmannTau r ω)).1]
  unfold boltzmannMarkWeight
  exact_mod_cast hmarks.symm

end DirectedDistances.PaperProofs.Section3
