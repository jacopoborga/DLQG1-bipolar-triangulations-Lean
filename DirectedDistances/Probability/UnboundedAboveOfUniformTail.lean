module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

public section
namespace DirectedDistances.Probability

open MeasureTheory
open scoped ENNReal

private theorem unboundedAbove_eq_iInter_nat
    {Ω : Type*} [MeasurableSpace Ω] {S : ℕ → Ω → ℝ} :
    {ω | ∀ A : ℝ, ∃ k, A < S k ω} =
      ⋂ A : ℕ, {ω | ∃ k, (A : ℝ) < S k ω} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro h A
    exact h (A : ℝ)
  · intro h A
    obtain ⟨n, hn⟩ := exists_nat_gt A
    obtain ⟨k, hk⟩ := h n
    exact ⟨k, lt_trans hn hk⟩



theorem prob_unbounded_above_ge_of_uniform_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : ℕ → Ω → ℝ} (hS : ∀ k, Measurable (S k)) {c : ℝ≥0∞}
    (htail : ∀ A : ℕ, ∀ k, 2 * A ≤ k → c ≤ μ {ω | (A : ℝ) < S k ω}) :
    c ≤ μ {ω | ∀ A : ℝ, ∃ k, A < S k ω} := by
  let s : ℕ → Set Ω := fun A => {ω | ∃ k, (A : ℝ) < S k ω}
  have hs : ∀ A, MeasurableSet (s A) := by
    intro A
    change MeasurableSet {ω | ∃ k, (A : ℝ) < S k ω}
    rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_lt measurable_const (hS k)
  have hanti : Antitone s := by
    intro A B hAB ω hω
    obtain ⟨k, hk⟩ := hω
    exact ⟨k, lt_of_le_of_lt (Nat.cast_le.mpr hAB) hk⟩
  have hlower : ∀ A, c ≤ μ (s A) := by
    intro A
    calc
      c ≤ μ {ω | (A : ℝ) < S (2 * A) ω} := htail A (2 * A) le_rfl
      _ ≤ μ (s A) := measure_mono (by
        intro ω hω
        exact ⟨2 * A, hω⟩)
  have hfin : ∃ A, μ (s A) ≠ ∞ := by
    refine ⟨0, ?_⟩
    intro htop
    have hle : μ (s 0) ≤ (1 : ℝ≥0∞) := by
      calc
        μ (s 0) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    rw [htop] at hle
    norm_num at hle
  have hcont : μ (⋂ A : ℕ, s A) = ⨅ A : ℕ, μ (s A) :=
    hanti.measure_iInter (fun A => (hs A).nullMeasurableSet) hfin
  have heq : {ω | ∀ A : ℝ, ∃ k, A < S k ω} = ⋂ A : ℕ, s A := by
    simpa only [s] using (unboundedAbove_eq_iInter_nat (S := S))
  calc
    c ≤ ⨅ A : ℕ, μ (s A) := le_iInf hlower
    _ = μ (⋂ A : ℕ, s A) := hcont.symm
    _ = μ {ω | ∀ A : ℝ, ∃ k, A < S k ω} := congrArg μ heq.symm

private theorem measurable_int_cast_real : Measurable (fun z : ℤ => (z : ℝ)) :=
  measurable_of_countable _



theorem prob_unbounded_above_ge_of_uniform_tail_int
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : ℕ → Ω → ℤ} (hS : ∀ k, Measurable (S k)) {c : ℝ≥0∞}
    (htail : ∀ A : ℕ, ∀ k, 2 * A ≤ k →
      c ≤ μ {ω | (A : ℝ) < (S k ω : ℝ)}) :
    c ≤ μ {ω | ∀ A : ℤ, ∃ k, A < S k ω} := by
  have hSreal : ∀ k, Measurable (fun ω => (S k ω : ℝ)) := by
    intro k
    exact measurable_int_cast_real.comp (hS k)
  have hreal := prob_unbounded_above_ge_of_uniform_tail
    (μ := μ) (S := fun k ω => (S k ω : ℝ)) hSreal htail
  apply le_trans hreal
  apply measure_mono
  intro ω hω
  change ∀ A : ℤ, ∃ k, A < S k ω
  intro A
  obtain ⟨k, hk⟩ := hω (A : ℝ)
  exact ⟨k, by exact_mod_cast hk⟩



theorem prob_eq_one_of_zero_one_of_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {E : Set Ω}
    (h01 : μ E = 0 ∨ μ E = 1) (hpos : 0 < μ E) : μ E = 1 := by
  rcases h01 with hzero | hone
  · rw [hzero] at hpos
    exact False.elim ((lt_irrefl (0 : ℝ≥0∞)) hpos)
  · exact hone

end DirectedDistances.Probability
