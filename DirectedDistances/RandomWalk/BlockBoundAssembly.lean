module

public import DirectedDistances.RandomWalk.IIDWalkTubeAssembly
public import DirectedDistances.RandomWalk.TubeBlockEvent
public import DirectedDistances.RandomWalk.BlockEventPositive
public import DirectedDistances.RandomWalk.SuccessSumAssembly
public import DirectedDistances.KMSW.CutVerticesInfinite
import DirectedDistances.RandomWalk.PitmanPrefixCompatibility

/-! # Block bound assembly for the proof of Lemma 4.12

The eventual tube estimate for the iid code walk, the tube-to-block inclusion through the
vector Pitman flip, and positivity for each fixed `N ≥ 100` combine into the uniform block
bound `∃ q > 0, ∀ N ≥ 100, q ≤ P̂[E_N]` used in the proof of `lem-walk-bdy-sum`,

The within-block maximal tail of the iid code walk remains an explicit hypothesis `htail`
of every statement here; it is supplied by a separate helper. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem measurable_vectorPitman_block : Measurable vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add ((measurable_globalLazyRunningMinimum n).comp hf))

private theorem exists_pos_le_below (p : ℕ → ℝ) (hp : ∀ N, 100 ≤ N → 0 < p N) (M : ℕ) :
    ∃ q : ℝ, 0 < q ∧ ∀ N, 100 ≤ N → N < M → q ≤ p N := by
  induction M with
  | zero => exact ⟨1, one_pos, fun N _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ M ih =>
    obtain ⟨q, hq, hle⟩ := ih
    by_cases hM : 100 ≤ M
    · refine ⟨min q (p M), lt_min hq (hp M hM), fun N hN hNM => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hNM) with h | h
      · exact (min_le_left _ _).trans (hle N hN h)
      · rw [h]
        exact min_le_right _ _
    · exact ⟨q, hq, fun N hN hNM => hle N hN (by omega)⟩

/-- The tube event of the iid code walk has at most the conditioned mass of the block
event `E_N`, through the vector Pitman flip (`lem-walk-bdy-sum`, -/
theorem iidTube_real_le_conditionedBlock (N : ℕ) (hN : 1 ≤ N) :
    iidCodeMeasure.real {ω : ℕ → Fin 3 | ∀ n ≤ N,
        |((codeWalk ω n).1 : ℝ) - (n : ℝ) / N * Real.sqrt N| ≤ Real.sqrt N / 10 ∧
        |((codeWalk ω n).2 : ℝ) - (-6 * max 0 ((n : ℝ) / N - 1 / 2)) * Real.sqrt N| ≤
          Real.sqrt N / 10} ≤
      (conditionedVectorPathLaw 0 0).real {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
  have hmeas : Measurable (fun ω : ℕ → Fin 3 => fun k => vectorPitman (codeWalk ω) k) :=
    measurable_vectorPitman_block.comp measurable_codeWalk
  rw [← map_vectorPitman_codeWalk]
  refine (measureReal_mono (s₂ := (fun ω : ℕ → Fin 3 => fun k => vectorPitman (codeWalk ω) k) ⁻¹'
      {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) ?_ (measure_ne_top _ _)).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_map_apply hmeas.aemeasurable _))
  intro ω hω
  exact vectorPitman_mem_block_of_tube (codeWalk ω) N hN (codeWalk_zero ω)
    (fun n hn => (hω n hn).1) (fun n hn => (hω n hn).2)

/-- Uniform block bound `∃ q > 0, ∀ N ≥ 100, q ≤ P̂[E_N]` for the constructed conditioned
maximal tail `htail` of the iid code walk. -/
theorem conditionedVectorPathLaw_blockProb_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ)))) :
    ∃ q : ℝ, 0 < q ∧ ∀ N : ℕ, 100 ≤ N → q ≤ (conditionedVectorPathLaw 0 0).real
      {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
  obtain ⟨q₁, hq₁, N₀, hN₀⟩ := iidCodeWalk_eventually_tube_mass_of_tail htail
  obtain ⟨q₂, hq₂, hsmall⟩ := exists_pos_le_below
    (fun N => (conditionedVectorPathLaw 0 0).real {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N})
    conditionedVectorPathLaw_recordBlock_pos (max N₀ 1)
  refine ⟨min q₁ q₂, lt_min hq₁ hq₂, fun N hN => ?_⟩
  by_cases hNM : N < max N₀ 1
  · exact (min_le_right _ _).trans (hsmall N hN hNM)
  · have hge : max N₀ 1 ≤ N := Nat.le_of_not_lt hNM
    exact (min_le_left _ _).trans ((hN₀ N ((le_max_left _ _).trans hge)).trans
      (iidTube_real_le_conditionedBlock N ((le_max_right _ _).trans hge)))

/-- The success-probability series of `lem-walk-bdy-sum` diverges -/
theorem conditionedVectorPathLaw_tsum_success_eq_top_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ)))) :
    ∑' n, conditionedVectorPathLaw 0 0 {p : ℕ → ℤ × ℤ |
      (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1} = ∞ := by
  obtain ⟨q, hq, hE⟩ := conditionedVectorPathLaw_blockProb_of_tail htail
  exact conditionedVectorPathLaw_tsum_success_eq_top_of_blockProb q hq hE

/-- Almost surely infinitely many successes `A_n ∩ B_n` (proof of `prop-cut-vertex`, -/
theorem conditionedVectorPathLaw_ae_infinite_success_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ)))) :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), {n : ℕ | (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.Infinite := by
  obtain ⟨q, hq, hE⟩ := conditionedVectorPathLaw_blockProb_of_tail htail
  exact conditionedVectorPathLaw_ae_infinite_success_of_blockProb q hq hE

end DirectedDistances.RandomWalk

namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.RandomWalk

/-- Almost surely the KMSW bookkeeping of the Pitman-flipped iid code sequence has
infinitely many cut vertices (helper for `prop-cut-vertex`,
tail `htail` of the iid code walk. -/
theorem pitmanCodes_ae_infinite_cutVertices_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ)))) :
    ∀ᵐ ω ∂iidCodeMeasure,
      {v : ℕ | IsCutVertex (pitmanCode (fun i => ω (i + 1))) v}.Infinite := by
  obtain ⟨q, hq, hE⟩ := conditionedVectorPathLaw_blockProb_of_tail htail
  exact pitmanCodes_ae_infinite_cutVertices_of_blockProb q hq hE

end DirectedDistances.KMSW
