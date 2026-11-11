module

public import DirectedDistances.RandomWalk.BlockBoundAssembly
public import DirectedDistances.RandomWalk.IIDWalkMaximalTailBound

/-! # Unconditional block bound for the proof of Lemma 4.12

The within-block maximal tail `iidCodeWalk_blockMax_tail` discharges the hypothesis `htail`
of `RandomWalk/BlockBoundAssembly.lean`. This gives, for the constructed conditioned law
`conditionedVectorPathLaw 0 0`, the uniform block bound of `lem-walk-bdy-sum`
infinitely many cut vertices of the KMSW bookkeeping of the fallback-free UIQBOT code
helper statements; no numbered source result is admitted here. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory
open scoped ENNReal

private theorem iidCodeWalk_htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
    iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
      (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
       a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
      4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))) :=
  fun s m hm a ha => iidCodeWalk_blockMax_tail s m hm a ha

/-- Uniform block bound `∃ q > 0, ∀ N ≥ 100, q ≤ P̂[E_N]` for the constructed conditioned -/
theorem conditionedVectorPathLaw_blockProb :
    ∃ q : ℝ, 0 < q ∧ ∀ N : ℕ, 100 ≤ N → q ≤ (conditionedVectorPathLaw 0 0).real
      {p : ℕ → ℤ × ℤ |
        (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
          Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
        (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
        ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} :=
  conditionedVectorPathLaw_blockProb_of_tail iidCodeWalk_htail

/-- The success-probability series diverges: `∑_{n ≥ 1} P̂[A_n ∩ B_n] = ∞` for the
constructed conditioned law, with `A_n`, `B_n` from `eqn-walk-bdy-event` -/
theorem conditionedVectorPathLaw_tsum_success_eq_top :
    ∑' n, conditionedVectorPathLaw 0 0 {p : ℕ → ℤ × ℤ |
      (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1} = ∞ :=
  conditionedVectorPathLaw_tsum_success_eq_top_of_tail iidCodeWalk_htail

/-- Almost surely there are infinitely many `n ≥ 1` with `A_n ∩ B_n` under the constructed -/
theorem conditionedVectorPathLaw_ae_infinite_success :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), {n : ℕ |
      (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.Infinite :=
  conditionedVectorPathLaw_ae_infinite_success_of_tail iidCodeWalk_htail

end DirectedDistances.RandomWalk

namespace DirectedDistances.KMSW

open MeasureTheory DirectedDistances.RandomWalk

/-- Almost surely the KMSW bookkeeping of the Pitman-flipped iid code sequence has
infinitely many cut vertices (helper for `prop-cut-vertex`, -/
theorem pitmanCodes_ae_infinite_cutVertices :
    ∀ᵐ ω ∂iidCodeMeasure,
      {v : ℕ | IsCutVertex (pitmanCode (fun i => ω (i + 1))) v}.Infinite :=
  pitmanCodes_ae_infinite_cutVertices_of_tail
    (fun s m hm a ha => iidCodeWalk_blockMax_tail s m hm a ha)

end DirectedDistances.KMSW
