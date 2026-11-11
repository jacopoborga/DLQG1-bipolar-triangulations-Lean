module

public import DirectedDistances.RandomWalk.IIDCodeRelabel
import DirectedDistances.RandomWalk.CellSDPLowerBdy

/-! # First-coordinate boundary hitting time

The source estimate `eqn-lower-tail-time` uses level `-⌊A^(-2/3+ε)√n⌋` and a
gives the explicit constant `4` at every positive integer level `k`, with error
`4k/√N`. For `k ≥ 1`, hitting `-k` cannot occur at time zero. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private theorem sndFirstHit_relabel_twice (a : ℤ) (ω : ℕ → Fin 3) :
    codeSndFirstHit a (codeRelabel (codeRelabel ω)) = codeFstFirstHit a ω := by
  classical
  have hrot (n : ℕ) :
      (codeWalk (codeRelabel (codeRelabel ω)) n).2 = (codeWalk ω n).1 := by
    rw [codeWalk_codeRelabel, codeWalk_codeRelabel]
    dsimp only [stepRotate]
    omega
  unfold codeSndFirstHit codeFstFirstHit
  simp only [hrot]

/-- first-coordinate boundary hitting estimate for the iid code walk; the Busemann
increment estimates of Lemma 7.2 are not claimed; not the paper result. -/
theorem codeFstFirstHit_le_prob_ge (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    1 - 4 * (k : ℝ) / Real.sqrt N ≤
      iidCodeMeasure.real {ω | codeFstFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} := by
  have hm : MeasurableSet {ω | codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} := by
    have hset : {ω | codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} =
        ⋃ n : ℕ, ⋃ (_ : n ≤ N), {ω | codeSndFirstHit (-(k : ℤ)) ω = (n : ℕ∞)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, ENat.le_natCast_iff]
      exact exists_congr fun n =>
        ⟨fun h => ⟨h.2, h.1⟩, fun ⟨hn, heq⟩ => ⟨heq, hn⟩⟩
    rw [hset]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      codePast_le n _ (measurableSet_codePast_codeSndFirstHit_eq (-(k : ℤ)) n)
  have hmp := measurePreserving_codeRelabel.comp measurePreserving_codeRelabel
  have hh := map_measureReal_apply (μ := iidCodeMeasure) hmp.measurable hm
  rw [hmp.map_eq] at hh
  have he : {ω | codeFstFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} =
      (codeRelabel ∘ codeRelabel) ⁻¹'
        {ω | codeSndFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)} := by
    ext ω
    change (codeFstFirstHit (-(k : ℤ)) ω ≤ (N : ℕ∞)) ↔
      (codeSndFirstHit (-(k : ℤ)) (codeRelabel (codeRelabel ω)) ≤ (N : ℕ∞))
    rw [sndFirstHit_relabel_twice]
  rw [he, ← hh]
  exact codeSndFirstHit_le_prob_ge k N hk hN

end DirectedDistances.RandomWalk
