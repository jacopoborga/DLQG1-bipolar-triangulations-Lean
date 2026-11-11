module

public import DirectedDistances.KMSW.CutEquivalenceConverse
public import DirectedDistances.RandomWalk.PitmanCodes
import DirectedDistances.RandomWalk.ConditionedTransience
import DirectedDistances.RandomWalk.PitmanPrefixCompatibility

/-! # Almost-sure cut-vertex equivalence for the flipped iid codes -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk

private theorem measurable_vectorPitman'' : Measurable vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add ((measurable_globalLazyRunningMinimum n).comp hf))

/-- Almost surely, for the Pitman-flipped iid codes, the cut-vertex/first-visit condition at -/
theorem pitmanCodes_ae_cut_equiv :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ n : ℕ,
      let w := pitmanCode (fun i => ω (i + 1))
      (IsCutVertex w (activeInitial w n) ∧ ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
        ((∀ j < n, R w n ≤ R w j - 1) ∧ (∀ j, n ≤ j → L w n ≤ L w j)) := by
  have hmeas : Measurable (fun ω : ℕ → Fin 3 => fun k => vectorPitman (codeWalk ω) k) :=
    measurable_vectorPitman''.comp measurable_codeWalk
  have hT := ae_of_ae_map hmeas.aemeasurable
    (by rw [map_vectorPitman_codeWalk]
        exact conditionedVectorPathLaw_tendsto_fst_atTop 0 0)
  filter_upwards [hT] with ω hT n
  intro w
  have hPw : ∀ n, vectorPitman (codeWalk ω) n = integrateCodes w n := by
    intro n
    rw [integrateCodes_pitmanCode]
    rfl
  have htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop := by
    have : L w = fun j => (vectorPitman (codeWalk ω) j).1 := by
      funext j
      rw [kmsw_L_eq, hPw]
    rw [this]
    exact hT
  have hL0 : ∀ j, 0 ≤ L w j := by
    intro j
    rw [kmsw_L_eq]
    exact integrateCodes_pitmanCode_fst_nonneg _ j
  exact cut_equiv_of_nonneg_of_tendsto w hL0 htrans n

end DirectedDistances.KMSW
