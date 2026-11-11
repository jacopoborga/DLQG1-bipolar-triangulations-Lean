module

public import DirectedDistances.KMSW.EventuallyPresent
public import DirectedDistances.RandomWalk.SecondCoordinateUnbounded

/-! # Almost surely no missing KMSW edges -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory

/-- Almost surely, every edge ID is eventually allocated and permanently present along the -/
theorem pitmanCodes_ae_eventually_present :
    ∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure, ∀ e : ℕ, ∃ N, ∀ n, N ≤ n →
      e < (kmswStage (DirectedDistances.RandomWalk.pitmanCode (fun i => ω (i + 1))) n).nextEdge ∧
      (kmswStage (DirectedDistances.RandomWalk.pitmanCode (fun i => ω (i + 1))) n).present e
        = true := by
  filter_upwards [DirectedDistances.RandomWalk.pitmanCodes_ae_R_unbounded_below] with ω hω e
  refine eventually_present_of_nonneg_of_unbounded _ ?_ ?_ e
  · intro j
    rw [DirectedDistances.RandomWalk.kmsw_L_eq]
    exact DirectedDistances.RandomWalk.integrateCodes_pitmanCode_fst_nonneg _ j
  · intro a
    obtain ⟨n, hn⟩ := hω a
    exact ⟨n, by rw [DirectedDistances.RandomWalk.kmsw_R_eq]; exact hn⟩

end DirectedDistances.KMSW
