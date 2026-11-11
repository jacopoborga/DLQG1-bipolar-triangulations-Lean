/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineEntryFrontier
public import DirectedDistances.KMSW.FlowLineLPhase

/-! # Reachability characterization of the flow-line times

`flowLineTimes_iff` is `eqn-flow-line-times` of `lem-flow-line-times`
`walkNR k = N_{k+1}^R`, `walkNL k = N_{k+1}^L`: the active west vertex at stage
`n` is reachable from the root exactly when `n` lies in some right phase
`[N_{k+1}^R, N_{k+1}^L)`. Items (i) and (ii) of the lemma are separate. -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Every time lies in some right phase `[walkNR k, walkNL k)` or some left phase
`[walkNL k, walkNR (k+1))`. -/
theorem flowLine_phase_partition (w : ℕ → Fin 3) (h : HasFlowLineHits w) (n : ℕ) :
    ∃ k, (walkNR w h k ≤ n ∧ n < walkNL w h k) ∨
      (walkNL w h k ≤ n ∧ n < walkNR w h (k + 1)) := by
  induction n with
  | zero =>
      refine ⟨0, Or.inl ⟨by rw [walkNR_zero], ?_⟩⟩
      have := walkNL_spec w h 0
      omega
  | succ n ih =>
      obtain ⟨k, hk | hk⟩ := ih
      · by_cases hlt : n + 1 < walkNL w h k
        · exact ⟨k, Or.inl ⟨by omega, hlt⟩⟩
        · have := walkNR_succ_spec w h k
          exact ⟨k, Or.inr ⟨by omega, by omega⟩⟩
      · by_cases hlt : n + 1 < walkNR w h (k + 1)
        · exact ⟨k, Or.inr ⟨by omega, hlt⟩⟩
        · have := walkNL_spec w h (k + 1)
          exact ⟨k + 1, Or.inl ⟨by omega, by omega⟩⟩

/-- `eqn-flow-line-times` of `lem-flow-line-times`
reachable from the root iff `n ∈ [N_{k+1}^R, N_{k+1}^L)` for some `k`. -/
theorem flowLineTimes_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w) (n : ℕ) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).west (act w n)⟩ ↔
      ∃ k, walkNR w h k ≤ n ∧ n < walkNL w h k := by
  constructor
  · intro hr
    obtain ⟨k, hk | hk⟩ := flowLine_phase_partition w h n
    · exact ⟨k, hk⟩
    · exact absurd hr (lPhase_activeWest_unreachable w h k n hk.1 hk.2)
  · rintro ⟨k, hk, hk'⟩
    exact flowLine_phase_reachable w h k n hk hk'

/-- Almost surely, `eqn-flow-line-times` holds for the walk codes
`fun i => ω (i + 1)`. -/
theorem iidCodes_ae_flowLineTimes_iff :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
        ∀ n, Reachable (⟨0⟩ : PresentVertex (fun i => ω (i + 1)))
            ⟨(kmswStage (fun i => ω (i + 1)) n).west (act (fun i => ω (i + 1)) n)⟩ ↔
          ∃ k, walkNR (fun i => ω (i + 1)) h k ≤ n ∧
            n < walkNL (fun i => ω (i + 1)) h k := by
  filter_upwards [ae_hasFlowLineHits] with ω hω
  exact ⟨hω, fun n => flowLineTimes_iff _ hω n⟩

end DirectedDistances.KMSW
