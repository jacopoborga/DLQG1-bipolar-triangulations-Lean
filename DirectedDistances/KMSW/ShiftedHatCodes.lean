/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.ZHatCharacterization
public import DirectedDistances.KMSW.InftyCutCore
public import DirectedDistances.KMSW.FlowLineTimes

/-! # Shifted R-code composition helpers

These helpers connect the fixed-time future-code convention in
R-phase window codes in `lem-infty-cut`
P1; they do not prove `lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk

private theorem quadrantSplitState_congr_of_succ_eq
    (ω ν : ℕ → Fin 3) (h : ∀ i, ω (i + 1) = ν (i + 1)) :
    ∀ n, RandomWalk.quadrantSplitState ω n =
      RandomWalk.quadrantSplitState ν n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [RandomWalk.quadrantSplitState, ih, h n]

private theorem quadrantRCode_congr_of_succ_eq
    (ω ν : ℕ → Fin 3) (h : ∀ i, ω (i + 1) = ν (i + 1)) (k : ℕ) :
    RandomWalk.quadrantRCode ω k = RandomWalk.quadrantRCode ν k := by
  classical
  let P (ξ : ℕ → Fin 3) :=
    ∃ n, (RandomWalk.quadrantSplitState ξ n).rCount = k + 1
  have hP : P ω ↔ P ν := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [P, quadrantSplitState_congr_of_succ_eq ω ν h n] using hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [P, quadrantSplitState_congr_of_succ_eq ω ν h n] using hn⟩
  change (if hω : P ω then ω (Nat.find hω) else 0) =
    (if hν : P ν then ν (Nat.find hν) else 0)
  by_cases hω : P ω
  · have hν : P ν := hP.mp hω
    rw [dite_eq_left hν, dite_eq_left hω]
    have hfind : Nat.find hν = Nat.find hω := by
      apply Nat.find_congr'
      intro n
      rw [quadrantSplitState_congr_of_succ_eq ω ν h n]
    rw [hfind]
    have hpos : Nat.find hω ≠ 0 := by
      intro hz
      have hs := Nat.find_spec hω
      rw [hz, RandomWalk.quadrantSplitState] at hs
      simp [RandomWalk.quadrantSplitStart] at hs
    have hindex : Nat.find hω - 1 + 1 = Nat.find hω := by omega
    have hh := h (Nat.find hω - 1)
    rw [hindex] at hh
    exact hh
  · have hν : ¬ P ν := fun hν => hω (hP.mpr hν)
    simp [hω, hν]

private theorem phaseSplit_fst_congr_of_succ_eq
    (ω ν : ℕ → Fin 3) (h : ∀ i, ω (i + 1) = ν (i + 1)) :
    (RandomWalk.phaseSplit ω).1 = (RandomWalk.phaseSplit ν).1 := by
  funext i
  simp only [RandomWalk.phaseSplit]
  by_cases hi : i = 0
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    exact quadrantRCode_congr_of_succ_eq ω ν h (i - 1)

/-- `rCodeSequence` is independent of the input at index zero: it depends
only on the positive-index source codes. This follows from `phaseSplit`
reading `ω (n + 1)` and `rPhaseCodeSequence` dropping its dummy coordinate
composition helper for P1, not a proof of `lem-quad-kmsw`. -/
theorem rCodeSequence_eq_of_succ_eq (ω ν : ℕ → Fin 3)
    (h : ∀ i, ω (i + 1) = ν (i + 1)) :
    rCodeSequence ω = rCodeSequence ν := by
  have hphase : rPhaseCodeSequence ω = rPhaseCodeSequence ν := by
    funext i
    change (RandomWalk.phaseSplit ω).1 (i + 1) =
      (RandomWalk.phaseSplit ν).1 (i + 1)
    rw [phaseSplit_fst_congr_of_succ_eq ω ν h]
  funext i
  change pitmanCode (rPhaseCodeSequence ω) i =
    pitmanCode (rPhaseCodeSequence ν) i
  rw [hphase]

/-- The R-phase code sequence used by `cutWindowRPhaseCodes` is exactly the
`rCodeSequence` of the shifted stage-code trajectory. The equality uses the
positive-index convention of `codeShift` and
`quadrantTrajectoryOfStageCodes` (`eqn-bdy-vertex-hit`,
`lem-infty-cut`, lines 127–143). This is a composition helper for P1, not a
proof of `lem-quad-kmsw`. -/
theorem cutWindowRPhaseCodes_eq_shiftedStageCodes
    (ω : ℕ → Fin 3) (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (K : ℕ) :
    cutWindowRPhaseCodes ω h K =
      rCodeSequence (quadrantTrajectoryOfStageCodes
        (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h (-(K : ℤ)) + i + 1))) := by
  let τ := boundaryHitTime (fun i => ω (i + 1)) h (-(K : ℤ))
  apply rCodeSequence_eq_of_succ_eq
  intro i
  simp [RandomWalk.codeShift, quadrantTrajectoryOfStageCodes, Nat.add_assoc]

private theorem ae_comp_codeShift {p : (ℕ → Fin 3) → Prop} (n : ℕ)
    (h : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p (RandomWalk.codeShift n ω) := by
  have hp : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure.map (RandomWalk.codeShift n), p ω := by
    simpa only [RandomWalk.map_codeShift] using h
  exact (Measure.tendsto_ae_map
    (RandomWalk.measurable_codeShift n).aemeasurable).eventually hp

/-- Almost surely, every deterministic future stage-code sequence has the
two flow-line hit properties. For each time this is shift invariance of the
iid code measure applied to `ae_hasFlowLineHits`, followed by the countable
intersection over times (`lem-directed-contain`,
This is a composition helper for P1, not a proof of `lem-quad-kmsw`. -/
theorem iidCodes_ae_hasFlowLineHits_all_future_times :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, ∀ t : ℕ,
      HasFlowLineHits (fun i => ω (t + i + 1)) := by
  rw [ae_all_iff]
  intro t
  have ht := ae_comp_codeShift t ae_hasFlowLineHits
  filter_upwards [ht] with ω hω
  simpa [RandomWalk.codeShift, Nat.add_assoc] using hω

/-- Almost surely, every left-hit-shifted future sequence in a finite window
has `HasFlowLineHits`, simultaneously for every window size and every
boundary-hit witness. This specializes
`iidCodes_ae_hasFlowLineHits_all_future_times` at the random time from
composition helper for P1 in `lem-infty-cut` (lines 127–143); it does not
prove `lem-quad-kmsw`. -/
theorem iidCodes_ae_hasFlowLineHits_at_all_boundary_leftHits :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ K : ℕ,
        HasFlowLineHits
          (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h
            (-(K : ℤ)) + i + 1)) := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times] with ω hω
  intro h K
  exact hω (boundaryHitTime (fun j => ω (j + 1)) h (-(K : ℤ)))

end DirectedDistances.KMSW
