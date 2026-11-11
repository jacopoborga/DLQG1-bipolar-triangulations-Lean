/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.FutureCodesAtHits
public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.Recursive.LDPMasterFromLaw
public import DirectedDistances.Recursive.SDPMasterFromLaw
public import DirectedDistances.Recursive.MeasurableVersionPos
public import DirectedDistances.Recursive.BusemannSDPMeasurable

/-! # Conditional left stationarity and process laws

These are CONDITIONAL generic helpers for item `stationary` of
first-hit shift identities are explicit hypotheses and are not discharged
here; the increment identities belong in `LeftStationaryBusemann`, and the
process identities belong in their respective process files. These helpers
are not counted as paper results. The F1/F4 source-identification caveats
remain in force. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk

/-- CONDITIONAL generic left-increment law helper for item
first-hit shift identity is an explicit hypothesis to be discharged in
`LeftStationaryBusemann`; it is not proved here. This helper is not counted
as a paper result, and the F1/F4 source-identification caveats remain. -/
theorem left_increment_law_of_shift_identity
    {V : (ℕ → Fin 3) → ℤ → ℤ}
    (hY : ∀ k : ℤ, Measurable (fun ω => V ω k))
    (h0 : ∀ ω, V ω 0 = 0)
    (hshift : ∀ k : ℤ, k ≤ -1 →
      ∀ᵐ ω ∂iidCodeMeasure,
        V (codeShift (codeFstFirstHit k ω).toNat ω) (-1) =
          V ω (k - 1) - V ω k) :
    ∀ k : ℤ, k ≤ 0 →
      iidCodeMeasure.map (fun ω => V ω k - V ω (k - 1)) =
        iidCodeMeasure.map (fun ω => V ω 0 - V ω (-1)) := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    rfl
  · have hkneg : k ≤ -1 := by omega
    have hshiftk := hshift k hkneg
    have hAE :
        (fun ω => V ω k - V ω (k - 1)) =ᵐ[iidCodeMeasure]
          (fun ω => -(V (codeShift (codeFstFirstHit k ω).toNat ω) (-1))) := by
      filter_upwards [hshiftk] with ω hω
      omega
    have hmapShift := map_comp_codeShift_codeFstFirstHit k
      (F := fun ω => -(V ω (-1)))
      (measurable_neg.comp (hY (-1)))
    have hnorm : (fun ω => -(V ω (-1))) =ᵐ[iidCodeMeasure]
        (fun ω => V ω 0 - V ω (-1)) := by
      filter_upwards [] with ω
      rw [h0 ω, zero_sub]
    calc
      iidCodeMeasure.map (fun ω => V ω k - V ω (k - 1)) =
          iidCodeMeasure.map
            (fun ω => -(V (codeShift (codeFstFirstHit k ω).toNat ω) (-1))) :=
        Measure.map_congr hAE
      _ = iidCodeMeasure.map (fun ω => -(V ω (-1))) := hmapShift
      _ = iidCodeMeasure.map (fun ω => V ω 0 - V ω (-1)) :=
        Measure.map_congr hnorm

/-- CONDITIONAL LDP instance of
`left_increment_law_of_shift_identity`, in the exact `hstatL` form used by
`BusemannTailReducedItems`. Its first-hit shift identity remains an explicit
hypothesis to be discharged in `LeftStationaryBusemann`. This helper is not
counted as a paper result; the F1/F4 caveats remain. -/
theorem busemannLDPMeasurableVersion_left_increment_law_of_shift_identity
    (hshift : ∀ k : ℤ, k ≤ -1 →
      ∀ᵐ ω ∂iidCodeMeasure,
        busemannLDPMeasurableVersion
            (codeShift (codeFstFirstHit k ω).toNat ω) (-1) =
          busemannLDPMeasurableVersion ω (k - 1) -
            busemannLDPMeasurableVersion ω k) :
    ∀ k ≤ 0,
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
        iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) := by
  intro k hk
  change iidCodeMeasure.map
      (fun ω => busemannLDPMeasurableVersion ω k -
        busemannLDPMeasurableVersion ω (k - 1)) =
    iidCodeMeasure.map
      (fun ω => busemannLDPMeasurableVersion ω 0 -
        busemannLDPMeasurableVersion ω (0 - 1))
  exact left_increment_law_of_shift_identity
    measurable_busemannLDPMeasurableVersion busemannLDPMeasurableVersion_zero
    hshift k hk

/-- CONDITIONAL SDP instance of
`left_increment_law_of_shift_identity`, in the exact `hstatL` form used by
`BusemannTailReducedItems`. Its first-hit shift identity remains an explicit
hypothesis to be discharged in `LeftStationaryBusemann`. This helper is not
counted as a paper result; the F1/F4 caveats remain. -/
theorem busemannSDPMeasurableVersion_left_increment_law_of_shift_identity
    (hshift : ∀ k : ℤ, k ≤ -1 →
      ∀ᵐ ω ∂iidCodeMeasure,
        busemannSDPMeasurableVersion
            (codeShift (codeFstFirstHit k ω).toNat ω) (-1) =
          busemannSDPMeasurableVersion ω (k - 1) -
            busemannSDPMeasurableVersion ω k) :
    ∀ k ≤ 0,
      iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k) =
        iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) := by
  intro k hk
  change iidCodeMeasure.map
      (fun ω => busemannSDPMeasurableVersion ω k -
        busemannSDPMeasurableVersion ω (k - 1)) =
    iidCodeMeasure.map
      (fun ω => busemannSDPMeasurableVersion ω 0 -
        busemannSDPMeasurableVersion ω (0 - 1))
  exact left_increment_law_of_shift_identity
    measurable_busemannSDPMeasurableVersion busemannSDPMeasurableVersion_zero
    hshift k hk

/-- CONDITIONAL generic left-process law helper for item
simultaneous first-hit shift identity is an explicit hypothesis to be
discharged in the left-process file. This helper is not counted as a paper
result, and the F1/F4 source-identification caveats remain. -/
theorem left_process_law_of_shift_identity
    {V : (ℕ → Fin 3) → ℤ → ℤ}
    (hY : ∀ k : ℤ, Measurable (fun ω => V ω k))
    (h0 : ∀ ω, V ω 0 = 0)
    (hshift : ∀ k : ℤ, k ≤ -1 →
      ∀ᵐ ω ∂iidCodeMeasure, ∀ j : ℕ,
        V (codeShift (codeFstFirstHit k ω).toNat ω) (-(j : ℤ)) =
          V ω (k - j) - V ω k) :
    ∀ k : ℤ, k ≤ -1 →
      iidCodeMeasure.map (fun ω (j : ℕ) => V ω (k - j) - V ω k) =
        iidCodeMeasure.map (fun ω (j : ℕ) => V ω (-(j : ℤ))) := by
  intro k hk
  have hF : Measurable
      (fun ω (j : ℕ) => V ω (-(j : ℤ)) - V ω 0) :=
    measurable_pi_iff.mpr fun j => (hY (-(j : ℤ))).sub (hY 0)
  have hshiftMap := map_comp_codeShift_codeFstFirstHit k
    (F := fun ω (j : ℕ) => V ω (-(j : ℤ)) - V ω 0) hF
  have hAE :
      (fun ω (j : ℕ) => V ω (k - j) - V ω k) =ᵐ[iidCodeMeasure]
        (fun ω (j : ℕ) =>
          V (codeShift (codeFstFirstHit k ω).toNat ω) (-(j : ℤ)) -
            V (codeShift (codeFstFirstHit k ω).toNat ω) 0) := by
    filter_upwards [hshift k hk] with ω hω
    funext j
    rw [h0 (codeShift (codeFstFirstHit k ω).toNat ω), sub_zero]
    exact (hω j).symm
  have hnorm :
      (fun ω (j : ℕ) => V ω (-(j : ℤ)) - V ω 0) =ᵐ[iidCodeMeasure]
        (fun ω (j : ℕ) => V ω (-(j : ℤ))) := by
    filter_upwards [] with ω
    funext j
    rw [h0 ω, sub_zero]
  calc
    iidCodeMeasure.map (fun ω (j : ℕ) => V ω (k - j) - V ω k) =
        iidCodeMeasure.map
          (fun ω (j : ℕ) =>
            V (codeShift (codeFstFirstHit k ω).toNat ω) (-(j : ℤ)) -
              V (codeShift (codeFstFirstHit k ω).toNat ω) 0) :=
      Measure.map_congr hAE
    _ = iidCodeMeasure.map (fun ω (j : ℕ) => V ω (-(j : ℤ)) - V ω 0) :=
      hshiftMap
    _ = iidCodeMeasure.map (fun ω (j : ℕ) => V ω (-(j : ℤ))) :=
      Measure.map_congr hnorm

/-- CONDITIONAL generic right-process law helper for item
simultaneous second-coordinate first-hit shift identity is an explicit
hypothesis to be discharged in the right-process file. This helper is not
counted as a paper result, and the F1/F4 source-identification caveats remain. -/
theorem right_process_law_of_shift_identity
    {V : (ℕ → Fin 3) → ℤ → ℤ}
    (hY : ∀ k : ℤ, Measurable (fun ω => V ω k))
    (h0 : ∀ ω, V ω 0 = 0)
    (hshift : ∀ k : ℕ, 1 ≤ k →
      ∀ᵐ ω ∂iidCodeMeasure, ∀ j : ℕ,
        V (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) j =
          V ω (k + j) - V ω k) :
    ∀ k : ℕ, 1 ≤ k →
      iidCodeMeasure.map (fun ω (j : ℕ) => V ω (k + j) - V ω k) =
        iidCodeMeasure.map (fun ω (j : ℕ) => V ω j) := by
  intro k hk
  have hF : Measurable (fun ω (j : ℕ) => V ω j - V ω 0) :=
    measurable_pi_iff.mpr fun j => (hY j).sub (hY 0)
  have hshiftMap := map_comp_codeShift_codeSndFirstHit (-(k : ℤ))
    (F := fun ω (j : ℕ) => V ω j - V ω 0) hF
  have hAE :
      (fun ω (j : ℕ) => V ω (k + j) - V ω k) =ᵐ[iidCodeMeasure]
        (fun ω (j : ℕ) =>
          V (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) j -
            V (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 0) := by
    filter_upwards [hshift k hk] with ω hω
    funext j
    rw [h0 (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω), sub_zero]
    exact (hω j).symm
  have hnorm :
      (fun ω (j : ℕ) => V ω j - V ω 0) =ᵐ[iidCodeMeasure]
        (fun ω (j : ℕ) => V ω j) := by
    filter_upwards [] with ω
    funext j
    rw [h0 ω, sub_zero]
  calc
    iidCodeMeasure.map (fun ω (j : ℕ) => V ω (k + j) - V ω k) =
        iidCodeMeasure.map
          (fun ω (j : ℕ) =>
            V (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) j -
              V (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 0) :=
      Measure.map_congr hAE
    _ = iidCodeMeasure.map (fun ω (j : ℕ) => V ω j - V ω 0) := hshiftMap
    _ = iidCodeMeasure.map (fun ω (j : ℕ) => V ω j) := Measure.map_congr hnorm

end DirectedDistances.Recursive

