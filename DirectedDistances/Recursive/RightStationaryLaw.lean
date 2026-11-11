module

public import DirectedDistances.RandomWalk.FutureCodesAtHits
public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.Recursive.LDPMasterFromLaw
public import DirectedDistances.Recursive.SDPMasterFromLaw
public import DirectedDistances.Recursive.MeasurableVersionPos
public import DirectedDistances.Recursive.BusemannSDPMeasurable








public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk







theorem right_increment_law_of_shift_identity
    {V : (ℕ → Fin 3) → ℤ → ℤ}
    (hY : ∀ k : ℤ, Measurable (fun ω => V ω k))
    (h0 : ∀ ω, V ω 0 = 0)
    (hshift : ∀ k : ℕ, 1 ≤ k →
      ∀ᵐ ω ∂iidCodeMeasure,
        V (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 1 =
          V ω ((k : ℤ) + 1) - V ω (k : ℤ)) :
    ∀ k : ℤ, 1 ≤ k →
      iidCodeMeasure.map (fun ω => V ω k - V ω (k - 1)) =
        iidCodeMeasure.map (fun ω => V ω 1 - V ω 0) := by
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    rfl
  · have hk0 : 0 ≤ k := by omega
    have hkNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    have hk2 : 2 ≤ k := by omega
    let j : ℕ := k.toNat - 1
    have hj : 1 ≤ j := by
      dsimp [j]
      omega
    have hj_add : (j : ℤ) + 1 = k := by
      dsimp [j]
      omega
    have hj_sub : (j : ℤ) = k - 1 := by
      dsimp [j]
      omega
    have hshiftj := hshift j hj
    have hAE :
        (fun ω => V (codeShift (codeSndFirstHit (-(j : ℤ)) ω).toNat ω) 1) =ᵐ[iidCodeMeasure]
          (fun ω => V ω k - V ω (k - 1)) := by
      filter_upwards [hshiftj] with ω hω
      calc
        V (codeShift (codeSndFirstHit (-(j : ℤ)) ω).toNat ω) 1 =
            V ω ((j : ℤ) + 1) - V ω (j : ℤ) := hω
        _ = V ω k - V ω (k - 1) := by rw [hj_add, hj_sub]
    have hmapShift := map_comp_codeShift_codeSndFirstHit (-(j : ℤ))
      (F := fun ω => V ω 1) (hY 1)
    have hnorm : (fun ω => V ω 1) =ᵐ[iidCodeMeasure]
        (fun ω => V ω 1 - V ω 0) := by
      filter_upwards [] with ω
      rw [h0 ω, sub_zero]
    calc
      iidCodeMeasure.map (fun ω => V ω k - V ω (k - 1)) =
          iidCodeMeasure.map
            (fun ω => V (codeShift (codeSndFirstHit (-(j : ℤ)) ω).toNat ω) 1) :=
        (Measure.map_congr hAE).symm
      _ = iidCodeMeasure.map (fun ω => V ω 1) := hmapShift
      _ = iidCodeMeasure.map (fun ω => V ω 1 - V ω 0) := Measure.map_congr hnorm

/- CONDITIONAL LDP instance of
`right_increment_law_of_shift_identity`, in the `hstatR` form used by
`LDPRecursiveConditional`. Its shifted/global identity remains an explicit
independence or left-side stationarity. The F1/F4 caveats apply. -/
theorem busemannLDPMeasurableVersion_right_increment_law_of_shift_identity
    (hshift : ∀ k : ℕ, 1 ≤ k →
      ∀ᵐ ω ∂iidCodeMeasure,
        busemannLDPMeasurableVersion
            (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 1 =
          busemannLDPMeasurableVersion ω ((k : ℤ) + 1) -
            busemannLDPMeasurableVersion ω (k : ℤ)) :
    ∀ k ≥ 1, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 1) := by
  intro k hk
  change iidCodeMeasure.map
      (fun ω => busemannLDPMeasurableVersion ω k -
        busemannLDPMeasurableVersion ω (k - 1)) =
    iidCodeMeasure.map
      (fun ω => busemannLDPMeasurableVersion ω 1 -
        busemannLDPMeasurableVersion ω 0)
  exact right_increment_law_of_shift_identity
    measurable_busemannLDPMeasurableVersion busemannLDPMeasurableVersion_zero
    hshift k hk

/- CONDITIONAL SDP instance of
`right_increment_law_of_shift_identity`, in the `hstatR` form used by
`SDPRecursiveConditional`. Its shifted/global identity remains an explicit
independence or left-side stationarity. The F1/F4 caveats apply. -/
theorem busemannSDPMeasurableVersion_right_increment_law_of_shift_identity
    (hshift : ∀ k : ℕ, 1 ≤ k →
      ∀ᵐ ω ∂iidCodeMeasure,
        busemannSDPMeasurableVersion
            (codeShift (codeSndFirstHit (-(k : ℤ)) ω).toNat ω) 1 =
          busemannSDPMeasurableVersion ω ((k : ℤ) + 1) -
            busemannSDPMeasurableVersion ω (k : ℤ)) :
    ∀ k ≥ 1,
      iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k) =
        iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 1) := by
  intro k hk
  change iidCodeMeasure.map
      (fun ω => busemannSDPMeasurableVersion ω k -
        busemannSDPMeasurableVersion ω (k - 1)) =
    iidCodeMeasure.map
      (fun ω => busemannSDPMeasurableVersion ω 1 -
        busemannSDPMeasurableVersion ω 0)
  exact right_increment_law_of_shift_identity
    measurable_busemannSDPMeasurableVersion busemannSDPMeasurableVersion_zero
    hshift k hk

end DirectedDistances.Recursive
