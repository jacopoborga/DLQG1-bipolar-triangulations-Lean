module

public import DirectedDistances.Recursive.BusemannWindowLimit
public import DirectedDistances.Recursive.BusemannPositiveHalfLaw
public import DirectedDistances.Recursive.BusemannWindowLimitSDP
public import DirectedDistances.Recursive.BusemannPositiveHalfLawSDP
public import DirectedDistances.Recursive.BusemannWholeLineLawConditional
public import DirectedDistances.Recursive.HLRLdpFinal
public import DirectedDistances.Recursive.HLRSdpFinal

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology






theorem ldp_busemann_window_tendsto_of_sym
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => ldpBusemannWindowLaw n hT) atTop (𝓝 ν) ∧
      ∃ S : Set (J1Window T), Sᶜ.Countable ∧
        (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ S ∧
        ∀ (m : ℕ) (t : ℕ → J1Window T), (t 0 : ℝ) = 0 → Monotone t →
          (∀ i : Fin m, t (i.val + 1) ∈ S) →
          let a : ℝ :=
            ((3 + ldpF iidCodeMeasure busemannLDPMeasurableVersion 0) / 2) ^
              (1 / 3 : ℝ)
          let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
          0 < a ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
            (∀ θ : EuclideanSpace ℝ (Fin m),
              charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
                (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
                  ((if 0 ≤ θ i then κ else star κ) *
                    (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
            ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
              (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  exact ldp_busemann_window_tendsto ldpIncrements_iIndep_proved hsym hT






theorem ldpBusemannPositiveHalfLaw_tendsto_of_sym
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
        iidCodeMeasure.map
          (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto ldpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) =
        ldpBusemannPositiveCutoffLimit ldpIncrements_iIndep_proved hsym N := by
  exact ldpBusemannPositiveHalfLaw_tendsto ldpIncrements_iIndep_proved hsym






theorem sdp_busemann_window_tendsto_of_sym
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
        iidCodeMeasure.map
          (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => sdpBusemannWindowLaw n hT) atTop (𝓝 ν) ∧
      ∃ S : Set (J1Window T), Sᶜ.Countable ∧
        (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ S ∧
        ∀ (m : ℕ) (t : ℕ → J1Window T), (t 0 : ℝ) = 0 → Monotone t →
          (∀ i : Fin m, t (i.val + 1) ∈ S) →
          let b : ℝ :=
            (SDPMasterFromLaw.sdpG iidCodeMeasure
              busemannSDPMeasurableVersion (-1)) ^ (2 / 3 : ℝ)
          let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
          0 < b ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
            (∀ θ : EuclideanSpace ℝ (Fin m),
              charFun (L : Measure _) θ = ∏ i : Fin m, Complex.exp
                (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
                  ((if 0 ≤ θ i then κ else star κ) *
                    (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
            ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
              (L.map (cumulativeSum (k := m))).map WithLp.ofLp := by
  exact sdp_busemann_window_tendsto sdpIncrements_iIndep_proved hsym hT






theorem sdpBusemannPositiveHalfLaw_tendsto_of_sym
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
        iidCodeMeasure.map
          (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto sdpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) =
        sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved hsym N := by
  exact sdpBusemannPositiveHalfLaw_tendsto sdpIncrements_iIndep_proved hsym





theorem ldpBusemannWholeLineHalfPaths_indep_of_sym (n : ℕ) :
    IndepFun (fun ω => ldpBusemannWholeLinePositiveHalf n ω)
      (fun ω => ldpBusemannWholeLineNegativeHalf n ω) iidCodeMeasure :=
  ldpBusemannWholeLineHalfPaths_indep n ldpIncrements_iIndep_proved

end DirectedDistances.Recursive
