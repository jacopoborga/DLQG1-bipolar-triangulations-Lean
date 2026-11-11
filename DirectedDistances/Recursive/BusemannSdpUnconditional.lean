module

public import DirectedDistances.Recursive.BusemannItemsSymOnly
public import DirectedDistances.Recursive.BusemannWindowLimitsSymOnly
public import DirectedDistances.Recursive.BusemannWholeLineLimitSdp
public import DirectedDistances.Recursive.ItemSymmetryBridge
public import DirectedDistances.Recursive.HLRSdpFinal
public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableCloseSdp3

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.Recursive.SDPExpansion
open scoped ENNReal Topology

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem hsymSdp_sdpCode :
    iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω) :=
  hsymSdp_unconditional

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdp_nonpositive_increment_symmetry_sdpCode :
    ∀ k ≤ 0, iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω) :=
  sdp_nonpositive_increment_symmetry hsymSdp_unconditional

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem hLR_sdp_sdpCode :
    IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure :=
  hLR_sdp_proved

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdpIncrements_iIndep_sdpCode :
    iIndepFun
      (fun k ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω)
      iidCodeMeasure :=
  sdpIncrements_iIndep_proved

section SDP

local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem busemann_tail_sdp_sdpCode :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ ((Y ω 1 - Y ω 0 : ℤ) : ℝ)} -
        c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₂ * x ^ (-(4 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) :=
  busemann_tail_sdp_of_sym hsymSdp_unconditional

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem busemann_sdp_increment_mean_zero_sdpCode :
    ∀ k : ℤ,
      Integrable (fun ω => ((Y ω k - Y ω (k - 1) : ℤ) : ℝ)) iidCodeMeasure ∧
        (∫ ω, ((Y ω k - Y ω (k - 1) : ℤ) : ℝ) ∂iidCodeMeasure) = 0 :=
  busemann_sdp_increment_mean_zero_of_sym hsymSdp_unconditional

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdp_master_equation_sdpCode :
    ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
          g j * g (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2},
              f j * f (x - (j : ℤ) - 1)) +
              g (-1) ^ 2 * f (x + 1) + g (x - 1)
           else 0) :=
  sdp_master_equation_of_sym hsymSdp_unconditional

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdp_hgeo_sdpCode :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤
        (Measure.infinitePi (fun _ : ℕ => mu_f
          (KappaHgeoTransfer.incrementMass iidCodeMeasure
            busemannSDPMeasurableVersion))).real
          {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1} :=
  sdp_hgeo_of_sym hsymSdp_unconditional

end SDP

section ExplicitTails

local notation "Y" => busemannSDPMeasurableVersion
local notation "f" => SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion
local notation "g" => SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdp_tail_asymptotics_explicit_sdpCode :
    let κ : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    κ = 0 ∧
      (fun R : ℝ =>
        (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
          (Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
            (Real.sqrt 3 * Real.pi)) * R ^ (-(4 / 3 : ℝ)))
        =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) ∧
      (fun R : ℝ =>
        (∑' y : ℤ, if R < (y : ℝ) then g y else 0) -
          (Real.Gamma (1 / 3 : ℝ) * (g (-1)) ^ (2 / 3 : ℝ) /
            (2 * Real.sqrt 3 * Real.pi)) * R ^ (-(4 / 3 : ℝ)))
        =o[atTop] (fun R : ℝ => R ^ (-(4 / 3 : ℝ))) :=
  sdp_tail_asymptotics_explicit_of_sym hsymSdp_unconditional

end ExplicitTails

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdp_busemann_window_tendsto_sdpCode
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
  exact sdp_busemann_window_tendsto_of_sym hsymSdp_unconditional hT

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdpBusemannPositiveHalfLaw_tendsto_sdpCode :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto sdpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) =
        sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved
          hsymSdp_unconditional N := by
  exact sdpBusemannPositiveHalfLaw_tendsto_of_sym hsymSdp_unconditional

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdpBusemannWholeLinePositiveHalfLaw_tendsto_sdpCode :
    ∃ μ : ProbabilityMeasure CadlagLocalZero,
      Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ) ∧
      ∀ N, (ProbabilityMeasure.map μ
        (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) =
          sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved
            hsymSdp_unconditional N := by
  exact sdpBusemannWholeLinePositiveHalfLaw_tendsto_of_sym hsymSdp_unconditional

/-- Helper (code level, SDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem sdpBusemannWholeLineLaw_tendsto_sdpCode :
    ∃ (μpos μneg : ProbabilityMeasure CadlagLocalZero),
      Tendsto sdpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μpos) ∧
      (∀ N, (ProbabilityMeasure.map μpos
        (Subtype.val : CadlagLocalZero → CadlagLocal)).map
          (finiteCutoffWindows N) =
            sdpBusemannPositiveCutoffLimit sdpIncrements_iIndep_proved
              hsymSdp_unconditional N) ∧
      SdpBusemannWholeLineNegativeHalfConverges μneg ∧
      (∀ N, (μneg.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) = negativeHalfSdpCutoffLimit hsymSdp_unconditional N) ∧
      Tendsto sdpBusemannWholeLineLaw atTop
        (𝓝 ((probabilityProduct μpos μneg).map wholeLineGlueZero)) := by
  exact sdpBusemannWholeLineLaw_tendsto_of_sym hsymSdp_unconditional

end DirectedDistances.Recursive
