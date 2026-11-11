module

public import DirectedDistances.Recursive.BusemannItemsSymOnly
public import DirectedDistances.Recursive.BusemannWindowLimitsSymOnly
public import DirectedDistances.Recursive.BusemannWholeLineLdpOfSym
public import DirectedDistances.Recursive.ItemSymmetryBridge
public import DirectedDistances.Recursive.HLRLdpFinal
public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementReflectLdp
import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableClose4

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.RandomWalk DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.Recursive.SDPExpansion
open scoped ENNReal Topology

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem hsymLdp_ldpCode :
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) :=
  hsym_ldp_of_facedShellTransport incrementClose4_facedShellTransport

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldp_nonpositive_increment_symmetry_ldpCode :
    ∀ k ≤ 0, iidCodeMeasure.map
        (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map
        (fun ω => -ldpIncrement busemannLDPMeasurableVersion k ω) :=
  ldp_nonpositive_increment_symmetry hsymLdp_ldpCode

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem hLR_ldpCode :
    IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure :=
  hLR_ldp_proved

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldpIncrements_iIndep_ldpCode :
    iIndepFun (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure :=
  ldpIncrements_iIndep_proved

section LDP

local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF iidCodeMeasure busemannLDPMeasurableVersion
local notation "g" => ldpG iidCodeMeasure busemannLDPMeasurableVersion

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem busemann_tail_ldp_ldpCode :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | ((Y ω 1 - Y ω 0 : ℤ) : ℝ) ≤ -x} -
        c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => iidCodeMeasure.real {ω | x ≤ |((Y ω 0 - Y ω (-1) : ℤ) : ℝ)|} -
        2 * c₁ * x ^ (-(2 / 3 : ℝ))) =o[atTop]
          (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) :=
  busemann_tail_ldp_of_sym hsymLdp_ldpCode

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldp_master_equation_ldpCode :
    ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
          f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
          (if y = -1 then
            (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
           else 0) :=
  ldp_master_equation_of_sym hsymLdp_ldpCode

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldp_fluctuation_ldpCode :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        iidCodeMeasure.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} :=
  ldp_fluctuation_of_sym hsymLdp_ldpCode

end LDP

section ExplicitLDP

local notation "Y" => busemannLDPMeasurableVersion
local notation "f" => ldpF iidCodeMeasure busemannLDPMeasurableVersion
local notation "g" => ldpG iidCodeMeasure busemannLDPMeasurableVersion

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldp_tail_asymptotics_explicit_ldpCode :
    let κ : ℝ := 3 + f 0
    ((fun R : ℝ =>
      (∑' x : ℤ, if R < |(x : ℝ)| then f x else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / Real.pi) *
          (κ / 2) ^ (1 / 3 : ℝ) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ))) ∧
    (fun R : ℝ =>
      (∑' y : ℤ, if (y : ℝ) < -R then g y else 0) -
        (Real.sqrt 3 * Real.Gamma (2 / 3 : ℝ) / (2 * Real.pi)) *
          (κ / 2) ^ (1 / 3 : ℝ) * R ^ (-(2 / 3 : ℝ)))
      =o[atTop] (fun R : ℝ => R ^ (-(2 / 3 : ℝ)))) :=
  ldp_tail_asymptotics_explicit_of_sym hsymLdp_ldpCode

end ExplicitLDP

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldp_busemann_window_tendsto_ldpCode
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
  exact ldp_busemann_window_tendsto_of_sym hsymLdp_ldpCode hT

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldpBusemannPositiveHalfLaw_tendsto_ldpCode :
    ∃ ν : ProbabilityMeasure CadlagLocal,
      Tendsto ldpBusemannPositiveHalfLaw atTop (𝓝 ν) ∧
      ∀ N, ν.map (finiteCutoffWindows N) =
        ldpBusemannPositiveCutoffLimit ldpIncrements_iIndep_proved
          hsymLdp_ldpCode N := by
  exact ldpBusemannPositiveHalfLaw_tendsto_of_sym hsymLdp_ldpCode

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldpBusemannWholeLineHalfPaths_indep_ldpCode (n : ℕ) :
    IndepFun (fun ω => ldpBusemannWholeLinePositiveHalf n ω)
      (fun ω => ldpBusemannWholeLineNegativeHalf n ω) iidCodeMeasure :=
  ldpBusemannWholeLineHalfPaths_indep_of_sym n

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldpBusemannWholeLinePositiveHalfLaw_tendsto_ldpCode :
    ∃ μ : ProbabilityMeasure CadlagLocalZero,
      Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μ) ∧
      ∀ N, (ProbabilityMeasure.map μ
        (Subtype.val : CadlagLocalZero → CadlagLocal)).map
          (finiteCutoffWindows N) =
            ldpBusemannPositiveCutoffLimit ldpIncrements_iIndep_proved
              hsymLdp_ldpCode N := by
  exact ldpBusemannWholeLinePositiveHalfLaw_tendsto_of_sym hsymLdp_ldpCode

/-- Helper (code level, LDP) toward Theorem 1.6/1.7; not a paper result: the
paper-facing statement still needs the Q-M0-repr binding of M_{0,∞}. -/
theorem ldpBusemannWholeLineLaw_tendsto_ldpCode :
    ∃ (μpos μneg : ProbabilityMeasure CadlagLocalZero),
      Tendsto ldpBusemannWholeLinePositiveHalfLaw atTop (𝓝 μpos) ∧
      (∀ N, (ProbabilityMeasure.map μpos
        (Subtype.val : CadlagLocalZero → CadlagLocal)).map
          (finiteCutoffWindows N) =
            ldpBusemannPositiveCutoffLimit ldpIncrements_iIndep_proved
              hsymLdp_ldpCode N) ∧
      LdpBusemannWholeLineNegativeHalfConverges μneg ∧
      (∀ N, (μneg.map (Subtype.val : CadlagLocalZero → CadlagLocal)).map
        (finiteCutoffWindows N) = negativeHalfLdpCutoffLimit hsymLdp_ldpCode N) ∧
      Tendsto ldpBusemannWholeLineLaw atTop
        (𝓝 ((probabilityProduct μpos μneg).map wholeLineGlueZero)) := by
  exact ldpBusemannWholeLineLaw_tendsto_of_sym hsymLdp_ldpCode

end DirectedDistances.Recursive
