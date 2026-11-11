/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section6.Section6Pinned
public import DirectedDistances.PaperProofs.Section6.NonrealIdentified

/-! # Isolated proof providers for the Section 6 law statements

The laws concern the identified Busemann increments.
Packaging only; installation, sealing and counting are separate gates.


Reading (Team w387): f and g are the laws of the pinned identified Busemann increments
under `RandomWalk.wholePlaneIIDCodeMeasure`: the left increment X(0) - X(-1) for f
and the right increment X(1) - X(0) for g, as in eq:den-dist-f-g.
The pinning and pmf conjuncts are included; the LDP g law is supported on negative integers.
The nonreal statement includes the full LDP and SDP root and continuous-branch clauses. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory Filter Asymptotics
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open DirectedDistances.PaperProofs.Section6
open scoped Topology

section LDP

local notation "f" => incrementLawsIdentified_ldpF
local notation "g" => incrementLawsIdentified_ldpG

/-- prop:asympt-exp2 isolated provider (recursive.tex label prop:asympt-exp2);
packaging only. -/
theorem prop_asympt_exp2_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (identifiedLDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, 0 ≤ k → g k = 0) ∧
    (let kappa : ℝ := 3 + f 0
    let a : ℝ := (kappa / 2) ^ (1 / 3 : ℝ)
    let d : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
    0 < kappa ∧
      ((fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) ∧
      ((fun t : ℝ => negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) -
        (d * (a : ℂ)) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ))) ∧
      ((fun t : ℝ => negativeCF g t - 1 -
        (d * (a : ℂ)) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)))) := by
  exact DirectedDistances.PaperProofs.Section6.section6_ldp_asympt_exp2_pinned

/-- prop:LDP-recursive-equation isolated provider (recursive.tex label prop:LDP-recursive-equation);
packaging only. -/
theorem prop_ldp_recursive_equation_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (identifiedLDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, 0 ≤ k → g k = 0) ∧
    (∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
          f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
          (if y = -1 then
            (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
           else 0)) := by
  exact DirectedDistances.PaperProofs.Section6.section6_ldp_recursive_equation_pinned

/-- lem:Y-not-const isolated provider (recursive.tex label lem:Y-not-const);
packaging only. -/
theorem lem_y_not_const_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (identifiedLDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, 0 ≤ k → g k = 0) ∧
    ((∀ c : ℤ, f c < 1) ∧ 0 < f 0) := by
  exact DirectedDistances.PaperProofs.Section6.section6_ldp_y_not_const_pinned

local notation "hat" =>
  SDPExpansion.sdpHat incrementLawsIdentified_sdpF incrementLawsIdentified_sdpG
local notation "cf" => SDPExpansion.integerCF incrementLawsIdentified_sdpF

/-- lem:nonreal2 isolated provider (recursive.tex label lem:nonreal2);
packaging only. -/
theorem lem_nonreal2_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (identifiedLDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, 0 ≤ k → g k = 0) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ incrementLawsIdentified_sdpF k) ∧
    HasSum incrementLawsIdentified_sdpF 1 ∧
    (∀ k : ℤ, 0 ≤ incrementLawsIdentified_sdpG k) ∧
    HasSum incrementLawsIdentified_sdpG 1 ∧
    (∀ k : ℤ, k < -1 → incrementLawsIdentified_sdpG k = 0) ∧
    (∃ delta : ℝ, 0 < delta ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (integerCF incrementLawsIdentified_ldpF t).re
         (integerCF incrementLawsIdentified_ldpF t).im = 0 ∧
         (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0 ∧
           ∀ z : ℂ, (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + F = 0 →
             z.im ≠ 0) ∧
       ContinuousOn (ldpHat incrementLawsIdentified_ldpF) (Set.Ioo 0 delta) ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (integerCF incrementLawsIdentified_ldpF t).re
         (F : ℂ) ^ 2 * (ldpHat incrementLawsIdentified_ldpF t) ^ 2 +
           (3 * (F : ℂ) - 1) * ldpHat incrementLawsIdentified_ldpF t + F = 0) ∧
       (∀ t ∈ Set.Ioo 0 delta, (ldpHat incrementLawsIdentified_ldpF t).im ≠ 0) ∧
       (∀ alpha beta : ℝ → ℝ,
         ContinuousOn alpha (Set.Ioo 0 delta) → ContinuousOn beta (Set.Ioo 0 delta) →
         (∀ s ∈ Set.Ioo 0 delta,
           let F := (integerCF incrementLawsIdentified_ldpF s).re
           (F : ℂ) ^ 2 * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) ^ 2 +
             (3 * (F : ℂ) - 1) * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) + F = 0) →
         ∀ s ∈ Set.Ioo 0 delta, beta s ≠ 0)) ∧
    (∃ delta : ℝ, 0 < delta ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (cf t).re
         (cf t).im = 0 ∧
         (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0 ∧
           ∀ z : ℂ, (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + F = 0 →
             z.im ≠ 0) ∧
       ContinuousOn hat (Set.Ioo 0 delta) ∧
       (∀ t ∈ Set.Ioo 0 delta,
         let F := (cf t).re
         (F : ℂ) ^ 2 * (hat t) ^ 2 + (3 * (F : ℂ) - 1) * hat t + F = 0) ∧
       (∀ t ∈ Set.Ioo 0 delta, (hat t).im ≠ 0) ∧
       (∀ alpha beta : ℝ → ℝ,
         ContinuousOn alpha (Set.Ioo 0 delta) → ContinuousOn beta (Set.Ioo 0 delta) →
         (∀ s ∈ Set.Ioo 0 delta,
           let F := (cf s).re
           (F : ℂ) ^ 2 * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) ^ 2 +
             (3 * (F : ℂ) - 1) * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) + F = 0) →
         ∀ s ∈ Set.Ioo 0 delta, beta s ≠ 0)) := by
  obtain ⟨hpin, hf, hfs, hg, hgs, hsupp, _⟩ :=
    DirectedDistances.PaperProofs.Section6.section6_ldp_y_not_const_pinned
  obtain ⟨hpinSDP, hfSDP, hfsSDP, hgSDP, hgsSDP, hsuppSDP, _⟩ :=
    DirectedDistances.PaperProofs.Section6.section6_sdp_y_not_const2_pinned
  exact ⟨hpin, hf, hfs, hg, hgs, hsupp,
    hpinSDP, hfSDP, hfsSDP, hgSDP, hgsSDP, hsuppSDP,
    DirectedDistances.PaperProofs.Section6.lem_nonreal2_full_identified,
    DirectedDistances.PaperProofs.Section6.nonrealIdentified_sdp_full⟩

end LDP

section SDP

open DirectedDistances.Recursive.SDPExpansion

local notation "f" => incrementLawsIdentified_sdpF
local notation "g" => incrementLawsIdentified_sdpG

/-- prop:asympt-exp isolated provider (recursive.tex label prop:asympt-exp);
packaging only. -/
theorem prop_asympt_exp_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, k < -1 → g k = 0) ∧
    (let kappa : ℝ := 3 - 6 * g (-1) ^ 2 - f 0
    let b : ℝ := g (-1) ^ (2 / 3 : ℝ)
    let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2
    let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2
    kappa = 0 ∧ 0 < g (-1) ∧
      ((fun t : ℝ => SDPExpansion.integerCF f t -
        ((1 : ℂ) - (b : ℂ) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) ∧
      ((fun t : ℝ => SDPExpansion.negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) +
        (((2 * g (-1) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ) -
        (dPlus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ))) ∧
      ((fun t : ℝ => sdpCF g t - 1 -
        (dMinus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ)))) := by
  exact DirectedDistances.PaperProofs.Section6.section6_sdp_asympt_exp_pinned

/-- prop:SDP-recursive-equation isolated provider (recursive.tex label prop:SDP-recursive-equation);
packaging only. -/
theorem prop_sdp_recursive_equation_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, k < -1 → g k = 0) ∧
    (∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
              g (-1) ^ 2 * f (x + 1) + g (x - 1)
           else 0)) := by
  exact DirectedDistances.PaperProofs.Section6.section6_sdp_recursive_equation_pinned

/-- lem:Y-not-const2 isolated provider (recursive.tex label lem:Y-not-const2);
packaging only. -/
theorem lem_y_not_const2_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W)) ∧
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, k < -1 → g k = 0) ∧
    ((∀ c : ℤ, f c < 1) ∧ 0 < f 0 ∧ 0 < g (-1)) := by
  exact DirectedDistances.PaperProofs.Section6.section6_sdp_y_not_const2_pinned

end SDP

end DirectedDistances.PaperProofs.SourceResults
