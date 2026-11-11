/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section6.IncrementLawsIdentified

public section
namespace DirectedDistances.PaperProofs.Section6

open MeasureTheory Filter Asymptotics
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open scoped Topology

section LDP

local notation "f" => incrementLawsIdentified_ldpF
local notation "g" => incrementLawsIdentified_ldpG

private theorem section6Pinned_ldp_pinning :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (identifiedLDPBusemann W)) := by
  filter_upwards [thm_busemann_paper,
    identifiedLDPBusemann_characterization_ae] with W hW hc
  obtain ⟨H, h, hLL, _⟩ := hW
  exact ⟨H, h, hLL, hc H h hLL⟩

private theorem section6Pinned_ldp_pmf :
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, 0 ≤ k → g k = 0) := by
  rw [incrementLawsIdentified_ldpF_eq, incrementLawsIdentified_ldpG_eq]
  exact ⟨busemann_ldpF_nonneg, busemann_ldpF_hasSum_one,
    busemann_ldpG_nonneg, busemann_ldpG_hasSum_one, busemann_ldpG_zero_of_nonneg⟩

/-- Helper toward prop:asympt-exp2 (recursive.tex) on the identified Busemann increments,
with pinning and pmf conjuncts (Team w387); not a paper result. -/
theorem section6_ldp_asympt_exp2_pinned :
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
  obtain ⟨hf, hfs, hg, hgs, hsupp⟩ := section6Pinned_ldp_pmf
  exact ⟨section6Pinned_ldp_pinning, hf, hfs, hg, hgs, hsupp,
    incrementLawsIdentified_ldp_expansions⟩

/-- Helper toward prop:LDP-recursive-equation (recursive.tex) on the identified Busemann increments,
with pinning and pmf conjuncts (Team w387); not a paper result. -/
theorem section6_ldp_recursive_equation_pinned :
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
  obtain ⟨hf, hfs, hg, hgs, hsupp⟩ := section6Pinned_ldp_pmf
  exact ⟨section6Pinned_ldp_pinning, hf, hfs, hg, hgs, hsupp,
    incrementLawsIdentified_ldp_recursive_equation⟩

/-- Helper toward lem:Y-not-const (recursive.tex) on the identified Busemann increments,
with pinning and pmf conjuncts (Team w387); not a paper result. -/
theorem section6_ldp_y_not_const_pinned :
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
  obtain ⟨hf, hfs, hg, hgs, hsupp⟩ := section6Pinned_ldp_pmf
  exact ⟨section6Pinned_ldp_pinning, hf, hfs, hg, hgs, hsupp,
    incrementLawsIdentified_ldp_nondegenerate⟩

end LDP

section SDP

open DirectedDistances.Recursive.SDPExpansion

local notation "f" => incrementLawsIdentified_sdpF
local notation "g" => incrementLawsIdentified_sdpG

private theorem section6Pinned_sdp_pinning :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W)) := by
  filter_upwards [thm_busemann_paper,
    identifiedSDPBusemann_characterization_ae] with W hW hc
  obtain ⟨H, h, hLL, _⟩ := hW
  exact ⟨H, h, hLL, hc H h hLL⟩

private theorem section6Pinned_sdp_pmf :
    (∀ k : ℤ, 0 ≤ f k) ∧ HasSum f 1 ∧
    (∀ k : ℤ, 0 ≤ g k) ∧ HasSum g 1 ∧
    (∀ k : ℤ, k < -1 → g k = 0) := by
  rw [incrementLawsIdentified_sdpF_eq, incrementLawsIdentified_sdpG_eq]
  exact ⟨busemann_sdpF_nonneg, busemann_sdpF_hasSum_one,
    busemann_sdpG_nonneg, busemann_sdpG_hasSum_one, busemann_sdpG_zero_below⟩

/-- Helper toward prop:asympt-exp (recursive.tex) on the identified Busemann increments,
with pinning and pmf conjuncts (Team w387); not a paper result. -/
theorem section6_sdp_asympt_exp_pinned :
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
  obtain ⟨hf, hfs, hg, hgs, hsupp⟩ := section6Pinned_sdp_pmf
  exact ⟨section6Pinned_sdp_pinning, hf, hfs, hg, hgs, hsupp,
    incrementLawsIdentified_sdp_expansions⟩

/-- Helper toward prop:SDP-recursive-equation (recursive.tex) on the identified Busemann increments,
with pinning and pmf conjuncts (Team w387); not a paper result. -/
theorem section6_sdp_recursive_equation_pinned :
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
  obtain ⟨hf, hfs, hg, hgs, hsupp⟩ := section6Pinned_sdp_pmf
  exact ⟨section6Pinned_sdp_pinning, hf, hfs, hg, hgs, hsupp,
    incrementLawsIdentified_sdp_recursive_equation⟩

/-- Helper toward lem:Y-not-const2 (recursive.tex) on the identified Busemann increments,
with pinning and pmf conjuncts (Team w387); not a paper result. -/
theorem section6_sdp_y_not_const2_pinned :
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
  obtain ⟨hf, hfs, hg, hgs, hsupp⟩ := section6Pinned_sdp_pmf
  exact ⟨section6Pinned_sdp_pinning, hf, hfs, hg, hgs, hsupp,
    incrementLawsIdentified_sdp_nondegenerate⟩

end SDP

end DirectedDistances.PaperProofs.Section6
