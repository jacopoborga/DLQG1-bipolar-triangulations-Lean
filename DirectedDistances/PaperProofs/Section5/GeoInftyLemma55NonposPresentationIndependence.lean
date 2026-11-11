/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSide
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSide

/-! The theorem proves independence of the two decoded code presentations. The
geometric submap claim additionally needs the four side marked isomorphisms
and a measurable class space; it is not claimed here. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.5: the decoded nonpositive left and right code
presentations are independent. This is presentation-level independence only;
the geometric claim needs the four side marked isomorphisms and a measurable
class space, and is not asserted here. -/
theorem lemma55_nonpos_presentation_indepFun (x : XDP) (k : ℤ) :
    IndepFun
      (fun W => decodeLMinus x k (leftSideObsNonpos x k W))
      (fun W => decodeRMinus x k (rightSideObsNonpos x k W))
      wholePlaneIIDCodeMeasure := by
  exact (leftSideObsNonpos_indep_rightSideObsNonpos x k).comp
    (φ := decodeLMinus x k) (ψ := decodeRMinus x k)
    (measurable_decodeLMinus x k) (measurable_decodeRMinus x k)










end DirectedDistances.PaperProofs.Section5
