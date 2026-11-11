/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftReader
public import DirectedDistances.PaperProofs.Section5.GeoInftySideReader

/-! The theorem below proves independence of the two decoded nonnegative-layout
presentations. It does not assert independence of the geometric submaps in
Lemma 5.5. That transfer still needs the four side marked isomorphisms and a
measurable class space for geometric sides. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: decoding the independent nonnegative-layout
observations preserves independence at every integer index. This is a
presentation-level statement only; geometric submap independence requires
the four side marked isomorphisms and a measurable class space. -/
theorem lemma55_nonneg_presentation_indepFun (x : XDP) (k : ℤ) :
    IndepFun
      (fun W => decodeLPlus x k (leftSideObsNonneg x k W))
      (fun W => decodeRPlus x k (rightSideObsNonneg x k W))
      wholePlaneIIDCodeMeasure := by
  exact (leftSideObsNonneg_indep_rightSideObsNonneg x k).comp
    (φ := decodeLPlus x k) (ψ := decodeRPlus x k)
    (measurable_decodeLPlus x k) (measurable_decodeRPlus x k)












end DirectedDistances.PaperProofs.Section5
