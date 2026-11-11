/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusDecodedSide6

/-! module records a coordinatewise measurability step for the corrected decoded
left side. It does not claim class-reader measurability or paper completion. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4

/-- Helper toward Lemma 5.5. A fixed exterior boundary edge label is
measurable on the full two-block left-side presentation. This is the raw
label before its presentation-dependent glued-dart encoding. -/
theorem measurable_lMinusCodeExteriorBoundaryEdge_presentation_apply
    (x : XDP) (i : ℕ) :
    Measurable (fun r : LMinusSidePresentation x =>
      lMinusCodeExteriorBoundaryEdge r.code.1 i) := by
  exact (measurable_pi_apply i).comp
    (measurable_lMinusCodeExteriorBoundaryEdge_presentation x)































end DirectedDistances.PaperProofs.Section5
