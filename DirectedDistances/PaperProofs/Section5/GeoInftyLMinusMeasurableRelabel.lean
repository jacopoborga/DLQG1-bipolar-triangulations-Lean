/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusDecodedSide7

/-! module isolates the measurable raw exterior dart label. The label is before
the code-dependent quotient encoding used by the complete glued side; this
module does not claim measurability of that side or its class. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory

/-- Helper toward Lemma 5.5. The raw exterior boundary dart code records the
primed-block edge label and its reversed orientation bit, before quotient
identification with the hatted block. -/
@[expose] noncomputable def lMinusRawExteriorBoundaryDartCode
    {x : DirectedDistances.PlanarMap.XDP}
    (r : LMinusSidePresentation x) (i : ℕ) : ℕ × Bool :=
  (lMinusCodeExteriorBoundaryEdge r.code.1 i, true)

/-- Helper toward Lemma 5.5. Each raw exterior boundary dart code is
measurable as a function of the two-block presentation. This is not yet the
geometric `boundary` coordinate, which applies the glued quotient dart ID. -/
theorem measurable_lMinusRawExteriorBoundaryDartCode_presentation_apply
    (x : DirectedDistances.PlanarMap.XDP) (i : ℕ) :
    Measurable (fun r : LMinusSidePresentation x =>
      lMinusRawExteriorBoundaryDartCode r i) := by
  exact ((measurable_pi_apply i).comp
    (measurable_lMinusCodeExteriorBoundaryEdge_presentation x)).prodMk
      measurable_const

/-- Helper toward Lemma 5.5. The complete sequence of raw exterior boundary
dart codes is measurable on the presentation space. The quotient relabeling
needed for the marked geometric boundary remains separate. -/
theorem measurable_lMinusRawExteriorBoundaryDartCode_presentation
    (x : DirectedDistances.PlanarMap.XDP) :
    Measurable (fun r : LMinusSidePresentation x =>
      lMinusRawExteriorBoundaryDartCode r) := by
  exact measurable_pi_iff.mpr
    (measurable_lMinusRawExteriorBoundaryDartCode_presentation_apply x)


























































end DirectedDistances.PaperProofs.Section5
