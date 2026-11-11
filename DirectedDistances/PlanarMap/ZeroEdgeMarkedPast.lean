/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBoltzmannMapLaw

public section
namespace DirectedDistances.PlanarMap

/-- The singleton type for the zero-edge marked past in the full-scope ruling
Lemma 4.13 (full-scope ruling); not a paper result. -/
inductive ZeroEdgeMarkedPast where
  /-- The unique marked point. Helper toward Lemma 4.13 (full-scope ruling); -/
  | point
  deriving DecidableEq

/-- The canonical one-vertex, zero-edge past. Helper toward Lemma 4.13 -/
@[expose] def zeroEdgeMarkedPast : ZeroEdgeMarkedPast := .point

/-- The vertex carrier of the marked point past. Helper toward Lemma 4.13 -/
abbrev ZeroEdgeMarkedPastVertex := PUnit

/-- The edge carrier of the marked point past. Helper toward Lemma 4.13 -/
abbrev ZeroEdgeMarkedPastEdge := Empty

/-- The source vertex of the marked point past. Helper toward Lemma 4.13 -/
@[expose] def zeroEdgeMarkedPastSource : ZeroEdgeMarkedPastVertex := PUnit.unit

/-- The sink vertex of the marked point past. Helper toward Lemma 4.13 -/
@[expose] def zeroEdgeMarkedPastSink : ZeroEdgeMarkedPastVertex := PUnit.unit

/-- The left boundary length of the marked point past. Helper toward Lemma 4.13 -/
@[expose] def zeroEdgeMarkedPastLeftBoundaryLength : ℕ := 0

/-- The right boundary length of the marked point past. Helper toward Lemma 4.13 -/
@[expose] def zeroEdgeMarkedPastRightBoundaryLength : ℕ := 0

/-- The canonical point has exactly one vertex, no edges, coinciding source
and sink, and boundary lengths `(0, 0)`. Helper toward Lemma 4.13 (full-scope -/
theorem zeroEdgeMarkedPast_characterization :
    (∃! p : ZeroEdgeMarkedPast, p = zeroEdgeMarkedPast) ∧
    (∃! _v : ZeroEdgeMarkedPastVertex, True) ∧
    (∀ _e : ZeroEdgeMarkedPastEdge, False) ∧
    zeroEdgeMarkedPastSource = zeroEdgeMarkedPastSink ∧
    zeroEdgeMarkedPastSource = PUnit.unit ∧
    zeroEdgeMarkedPastSink = PUnit.unit ∧
    zeroEdgeMarkedPastLeftBoundaryLength = 0 ∧
    zeroEdgeMarkedPastRightBoundaryLength = 0 := by
  constructor
  · refine ⟨zeroEdgeMarkedPast, rfl, ?_⟩
    intro p _
    cases p
    rfl
  · simp [zeroEdgeMarkedPastSource, zeroEdgeMarkedPastSink,
      zeroEdgeMarkedPastLeftBoundaryLength, zeroEdgeMarkedPastRightBoundaryLength]

/-- Positive Boltzmann map classes with both boundary lengths positive.
Helper toward Lemma 4.13 (full-scope ruling); not a paper result -/
abbrev PositiveSelectedCutPastMap :=
  Σ ℓ : {n : ℕ // 1 ≤ n},
    Σ r : {n : ℕ // 1 ≤ n}, BoltzmannSpace ℓ.1 r.1

/-- The sum carrier for the zero point and positive selected-cut pasts, with
the discrete measurable space. Helper toward Lemma 4.13 (full-scope ruling); -/
abbrev SelectedCutPastMap := ZeroEdgeMarkedPast ⊕ PositiveSelectedCutPastMap

/-- The selected-cut carrier has the discrete measurable space. Helper toward
Lemma 4.13 (full-scope ruling); not a paper result
(full-scope ruling); not a paper result. -/
noncomputable instance : MeasurableSpace SelectedCutPastMap := ⊤

/-- The zero-edge point is distinct from every positive Boltzmann class by
the disjoint sum constructors. Helper toward Lemma 4.13 (full-scope ruling); -/
theorem zeroEdgeMarkedPast_ne_positive (m : PositiveSelectedCutPastMap) :
    (Sum.inl zeroEdgeMarkedPast : SelectedCutPastMap) ≠ Sum.inr m := by
  simp

end DirectedDistances.PlanarMap
