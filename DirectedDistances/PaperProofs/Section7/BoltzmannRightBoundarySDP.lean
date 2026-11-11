/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Distance
public import DirectedDistances.KMSW.BoltzmannMarkedRightLaw
public import DirectedDistances.PlanarMap.BipolarBoundaryData

/-! # Right-boundary shortest directed distance on marked Boltzmann maps

Helpers toward Lemma 7.12 (`lem-boltzmann-sdp-lower`, -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open Quiver
open scoped ENNReal

/-- The map's arrows are precisely its present oriented darts, retaining the
dart identity. Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a
paper result. -/
instance presentDartQuiver {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) : Quiver (MapVertex M) where
  Hom v w :=
    {d : D // ¬ M.missing d ∧ M.tail d ∧
      dartTailVertex M d = v ∧ dartHeadVertex M d = w}

/-- The shortest directed distance in the quiver whose arrows are exactly
present oriented darts. Parallel darts retain their identities and missing
edges contribute no arrows. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
@[expose] noncomputable def presentDartSDP {D : Type*} [Fintype D]
    [DecidableEq D] (M : DirectedMapWithMissing D) (v w : MapVertex M) : ℕ∞ := by
  exact DirectedDistances.sdp v w

/-- The shortest directed distance from a vertex to itself is zero in the
present-dart quiver. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem presentDartSDP_self {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (v : MapVertex M) :
    presentDartSDP M v v = 0 := by
  simp [presentDartSDP]

/-- The indexed right-boundary vertices of a marked map, in source-to-sink
order. Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper
result. -/
@[expose] noncomputable def rightBoundaryVertex {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) (i : Fin (r + 1)) :
    MapVertex q.1.2.2.out.B.map :=
  q.1.2.2.out.B.rightPath.vertices.get ⟨i.val, by
    rw [q.1.2.2.out.B.rightPath.vertices_length]
    omega⟩

/-- Index zero on the right boundary is the source. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem rightBoundaryVertex_zero {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) :
    rightBoundaryVertex q ⟨0, by omega⟩ = q.1.2.2.out.B.source := by
  simpa [rightBoundaryVertex] using q.1.2.2.out.B.rightPath.start_vertex

/-- The last right-boundary index is the sink. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem rightBoundaryVertex_last {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) :
    rightBoundaryVertex q ⟨r, by omega⟩ = q.1.2.2.out.B.sink := by
  simpa [rightBoundaryVertex] using q.1.2.2.out.B.rightPath.end_vertex

/-- Maps having a right-boundary vertex at SDP at least `c`, independent of
the mark. The distance is embedded in `ℝ≥0∞`, preserving `⊤` for unreachable
vertices. Helper toward Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper
result. -/
@[expose] noncomputable def rightBoundarySDPEvent (r : ℕ) (c : ℝ≥0∞) :
    Set (RightVertexMarkedBoltzmannSpace r) :=
  {q | ∃ i : Fin (r + 1),
    c ≤ ENat.toENNReal
      (presentDartSDP q.1.2.2.out.B.map q.1.2.2.out.B.source
        (rightBoundaryVertex q i))}

/-- Every subset of the marked space is measurable, hence so is the
right-boundary SDP event. Helper toward Lemma 7.12
(`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem measurableSet_rightBoundarySDPEvent (r : ℕ) (c : ℝ≥0∞) :
    MeasurableSet (rightBoundarySDPEvent r c) := by
  trivial

/-- Raising the distance threshold can only shrink the event. Helper toward
Lemma 7.12 (`lem-boltzmann-sdp-lower`); not a paper result. -/
theorem rightBoundarySDPEvent_antitone (r : ℕ) {c d : ℝ≥0∞}
    (hcd : c ≤ d) : rightBoundarySDPEvent r d ⊆ rightBoundarySDPEvent r c := by
  intro q hq
  obtain ⟨i, hi⟩ := hq
  exact ⟨i, le_trans hcd hi⟩

end DirectedDistances.PaperProofs.Section7
