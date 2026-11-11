/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Reduction
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SideAlignment

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: the chosen option-valued slice family has the
almost-sure geometric characterization by a common leftmost family, its
uniqueness clauses, and the least-coalescence witnesses. -/
theorem m0Cut_ae_geodesicSliceClassOption_characterization (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k
        (if x = XDP.ldp then true else false),
      (∀ k, Xdp.CutLeftmostXdp W H h hp hLL
        (if x = XDP.ldp then true else false) k (P k) (T k)) ∧
      (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL
        (if x = XDP.ldp then true else false) k Q (T k) → Q = P k) ∧
      ∀ k : ℤ, ∃ a b : ℕ,
        ∃ hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b,
        m0CutGeodesicSliceClassOption x k W = some (geometricSideClass
          (m0CutGeodesicSlice (hp := hp) P k a b hab)) := by
  exact m0Cut_ae_geodesicSlice_class x


















































































end DirectedDistances.PaperProofs.Section5
