/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Assembly4
public import DirectedDistances.PaperProofs.Section5.GeoSliceOneSliceReaderFixed2
public import DirectedDistances.PaperProofs.Section5.GeoSliceRightSliceUpdates3
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Provider
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SliceMeasurable

/-! The source slice provider remains conditional on the displayed right readers. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: conditional exactly on the displayed right
readers, the source slice family has almost-everywhere measurability, presence,
the common geometric characterization, independence after forgetting marks,
and the two half-index laws. -/
theorem lem_geo_slice_source_provider_of_rightReaders
    (default : GeometricSideClass) (x : XDP)
    (readR : ℤ → RMinusThinPresentation → GeometricSideClass)
    (hReadR : ∀ j : ℤ, ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        readR j (geoSlice56RightCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right))
    (readRplus : RMinusThinPresentation → GeometricSideClass)
    (hReadRplus : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ, 0 ≤ j →
      ∀ s : M0CutGeodesicSliceWitness W x,
        readRplus (geoSlice56RightCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) :
    ∃ G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass,
      (∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure) ∧
      (∀ k, ∀ᵐ W ∂wholePlaneIIDCodeMeasure, (G k W).isSome) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
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
          G k W = some (geometricSideClass
            (m0CutGeodesicSlice (hp := hp) P k a b hab))) ∧
      iIndepFun (fun k => forgetMarksOptionClassValue default ∘ G k)
        wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ G 1)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ G 0)) := by
  let G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass :=
    m0CutGeodesicSliceClassOption x
  refine ⟨G, aemeasurable_m0CutGeodesicSliceClassOption x,
    ae_m0CutGeodesicSliceClassOption_isSome x,
    m0Cut_ae_geodesicSliceClassOption_characterization x, ?_⟩
  exact lemma56_unmarked_of_sideReaders4 default x G
    (aemeasurable_m0CutGeodesicSliceClassOption x)
    (oneL (if x = XDP.ldp then true else false))
    (prevL (if x = XDP.ldp then true else false))
    (m0Cut_ae_leftSideUpdates x)
    (oneR3 x) (nextR3 x) (m0Cut_ae_rightSideUpdates x)
    (readL4 default x) (hReadL4 default x) readR hReadR
    (readLminus4 default x) (hReadLminus4 default x) readRplus hReadRplus

end DirectedDistances.PaperProofs.Section5
