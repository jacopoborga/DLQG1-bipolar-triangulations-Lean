/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Final
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Assembly4RightReaders

/-! # Isolated source provider for Lemma 5.6 (`lem-geo-slice`)

`m0CutGeodesicSliceClassOption x k`; the right readers of the exposed reduction are discharged
by `hReadR4` / `hReadRplus4`, and every other input is discharged inside
`lem_geo_slice_source_provider_of_rightReaders`. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.Paper.Section4

/-- Isolated source provider for Lemma 5.6 (`lem-geo-slice`, -/
theorem lem_geo_slice_source_provider (default : GeometricSideClass) :
    ∀ x : XDP,
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
  intro x
  exact lem_geo_slice_source_provider_of_rightReaders default x
    (readR4 default x) (hReadR4 default x)
    (readRplus4 default x) (hReadRplus4 default x)

end DirectedDistances.PaperProofs.SourceResults
