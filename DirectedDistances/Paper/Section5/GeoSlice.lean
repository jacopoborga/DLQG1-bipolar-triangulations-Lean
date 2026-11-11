 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.GeoSliceLemma56Provider

/-!
# Lemma 5.6 (`lem-geo-slice`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/




















public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.Paper.Section4

 
theorem lem_geo_slice (default : GeometricSideClass) :
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
            (forgetMarksOptionClassValue default ∘ G 0)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_geo_slice_source_provider default
 
 

end DirectedDistances.Paper.Section5
 
