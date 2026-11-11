/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole
public import DirectedDistances.KMSW.PrimedFaceOrbitEquiv

 

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section PrimedRetention

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "U" => boundaryGluingFutureStream W h k
local notation "p" => primedCode (primedSimInput U) hτ
local notation "hf" => primedCode_finiteIncidence U hτ hfin

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every dart in the primed block maps to a dart
whose edge ID is retained by the actual nonpositive left side. -/
theorem lMinusPrimedDartImage_mem_leftSide (d : ℕ × Bool) :
    (lMinusPrimedDartImage hτ d).1 ∈
      (m0GeodesicSide hp P ThinMapSide.left).edges := by
  have hmem : lMinusPrimedDartImage hτ d ∈
      Set.range (lMinusBlockDartImage hτ hqMode) := ⟨Sum.inl d, rfl⟩
  rw [lMinusBlockDartImage_range hτ hp P hqMode Tpath hfin hleft hk] at hmem
  exact hmem

include hτ hfin in
/-- Helper toward Lemma 5.5: each primed creation triangle has an ambient
creation triangle in the future stream containing all its geometric dart images. -/
theorem lMinusPrimedCreationTriangle_future_stageTriangle
    (j : TriangleCreationTime p) :
    ∃ J : TriangleCreationTime U,
      ∀ d ∈ stageTriangleDartList p j,
        (primedGeometricDartEquiv U hτ
          (show primedLimitFiniteIncidence U by
            simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin)
          (hatBoundaryHitWitnesses U hτ) d).val ∈ stageTriangleDartList U J := by
  exact (primedCreationTriangle_orientedImageGoal_holds U hτ
    (show primedLimitFiniteIncidence U by
      simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin)
    (hatBoundaryHitWitnesses U hτ)) j














































end PrimedRetention

end DirectedDistances.PaperProofs.Section5
