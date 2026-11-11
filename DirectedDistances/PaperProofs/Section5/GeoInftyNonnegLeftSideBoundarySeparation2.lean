/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff10

/-! Helpers toward Lemma 5.5: initial boundary-star separation. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W} {longest : Bool}

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))) )

/-- Helper toward Lemma 5.5: the initial beta dart and the first upper-left
east port are consecutive in the retained left-side rotation whenever that
port exists. The one-step interval is empty. -/
theorem lPlus_initial_beta_upperLeft_side_rotation
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge w (boundaryHitTime w h (j - 1))))}
    (hτ : HasFlowLineHits U) (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath w (boundaryPresentVertex w h k))
    (hfin : hatLimitFiniteIncidence U)
    (_hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) (hn : 0 < (ULedges).length) :
    (m0GeodesicSide hp P .left).rotation
      (boundaryGluingHatEdgeMap W h k hτ
        (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false)
      (ULedges[0], true) := by
  refine ⟨1, by omega, ?_, fun j hj hjn => by omega⟩
  change kmswInfRot w (H.1 0)
      (boundaryGluingHatEdgeMap W h k hτ
        (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
    (ULedges[0], true)
  exact lPlus_upperLeft_initial_beta_successor (H := H) hτ hqMode hfin hk hn















































end DirectedDistances.PaperProofs.Section5
