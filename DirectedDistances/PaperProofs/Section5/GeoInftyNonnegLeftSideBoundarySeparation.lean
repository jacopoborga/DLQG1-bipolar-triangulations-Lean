/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff8
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff7

/-! Helpers toward Lemma 5.5: separation at retained boundary ports.
Source reference used by the surrounding development: -/

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
local notation "ULedges" =>
  (List.reverse (List.dropLast (State.UL
    (kmswStage w (boundaryHitTime w h k)))) )

/-- Helper toward Lemma 5.5: at each interior vertex of the retained
upper-left boundary chain, the two incident boundary ports have their
ambient first returns to the retained left side. The gaps in these first
returns say that every intervening dart lies outside the retained side. -/
theorem lPlus_upperLeft_boundary_separation
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge w (boundaryHitTime w h (j - 1))))}
    (hτ : HasFlowLineHits U) (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath w (boundaryPresentVertex w h k))
    (hfin : hatLimitFiniteIncidence U)
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 < k) (i a b : ℕ)
    (ha : ULedges[i]? = some a) (hb : ULedges[i + 1]? = some b) :
    let S := m0GeodesicSide hp P ThinMapSide.left
    let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin)
    (∃ p : ℕ × Bool, lMinusPrimedDartImage hτ p = (a, false) ∧
      S.rotation (a, false) (lMinusPrimedDartImage hτ (TR p))) ∧
    ∃ q : LPlusPrefixDart W h k, q.val = (b, true) ∧
      S.rotation (b, true)
        (lPlusPrefixStageDart hk (stageRot w (boundaryHitTime w h k - 1)
          (lPlusPrefixDartStage hk q))).val := by
  exact lPlus_upperLeft_interior_side_returns hτ hp P hqMode Tpath hfin hleft
    hk i a b ha hb























































































end DirectedDistances.PaperProofs.Section5
