/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation4

/-! Helpers toward Lemma 5.5: the initial beta-port successor. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: in the nonempty-attachment case, the coded
root beta dart reaches the first upper-left attachment dart in one ambient
step; the open interval is empty. -/
theorem lPlus_initial_beta_upperLeft_side_rotation_coded
    (hn : 0 < (ULedges).length) :
    (m0GeodesicSide hp P .left).rotation
      (D (lPlusBetaGluedDart hτ hqMode (0, false))).val
      (D (lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true))).val := by
  simp only [lPlusBetaGluedDart, lPlusHattedGluedDart,
    lPlusGluedDartEquivNonneg_mk, lPlusBlockDartImage]
  have hb : ((MH).boundary 0).1 = kmswLeftBoundaryEdge (hatCodes U hτ) 0 := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) 0 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  rw [hb]
  exact lPlus_initial_beta_upperLeft_side_rotation hτ hp P hqMode Tpath hfin
    hleft hk hn










































end DirectedDistances.PaperProofs.Section5
