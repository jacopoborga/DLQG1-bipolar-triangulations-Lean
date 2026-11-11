/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation2
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff11
import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideSplice

/-! Helpers toward Lemma 5.5: the initial beta port. -/

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

/-- Helper toward Lemma 5.5: the unique beta dart incident at the initial
boundary vertex is the canonical west dart. -/
theorem lPlusBetaGluedDart_root_port_unique (p : ℕ × Bool)
    (hp0 : kmswLimitDartVertex w
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode p)).val = boundaryVertex w h k) :
    p = (0, false) := by
  have hroot : kmswLimitDartVertex w
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary p.1).1, p.2) =
        boundaryVertex w h k := by
    simpa only [lPlusBetaGluedDart, lPlusHattedGluedDart,
      lPlusGluedDartEquivNonneg_mk, lPlusBlockDartImage] using hp0
  have hlocal : kmswLimitDartVertex (hatCodes U hτ)
      (((MH).boundary p.1).1, p.2) = 0 := by
    have hend := boundaryGluing_hat_edge_endpoints W h k hτ
      ((MH).boundary p.1).1
    cases hb : p.2 with
    | false =>
      rw [hb] at hroot
      change edgeWest w
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary p.1).1) = _ at hroot
      rw [hend.1] at hroot
      have hm : boundaryGluingHatVertexMap W h k hτ
          (edgeWest (hatCodes U hτ) ((MH).boundary p.1).1) =
            boundaryGluingHatVertexMap W h k hτ 0 := by
        rw [boundaryGluingHatVertexMap_zero]
        exact hroot
      have hv := (boundaryGluingHatVertexMap_injective W h k hτ) hm
      change edgeWest (hatCodes U hτ) ((MH).boundary p.1).1 = 0
      exact hv
    | true =>
      rw [hb] at hroot
      change edgeEast w
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary p.1).1) = _ at hroot
      rw [hend.2] at hroot
      have hm : boundaryGluingHatVertexMap W h k hτ
          (edgeEast (hatCodes U hτ) ((MH).boundary p.1).1) =
            boundaryGluingHatVertexMap W h k hτ 0 := by
        rw [boundaryGluingHatVertexMap_zero]
        exact hroot
      have hv := (boundaryGluingHatVertexMap_injective W h k hτ) hm
      change edgeEast (hatCodes U hτ) ((MH).boundary p.1).1 = 0
      exact hv
  have hsource : kmswLimitDartVertex
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)))
      (((MH).boundary p.1).1, p.2) = 0 := by
    rw [← boundaryGluing_decoded_stream W h k hτ] at hlocal
    exact hlocal
  obtain ⟨hi, hb⟩ := (lMinus_hatted_boundary_source_iff hqMode p.1 p.2).mp hsource
  exact Prod.ext hi hb










































end DirectedDistances.PaperProofs.Section5
