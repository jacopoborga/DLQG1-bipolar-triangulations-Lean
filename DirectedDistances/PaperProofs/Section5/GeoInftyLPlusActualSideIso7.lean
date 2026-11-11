/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso6

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

This continuation records the remaining initial-root rotation obligations.
The imported nonempty-beta iff and the primed and hatted block actions are
available, as is the prefix iff from Iso4. The empty-beta output calculation
is also available, but it does not identify the output with the actual-side
successor or certify the intervening open interval. -/

public section

namespace DirectedDistances.PaperProofs.Section5


















/- theorem lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff_empty
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k)
    (p : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode p)).val =
          boundaryVertex (shiftedStream W 0) h k)
    (hzero : (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length = 0) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusBetaGluedDart hτ hqMode p) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusBetaGluedDart hτ hqMode p)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val -/






/- theorem lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k)
    (p : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode p)).val =
          boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusBetaGluedDart hτ hqMode p) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusBetaGluedDart hτ hqMode p)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val -/















/- theorem lPlusGluedCorrectedRotation2_primed_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k)
    (p : LPlusPrimedDart)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p)).val =
          boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) p)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val -/














/- theorem lPlusGluedCorrectedRotation2_hatted_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k)
    (a : LPlusHattedDart
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode))
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a)).val =
          boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val -/













/- theorem lPlusGluedCorrectedRotation2_initial_vertex_rotation_iff
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k)
    (d : LPlusGluedDart longest hqMode hτ)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk d).val =
        boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk d).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val -/

end DirectedDistances.PaperProofs.Section5
