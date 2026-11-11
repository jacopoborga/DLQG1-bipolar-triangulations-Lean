/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso3

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

This file carries the proved old-incoming prefix classification into the
actual-side rotation comparison. The finite attachment-plus-root-port
classification is contradicted by the left/left/down example in RootStar. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: a prefix dart is incident to the stopped root
exactly when it is an east dart of an edge allocated before the first hit,
whose finite-stage east endpoint is that root. This bounded allocation
classification retains older incoming edges outside the upper-left fan. -/
theorem lPlusPrefixDart_initial_vertex_bounded_root_star
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} (hk : 0 ≤ k) (d : LPlusPrefixDart W h k) :
    kmswLimitDartVertex (shiftedStream W 0) d.val =
        boundaryVertex (shiftedStream W 0) h k ↔
      d.val.2 = true ∧ ∃ n < boundaryHitTime (shiftedStream W 0) h k,
        d.val.1 < (kmswStage (shiftedStream W 0) n).nextEdge ∧
          (kmswStage (shiftedStream W 0) n).east d.val.1 =
            boundaryVertex (shiftedStream W 0) h k := by
  simpa only [LPlusOldIncomingRootDart] using
    (lPlusPrefixDart_initial_vertex_iff_old_incoming hk d)

/-- Helper toward Lemma 5.5: the candidate-2 rotation comparison holds for
every root-incident stopped-prefix input. The root-star classification and
the old-incoming first-return theorem supply this entire block case. -/
theorem lPlusGluedCorrectedRotation2_prefix_initial_vertex_rotation_iff
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
    (a : LPlusPrefixDart W h k)
    (ha : kmswLimitDartVertex (shiftedStream W 0) a.val =
      boundaryVertex (shiftedStream W 0) h k) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode) a) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode) a)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val := by
  exact lPlusGluedCorrectedRotation2_old_incoming_root_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk a
    (lPlusPrefixDart_initial_vertex_old_incoming hk a ha)


























































end DirectedDistances.PaperProofs.Section5
