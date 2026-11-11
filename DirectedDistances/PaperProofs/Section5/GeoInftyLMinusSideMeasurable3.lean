/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusSideMeasurable

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "LMinusCode" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap)

/-- Helper toward Lemma 5.5. A source-valid whole-plane input for the
complete nonpositive left-side construction. The mode equation ties the
presentation index `x` to the `longest` mode used by the cut geodesic. -/
structure LMinusPreimage (x : XDP) where
  W : ℤ → Fin 3
  h : BoundaryHitWitnesses (shiftedStream W 0)
  H : WholePlaneRotationHypothesis W
  hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))
  longest : Bool
  mode_eq : x = if longest then XDP.ldp else XDP.sdp
  k : ℤ
  hk : k ≤ 0
  hp : BoundaryHitWitnesses (kmswPastCode W)
  hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)
  hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
  hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)
  P : M0CutInfiniteGeodesic W H h hLL k longest
  Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k)
  hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath

/-- Helper toward Lemma 5.5. Read the two-block presentation code from a
whole-plane preimage at its nonpositive boundary index. -/
@[expose] noncomputable def lMinusCodeOf {x : XDP} (q : LMinusPreimage x) : LMinusCode :=
  leftSideObsNonpos x q.k q.W

/-- Helper toward Lemma 5.5. Realize the complete glued side when the two
blocks of the presentation have a source-valid whole-plane preimage. -/
@[expose] noncomputable def LMinusSidePresentation.wholeRealization
    {x : XDP} (r : LMinusSidePresentation x) : Option GeometricSideSubmap := by
  classical
  exact if hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code then
    some (lMinusDecodedSide (W := hq.choose.W) (h := hq.choose.h)
      (k := hq.choose.k) (longest := hq.choose.longest)
      hq.choose.hτ hq.choose.hqMode hq.choose.hfin)
  else none

/-- Helper toward Lemma 5.5. The whole-side reader returns the code-built
side of the same preimage selected by its realization guard. -/
theorem LMinusSidePresentation.wholeRealization_eq_some_lMinusDecodedSide
    {x : XDP} (r : LMinusSidePresentation x)
    (hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code) :
    r.wholeRealization =
      some (lMinusDecodedSide (W := hq.choose.W) (h := hq.choose.h)
        (k := hq.choose.k) (longest := hq.choose.longest)
        hq.choose.hτ hq.choose.hqMode hq.choose.hfin) := by
  classical
  simp [LMinusSidePresentation.wholeRealization, hq]























end DirectedDistances.PaperProofs.Section5
