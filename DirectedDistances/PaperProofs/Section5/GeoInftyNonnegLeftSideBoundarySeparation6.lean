/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation5
import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideSplice

/-! Helpers toward Lemma 5.5: identifying the initial beta-port successor. -/

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
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "F" => lPlusBlockDartImage
  (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
local notation "Q" => LPlusGluedDart longest hqMode hτ

include hp P Tpath hleft in
/-- Helper toward Lemma 5.5: the code-defined first return from the canonical
beta dart is the first upper-left attachment dart when that attachment is
nonempty. This uses the ambient one-step successor and first-return uniqueness. -/
theorem lPlusGluedCodeReturn_initial_beta_eq_first_upperLeft
    (hn : 0 < (ULedges).length) :
    lPlusGluedCodeReturn (H := H) hτ hqMode
        (lPlusBetaGluedDart hτ hqMode (0, false)) =
      lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true) := by
  let a := lPlusBetaGluedDart hτ hqMode (0, false)
  let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)
  obtain ⟨m, hmpos, hmret, hmgap⟩ :=
    lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk a
  obtain ⟨n, hnpos, hnret, hngap⟩ :=
    lPlus_initial_beta_upperLeft_firstReturn (H := H) hτ hqMode hfin hk hp P Tpath hleft hn
  have hmem (q : Q) : (D q).val ∈ Set.range F := by
    rw [← lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk q]
    exact (lPlusGluedCodeImageEquiv hτ hqMode q).property
  have hv : (D (lPlusGluedCodeReturn (H := H) hτ hqMode a)).val = (D d).val :=
    firstReturn_endpoint_unique (kmswInfRot w (H.1 0)) (Set.range F)
      (hmem _) (hmem d)
      ⟨m, hmpos, hmret, hmgap⟩ ⟨n, hnpos, hnret, hngap⟩
  apply (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk).injective
  exact Subtype.ext hv





































end DirectedDistances.PaperProofs.Section5
