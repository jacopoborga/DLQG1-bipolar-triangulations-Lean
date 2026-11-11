/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideRotation






public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section GeometricGluing

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
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "F" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: at a primed interior input, the replacement
permutation has the primed block output, provided its two changed inputs are
excluded. This is the code-level calculation; geometric first-return
transport is a separate statement. -/
theorem lMinusCodeInitialSplicedRotation_primed_block_output
    (d : ℕ × Bool)
    (hboundary : ∀ i : ℕ, ∀ b : Bool,
      lMinusCodePrimedDart rL Q d ≠ lMinusCodeBoundaryDart rL qL (i, b))
    (hpred : lMinusCodePrimedDart rL Q d ≠
      ((lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL).extendDomain
        (Equiv.ofInjective (lMinusCodeHattedDart rL Q)
          (lMinusCodeHattedDart_injective rL qL))).symm
        (lMinusCodeBoundaryDart rL qL (0, false)))
    (hadjpred : lMinusCodePrimedDart rL Q d ≠
      (lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)).symm
        (lMinusCodeBoundaryDart rL qL (0, false))) :
    lMinusCodeInitialSplicedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin)
        (lMinusCodePrimedDart rL Q d) =
      lMinusCodePrimedDart rL Q
        (kmswInfRot (rL).code.1
          (lMinus_primed_observation_finiteIncidence hτ hfin) d) := by
  rw [lMinusCodeInitialSplicedRotation_apply_of_ne rL qL
    (lMinus_primed_observation_finiteIncidence hτ hfin)
    (lMinusCodePrimedDart rL Q d) hpred hadjpred]
  exact lMinusCodeInitialAdjustedRotation_primed_interior
    hτ hp P hqMode Tpath hfin hleft hk d hboundary


































































end GeometricGluing

end DirectedDistances.PaperProofs.Section5


