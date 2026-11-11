/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso4

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

This file proves supporting corner and block-action facts for the non-prefix
root-incident cases. The remaining iff cases and the combined target are
recorded with their full binders below. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the two primed darts at the initial root corner
are interchanged by the primed extended rotation. -/
theorem lPlusPrimedExtendedRotation_initial_root_corners
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    let b₀ := primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
      (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) hfin 0
    lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true)) =
          lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (b₀, true) ∧
    lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (b₀, true)) =
          lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true) := by
  dsimp only
  let U := boundaryGluingFutureStream W h k
  let b₀ := primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin 0
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  have haction (p : ℕ × Bool) :
      lPlusPrimedExtendedRotation hτ hqMode hfin (IT p) = IT (TR p) :=
    TR.extendDomain_apply_image
      (Equiv.ofInjective IT (lPlusPrimedGluedDart_injective
        (hτ := hτ) (hqMode := hqMode))) p
  constructor
  · calc
      lPlusPrimedExtendedRotation hτ hqMode hfin (IT (0, true)) =
          IT (TR (0, true)) := haction (0, true)
      _ = IT (b₀, true) := congrArg IT (lPlusPrimedRotation_initial_root_corner hτ hfin)
  · calc
      lPlusPrimedExtendedRotation hτ hqMode hfin (IT (b₀, true)) =
          IT (TR (b₀, true)) := haction (b₀, true)
      _ = IT (0, true) := congrArg IT (lMinusPrimedRotation_initial_corner hτ hfin)

/-- Helper toward Lemma 5.5: on every hatted representative, the hatted
extended rotation acts by the retained hatted rotation. -/
theorem lPlusHattedExtendedRotation_apply_hatted
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (a : LPlusHattedDart
      (lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode)) :
    lPlusHattedExtendedRotation hτ hqMode
        (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) a) =
      lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
        (lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
          ⟨boundaryFutureHattedPath k W, hqMode⟩ a) := by
  exact (lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
      ⟨boundaryFutureHattedPath k W, hqMode⟩).extendDomain_apply_image
    (Equiv.ofInjective _ (lPlusHattedGluedDart_injective
      (hτ := hτ) (hqMode := hqMode))) a

/-- Helper toward Lemma 5.5: a beta representative at the initial root is
the canonical west dart. -/
theorem lPlusBetaGluedDart_initial_root_eq_canonical
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
    (hk : 0 ≤ k) (p : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode p)).val =
          boundaryVertex (shiftedStream W 0) h k) :
    lPlusBetaGluedDart hτ hqMode p =
      lPlusBetaGluedDart hτ hqMode (0, false) := by
  exact congrArg (lPlusBetaGluedDart hτ hqMode)
    (lPlusBetaGluedDart_root_port_unique hτ hp P hqMode Tpath hfin hleft hk p hd)

/-- Helper toward Lemma 5.5: the canonical beta dart has the proved block
output in both finite upper-left attachment cases. -/
theorem lPlusGluedBlockRotation2_beta_initial_output
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
    (hk : 0 ≤ k) :
    (∀ hn : 0 < (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length,
      lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft
          (lPlusBetaGluedDart hτ hqMode (0, false))) =
      lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusUpperLeftGluedDart hτ hqMode hfin hk
          (⟨0, hn⟩, true))) ∧
    ((List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length = 0 →
      lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft
          (lPlusBetaGluedDart hτ hqMode (0, false)) =
        lPlusHattedExtendedRotation hτ hqMode
          (lPlusBetaCornerRotation hτ hqMode
            (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true)))) := by
  constructor
  · intro hn
    exact lPlusGluedBlockRotation2_beta_output_initial_upperLeft
      hτ hp P hqMode Tpath hfin hleft hk hn
  · intro hzero
    exact lPlusGluedBlockRotation2_beta_output_of_upperLeft_empty
      hτ hp P hqMode Tpath hfin hleft hk hzero





















































































































































end DirectedDistances.PaperProofs.Section5
