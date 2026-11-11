/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE3




public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. A coherent hatted observation gives existence
of the decoded whole-side realization at every nonpositive boundary index. -/
theorem boundaryGluing_nonpos_right_wholeRealization_isSome
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hk : k ≤ 0) :
    (decodeRMinus (if longest then XDP.ldp else XDP.sdp) k
      (rightSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).wholeRealization.isSome := by
  exact decodeRMinus_rightSideObsNonpos_wholeRealization_isSome_of_coherent
    (h := h) longest hqMode hk
















































/- Attempts and current obstruction for the marked-isomorphism and class-reader
statements above:

1. The source-selected `boundaryGluing_nonpos_right_markedIso_nonempty` gives
   an isomorphism from `rMinusDecodedSide` for `shiftedStream W 0` and the
   boundary-hit stage. Direct application cannot typecheck: the target side
   is selected by the observation's `wholeRealization` and is indexed by its
   stopped prefix code.
2. Rewriting `wholeRealization` with
   `RMinusSidePresentation.wholeRealization_eq_some_rMinusDecodedSide` and
   identifying the prefix stage reduces the mismatch to comparing
   `rMinusCodeInitialAdjustedRotation` across streams that agree only before
   the stopping time. `stageRot_comm_of_prefix` gives conjugacy of the finite
   rotations, but the required transport through the stage-dependent
   `RMinusCodeGluedDart` quotient and its adjusted permutation is not proved.
   Direct equality elimination and rewriting on the dependent stage state both
3. Extracting the hatted realization and using
   `rMinusDecodedSideOfBlocks_markedIso_of_eq` handles equal coherent thin
   codes at a fixed stream and stage. It does not transport the prefix
   permutation across the stopped/source stream comparison, so the same
   adjusted-rotation obligation remains. Comparing the optional class readers
   directly through `geometricSideClass_eq_iff` has the same missing premise.

For the decoded-law measurability statement, the inspected Lemma 5.5 files
provide `aemeasurable_lemma55RightSideClassOption_nonpositive_of_AE3`, whose
hypothesis supplies an almost-everywhere identification of the actual right
observable with a measurable R-minus reader. That identity is the open target
above; it cannot be used here as an independent measurability result. The
imported `aemeasurable_RMinusSidePresentation_classOption_isSome` proves only
measurability of the presence indicator. No class-valued measurability or
marked-isomorphism premise is added. -/

end DirectedDistances.PaperProofs.Section5
