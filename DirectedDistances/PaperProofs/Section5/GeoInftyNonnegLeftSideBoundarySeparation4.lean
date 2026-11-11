/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation3

/-! Helpers toward Lemma 5.5: the initial beta-port block output. -/

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
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))
local notation "β" => lPlusBetaGluedDart hτ hqMode (0, false)
local notation "C" => lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: on a nonempty upper-left attachment, the
block permutation's beta-port output is the terminal transposition applied
to the preceding corrected-permutation output. -/
theorem lPlusGluedBlockRotation2_beta_apply_nonempty
    (hn : 0 < (ULedges).length) :
    lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft β =
      Equiv.swap
        (C (lPlusUpperLeftGluedDart hτ hqMode hfin hk
          (⟨(ULedges).length - 1, by omega⟩, false)))
        (lPlusPrimedExtendedRotation hτ hqMode hfin
          (lPlusUpperLeftGluedDart hτ hqMode hfin hk
            (⟨(ULedges).length - 1, by omega⟩, false)))
        (C β) := by
  rw [lPlusGluedBlockRotation2, dite_eq_left hn]
  simp only [Equiv.Perm.mul_apply]

/-- Helper toward Lemma 5.5: when the upper-left attachment is empty, the
block permutation has no terminal exchange; its beta-port output is the
explicit five-factor corrected block action. -/
theorem lPlusGluedBlockRotation2_beta_apply_empty
    (h0 : (ULedges).length = 0) :
    lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft β =
      lPlusHattedExtendedRotation hτ hqMode
        (lPlusBetaCornerRotation hτ hqMode
          (lPlusPrimedExtendedRotation hτ hqMode hfin
            (lPlusUpperLeftCornerRotation hτ hqMode hfin hk
              (lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk β)))) := by
  simp [lPlusGluedBlockRotation2, h0, lPlusGluedCorrectedRotation,
    Equiv.Perm.mul_apply]









































end DirectedDistances.PaperProofs.Section5
