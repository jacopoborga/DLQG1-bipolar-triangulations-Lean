/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCorrectedDecoder4
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly7

/-! Almost-sure assembly of the corrected nonnegative left-side comparison.
No paper-completion claim is made. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: on one common probability-one event, the
actual left-side classes equal the corrected code-block classes at every
nonnegative index, retaining both modes, uniqueness and pairwise coalescence. -/
theorem ae_boundaryGluing_nonneg_left_class_eq_lPlusCodeBlockSide4 :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
      ∃ hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k),
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ∧
        ∀ (k : ℤ) (hk : 0 ≤ k),
          ∃ (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
            (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
            (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
              (if longest then XDP.ldp else XDP.sdp)
                renewalTime renewalTime_positiveSuccessTime),
            geometricSideClass (m0GeodesicSide hp (P k) .left) =
              geometricSideClass
                (lPlusCodeBlockSide4 hτ hp (P k) hqMode (T k) hfin (hleft k) hk) := by
  filter_upwards [Xdp.m0Cut_ae_leftmost_xdp_and_pairwise_coalescence,
    wholePlane_ae_boundaryGluing_inputs] with W hgeo hglue
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hgeo
  refine ⟨H, h, hLL, hp, ?_⟩
  intro longest
  obtain ⟨R, T, P, hR, hleft, huniq, hcoal⟩ := hpaths longest
  refine ⟨R, T, P, hleft, hR, huniq, hcoal, ?_⟩
  intro k hk
  obtain ⟨hτ, hfin, _, hcoherent⟩ := hglue h k
  let hq := hcoherent (if longest then XDP.ldp else XDP.sdp)
  refine ⟨hτ, hfin, hq, ?_⟩
  exact (geometricSideClass_eq_iff _ _).mpr
    (boundaryGluing_nonneg_left_markedIso_lPlusCodeBlockSide4
      hτ hp (P k) hq (T k) hfin (hleft k) hk)

/-- Helper toward Lemma 5.5: identify the actual-left observable with the
corrected code block built from its very same chosen reader witness.
This does not replace that witness by the presentation reader's choice. -/
theorem ae_lemma55LeftSideClassOption_eq_lPlusCodeBlockSide4
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ hw : Nonempty (M0LeftSideReaderWitness W
          (if x = XDP.ldp then true else false)),
      let w := Classical.choice hw
      ∃ (hτ : HasFlowLineHits (boundaryGluingFutureStream W w.h k))
        (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W w.h k))
        (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
          (if (if x = XDP.ldp then true else false) then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime),
        lemma55LeftSideClassOption x k W =
          some (geometricSideClass
            (lPlusCodeBlockSide4 hτ w.hp (w.P k) hqMode (w.T k) hfin (w.hleft k) hk)) := by
  filter_upwards [ae_m0LeftSideReaderWitness,
    wholePlane_ae_boundaryGluing_inputs] with W hreaders hglue
  let hw : Nonempty (M0LeftSideReaderWitness W
      (if x = XDP.ldp then true else false)) :=
    hreaders (if x = XDP.ldp then true else false)
  let w := Classical.choice hw
  obtain ⟨hτ, hfin, _, hcoherent⟩ := hglue w.h k
  let hq := hcoherent
    (if (if x = XDP.ldp then true else false) then XDP.ldp else XDP.sdp)
  refine ⟨hw, hτ, hfin, hq, ?_⟩
  rw [lemma55LeftSideClassOption_eq_some_of_nonempty x k W hw]
  exact congrArg some ((geometricSideClass_eq_iff _ _).mpr
    (boundaryGluing_nonneg_left_markedIso_lPlusCodeBlockSide4
      hτ w.hp (w.P k) hq (w.T k) hfin (w.hleft k) hk))




























































































































end DirectedDistances.PaperProofs.Section5

/- Validation (2026-11-06): temporary signature and axiom probes for both
declarations compiled successfully. Each reported exactly
[propext, Classical.choice, Quot.sound]; the probes were removed.
Development compile exits: 1, 0, 0, 0. Probe compile exit: 0.
The first development failure was a dependent statement binder and was
repaired by explicitly existentially binding hleft before using it.
no placeholders or additional identification premises were introduced. -/
