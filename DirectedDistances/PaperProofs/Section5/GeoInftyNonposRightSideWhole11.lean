/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole9
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole4

/-! Transport from the stopped observation to the actual nonpositive right side. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.Probability DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the whole decoded sides agree across streams
with a common finite prefix. The rotation conjugacy is supplied by Whole9;
all other fields depend on the finite state and the shared hatted block. -/
theorem rMinusDecodedSideOfBlocks_eq_of_sharedPrefix11
    (x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    rMinusDecodedSideOfBlocks (kmswStage u n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (rMinusCodeInitialAdjustedRotation u n q) =
      rMinusDecodedSideOfBlocks (kmswStage v n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (rMinusCodeInitialAdjustedRotation v n q) := by
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  have hblocks : ∀ (F G : State) (hs : F = G)
      (R : Equiv.Perm (RMinusCodeGluedDart F M))
      (S : Equiv.Perm (RMinusCodeGluedDart G M)),
      (∀ d, transportEquivOfTypeEq
        (congrArg (fun A : State => RMinusCodeGluedDart A M) hs) (R d) =
          S (transportEquivOfTypeEq
            (congrArg (fun A : State => RMinusCodeGluedDart A M) hs) d)) →
      rMinusDecodedSideOfBlocks F M R = rMinusDecodedSideOfBlocks G M S := by
    intro F G hs R S hr
    cases hs
    have hRS : R = S := by
      apply Equiv.ext
      intro d
      exact hr d
    rw [hRS]
  apply hblocks (kmswStage u n) (kmswStage v n) (kmswStage_eq_of_prefix u v n hp)
  intro d
  exact rMinusCodeInitialAdjustedRotation_conj_of_sharedPrefix x u v n hp q d

/-- Helper toward Lemma 5.5: the cross-prefix marked isomorphism at a shared
boundary stopping frontier, obtained from equality of all decoded fields. -/
theorem rMinusDecodedSideOfBlocks_markedIso_of_sharedBoundaryStoppingFrontier11
    (x : XDP) (k : ℤ) (u v : ℕ → Fin 3) (n : ℕ)
    (_hk : k ≤ 0)
    (_hstopU : boundaryCodeStoppingTime k (rMinusPrefixPath u) = n)
    (hp : ∀ i < n, u i = v i)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    Nonempty (GeometricSideMarkedIso
      (rMinusDecodedSideOfBlocks (kmswStage u n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (rMinusCodeInitialAdjustedRotation u n q))
      (rMinusDecodedSideOfBlocks (kmswStage v n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (rMinusCodeInitialAdjustedRotation v n q))) := by
  rw [rMinusDecodedSideOfBlocks_eq_of_sharedPrefix11 x u v n hp q]
  exact ⟨GeometricSideMarkedIso.refl _⟩

/-- Helper toward Lemma 5.5: the observed whole realization is marked
isomorphic to the actual nonpositive right side, with the source binders. -/
theorem boundaryGluing_nonpos_right_markedIso_wholeRealization
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
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    ∃ hreal : (decodeRMinus (if longest then XDP.ldp else XDP.sdp) k
        (rightSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).wholeRealization.isSome,
      Nonempty (GeometricSideMarkedIso
        ((decodeRMinus (if longest then XDP.ldp else XDP.sdp) k
          (rightSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).wholeRealization.get hreal)
        (m0GeodesicSide hp P .right)) := by
  let x := if longest then XDP.ldp else XDP.sdp
  let r := decodeRMinus x k (rightSideObsNonpos x k W)
  let w := shiftedStream W 0
  let n := boundaryHitTime w h k
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  have hprefix : r.prefixValid := by
    by_contra hn
    have hh := (r.prefixRealization_eq_none_iff).2 hn
    rw [decodeRMinus_rightSideObsNonpos_prefixRealization (h := h) x] at hh
    cases hh
  have hq : ∃ q' : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1 = r.code.2 :=
    ⟨q, rfl⟩
  have hstop : boundaryCodeStoppingTime k (rMinusPrefixPath w) = n := by
    have hh : BoundaryHitWitnesses (fun i => rMinusPrefixPath w (i + 1)) := by
      simpa only [rMinusPrefixPath, Nat.add_one_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel] using h
    simpa only [rMinusPrefixPath, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel] using
      rMinus_boundaryCodeStoppingTime_eq_boundaryHitTime k (rMinusPrefixPath w) hh
  have hprefixEq : ∀ i < n, r.code.1 i = w i := by
    intro i hi
    exact rightSideObsNonpos_prefix_eq_source (h := h) x i hi
  have hstopObs : boundaryCodeStoppingTime k (rMinusPrefixPath r.code.1) = n :=
    (kmswStage_eq_of_sharedBoundaryStoppingFrontier k w r.code.1 n hstop
      (fun i hi => (hprefixEq i hi).symm)).1
  have hn : hprefix.choose = n :=
    rMinus_prefix_frontier_unique k r.code.1 hprefix.choose n
      hprefix.choose_spec.1 hstopObs
  have hreal := decodeRMinus_rightSideObsNonpos_wholeRealization_isSome_of_coherent
    (h := h) longest hqMode hk
  refine ⟨hreal, ?_⟩
  have hget : r.wholeRealization.get hreal =
      rMinusDecodedSide r.code.1 hprefix.choose hq.choose := by
    apply Option.some.inj
    exact (Option.some_get hreal).trans
      (r.wholeRealization_eq_some_rMinusDecodedSide hk hprefix hq)
  rw [hget, hn, rMinusDecodedSide_eq_ofBlocks]
  rw [rMinusDecodedSideOfBlocks_eq_of_sharedPrefix11 x r.code.1 w n hprefixEq hq.choose]
  obtain ⟨I⟩ := rMinusDecodedSideOfBlocks_markedIso_of_eq x w n hq.choose q
    (hq.choose_spec.trans (show r.code.2 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 from rfl))
  obtain ⟨J⟩ := boundaryGluing_nonpos_right_markedIso_nonempty
    hτ hp P hqMode Tpath hfin hleft hk
  rw [rMinusDecodedSide_eq_ofBlocks] at J
  exact ⟨GeometricSideMarkedIso.trans I J⟩








































end DirectedDistances.PaperProofs.Section5

