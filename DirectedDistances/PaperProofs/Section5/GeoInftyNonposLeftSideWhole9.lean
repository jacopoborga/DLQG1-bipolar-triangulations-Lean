/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole8

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section DecodedEdgeIdentification

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

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "U" => boundaryGluingFutureStream W h k
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL

/-- Helper toward Lemma 5.5: a block dart written in the intrinsic code
presentation. -/
@[expose] noncomputable def lMinusBlockDartCode : LMinusBlockDart hqMode →
    LMinusCodeGluedDart rL Q
  | .inl d => lMinusCodePrimedDart rL Q d
  | .inr d => lMinusCodeHattedDart rL Q d

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the intrinsic code of a block dart maps back to
that exact dart class in the geometric gluing. -/
theorem lMinusBlockDartCode_equiv (a : LMinusBlockDart hqMode) :
    lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (lMinusBlockDartCode hqMode a) = ⟦a⟧ := by
  apply (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
  apply Subtype.ext
  cases a with
  | inl d =>
      change (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
        (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (lMinusCodePrimedDart rL Q d))).val =
        (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (⟦Sum.inl d⟧ : LMinusGluedDart hτ hqMode)).val
      rw [lMinusCodeToGluedDartEquiv_equiv hτ hp P hqMode Tpath hfin hleft hk,
        lMinusGluedDartEquiv_val hτ hp P hqMode Tpath hfin hleft hk,
        lMinusCodeGluedDartEquiv_primed hτ hp P hqMode Tpath hfin hleft hk]
      rfl
  | inr d =>
      change (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
        (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (lMinusCodeHattedDart rL Q d))).val =
        (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (⟦Sum.inr d⟧ : LMinusGluedDart hτ hqMode)).val
      rw [lMinusCodeToGluedDartEquiv_equiv hτ hp P hqMode Tpath hfin hleft hk,
        lMinusGluedDartEquiv_val hτ hp P hqMode Tpath hfin hleft hk,
        lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk]
      rfl

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: code presence is exactly directed orientation
after transport to the geometric gluing. -/
theorem lMinusCodeToGluedEdgePresence_iff
    (d : LMinusCodeGluedDart rL Q) :
    lMinusCodeEdgePresent rL Q (PrimedEdgePresent U hτ) d.1 ↔
      lMinusGluedDartOriented hτ hqMode
        (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (d.1, false)) := by
  let E := lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  rcases d with ⟨e, s⟩
  change lMinusCodeEdgePresent rL Q (PrimedEdgePresent U hτ) e ↔
    lMinusGluedDartOriented hτ hqMode (E (e, false))
  constructor
  · rintro (⟨a, ha, he⟩ | ⟨a, ha, he⟩)
    · let b : LMinusBlockDart hqMode := .inl (a, false)
      refine ⟨b, ?_, ⟨ha, rfl⟩⟩
      have hrep : lMinusBlockDartCode hqMode b = (⟦Sum.inl a⟧, false) := by
        change (⟦Sum.inl a⟧,
          false ^^ lMinusCodePrimedSideFlip rL a) = (⟦Sum.inl a⟧, false)
        rw [lMinusCodePrimedSideFlip_observation hτ hfin,
          primedLimitSideFlip_of_present U hτ ha]
        rfl
      calc
        (⟦b⟧ : LMinusGluedDart hτ hqMode) = E (lMinusBlockDartCode hqMode b) :=
          (lMinusBlockDartCode_equiv hτ hp P hqMode Tpath hfin hleft hk b).symm
        _ = E (⟦Sum.inl a⟧, false) := congrArg E hrep
        _ = E (e, false) := congrArg E (Prod.ext he rfl)
    · let b : LMinusBlockDart hqMode :=
        .inr ⟨(a.1, false), a.property⟩
      refine ⟨b, ?_, ⟨ha, rfl⟩⟩
      have hrep : lMinusBlockDartCode hqMode b = (⟦Sum.inr a⟧, false) := rfl
      calc
        (⟦b⟧ : LMinusGluedDart hτ hqMode) = E (lMinusBlockDartCode hqMode b) :=
          (lMinusBlockDartCode_equiv hτ hp P hqMode Tpath hfin hleft hk b).symm
        _ = E (⟦Sum.inr a⟧, false) := congrArg E hrep
        _ = E (e, false) := congrArg E (Prod.ext he rfl)
  · rintro ⟨a, ha, hor⟩
    have hc : lMinusBlockDartCode hqMode a = (e, false) := by
      apply E.injective
      exact (lMinusBlockDartCode_equiv hτ hp P hqMode Tpath hfin hleft hk a).trans ha
    cases a with
    | inl a =>
        rcases hor with ⟨hpresent, _⟩
        have he : (⟦Sum.inl a.1⟧ : LMinusCodeGluedEdge rL Q) = e := by
          have hc' := congrArg Prod.fst hc
          change (⟦Sum.inl a.1⟧ : LMinusCodeGluedEdge rL Q) = e at hc'
          exact hc'
        exact Or.inl ⟨a.1, hpresent, he⟩
    | inr a =>
        have he : (⟦Sum.inr ⟨a.val.1, a.property⟩⟧ :
            LMinusCodeGluedEdge rL Q) = e := by
          have hc' := congrArg Prod.fst hc
          change (⟦Sum.inr ⟨a.val.1, a.property⟩⟧ :
            LMinusCodeGluedEdge rL Q) = e at hc'
          exact hc'
        exact Or.inr ⟨⟨a.val.1, a.property⟩, hor.1, he⟩































end DecodedEdgeIdentification

end DirectedDistances.PaperProofs.Section5
