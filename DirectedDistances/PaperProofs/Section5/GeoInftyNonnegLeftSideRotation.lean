/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideGlued
import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideSplice




public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
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

local notation "M" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "Q" => LPlusGluedDart longest hqMode hτ

/-- Helper toward Lemma 5.5: the deleted prefix's block permutation is the
preceding KMSW stage rotation, transported to its geometric dart subtype.
At `k = 0` the carrier is empty and its rotation is the identity. -/
@[expose] noncomputable def lPlusPrefixRotation (hk : 0 ≤ k) :
    Equiv.Perm (LPlusPrefixDart W h k) := by
  by_cases hkpos : 0 < k
  · let f : LPlusPrefixDart W h k → StageDart
        (kmswStage (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge :=
      lPlusPrefixDartStage (W := W) (h := h) (k := k) hkpos
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact congrArg (fun d : StageDart _ => (d.1.val, d.2)) hab
      · intro d
        refine ⟨lPlusPrefixStageDart (W := W) (h := h) (k := k) hkpos d, ?_⟩
        rfl
    exact Equiv.permCongr (Equiv.ofBijective f hf).symm
      (stageRot (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k - 1))
  · have hkzero : k = 0 := by omega
    subst k
    exact Equiv.refl _

/-- Helper toward Lemma 5.5: the three component dart carriers embed
injectively into the code-glued quotient, retaining both endpoint bits. -/
@[expose] noncomputable def lPlusPrefixGluedDart : LPlusPrefixDart W h k → Q :=
  fun d => ⟦Sum.inl d⟧

@[expose] noncomputable def lPlusPrimedGluedDart : LPlusPrimedDart → Q :=
  fun d => ⟦Sum.inr (Sum.inl d)⟧

@[expose] noncomputable def lPlusHattedGluedDart : LPlusHattedDart M → Q :=
  fun d => ⟦Sum.inr (Sum.inr d)⟧

/-- Helper toward Lemma 5.5: the prefix block embedding is injective on
the quotient because its geometric dart image retains both coordinates. -/
theorem lPlusPrefixGluedDart_injective :
    Function.Injective (lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)) := by
  intro a b hab
  have hf := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
    (Sum.inl a) (Sum.inl b)).mp hab
  change a.val = b.val at hf
  exact Subtype.ext hf

/-- Helper toward Lemma 5.5: the primed block embedding is injective on
the quotient, including its transported endpoint bit. -/
theorem lPlusPrimedGluedDart_injective :
    Function.Injective (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)) := by
  intro a b hab
  have hf := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
    (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b))).mp hab
  exact lPlusPrimedDartImage_injective (hτ := hτ) hqMode hf

/-- Helper toward Lemma 5.5: the hatted block embedding is injective on
the quotient, retaining geometric edge identity and endpoint bit. -/
theorem lPlusHattedGluedDart_injective :
    Function.Injective (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)) := by
  intro a b hab
  have hf := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
    (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b))).mp hab
  exact lPlusHattedDartImage_injective (hτ := hτ) hqMode hf

/-- Helper toward Lemma 5.5: the three extended block rotations compose on
the quotient in prefix-after-primed-after-hatted order. Thus on an upper-left
glued class the primed factor acts before the prefix factor, and on a beta
glued class the hatted factor acts before the primed factor; every factor is
the identity off its embedded block. This specifies a single-valued action
on the shared boundary classes and is a permutation independently of whether
that action agrees there with geometric rotation. -/
@[expose] noncomputable def lPlusGluedSplicedRotation (hk : 0 ≤ k) : Equiv.Perm Q :=
  (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
    (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk).extendDomain
      (Equiv.ofInjective _ (lPlusPrefixGluedDart_injective
        (hτ := hτ) (hqMode := hqMode))) *
    (kmswInfRot (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
      (primedCode_finiteIncidence (boundaryGluingFutureStream W h k) hτ hfin)).extendDomain
      (Equiv.ofInjective _ (lPlusPrimedGluedDart_injective
        (hτ := hτ) (hqMode := hqMode))) *
    (lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
      (Subtype.mk (boundaryFutureHattedPath k W) hqMode)).extendDomain
      (Equiv.ofInjective _ (lPlusHattedGluedDart_injective
        (hτ := hτ) (hqMode := hqMode)))

/-- Helper toward Lemma 5.5: the three-block splice is bijective on the
glued dart quotient without any geometric rotation premise. -/
theorem lPlusGluedSplicedRotation_bijective {hk : 0 ≤ k} :
    Function.Bijective (lPlusGluedSplicedRotation (hτ := hτ) (hp := hp) (P := P)
      (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft)
      (hk := hk)) :=
  (lPlusGluedSplicedRotation (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
    (Tpath := Tpath) (hfin := hfin) (hleft := hleft) (hk := hk)).bijective






























































































end DirectedDistances.PaperProofs.Section5
