/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso2

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

This file computes the initial beta output when the finite upper-left
attachment is empty. The full initial-root rotation iff remains a separate
obligation. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: with no upper-left attachment, the initial beta
dart passes through the primed root corner and then the two remaining block
corrections. -/
theorem lPlusGluedBlockRotation2_beta_output_of_upperLeft_empty
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
    (hk : 0 ≤ k)
    (hzero : (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length = 0) :
    lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft
      (lPlusBetaGluedDart hτ hqMode (0, false)) =
    lPlusHattedExtendedRotation hτ hqMode
      (lPlusBetaCornerRotation hτ hqMode
        (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true))) := by
  let MH := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
  let st := kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
  let es := st.UL.dropLast.reverse
  let betaHat : LPlusHattedDart MH :=
    ⟨((MH.boundary 0).1, false),
      lMinus_hatted_boundary_mem _
        ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let beta := lPlusBetaGluedDart hτ hqMode (0, false)
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let J : LPlusHattedDart MH → ℕ × Bool := fun d =>
    (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
  let PE := lPlusPrefixExtendedRotation (W := W) (h := h) (k := k)
    (H := H) (hLL := hLL) (longest := longest) hτ hp P hqMode Tpath hfin hleft hk
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let TR := kmswInfRot (primedCode
    (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
      (primedCode_finiteIncidence (boundaryGluingFutureStream W h k) hτ hfin)
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let CB := lPlusBetaCornerRotation hτ hqMode
  let HE := lPlusHattedExtendedRotation hτ hqMode
  let U := boundaryGluingFutureStream W h k
  let b0 := primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin 0

  have hnotJ (a : LPlusPrefixDart W h k) : a.val ∉ Set.range J := by
    rintro ⟨d, hd⟩
    have hm : a.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨a.property, ⟨d.val.1, congrArg Prod.fst hd⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm

  have hbetaNotIP : beta ∉ Set.range IP := by
    rintro ⟨a, ha⟩
    have hq : (⟦Sum.inr (Sum.inr betaHat)⟧ :
        LPlusGluedDart longest hqMode hτ) = ⟦Sum.inl a⟧ := by
      change beta = IP a
      exact ha.symm
    have himage := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
      (.inr (.inr betaHat)) (.inl a)).mp hq
    change J betaHat = a.val at himage
    exact hnotJ a ⟨betaHat, himage⟩

  have hbetaNotUL : beta ∉ Set.range
      (lPlusUpperLeftGluedDart hτ hqMode hfin hk) := by
    rintro ⟨i, hi⟩
    have hfalse : i.1.val < 0 := by simpa only [hzero] using i.1.isLt
    omega

  have hPEbeta : PE beta = beta :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hbetaNotIP
  have hCUbeta : CU beta = beta :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hbetaNotUL

  have hbetaRep : IT (b0, true) = beta := by
    apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
      (.inr (.inl (b0, true))) (.inr (.inr betaHat))).mpr
    change lMinusPrimedDartImage hτ (b0, true) =
      (boundaryGluingHatEdgeMap W h k hτ ((MH.boundary 0).1), false)
    rw [lMinusPrimedDartImage_boundary hτ hfin]
    change (boundaryGluingHatEdgeMap W h k hτ
        (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
      (boundaryGluingHatEdgeMap W h k hτ
        (kmswLeftBoundaryEdge (boltzmannKMSWStream
          (pathCode (boundaryFutureHattedPath k W))) 0), false)
    rw [boundaryGluing_decoded_stream W h k hτ]

  have hTEaction (p : ℕ × Bool) : TE (IT p) = IT (TR p) :=
    TR.extendDomain_apply_image
      (Equiv.ofInjective IT (lPlusPrimedGluedDart_injective
        (hτ := hτ) (hqMode := hqMode))) p
  have hTEbeta : TE beta = IT (0, true) := by
    rw [← hbetaRep, hTEaction]
    exact congrArg IT (lMinusPrimedRotation_initial_corner hτ hfin)

  have hblock :
      lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft beta =
        HE (CB (IT (0, true))) := by
    have hnot : ¬ 0 < es.length := by
      rw [show es.length = 0 by simpa [es, st] using hzero]
      omega
    unfold lPlusGluedBlockRotation2
    rw [dite_eq_right hnot]
    change HE (CB (TE (CU (PE beta)))) = HE (CB (IT (0, true)))
    rw [hPEbeta, hCUbeta, hTEbeta]
  change lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft beta =
    HE (CB (IT (0, true)))
  exact hblock









































end DirectedDistances.PaperProofs.Section5
