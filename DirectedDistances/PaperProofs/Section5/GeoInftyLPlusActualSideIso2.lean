/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation8
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff11
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRootStar2
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideSplice

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

This file develops the rotation field for the L-plus actual-side marked
isomorphism by proving the canonical beta dart's output when the upper-left
attachment is nonempty. The remaining all-dart initial-root and boundary-star
rotation iff statements remain recorded with full binders in
`GeoInftyNonnegLeftSideRotationIff11.lean:720` and
`GeoInftyNonnegLeftSideRotationIff8.lean:135`; this helper assumes neither. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the beta dart's block successor is the first
upper-left attachment dart whenever that attachment is nonempty. -/
theorem lPlusGluedBlockRotation2_beta_output_initial_upperLeft
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
    (hn : 0 < (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length) :
    lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
      (lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft
        (lPlusBetaGluedDart hτ hqMode (0, false))) =
    lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
      (lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)) := by
  let MH := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
  let st := kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
  let es := st.UL.dropLast.reverse
  let iLast : Fin es.length := ⟨es.length - 1, by
    have hlen : 0 < es.length := by simpa [es, st] using hn
    omega⟩
  let betaHat : LPlusHattedDart MH :=
    ⟨((MH.boundary 0).1, false),
      lMinus_hatted_boundary_mem _
        ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let beta := lPlusBetaGluedDart hτ hqMode (0, false)
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let UL := lPlusUpperLeftGluedDart hτ hqMode hfin hk
  let F := lPlusBlockDartImage (M := MH) hτ
  let J : LPlusHattedDart MH → ℕ × Bool := fun d =>
    (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
  let d0 := UL (⟨0, hn⟩, true)
  let t := UL (iLast, false)
  let PE := lPlusPrefixExtendedRotation (W := W) (h := h) (k := k)
    (H := H) (hLL := hLL) (longest := longest) hτ hp P hqMode Tpath hfin hleft hk
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let TR := kmswInfRot (primedCode
    (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
      (primedCode_finiteIncidence (boundaryGluingFutureStream W h k) hτ hfin)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let Beta := lPlusBetaGluedDart hτ hqMode
  let CB := lPlusBetaCornerRotation hτ hqMode
  let HE := lPlusHattedExtendedRotation hτ hqMode
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
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

  have hbetaNotUL : beta ∉ Set.range UL := by
    rintro ⟨i, hi⟩
    let a : LPlusPrefixDart W h k :=
      ⟨(es[i.1], i.2), lPlusUpperLeftEdge_mem_prefix hτ hfin hk i.1⟩
    have hULIP : UL i = IP a := rfl
    exact hbetaNotIP ⟨a, hULIP.trans hi⟩

  let ha0 : LPlusPrefixDart W h k :=
    ⟨(es[0], true),
      lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
  have hd0IP : d0 = IP ha0 := by
    change IP ⟨(es[0], true), _⟩ = IP ha0
    congr 1

  have hd0NotIH : d0 ∉ Set.range IH := by
    rintro ⟨b, hbd⟩
    have himage := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
      (.inl ha0) (.inr (.inr b))).mp (hd0IP.symm.trans hbd.symm)
    change ha0.val = J b at himage
    exact hnotJ ha0 ⟨b, himage.symm⟩

  have hd0NotBeta : d0 ∉ Set.range Beta := by
    rintro ⟨p, hp⟩
    let b : LPlusHattedDart MH :=
      ⟨((MH.boundary p.1).1, p.2),
        lMinus_hatted_boundary_mem _
          ⟨boundaryFutureHattedPath k W, hqMode⟩ p.1⟩
    have hBeta : Beta p = IH b := rfl
    exact hd0NotIH ⟨b, hBeta.symm.trans hp⟩

  have hPEbeta : PE beta = beta :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hbetaNotIP
  have hCUbeta : CU beta = beta :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hbetaNotUL
  have hCBd0 : CB d0 = d0 :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hd0NotBeta
  have hHEd0 : HE d0 = d0 :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ hd0NotIH

  have hTR0 : TR (0, true) = (b0, true) :=
    lPlusPrimedRotation_initial_root_corner hτ hfin
  have hTRb0 : TR (b0, true) = (0, true) :=
    lMinusPrimedRotation_initial_corner hτ hfin
  have hTEaction (p : ℕ × Bool) : TE (IT p) = IT (TR p) :=
    TR.extendDomain_apply_image
      (Equiv.ofInjective IT (lPlusPrimedGluedDart_injective
        (hτ := hτ) (hqMode := hqMode))) p
  have hd0Primed : d0 = IT (0, true) :=
    lPlusUpperLeftGluedDart_initial_eq_primed_root hτ hqMode hfin hk hn
  have hTEbeta : TE beta = d0 := by
    have hTEd0beta := lPlusPrimedExtendedRotation_initial_east
      hτ hqMode hfin hk hn
    have hBetarep : beta = IT (b0, true) := by
      calc
        beta = TE d0 := hTEd0beta.symm
        _ = TE (IT (0, true)) := congrArg TE hd0Primed
        _ = IT (TR (0, true)) := hTEaction (0, true)
        _ = IT (b0, true) := congrArg IT hTR0
    calc
      TE beta = TE (IT (b0, true)) := congrArg TE hBetarep
      _ = IT (TR (b0, true)) := hTEaction (b0, true)
      _ = IT (0, true) := congrArg IT hTRb0
      _ = d0 := hd0Primed.symm

  have hCbeta : C beta = d0 := by
    change HE (CB (TE (CU (PE beta)))) = d0
    rw [hPEbeta, hCUbeta, hTEbeta, hCBd0, hHEd0]

  have hbetat : beta ≠ t := by
    intro he
    apply hbetaNotUL
    have hlast : UL (iLast, false) = t := rfl
    exact ⟨(iLast, false), hlast.trans he.symm⟩
  have hCt : C t ≠ d0 := by
    intro he
    apply hbetat
    exact (lPlusGluedCorrectedRotation_bijective
      hτ hp P hqMode Tpath hfin hleft hk).1 (hCbeta.trans he.symm)
  have hTEt : TE t ≠ d0 := by
    intro he
    apply hbetat
    exact TE.injective (hTEbeta.trans he.symm)
  have hswap : Equiv.swap (C t) (TE t) d0 = d0 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact Ne.symm hCt
    · exact Ne.symm hTEt

  have hblock :
      lPlusGluedBlockRotation2 hτ hqMode hfin hk hp P Tpath hleft beta = d0 := by
    unfold lPlusGluedBlockRotation2
    rw [dite_eq_left hn, Equiv.Perm.mul_apply]
    change Equiv.swap (C t) (TE t) (C beta) = d0
    rw [hCbeta]
    exact hswap

  exact congrArg
    (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk) hblock

end DirectedDistances.PaperProofs.Section5
