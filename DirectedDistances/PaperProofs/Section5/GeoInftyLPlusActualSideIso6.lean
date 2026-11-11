/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso5

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

This file transfers the beta-port block computation to the actual-side
rotation when the finite upper-left attachment is nonempty. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: with a nonempty upper-left attachment, the
canonical beta dart has the actual left-side rotation successor given by the
initial upper-left east dart. -/
theorem lPlusGluedCorrectedRotation2_beta_initial_vertex_rotation_iff_nonempty
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
    (p : ℕ × Bool)
    (hd : kmswLimitDartVertex (shiftedStream W 0)
      (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
        (lPlusBetaGluedDart hτ hqMode p)).val =
          boundaryVertex (shiftedStream W 0) h k)
    (hn : 0 < (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length) :
    ∀ e : LPlusGluedDart longest hqMode hτ,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (lPlusBetaGluedDart hτ hqMode p) = e ↔
        (m0GeodesicSide hp P .left).rotation
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
            (lPlusBetaGluedDart hτ hqMode p)).val
          (lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk e).val := by
  let D := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  let beta := lPlusBetaGluedDart hτ hqMode (0, false)
  let out := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)
  have hcanonical : lPlusBetaGluedDart hτ hqMode p = beta :=
    lPlusBetaGluedDart_initial_root_eq_canonical hτ hp P hqMode Tpath hfin hleft
      hk p hd
  rw [hcanonical]
  have hblock :
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk beta = out := by
    rw [lPlusGluedCorrectedRotation2_eq_blockRotation2
      hτ hqMode hfin hk hp P Tpath hleft]
    apply D.injective
    exact (lPlusGluedBlockRotation2_beta_initial_output
      hτ hp P hqMode Tpath hfin hleft hk).1 hn
  let MH := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
  let ULedges := List.reverse (List.dropLast (State.UL
    (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k))))
  have hstep :
      (kmswInfRot (shiftedStream W 0) (H.1 0)) (D beta).val = (D out).val := by
    change kmswInfRot (shiftedStream W 0) (H.1 0)
      (boundaryGluingHatEdgeMap W h k hτ (MH.boundary 0).1, false) =
        (ULedges[0], true)
    have hb : (MH.boundary 0).1 = kmswLeftBoundaryEdge
        (hatCodes (boundaryGluingFutureStream W h k) hτ) 0 := by
      change kmswLeftBoundaryEdge (boltzmannKMSWStream
        (pathCode (boundaryFutureHattedPath k W))) 0 = _
      rw [boundaryGluing_decoded_stream W h k hτ]
    rw [hb]
    exact lPlus_upperLeft_initial_beta_successor (H := H) hτ hqMode hfin hk hn
  have hmemEdge : (D out).val.1 ∈ (m0GeodesicSide hp P .left).edges :=
    (D out).property
  intro e
  constructor
  · intro he
    have heout : out = e := hblock.symm.trans he
    change ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n]
          (D beta).val = (D e).val ∧
        ∀ j : ℕ, 0 < j → j < n →
          ((kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[j]
            (D beta).val).1 ∉ (m0GeodesicSide hp P .left).edges
    refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
    · simpa only [Function.iterate_one] using
        hstep.trans (congrArg (fun q => (D q).val) heout)
    · intro j hj hjlt
      omega
  · intro hrot
    change ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n]
          (D beta).val = (D e).val ∧
        ∀ j : ℕ, 0 < j → j < n →
          ((kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[j]
            (D beta).val).1 ∉ (m0GeodesicSide hp P .left).edges at hrot
    obtain ⟨n, hnpos, hend, hgap⟩ := hrot
    have hiter :
        (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[1]
          (D beta).val = (D out).val := by
      simpa only [Function.iterate_one] using hstep
    have hn1 : n = 1 := by
      by_contra hne
      have hlt : 1 < n := by omega
      apply hgap 1 Nat.zero_lt_one hlt
      rw [hiter]
      exact hmemEdge
    have heout : e = out := by
      apply D.injective
      apply Subtype.ext
      calc
        (D e).val =
            (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n]
              (D beta).val := hend.symm
        _ = (kmswInfRot (shiftedStream W 0) (H.1 0)) (D beta).val := by
          rw [hn1]
          rfl
        _ = (D out).val := hstep
    exact hblock.trans heout.symm







































































































































































end DirectedDistances.PaperProofs.Section5

