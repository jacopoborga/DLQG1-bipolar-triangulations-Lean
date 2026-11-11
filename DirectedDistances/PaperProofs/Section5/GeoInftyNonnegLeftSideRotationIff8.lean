/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff6

/-! Helper toward Lemma 5.5: the repaired terminal upper-left port has its -/

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
    (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "w" => shiftedStream W 0
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))
local notation "F" => lPlusBlockDartImage
  (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
local notation "S" => m0GeodesicSide hp P ThinMapSide.left

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the repaired terminal port has the geometric
left-side successor, by the complete first-return characterization. -/
theorem lPlusGluedCorrectedRotation2_terminal_side_rotation
    (hn : 0 < (ULedges).length) :
    let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
      (⟨(ULedges).length - 1, by omega⟩, false)
    ∀ e : Q,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk t = e ↔
        (S).rotation (D t).val (D e).val := by
  dsimp only
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(ULedges).length - 1, by omega⟩, false)
  have hmem (q : Q) : (D q).val ∈ Set.range F := by
    rw [← lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
    exact (lPlusGluedCodeImageEquiv hτ hqMode q).property
  have hret := lPlusGluedCorrectedRotation2_terminal_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk hn
  dsimp only at hret
  change ∀ e : Q,
    lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk t = e ↔
      ∃ n : ℕ, 0 < n ∧
        (kmswInfRot w (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n] (D t).val =
          (D e).val ∧
        ∀ j : ℕ, 0 < j → j < n →
          ((kmswInfRot w (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[j] (D t).val).1 ∉
            (S).edges
  intro e
  constructor
  · intro he
    obtain ⟨n, hnpos, hend, hgap⟩ := hret
    refine ⟨n, hnpos, ?_, ?_⟩
    · have heD := congrArg (fun q : Q => (D q).val) he
      rw [heD] at hend
      exact hend
    · intro j hj hjn hs
      apply hgap j hj hjn
      rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
      exact hs
  · intro hside
    obtain ⟨n, hnpos, hend, hgap⟩ := hside
    have hgapF : ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[j] (D t).val ∉
          Set.range F := by
      intro j hj hjn hm
      rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk] at hm
      exact hgap j hj hjn hm
    obtain ⟨m, hmpos, hmend, hmgap⟩ := hret
    have hmn : n = m := by
      apply Nat.le_antisymm
      · by_contra hlt
        apply hgapF m hmpos (by omega)
        rw [hmend]
        exact hmem _
      · by_contra hlt
        apply hmgap n hnpos (by omega)
        rw [hend]
        exact hmem e
    have heq : (D e).val =
        (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk t)).val := by
      calc
        (D e).val =
            (kmswInfRot w (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n] (D t).val := hend.symm
        _ = (kmswInfRot w (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[m] (D t).val := by rw [hmn]
        _ = (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk t)).val := hmend
    apply (D).injective
    apply Subtype.ext
    exact heq.symm



























































end DirectedDistances.PaperProofs.Section5
