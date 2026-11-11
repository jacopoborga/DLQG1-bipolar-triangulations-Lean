/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso11

/-! Formalization-internal decoder analysis, not a manuscript change.
This file studies the conditional terminal lower-left obstruction for the
nonnegative left-side code. It makes no paper-completion claim. -/

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

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "C" => lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
local notation "w" => shiftedStream W 0
local notation "ULedges" => List.reverse (List.dropLast
  (State.UL (kmswStage w (boundaryHitTime w h k))))

/-- Helper toward Lemma 5.5: exchange two code-selected outputs after
corrected rotation 2. The two dart arguments are quotient code darts; the
definition does not inspect the actual-side rotation. -/
@[expose] noncomputable def lPlusGluedCorrectedRotation3 (d t : Q) : Equiv.Perm Q :=
  Equiv.swap d t * C

/-- Helper toward Lemma 5.5: the third candidate agrees with corrected
rotation 2 whenever that candidate's output is outside the exchanged pair. -/
theorem lPlusGluedCorrectedRotation3_eq_rotation2_of_ne
    (d t x : Q) (hxd : C x ≠ d) (hxt : C x ≠ t) :
    lPlusGluedCorrectedRotation3 hτ hp P hqMode Tpath hfin hleft hk d t x = C x := by
  change Equiv.swap d t (C x) = C x
  exact Equiv.swap_apply_of_ne_of_ne hxd hxt

/-- Helper toward Lemma 5.5: for the left/down prefix, the code-selected
transposition sends the old lower-left dart to its actual side successor.
The witness stream and all decoder binders remain explicit. -/
theorem lPlusGluedCorrectedRotation3_transports_left_down
    (hk₁ : k = 1) (hc₀ : w 0 = 0) (hc₁ : w 1 = 2) :
    ∃ d t : Q,
      (D d).val = (2, false) ∧
      (D t).val = (1, false) ∧
      lPlusGluedCorrectedRotation3 hτ hp P hqMode Tpath hfin hleft hk d t d = t ∧
      (m0GeodesicSide hp P ThinMapSide.left).rotation (D d).val (D t).val := by
  subst k
  let D₁ := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  let C₁ := lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
  let es := List.reverse (List.dropLast (State.UL
    (kmswStage w (boundaryHitTime w h 1))))
  have ht := lPlus_hit_one_of_left_down (h := h) hc₀ hc₁
  have hUL : es = [1] := by
    dsimp only [es]
    rw [ht]
    simp [kmswStage, hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  have hn : 0 < es.length := by rw [hUL]; decide
  let i : Fin es.length := ⟨es.length - 1, by omega⟩
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, false)
  have htv : (D₁ t).val = (1, false) := by
    change (es[i.val], false) = _
    simp [i, hUL]
  obtain ⟨d, hdval, hfix, _⟩ :=
    lPlusGluedCorrectedRotation2_terminal_nonport_obstruction
      hτ hp P hqMode Tpath hfin hleft hk rfl hc₀ hc₁
  have hσ := (lPlus_first_left_lowerLeft_rotations (H := H) hc₀).1
  let S₁ := m0GeodesicSide hp P ThinMapSide.left
  have hrot : (S₁).rotation (D₁ d).val (D₁ t).val := by
    refine ⟨1, by omega, ?_, ?_⟩
    · rw [hdval]
      change kmswInfRot w (H.1 0) (2, false) = (D₁ t).val
      exact hσ.trans htv.symm
    · intro j hj hj1
      omega
  have hnew : lPlusGluedCorrectedRotation3 hτ hp P hqMode Tpath hfin hleft hk d t d = t := by
    change Equiv.swap d t (C₁ d) = t
    rw [hfix]
    simp
  exact ⟨d, t, hdval, (by simpa only [D₁] using htv), hnew, (by simpa only [D₁] using hrot)⟩

end DirectedDistances.PaperProofs.Section5


















































