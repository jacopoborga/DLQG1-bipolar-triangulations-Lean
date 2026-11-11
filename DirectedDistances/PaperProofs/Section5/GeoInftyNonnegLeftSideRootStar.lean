/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff11
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation4

/-! Helper toward Lemma 5.5: stopped-prefix incidence at the boundary root. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: two left steps followed by a down step leave
an earlier incoming edge at the sink outside the upper-left attachment.
This is a finite-stage obstruction to the proposed root-star classification. -/
theorem lPlusRootStar_left_left_down_stage
    (u : ℕ → Fin 3) (hc₀ : u 0 = 0) (hc₁ : u 1 = 0) (hc₂ : u 2 = 2) :
    (kmswStage u 2).nextEdge = 5 ∧
    (kmswStage u 2).east 1 = 1 ∧
    (kmswStage u 3).active = 5 ∧
    (kmswStage u 3).UL.dropLast.reverse = [3] := by
  simp [kmswStage, hc₀, hc₁, hc₂, kmswStep, kmswCodeStep,
    kmswStepOfStep, kmswInit, State.addEdge]

/-- Helper toward Lemma 5.5: the first right-coordinate hit after
left/left/down is stage three, independently of the remaining stream. -/
theorem lPlusRootStar_hit_one_of_left_left_down
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    (hc₀ : shiftedStream W 0 0 = 0) (hc₁ : shiftedStream W 0 1 = 0)
    (hc₂ : shiftedStream W 0 2 = 2) :
    boundaryHitTime (shiftedStream W 0) h 1 = 3 := by
  let u := shiftedStream W 0
  have hr : R u 3 = -1 := by
    simp [R, Finset.sum_range_succ, u, hc₀, hc₁, hc₂, lazyTwoDimensionalStep]
  have hf : Nat.find (h.rightHit 1 (by omega)) = 3 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' _ hr
    · have hs := Nat.find_spec (h.rightHit 1 (by omega))
      by_contra hn
      have he : Nat.find (h.rightHit 1 (by omega)) = 0 ∨
          Nat.find (h.rightHit 1 (by omega)) = 1 ∨
          Nat.find (h.rightHit 1 (by omega)) = 2 := by omega
      rcases he with he | he | he <;> rw [he] at hs
      · change (0 : ℤ) = -1 at hs
        omega
      · simp [R, hc₀, lazyTwoDimensionalStep] at hs
      · simp [R, Finset.sum_range_succ, hc₀, hc₁, lazyTwoDimensionalStep] at hs
  simpa [boundaryHitTime] using hf

/-- Helper toward Lemma 5.5: on left/left/down, the prefix dart `(1,true)`
is root-incident and belongs to neither alternative of the recorded
RotationIff13 classification. The hypotheses specify only the three codes
and the already required boundary-hit witnesses. -/
theorem lPlusRootStar_left_left_down_obstruction
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    (hc₀ : shiftedStream W 0 0 = 0) (hc₁ : shiftedStream W 0 1 = 0)
    (hc₂ : shiftedStream W 0 2 = 2) :
    ∃ d : LPlusPrefixDart W h 1,
      d.val = (1, true) ∧
      kmswLimitDartVertex (shiftedStream W 0) d.val =
        boundaryVertex (shiftedStream W 0) h 1 ∧
      ¬ ((∃ i : Fin (List.reverse (List.dropLast (State.UL
          (kmswStage (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h 1))))).length,
          ∃ b : Bool, d.val =
            ((List.reverse (List.dropLast (State.UL
              (kmswStage (shiftedStream W 0)
                (boundaryHitTime (shiftedStream W 0) h 1)))))[i.val], b)) ∨
        d.val = (0, true)) := by
  have ht := lPlusRootStar_hit_one_of_left_left_down (h := h) hc₀ hc₁ hc₂
  have hstage := lPlusRootStar_left_left_down_stage (shiftedStream W 0) hc₀ hc₁ hc₂
  have hm : 1 ∈ boundaryGluingPrefixMinusEdges W h 1 := by
    rw [lPlusPrefixMinusEdges_eq_previousStage (by omega : 0 < (1 : ℤ))]
    change 1 < (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h 1 - 1)).nextEdge
    rw [ht]
    change 1 < (kmswStage (shiftedStream W 0) 2).nextEdge
    rw [hstage.1]
    omega
  let d : LPlusPrefixDart W h 1 := ⟨(1, true), hm⟩
  refine ⟨d, rfl, ?_, ?_⟩
  · change edgeEast (shiftedStream W 0) 1 = boundaryVertex (shiftedStream W 0) h 1
    rw [boundaryVertex_one]
    simp [edgeEast, kmswStage, hc₀, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswInit, State.addEdge]
  · rintro (⟨i, b, hi⟩ | hi)
    · have he := congrArg Prod.fst hi
      have hm' : 1 ∈ (kmswStage (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h 1)).UL.dropLast.reverse := by
        change 1 = _ at he
        rw [he]
        exact List.getElem_mem i.isLt
      rw [ht, hstage.2.2.2] at hm'
      norm_num at hm'
    · have he := congrArg Prod.fst hi
      change 1 = 0 at he
      omega





















































/- Validation: the temporary in-file probes reported [propext, Quot.sound]
for lPlusRootStar_left_left_down_stage, and [propext, Classical.choice,
Quot.sound] for the hit-time and prefix-dart obstruction theorems.
The initial import check exited 0; one development check exited 1 because
of a dependent rewrite and the corrected development check exited 0. -/

end DirectedDistances.PaperProofs.Section5
