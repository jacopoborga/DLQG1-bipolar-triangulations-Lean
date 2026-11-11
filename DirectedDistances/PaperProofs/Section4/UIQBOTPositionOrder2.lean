/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPositionOrder

/-! Helper toward Definition 3.2: integer interval order for the exposed
canonical UIQBOT boundary and its labeled presentation. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)

local notation "P" => uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
local notation "pos" => uiqbotCanonicalBoundaryPresentationX_position w hfin htrans hR hL0

/-- Helper toward Definition 3.2: UL advances to the next natural index. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationX_sideNext_upperLeft (n : ℕ) :
    sideNext P (.upperLeft n) = some (.upperLeft (n + 1)) := by
  simp [sideNext, uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]

/-- Helper toward Definition 3.2: LR advances toward its zero index. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationX_sideNext_lowerRight_succ (n : ℕ) :
    sideNext P (.lowerRight (n + 1)) = some (.lowerRight n) := by
  simp [sideNext, uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]

/-- Helper toward Definition 3.2: LR terminates at index zero. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationX_sideNext_lowerRight_zero :
    sideNext P (.lowerRight (0 : ℕ)) = none := by
  simp [sideNext, uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]

/-- Helper toward Definition 3.2: UL occupies the nonnegative positions. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationX_position_upperLeft (n : ℕ) :
    pos (.upperLeft n) = (n : ℤ) := by
  rfl

/-- Helper toward Definition 3.2: LR occupies the negative positions. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationX_position_lowerRight (n : ℕ) :
    pos (.lowerRight n) = -(n : ℤ) - 1 := by
  rfl

/-- Helper toward Definition 3.2: UL has side tag zero. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationX_sideTag_upperLeft (n : ℕ) :
    sideTag P (.upperLeft n) = 0 := by
  rfl

/-- Helper toward Definition 3.2: LR has side tag two. -/
@[simp] theorem uiqbotCanonicalBoundaryPresentationX_sideTag_lowerRight (n : ℕ) :
    sideTag P (.lowerRight n) = 2 := by
  rfl

/-- Helper toward Definition 3.2: distinct boundary occurrences have distinct
integer positions. -/
theorem uiqbotCanonicalBoundaryPresentationX_position_injective :
    Function.Injective pos := by
  intro i j h
  cases i <;> cases j <;> rename_i a b
  all_goals try { first | (change Empty at a; cases a) | (change Empty at b; cases b) }
  all_goals change ℕ at a b
  all_goals simp only [uiqbotCanonicalBoundaryPresentationX_position_upperLeft,
    uiqbotCanonicalBoundaryPresentationX_position_lowerRight] at h
  all_goals first
    | have hab : a = b := by omega
      subst b
      rfl
    | omega

/-- Helper toward Definition 3.2: every integer occurs on the boundary. -/
theorem uiqbotCanonicalBoundaryPresentationX_position_surjective :
    Function.Surjective pos := by
  intro z
  by_cases hz : 0 ≤ z
  · refine ⟨.upperLeft z.toNat, ?_⟩
    rw [uiqbotCanonicalBoundaryPresentationX_position_upperLeft]
    omega
  · refine ⟨.lowerRight (-z - 1).toNat, ?_⟩
    rw [uiqbotCanonicalBoundaryPresentationX_position_lowerRight]
    omega

/-- Helper toward Definition 3.2: within either nonempty side, successors
are exactly the pairs separated by one integer position. -/
theorem uiqbotCanonicalBoundaryPresentationX_sideNext_iff_position
    (i j : InfiniteBoundaryDartIndex P) (htag : sideTag P i = sideTag P j) :
    sideNext P i = some j ↔ pos j = pos i + 1 := by
  cases i <;> cases j <;> rename_i a b
  all_goals try { first | (change Empty at a; cases a) | (change Empty at b; cases b) }
  all_goals change ℕ at a b
  all_goals simp only [uiqbotCanonicalBoundaryPresentationX_sideTag_upperLeft,
    uiqbotCanonicalBoundaryPresentationX_sideTag_lowerRight] at htag
  all_goals try { norm_num at htag }
  · simp only [uiqbotCanonicalBoundaryPresentationX_sideNext_upperLeft,
      uiqbotCanonicalBoundaryPresentationX_position_upperLeft,
      Option.some.injEq]
    constructor
    · intro h
      have hab : a + 1 = b := by cases h; rfl
      omega
    · intro h
      have hab : a + 1 = b := by omega
      exact congrArg (fun n : ℕ =>
        (InfiniteBoundaryDartIndex.upperLeft n : InfiniteBoundaryDartIndex P)) hab
  · cases a with
    | zero =>
        simp only [uiqbotCanonicalBoundaryPresentationX_sideNext_lowerRight_zero,
          uiqbotCanonicalBoundaryPresentationX_position_lowerRight,
          reduceCtorEq, false_iff]
        omega
    | succ a =>
        rw [uiqbotCanonicalBoundaryPresentationX_sideNext_lowerRight_succ
          w hfin htrans hR hL0 a]
        simp only [
          uiqbotCanonicalBoundaryPresentationX_position_lowerRight,
          Option.some.injEq]
        constructor
        · intro h
          have hab : a = b := by cases h; rfl
          omega
        · intro h
          have hab : a = b := by omega
          exact congrArg (fun n : ℕ =>
            (InfiniteBoundaryDartIndex.lowerRight n : InfiniteBoundaryDartIndex P)) hab

/-- Helper toward Definition 3.2: each nonempty side occupies a convex block
of integer positions. -/
theorem uiqbotCanonicalBoundaryPresentationX_position_block
    (i j k : InfiniteBoundaryDartIndex P)
    (hij : pos i ≤ pos j) (hjk : pos j ≤ pos k)
    (hends : sideTag P i = sideTag P k) : sideTag P j = sideTag P i := by
  cases i <;> cases j <;> cases k <;> rename_i a b c
  all_goals try { first
    | (change Empty at a; cases a)
    | (change Empty at b; cases b)
    | (change Empty at c; cases c) }
  all_goals change ℕ at a b c
  all_goals simp only [uiqbotCanonicalBoundaryPresentationX_position_upperLeft,
    uiqbotCanonicalBoundaryPresentationX_position_lowerRight] at hij hjk
  all_goals simp only [uiqbotCanonicalBoundaryPresentationX_sideTag_upperLeft,
    uiqbotCanonicalBoundaryPresentationX_sideTag_lowerRight] at hends ⊢
  all_goals omega

/-- Helper toward Definition 3.2: three pairwise distinct side tags cannot
occur, since only UL and LR have indices. -/
theorem uiqbotCanonicalBoundaryPresentationX_not_three_distinct_sideTags
    (i j k : InfiniteBoundaryDartIndex P)
    (hij : sideTag P i ≠ sideTag P j) (hjk : sideTag P j ≠ sideTag P k)
    (hik : sideTag P i ≠ sideTag P k) : False := by
  cases i <;> cases j <;> cases k <;> rename_i a b c
  all_goals try { first
    | (change Empty at a; cases a)
    | (change Empty at b; cases b)
    | (change Empty at c; cases c) }
  all_goals change ℕ at a b c
  all_goals simp only [uiqbotCanonicalBoundaryPresentationX_sideTag_upperLeft,
    uiqbotCanonicalBoundaryPresentationX_sideTag_lowerRight] at hij hjk hik
  all_goals contradiction

/-- Helper toward Definition 3.2: the given signed position map satisfies
all five integer boundary-order clauses. -/
theorem uiqbotCanonicalBoundaryPresentationX_isBoundaryPositionOrder3 :
    IsBoundaryPositionOrder3 P pos := by
  refine ⟨uiqbotCanonicalBoundaryPresentationX_position_injective
    w hfin htrans hR hL0, ?_, ?_, ?_, ?_⟩
  · exact uiqbotCanonicalBoundaryPresentationX_sideNext_iff_position
      w hfin htrans hR hL0
  · intro i j z _ _
    exact uiqbotCanonicalBoundaryPresentationX_position_surjective
      w hfin htrans hR hL0 z
  · exact uiqbotCanonicalBoundaryPresentationX_position_block
      w hfin htrans hR hL0
  · intro i j k _ _ hij hjk hik
    exact (uiqbotCanonicalBoundaryPresentationX_not_three_distinct_sideTags
      w hfin htrans hR hL0 i j k hij hjk hik).elim

/-- Helper toward Definition 3.2: the unlabeled canonical presentation has
integer boundary interval order. -/
theorem uiqbotCanonicalBoundaryPresentationX_positionOrder3 :
    BoundaryPositionOrder3 P :=
  ⟨pos, uiqbotCanonicalBoundaryPresentationX_isBoundaryPositionOrder3
    w hfin htrans hR hL0⟩

local notation "Q" => uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
local notation "idxEquiv" =>
  uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY w hfin htrans hR hL0

/-- Helper toward Definition 3.2: transport the signed integer positions
through the labeled presentation's boundary-index equivalence. -/
@[expose] def uiqbotCanonicalBoundaryPresentationLabeledX_position :
    InfiniteBoundaryDartIndex Q → ℤ := fun i => pos (idxEquiv i)

/-- Helper toward Definition 3.2: relabeling endpoints preserves all five
integer boundary-order clauses. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_isBoundaryPositionOrder3 :
    IsBoundaryPositionOrder3 Q
      (uiqbotCanonicalBoundaryPresentationLabeledX_position w hfin htrans hR hL0) := by
  change IsBoundaryPositionOrder3 Q (fun i => pos (idxEquiv i))
  obtain ⟨hinj, hnext, hgap, hblock, hcyclic⟩ :=
    uiqbotCanonicalBoundaryPresentationX_isBoundaryPositionOrder3 w hfin htrans hR hL0
  have htag (i : InfiniteBoundaryDartIndex Q) :
      sideTag P (idxEquiv i) = sideTag Q i :=
    uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideTag
      w hfin htrans hR hL0 i
  have hstep (i : InfiniteBoundaryDartIndex Q) :
      Option.map idxEquiv (sideNext Q i) = sideNext P (idxEquiv i) :=
    uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideNext
      w hfin htrans hR hL0 i
  refine ⟨hinj.comp (idxEquiv).injective, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have htags : sideTag P (idxEquiv i) = sideTag P (idxEquiv j) := by
      rw [htag i, htag j]
      exact hij
    constructor
    · intro h
      apply (hnext (idxEquiv i) (idxEquiv j) htags).mp
      rw [← hstep i, h]
      rfl
    · intro h
      have hm : Option.map idxEquiv (sideNext Q i) = some (idxEquiv j) :=
        (hstep i).trans ((hnext (idxEquiv i) (idxEquiv j) htags).mpr h)
      cases hs : sideNext Q i with
      | none => rw [hs] at hm; cases hm
      | some k =>
          rw [hs] at hm
          have hkj : k = j := (idxEquiv).injective (Option.some.inj hm)
          exact congrArg some hkj
  · intro i j z hiz hzj
    obtain ⟨k, hk⟩ := hgap (idxEquiv i) (idxEquiv j) z hiz hzj
    refine ⟨(idxEquiv).symm k, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hk
  · intro i j k hij hjk hends
    have htags : sideTag P (idxEquiv i) = sideTag P (idxEquiv k) := by
      rw [htag i, htag k]
      exact hends
    have hmiddle := hblock (idxEquiv i) (idxEquiv j) (idxEquiv k) hij hjk htags
    simpa only [htag] using hmiddle
  · intro i j k hij hjk hneij hnejk hneik
    have htagsij : sideTag P (idxEquiv i) ≠ sideTag P (idxEquiv j) := by
      simpa only [htag] using hneij
    have htagsjk : sideTag P (idxEquiv j) ≠ sideTag P (idxEquiv k) := by
      simpa only [htag] using hnejk
    have htagsik : sideTag P (idxEquiv i) ≠ sideTag P (idxEquiv k) := by
      simpa only [htag] using hneik
    have h := hcyclic (idxEquiv i) (idxEquiv j) (idxEquiv k)
      hij hjk htagsij htagsjk htagsik
    simpa only [htag] using h

/-- Helper toward Definition 3.2: the labeled canonical presentation has
integer boundary interval order. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_positionOrder3 :
    BoundaryPositionOrder3 Q :=
  ⟨uiqbotCanonicalBoundaryPresentationLabeledX_position w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_isBoundaryPositionOrder3
      w hfin htrans hR hL0⟩

end DirectedDistances.PaperProofs.Section4

end
