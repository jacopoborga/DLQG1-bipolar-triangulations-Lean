/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapSides

/-! # Boundary presentation data

four-part boundary word and its cuts are supplied data. Its relation to the
frontier of external faces is a separate proposition and is not part of the
presentation structure. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

variable {V E : Type*}
variable {M : DirectedPlaneMapWithMissing V E}

/-- finite linear presentation of the four consecutive outer-boundary blocks.
The word starts at the beginning of UL; `c0` is zero, and `c1`, `c2`, and
`c3` are the starts of UR, LR, and LL. All four blocks may be empty. A dart's
Boolean is true when it traverses the stored arc parameterization forward. -/
structure FiniteBoundaryPresentation (M : DirectedPlaneMapWithMissing V E) where
  word : List (E × Bool)
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c0_eq_zero : c0 = 0
  cuts_le : c0 ≤ c1 ∧ c1 ≤ c2 ∧ c2 ≤ c3 ∧ c3 ≤ word.length

namespace FiniteBoundaryPresentation

variable (P : FiniteBoundaryPresentation (V := V) (E := E) M)

private def slice (i j : ℕ) : List (E × Bool) :=
  (P.word.drop i).take (j - i)

/-- Helper toward Definition 3.2: the UL block is the first slice of the
supplied cyclic word. -/
def ul : List (E × Bool) := P.slice P.c0 P.c1

/-- Helper toward Definition 3.2: the UR block follows UL. -/
def ur : List (E × Bool) := P.slice P.c1 P.c2

/-- Helper toward Definition 3.2: the LR block follows UR in outer-face
order, hence consists of the reversed opposite darts of the directed LR
path in the finite decomposition convention. -/
def lr : List (E × Bool) := P.slice P.c2 P.c3

/-- Helper toward Definition 3.2: the LL block is the suffix after LR. -/
def ll : List (E × Bool) := P.word.drop P.c3

/-- Helper toward Definition 3.2: the UL block is the corresponding drop/take slice. -/
theorem ul_eq : P.ul = (P.word.drop P.c0).take (P.c1 - P.c0) := by unfold ul slice; rfl

/-- Helper toward Definition 3.2: the UR block is the corresponding drop/take slice. -/
theorem ur_eq : P.ur = (P.word.drop P.c1).take (P.c2 - P.c1) := by unfold ur slice; rfl

/-- Helper toward Definition 3.2: the LR block is the corresponding drop/take slice. -/
theorem lr_eq : P.lr = (P.word.drop P.c2).take (P.c3 - P.c2) := by unfold lr slice; rfl

/-- Helper toward Definition 3.2: the LL block is the suffix after its starting cut. -/
theorem ll_eq : P.ll = P.word.drop P.c3 := by unfold ll; rfl

/-- Helper toward Definition 3.2: the four derived slices concatenate to the
supplied word, including when any of the four blocks is empty. -/
theorem slices_append : P.ul ++ P.ur ++ P.lr ++ P.ll = P.word := by
  have h01 : P.c0 ≤ P.c1 := P.cuts_le.1
  have h12 : P.c1 ≤ P.c2 := P.cuts_le.2.1
  have h23 : P.c2 ≤ P.c3 := P.cuts_le.2.2.1
  have h23slice : P.lr ++ P.ll = P.word.drop P.c2 := by
    dsimp [lr, slice, ll]
    calc
      (P.word.drop P.c2).take (P.c3 - P.c2) ++ P.word.drop P.c3 =
          (P.word.drop P.c2).take (P.c3 - P.c2) ++
            (P.word.drop P.c2).drop (P.c3 - P.c2) := by
              congr 1
              rw [List.drop_drop]
              congr 1
              omega
      _ = P.word.drop P.c2 := List.take_append_drop _ _
  have h12slice : P.ur ++ P.word.drop P.c2 = P.word.drop P.c1 := by
    dsimp [ur, slice]
    calc
      (P.word.drop P.c1).take (P.c2 - P.c1) ++ P.word.drop P.c2 =
          (P.word.drop P.c1).take (P.c2 - P.c1) ++
            (P.word.drop P.c1).drop (P.c2 - P.c1) := by
              congr 1
              rw [List.drop_drop]
              congr 1
              omega
      _ = P.word.drop P.c1 := List.take_append_drop _ _
  have h01slice : P.ul ++ P.word.drop P.c1 = P.word := by
    dsimp [ul, slice]
    rw [P.c0_eq_zero]
    simp only [Nat.sub_zero, List.drop_zero]
    exact List.take_append_drop _ _
  calc
    P.ul ++ P.ur ++ P.lr ++ P.ll = P.ul ++ (P.ur ++ P.word.drop P.c2) := by
      rw [← h23slice]
      simp [List.append_assoc]
    _ = P.ul ++ P.word.drop P.c1 := by rw [h12slice]
    _ = P.word := h01slice

/-- Helper toward Definition 3.2: UL is empty when its two cut indices
coincide. -/
@[simp] theorem ul_eq_nil_of_c0_eq_c1 (h : P.c0 = P.c1) : P.ul = [] := by
  simp [ul, slice, h]

/-- Helper toward Definition 3.2: UR is empty when its two cut indices
coincide. -/
@[simp] theorem ur_eq_nil_of_c1_eq_c2 (h : P.c1 = P.c2) : P.ur = [] := by
  simp [ur, slice, h]

/-- Helper toward Definition 3.2: LR is empty when its two cut indices
coincide. -/
@[simp] theorem lr_eq_nil_of_c2_eq_c3 (h : P.c2 = P.c3) : P.lr = [] := by
  simp [lr, slice, h]

/-- Helper toward Definition 3.2: LL is empty when its starting cut is the
word length. -/
@[simp] theorem ll_eq_nil_of_c3_eq_word_length
    (h : P.c3 = P.word.length) : P.ll = [] := by
  simp [ll, h]

/-- Helper toward Definition 3.2: membership in one of the four slices is
equivalent to membership in the supplied word. -/
theorem mem_ul_or_ur_or_lr_or_ll_iff (d : E × Bool) :
    d ∈ P.ul ∨ d ∈ P.ur ∨ d ∈ P.lr ∨ d ∈ P.ll ↔ d ∈ P.word := by
  rw [← P.slices_append]
  simp only [List.mem_append]
  tauto

end FiniteBoundaryPresentation

/-- Helper toward Definition 3.2: every dart in the derived UR block is a
missing geometric edge. This is a proposition about the supplied data, not a
field of that data. -/
def UROk (P : FiniteBoundaryPresentation (V := V) (E := E) M) : Prop :=
  ∀ d ∈ P.ur, M.toPlaneMapWithMissing.missing d.1

/-- Helper toward Definition 3.2: every dart in the derived LL block is a
missing geometric edge. This is a proposition about the supplied data, not a
field of that data. -/
def LLOk (P : FiniteBoundaryPresentation (V := V) (E := E) M) : Prop :=
  ∀ d ∈ P.ll, M.toPlaneMapWithMissing.missing d.1

/-- Helper toward Definition 3.2: every dart in UL is present, follows its
directed edge orientation, and has an external face on the left of that
directed edge. -/
def ULOk (P : FiniteBoundaryPresentation (V := V) (E := E) M) : Prop :=
  ∀ d ∈ P.ul, ∃ hp : ¬ M.toPlaneMapWithMissing.missing d.1,
    d.2 = M.forward ⟨d.1, hp⟩ ∧
      ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F ∧
        LeftOf M F ⟨d.1, hp⟩

/-- Helper toward Definition 3.2: every dart in LR is present, traverses its
directed edge backwards as in the outer-face word, and has an external face
on the right of the directed edge. -/
def LROk (P : FiniteBoundaryPresentation (V := V) (E := E) M) : Prop :=
  ∀ d ∈ P.lr, ∃ hp : ¬ M.toPlaneMapWithMissing.missing d.1,
    d.2 = !(M.forward ⟨d.1, hp⟩) ∧
      ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F ∧
        RightOf M F ⟨d.1, hp⟩

/-- Helper toward Definition 3.2: an edge lies on an external face frontier
when its whole drawn arc is contained in the frontier of an external face. -/
def ExternalFrontierEdge (M : DirectedPlaneMapWithMissing V E) (e : E) : Prop :=
  ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F ∧
    Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.1

/-- Helper toward Definition 3.2: set-level correspondence of a supplied
word to the external-face frontier. Each frontier edge occurs, each listed
edge is a frontier edge, and a repeated edge is allowed only when both of its
directed sides have external faces; no edge occurs more than twice. -/
def IsBoundaryOrderOf (M : DirectedPlaneMapWithMissing V E)
    (P : FiniteBoundaryPresentation M) : Prop := by
  classical
  exact
    (∀ e, (∃ b : Bool, (e, b) ∈ P.word) ↔ ExternalFrontierEdge M e) ∧
    ∀ e,
      (P.word.filter (fun d => decide (d.1 = e))).length ≤ 2 ∧
      ((P.word.filter (fun d => decide (d.1 = e))).length ≤ 1 ∨
        ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
          ∃ F G : PlaneGraphDrawing.Face (Drawing M),
            (Drawing M).IsExternal F ∧ (Drawing M).IsExternal G ∧
            LeftOf M F ⟨e, hp⟩ ∧ RightOf M G ⟨e, hp⟩)

/-! The first remaining construction obligation is to prove that a concrete
source construction supplies a word satisfying `IsBoundaryOrderOf` and the
four separate block propositions above. It is not asserted for arbitrary
`M` and arbitrary `P`, since `P.word` is supplied data and has no geometric
correctness field. No concrete construction type is available in this module
from which to state that correspondence without adding an assumption.

The tempting general statement

```lean
theorem suppliedPresentation_isBoundaryOrderOf
    {V E : Type*} (M : DirectedPlaneMapWithMissing V E)
    (P : FiniteBoundaryPresentation M) : IsBoundaryOrderOf M P
```

is not valid for arbitrary supplied data and is therefore not introduced. -/

/-- Helper toward Definition 3.2: unfolding equation for ExternalFrontierEdge. -/
theorem externalFrontierEdge_iff (M : DirectedPlaneMapWithMissing V E) (e : E) :
    ExternalFrontierEdge M e <->
      ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F /\
        Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.1 := Iff.rfl

/-- Helper toward Definition 3.2: characterization of the UR missing-edge predicate. -/
theorem UROk_iff (P : FiniteBoundaryPresentation (V := V) (E := E) M) :
    UROk P ↔ ∀ d ∈ P.ur, M.toPlaneMapWithMissing.missing d.1 := by
  unfold UROk
  rfl

/-- Helper toward Definition 3.2: characterization of the LL missing-edge predicate. -/
theorem LLOk_iff (P : FiniteBoundaryPresentation (V := V) (E := E) M) :
    LLOk P ↔ ∀ d ∈ P.ll, M.toPlaneMapWithMissing.missing d.1 := by
  unfold LLOk
  rfl

/-- Helper toward Definition 3.2: characterization of the UL side predicate. -/
theorem ULOk_iff (P : FiniteBoundaryPresentation (V := V) (E := E) M) :
    ULOk P ↔ ∀ d ∈ P.ul, ∃ hp : ¬ M.toPlaneMapWithMissing.missing d.1,
      d.2 = M.forward ⟨d.1, hp⟩ ∧
        ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F ∧
          LeftOf M F ⟨d.1, hp⟩ := by
  unfold ULOk
  rfl

/-- Helper toward Definition 3.2: characterization of the LR side predicate. -/
theorem LROk_iff (P : FiniteBoundaryPresentation (V := V) (E := E) M) :
    LROk P ↔ ∀ d ∈ P.lr, ∃ hp : ¬ M.toPlaneMapWithMissing.missing d.1,
      d.2 = !(M.forward ⟨d.1, hp⟩) ∧
        ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F ∧
          RightOf M F ⟨d.1, hp⟩ := by
  unfold LROk
  rfl

/-- Helper toward Definition 3.2: the defining clauses of `IsBoundaryOrderOf`. -/
theorem IsBoundaryOrderOf_iff (M : DirectedPlaneMapWithMissing V E)
    (P : FiniteBoundaryPresentation M) :
    (letI : DecidableEq E := Classical.decEq E
     IsBoundaryOrderOf M P ↔
       (∀ e, (∃ b : Bool, (e, b) ∈ P.word) ↔ ExternalFrontierEdge M e) ∧
         ∀ e,
           (P.word.filter (fun d => decide (d.1 = e))).length ≤ 2 ∧
           ((P.word.filter (fun d => decide (d.1 = e))).length ≤ 1 ∨
             ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
               ∃ F G : PlaneGraphDrawing.Face (Drawing M),
                 (Drawing M).IsExternal F ∧ (Drawing M).IsExternal G ∧
                   LeftOf M F ⟨e, hp⟩ ∧ RightOf M G ⟨e, hp⟩)) := Iff.rfl

end DirectedDistances.PlanarMap

end
