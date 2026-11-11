/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.List

import Mathlib.Tactic.FinCases

/-! # Cyclic outer boundaries

An outer boundary is represented by a nonempty, duplicate-free cyclic word of
darts. The list representative keeps singleton face cycles visible, including
the one-edge initial map (`defn:bound-edges`, -/

public section
namespace DirectedDistances.PlanarMap

open Equiv List

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A finite linear representative of a nonempty cyclic word used to enumerate
the external boundary (`defn:bound-edges`, -/
structure NonemptyWord (D : Type*) where
  letters : List D
  nonempty : letters ≠ []
  nodup : letters.Nodup

/-- `B` is an exact cyclic enumeration of the distinguished outer face:
its letters are precisely the outer darts, and the cyclic permutation
associated to the word agrees with `faceSucc` on every letter -/
@[expose] def IsOuterCycle (M : DirectedMapWithMissing D) (B : NonemptyWord D) : Prop :=
  (∀ d ∈ B.letters, M.IsOuter d) ∧
  (∀ d, M.IsOuter d → d ∈ B.letters) ∧
  (∀ d ∈ B.letters,
    M.toCombinatorialMap.faceSucc d = B.letters.formPerm d)

/-- In an exact outer word, membership is equivalent to being on the
distinguished outer face (`defn:bound-edges`, -/
theorem mem_iff_isOuter (M : DirectedMapWithMissing D) (B : NonemptyWord D)
    (hB : IsOuterCycle M B) (d : D) : d ∈ B.letters ↔ M.IsOuter d := by
  exact ⟨hB.1 d, hB.2.1 d⟩

/-- Exact cyclic enumerations of the same outer face differ only by a
rotation of their list representatives. -/
theorem isOuterCycle_unique_up_to_rotation (M : DirectedMapWithMissing D)
    (B C : NonemptyWord D) (hB : IsOuterCycle M B) (hC : IsOuterCycle M C) :
    B.letters ~r C.letters := by
  classical
  have hmem : ∀ d, d ∈ B.letters ↔ d ∈ C.letters := by
    intro d
    rw [mem_iff_isOuter M B hB, mem_iff_isOuter M C hC]
  have hperm : B.letters.formPerm = C.letters.formPerm := by
    ext d
    by_cases hd : d ∈ B.letters
    · calc
        B.letters.formPerm d = M.toCombinatorialMap.faceSucc d := (hB.2.2 d hd).symm
        _ = C.letters.formPerm d := hC.2.2 d ((hmem d).mp hd)
    · have hd' : d ∉ C.letters := fun hc => hd ((hmem d).mpr hc)
      rw [List.formPerm_apply_of_notMem hd, List.formPerm_apply_of_notMem hd']
  rcases (List.formPerm_eq_formPerm_iff B.nodup C.nodup).mp hperm with hrot | hsmall
  · exact hrot
  · have hBsingle : ∃ b, B.letters = [b] := by
      cases hBlist : B.letters with
      | nil =>
        have hn := B.nonempty
        rw [hBlist] at hn
        exact (hn rfl).elim
      | cons b bs =>
        have hlen : (b :: bs).length ≤ 1 := by simpa [hBlist] using hsmall.1
        cases bs with
        | nil => exact ⟨b, by simp⟩
        | cons x xs => simp at hlen
    have hCsingle : ∃ c, C.letters = [c] := by
      cases hClist : C.letters with
      | nil =>
        have hn := C.nonempty
        rw [hClist] at hn
        exact (hn rfl).elim
      | cons c cs =>
        have hlen : (c :: cs).length ≤ 1 := by simpa [hClist] using hsmall.2
        cases cs with
        | nil => exact ⟨c, by simp⟩
        | cons x xs => simp at hlen
    rcases hBsingle with ⟨b, hBlist⟩
    rcases hCsingle with ⟨c, hClist⟩
    have hbc : b = c := by
      have hb : b ∈ B.letters := by simp [hBlist]
      have hc : b ∈ C.letters := (hmem b).mp hb
      simpa [hClist] using hc
    subst c
    rw [hBlist, hClist]

/-- A list contains exactly the elements of a set, with no assertion about
their order. Its order as a block is supplied by the surrounding cyclic word -/
@[expose]
def EnumeratesSet (xs : List D) (s : Set D) : Prop :=
  ∀ d, d ∈ xs ↔ d ∈ s

/-- A block containing only missing darts -/
@[expose]
def MissingRun (M : DirectedMapWithMissing D) (xs : List D) : Prop :=
  ∀ d ∈ xs, M.missing d

/-- A four-arc witness: an exact outer word, cyclically divided into the
upper-left present boundary, upper-right missing run, lower-right present
boundary, and lower-left missing run (`defn:bound-edges`, -/
@[expose]
def FourArcsWitness (M : DirectedMapWithMissing D) (B : NonemptyWord D)
    (ul ur lr ll : List D) : Prop :=
  IsOuterCycle M B ∧
  B.letters ~r (ul ++ ur ++ lr ++ ll) ∧
  EnumeratesSet ul M.ulDarts ∧
  EnumeratesSet lr M.lrDarts ∧
  MissingRun M ur ∧
  MissingRun M ll

/-- The outer boundary admits four consecutive arcs, with the present arcs
listed in their outer-face order and the other two arcs containing only
uniqueness is restricted to the domain where both present arcs are nonempty:
when one is empty, adjacent missing blocks may not have a distinguished cut. -/
@[expose]
def FourArcs (M : DirectedMapWithMissing D) : Prop :=
  ∃ (B : NonemptyWord D) (ul ur lr ll : List D),
    FourArcsWitness M B ul ur lr ll

/-- The upper-right missing run following the upper-left block, ranging over
all four-arc witnesses (`defn:bound-edges`, -/
@[expose] def urDarts (M : DirectedMapWithMissing D) : Set D :=
  {d | ∃ (B : NonemptyWord D) (ul ur lr ll : List D),
    FourArcsWitness M B ul ur lr ll ∧ d ∈ ur}

/-- The lower-left missing run following the lower-right block, ranging over
all four-arc witnesses (`defn:bound-edges`, -/
@[expose] def llDarts (M : DirectedMapWithMissing D) : Set D :=
  {d | ∃ (B : NonemptyWord D) (ul ur lr ll : List D),
    FourArcsWitness M B ul ur lr ll ∧ d ∈ ll}

/-- The initial one-edge directed map has its two present boundary arcs and -/
theorem singleEdgeDirected_fourArcs :
    FourArcs (D := Fin 2) CombinatorialMap.singleEdgeDirected := by
  classical
  let B : NonemptyWord (Fin 2) :=
    ⟨[0, 1], by simp, by simp⟩
  have ho0 : CombinatorialMap.singleEdgeDirected.IsOuter (0 : Fin 2) := by
    change CombinatorialMap.singleEdge.faceSucc.SameCycle 0 0
    exact Equiv.Perm.SameCycle.rfl
  have ho1 : CombinatorialMap.singleEdgeDirected.IsOuter (1 : Fin 2) := by
    change CombinatorialMap.singleEdge.faceSucc.SameCycle 0 1
    exact ⟨1, by simp [CombinatorialMap.singleEdge, CombinatorialMap.faceSucc]⟩
  have hul0 : (0 : Fin 2) ∈ DirectedMapWithMissing.ulDarts
      CombinatorialMap.singleEdgeDirected := by
    simp only [DirectedMapWithMissing.ulDarts, Set.mem_ofPred_eq]
    exact ⟨by simp [CombinatorialMap.singleEdgeDirected],
      by simp [CombinatorialMap.singleEdgeDirected], ho0⟩
  have hul1 : (1 : Fin 2) ∉ DirectedMapWithMissing.ulDarts
      CombinatorialMap.singleEdgeDirected := by
    simp [DirectedMapWithMissing.ulDarts, CombinatorialMap.singleEdgeDirected]
  have hlr0 : (0 : Fin 2) ∉ DirectedMapWithMissing.lrDarts
      CombinatorialMap.singleEdgeDirected := by
    simp [DirectedMapWithMissing.lrDarts, CombinatorialMap.singleEdgeDirected]
  have hlr1 : (1 : Fin 2) ∈ DirectedMapWithMissing.lrDarts
      CombinatorialMap.singleEdgeDirected := by
    simp only [DirectedMapWithMissing.lrDarts, Set.mem_ofPred_eq]
    exact ⟨by simp [CombinatorialMap.singleEdgeDirected],
      by simp [CombinatorialMap.singleEdgeDirected], ho1⟩
  have hB : IsOuterCycle CombinatorialMap.singleEdgeDirected B := by
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      fin_cases d
      · exact ho0
      · exact ho1
    · intro d hd
      fin_cases d
      · simp [B]
      · simp [B]
    · intro d hd
      fin_cases d <;> simp [B, CombinatorialMap.singleEdgeDirected,
        CombinatorialMap.singleEdge, CombinatorialMap.faceSucc]
  refine ⟨B, [0], [], [1], [], ?_⟩
  refine ⟨hB, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, by simp [B]⟩
  · intro d
    fin_cases d <;> simp [hul0, hul1]
  · intro d
    fin_cases d <;> simp [hlr0, hlr1]
  · simp [MissingRun]
  · simp [MissingRun]

end DirectedDistances.PlanarMap
