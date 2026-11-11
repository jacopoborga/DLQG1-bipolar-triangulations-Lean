/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap
public import DirectedDistances.PlanarMap.OuterBoundary

/-! # Reversing selected edge orientations

The combinatorial map keeps its darts, edge involution, rotation, and marked
outer face when orientations of selected present edges are reversed. The
bipolarity and acyclicity part of Lemma `lem-bdy-reverse` is a separate -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Reverse the orientation of the edge orbits represented by `S`. The
condition says that `S` contains both darts of every selected edge and that
each selected edge is present; missing edges have no orientation to reverse -/
@[expose] noncomputable def flipOrientation (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) : DirectedMapWithMissing D := by
  classical
  refine
    { toCombinatorialMap := M.toCombinatorialMap
      missing := M.missing
      missing_edgeInv := M.missing_edgeInv
      tail := fun d =>
        if d ∈ S then M.tail (M.toCombinatorialMap.edgeInv d) else M.tail d
      tail_iff := ?_
      tail_missing := ?_
      outer := M.outer
      missing_outer := ?_ }
  · intro d hd
    by_cases h : d ∈ S
    · have hinv : M.toCombinatorialMap.edgeInv d ∈ S := hS.1 d h
      have hpresent : ¬ M.missing (M.toCombinatorialMap.edgeInv d) := by
        intro hmiss
        exact hd ((M.missing_edgeInv d).mpr hmiss)
      simp [h, hinv]
      simpa only [M.toCombinatorialMap.edgeInv_invol] using
        M.tail_iff (M.toCombinatorialMap.edgeInv d) hpresent
    · have hinv : M.toCombinatorialMap.edgeInv d ∉ S := by
        intro hinv
        apply h
        simpa only [M.toCombinatorialMap.edgeInv_invol] using hS.1 _ hinv
      simp [h, hinv]
      exact M.tail_iff d hd
  · intro d hd
    by_cases h : d ∈ S
    · exact False.elim ((hS.2 d h) hd)
    · simp [h]
      exact M.tail_missing d hd
  · intro d hd
    exact M.missing_outer d hd

/-- The underlying rotation system is unchanged by an orientation flip. -/
theorem flipOrientation_toCombinatorialMap (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) :
    (flipOrientation M S hS).toCombinatorialMap = M.toCombinatorialMap := rfl

/-- The set of missing darts is unchanged by an orientation flip. -/
theorem flipOrientation_missing (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) :
    (flipOrientation M S hS).missing = M.missing := rfl

/-- The marked dart of the outer face is unchanged by an orientation flip. -/
theorem flipOrientation_outer (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) :
    (flipOrientation M S hS).outer = M.outer := rfl

/-- The face permutation is unchanged by an orientation flip. -/
theorem flipOrientation_faceSucc (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) :
    (flipOrientation M S hS).toCombinatorialMap.faceSucc =
      M.toCombinatorialMap.faceSucc := rfl

/-- Face-cycle membership between any two darts is unchanged by an
orientation flip. -/
theorem flipOrientation_faceRel_iff (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) (d e : D) :
    (flipOrientation M S hS).toCombinatorialMap.FaceRel d e ↔
      M.toCombinatorialMap.FaceRel d e := Iff.rfl

/-- Membership in the distinguished outer face is unchanged by an
orientation flip. -/
theorem flipOrientation_isOuter_iff (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) (d : D) :
    (flipOrientation M S hS).IsOuter d ↔ M.IsOuter d := Iff.rfl

/-- Any exact cyclic word for the external face remains an exact cyclic word
after an orientation flip (`lem-bdy-reverse`, -/
theorem flipOrientation_isOuterCycle_iff (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) (B : NonemptyWord D) :
    IsOuterCycle (flipOrientation M S hS) B ↔ IsOuterCycle M B := Iff.rfl

/-- Combinatorial planarity is unchanged by an orientation flip. -/
theorem flipOrientation_isPlanar_iff (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) :
    (flipOrientation M S hS).toCombinatorialMap.IsPlanar ↔
      M.toCombinatorialMap.IsPlanar := Iff.rfl

/-- On each selected edge, the new tail dart is the old head dart; outside
`S`, the orientation is unchanged. Since `S` is closed under `edgeInv`, this
is an edge-orbit condition rather than a choice of dart representative. -/
theorem flipOrientation_tail_of_mem (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) (d : D) (hd : d ∈ S) :
    (flipOrientation M S hS).tail d ↔
      M.tail (M.toCombinatorialMap.edgeInv d) := by
  classical
  simp [flipOrientation, hd]

/-- Outside the selected edge orbits, the orientation is unchanged. -/
theorem flipOrientation_tail_of_not_mem (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) (d : D) (hd : d ∉ S) :
    (flipOrientation M S hS).tail d ↔ M.tail d := by
  classical
  simp [flipOrientation, hd]

/-- Extensionality for the data fields of a directed map with missing edges. -/
private theorem directedMapWithMissing_ext {M N : DirectedMapWithMissing D}
    (hmap : M.toCombinatorialMap = N.toCombinatorialMap)
    (hmissing : M.missing = N.missing)
    (htail : M.tail = N.tail)
    (houter : M.outer = N.outer) : M = N := by
  cases M with
  | mk cm miss hmiss tail htail' htailMissing outer houterMissing =>
    cases N with
    | mk cm' miss' hmiss' tail' htail'' htailMissing' outer' houterMissing' =>
      simp_all

/-- Flipping the same edge orbits twice restores the original directed map. -/
theorem flipOrientation_involutive (M : DirectedMapWithMissing D)
    (S : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d)) :
    flipOrientation (flipOrientation M S hS) S hS = M := by
  classical
  apply directedMapWithMissing_ext
  · rfl
  · rfl
  · funext d
    by_cases hd : d ∈ S
    · have hinv : M.toCombinatorialMap.edgeInv d ∈ S := hS.1 d hd
      simp [flipOrientation, hd, hinv, M.toCombinatorialMap.edgeInv_invol]
    · simp [flipOrientation, hd]
  · rfl

end DirectedDistances.PlanarMap
