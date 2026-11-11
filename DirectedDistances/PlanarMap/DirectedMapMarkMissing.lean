/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.DirectedMapIso

/-! # Declaring outer edges of a directed map missing

Given a directed map with missing edges (`defn:planar-map-with-missing-edges`,
edges of those darts are declared missing: they stay geometric edges, but lose
their orientation. Every other edge keeps its status and orientation.

This is the operation "with all its right (left) boundary edges declared to be
missing except for the edge having the sink vertex as the terminal vertex" in
S7. -/

public section
namespace DirectedDistances.PlanarMap

namespace DirectedMapWithMissing

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

/-- Declare the edges of the darts in `S` missing. The set need not be
saturated under the edge flip; both darts of each selected edge become
missing. Every selected dart must lie on the outer face up to the edge flip.
not the paper result. -/
@[expose] def markMissing (M : DirectedMapWithMissing D) (S : Set D)
    (hS : ∀ d ∈ S, M.IsOuter d ∨ M.IsOuter (M.edgeInv d)) :
    DirectedMapWithMissing D where
  toCombinatorialMap := M.toCombinatorialMap
  missing d := M.missing d ∨ d ∈ S ∨ M.edgeInv d ∈ S
  missing_edgeInv := by
    intro d
    rw [M.edgeInv_invol d, ← M.missing_edgeInv d]
    tauto
  tail d := M.tail d ∧ ¬ (d ∈ S ∨ M.edgeInv d ∈ S)
  tail_iff := by
    intro d hd
    have hm : ¬ M.missing d := fun h => hd (Or.inl h)
    have hs : ¬ (d ∈ S ∨ M.edgeInv d ∈ S) := fun h => hd (Or.inr h)
    have hs' : ¬ (M.edgeInv d ∈ S ∨ M.edgeInv (M.edgeInv d) ∈ S) := by
      rw [M.edgeInv_invol d]
      tauto
    simp only [hs, hs', not_false_eq_true, and_true]
    exact M.tail_iff d hm
  tail_missing := by
    intro d hd ht
    rcases hd with hd | hd
    · exact M.tail_missing d hd ht.1
    · exact ht.2 hd
  outer := M.outer
  missing_outer := by
    intro d hd
    rcases hd with hd | hd | hd
    · exact M.missing_outer d hd
    · exact hS d hd
    · rcases hS _ hd with h | h
      · exact Or.inr h
      · rw [M.edgeInv_invol d] at h
        exact Or.inl h

variable (M : DirectedMapWithMissing D) (S : Set D)
  (hS : ∀ d ∈ S, M.IsOuter d ∨ M.IsOuter (M.edgeInv d))

/-- The underlying combinatorial map is unchanged. Helper toward
result. -/
@[simp] theorem markMissing_toCombinatorialMap :
    (M.markMissing S hS).toCombinatorialMap = M.toCombinatorialMap := rfl

/-- Missing status after marking. Helper toward `lem-kmsw-left` -/
@[simp] theorem markMissing_missing_iff (d : D) :
    (M.markMissing S hS).missing d ↔ M.missing d ∨ d ∈ S ∨ M.edgeInv d ∈ S :=
  Iff.rfl

/-- Orientation after marking: unchanged off the marked edges. Helper toward
result. -/
@[simp] theorem markMissing_tail_iff (d : D) :
    (M.markMissing S hS).tail d ↔ M.tail d ∧ ¬ (d ∈ S ∨ M.edgeInv d ∈ S) :=
  Iff.rfl

/-- The outer face is unchanged. Helper toward `lem-kmsw-left` -/
@[simp] theorem markMissing_isOuter_iff (d : D) :
    (M.markMissing S hS).IsOuter d ↔ M.IsOuter d :=
  Iff.rfl

end DirectedMapWithMissing

namespace DirectedMapWithMissingIso

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}

/-- An isomorphism carrying the marked set of one map onto the marked set of
the other induces an isomorphism of the marked maps, with the same dart
bijection. Helper toward `lem-kmsw-left` -/
@[expose] def markMissing (I : DirectedMapWithMissingIso M N) (S : Set D) (T : Set E)
    (hS : ∀ d ∈ S, M.IsOuter d ∨ M.IsOuter (M.edgeInv d))
    (hT : ∀ d ∈ T, N.IsOuter d ∨ N.IsOuter (N.edgeInv d))
    (hST : ∀ d, I.toEquiv d ∈ T ↔ d ∈ S) :
    DirectedMapWithMissingIso (M.markMissing S hS) (N.markMissing T hT) where
  toEquiv := I.toEquiv
  rot_comm := I.rot_comm
  edgeInv_comm := I.edgeInv_comm
  missing_iff := by
    intro d
    change N.missing (I.toEquiv d) ∨ I.toEquiv d ∈ T ∨ N.edgeInv (I.toEquiv d) ∈ T ↔
      M.missing d ∨ d ∈ S ∨ M.edgeInv d ∈ S
    rw [← I.edgeInv_comm, I.missing_iff, hST, hST]
  tail_iff := by
    intro d
    change N.tail (I.toEquiv d) ∧ ¬ (I.toEquiv d ∈ T ∨ N.edgeInv (I.toEquiv d) ∈ T) ↔
      M.tail d ∧ ¬ (d ∈ S ∨ M.edgeInv d ∈ S)
    rw [← I.edgeInv_comm, I.tail_iff, hST, hST]
  outer_iff := I.outer_iff

end DirectedMapWithMissingIso

end DirectedDistances.PlanarMap
