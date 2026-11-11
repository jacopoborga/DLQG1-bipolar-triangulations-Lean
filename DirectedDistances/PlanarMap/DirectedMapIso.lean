/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap

/-! # Unrooted isomorphisms of directed maps with missing edges

An isomorphism of directed planar maps with missing edges in the sense of
a bijection of darts that preserves the rotation system, the edge flip, the
missing edges, the orientation of every dart and the distinguished outer face
(as a face orbit, not its marked dart). No root and no boundary paths are
recorded.

This is the notion of "coincides" used for partial maps in the proof of -/

public section
namespace DirectedDistances.PlanarMap

/-- An unrooted isomorphism of directed maps with missing edges
the paper result. -/
structure DirectedMapWithMissingIso {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E]
    (M : DirectedMapWithMissing D) (N : DirectedMapWithMissing E) where
  /-- The bijection of darts. -/
  toEquiv : D ≃ E
  /-- Preserve the cyclic order around vertices. -/
  rot_comm : ∀ d, toEquiv (M.rot d) = N.rot (toEquiv d)
  /-- Preserve the opposite dart of each edge. -/
  edgeInv_comm : ∀ d, toEquiv (M.edgeInv d) = N.edgeInv (toEquiv d)
  /-- Preserve missing status. -/
  missing_iff : ∀ d, N.missing (toEquiv d) ↔ M.missing d
  /-- Preserve the orientation of every dart. -/
  tail_iff : ∀ d, N.tail (toEquiv d) ↔ M.tail d
  /-- Preserve membership in the distinguished outer face orbit. -/
  outer_iff : ∀ d, N.IsOuter (toEquiv d) ↔ M.IsOuter d

namespace DirectedMapWithMissingIso

variable {D E F : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  [Fintype F] [DecidableEq F]
  {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
  {P : DirectedMapWithMissing F}

/-- The identity isomorphism. Helper toward `lem-kmsw-left` -/
@[expose] def refl (M : DirectedMapWithMissing D) : DirectedMapWithMissingIso M M where
  toEquiv := Equiv.refl D
  rot_comm := fun _ => rfl
  edgeInv_comm := fun _ => rfl
  missing_iff := fun _ => Iff.rfl
  tail_iff := fun _ => Iff.rfl
  outer_iff := fun _ => Iff.rfl

/-- The inverse isomorphism. Helper toward `lem-kmsw-left` -/
@[expose] def symm (I : DirectedMapWithMissingIso M N) : DirectedMapWithMissingIso N M where
  toEquiv := I.toEquiv.symm
  rot_comm := by
    intro d
    apply I.toEquiv.injective
    rw [I.rot_comm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  edgeInv_comm := by
    intro d
    apply I.toEquiv.injective
    rw [I.edgeInv_comm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  missing_iff := by
    intro d
    have h := I.missing_iff (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  tail_iff := by
    intro d
    have h := I.tail_iff (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  outer_iff := by
    intro d
    have h := I.outer_iff (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- Composition of isomorphisms. Helper toward `lem-kmsw-left` -/
@[expose] def trans (I : DirectedMapWithMissingIso M N) (J : DirectedMapWithMissingIso N P) :
    DirectedMapWithMissingIso M P where
  toEquiv := I.toEquiv.trans J.toEquiv
  rot_comm := by
    intro d
    simp only [Equiv.trans_apply]
    rw [I.rot_comm, J.rot_comm]
  edgeInv_comm := by
    intro d
    simp only [Equiv.trans_apply]
    rw [I.edgeInv_comm, J.edgeInv_comm]
  missing_iff := by
    intro d
    simp only [Equiv.trans_apply]
    exact (J.missing_iff _).trans (I.missing_iff d)
  tail_iff := by
    intro d
    simp only [Equiv.trans_apply]
    exact (J.tail_iff _).trans (I.tail_iff d)
  outer_iff := by
    intro d
    simp only [Equiv.trans_apply]
    exact (J.outer_iff _).trans (I.outer_iff d)

end DirectedMapWithMissingIso

end DirectedDistances.PlanarMap
