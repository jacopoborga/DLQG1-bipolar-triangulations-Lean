/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageOuterCycle

/-! # Rooted isomorphisms and inverse data for finite KMSW stages

160–202`): an isomorphism is a bijection of darts commuting with the vertex
rotation and edge flip, preserving present/missing status, the directed tail,
the distinguished outer-face orbit, and the active root dart. The particular
dart chosen to name the outer face is only a representative of that face orbit.

The integer edge IDs and vertex IDs in `kmswStage` are allocation labels, not
isomorphism invariants: an isomorphism may rename the darts and therefore the
edge orbits. Consequently equality of the stored `active`/edge-ID fields is
not an injectivity argument. A genuine inverse must recover the walk from
structure. The intended route is the inverse procedure in `defn:KMSW-inv`:
the Peano contour order supplies the ordered edges, and the two rooted trees
`T_UL` and `T_LR` supply the two heights. A step-by-step peeling implementation
would need the same invariant information at each predecessor stage. The
current finite-stage API provides rotations, orientations and missing-edge
status, but does not yet provide either rooted tree, contour order, or a
proved, isomorphism-compatible peeling operation.

The printed step set in `thm-kmsw` has the confirmed increment typo recorded
surjectivity claim is made here. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- A directed map with missing edges and a distinguished present directed root
dart. The root is the active edge of a finite KMSW stage -/
structure RootedDirectedMapWithMissing (D : Type*) [Fintype D] [DecidableEq D] where
  map : DirectedMapWithMissing D
  root : D
  root_present : ¬ map.missing root
  root_tail : map.tail root

/-- Root-preserving isomorphism of directed maps with missing edges. The dart
bijection commutes with vertex rotation and edge flip, preserves the present
and missing predicates, the orientation, the distinguished outer-face orbit,
and the root dart (`defn:planar-map-with-missing-edges`, -/
structure RootedDirectedMapIso {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E]
    (M : RootedDirectedMapWithMissing D) (N : RootedDirectedMapWithMissing E) where
  dartEquiv : D ≃ E
  rot_comm : ∀ d, dartEquiv (M.map.rot d) = N.map.rot (dartEquiv d)
  edgeFlip_comm : ∀ d,
    dartEquiv (M.map.toCombinatorialMap.edgeInv d) =
      N.map.toCombinatorialMap.edgeInv (dartEquiv d)
  missing_iff : ∀ d, M.map.missing d ↔ N.map.missing (dartEquiv d)
  present_iff : ∀ d, ¬ M.map.missing d ↔ ¬ N.map.missing (dartEquiv d)
  tail_iff : ∀ d, M.map.tail d ↔ N.map.tail (dartEquiv d)
  outer_iff : ∀ d, M.map.IsOuter d ↔ N.map.IsOuter (dartEquiv d)
  root_comm : dartEquiv M.root = N.root

/-- The identity rooted isomorphism. -/
def RootedDirectedMapIso.refl {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) : RootedDirectedMapIso M M where
  dartEquiv := Equiv.refl D
  rot_comm := fun _ => rfl
  edgeFlip_comm := fun _ => rfl
  missing_iff := fun _ => Iff.rfl
  present_iff := fun _ => Iff.rfl
  tail_iff := fun _ => Iff.rfl
  outer_iff := fun _ => Iff.rfl
  root_comm := rfl

/-- The rooted directed map carried by stage `n`, rooted at its active tail -/
@[expose] def kmswRootedStage (w : ℕ → Fin 3) (n : ℕ) :
    RootedDirectedMapWithMissing (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  let hactive : s.active < s.nextEdge := act_lt_nextEdge w (Nat.le_refl n)
  let d : StageDart s.nextEdge := (⟨s.active, hactive⟩, false)
  have hULne : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w n).1
  have hULlast? : s.UL.getLast? = some s.active :=
    (kmswStage_UL_nonempty_active_last w n).2
  have hULlast : s.UL.getLast hULne = s.active := by
    have h := hULlast?
    rw [List.getLast?_eq_getLast_of_ne_nil hULne] at h
    exact Option.some.inj h
  have hactiveMem : s.active ∈ s.UL := by
    rw [← hULlast]
    exact List.getLast_mem hULne
  have hactivePresent : s.present s.active = true :=
    (kmswStage_status w n).2.1 s.active hactiveMem
  refine ⟨kmswStageDirectedMap w n, d, ?_, ?_⟩
  · change ¬ s.present s.active = false
    rw [hactivePresent]
    decide
  · change (s.present s.active = true ∧ false = false)
    exact ⟨hactivePresent, rfl⟩

/-- Equal KMSW input prefixes give equal bookkeeping states. This is the
label-level forward construction; it does not establish inverse injectivity. -/
theorem kmswStage_eq_of_prefix (w w' : ℕ → Fin 3) (n : ℕ)
    (hprefix : ∀ i < n, w i = w' i) :
    kmswStage w n = kmswStage w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprefix' : ∀ i < n, w i = w' i := by
      intro i hi
      exact hprefix i (by omega)
    have hlast : w n = w' n := hprefix n (by omega)
    change kmswStep (kmswStage w n) (w n) =
      kmswStep (kmswStage w' n) (w' n)
    rw [ih hprefix', hlast]

/-- Identical code functions give identical rooted finite stages. -/
def kmswRootedStage_iso_of_words_eq (w w' : ℕ → Fin 3) (n : ℕ)
    (hwords : w = w') :
    RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n) := by
  subst w'
  exact RootedDirectedMapIso.refl (kmswRootedStage w n)

end DirectedDistances.KMSW
