/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PlanarRootedMap

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8. A whole-map isomorphism preserves the plane
rotation, geometric edge identities and missing tags, present-edge directions,
and the ordered root dart. Missing roots remain unoriented: their missing tag
is preserved and the orientation condition below applies only to present
darts. -/
structure D39RootedMapIso (M N : D39RootedMap) where
  /-- The bijection of geometric darts. -/
  toEquiv : M.core.D ≃ N.core.D
  /-- Preserve the plane rotation system. -/
  rot_comm : ∀ d, toEquiv (M.core.rot d) = N.core.rot (toEquiv d)
  /-- Preserve edge reversal, retaining parallel edge identities. -/
  edgeInv_comm : ∀ d, toEquiv (M.core.edgeInv d) = N.core.edgeInv (toEquiv d)
  /-- Preserve the present or missing tag of every geometric edge. -/
  missing_iff : ∀ d, N.core.missing (toEquiv d) ↔ M.core.missing d
  /-- Preserve orientation on present darts only. -/
  tail_iff : ∀ d, ¬ M.core.missing d →
    (N.core.tail (toEquiv d) ↔ M.core.tail d)
  /-- Preserve the ordered root mark's dart, including when it is missing. -/
  root_dart_comm : toEquiv M.rootMark.dart = N.rootMark.dart

namespace D39RootedMapIso

variable {M N P : D39RootedMap}

/-- The identity whole-map isomorphism. Helper toward Definition 3.8. -/
@[expose] def refl (M : D39RootedMap) : D39RootedMapIso M M where
  toEquiv := Equiv.refl _
  rot_comm := fun _ => rfl
  edgeInv_comm := fun _ => rfl
  missing_iff := fun _ => Iff.rfl
  tail_iff := fun _ _ => Iff.rfl
  root_dart_comm := rfl

/-- Invert a whole-map isomorphism. Helper toward Definition 3.8. -/
@[expose] def symm (I : D39RootedMapIso M N) : D39RootedMapIso N M where
  toEquiv := I.toEquiv.symm
  rot_comm := by
    intro d
    apply I.toEquiv.injective
    rw [Equiv.apply_symm_apply, I.rot_comm, Equiv.apply_symm_apply]
  edgeInv_comm := by
    intro d
    apply I.toEquiv.injective
    rw [Equiv.apply_symm_apply, I.edgeInv_comm, Equiv.apply_symm_apply]
  missing_iff := by
    intro d
    have h := I.missing_iff (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  tail_iff := by
    intro d hd
    have hd' : ¬ M.core.missing (I.toEquiv.symm d) := by
      intro hm
      have hmiss := (I.missing_iff (I.toEquiv.symm d)).mpr hm
      exact hd (by simpa using hmiss)
    simpa only [Equiv.apply_symm_apply] using (I.tail_iff _ hd').symm
  root_dart_comm := by
    rw [← I.root_dart_comm, Equiv.symm_apply_apply]

/-- Compose whole-map isomorphisms. Helper toward Definition 3.8. -/
@[expose] def trans (I : D39RootedMapIso M N) (J : D39RootedMapIso N P) :
    D39RootedMapIso M P where
  toEquiv := I.toEquiv.trans J.toEquiv
  rot_comm := by
    intro d
    exact (congrArg J.toEquiv (I.rot_comm d)).trans (J.rot_comm _)
  edgeInv_comm := by
    intro d
    exact (congrArg J.toEquiv (I.edgeInv_comm d)).trans (J.edgeInv_comm _)
  missing_iff := fun d => (J.missing_iff _).trans (I.missing_iff d)
  tail_iff := by
    intro d hd
    have hd' : ¬ N.core.missing (I.toEquiv d) := by
      intro hm
      exact hd ((I.missing_iff d).mp hm)
    exact (J.tail_iff _ hd').trans (I.tail_iff d hd)
  root_dart_comm := (congrArg J.toEquiv I.root_dart_comm).trans J.root_dart_comm

end D39RootedMapIso

/-- Helper toward Definition 3.8. Whole-map isomorphism is an equivalence
relation on rooted planar maps, allowing their dart types to vary. -/
@[expose] def D39PlanarRootedMap.setoid : Setoid D39PlanarRootedMap where
  r M N := Nonempty (D39RootedMapIso M.toD39RootedMap N.toD39RootedMap)
  iseqv := ⟨fun M => ⟨D39RootedMapIso.refl M.toD39RootedMap⟩,
    fun ⟨I⟩ => ⟨I.symm⟩, fun ⟨I⟩ ⟨J⟩ => ⟨I.trans J⟩⟩

/-- Helper toward Definition 3.8. Rooted planar maps up to whole-map
isomorphism, with the root mark, missing tags and plane rotation retained. -/
@[expose] def D39PlanarRootedMapClass :=
  Quotient D39PlanarRootedMap.setoid

/-- Helper toward Definition 3.8. Lift an isomorphism-invariant function to
the quotient of rooted planar maps. -/
@[expose] def D39PlanarRootedMapClass.lift {β : Sort*}
    (f : D39PlanarRootedMap → β)
    (hf : ∀ M N,
      Nonempty (D39RootedMapIso M.toD39RootedMap N.toD39RootedMap) → f M = f N) :
    D39PlanarRootedMapClass → β :=
  Quotient.lift f (by
    intro M N h
    exact hf M N h)

/-- Helper toward Definition 3.8. The quotient lift agrees with its function
on each representative. -/
@[simp] theorem D39PlanarRootedMapClass.lift_mk {β : Sort*}
    (f : D39PlanarRootedMap → β)
    (hf : ∀ M N,
      Nonempty (D39RootedMapIso M.toD39RootedMap N.toD39RootedMap) → f M = f N)
    (M : D39PlanarRootedMap) :
    D39PlanarRootedMapClass.lift f hf (Quotient.mk _ M) = f M := rfl













end DirectedDistances.PlanarMap
