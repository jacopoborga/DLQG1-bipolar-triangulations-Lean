/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWInverse

/-! # Root-local information for inverse KMSW peeling

uses the rooted outer boundary and the two trees `T_UL` and `T_LR`. This module
records root-local missing-edge incidence that is already visible to the
rooted-map isomorphisms of `KMSWInverse.lean`. It does not assert a complete
peeling or injectivity theorem. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- A missing edge is incident to the vertex at the tail of the root dart.
The vertex is represented by the root's rotation cycle -/
@[expose] def RootedDirectedMapWithMissing.missingAtRootTailVertex
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) : Prop :=
  ∃ d, M.map.missing d ∧ M.map.rot.SameCycle M.root d

/-- A missing edge is incident to the vertex at the head of the root dart.
The head vertex is the rotation cycle of the opposite root dart -/
@[expose] def RootedDirectedMapWithMissing.missingAtRootHeadVertex
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) : Prop :=
  ∃ d, M.map.missing d ∧
    M.map.rot.SameCycle (M.map.toCombinatorialMap.edgeInv M.root) d

private theorem rootedIso_rot_pow
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (k : ℕ) (d : D) :
    h.dartEquiv ((M.map.rot ^ k) d) = (N.map.rot ^ k) (h.dartEquiv d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [h.rot_comm, ih]

private theorem rootedIso_rot_sameCycle_iff
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (a b : D) :
    M.map.rot.SameCycle a b ↔
      N.map.rot.SameCycle (h.dartEquiv a) (h.dartEquiv b) := by
  constructor
  · intro hab
    obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
    refine ⟨k, ?_⟩
    calc
      (N.map.rot ^ k) (h.dartEquiv a) = h.dartEquiv ((M.map.rot ^ k) a) :=
        (rootedIso_rot_pow h k a).symm
      _ = h.dartEquiv b := congrArg h.dartEquiv hk
  · intro hab
    obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
    have heq : (M.map.rot ^ k) a = b := by
      apply h.dartEquiv.injective
      rw [rootedIso_rot_pow h k a]
      exact hk
    exact ⟨k, heq⟩

/-- Rooted isomorphisms preserve whether a missing edge meets the root tail
vertex. -/
theorem RootedDirectedMapIso.missingAtRootTailVertex_iff
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) :
    M.missingAtRootTailVertex ↔ N.missingAtRootTailVertex := by
  constructor
  · rintro ⟨d, hmiss, hcycle⟩
    refine ⟨h.dartEquiv d, (h.missing_iff d).mp hmiss, ?_⟩
    have hc := (rootedIso_rot_sameCycle_iff h M.root d).mp hcycle
    simpa [h.root_comm] using hc
  · rintro ⟨d, hmiss, hcycle⟩
    obtain ⟨d', rfl⟩ := h.dartEquiv.surjective d
    refine ⟨d', (h.missing_iff d').mpr hmiss, ?_⟩
    have hc : N.map.rot.SameCycle (h.dartEquiv M.root) (h.dartEquiv d') := by
      simpa [h.root_comm] using hcycle
    exact (rootedIso_rot_sameCycle_iff h M.root d').mpr hc

/-- Rooted isomorphisms preserve whether a missing edge meets the root head
vertex. -/
theorem RootedDirectedMapIso.missingAtRootHeadVertex_iff
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) :
    M.missingAtRootHeadVertex ↔ N.missingAtRootHeadVertex := by
  have hhead : h.dartEquiv (M.map.toCombinatorialMap.edgeInv M.root) =
      N.map.toCombinatorialMap.edgeInv N.root := by
    rw [h.edgeFlip_comm, h.root_comm]
  constructor
  · rintro ⟨d, hmiss, hcycle⟩
    refine ⟨h.dartEquiv d, (h.missing_iff d).mp hmiss, ?_⟩
    have hc :=
      (rootedIso_rot_sameCycle_iff h (M.map.toCombinatorialMap.edgeInv M.root) d).mp
        hcycle
    simpa [hhead] using hc
  · rintro ⟨d, hmiss, hcycle⟩
    obtain ⟨d', rfl⟩ := h.dartEquiv.surjective d
    refine ⟨d', (h.missing_iff d').mpr hmiss, ?_⟩
    have hc : N.map.rot.SameCycle
        (h.dartEquiv (M.map.toCombinatorialMap.edgeInv M.root)) (h.dartEquiv d') := by
      simpa [hhead] using hcycle
    exact (rootedIso_rot_sameCycle_iff h
      (M.map.toCombinatorialMap.edgeInv M.root) d').mpr hc

/-- An up step creates a missing edge incident to the head vertex of its new
root-local peeling signal; it is not an exclusive characterization of the
last code letter. -/
theorem kmswRootedStage_up_missingAtRootHeadVertex
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    (kmswRootedStage w (n + 1)).missingAtRootHeadVertex := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hstep : kmswCodeStep (w n) = .up := by
    simp [hc, kmswCodeStep]
  have ht : t = kmswStepOfStep s .up := by
    simp [t, s, kmswStage, kmswStep, hstep]
  have hrootBound : s.nextEdge < t.nextEdge := by
    rw [ht]
    simp only [kmswStepOfStep, State.addEdge]
    omega
  have hrootBound' : s.nextEdge < (kmswStage w (n + 1)).nextEdge := by
    simpa [t] using hrootBound
  have hroot : (kmswRootedStage w (n + 1)).root =
      ((⟨s.nextEdge, hrootBound'⟩ :
          Fin (kmswStage w (n + 1)).nextEdge), false) := by
    simp [kmswRootedStage, s, kmswStage, kmswStep, hstep,
      kmswStepOfStep, State.addEdge]
  have hmissBound : s.nextEdge + 1 < t.nextEdge := by
    simp [t, s, kmswStage, kmswStep, hstep, kmswStepOfStep, State.addEdge]
  let d : StageDart t.nextEdge := (⟨s.nextEdge + 1, hmissBound⟩, false)
  have hmissing : (kmswStageDirectedMap w (n + 1)).missing d := by
    change t.present (s.nextEdge + 1) = false
    simp [t, s, kmswStage, kmswStep, hstep, kmswStepOfStep, State.addEdge]
  have hendpoint : stageEndpoint t
      (edgeFlip t.nextEdge (kmswRootedStage w (n + 1)).root) =
      stageEndpoint t d := by
    rw [hroot]
    simp [d, t, ht, s, kmswStepOfStep, State.addEdge,
      stageEndpoint, edgeFlip]
  refine ⟨d, hmissing, ?_⟩
  apply (stageRot_sameCycle_iff_endpoint_eq w (n + 1)
    (edgeFlip t.nextEdge (kmswRootedStage w (n + 1)).root) d).2
  exact hendpoint

end DirectedDistances.KMSW
