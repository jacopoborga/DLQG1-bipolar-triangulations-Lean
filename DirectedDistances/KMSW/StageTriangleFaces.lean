/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageRotation

/-! # Triangle faces created by KMSW rotation splices

Local face-cycle calculations for the fresh-left and up branches of `def-kmsw`,
successor tables. Existing-predecessor left steps also require the old outer
corner equation, recorded below as a local splice lemma. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The three specified darts form a directed three-cycle under the face
successor, with no repeated dart (`def-kmsw`, -/
@[expose] def FaceSucc3Cycle {D : Type*} (f : Equiv.Perm D)
    (d₁ d₂ d₃ : D) : Prop :=
  f d₁ = d₂ ∧ f d₂ = d₃ ∧ f d₃ = d₁ ∧
    d₁ ≠ d₂ ∧ d₂ ≠ d₃ ∧ d₃ ≠ d₁

/-- A rotation equation gives the corresponding face-successor equation for
`faceSucc = rot⁻¹ * edgeInv` (`sec-kmsw`, -/
theorem faceSucc_eq_of_rot_eq {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) {x y : D} (h : M.rot y = M.edgeInv x) :
    M.faceSucc x = y := by
  change M.rot.symm (M.edgeInv x) = y
  apply M.rot.injective
  simpa using h.symm

/-- The rotation `σ` together with the geometric edge flip is a raw stage -/
@[expose] def stageRotationMap (k : ℕ)
    (σ : Equiv.Perm (StageDart k)) : CombinatorialMap (StageDart k) where
  edgeInv := edgeFlip k
  edgeInv_invol := by rintro ⟨e, b⟩; cases b <;> rfl
  edgeInv_ne := by
    rintro ⟨e, b⟩ h
    have hb := congrArg Prod.snd h
    cases b <;> cases hb
  rot := σ

private theorem allocation_old_ne_new (k r : ℕ)
    (d : StageDart k) (e : StageDart r) :
    StageRotation.allocation k r (.inl d) ≠ StageRotation.allocation k r (.inr e) := by
  intro h
  have h' := (StageRotation.allocation k r).injective h
  cases h'

private theorem allocation_new0_ne_new1 (k : ℕ) (b c : Bool) :
    StageRotation.allocation k 2 (.inr ((⟨0, by omega⟩ : Fin 2), b)) ≠
      StageRotation.allocation k 2 (.inr ((⟨1, by omega⟩ : Fin 2), c)) := by
  intro h
  have h' := (StageRotation.allocation k 2).injective h
  have he : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := by
    exact congrArg Prod.fst (Sum.inr.inj h')
  have hv := congrArg Fin.val he
  norm_num at hv

/-- At the creation of a fresh-left triangle, the darts `(a, h_p, t_q)` form -/
theorem leftFresh_triangle_face_cycle (k : ℕ)
    (σ : Equiv.Perm (StageDart k)) (active : Fin k) :
    let a : StageDart k := (active, false)
    let M := stageRotationMap (k + 2)
      (StageRotation.leftFresh k σ a (active, true))
    FaceSucc3Cycle M.faceSucc
      (StageRotation.allocation k 2 (.inl a))
      (StageRotation.allocation k 2 (.inr ((⟨0, by omega⟩ : Fin 2), true)))
      (StageRotation.allocation k 2 (.inr ((⟨1, by omega⟩ : Fin 2), false))) := by
  dsimp only
  let a : StageDart k := (active, false)
  let A : StageDart k := (active, true)
  let pₕ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨0, by omega⟩ : Fin 2), true))
  let pₜ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨0, by omega⟩ : Fin 2), false))
  let qₜ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨1, by omega⟩ : Fin 2), false))
  let qₕ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨1, by omega⟩ : Fin 2), true))
  let a' : StageDart (k + 2) := StageRotation.allocation k 2 (.inl a)
  let A' : StageDart (k + 2) := StageRotation.allocation k 2 (.inl A)
  let M := stageRotationMap (k + 2) (StageRotation.leftFresh k σ a A)
  have h₁ : M.rot pₕ = M.edgeInv a' := by
    dsimp [M, stageRotationMap, pₕ, a', A']
    have ht := (StageRotation.leftFresh_new k σ a A).2.1
    rw [ht]
    simp [edgeFlip, StageRotation.allocation, a, A]
  have h₂ : M.rot qₜ = M.edgeInv pₕ := by
    dsimp [M, stageRotationMap, qₜ, pₕ, A']
    have ht := (StageRotation.leftFresh_new k σ a A).2.2.2
    rw [ht]
    simp [edgeFlip, StageRotation.allocation]
  have h₃ : M.rot a' = M.edgeInv qₜ := by
    dsimp [M, stageRotationMap, a', qₜ, A']
    have ht := StageRotation.leftFresh_old k σ a A a
    rw [ht]
    simp [edgeFlip, StageRotation.allocation, a]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact faceSucc_eq_of_rot_eq M h₁
  · exact faceSucc_eq_of_rot_eq M h₂
  · exact faceSucc_eq_of_rot_eq M h₃
  · exact allocation_old_ne_new k 2 a ((⟨0, by omega⟩, true))
  · exact allocation_new0_ne_new1 k true false
  · exact (allocation_old_ne_new k 2 a ((⟨1, by omega⟩, false))).symm

/-- At the creation of an up triangle, the darts `(a, h_q, h_p)` form its -/
theorem up_triangle_face_cycle (k : ℕ)
    (σ : Equiv.Perm (StageDart k)) (active : Fin k) :
    let a : StageDart k := (active, false)
    let M := stageRotationMap (k + 2)
      (StageRotation.up k σ a (active, true))
    FaceSucc3Cycle M.faceSucc
      (StageRotation.allocation k 2 (.inl a))
      (StageRotation.allocation k 2 (.inr ((⟨1, by omega⟩ : Fin 2), true)))
      (StageRotation.allocation k 2 (.inr ((⟨0, by omega⟩ : Fin 2), true))) := by
  dsimp only
  let a : StageDart k := (active, false)
  let A : StageDart k := (active, true)
  let pₕ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨0, by omega⟩ : Fin 2), true))
  let pₜ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨0, by omega⟩ : Fin 2), false))
  let qₜ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨1, by omega⟩ : Fin 2), false))
  let qₕ : StageDart (k + 2) :=
    StageRotation.allocation k 2 (.inr ((⟨1, by omega⟩ : Fin 2), true))
  let a' : StageDart (k + 2) := StageRotation.allocation k 2 (.inl a)
  let A' : StageDart (k + 2) := StageRotation.allocation k 2 (.inl A)
  let M := stageRotationMap (k + 2) (StageRotation.up k σ a A)
  have h₁ : M.rot qₕ = M.edgeInv a' := by
    dsimp [M, stageRotationMap, qₕ, a', A']
    have ht := (StageRotation.up_new k σ a A).2.1
    rw [ht]
    simp [edgeFlip, StageRotation.allocation, a, A]
  have h₂ : M.rot pₕ = M.edgeInv qₕ := by
    dsimp [M, stageRotationMap, pₕ, qₕ, A']
    have ht := (StageRotation.up_new k σ a A).2.2.1
    rw [ht]
    simp [edgeFlip, StageRotation.allocation]
  have h₃ : M.rot a' = M.edgeInv pₕ := by
    dsimp [M, stageRotationMap, a', pₕ, A']
    have ht := StageRotation.up_old k σ a A a
    rw [ht]
    simp [edgeFlip, StageRotation.allocation, a]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact faceSucc_eq_of_rot_eq M h₁
  · exact faceSucc_eq_of_rot_eq M h₂
  · exact faceSucc_eq_of_rot_eq M h₃
  · exact allocation_old_ne_new k 2 a ((⟨1, by omega⟩, true))
  · exact (allocation_new0_ne_new1 k true true).symm
  · exact (allocation_old_ne_new k 2 a ((⟨0, by omega⟩, true))).symm

/-- The existing-predecessor splice creates `(t_e, a, h_p)` whenever the old
rotation has the corresponding upper-left corner equation. The corner premise
is exactly the old outer-word successor at that location (`def-kmsw`, -/
theorem leftExisting_triangle_face_cycle (k : ℕ)
    (σ : Equiv.Perm (StageDart k)) (e active : Fin k)
    (heactive : e ≠ active)
    (hcorner : σ (active, false) = (e, true)) :
    let a : StageDart k := (active, false)
    let tₑ : StageDart (k + 1) :=
      StageRotation.allocation k 1 (.inl (e, false))
    let a' : StageDart (k + 1) := StageRotation.allocation k 1 (.inl a)
    let pₕ : StageDart (k + 1) :=
      StageRotation.allocation k 1 (.inr ((⟨0, by omega⟩ : Fin 1), true))
    let M := stageRotationMap (k + 1)
      (StageRotation.leftExisting k σ (e, false) (active, true))
    FaceSucc3Cycle M.faceSucc tₑ a' pₕ := by
  dsimp only
  let a : StageDart k := (active, false)
  let A : StageDart k := (active, true)
  let eₜ : StageDart k := (e, false)
  let eₕ : StageDart k := (e, true)
  let tₚ : StageDart (k + 1) :=
    StageRotation.allocation k 1 (.inr ((⟨0, by omega⟩ : Fin 1), false))
  let pₕ : StageDart (k + 1) :=
    StageRotation.allocation k 1 (.inr ((⟨0, by omega⟩ : Fin 1), true))
  let tₑ : StageDart (k + 1) := StageRotation.allocation k 1 (.inl eₜ)
  let a' : StageDart (k + 1) := StageRotation.allocation k 1 (.inl a)
  let A' : StageDart (k + 1) := StageRotation.allocation k 1 (.inl A)
  let eₕ' : StageDart (k + 1) := StageRotation.allocation k 1 (.inl eₕ)
  let M := stageRotationMap (k + 1)
    (StageRotation.leftExisting k σ eₜ A)
  change σ a = eₕ at hcorner
  have h₁ : M.rot a' = M.edgeInv tₑ := by
    dsimp [M, stageRotationMap, a', tₑ, eₕ']
    have ht := StageRotation.leftExisting_old k σ eₜ A a
    rw [ht]
    have hae : active ≠ e := by
      intro h
      exact heactive h.symm
    simp [edgeFlip, StageRotation.allocation, a, A, eₜ, eₕ, hcorner, hae,
      heactive]
  have h₂ : M.rot pₕ = M.edgeInv a' := by
    dsimp [M, stageRotationMap, pₕ, a', A']
    have ht := (StageRotation.leftExisting_new k σ eₜ A).2
    rw [ht]
    simp [edgeFlip, StageRotation.allocation, a, A]
  have h₃ : M.rot tₑ = M.edgeInv pₕ := by
    dsimp [M, stageRotationMap, tₑ, pₕ]
    have ht := StageRotation.leftExisting_old k σ eₜ A eₜ
    rw [ht]
    simp [edgeFlip, StageRotation.allocation]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact faceSucc_eq_of_rot_eq M h₁
  · exact faceSucc_eq_of_rot_eq M h₂
  · exact faceSucc_eq_of_rot_eq M h₃
  · intro h
    have h' := (StageRotation.allocation k 1).injective h
    have hval := congrArg (fun d : StageDart k => d.1.val) (Sum.inl.inj h')
    have hid : e = active := Fin.ext (by simpa [eₜ, a] using hval)
    exact heactive hid
  · exact allocation_old_ne_new k 1 a ((⟨0, by omega⟩, true))
  · exact (allocation_old_ne_new k 1 eₜ ((⟨0, by omega⟩, true))).symm

end DirectedDistances.KMSW
