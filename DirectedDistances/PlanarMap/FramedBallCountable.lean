/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FramedBallIso
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The class space is equipped with the top measurable space. -/
instance instMeasurableSpaceFramedBallClass : MeasurableSpace FramedBallClass := ⊤

private structure CanonicalFramedBall (n : ℕ) where
  map : DirectedMapWithMissing (Fin n)
  rootDart : Fin n
  frameEdgeDart : Fin n
  frameEdge_missing : map.missing frameEdgeDart
  frameEdge_at_root : map.rot.SameCycle rootDart frameEdgeDart
  frameOtherDart : Option (Fin n)
  frameOtherDart_valid : ∀ y, frameOtherDart = some y →
    map.rot.SameCycle (map.edgeInv frameEdgeDart) y

private def canonicalCode {n : ℕ} (M : CanonicalFramedBall n) :=
  (M.map.rot, M.map.edgeInv, M.map.missing, M.map.tail, M.map.outer,
    M.rootDart, M.frameEdgeDart, M.frameOtherDart)

private theorem canonicalCode_injective {n : ℕ} :
    Function.Injective (@canonicalCode n) := by
  intro M N h
  cases M with
  | mk Mm Mr Me hmiss hroot Mo hvalid =>
    cases N with
    | mk Nm Nr Ne hmissN hrootN No hvalidN =>
      cases Mm with
      | mk Mmap Minvol Mne Mrot =>
        cases Nm with
        | mk Nmap Ninvol Nne Nrot =>
          simp [canonicalCode] at h
          rcases h with ⟨hrot, hedge, hmissing, htail, houter,
            hrootDart, hframeEdge, hframeOther⟩
          cases Mmap
          cases Nmap
          simp_all

private instance canonicalFramedBall_finite (n : ℕ) :
    Finite (CanonicalFramedBall n) :=
  Finite.of_injective canonicalCode canonicalCode_injective

private instance canonicalFramedBall_countable (n : ℕ) :
    Countable (CanonicalFramedBall n) := inferInstance

private theorem relabelSameCycle {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (e : D ≃ E) (f : Equiv.Perm D)
    {x y : D} (h : f.SameCycle x y) :
    (e.permCongr f).SameCycle (e x) (e y) := by
  rcases h with ⟨i, hi⟩
  have hpow : e.permCongr (f ^ i) = (e.permCongr f) ^ i := by
    change e.permCongrHom (f ^ i) = _
    exact map_zpow e.permCongrHom f i
  refine ⟨i, ?_⟩
  calc
    ((e.permCongr f) ^ i) (e x) = e ((f ^ i) x) := by
      rw [← hpow]
      simp
    _ = e y := congrArg e hi

private theorem relabelSameCycle_iff {D E : Type*} [Fintype D]
    [DecidableEq D] [Fintype E] [DecidableEq E] (e : D ≃ E)
    (f : Equiv.Perm D) (x y : D) :
    (e.permCongr f).SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    have hpow : e.permCongr (f ^ i) = (e.permCongr f) ^ i := by
      change e.permCongrHom (f ^ i) = _
      exact map_zpow e.permCongrHom f i
    have htrans : e ((f ^ i) x) = e y := by
      calc
        e ((f ^ i) x) = (e.permCongr (f ^ i)) (e x) := by simp
        _ = ((e.permCongr f) ^ i) (e x) := by rw [hpow]
        _ = e y := hi
    exact ⟨i, e.injective htrans⟩
  · intro h
    exact relabelSameCycle e f h

private def relabelCombinatorialMap {D E : Type*} [Fintype D]
    [DecidableEq D] [Fintype E] [DecidableEq E] (e : D ≃ E)
    (M : CombinatorialMap D) : CombinatorialMap E where
  edgeInv := e.permCongr M.edgeInv
  edgeInv_invol := by
    intro d
    simp [Equiv.permCongr_apply, M.edgeInv_invol]
  edgeInv_ne := by
    intro d hd
    apply M.edgeInv_ne (e.symm d)
    apply e.injective
    simpa [Equiv.permCongr_apply] using hd
  rot := e.permCongr M.rot

private theorem relabelFaceSucc {D E : Type*} [Fintype D]
    [DecidableEq D] [Fintype E] [DecidableEq E] (e : D ≃ E)
    (M : CombinatorialMap D) :
    e.permCongr M.faceSucc = (relabelCombinatorialMap e M).faceSucc := by
  have hinv : e.permCongr M.rot⁻¹ = (e.permCongr M.rot)⁻¹ :=
    map_inv e.permCongrHom M.rot
  ext d
  simp [CombinatorialMap.faceSucc, relabelCombinatorialMap,
    Equiv.permCongr_apply, hinv]

private def relabelMap {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (e : D ≃ E)
    (M : DirectedMapWithMissing D) : DirectedMapWithMissing E where
  toCombinatorialMap := relabelCombinatorialMap e M.toCombinatorialMap
  missing := fun d => M.missing (e.symm d)
  missing_edgeInv := by
    intro d
    simpa [relabelCombinatorialMap, Equiv.permCongr_apply] using
      M.missing_edgeInv (e.symm d)
  tail := fun d => M.tail (e.symm d)
  tail_iff := by
    intro d hd
    have hd' : ¬ M.missing (e.symm d) := by simpa using hd
    simpa [relabelCombinatorialMap, Equiv.permCongr_apply] using
      M.tail_iff (e.symm d) hd'
  tail_missing := by
    intro d hd
    exact M.tail_missing (e.symm d) hd
  outer := e M.outer
  missing_outer := by
    intro d hd
    have hd' : M.missing (e.symm d) := by simpa using hd
    rcases M.missing_outer (e.symm d) hd' with h | h
    · left
      have hc := relabelSameCycle e M.faceSucc h
      change (relabelCombinatorialMap e M.toCombinatorialMap).faceSucc.SameCycle
        (e M.outer) d
      rw [← relabelFaceSucc]
      simpa using hc
    · right
      have hc := relabelSameCycle e M.faceSucc h
      change (relabelCombinatorialMap e M.toCombinatorialMap).faceSucc.SameCycle
        (e M.outer) ((e.permCongr M.edgeInv) d)
      rw [← relabelFaceSucc]
      simpa [Equiv.permCongr_apply] using hc

private def relabelMapIso {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (e : D ≃ E)
    (M : DirectedMapWithMissing D) :
    DirectedMapWithMissingIso M (relabelMap e M) where
  toEquiv := e
  rot_comm := by
    intro d
    simp [relabelMap, relabelCombinatorialMap, Equiv.permCongr_apply]
  edgeInv_comm := by
    intro d
    simp [relabelMap, relabelCombinatorialMap, Equiv.permCongr_apply]
  missing_iff := by intro d; simp [relabelMap]
  tail_iff := by intro d; simp [relabelMap]
  outer_iff := by
    intro d
    change (relabelCombinatorialMap e M.toCombinatorialMap).faceSucc.SameCycle
      (e M.outer) (e d) ↔ M.faceSucc.SameCycle M.outer d
    rw [← relabelFaceSucc]
    exact relabelSameCycle_iff e M.faceSucc M.outer d

private def CanonicalFramedBall.toFramedBall {n : ℕ}
    (B : CanonicalFramedBall n) : FramedBall where
  D := Fin n
  instFintypeD := inferInstance
  instDecidableEqD := inferInstance
  map := B.map
  rootDart := B.rootDart
  frameEdgeDart := B.frameEdgeDart
  frameEdge_missing := B.frameEdge_missing
  frameEdge_at_root := B.frameEdge_at_root
  frameOtherDart := B.frameOtherDart
  frameOtherDart_valid := B.frameOtherDart_valid

private def canonicalOf {M : FramedBall}
    (e : M.D ≃ Fin (Fintype.card M.D)) :
    CanonicalFramedBall (Fintype.card M.D) := by
  refine ⟨relabelMap e M.map, e M.rootDart, e M.frameEdgeDart, ?_, ?_,
    M.frameOtherDart.map e, ?_⟩
  · simpa [relabelMap] using M.frameEdge_missing
  · simpa [relabelMap, relabelCombinatorialMap, Equiv.permCongr_apply] using
      relabelSameCycle e M.map.rot M.frameEdge_at_root
  · intro y hy
    cases ho : M.frameOtherDart with
    | none => simp [ho] at hy
    | some d =>
      have hy' : e d = y := by simpa [ho] using hy
      subst y
      have hs := relabelSameCycle e M.map.rot (M.frameOtherDart_valid d ho)
      simpa [relabelMap, relabelCombinatorialMap, Equiv.permCongr_apply] using hs

private def canonicalClass (B : Σ n, CanonicalFramedBall n) : FramedBallClass :=
  Quotient.mk FramedBall.setoid B.2.toFramedBall

private theorem canonicalClass_surjective : Function.Surjective canonicalClass := by
  intro q
  refine Quotient.inductionOn q ?_
  intro M
  let e := Fintype.equivFin M.D
  let B := canonicalOf e
  let N := B.toFramedBall
  have hclass :
      Quotient.mk FramedBall.setoid M = Quotient.mk FramedBall.setoid N := by
    apply Quotient.sound
    refine ⟨{
      mapIso := relabelMapIso e M.map
      root_vertex := Equiv.Perm.SameCycle.rfl
      frameEdge_comm := rfl
      frameOther_comm := ?_
    }⟩
    cases ho : M.frameOtherDart with
    | none =>
      apply Or.inl
      constructor
      · simp
      · change (canonicalOf e).frameOtherDart = none
        simp [canonicalOf, ho]
    | some d =>
      right
      refine ⟨e d, e d, ?_, ?_, Equiv.Perm.SameCycle.rfl⟩
      · change some ((relabelMapIso e M.map).toEquiv d) = some (e d)
        rfl
      · change (canonicalOf e).frameOtherDart = some (e d)
        simp [canonicalOf, ho]
  refine ⟨⟨Fintype.card M.D, B⟩, ?_⟩
  change Quotient.mk FramedBall.setoid N = Quotient.mk FramedBall.setoid M
  exact hclass.symm

/-- The isomorphism classes have a countable coding by finite canonical dart
carriers. Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper
result. -/
instance instCountableFramedBallClass : Countable FramedBallClass :=
  Function.Surjective.countable canonicalClass_surjective

end DirectedDistances.PlanarMap
