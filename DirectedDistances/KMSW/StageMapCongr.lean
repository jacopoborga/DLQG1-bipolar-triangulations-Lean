/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageFaceDetermination
public import DirectedDistances.KMSW.StageOuterCycle
public import DirectedDistances.PlanarMap.DirectedMapMarkMissing
public import DirectedDistances.KMSW.KMSWInverse

/-! # Isomorphisms between KMSW stages with a common code prefix

KMSW stage map depends only on the codes read so far (`def-kmsw`, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private def kmswStageDartEquivOfPrefix (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) :
    StageDart (kmswStage w n).nextEdge ≃ StageDart (kmswStage w' n).nextEdge :=
  Equiv.prodCongr
    (finCongr (congrArg State.nextEdge (kmswStage_eq_of_prefix w w' n h)))
    (Equiv.refl Bool)

private theorem kmswStageDartEquivOfPrefix_val (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i)
    (d : StageDart (kmswStage w n).nextEdge) :
    (kmswStageDartEquivOfPrefix w w' n h d).1.val = d.1.val ∧
      (kmswStageDartEquivOfPrefix w w' n h d).2 = d.2 := by
  simp [kmswStageDartEquivOfPrefix]

private theorem sameCycle_equiv_of_conj {α β : Type*} [Finite α] [Finite β]
    (e : α ≃ β) {f : Equiv.Perm α} {g : Equiv.Perm β}
    (h : ∀ x, e (f x) = g (e x)) (x y : α) :
    f.SameCycle x y ↔ g.SameCycle (e x) (e y) := by
  have hpow : ∀ k x, e ((f ^ k) x) = (g ^ k) (e x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      calc
        e ((f ^ (k + 1)) x) = e (f ((f ^ k) x)) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        _ = g (e ((f ^ k) x)) := h _
        _ = g ((g ^ k) (e x)) := congrArg g (ih x)
        _ = (g ^ (k + 1)) (e x) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
  constructor
  · intro hxy
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    exact ⟨k, (hpow k x).symm.trans (congrArg e hk)⟩
  · intro hxy
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    refine ⟨k, ?_⟩
    apply e.injective
    exact (hpow k x).trans hk

/-- KMSW stage map depends only on the codes read so far (`def-kmsw`, -/
@[expose] def kmswStageDirectedMapIsoOfPrefix (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) :
    DirectedMapWithMissingIso (kmswStageDirectedMap w n) (kmswStageDirectedMap w' n) := by
  let hstage : kmswStage w n = kmswStage w' n :=
    kmswStage_eq_of_prefix w w' n h
  let φ : Fin (kmswStage w n).nextEdge ≃ Fin (kmswStage w' n).nextEdge :=
    finCongr (congrArg State.nextEdge hstage)
  let φv : ℕ → ℕ := id
  have hφval : ∀ e, (φ e).val = e.val := by
    intro e
    simp [φ]
  have hφv : ∀ e, (φ e).val = φv e.val := by
    intro e
    simpa [φv] using hφval e
  have houterVal : stageOuterWordVal w n = stageOuterWordVal w' n := by
    rw [stageOuterWordVal_eq_runs, stageOuterWordVal_eq_runs, hstage]
  have houter : List.IsRotated
      ((stageOuterWordVal w n).map (fun p => (φv p.1, p.2)))
      (stageOuterWordVal w' n) := by
    rw [houterVal]
    simpa [φv] using List.IsRotated.refl (stageOuterWordVal w' n)
  have htri : ∀ j : TriangleCreationTime w, j.val < n →
      ∃ j' : TriangleCreationTime w', j'.val < n ∧
        List.IsRotated
          ((stageTriangleDartList w j).map (fun p => (φv p.1, p.2)))
          (stageTriangleDartList w' j') := by
    intro j hj
    have hcode : w j.val = w' j.val := h j.val (by omega)
    let j' : TriangleCreationTime w' := ⟨j.val, by rw [← hcode]; exact j.property⟩
    have hstagej : kmswStage w j.val = kmswStage w' j.val := by
      apply kmswStage_eq_of_prefix
      intro i hi
      exact h i (by omega)
    have hlist : stageTriangleDartList w j = stageTriangleDartList w' j' := by
      simp only [stageTriangleDartList, stageTriangleDartTriple]
      rw [hstagej, hcode]
    refine ⟨j', hj, ?_⟩
    simpa [φv, hlist] using List.IsRotated.refl (stageTriangleDartList w' j')
  have hconj := kmswMap_conj_of_faces w w' n n φ φv hφv houter htri
  let Φ : StageDart (kmswStage w n).nextEdge ≃
      StageDart (kmswStage w' n).nextEdge := Equiv.prodCongr φ (Equiv.refl Bool)
  have hface : ∀ d, Φ ((kmswMap w n).faceSucc d) =
      (kmswMap w' n).faceSucc (Φ d) := hconj.1
  have hrot : ∀ d, Φ ((kmswMap w n).rot d) = (kmswMap w' n).rot (Φ d) :=
    hconj.2.1
  have hflip : ∀ d, Φ (edgeFlip (kmswStage w n).nextEdge d) =
      edgeFlip (kmswStage w' n).nextEdge (Φ d) := hconj.2.2
  have hpresent : (kmswStage w' n).present = (kmswStage w n).present := by
    exact congrArg State.present hstage.symm
  have hroot : Φ (stageULHeadDart w n) = stageULHeadDart w' n := by
    simp [Φ, φ, stageULHeadDart, hstage]
  refine {
    toEquiv := Φ
    rot_comm := by
      intro d
      change Φ ((kmswMap w n).rot d) = (kmswMap w' n).rot (Φ d)
      exact hrot d
    edgeInv_comm := by
      intro d
      change Φ (edgeFlip (kmswStage w n).nextEdge d) =
        edgeFlip (kmswStage w' n).nextEdge (Φ d)
      exact hflip d
    missing_iff := by
      intro d
      change (kmswStage w' n).present (φ d.1).val = false ↔
        (kmswStage w n).present d.1.val = false
      rw [hφval d.1, hpresent]
    tail_iff := by
      intro d
      change ((kmswStage w' n).present (φ d.1).val = true ∧ d.2 = false) ↔
        ((kmswStage w n).present d.1.val = true ∧ d.2 = false)
      rw [hφval d.1, hpresent]
    outer_iff := by
      intro d
      change Equiv.Perm.SameCycle (kmswMap w' n).faceSucc
          (stageULHeadDart w' n) (Φ d) ↔
        Equiv.Perm.SameCycle (kmswMap w n).faceSucc (stageULHeadDart w n) d
      rw [← hroot]
      exact (sameCycle_equiv_of_conj Φ hface (stageULHeadDart w n) d).symm
  }

/-- KMSW stage map depends only on the codes read so far (`def-kmsw`, -/
theorem kmswStageDirectedMapIsoOfPrefix_val (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) (d : StageDart (kmswStage w n).nextEdge) :
    ((kmswStageDirectedMapIsoOfPrefix w w' n h).toEquiv d).1.val = d.1.val ∧
      ((kmswStageDirectedMapIsoOfPrefix w w' n h).toEquiv d).2 = d.2 := by
  change (kmswStageDartEquivOfPrefix w w' n h d).1.val = d.1.val ∧
    (kmswStageDartEquivOfPrefix w w' n h d).2 = d.2
  exact kmswStageDartEquivOfPrefix_val w w' n h d

/-- KMSW stage map depends only on the codes read so far (`def-kmsw`, -/
@[expose] def kmswStageDirectedMapIsoOfPrefix_markMissing (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) (P : ℕ → Bool → Prop)
    (hS : ∀ d : StageDart (kmswStage w n).nextEdge, P d.1.val d.2 →
      (kmswStageDirectedMap w n).IsOuter d ∨
        (kmswStageDirectedMap w n).IsOuter
          ((kmswStageDirectedMap w n).edgeInv d))
    (hT : ∀ d : StageDart (kmswStage w' n).nextEdge, P d.1.val d.2 →
      (kmswStageDirectedMap w' n).IsOuter d ∨
        (kmswStageDirectedMap w' n).IsOuter
          ((kmswStageDirectedMap w' n).edgeInv d)) :
    DirectedMapWithMissingIso
      ((kmswStageDirectedMap w n).markMissing {d | P d.1.val d.2}
        (by intro d hd; exact hS d (by simpa using hd)))
      ((kmswStageDirectedMap w' n).markMissing {d | P d.1.val d.2}
        (by intro d hd; exact hT d (by simpa using hd))) := by
  let I := kmswStageDirectedMapIsoOfPrefix w w' n h
  have hST : ∀ d, I.toEquiv d ∈ {d | P d.1.val d.2} ↔
      d ∈ {d | P d.1.val d.2} := by
    intro d
    change P (I.toEquiv d).1.val (I.toEquiv d).2 ↔ P d.1.val d.2
    obtain ⟨hv, hb⟩ := kmswStageDirectedMapIsoOfPrefix_val w w' n h d
    rw [hv, hb]
  exact DirectedMapWithMissingIso.markMissing I
    {d | P d.1.val d.2} {d | P d.1.val d.2}
    (by intro d hd; exact hS d (by simpa using hd))
    (by intro d hd; exact hT d (by simpa using hd)) hST

end DirectedDistances.KMSW
