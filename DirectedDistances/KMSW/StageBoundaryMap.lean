/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.KMSW.StageOuterCycle
public import DirectedDistances.PlanarMap.CombinatorialMap

/-! # The four boundary runs of a finite KMSW stage as map darts

The four edge lists of the recursive construction are identified with the
present and missing darts on the outer face. Their finite cardinalities are
the map-level form of the formulas in `lem-kmsw-bdy` -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem stageDarts_mem_side (s : State) (es : List ℕ) (side : Bool)
    (hes : ∀ e ∈ es, e < s.nextEdge) (e : Fin s.nextEdge) (b : Bool) :
    (e, b) ∈ stageDarts s es side hes ↔ b = side ∧ e.val ∈ es := by
  constructor
  · intro h
    obtain ⟨f, hf, hde⟩ := (stageDarts_mem s es side hes (e, b)).1 h
    exact ⟨congrArg Prod.snd hde,
      by
        have hv : e.val = f := congrArg (fun x : StageDart s.nextEdge => x.1.val) hde
        simpa [hv] using hf⟩
  · rintro ⟨hb, he⟩
    apply (stageDarts_mem s es side hes (e, b)).2
    refine ⟨e.val, he, ?_⟩
    have hb' : b = side := hb
    subst b
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl

/-- The finite stage allocates every edge ID in its four boundary lists -/
theorem stageRun_edge_bound (w : ℕ → Fin 3) (n e : ℕ)
    (he : ((e ∈ (kmswStage w n).UL ∨ e ∈ (kmswStage w n).UR) ∨
      e ∈ (kmswStage w n).LL) ∨ e ∈ (kmswStage w n).LR) :
    e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2
  simpa only [List.mem_append] using he

/-- Ordered west darts in the UL run (`defn:bound-edges`, -/
@[expose] def kmswStageULDartRun (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.UL false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inl he))))

/-- Ordered west darts in the UR run (`defn:bound-edges`, -/
@[expose] def kmswStageURDartRun (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.UR false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inr he))))

/-- Ordered east darts in the reversed LR run (`defn:bound-edges`, -/
@[expose] def kmswStageLRDartRun (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.LR.reverse true (fun e he =>
    stageRun_edge_bound w n e (Or.inr (List.mem_reverse.mp he)))

/-- Ordered east darts in the reversed LL run (`defn:bound-edges`, -/
@[expose] def kmswStageLLDartRun (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) := by
  let s := kmswStage w n
  exact stageDarts s s.LL.reverse true (fun e he =>
    stageRun_edge_bound w n e (Or.inl (Or.inr (List.mem_reverse.mp he))))

private theorem stageOuterWord_eq_runs (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWord w n =
      kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
  simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
    kmswStageLRDartRun, kmswStageLLDartRun]

private theorem stageULDartRun_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageULDartRun w n).Nodup := by
  have h := stageOuterWord_nodup w n
  rw [stageOuterWord_eq_runs] at h
  exact (List.nodup_append.mp (List.nodup_append.mp
    (List.nodup_append.mp h).1).1).1

private theorem stageURDartRun_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageURDartRun w n).Nodup := by
  have h := stageOuterWord_nodup w n
  rw [stageOuterWord_eq_runs] at h
  exact (List.nodup_append.mp (List.nodup_append.mp
    (List.nodup_append.mp h).1).1).2.1

private theorem stageLRDartRun_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageLRDartRun w n).Nodup := by
  have h := stageOuterWord_nodup w n
  rw [stageOuterWord_eq_runs] at h
  exact (List.nodup_append.mp (List.nodup_append.mp h).1).2.1

private theorem stageLLDartRun_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageLLDartRun w n).Nodup := by
  have h := stageOuterWord_nodup w n
  rw [stageOuterWord_eq_runs] at h
  exact (List.nodup_append.mp h).2.1

/-- Finite set of UL darts (`defn:bound-edges`, -/
@[expose] noncomputable def kmswStageULDartsFinset (w : ℕ → Fin 3) (n : ℕ) :
    Finset (StageDart (kmswStage w n).nextEdge) := by
  classical
  exact (kmswStageULDartRun w n).toFinset

/-- Finite set of UR missing west darts (`defn:bound-edges`, -/
@[expose] noncomputable def kmswStageURDartsFinset (w : ℕ → Fin 3) (n : ℕ) :
    Finset (StageDart (kmswStage w n).nextEdge) := by
  classical
  exact (kmswStageURDartRun w n).toFinset

/-- Finite set of LR darts (`defn:bound-edges`, -/
@[expose] noncomputable def kmswStageLRDartsFinset (w : ℕ → Fin 3) (n : ℕ) :
    Finset (StageDart (kmswStage w n).nextEdge) := by
  classical
  exact (kmswStageLRDartRun w n).toFinset

/-- Finite set of LL missing east darts (`defn:bound-edges`, -/
@[expose] noncomputable def kmswStageLLDartsFinset (w : ℕ → Fin 3) (n : ℕ) :
    Finset (StageDart (kmswStage w n).nextEdge) := by
  classical
  exact (kmswStageLLDartRun w n).toFinset

private theorem sameCycle_formPerm_of_mem {D : Type*} [DecidableEq D]
    (l : List D) (hl : l.Nodup) (hne : l ≠ []) {a b : D}
    (ha : a ∈ l) (hb : b ∈ l) : l.formPerm.SameCycle a b := by
  cases hlst : l with
  | nil => exact (hne hlst).elim
  | cons x xs =>
    have hnodup : (x :: xs).Nodup := by simpa [hlst] using hl
    have ha' : a ∈ x :: xs := by simpa [hlst] using ha
    have hb' : b ∈ x :: xs := by simpa [hlst] using hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
    have hpowA : ((x :: xs).formPerm ^ i) x = (x :: xs)[i] := by
      simpa only [Nat.mod_eq_of_lt hi] using
        (List.formPerm_pow_apply_head x xs hnodup i)
    have hpowB : ((x :: xs).formPerm ^ j) x = (x :: xs)[j] := by
      simpa only [Nat.mod_eq_of_lt hj] using
        (List.formPerm_pow_apply_head x xs hnodup j)
    have hheadA : (x :: xs).formPerm.SameCycle x (x :: xs)[i] := ⟨i, hpowA⟩
    have hheadB : (x :: xs).formPerm.SameCycle x (x :: xs)[j] := ⟨j, hpowB⟩
    exact hheadA.symm.trans hheadB

private theorem stageOuterWord_mem_iff_outer (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ stageOuterWord w n ↔ (kmswStageDirectedMap w n).IsOuter d := by
  let l := stageOuterWord w n
  let outer := stageULHeadDart w n
  have hcycle := stageOuterWord_faceSucc w n
  have houterSide : outer.2 = false := by
    simp [outer, stageULHeadDart]
  have houterEdge : outer.1.val ∈ (kmswStage w n).UL := by
    simp [outer, stageULHeadDart]
  have houter : outer ∈ l := by
    apply (stageOuterWord_mem_iff w n outer).2
    exact Or.inl ⟨houterSide, Or.inl houterEdge⟩
  have hnodup : l.Nodup := stageOuterWord_nodup w n
  have hne : l ≠ [] := stageOuterWord_nonempty w n
  have hformMem : ∀ k : ℕ, (l.formPerm ^ k) outer ∈ l := by
    intro k
    induction k with
    | zero => simpa using houter
    | succ k ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using
        (List.formPerm_apply_mem_of_mem ih)
  have hiter : ∀ k : ℕ,
      ((kmswMap w n).faceSucc ^ k) outer = (l.formPerm ^ k) outer := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        ((kmswMap w n).faceSucc ^ (k + 1)) outer =
            (kmswMap w n).faceSucc (((kmswMap w n).faceSucc ^ k) outer) := by
              simp only [pow_succ', Equiv.Perm.mul_apply]
        _ = (kmswMap w n).faceSucc ((l.formPerm ^ k) outer) := by rw [ih]
        _ = l.formPerm ((l.formPerm ^ k) outer) := hcycle _ (by
              simpa [l] using hformMem k)
        _ = (l.formPerm ^ (k + 1)) outer := by
              simp only [pow_succ', Equiv.Perm.mul_apply]
  constructor
  · intro hd
    change (kmswMap w n).faceSucc.SameCycle outer d
    have hform : l.formPerm.SameCycle outer d :=
      sameCycle_formPerm_of_mem l hnodup hne houter (by simpa [l] using hd)
    obtain ⟨k, _, hpow⟩ := hform.exists_pow_eq'
    exact ⟨k, (hiter k).trans hpow⟩
  · intro hd
    change (kmswMap w n).faceSucc.SameCycle outer d at hd
    obtain ⟨k, _, hpow⟩ := hd.exists_pow_eq'
    have hactual : ((kmswMap w n).faceSucc ^ k) outer ∈ l := by
      rw [hiter k]
      exact hformMem k
    rw [hpow] at hactual
    simpa [l] using hactual

private theorem kmswStageULDartRun_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageULDartRun w n ↔ d.2 = false ∧ d.1.val ∈ (kmswStage w n).UL := by
  change (d.1, d.2) ∈ stageDarts (kmswStage w n) (kmswStage w n).UL false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inl he)))) ↔ _
  exact stageDarts_mem_side _ _ _ _ _ _

private theorem kmswStageURDartRun_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageURDartRun w n ↔ d.2 = false ∧ d.1.val ∈ (kmswStage w n).UR := by
  change (d.1, d.2) ∈ stageDarts (kmswStage w n) (kmswStage w n).UR false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inr he)))) ↔ _
  exact stageDarts_mem_side _ _ _ _ _ _

private theorem kmswStageLRDartRun_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageLRDartRun w n ↔ d.2 = true ∧ d.1.val ∈ (kmswStage w n).LR := by
  change (d.1, d.2) ∈ stageDarts (kmswStage w n)
    (kmswStage w n).LR.reverse true
    (fun e he => stageRun_edge_bound w n e (Or.inr (List.mem_reverse.mp he))) ↔ _
  simpa only [List.mem_reverse] using
    (stageDarts_mem_side (kmswStage w n) (kmswStage w n).LR.reverse true
      (fun e he => stageRun_edge_bound w n e (Or.inr (List.mem_reverse.mp he)))
      d.1 d.2)

private theorem kmswStageLLDartRun_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageLLDartRun w n ↔ d.2 = true ∧ d.1.val ∈ (kmswStage w n).LL := by
  change (d.1, d.2) ∈ stageDarts (kmswStage w n)
    (kmswStage w n).LL.reverse true
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inr (List.mem_reverse.mp he)))) ↔ _
  simpa only [List.mem_reverse] using
    (stageDarts_mem_side (kmswStage w n) (kmswStage w n).LL.reverse true
      (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inr (List.mem_reverse.mp he))))
      d.1 d.2)

/-- Membership in the finite UL dart set records its west side and edge ID -/
theorem kmswStageULDartsFinset_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageULDartsFinset w n ↔
      d.2 = false ∧ d.1.val ∈ (kmswStage w n).UL := by
  simpa only [kmswStageULDartsFinset, List.mem_toFinset] using
    kmswStageULDartRun_mem w n d

/-- Membership in the finite UR dart set records its west side and edge ID -/
theorem kmswStageURDartsFinset_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageURDartsFinset w n ↔
      d.2 = false ∧ d.1.val ∈ (kmswStage w n).UR := by
  simpa only [kmswStageURDartsFinset, List.mem_toFinset] using
    kmswStageURDartRun_mem w n d

/-- Membership in the finite LR dart set records its east side and edge ID -/
theorem kmswStageLRDartsFinset_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageLRDartsFinset w n ↔
      d.2 = true ∧ d.1.val ∈ (kmswStage w n).LR := by
  simpa only [kmswStageLRDartsFinset, List.mem_toFinset] using
    kmswStageLRDartRun_mem w n d

/-- Membership in the finite LL dart set records its east side and edge ID -/
theorem kmswStageLLDartsFinset_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageLLDartsFinset w n ↔
      d.2 = true ∧ d.1.val ∈ (kmswStage w n).LL := by
  simpa only [kmswStageLLDartsFinset, List.mem_toFinset] using
    kmswStageLLDartRun_mem w n d

/-- The finite UL dart class is exactly the map's upper-left dart set -/
theorem kmswStageULDartsFinset_map_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageULDartsFinset w n ↔ d ∈ (kmswStageDirectedMap w n).ulDarts := by
  rw [kmswStageULDartsFinset_mem]
  constructor
  · rintro ⟨hside, he⟩
    have hcanon : ((d.1, false) : StageDart (kmswStage w n).nextEdge) ∈
        (kmswStageDirectedMap w n).ulDarts := (kmswStageDirectedMap_UL_bridge w n d.1).1 he
    have hdeq : d = (d.1, false) := by
      rcases d with ⟨e, b⟩
      cases b
      · rfl
      · cases hside
    rw [hdeq]
    exact hcanon
  · intro hd
    have hside : d.2 = false := by
      change ¬ (kmswStage w n).present d.1.val = false ∧
        ((kmswStage w n).present d.1.val = true ∧ d.2 = false) ∧ _ at hd
      exact hd.2.1.2
    have hdeq : d = (d.1, false) := by
      rcases d with ⟨e, b⟩
      cases b
      · rfl
      · cases hside
    have hcanon : ((d.1, false) : StageDart (kmswStage w n).nextEdge) ∈
        (kmswStageDirectedMap w n).ulDarts := hdeq.symm ▸ hd
    exact ⟨hside, (kmswStageDirectedMap_UL_bridge w n d.1).2 hcanon⟩

/-- The finite LR dart class is exactly the map's lower-right dart set -/
theorem kmswStageLRDartsFinset_map_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageLRDartsFinset w n ↔ d ∈ (kmswStageDirectedMap w n).lrDarts := by
  rw [kmswStageLRDartsFinset_mem]
  constructor
  · rintro ⟨hside, he⟩
    have hcanon : ((d.1, true) : StageDart (kmswStage w n).nextEdge) ∈
        (kmswStageDirectedMap w n).lrDarts := (kmswStageDirectedMap_LR_bridge w n d.1).1 he
    have hdeq : d = (d.1, true) := by
      rcases d with ⟨e, b⟩
      cases b
      · cases hside
      · rfl
    rw [hdeq]
    exact hcanon
  · intro hd
    have hp : (kmswStage w n).present d.1.val = true := by
      have hnot : ¬ (kmswStage w n).present d.1.val = false := by
        change ¬ (kmswStage w n).present d.1.val = false ∧ _ at hd
        exact hd.1
      cases h : (kmswStage w n).present d.1.val <;> simp_all
    have hside : d.2 = true := by
      cases hb : d.2
      · have htail : (kmswStageDirectedMap w n).tail d := by
          change (kmswStage w n).present d.1.val = true ∧ d.2 = false
          exact ⟨hp, hb⟩
        exact False.elim (hd.2.1 htail)
      · rfl
    have hdeq : d = (d.1, true) := by
      rcases d with ⟨e, b⟩
      cases b
      · cases hside
      · rfl
    have hcanon : ((d.1, true) : StageDart (kmswStage w n).nextEdge) ∈
        (kmswStageDirectedMap w n).lrDarts := hdeq.symm ▸ hd
    exact ⟨hside, (kmswStageDirectedMap_LR_bridge w n d.1).2 hcanon⟩

/-- The finite UR class consists exactly of missing west outer darts -/
theorem kmswStageURDartsFinset_map_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageURDartsFinset w n ↔
      (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = false := by
  rw [kmswStageURDartsFinset_mem]
  constructor
  · rintro ⟨hside, he⟩
    have hword : d ∈ stageOuterWord w n := by
      apply (stageOuterWord_mem_iff w n d).2
      exact Or.inl ⟨hside, Or.inr he⟩
    refine ⟨?_, (stageOuterWord_mem_iff_outer w n d).1 hword, hside⟩
    change (kmswStage w n).present d.1.val = false
    exact ((kmswStage_status w n).1 d.1.val d.1.isLt).2 (Or.inl he)
  · rintro ⟨hmiss, houter, hside⟩
    have hword := (stageOuterWord_mem_iff_outer w n d).2 houter
    have hclass := (stageOuterWord_mem_iff w n d).1 hword
    rcases hclass with ⟨_, hUL | hUR⟩ | ⟨htrue, _⟩
    · have hp := (kmswStage_status w n).2.1 d.1.val hUL
      change (kmswStage w n).present d.1.val = false at hmiss
      rw [hp] at hmiss
      cases hmiss
    · exact ⟨hside, hUR⟩
    · have hside' : d.2 = true := htrue
      rw [hside] at hside'
      cases hside'

/-- The finite LL class consists exactly of missing east outer darts -/
theorem kmswStageLLDartsFinset_map_mem (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageLLDartsFinset w n ↔
      (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = true := by
  rw [kmswStageLLDartsFinset_mem]
  constructor
  · rintro ⟨hside, he⟩
    have hword : d ∈ stageOuterWord w n := by
      apply (stageOuterWord_mem_iff w n d).2
      exact Or.inr ⟨hside, Or.inr (by simpa using he)⟩
    refine ⟨?_, (stageOuterWord_mem_iff_outer w n d).1 hword, hside⟩
    change (kmswStage w n).present d.1.val = false
    exact ((kmswStage_status w n).1 d.1.val d.1.isLt).2 (Or.inr he)
  · rintro ⟨hmiss, houter, hside⟩
    have hword := (stageOuterWord_mem_iff_outer w n d).2 houter
    have hclass := (stageOuterWord_mem_iff w n d).1 hword
    rcases hclass with ⟨hfalse, _⟩ | ⟨_, hLR | hLL⟩
    · have hside' : d.2 = false := hfalse
      rw [hside] at hside'
      cases hside'
    · have hp := (kmswStage_status w n).2.2.1 d.1.val hLR
      change (kmswStage w n).present d.1.val = false at hmiss
      rw [hp] at hmiss
      cases hmiss
    · exact ⟨hside, by simpa using hLL⟩

/-- UL edge orbits are exactly the upper-left edges in the KMSW state -/
theorem kmswStageDirectedMap_UL_edges (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    (kmswStageDirectedMap w n).IsUpperLeftEdge
      (Quotient.mk (Equiv.Perm.SameCycle.setoid
        (kmswStageDirectedMap w n).toCombinatorialMap.edgeInv) (e, false)) ↔
      e.val ∈ (kmswStage w n).UL := by
  classical
  by_cases hp : (kmswStage w n).present e.val = true
  · have htail : (kmswStageDirectedMap w n).tail (e, false) := by
      change (kmswStage w n).present e.val = true ∧ false = false
      exact ⟨hp, rfl⟩
    rw [(kmswStageDirectedMap w n).isUpperLeftEdge_iff_tail_mem_ulDarts
      (e, false) htail, kmswStageDirectedMap_UL_bridge]
  · have hfalse : (kmswStage w n).present e.val = false := by
      cases h : (kmswStage w n).present e.val <;> simp_all
    constructor
    · rintro ⟨d, heq, hd⟩
      change ¬ (kmswStage w n).present d.1.val = false ∧
        ((kmswStage w n).present d.1.val = true ∧ d.2 = false) ∧ _ at hd
      have hrel := (Quotient.exact heq).symm
      have hchoices := (CombinatorialMap.edgeInv_sameCycle_iff
        (kmswStageDirectedMap w n).toCombinatorialMap (e, false) d).mp hrel
      rcases hchoices with hdeq | hdeq
      · have hval : d.1.val = e.val := congrArg (fun x : StageDart _ => x.1.val) hdeq
        rw [hval, hfalse] at hd
        exact (hd.1 rfl).elim
      · have hside : d.2 = true := by
          simpa [kmswStageDirectedMap, kmswDirectedMap, kmswMap, edgeFlip] using
            congrArg Prod.snd hdeq.symm
        have hfalse : d.2 = false := hd.2.1.2
        exact Bool.noConfusion (hfalse.symm.trans hside)
    · intro he
      have hp' : (kmswStage w n).present e.val = true :=
        (kmswStage_status w n).2.1 e.val he
      exact False.elim (hp hp')

/-- LR edge orbits are exactly the lower-right edges in the KMSW state -/
theorem kmswStageDirectedMap_LR_edges (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    (kmswStageDirectedMap w n).IsLowerRightEdge
      (Quotient.mk (Equiv.Perm.SameCycle.setoid
        (kmswStageDirectedMap w n).toCombinatorialMap.edgeInv) (e, false)) ↔
      e.val ∈ (kmswStage w n).LR := by
  classical
  by_cases hp : (kmswStage w n).present e.val = true
  · have htail : (kmswStageDirectedMap w n).tail (e, false) := by
      change (kmswStage w n).present e.val = true ∧ false = false
      exact ⟨hp, rfl⟩
    rw [(kmswStageDirectedMap w n).isLowerRightEdge_iff_nontail_mem_lrDarts
      (e, false) htail]
    simpa [kmswStageDirectedMap, kmswDirectedMap, kmswMap, edgeFlip] using
      (kmswStageDirectedMap_LR_bridge w n e).symm
  · have hfalse : (kmswStage w n).present e.val = false := by
      cases h : (kmswStage w n).present e.val <;> simp_all
    constructor
    · rintro ⟨d, heq, hd⟩
      change ¬ (kmswStage w n).present d.1.val = false ∧ _ at hd
      have hrel := (Quotient.exact heq).symm
      have hchoices := (CombinatorialMap.edgeInv_sameCycle_iff
        (kmswStageDirectedMap w n).toCombinatorialMap (e, false) d).mp hrel
      rcases hchoices with hdeq | hdeq
      · have hval : d.1.val = e.val := congrArg (fun x : StageDart _ => x.1.val) hdeq
        rw [hval, hfalse] at hd
        exact (hd.1 rfl).elim
      · have hval : d.1.val = e.val := by
          have := congrArg (fun x : StageDart _ => x.1.val) hdeq
          simpa [kmswStageDirectedMap, kmswDirectedMap, kmswMap, edgeFlip] using this
        rw [hval, hfalse] at hd
        exact (hd.1 rfl).elim
    · intro he
      have hp' : (kmswStage w n).present e.val = true :=
        (kmswStage_status w n).2.2.1 e.val he
      exact False.elim (hp hp')

/-- The missing west dart of an outer edge is in UR exactly when that dart is -/
theorem kmswStageDirectedMap_UR_west (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    (kmswStageDirectedMap w n).missing (e, false) ∧
      (kmswStageDirectedMap w n).IsOuter (e, false) ↔
      e.val ∈ (kmswStage w n).UR := by
  constructor
  · rintro ⟨hmiss, houter⟩
    have hword := (stageOuterWord_mem_iff_outer w n (e, false)).2 houter
    have hclass := (stageOuterWord_mem_iff w n (e, false)).1 hword
    rcases hclass with ⟨_, hUL | hUR⟩ | ⟨htrue, _⟩
    · have hp := (kmswStage_status w n).2.1 e.val hUL
      change (kmswStage w n).present e.val = false at hmiss
      rw [hp] at hmiss
      cases hmiss
    · exact hUR
    · cases htrue
  · intro he
    have hword : (e, false) ∈ stageOuterWord w n := by
      apply (stageOuterWord_mem_iff w n (e, false)).2
      exact Or.inl ⟨rfl, Or.inr he⟩
    constructor
    · change (kmswStage w n).present e.val = false
      exact ((kmswStage_status w n).1 e.val e.isLt).2 (Or.inl he)
    · exact (stageOuterWord_mem_iff_outer w n (e, false)).1 hword

/-- The missing east dart of an outer edge is in LL exactly when that dart is -/
theorem kmswStageDirectedMap_LL_east (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    (kmswStageDirectedMap w n).missing (e, true) ∧
      (kmswStageDirectedMap w n).IsOuter (e, true) ↔
      e.val ∈ (kmswStage w n).LL := by
  constructor
  · rintro ⟨hmiss, houter⟩
    have hword := (stageOuterWord_mem_iff_outer w n (e, true)).2 houter
    have hclass := (stageOuterWord_mem_iff w n (e, true)).1 hword
    rcases hclass with ⟨hfalse, _⟩ | ⟨_, hLR | hLL⟩
    · cases hfalse
    · have hp := (kmswStage_status w n).2.2.1 e.val hLR
      change (kmswStage w n).present e.val = false at hmiss
      rw [hp] at hmiss
      cases hmiss
    · exact hLL
  · intro he
    have hword : (e, true) ∈ stageOuterWord w n := by
      apply (stageOuterWord_mem_iff w n (e, true)).2
      exact Or.inr ⟨rfl, Or.inr he⟩
    constructor
    · change (kmswStage w n).present e.val = false
      exact ((kmswStage_status w n).1 e.val e.isLt).2 (Or.inr he)
    · exact (stageOuterWord_mem_iff_outer w n (e, true)).1 hword

/-- The cardinalities of the four finite dart sets are the source formulas -/
theorem kmswStage_boundary_dart_cardinalities (w : ℕ → Fin 3) (n : ℕ) :
    ((Finset.card (kmswStageULDartsFinset w n) : ℤ) = L w n - minL w n + 1) ∧
    ((Finset.card (kmswStageURDartsFinset w n) : ℤ) = R w n - minR w n) ∧
    ((Finset.card (kmswStageLLDartsFinset w n) : ℤ) = -minL w n) ∧
    ((Finset.card (kmswStageLRDartsFinset w n) : ℤ) = -minR w n + 1) := by
  have hUL : Finset.card (kmswStageULDartsFinset w n) =
      (kmswStageULDartRun w n).length := by
    rw [kmswStageULDartsFinset]
    exact List.toFinset_card_of_nodup (stageULDartRun_nodup w n)
  have hUR : Finset.card (kmswStageURDartsFinset w n) =
      (kmswStageURDartRun w n).length := by
    rw [kmswStageURDartsFinset]
    exact List.toFinset_card_of_nodup (stageURDartRun_nodup w n)
  have hLL : Finset.card (kmswStageLLDartsFinset w n) =
      (kmswStageLLDartRun w n).length := by
    rw [kmswStageLLDartsFinset]
    exact List.toFinset_card_of_nodup (stageLLDartRun_nodup w n)
  have hLR : Finset.card (kmswStageLRDartsFinset w n) =
      (kmswStageLRDartRun w n).length := by
    rw [kmswStageLRDartsFinset]
    exact List.toFinset_card_of_nodup (stageLRDartRun_nodup w n)
  have hULlen : (kmswStageULDartRun w n).length = (kmswStage w n).UL.length := by
    simp [kmswStageULDartRun, stageDarts]
  have hURlen : (kmswStageURDartRun w n).length = (kmswStage w n).UR.length := by
    simp [kmswStageURDartRun, stageDarts]
  have hLLlen : (kmswStageLLDartRun w n).length = (kmswStage w n).LL.length := by
    simp [kmswStageLLDartRun, stageDarts]
  have hLRlen : (kmswStageLRDartRun w n).length = (kmswStage w n).LR.length := by
    simp [kmswStageLRDartRun, stageDarts]
  constructor
  · rw [hUL, hULlen, kmswStage_UL_length]
  · constructor
    · rw [hUR, hURlen, kmswStage_UR_length]
    · constructor
      · rw [hLL, hLLlen, kmswStage_LL_length]
      · rw [hLR, hLRlen, kmswStage_LR_length]

/-- Each outer-face dart lies in exactly one of the finite UL, UR, LR, and LL -/
theorem kmswStage_outer_dart_exactly_one (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : (kmswStageDirectedMap w n).IsOuter d) :
    (d ∈ kmswStageULDartsFinset w n ∧
        d ∉ kmswStageURDartsFinset w n ∧ d ∉ kmswStageLRDartsFinset w n ∧
        d ∉ kmswStageLLDartsFinset w n) ∨
    (d ∈ kmswStageURDartsFinset w n ∧
        d ∉ kmswStageULDartsFinset w n ∧ d ∉ kmswStageLRDartsFinset w n ∧
        d ∉ kmswStageLLDartsFinset w n) ∨
    (d ∈ kmswStageLRDartsFinset w n ∧
        d ∉ kmswStageULDartsFinset w n ∧ d ∉ kmswStageURDartsFinset w n ∧
        d ∉ kmswStageLLDartsFinset w n) ∨
    (d ∈ kmswStageLLDartsFinset w n ∧
        d ∉ kmswStageULDartsFinset w n ∧ d ∉ kmswStageURDartsFinset w n ∧
        d ∉ kmswStageLRDartsFinset w n) := by
  have hword := (stageOuterWord_mem_iff_outer w n d).2 hd
  have hclass := (stageOuterWord_mem_iff w n d).1 hword
  rcases hclass with (⟨hfalse, hUL | hUR⟩ | ⟨htrue, hLR | hLL⟩)
  · left
    have hmem := (kmswStageULDartsFinset_mem w n d).2 ⟨hfalse, hUL⟩
    refine ⟨hmem, ?_, ?_, ?_⟩
    · intro hbad
      obtain ⟨_, hUR'⟩ := (kmswStageURDartsFinset_mem w n d).mp hbad
      have hp := (kmswStage_status w n).2.1 d.1.val hUL
      have hm := ((kmswStage_status w n).1 d.1.val d.1.isLt).2 (Or.inl hUR')
      rw [hp] at hm
      cases hm
    · intro hbad
      obtain ⟨htrue, _⟩ := (kmswStageLRDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (hfalse.symm.trans htrue)
    · intro hbad
      obtain ⟨htrue, _⟩ := (kmswStageLLDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (hfalse.symm.trans htrue)
  · right; left
    have hmem := (kmswStageURDartsFinset_mem w n d).2 ⟨hfalse, hUR⟩
    refine ⟨hmem, ?_, ?_, ?_⟩
    · intro hbad
      obtain ⟨_, hUL'⟩ := (kmswStageULDartsFinset_mem w n d).mp hbad
      have hp := (kmswStage_status w n).2.1 d.1.val hUL'
      have hm := ((kmswStage_status w n).1 d.1.val d.1.isLt).2 (Or.inl hUR)
      rw [hp] at hm
      cases hm
    · intro hbad
      obtain ⟨htrue, _⟩ := (kmswStageLRDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (hfalse.symm.trans htrue)
    · intro hbad
      obtain ⟨htrue, _⟩ := (kmswStageLLDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (hfalse.symm.trans htrue)
  · right; right; left
    have hmem := (kmswStageLRDartsFinset_mem w n d).2 ⟨htrue, hLR⟩
    refine ⟨hmem, ?_, ?_, ?_⟩
    · intro hbad
      obtain ⟨hfalse, _⟩ := (kmswStageULDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (htrue.symm.trans hfalse)
    · intro hbad
      obtain ⟨hfalse, _⟩ := (kmswStageURDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (htrue.symm.trans hfalse)
    · intro hbad
      obtain ⟨_, hLL'⟩ := (kmswStageLLDartsFinset_mem w n d).mp hbad
      have hp := (kmswStage_status w n).2.2.1 d.1.val hLR
      have hm := ((kmswStage_status w n).1 d.1.val d.1.isLt).2 (Or.inr hLL')
      rw [hp] at hm
      cases hm
  · right; right; right
    have hmem := (kmswStageLLDartsFinset_mem w n d).2 ⟨htrue, hLL⟩
    refine ⟨hmem, ?_, ?_, ?_⟩
    · intro hbad
      obtain ⟨hfalse, _⟩ := (kmswStageULDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (htrue.symm.trans hfalse)
    · intro hbad
      obtain ⟨hfalse, _⟩ := (kmswStageURDartsFinset_mem w n d).mp hbad
      exact Bool.noConfusion (htrue.symm.trans hfalse)
    · intro hbad
      obtain ⟨_, hLR'⟩ := (kmswStageLRDartsFinset_mem w n d).mp hbad
      have hp := (kmswStage_status w n).2.2.1 d.1.val hLR'
      have hm := ((kmswStage_status w n).1 d.1.val d.1.isLt).2 (Or.inr hLL)
      rw [hp] at hm
      cases hm

/-- The outer-face word lists UL, UR, reversed LR, and reversed LL, in that
order; its face successor follows the word (`defn:bound-edges`, -/
theorem kmswStage_outer_face_orbit_runs (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWordVal w n =
      ((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) ∧
    ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d := by
  exact ⟨stageOuterWordVal_eq_runs w n, stageOuterWord_faceSucc w n⟩

end DirectedDistances.KMSW
