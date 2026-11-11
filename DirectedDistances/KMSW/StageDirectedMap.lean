/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageOuterWord
public import DirectedDistances.KMSW.StageIncidenceChains
public import DirectedDistances.KMSW.StageVertices

/-! # Directed KMSW stage maps

Bundles the finite KMSW rotation with its missing-edge and orientation
predicates (`defn:planar-map-with-missing-edges` and `def-kmsw`,
theorem is not yet exported by `StageOuterWordSucc`; the explicit `hcycle` -/

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

/-- West dart of the first upper-left boundary edge, used to mark the stage's -/
@[expose] def stageULHeadDart (w : ℕ → Fin 3) (n : ℕ) :
    StageDart (kmswStage w n).nextEdge := by
  let s := kmswStage w n
  have hUL : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w n).1
  have hsource : s.UL.head hUL ∈ (kmswStage w n).UL := by
    simpa only [s] using List.head_mem hUL
  have hbound : s.UL.head hUL < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hsource)))
  exact ((⟨s.UL.head hUL, hbound⟩ : Fin s.nextEdge), false)

private theorem stageULHeadDart_mem (w : ℕ → Fin 3) (n : ℕ) :
    stageULHeadDart w n ∈ stageOuterWord w n := by
  let s := kmswStage w n
  let hUL : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w n).1
  let hbound : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he
    have he' : e ∈ (kmswStage w n).UL := by simpa [s] using he
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl he')))
  have hmem : stageULHeadDart w n ∈ stageDarts s s.UL false hbound := by
    have heq : stageULHeadDart w n =
        ((⟨s.UL.head hUL, hbound _ (List.head_mem hUL)⟩ : Fin s.nextEdge), false) := by
      unfold stageULHeadDart
      apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    rw [heq]
    exact (stageDarts_mem_side s s.UL false hbound _ false).2
      ⟨rfl, List.head_mem hUL⟩
  change stageULHeadDart w n ∈
    ((stageDarts s s.UL false hbound ++ stageDarts s s.UR false _) ++
      stageDarts s s.LR.reverse true _) ++ stageDarts s s.LL.reverse true _
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl hmem))

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
    (hcycle : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ stageOuterWord w n ↔
      (kmswMap w n).IsOuter (stageULHeadDart w n) d := by
  let l := stageOuterWord w n
  let outer := stageULHeadDart w n
  have houter : outer ∈ l := stageULHeadDart_mem w n
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
    have hdl : d ∈ l := by simpa [l] using hd
    have hform : l.formPerm.SameCycle outer d :=
      sameCycle_formPerm_of_mem l hnodup hne houter hdl
    obtain ⟨k, _, hpow⟩ := hform.exists_pow_eq'
    exact ⟨k, (hiter k).trans hpow⟩
  · intro hd
    change (kmswMap w n).faceSucc.SameCycle outer d at hd
    obtain ⟨k, _, hpow⟩ := hd.exists_pow_eq'
    have hpowmem : (l.formPerm ^ k) outer ∈ l := hformMem k
    have hactual : ((kmswMap w n).faceSucc ^ k) outer ∈ l := by
      rw [hiter k]
      exact hpowmem
    rw [hpow] at hactual
    simpa [l] using hactual

private theorem stageOuterWord_west_mem (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    (e, false) ∈ stageOuterWord w n ↔
      e.val ∈ (kmswStage w n).UL ∨ e.val ∈ (kmswStage w n).UR := by
  simp only [stageOuterWord, List.mem_append, stageDarts_mem_side]
  simp

private theorem stageOuterWord_east_mem (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) :
    (e, true) ∈ stageOuterWord w n ↔
      e.val ∈ (kmswStage w n).LR ∨ e.val ∈ (kmswStage w n).LL := by
  simp only [stageOuterWord, List.mem_append, stageDarts_mem_side]
  simp

/-- The directed stage map keeps every KMSW edge as a geometric edge.
compiled incidence and rotation constructions. -/
@[expose] def kmswDirectedMap (w : ℕ → Fin 3) (n : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    DirectedMapWithMissing (StageDart (kmswStage w n).nextEdge) where
  toCombinatorialMap := kmswMap w n
  missing d := (kmswStage w n).present d.1.val = false
  missing_edgeInv := by
    intro d
    rfl
  tail d := (kmswStage w n).present d.1.val = true ∧ d.2 = false
  tail_iff := by
    intro d hd
    change ((kmswStage w n).present d.1.val = true ∧ d.2 = false) ↔
      ¬ ((kmswStage w n).present d.1.val = true ∧
        (edgeFlip (kmswStage w n).nextEdge d).2 = false)
    change ¬ ((kmswStage w n).present d.1.val = false) at hd
    cases hb : d.2 <;> cases hp : (kmswStage w n).present d.1.val <;>
      simp [edgeFlip, hb, hp] at hd ⊢
  tail_missing := by
    intro d hd ht
    change (kmswStage w n).present d.1.val = false at hd
    change (kmswStage w n).present d.1.val = true ∧ d.2 = false at ht
    rw [hd] at ht
    cases ht.1
  outer := stageULHeadDart w n
  missing_outer := by
    intro d hd
    have hbound : d.1.val < (kmswStage w n).nextEdge := d.1.isLt
    have hstatus := (kmswStage_status w n).1 d.1.val hbound
    have hrun : d.1.val ∈ (kmswStage w n).UR ∨
        d.1.val ∈ (kmswStage w n).LL := by
      apply hstatus.mp
      exact hd
    rcases hrun with hur | hll
    · have hw := (stageOuterWord_west_mem w n d.1).2 (Or.inr hur)
      by_cases hb : d.2
      · apply Or.inr
        have hout := (stageOuterWord_mem_iff_outer w n hcycle (d.1, false)).mp hw
        simpa [kmswMap, edgeFlip, hb] using hout
      · apply Or.inl
        have heq : d = (d.1, false) := by
          rcases d with ⟨e, b⟩
          simp_all
        rw [heq]
        exact (stageOuterWord_mem_iff_outer w n hcycle _).mp hw
    · have hw := (stageOuterWord_east_mem w n d.1).2 (Or.inr hll)
      by_cases hb : d.2
      · apply Or.inl
        have heq : d = (d.1, true) := by
          rcases d with ⟨e, b⟩
          simp_all
        rw [heq]
        exact (stageOuterWord_mem_iff_outer w n hcycle _).mp hw
      · apply Or.inr
        have hout := (stageOuterWord_mem_iff_outer w n hcycle (d.1, true)).mp hw
        simpa [kmswMap, edgeFlip, hb] using hout

/-- The orientation on present stage edges is acyclic, by strict increase of -/
theorem kmswDirectedMap_isAcyclic (w : ℕ → Fin 3) (n : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d) :
    (kmswDirectedMap w n hcycle).IsAcyclic := by
  let M := kmswDirectedMap w n hcycle
  let s := kmswStage w n
  let rank : M.VertexQuotient → ℚ :=
    Quotient.lift (fun d => kmswStageRank w n (stageEndpoint s d)) (by
      intro d d' h
      exact congrArg (kmswStageRank w n)
        ((stageRot_sameCycle_iff_endpoint_eq w n d d').1 h))
  have hstep : ∀ {u v : M.VertexQuotient}, M.directedStep u v → rank u < rank v := by
    intro u v hs
    rcases hs with ⟨d, _, htail, hu, hv⟩
    have hside : d.2 = false := htail.2
    let e := d.1.val
    have ht : stageEndpoint s d = s.west e := by
      simp [stageEndpoint, hside, e]
    have he : stageEndpoint s ((kmswMap w n).edgeInv d) = s.east e := by
      simp [kmswMap, edgeFlip, stageEndpoint, hside, e]
    rw [← hu, ← hv]
    change kmswStageRank w n (stageEndpoint s d) <
      kmswStageRank w n (stageEndpoint s ((kmswMap w n).edgeInv d))
    rw [ht, he]
    have hrank := kmswStageRank_strict w n e d.1.isLt
    exact hrank
  have hpath : ∀ {u v : M.VertexQuotient},
      Relation.TransGen M.directedStep u v → rank u < rank v := by
    intro u v hpath
    induction hpath with
    | single hs => exact hstep hs
    | tail _ hs ih => exact lt_trans ih (hstep hs)
  intro v hcyclePath
  exact (lt_irrefl _ (hpath hcyclePath))

/-- The upper-left edge IDs are exactly the false-side outer tail darts -/
theorem kmswDirectedMap_UL_bridge (w : ℕ → Fin 3) (n : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (e : Fin (kmswStage w n).nextEdge) :
    e.val ∈ (kmswStage w n).UL ↔
      (e, false) ∈ (kmswDirectedMap w n hcycle).ulDarts := by
  let M := kmswDirectedMap w n hcycle
  constructor
  · intro he
    have hp := (kmswStage_status w n).2.1 e.val he
    have hw := (stageOuterWord_west_mem w n e).2 (Or.inl he)
    have ho := (stageOuterWord_mem_iff_outer w n hcycle (e, false)).mp hw
    change ¬ M.missing (e, false) ∧ M.tail (e, false) ∧
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer (e, false)
    refine ⟨?_, ?_, ?_⟩
    · change ¬ ((kmswStage w n).present e.val = false)
      simp [hp]
    · change (kmswStage w n).present e.val = true ∧ false = false
      exact ⟨hp, rfl⟩
    · change (kmswMap w n).IsOuter (stageULHeadDart w n) (e, false)
      exact ho
  · intro hd
    change ¬ M.missing (e, false) ∧ M.tail (e, false) ∧
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer (e, false) at hd
    have hp : (kmswStage w n).present e.val = true := by
      have hnot : ¬ (kmswStage w n).present e.val = false := by
        exact hd.1
      cases h : (kmswStage w n).present e.val <;> simp_all
    have ho : (kmswMap w n).IsOuter (stageULHeadDart w n) (e, false) := by
      simpa [M, kmswDirectedMap] using hd.2.2
    have hw := (stageOuterWord_mem_iff_outer w n hcycle (e, false)).mpr ho
    rcases (stageOuterWord_west_mem w n e).mp hw with he | he
    · exact he
    · have hmiss := ((kmswStage_status w n).1 e.val e.isLt).2 (Or.inl he)
      rw [hp] at hmiss
      cases hmiss

/-- The lower-right edge IDs are exactly the true-side outer non-tail darts -/
theorem kmswDirectedMap_LR_bridge (w : ℕ → Fin 3) (n : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (e : Fin (kmswStage w n).nextEdge) :
    e.val ∈ (kmswStage w n).LR ↔
      (e, true) ∈ (kmswDirectedMap w n hcycle).lrDarts := by
  let M := kmswDirectedMap w n hcycle
  constructor
  · intro he
    have hp := (kmswStage_status w n).2.2.1 e.val he
    have hw := (stageOuterWord_east_mem w n e).2 (Or.inl he)
    have ho := (stageOuterWord_mem_iff_outer w n hcycle (e, true)).mp hw
    change ¬ M.missing (e, true) ∧ ¬ M.tail (e, true) ∧
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer (e, true)
    refine ⟨?_, ?_, ?_⟩
    · change ¬ ((kmswStage w n).present e.val = false)
      simp [hp]
    · change ¬ ((kmswStage w n).present e.val = true ∧ true = false)
      simp
    · change (kmswMap w n).IsOuter (stageULHeadDart w n) (e, true)
      exact ho
  · intro hd
    change ¬ M.missing (e, true) ∧ ¬ M.tail (e, true) ∧
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer (e, true) at hd
    have hp : (kmswStage w n).present e.val = true := by
      have hnot : ¬ (kmswStage w n).present e.val = false := by
        exact hd.1
      cases h : (kmswStage w n).present e.val <;> simp_all
    have ho : (kmswMap w n).IsOuter (stageULHeadDart w n) (e, true) := by
      simpa [M, kmswDirectedMap] using hd.2.2
    have hw := (stageOuterWord_mem_iff_outer w n hcycle (e, true)).mpr ho
    rcases (stageOuterWord_east_mem w n e).mp hw with he | he
    · exact he
    · have hmiss := ((kmswStage_status w n).1 e.val e.isLt).2 (Or.inr he)
      rw [hp] at hmiss
      cases hmiss

end DirectedDistances.KMSW
