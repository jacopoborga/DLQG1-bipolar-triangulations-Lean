/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWBdyAdded
public import DirectedDistances.PaperProofs.Section3.KMSWBdyGeometric
public import DirectedDistances.PlanarMap.OuterBoundaryRuns
public import DirectedDistances.KMSW.StageTriangleDarts

/-! # Literal four-arc provider for the KMSW boundary lemma

This provider connects clauses (i)–(iv) and the cardinalities in -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open scoped Classical

private theorem kmsw_bdy_final_formPerm_sameCycle {D : Type*} [DecidableEq D]
    (l : List D) (hnd : l.Nodup) (hne : l ≠ []) {a b : D}
    (ha : a ∈ l) (hb : b ∈ l) : l.formPerm.SameCycle a b := by
  cases hlst : l with
  | nil => exact (hne hlst).elim
  | cons x xs =>
      have hnodup : (x :: xs).Nodup := by simpa [hlst] using hnd
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

private theorem kmsw_bdy_final_outer_cycle (w : ℕ → Fin 3) (n : ℕ) :
    IsOuterCycle (kmswStageDirectedMap w n) (stageOuterNonemptyWord w n) := by
  let l := stageOuterWord w n
  let o := stageULHeadDart w n
  have houterUL : o.1.val ∈ (kmswStage w n).UL := by
    simp [o, stageULHeadDart]
  have houterSide : o.2 = false := by
    simp [o, stageULHeadDart]
  have houter : o ∈ l := by
    apply (stageOuterWord_mem_iff w n o).2
    exact Or.inl ⟨houterSide, Or.inl houterUL⟩
  have hcycle := (kmsw_bdy_geometric_outer_order w n).2
  have hformMem : ∀ k : ℕ, (l.formPerm ^ k) o ∈ l := by
    intro k
    induction k with
    | zero => simpa [l] using houter
    | succ k ih =>
        simpa only [pow_succ', Equiv.Perm.mul_apply] using
          (List.formPerm_apply_mem_of_mem ih)
  have hiter : ∀ k : ℕ,
      ((kmswMap w n).faceSucc ^ k) o = (l.formPerm ^ k) o := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        calc
          ((kmswMap w n).faceSucc ^ (k + 1)) o =
              (kmswMap w n).faceSucc (((kmswMap w n).faceSucc ^ k) o) := by
                  simp only [pow_succ', Equiv.Perm.mul_apply]
          _ = (kmswMap w n).faceSucc ((l.formPerm ^ k) o) := by
                rw [ih]
          _ = l.formPerm ((l.formPerm ^ k) o) := hcycle _ (by
                simpa [l] using hformMem k)
          _ = (l.formPerm ^ (k + 1)) o := by
                simp only [pow_succ', Equiv.Perm.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    change (kmswMap w n).faceSucc.SameCycle o d
    have hd' : d ∈ l := by simpa [l, stageOuterNonemptyWord] using hd
    have hform : l.formPerm.SameCycle o d := by
      apply kmsw_bdy_final_formPerm_sameCycle l (stageOuterWord_nodup w n)
        (stageOuterWord_nonempty w n) houter hd'
    obtain ⟨k, _, hpow⟩ := hform.exists_pow_eq'
    exact ⟨k, (hiter k).trans hpow⟩
  · intro d hd
    change (kmswMap w n).faceSucc.SameCycle o d at hd
    obtain ⟨k, _, hpow⟩ := hd.exists_pow_eq'
    have hactual : ((kmswMap w n).faceSucc ^ k) o ∈ l := by
      rw [hiter k]
      exact hformMem k
    rw [hpow] at hactual
    simpa [l, stageOuterNonemptyWord] using hactual
  · intro d hd
    have hcycle := (kmsw_bdy_geometric_outer_order w n).2
    change (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d
    exact hcycle d hd

private theorem kmsw_bdy_final_ul_nonempty (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageDirectedMap w n).ulDarts.Nonempty := by
  have hactive : (kmswStage w n).active ∈ (kmswStage w n).UL := by
    obtain ⟨es, hlast⟩ := kmswStage_UL_last w n
    rw [hlast]
    simp
  have hlt := stageRun_edge_bound w n (kmswStage w n).active
    (Or.inl (Or.inl (Or.inl hactive)))
  let e : Fin (kmswStage w n).nextEdge := ⟨(kmswStage w n).active, hlt⟩
  refine ⟨(e, false), ?_⟩
  exact (kmswStageDirectedMap_UL_bridge w n e).1 hactive

private theorem kmsw_bdy_final_lr_nonempty (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageDirectedMap w n).lrDarts.Nonempty := by
  have hroot := kmsw_bdy_geometric_root_edge_in_LR w n
  have hrootmem : 0 ∈ (kmswStage w n).LR := List.mem_of_getElem? hroot
  have hlt := stageRun_edge_bound w n 0 (Or.inr hrootmem)
  let e : Fin (kmswStage w n).nextEdge := ⟨0, hlt⟩
  refine ⟨(e, true), ?_⟩
  exact (kmswStageDirectedMap_LR_bridge w n e).1 hrootmem

/-- A concrete four-arc witness whose ordered blocks are the KMSW stage dart
runs in outer-face order (UL forward, UR forward, LR reversed, LL reversed). -/
theorem kmsw_bdy_source_four_arcs (w : ℕ → Fin 3) (n : ℕ) :
    FourArcsWitness (kmswStageDirectedMap w n) (stageOuterNonemptyWord w n)
      (kmswStageULDartRun w n) (kmswStageURDartRun w n)
      (kmswStageLRDartRun w n) (kmswStageLLDartRun w n) ∧
    (∀ e, e ∈ (kmswStage w n).UL ↔
      ∃ d, d ∈ (kmswStageDirectedMap w n).ulDarts ∧ d.1.val = e) ∧
    (∀ e, e ∈ (kmswStage w n).UR ↔
      ∃ d, d ∈ urDarts (kmswStageDirectedMap w n) ∧ d.1.val = e) ∧
    (∀ e, e ∈ (kmswStage w n).LR ↔
      ∃ d, d ∈ (kmswStageDirectedMap w n).lrDarts ∧ d.1.val = e) ∧
    (∀ e, e ∈ (kmswStage w n).LL ↔
      ∃ d, d ∈ llDarts (kmswStageDirectedMap w n) ∧ d.1.val = e) ∧
    (kmswStageDirectedMap w n).ulDarts.ncard =
      (kmswStageULDartRun w n).length ∧
    (urDarts (kmswStageDirectedMap w n)).ncard =
      (kmswStageURDartRun w n).length ∧
    (kmswStageDirectedMap w n).lrDarts.ncard =
      (kmswStageLRDartRun w n).length ∧
    (llDarts (kmswStageDirectedMap w n)).ncard =
      (kmswStageLLDartRun w n).length := by
  classical
  let M := kmswStageDirectedMap w n
  let B := stageOuterNonemptyWord w n
  let ul := kmswStageULDartRun w n
  let ur := kmswStageURDartRun w n
  let lr := kmswStageLRDartRun w n
  let ll := kmswStageLLDartRun w n
  have hB : FourArcsWitness M B ul ur lr ll := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [M, B] using kmsw_bdy_final_outer_cycle w n
    · change (stageOuterWord w n) ~r
        (kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
          kmswStageLRDartRun w n ++ kmswStageLLDartRun w n)
      have heq : stageOuterWord w n =
          kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
            kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
        simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
          kmswStageLRDartRun, kmswStageLLDartRun]
      rw [heq]
    · intro d
      dsimp [ul, M, EnumeratesSet]
      simpa only [kmswStageULDartsFinset, List.mem_toFinset] using
        (kmswStageULDartsFinset_map_mem w n d)
    · intro d
      dsimp [lr, M, EnumeratesSet]
      simpa only [kmswStageLRDartsFinset, List.mem_toFinset] using
        (kmswStageLRDartsFinset_map_mem w n d)
    · intro d hd
      have hfin : d ∈ kmswStageURDartsFinset w n := by
        change d ∈ (kmswStageURDartRun w n).toFinset
        exact List.mem_toFinset.mpr (by simpa [ur] using hd)
      exact (kmswStageURDartsFinset_map_mem w n d).mp hfin |>.1
    · intro d hd
      have hfin : d ∈ kmswStageLLDartsFinset w n := by
        change d ∈ (kmswStageLLDartRun w n).toFinset
        exact List.mem_toFinset.mpr (by simpa [ll] using hd)
      exact (kmswStageLLDartsFinset_map_mem w n d).mp hfin |>.1
  have hUL := kmsw_bdy_final_ul_nonempty w n
  have hLR := kmsw_bdy_final_lr_nonempty w n
  have hURliteral := mem_urDarts_iff_of_witness M hUL hLR B ul ur lr ll hB
  have hLLliteral := mem_llDarts_iff_of_witness M hUL hLR B ul ur lr ll hB
  have hsetUL : M.ulDarts = (kmswStageULDartsFinset w n : Set _) := by
    ext d
    exact (kmswStageULDartsFinset_map_mem w n d).symm
  have hsetUR : urDarts M = (kmswStageURDartsFinset w n : Set _) := by
    ext d
    change d ∈ urDarts M ↔ d ∈ (kmswStageURDartRun w n).toFinset
    simp only [List.mem_toFinset]
    simpa [ur] using hURliteral d
  have hsetLR : M.lrDarts = (kmswStageLRDartsFinset w n : Set _) := by
    ext d
    exact (kmswStageLRDartsFinset_map_mem w n d).symm
  have hsetLL : llDarts M = (kmswStageLLDartsFinset w n : Set _) := by
    ext d
    change d ∈ llDarts M ↔ d ∈ (kmswStageLLDartRun w n).toFinset
    simp only [List.mem_toFinset]
    simpa [ll] using hLLliteral d
  obtain ⟨_, _, _, _, _, _, _, _, hULcard, hURcard, hLLcard, hLRcard⟩ :=
    kmsw_bdy_geometric_edge_bridge w n
  obtain ⟨hULorder, hURorder, hLRorder, hLLorder⟩ :=
    kmsw_bdy_geometric_run_edge_order w n
  have hULlen : (kmswStageULDartRun w n).length = (kmswStage w n).UL.length := by
    have h := congrArg List.length hULorder
    simpa only [List.length_map] using h
  have hURlen : (kmswStageURDartRun w n).length = (kmswStage w n).UR.length := by
    have h := congrArg List.length hURorder
    simpa only [List.length_map] using h
  have hLRlen : (kmswStageLRDartRun w n).length = (kmswStage w n).LR.length := by
    have h := congrArg List.length hLRorder
    simpa only [List.length_map, List.length_reverse] using h
  have hLLlen : (kmswStageLLDartRun w n).length = (kmswStage w n).LL.length := by
    have h := congrArg List.length hLLorder
    simpa only [List.length_map, List.length_reverse] using h
  have hSetULcard : M.ulDarts.ncard = Finset.card (kmswStageULDartsFinset w n) := by
    rw [hsetUL]
    simp
  have hSetURcard : (urDarts M).ncard = Finset.card (kmswStageURDartsFinset w n) := by
    rw [hsetUR]
    simp
  have hSetLRcard : M.lrDarts.ncard = Finset.card (kmswStageLRDartsFinset w n) := by
    rw [hsetLR]
    simp
  have hSetLLcard : (llDarts M).ncard = Finset.card (kmswStageLLDartsFinset w n) := by
    rw [hsetLL]
    simp
  have hbridge := kmsw_bdy_geometric_edge_bridge w n
  refine ⟨hB, hbridge.1, ?_, hbridge.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rw [hbridge.2.1 e]
    constructor
    · rintro ⟨d, hmiss, houter, hside, he⟩
      have hfin : d ∈ kmswStageURDartsFinset w n :=
        (kmswStageURDartsFinset_map_mem w n d).2 ⟨hmiss, houter, hside⟩
      have hdUR : d ∈ ur := by
        have hrun : d ∈ kmswStageURDartRun w n := by
          simpa only [kmswStageURDartsFinset, List.mem_toFinset] using hfin
        simpa [ur] using hrun
      exact ⟨d, (hURliteral d).2 hdUR, he⟩
    · rintro ⟨d, hd, he⟩
      have hdUR : d ∈ ur := (hURliteral d).1 hd
      have hfin : d ∈ kmswStageURDartsFinset w n := by
        simpa only [kmswStageURDartsFinset, List.mem_toFinset] using
          (show d ∈ kmswStageURDartRun w n by simpa [ur] using hdUR)
      have hgeom := (kmswStageURDartsFinset_map_mem w n d).mp hfin
      exact ⟨d, hgeom.1, hgeom.2.1, hgeom.2.2, he⟩
  · intro e
    rw [hbridge.2.2.1 e]
    constructor
    · rintro ⟨d, hmiss, houter, hside, he⟩
      have hfin : d ∈ kmswStageLLDartsFinset w n :=
        (kmswStageLLDartsFinset_map_mem w n d).2 ⟨hmiss, houter, hside⟩
      have hdLL : d ∈ ll := by
        have hrun : d ∈ kmswStageLLDartRun w n := by
          simpa only [kmswStageLLDartsFinset, List.mem_toFinset] using hfin
        simpa [ll] using hrun
      exact ⟨d, (hLLliteral d).2 hdLL, he⟩
    · rintro ⟨d, hd, he⟩
      have hdLL : d ∈ ll := (hLLliteral d).1 hd
      have hfin : d ∈ kmswStageLLDartsFinset w n := by
        simpa only [kmswStageLLDartsFinset, List.mem_toFinset] using
          (show d ∈ kmswStageLLDartRun w n by simpa [ll] using hdLL)
      have hgeom := (kmswStageLLDartsFinset_map_mem w n d).mp hfin
      exact ⟨d, hgeom.1, hgeom.2.1, hgeom.2.2, he⟩
  · calc
      M.ulDarts.ncard = Finset.card (kmswStageULDartsFinset w n) := hSetULcard
      _ = (kmswStage w n).UL.length := hULcard
      _ = (kmswStageULDartRun w n).length := hULlen.symm
  · calc
      (urDarts M).ncard = Finset.card (kmswStageURDartsFinset w n) := hSetURcard
      _ = (kmswStage w n).UR.length := hURcard
      _ = (kmswStageURDartRun w n).length := hURlen.symm
  · calc
      M.lrDarts.ncard = Finset.card (kmswStageLRDartsFinset w n) := hSetLRcard
      _ = (kmswStage w n).LR.length := hLRcard
      _ = (kmswStageLRDartRun w n).length := hLRlen.symm
  · calc
      (llDarts M).ncard = Finset.card (kmswStageLLDartsFinset w n) := hSetLLcard
      _ = (kmswStage w n).LL.length := hLLcard
      _ = (kmswStageLLDartRun w n).length := hLLlen.symm

private theorem kmsw_bdy_final_getElem_map {α β : Type*} (f : α → β)
    (xs : List α) (ys : List β) (hmap : xs.map f = ys) {i : ℕ}
    (hi : i < ys.length) :
    ∃ hx : i < xs.length, f (xs[i]'hx) = ys[i]'hi := by
  have hlen : xs.length = ys.length := by
    have h := congrArg List.length hmap
    simpa only [List.length_map] using h
  have hx : i < xs.length := by omega
  refine ⟨hx, ?_⟩
  have hget := List.getElem_map_rev f (l := xs) (n := i) (h := hx)
  simpa [hmap] using hget

/-- The candidate clauses of `lem-kmsw-bdy` restated on the literal ordered
130–148`). The LL/UL/UR runs and LR run in source orientation are used for
the indexed clauses; their darts belong to the corresponding witness-defined -/
theorem kmsw_bdy_source_candidate (w : ℕ → Fin 3) (n : ℕ) :
    (((∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minL w n),
      ∃ hhit : ∃ t, L w t = -(k : ℤ),
        Nat.find hhit ≤ n ∧
        ∃ h : k - 1 < ((kmswStage w n).LL.reverse).length,
          ((kmswStage w n).LL.reverse)[k - 1]'h =
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          (kmswStage w (Nat.find hhit - 1)).nextEdge ≤
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          kmswLLCreatedEdge w (Nat.find hhit) <
              (kmswStage w (Nat.find hhit)).nextEdge ∧
          (kmswStage w (Nat.find hhit)).present
              (kmswLLCreatedEdge w (Nat.find hhit)) = false ∧
          (kmswStage w (Nat.find hhit)).west (act w (Nat.find hhit)) =
              (kmswStage w (Nat.find hhit)).west
                (kmswLLCreatedEdge w (Nat.find hhit)) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).west (act w m) =
                (kmswStage w (Nat.find hhit)).west
                  (kmswLLCreatedEdge w (Nat.find hhit)) ↔
              L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j)) ∧
          IsLeast {m | (kmswStage w m).west (act w m) =
            (kmswStage w (Nat.find hhit)).west
              (kmswLLCreatedEdge w (Nat.find hhit))} (Nat.find hhit)) ∧
    (∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minR w n),
      ∃ hhit : ∃ t, R w t = -(k : ℤ),
        Nat.find hhit ≤ n ∧
        (kmswStage w n).LR[0]? = some 0 ∧
        ∃ h : k < (kmswStage w n).LR.length,
          (kmswStage w n).LR[k]'h = act w (Nat.find hhit) ∧
          (kmswStage w (Nat.find hhit)).present (act w (Nat.find hhit)) = true ∧
          (0 < Nat.find hhit →
            ¬ ((act w (Nat.find hhit) <
                (kmswStage w (Nat.find hhit - 1)).nextEdge) ∧
              (kmswStage w (Nat.find hhit - 1)).present
                (act w (Nat.find hhit)) = true)) ∧
          (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) =
            (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).east (act w m) =
                (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ↔
              R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j)) ∧
          IsLeast {m | (kmswStage w m).east (act w m) =
            (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit))}
            (Nat.find hhit)) ∧
    ((kmswStage w n).UL = (recUL w n).map (act w)) ∧
    (∀ m' m, m' ≤ m → m ≤ n → L w m' = L w m →
      (∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) →
      (kmswStage w m).west (act w m') = (kmswStage w m).west (act w m)) ∧
    (((kmswStage w n).UR).reverse = (recUR w n).map (kmswURCreatedEdge w)) ∧
    ((Finset.card (kmswStageULDartsFinset w n) : ℤ) =
        L w n - minL w n + 1) ∧
      ((Finset.card (kmswStageURDartsFinset w n) : ℤ) =
        R w n - minR w n) ∧
      ((Finset.card (kmswStageLLDartsFinset w n) : ℤ) = -minL w n) ∧
    ((Finset.card (kmswStageLRDartsFinset w n) : ℤ) = -minR w n + 1)) ∧
    (∀ k, ∀ hk : k < (recUL w n).length,
      let m := (recUL w n)[k]'hk
      (kmswStage w n).UL.length = (recUL w n).length ∧
      ∃ h : k < (kmswStage w n).UL.length,
        (kmswStage w n).UL[k]'h = act w m ∧
        (kmswStage w m).present (act w m) = true ∧
        (m = 0 → act w m = 0) ∧
        (0 < m → ¬ (act w m < (kmswStage w (m - 1)).nextEdge ∧
          (kmswStage w (m - 1)).present (act w m) = true)) ∧
        (kmswStage w n).present (act w m) = true) ∧
    (∀ k, ∀ hk : k < (recUR w n).length,
      let m := (recUR w n)[k]'hk
      ((kmswStage w n).UR.reverse).length = (recUR w n).length ∧
      ∃ h : k < (kmswStage w n).UR.reverse.length,
        (kmswStage w n).UR.reverse[k]'h = kmswURCreatedEdge w m ∧
        (kmswStage w (m - 1)).nextEdge ≤ kmswURCreatedEdge w m ∧
        kmswURCreatedEdge w m < (kmswStage w m).nextEdge ∧
        (kmswStage w n).present (kmswURCreatedEdge w m) = false)) ∧
    (∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minL w n),
      ∃ hhit : ∃ t, L w t = -(k : ℤ),
        0 < Nat.find hhit ∧ Nat.find hhit ≤ n ∧
        ∃ h : k - 1 < (kmswStageLLDartRun w n).length,
          (kmswStageLLDartRun w n)[k - 1]'h |>.1.val =
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          (kmswStageLLDartRun w n)[k - 1]'h ∈
              llDarts (kmswStageDirectedMap w n) ∧
          (kmswStage w (Nat.find hhit - 1)).nextEdge ≤
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          kmswLLCreatedEdge w (Nat.find hhit) <
              (kmswStage w (Nat.find hhit)).nextEdge ∧
          (kmswStage w (Nat.find hhit)).present
              (kmswLLCreatedEdge w (Nat.find hhit)) = false ∧
          (kmswStage w (Nat.find hhit)).west (act w (Nat.find hhit)) =
              (kmswStage w (Nat.find hhit)).west
                (kmswLLCreatedEdge w (Nat.find hhit)) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).west (act w m) =
                (kmswStage w (Nat.find hhit)).west
                  (kmswLLCreatedEdge w (Nat.find hhit)) ↔
              L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j)) ∧
          IsLeast {m | (kmswStage w m).west (act w m) =
            (kmswStage w (Nat.find hhit)).west
              (kmswLLCreatedEdge w (Nat.find hhit))} (Nat.find hhit)) ∧
    (∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minR w n),
      ∃ hhit : ∃ t, R w t = -(k : ℤ),
        Nat.find hhit ≤ n ∧
        (kmswStage w n).LR[0]? = some 0 ∧
        ∃ h : k < (kmswStageLRDartRun w n).reverse.length,
          (kmswStageLRDartRun w n).reverse[k]'h |>.1.val =
              act w (Nat.find hhit) ∧
          (kmswStageLRDartRun w n).reverse[k]'h ∈
              (kmswStageDirectedMap w n).lrDarts ∧
          (kmswStage w (Nat.find hhit)).present (act w (Nat.find hhit)) = true ∧
          (0 < Nat.find hhit →
            ¬ ((act w (Nat.find hhit) <
                (kmswStage w (Nat.find hhit - 1)).nextEdge) ∧
              (kmswStage w (Nat.find hhit - 1)).present
                (act w (Nat.find hhit)) = true)) ∧
          (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) =
            (kmswStage w (Nat.find hhit)).east
              ((kmswStageLRDartRun w n).reverse[k]'h |>.1.val) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).east (act w m) =
                (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ↔
              R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j)) ∧
          IsLeast {m | (kmswStage w m).east (act w m) =
            (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit))}
            (Nat.find hhit)) ∧
    (((kmswStageULDartRun w n).map (fun d => d.1.val) =
        (recUL w n).map (act w)) ∧
      (∀ m' m, m' ≤ m → m ≤ n → L w m' = L w m →
        (∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) →
        (kmswStage w m).west (act w m') = (kmswStage w m).west (act w m)) ∧
      (∀ k, ∀ hk : k < (recUL w n).length,
        let m := (recUL w n)[k]'hk
        (kmswStageULDartRun w n).length = (recUL w n).length ∧
        ∃ h : k < (kmswStageULDartRun w n).length,
          (kmswStageULDartRun w n)[k]'h |>.1.val = act w m ∧
          (kmswStage w m).present (act w m) = true ∧
          (m = 0 → act w m = 0) ∧
          (0 < m → ¬ (act w m < (kmswStage w (m - 1)).nextEdge ∧
            (kmswStage w (m - 1)).present (act w m) = true)) ∧
          (kmswStage w n).present (act w m) = true)) ∧
    ((((kmswStageURDartRun w n).reverse).map (fun d => d.1.val) =
        (recUR w n).map (kmswURCreatedEdge w)) ∧
      (∀ k, ∀ hk : k < (recUR w n).length,
        let m := (recUR w n)[k]'hk
        ((kmswStageURDartRun w n).reverse).length = (recUR w n).length ∧
        ∃ h : k < (kmswStageURDartRun w n).reverse.length,
          (kmswStageURDartRun w n).reverse[k]'h |>.1.val =
            kmswURCreatedEdge w m ∧
          (kmswStageURDartRun w n).reverse[k]'h ∈
            urDarts (kmswStageDirectedMap w n) ∧
          (kmswStage w (m - 1)).nextEdge ≤ kmswURCreatedEdge w m ∧
          kmswURCreatedEdge w m < (kmswStage w m).nextEdge ∧
          (kmswStage w n).present (kmswURCreatedEdge w m) = false)) ∧
    ((((kmswStageDirectedMap w n).ulDarts.ncard : ℤ) =
        L w n - minL w n + 1) ∧
      (((urDarts (kmswStageDirectedMap w n)).ncard : ℤ) =
        R w n - minR w n) ∧
      (((llDarts (kmswStageDirectedMap w n)).ncard : ℤ) = -minL w n) ∧
    (((kmswStageDirectedMap w n).lrDarts.ncard : ℤ) = -minR w n + 1)) := by
  classical
  have hfull := kmsw_bdy_candidate_full w n
  have hgeometry := kmsw_bdy_source_four_arcs w n
  obtain ⟨hB, _, _, _, _, hULncard, hURncard, hLRncard, hLLncard⟩ := hgeometry
  have hULnonempty := kmsw_bdy_final_ul_nonempty w n
  have hLRnonempty := kmsw_bdy_final_lr_nonempty w n
  have hULrun : ∀ d, d ∈ kmswStageULDartRun w n ↔
      d ∈ (kmswStageDirectedMap w n).ulDarts := hB.2.2.1
  have hURrun : ∀ d, d ∈ kmswStageURDartRun w n ↔
      d ∈ urDarts (kmswStageDirectedMap w n) := by
    intro d
    exact (mem_urDarts_iff_of_witness (kmswStageDirectedMap w n)
      hULnonempty hLRnonempty (stageOuterNonemptyWord w n)
      (kmswStageULDartRun w n) (kmswStageURDartRun w n)
      (kmswStageLRDartRun w n) (kmswStageLLDartRun w n) hB d).symm
  have hLRrun : ∀ d, d ∈ kmswStageLRDartRun w n ↔
      d ∈ (kmswStageDirectedMap w n).lrDarts := hB.2.2.2.1
  have hLLrun : ∀ d, d ∈ kmswStageLLDartRun w n ↔
      d ∈ llDarts (kmswStageDirectedMap w n) := by
    intro d
    exact (mem_llDarts_iff_of_witness (kmswStageDirectedMap w n)
      hULnonempty hLRnonempty (stageOuterNonemptyWord w n)
      (kmswStageULDartRun w n) (kmswStageURDartRun w n)
      (kmswStageLRDartRun w n) (kmswStageLLDartRun w n) hB d).symm
  obtain ⟨hULorder, hURorder, hLRorder, hLLorder⟩ :=
    kmsw_bdy_geometric_run_edge_order w n
  have hLRreverseOrder :
      ((kmswStageLRDartRun w n).reverse).map (fun d => d.1.val) =
        (kmswStage w n).LR := by
    calc
      ((kmswStageLRDartRun w n).reverse).map (fun d => d.1.val) =
          ((kmswStageLRDartRun w n).map (fun d => d.1.val)).reverse := by simp
      _ = ((kmswStage w n).LR.reverse).reverse := by rw [hLRorder]
      _ = (kmswStage w n).LR := List.reverse_reverse _
  have hURreverseOrder :
      ((kmswStageURDartRun w n).reverse).map (fun d => d.1.val) =
        ((kmswStage w n).UR).reverse := by
    simpa only [List.map_reverse] using congrArg List.reverse hURorder
  have hLists := kmsw_bdy_source_ordered_boundary_lists w n
  have hLowerLeft := kmsw_bdy_lower_left
  have hLowerRight := kmsw_bdy_lower_right
  have hULIndexed := kmsw_bdy_upper_left_indexed_record w n
  have hURIndexed := kmsw_bdy_upper_right_indexed_record w n
  refine ⟨hfull, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hkmin
    obtain ⟨hhit, hbound, hidx, hedge, hallocLo, hallocHi, hmissing,
        hwest, hvisits, hleast⟩ := kmsw_bdy_lower_left w n k hk hkmin
    have hpos : 0 < Nat.find hhit := by
      by_contra hnot
      have hzero : Nat.find hhit = 0 := by omega
      have hhit0 : L w 0 = -(k : ℤ) := by simpa [hzero] using Nat.find_spec hhit
      simp [L] at hhit0
      omega
    obtain ⟨hD, hmapval⟩ := kmsw_bdy_final_getElem_map
      (fun d => d.1.val) (kmswStageLLDartRun w n)
      ((kmswStage w n).LL.reverse) hLLorder hidx
    let d := (kmswStageLLDartRun w n)[k - 1]'hD
    have hdsegment : d ∈ llDarts (kmswStageDirectedMap w n) :=
      (hLLrun d).mp (List.getElem_mem hD)
    refine ⟨hhit, hpos, hbound, hD, ?_, hdsegment, hallocLo, hallocHi,
      hmissing, hwest, hvisits, hleast⟩
    calc
      d.1.val = ((kmswStage w n).LL.reverse)[k - 1]'hidx := hmapval
      _ = kmswLLCreatedEdge w (Nat.find hhit) := hedge
  · intro k hk hkmin
    obtain ⟨hhit, hbound, hroot, hidx, hedge, hpresent, hprevious,
        _heast, hvisits, hleast⟩ := kmsw_bdy_lower_right w n k hk hkmin
    obtain ⟨hD, hmapval⟩ := kmsw_bdy_final_getElem_map
      (fun d => d.1.val) ((kmswStageLRDartRun w n).reverse)
      ((kmswStage w n).LR) hLRreverseOrder hidx
    let d := (kmswStageLRDartRun w n).reverse[k]'hD
    have hdsegment : d ∈ (kmswStageDirectedMap w n).lrDarts := by
      apply (hLRrun d).mp
      exact List.mem_reverse.mp (List.getElem_mem hD)
    refine ⟨hhit, hbound, hroot, hD, ?_, hdsegment, hpresent, hprevious,
      ?_, hvisits, hleast⟩
    · calc
        d.1.val = ((kmswStage w n).LR)[k]'hidx := hmapval
        _ = act w (Nat.find hhit) := hedge
    · rw [show d.1.val = act w (Nat.find hhit) from hmapval.trans hedge]
  · refine ⟨?_, ?_, ?_⟩
    · calc
        (kmswStageULDartRun w n).map (fun d => d.1.val) =
            (kmswStage w n).UL := hULorder
        _ = (recUL w n).map (act w) := hLists.1
    · intro m' m hm'm hmn hlev habove
      exact kmsw_bdy_upper_left_initial_vertex w hm'm hlev habove
    · intro k hk
      let m := (recUL w n)[k]'hk
      obtain ⟨hstateLen, hstateIndex⟩ := hULIndexed k hk
      obtain ⟨hstate, hedge, hpresent, hzero, hactivation, hpresentN⟩ := hstateIndex
      have hrunLen : (kmswStageULDartRun w n).length = (recUL w n).length := by
        have hlen : (kmswStageULDartRun w n).length = (kmswStage w n).UL.length := by
          have h := congrArg List.length hULorder
          simpa only [List.length_map] using h
        exact hlen.trans hstateLen
      obtain ⟨hrun, hmapval⟩ := kmsw_bdy_final_getElem_map
        (fun d => d.1.val) (kmswStageULDartRun w n)
        ((kmswStage w n).UL) hULorder hstate
      have hdsegment : (kmswStageULDartRun w n)[k]'hrun ∈
          (kmswStageDirectedMap w n).ulDarts :=
        (hULrun _).mp (List.getElem_mem hrun)
      refine ⟨hrunLen, hrun, ?_, hpresent, hzero, hactivation, hpresentN⟩
      calc
        ((kmswStageULDartRun w n)[k]'hrun).1.val = (kmswStage w n).UL[k]'hstate := hmapval
        _ = act w m := hedge
  · refine ⟨?_, ?_⟩
    · calc
        ((kmswStageURDartRun w n).reverse).map (fun d => d.1.val) =
            ((kmswStage w n).UR).reverse := hURreverseOrder
        _ = (recUR w n).map (kmswURCreatedEdge w) := hLists.2.2.2
    · intro k hk
      let m := (recUR w n)[k]'hk
      obtain ⟨hstateLen, hstateIndex⟩ := hURIndexed k hk
      obtain ⟨hstate, hedge, hallocLo, hallocHi, hmissing⟩ := hstateIndex
      have hrunLen : ((kmswStageURDartRun w n).reverse).length =
          (recUR w n).length := by
        have hlen : ((kmswStageURDartRun w n).reverse).length =
            ((kmswStage w n).UR).reverse.length := by
          have h := congrArg List.length hURreverseOrder
          simpa only [List.length_map] using h
        exact hlen.trans hstateLen
      obtain ⟨hrun, hmapval⟩ := kmsw_bdy_final_getElem_map
        (fun d => d.1.val) ((kmswStageURDartRun w n).reverse)
        ((kmswStage w n).UR.reverse) hURreverseOrder hstate
      have hdsegment : ((kmswStageURDartRun w n).reverse)[k]'hrun ∈
          urDarts (kmswStageDirectedMap w n) := by
        apply (hURrun _).mp
        exact List.mem_reverse.mp (List.getElem_mem hrun)
      refine ⟨hrunLen, hrun, ?_, hdsegment, hallocLo, hallocHi, hmissing⟩
      calc
        (((kmswStageURDartRun w n).reverse)[k]'hrun).1.val =
            ((kmswStage w n).UR.reverse)[k]'hstate := hmapval
        _ = kmswURCreatedEdge w m := hedge
  · obtain ⟨_, _, _, _, _, _, _, _, hULfin, hURfin, hLLfin, hLRfin⟩ :=
      kmsw_bdy_geometric_edge_bridge w n
    have hULlength : (kmswStageULDartRun w n).length =
        (kmswStage w n).UL.length := by
      have h := congrArg List.length hULorder
      simpa only [List.length_map] using h
    have hURlength : (kmswStageURDartRun w n).length =
        (kmswStage w n).UR.length := by
      have h := congrArg List.length hURorder
      simpa only [List.length_map] using h
    have hLRlength : (kmswStageLRDartRun w n).length =
        (kmswStage w n).LR.length := by
      have h := congrArg List.length hLRorder
      simpa only [List.length_map, List.length_reverse] using h
    have hLLlength : (kmswStageLLDartRun w n).length =
        (kmswStage w n).LL.length := by
      have h := congrArg List.length hLLorder
      simpa only [List.length_map, List.length_reverse] using h
    have hULfinRun : Finset.card (kmswStageULDartsFinset w n) =
        (kmswStageULDartRun w n).length := hULfin.trans hULlength.symm
    have hURfinRun : Finset.card (kmswStageURDartsFinset w n) =
        (kmswStageURDartRun w n).length := hURfin.trans hURlength.symm
    have hLRfinRun : Finset.card (kmswStageLRDartsFinset w n) =
        (kmswStageLRDartRun w n).length := hLRfin.trans hLRlength.symm
    have hLLfinRun : Finset.card (kmswStageLLDartsFinset w n) =
        (kmswStageLLDartRun w n).length := hLLfin.trans hLLlength.symm
    have hULcast : ((kmswStageDirectedMap w n).ulDarts.ncard : ℤ) =
        (Finset.card (kmswStageULDartsFinset w n) : ℤ) := by
      exact congrArg (fun x : ℕ => (x : ℤ)) (hULncard.trans hULfinRun.symm)
    have hURcast : ((urDarts (kmswStageDirectedMap w n)).ncard : ℤ) =
        (Finset.card (kmswStageURDartsFinset w n) : ℤ) := by
      exact congrArg (fun x : ℕ => (x : ℤ)) (hURncard.trans hURfinRun.symm)
    have hLRcast : ((kmswStageDirectedMap w n).lrDarts.ncard : ℤ) =
        (Finset.card (kmswStageLRDartsFinset w n) : ℤ) := by
      exact congrArg (fun x : ℕ => (x : ℤ)) (hLRncard.trans hLRfinRun.symm)
    have hLLcast : ((llDarts (kmswStageDirectedMap w n)).ncard : ℤ) =
        (Finset.card (kmswStageLLDartsFinset w n) : ℤ) := by
      exact congrArg (fun x : ℕ => (x : ℤ)) (hLLncard.trans hLLfinRun.symm)
    have hformula := kmswStage_boundary_dart_cardinalities w n
    refine ⟨hULcast.trans hformula.1, hURcast.trans hformula.2.1,
      hLLcast.trans hformula.2.2.1, hLRcast.trans hformula.2.2.2⟩

end DirectedDistances.PaperProofs.Section3
