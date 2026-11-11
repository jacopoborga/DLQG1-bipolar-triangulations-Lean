/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWBdy
public import DirectedDistances.KMSW.StageBoundaryMap

/-! # Geometric and ordering bridge for the KMSW boundary lemma

This file connects the state lists in the candidate proof of Lemma 3.6 to the
These are bridge lemmas, not a counted paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

private theorem kmsw_bdy_outerWord_eq_dartRuns (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWord w n =
      kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
        kmswStageLRDartRun w n ++ kmswStageLLDartRun w n := by
  simp [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
    kmswStageLRDartRun, kmswStageLLDartRun]

private theorem kmsw_bdy_dartRuns_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageULDartRun w n).Nodup ∧
    (kmswStageURDartRun w n).Nodup ∧
    (kmswStageLRDartRun w n).Nodup ∧
    (kmswStageLLDartRun w n).Nodup := by
  have h := stageOuterWord_nodup w n
  rw [kmsw_bdy_outerWord_eq_dartRuns] at h
  exact ⟨(List.nodup_append.mp (List.nodup_append.mp
      (List.nodup_append.mp h).1).1).1,
    (List.nodup_append.mp (List.nodup_append.mp
      (List.nodup_append.mp h).1).1).2.1,
    (List.nodup_append.mp (List.nodup_append.mp h).1).2.1,
    (List.nodup_append.mp h).2.1⟩

private theorem kmsw_bdy_stageDarts_edgeIds_nodup (s : State) (es : List ℕ)
    (side : Bool) (hes : ∀ e ∈ es, e < s.nextEdge)
    (hnd : (stageDarts s es side hes).Nodup) : es.Nodup := by
  have hinj : ∀ d ∈ stageDarts s es side hes, ∀ d' ∈ stageDarts s es side hes,
      d.1.val = d'.1.val → d = d' := by
    intro d hd d' hd' he
    obtain ⟨e, hee, rfl⟩ := (stageDarts_mem s es side hes d).mp hd
    obtain ⟨e', hee', rfl⟩ := (stageDarts_mem s es side hes _).mp hd'
    have : e = e' := he
    subst e'
    rfl
  have hmap : ((stageDarts s es side hes).map fun d => d.1.val).Nodup :=
    (List.nodup_map_iff_inj_on hnd).2 hinj
  have hmap_eq : (stageDarts s es side hes).map (fun d => d.1.val) = es := by
    simp [stageDarts, List.map_map]
  rw [hmap_eq] at hmap
  exact hmap

private theorem kmsw_bdy_boundary_lists_nodup (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).UL).Nodup ∧ ((kmswStage w n).UR).Nodup ∧
    ((kmswStage w n).LL).Nodup ∧ ((kmswStage w n).LR).Nodup := by
  have hrun := kmsw_bdy_dartRuns_nodup w n
  have hUL := kmsw_bdy_stageDarts_edgeIds_nodup (kmswStage w n)
    (kmswStage w n).UL false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inl he)))) hrun.1
  have hUR := kmsw_bdy_stageDarts_edgeIds_nodup (kmswStage w n)
    (kmswStage w n).UR false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inr he)))) hrun.2.1
  have hLR := kmsw_bdy_stageDarts_edgeIds_nodup (kmswStage w n)
    (kmswStage w n).LR.reverse true
    (fun e he => stageRun_edge_bound w n e (Or.inr (List.mem_reverse.mp he))) hrun.2.2.1
  have hLL := kmsw_bdy_stageDarts_edgeIds_nodup (kmswStage w n)
    (kmswStage w n).LL.reverse true
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inr (List.mem_reverse.mp he)))) hrun.2.2.2
  exact ⟨hUL, hUR, by simpa using hLL, by simpa using hLR⟩

/-- The edge IDs of each state boundary list are exactly the edges represented by
the corresponding geometric segment dart set; each boundary list has no repeated
edge, and the segment dart count is its list length. This is the geometric bridge -/
theorem kmsw_bdy_geometric_edge_bridge (w : ℕ → Fin 3) (n : ℕ) :
    (∀ e, e ∈ (kmswStage w n).UL ↔
      ∃ d, d ∈ (kmswStageDirectedMap w n).ulDarts ∧ d.1.val = e) ∧
    (∀ e, e ∈ (kmswStage w n).UR ↔
      ∃ d, (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = false ∧ d.1.val = e) ∧
    (∀ e, e ∈ (kmswStage w n).LL ↔
      ∃ d, (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = true ∧ d.1.val = e) ∧
    (∀ e, e ∈ (kmswStage w n).LR ↔
      ∃ d, d ∈ (kmswStageDirectedMap w n).lrDarts ∧ d.1.val = e) ∧
    ((kmswStage w n).UL).Nodup ∧ ((kmswStage w n).UR).Nodup ∧
    ((kmswStage w n).LL).Nodup ∧ ((kmswStage w n).LR).Nodup ∧
    Finset.card (kmswStageULDartsFinset w n) = (kmswStage w n).UL.length ∧
    Finset.card (kmswStageURDartsFinset w n) = (kmswStage w n).UR.length ∧
    Finset.card (kmswStageLLDartsFinset w n) = (kmswStage w n).LL.length ∧
    Finset.card (kmswStageLRDartsFinset w n) = (kmswStage w n).LR.length := by
  have hb := kmsw_bdy_boundary_lists_nodup w n
  have hrun := kmsw_bdy_dartRuns_nodup w n
  have hULmem : ∀ e, e ∈ (kmswStage w n).UL ↔
      ∃ d, d ∈ (kmswStageDirectedMap w n).ulDarts ∧ d.1.val = e := by
    intro e
    constructor
    · intro he
      have helt := stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inl he)))
      let d : StageDart (kmswStage w n).nextEdge := (⟨e, helt⟩, false)
      exact ⟨d, (kmswStageDirectedMap_UL_bridge w n ⟨e, helt⟩).1 he, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      have hfin : d ∈ kmswStageULDartsFinset w n :=
        (kmswStageULDartsFinset_map_mem w n d).2 hd
      exact (kmswStageULDartsFinset_mem w n d).mp hfin |>.2
  have hURmem : ∀ e, e ∈ (kmswStage w n).UR ↔
      ∃ d, (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = false ∧ d.1.val = e := by
    intro e
    constructor
    · intro he
      have helt := stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inr he)))
      let d : StageDart (kmswStage w n).nextEdge := (⟨e, helt⟩, false)
      have hgeom := (kmswStageDirectedMap_UR_west w n ⟨e, helt⟩).2 he
      exact ⟨d, hgeom.1, hgeom.2, rfl, rfl⟩
    · rintro ⟨d, hmiss, houter, hside, he⟩
      have hfin : d ∈ kmswStageURDartsFinset w n :=
        (kmswStageURDartsFinset_map_mem w n d).2 ⟨hmiss, houter, hside⟩
      have hm := (kmswStageURDartsFinset_mem w n d).mp hfin
      rw [he] at hm
      exact hm.2
  have hLLmem : ∀ e, e ∈ (kmswStage w n).LL ↔
      ∃ d, (kmswStageDirectedMap w n).missing d ∧
        (kmswStageDirectedMap w n).IsOuter d ∧ d.2 = true ∧ d.1.val = e := by
    intro e
    constructor
    · intro he
      have helt := stageRun_edge_bound w n e (Or.inl (Or.inr he))
      let d : StageDart (kmswStage w n).nextEdge := (⟨e, helt⟩, true)
      have hgeom := (kmswStageDirectedMap_LL_east w n ⟨e, helt⟩).2 he
      exact ⟨d, hgeom.1, hgeom.2, rfl, rfl⟩
    · rintro ⟨d, hmiss, houter, hside, he⟩
      have hfin : d ∈ kmswStageLLDartsFinset w n :=
        (kmswStageLLDartsFinset_map_mem w n d).2 ⟨hmiss, houter, hside⟩
      have hm := (kmswStageLLDartsFinset_mem w n d).mp hfin
      rw [he] at hm
      exact hm.2
  have hLRmem : ∀ e, e ∈ (kmswStage w n).LR ↔
      ∃ d, d ∈ (kmswStageDirectedMap w n).lrDarts ∧ d.1.val = e := by
    intro e
    constructor
    · intro he
      have helt := stageRun_edge_bound w n e (Or.inr he)
      let d : StageDart (kmswStage w n).nextEdge := (⟨e, helt⟩, true)
      exact ⟨d, (kmswStageDirectedMap_LR_bridge w n ⟨e, helt⟩).1 he, rfl⟩
    · rintro ⟨d, hd, he⟩
      have hfin : d ∈ kmswStageLRDartsFinset w n :=
        (kmswStageLRDartsFinset_map_mem w n d).2 hd
      have hm := (kmswStageLRDartsFinset_mem w n d).mp hfin
      rw [he] at hm
      exact hm.2
  have hcardUL : Finset.card (kmswStageULDartsFinset w n) = (kmswStage w n).UL.length := by
    change (kmswStageULDartRun w n).toFinset.card = (kmswStage w n).UL.length
    rw [List.toFinset_card_of_nodup hrun.1]
    simp [kmswStageULDartRun, stageDarts]
  have hcardUR : Finset.card (kmswStageURDartsFinset w n) = (kmswStage w n).UR.length := by
    change (kmswStageURDartRun w n).toFinset.card = (kmswStage w n).UR.length
    rw [List.toFinset_card_of_nodup hrun.2.1]
    simp [kmswStageURDartRun, stageDarts]
  have hcardLR : Finset.card (kmswStageLRDartsFinset w n) = (kmswStage w n).LR.reverse.length := by
    change (kmswStageLRDartRun w n).toFinset.card = (kmswStage w n).LR.reverse.length
    rw [List.toFinset_card_of_nodup hrun.2.2.1]
    simp [kmswStageLRDartRun, stageDarts]
  have hcardLL : Finset.card (kmswStageLLDartsFinset w n) = (kmswStage w n).LL.reverse.length := by
    change (kmswStageLLDartRun w n).toFinset.card = (kmswStage w n).LL.reverse.length
    rw [List.toFinset_card_of_nodup hrun.2.2.2]
    simp [kmswStageLLDartRun, stageDarts]
  refine ⟨hULmem, ?_⟩
  refine ⟨hURmem, ?_⟩
  refine ⟨hLLmem, ?_⟩
  refine ⟨hLRmem, ?_⟩
  refine ⟨hb.1, ?_⟩
  refine ⟨hb.2.1, ?_⟩
  refine ⟨hb.2.2.1, ?_⟩
  refine ⟨hb.2.2.2, ?_⟩
  refine ⟨hcardUL, ?_⟩
  refine ⟨hcardUR, ?_⟩
  refine ⟨by simpa using hcardLL, ?_⟩
  simpa using hcardLR

private theorem kmsw_bdy_stageDartRun_edgeIds (s : State) (es : List ℕ)
    (side : Bool) (hes : ∀ e ∈ es, e < s.nextEdge) :
    (stageDarts s es side hes).map (fun d => d.1.val) = es := by
  simp [stageDarts]

/-- Every dart run projects back to its state edge list in the source boundary
order. The two east runs use reversed list order, exactly as in -/
theorem kmsw_bdy_geometric_run_edge_order (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageULDartRun w n).map (fun d => d.1.val) = (kmswStage w n).UL ∧
    (kmswStageURDartRun w n).map (fun d => d.1.val) = (kmswStage w n).UR ∧
    (kmswStageLRDartRun w n).map (fun d => d.1.val) = (kmswStage w n).LR.reverse ∧
    (kmswStageLLDartRun w n).map (fun d => d.1.val) = (kmswStage w n).LL.reverse := by
  have hUL := kmsw_bdy_stageDartRun_edgeIds (kmswStage w n) (kmswStage w n).UL false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inl he))))
  have hUR := kmsw_bdy_stageDartRun_edgeIds (kmswStage w n) (kmswStage w n).UR false
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inl (Or.inr he))))
  have hLR := kmsw_bdy_stageDartRun_edgeIds (kmswStage w n) (kmswStage w n).LR.reverse true
    (fun e he => stageRun_edge_bound w n e (Or.inr (List.mem_reverse.mp he)))
  have hLL := kmsw_bdy_stageDartRun_edgeIds (kmswStage w n) (kmswStage w n).LL.reverse true
    (fun e he => stageRun_edge_bound w n e (Or.inl (Or.inr (List.mem_reverse.mp he))))
  exact ⟨hUL, hUR, by simpa [kmswStageLRDartRun] using hLR,
    by simpa [kmswStageLLDartRun] using hLL⟩

/-- The map's outer-face successor traverses precisely the geometric boundary
word `UL ++ UR ++ LR.reverse ++ LL.reverse`; its cyclic successor therefore
includes each within-segment adjacency and both segment junctions. This is the
geometric ordering bridge for `lem-kmsw-bdy` (`defn:bound-edges`, -/
theorem kmsw_bdy_geometric_outer_order (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWordVal w n =
      ((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true)) ++
      ((kmswStage w n).LL.reverse.map fun e => (e, true)) ∧
    ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d :=
  kmswStage_outer_face_orbit_runs w n

/-- Each indexed outer-word dart is followed by the next indexed dart under
face successor, including the cyclic wraparound. -/
theorem kmsw_bdy_geometric_outer_successor (w : ℕ → Fin 3) (n : ℕ) :
    ∀ i (hi : i < (stageOuterWord w n).length),
      (kmswMap w n).faceSucc ((stageOuterWord w n)[i]'hi) =
        (stageOuterWord w n)[(i + 1) % (stageOuterWord w n).length]'
          (Nat.mod_lt _ (Nat.zero_le i |>.trans_lt hi)) := by
  intro i hi
  have hface := (kmswStage_outer_face_orbit_runs w n).2
    ((stageOuterWord w n)[i]'hi) (List.getElem_mem hi)
  exact hface.trans (List.formPerm_apply_getElem _ (stageOuterWord_nodup w n) i hi)

/-- The lower-right edge list starts at the root edge, so the last dart of
`LR.reverse` is the root dart adjacent to the following `LL.reverse` segment -/
theorem kmsw_bdy_geometric_root_edge_in_LR (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR[0]? = some 0 := by
  rw [kmswStage_LR_eq, List.range_succ_eq_map]
  simp [act, kmswStage, kmswInit]

/-- The rank supplied by clause (i) of the candidate boundary lemma is the
k-th edge of the geometric lower-left segment in its root-first outer-face -/
theorem kmsw_bdy_geometric_LL_rank (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkmin : (k : ℤ) ≤ -minL w n) :
    ∃ hhit : ∃ t, L w t = -(k : ℤ),
      Nat.find hhit ≤ n ∧
      ∃ h : k - 1 < ((kmswStage w n).LL.reverse).length,
        ((kmswStage w n).LL.reverse)[k - 1]'h =
          kmswLLCreatedEdge w (Nat.find hhit) := by
  obtain ⟨hhit, hhitBound, ⟨hrank, hedge, _⟩⟩ :=
    kmsw_bdy_lower_left w n k hk hkmin
  exact ⟨hhit, hhitBound, ⟨hrank, hedge⟩⟩

end DirectedDistances.PaperProofs.Section3
