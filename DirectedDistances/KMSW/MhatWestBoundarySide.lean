/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MhatWestBoundary

/-! # Side sensitivity of the M̂ west-boundary helper

the face opposite the reachable-submap interface edge is the west-side face.
The helper remains separate from identifying this edge with `β₀`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

/-- The three edge IDs in a triangle's creation record are distinct -/
theorem stageTriangleRecord_edgeIds_distinct (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    (stageTriangleRecord w j).1 ≠ (stageTriangleRecord w j).2.1 ∧
      (stageTriangleRecord w j).1 ≠ (stageTriangleRecord w j).2.2 ∧
      (stageTriangleRecord w j).2.1 ≠ (stageTriangleRecord w j).2.2 := by
  let s := kmswStage w j.val
  rcases j.property with hc | hc
  · by_cases hl : s.UL.dropLast.reverse = []
    · have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
      simp only [stageTriangleRecord, s, hc, hl]
      change s.active ≠ s.nextEdge ∧ s.active ≠ s.nextEdge + 1 ∧
        s.nextEdge ≠ s.nextEdge + 1
      omega
    · cases hl' : s.UL.dropLast.reverse with
      | nil => exact (hl hl').elim
      | cons e es =>
        have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
        have heUL : e ∈ s.UL := by
          have hem : e ∈ s.UL.dropLast.reverse := by rw [hl']; simp
          exact List.mem_of_mem_dropLast (List.mem_reverse.mp hem)
        have he : e < s.nextEdge :=
          (kmswStage_boundary_ids_lt_nextEdge w j.val).2 e
            (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ heUL)))
        have hnd := stageTriangleDartList_nodup w j
        have hnd' : [(e, false), (s.active, false), (s.nextEdge, true)].Nodup := by
          simpa [stageTriangleDartList, stageTriangleDartTriple, s, hc, hl'] using hnd
        have hnot : (e, false) ∉ [(s.active, false), (s.nextEdge, true)] :=
          (List.nodup_cons.mp hnd').1
        have hea : e ≠ s.active := by
          intro hh
          apply hnot
          simp [hh]
        simp only [stageTriangleRecord, s, hc, hl']
        change s.active ≠ s.nextEdge ∧ s.active ≠ e ∧ s.nextEdge ≠ e
        exact ⟨Nat.ne_of_lt ha, hea.symm, (Nat.ne_of_lt he).symm⟩
  · have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
    have h0 : w j.val ≠ 0 := by rw [hc]; decide
    simp only [stageTriangleRecord, h0]
    change s.active ≠ s.nextEdge ∧ s.active ≠ s.nextEdge + 1 ∧
      s.nextEdge ≠ s.nextEdge + 1
    omega

/-- The edge IDs of a creation-time face's three darts are pairwise distinct -/
theorem stageTriangleDartTriple_edgeIds_distinct (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    (stageTriangleDartTriple w j).1.1 ≠
        (stageTriangleDartTriple w j).2.1.1 ∧
      (stageTriangleDartTriple w j).1.1 ≠
        (stageTriangleDartTriple w j).2.2.1 ∧
      (stageTriangleDartTriple w j).2.1.1 ≠
        (stageTriangleDartTriple w j).2.2.1 := by
  let s := kmswStage w j.val
  rcases j.property with hc | hc
  · by_cases hl : s.UL.dropLast.reverse = []
    · have hrec := stageTriangleRecord_edgeIds_distinct w j
      simp only [stageTriangleRecord, s, hc, hl] at hrec
      have htri := stageTriangleDartTriple_left_fresh w j hc hl
      rw [htri]
      exact hrec
    · cases hl' : s.UL.dropLast.reverse with
      | nil => exact (hl hl').elim
      | cons e es =>
        have hrec := stageTriangleRecord_edgeIds_distinct w j
        simp only [stageTriangleRecord, s, hc, hl'] at hrec
        have htri := stageTriangleDartTriple_left_existing w j hc e es hl'
        rw [htri]
        exact ⟨hrec.2.1.symm, hrec.2.2.symm, hrec.1⟩
  · have hrec := stageTriangleRecord_edgeIds_distinct w j
    have h0 : w j.val ≠ 0 := by rw [hc]; decide
    simp only [stageTriangleRecord, h0] at hrec
    have htri := stageTriangleDartTriple_up w j hc
    rw [htri]
    exact ⟨hrec.2.1, hrec.1, hrec.2.2.symm⟩

/-- Every stored triangle comes from a creation time, is a three-dart face,
and has three distinct edge IDs (`def-kmsw`, -/
theorem storedTriangle_face_and_edgeIds_distinct (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles) :
    ∃ j : TriangleCreationTime w, ∃ hj : j.val < n,
      stageTriangleRecord w j = t ∧
      FaceSucc3Cycle (kmswMap w n).faceSucc
        (stageTriangleDart₁ w n j hj) (stageTriangleDart₂ w n j hj)
        (stageTriangleDart₃ w n j hj) ∧
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  have hmap : t ∈ (stageTriangleTimes w n).map (stageTriangleRecord w) := by
    rw [stageTriangleTimes_records]
    exact ht
  obtain ⟨j, hjmem, hrecord⟩ := List.mem_map.mp hmap
  have hj : j.val < n := (mem_stageTriangleTimes w n j).mp hjmem
  refine ⟨j, hj, hrecord, stageTriangle_isFace w j n hj, ?_⟩
  simpa only [hrecord] using stageTriangleRecord_edgeIds_distinct w j

/-- No edge contributes both of its opposite darts to one stored triangle -/
theorem stageTriangleFaceDarts_not_both_sides (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (e : Fin (kmswStage w n).nextEdge) :
    ¬ ((e, false) ∈ kmswStageTriangleFaceDarts w n j hj ∧
      (e, true) ∈ kmswStageTriangleFaceDarts w n j hj) := by
  have hids :
      (stageTriangleDart₁ w n j hj).1.val ≠
          (stageTriangleDart₂ w n j hj).1.val ∧
        (stageTriangleDart₁ w n j hj).1.val ≠
          (stageTriangleDart₃ w n j hj).1.val ∧
        (stageTriangleDart₂ w n j hj).1.val ≠
          (stageTriangleDart₃ w n j hj).1.val := by
    simpa [stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
      stageTriangleDartAt] using stageTriangleDartTriple_edgeIds_distinct w j
  intro h
  simp only [kmswStageTriangleFaceDarts, Set.mem_insert_iff,
    Set.mem_singleton_iff] at h
  rcases h with ⟨hf, ht⟩
  rcases hf with hf₁ | hf₂ | hf₃
  · rcases ht with ht₁ | ht₂ | ht₃
    · have hs₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.2) hf₁
      have hs₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.2) ht₁
      change false = (stageTriangleDart₁ w n j hj).2 at hs₁
      change true = (stageTriangleDart₁ w n j hj).2 at hs₂
      have hbool : false = true := hs₁.trans hs₂.symm
      cases hbool
    · have hi₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) hf₁
      have hi₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) ht₂
      exact hids.1 (hi₁.symm.trans hi₂)
    · have hi₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) hf₁
      have hi₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) ht₃
      exact hids.2.1 (hi₁.symm.trans hi₂)
  · rcases ht with ht₁ | ht₂ | ht₃
    · have hi₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) hf₂
      have hi₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) ht₁
      exact hids.1.symm (hi₁.symm.trans hi₂)
    · have hs₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.2) hf₂
      have hs₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.2) ht₂
      change false = (stageTriangleDart₂ w n j hj).2 at hs₁
      change true = (stageTriangleDart₂ w n j hj).2 at hs₂
      have hbool : false = true := hs₁.trans hs₂.symm
      cases hbool
    · have hi₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) hf₂
      have hi₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) ht₃
      exact hids.2.2 (hi₁.symm.trans hi₂)
  · rcases ht with ht₁ | ht₂ | ht₃
    · have hi₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) hf₃
      have hi₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) ht₁
      exact hids.2.1.symm (hi₁.symm.trans hi₂)
    · have hi₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) hf₃
      have hi₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) ht₂
      exact hids.2.2.symm (hi₁.symm.trans hi₂)
    · have hs₁ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.2) hf₃
      have hs₂ := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.2) ht₃
      change false = (stageTriangleDart₃ w n j hj).2 at hs₁
      change true = (stageTriangleDart₃ w n j hj).2 at hs₂
      have hbool : false = true := hs₁.trans hs₂.symm
      cases hbool

/-- Opposite darts of one edge cannot belong to the same stored triangle face
orbit. Each stored triangle has a three-dart face cycle with three distinct -/
theorem stageTriangle_edgeDarts_not_sameCycle (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (e : Fin (kmswStage w n).nextEdge) :
    ¬ ((e, false) ∈ kmswStageTriangleFaceDarts w n j hj ∧
      (e, true) ∈ kmswStageTriangleFaceDarts w n j hj) :=
  stageTriangleFaceDarts_not_both_sides w n j hj e

/-- The old active edge at a source-flow left exit has its created triangle
on the west, and its east-side face orbit is not that triangle at any later
is a side-sensitive M̂ boundary helper; the identification with `β₀` remains
separate. -/
theorem mhatWestBoundaryEdge_leftExit_sided (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 1 ≤ k) :
    let t := sourceFlowNL w h (k - 1)
    MhatWestBoundaryEdge w (act w (t - 1)) ∧
      ∀ n, (hn : t ≤ n) →
        ∃ j : TriangleCreationTime w, ∃ hj : j.val < n,
          j.val + 1 = t ∧
          kmswEastSideFaceOrbit w n
            ⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ ≠
              kmswStageTriangleFaceDarts w n j hj := by
  cases k with
  | zero => omega
  | succ m =>
    simp only [Nat.succ_sub_one]
    let t := sourceFlowNL w h m
    have htpos : 0 < t := by
      dsimp [t]
      rw [sourceFlowNL_eq_walkNL]
      have hs := (walkNL_spec w h m).1
      omega
    have hcode : w (t - 1) = 0 := by
      dsimp [t]
      rw [sourceFlowNL_eq_walkNL]
      exact walkNL_previous_code w h m
    have hshape : (kmswStage w (t - 1)).UL.dropLast.reverse = [] ∨
        ∃ e es, (kmswStage w (t - 1)).UL.dropLast.reverse = e :: es := by
      cases m with
      | zero =>
        have hsource := sourceFlow_firstLeftExit_triangle w h
        rcases hsource with ⟨⟨_, _, _, hUL, _, _, _⟩, _, _, _, _, _, _, _, _, _, _⟩
        exact Or.inl (by simpa [t] using hUL)
      | succ q =>
        have hsource := sourceFlow_leftExit_triangle w h (q + 2) (by omega)
        simp only [Nat.succ_sub_one] at hsource
        rcases hsource with ⟨⟨_, _, _, hparts⟩, _, _, _, _⟩
        rcases hparts with ⟨es, hUL, _, _, _, _, _, _⟩
        refine Or.inr ⟨act w (sourceFlowNR w h (q + 1) - 1), es, ?_⟩
        simpa [t] using hUL
    refine ⟨?_, ?_⟩
    · exact mhatWestBoundaryEdge_leftExit w h (m + 1) (by omega)
    · intro n hn
      let j : TriangleCreationTime w := ⟨t - 1, Or.inl hcode⟩
      have hj : j.val < n := by
        dsimp [j, t]
        omega
      have hbase :
          ((⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ :
            Fin (kmswStage w n).nextEdge), false) = stageTriangleDart₁ w n j hj ∨
          ((⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ :
            Fin (kmswStage w n).nextEdge), false) = stageTriangleDart₂ w n j hj ∨
          ((⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ :
            Fin (kmswStage w n).nextEdge), false) = stageTriangleDart₃ w n j hj := by
        rcases hshape with hnil | ⟨e, es, hcons⟩
        · have htri := stageTriangleDartTriple_left_fresh w j hcode
            (by simpa [j, t] using hnil)
          left
          apply Prod.ext
          · apply Fin.ext
            simp [stageTriangleDart₁, stageTriangleDartAt, htri, j, t, act]
          · simp [stageTriangleDart₁, stageTriangleDartAt, htri, j, t]
        · have htri := stageTriangleDartTriple_left_existing w j hcode e es
            (by simpa [j, t] using hcons)
          right
          left
          apply Prod.ext
          · apply Fin.ext
            simp [stageTriangleDart₂, stageTriangleDartAt, htri, j, t, act]
          · simp [stageTriangleDart₂, stageTriangleDartAt, htri, j, t]
      have hwestOrbit := kmswWestSideFaceOrbit_eq_triangleDarts w n j hj
        ⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ hbase
      have hfalseWest :
          ((⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ :
            Fin (kmswStage w n).nextEdge), false) ∈
              kmswWestSideFaceOrbit w n
                ⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ := by
        change (kmswMap w n).faceSucc.SameCycle
          (⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩, false)
          (⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩, false)
        exact Equiv.Perm.SameCycle.rfl
      have hfalseTri :
          ((⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ :
            Fin (kmswStage w n).nextEdge), false) ∈
              kmswStageTriangleFaceDarts w n j hj := by
        rw [← hwestOrbit]
        exact hfalseWest
      refine ⟨j, hj, ?_, ?_⟩
      · dsimp [j]
        omega
      · intro heq
        have htrueEast :
            ((⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ :
              Fin (kmswStage w n).nextEdge), true) ∈
                kmswEastSideFaceOrbit w n
                  ⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ := by
          change (kmswMap w n).faceSucc.SameCycle
            (⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩, true)
            (⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩, true)
          exact Equiv.Perm.SameCycle.rfl
        have htrueTri :
            ((⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩ :
              Fin (kmswStage w n).nextEdge), true) ∈
                kmswStageTriangleFaceDarts w n j hj := by
          rw [← heq]
          exact htrueEast
        exact (stageTriangleFaceDarts_not_both_sides w n j hj
          ⟨act w (t - 1), act_lt_nextEdge w (by omega)⟩) ⟨hfalseTri, htrueTri⟩

end DirectedDistances.KMSW
