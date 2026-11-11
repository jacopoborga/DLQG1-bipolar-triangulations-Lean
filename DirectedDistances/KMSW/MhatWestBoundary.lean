/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.FlowLineTimes
public import DirectedDistances.KMSW.StageTriangleDarts
public import DirectedDistances.KMSW.StageOuterCycle
public import DirectedDistances.KMSW.HatTriangleExact

/-! # West-side faces at left exits of flow lines

The west-side face convention here is the face-successor orbit of the dart
`(e, false)`. In the finite KMSW stages, false is the west dart and occurs on
the `UL` run of the outer word. These helpers supply only the west-side part
these edges with the infinite path `β₀` is a separate dependency. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Quiver

/-- The face incident to the west dart of an allocated geometric edge at a
false dart is the west dart; its face is represented by its orbit under the
stage map's face successor. -/
@[expose] def kmswWestSideFaceOrbit (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) : Set (StageDart (kmswStage w n).nextEdge) :=
  {d | (kmswMap w n).faceSucc.SameCycle (e, false) d}

/-- The face incident to the east dart of an allocated geometric edge at a -/
@[expose] def kmswEastSideFaceOrbit (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) : Set (StageDart (kmswStage w n).nextEdge) :=
  {d | (kmswMap w n).faceSucc.SameCycle (e, true) d}

/-- The three geometric darts bounding the face created at triangle time `j`, -/
@[expose] def kmswStageTriangleFaceDarts (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) :
    Set (StageDart (kmswStage w n).nextEdge) :=
  {stageTriangleDart₁ w n j hj, stageTriangleDart₂ w n j hj,
    stageTriangleDart₃ w n j hj}

private theorem sameCycle_iff_mem_three {D : Type*} [Fintype D] [DecidableEq D]
    (f : Equiv.Perm D) (a b c x : D)
    (h₁ : f a = b) (h₂ : f b = c) (h₃ : f c = a) :
    f.SameCycle a x ↔ x ∈ [a, b, c] := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hx.exists_nat_pow_eq
    have hp : ∀ k, (f ^ k) a = a ∨ (f ^ k) a = b ∨ (f ^ k) a = c := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with ha | hb | hc
        · rw [ha, h₁]
          exact Or.inr (Or.inl rfl)
        · rw [hb, h₂]
          exact Or.inr (Or.inr rfl)
        · rw [hc, h₃]
          exact Or.inl rfl
    rcases hp k with ha | hb | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (hk.symm.trans ha)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inl (hk.symm.trans hb))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inr (hk.symm.trans hc))
  · intro hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hxa | hxb | hxc
    · subst x
      exact Equiv.Perm.SameCycle.rfl
    · subst x
      rw [← h₁]
      have hp := (Equiv.Perm.sameCycle_pow_right (f := f) (x := a) (y := a)
        (n := 1)).2 Equiv.Perm.SameCycle.rfl
      simpa only [pow_one] using hp
    · subst x
      have h₂pow : (f ^ 2) a = c := by
        simp only [pow_two, Equiv.Perm.mul_apply, h₁, h₂]
      rw [← h₂pow]
      exact (Equiv.Perm.sameCycle_pow_right (f := f) (x := a) (y := a)
        (n := 2)).2 Equiv.Perm.SameCycle.rfl

private theorem faceOrbit_eq_three_darts {D : Type*} [Fintype D] [DecidableEq D]
    (f : Equiv.Perm D) (base a b c : D)
    (h₁ : f a = b) (h₂ : f b = c) (h₃ : f c = a)
    (hbase : base = a ∨ base = b ∨ base = c) :
    {d | f.SameCycle base d} = {a, b, c} := by
  have hab : f.SameCycle a b := by
    have hp := (Equiv.Perm.sameCycle_pow_right (f := f) (x := a) (y := a)
      (n := 1)).2 Equiv.Perm.SameCycle.rfl
    simpa only [pow_one, h₁] using hp
  have hac : f.SameCycle a c := by
    have hp := (Equiv.Perm.sameCycle_pow_right (f := f) (x := a) (y := a)
      (n := 2)).2 Equiv.Perm.SameCycle.rfl
    simpa only [pow_two, Equiv.Perm.mul_apply, h₁, h₂] using hp
  have hbase' : f.SameCycle a base := by
    rcases hbase with h | h | h
    · subst base
      exact Equiv.Perm.SameCycle.rfl
    · subst base
      exact hab
    · subst base
      exact hac
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have horbit : f.SameCycle base d ↔ f.SameCycle a d := by
    constructor
    · intro h
      exact hbase'.trans h
    · intro h
      exact hbase'.symm.trans h
  rw [horbit, (sameCycle_iff_mem_three f a b c d h₁ h₂ h₃)]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

/-- A three-cycle face has exactly its three creation darts as its face orbit.
This is the orbit-level form of the triangle face-cycle theorem. -/
theorem kmswWestSideFaceOrbit_eq_triangleDarts (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (e : Fin (kmswStage w n).nextEdge)
    (hbase : (e, false) = stageTriangleDart₁ w n j hj ∨
      (e, false) = stageTriangleDart₂ w n j hj ∨
      (e, false) = stageTriangleDart₃ w n j hj) :
    kmswWestSideFaceOrbit w n e = kmswStageTriangleFaceDarts w n j hj := by
  obtain ⟨h₁, h₂, h₃, _, _, _⟩ := stageTriangle_isFace w j n hj
  change {d | (kmswMap w n).faceSucc.SameCycle (e, false) d} = _
  exact faceOrbit_eq_three_darts (kmswMap w n).faceSucc (e, false)
    (stageTriangleDart₁ w n j hj) (stageTriangleDart₂ w n j hj)
    (stageTriangleDart₃ w n j hj) h₁ h₂ h₃ hbase

/-- The west dart of an edge is incident to a specified created triangle
exactly when that triangle's typed darts are its face-successor orbit. The
record equality keeps the source's stored edge triple tied to its geometric -/
@[expose] def kmswWestSideFaceIsTriangle (w : ℕ → Fin 3) (n : ℕ)
    (e : Fin (kmswStage w n).nextEdge) (t : ℕ × ℕ × ℕ) : Prop :=
  ∃ j : TriangleCreationTime w, ∃ hj : j.val < n,
    stageTriangleRecord w j = t ∧
      ((e, false) = stageTriangleDart₁ w n j hj ∨
        (e, false) = stageTriangleDart₂ w n j hj ∨
        (e, false) = stageTriangleDart₃ w n j hj) ∧
      kmswWestSideFaceOrbit w n e = kmswStageTriangleFaceDarts w n j hj

/-- A present edge of the reachable submap whose west-side face is a triangle
outside the reachable submap (`lem-flow-line-times`,
interface fact only; it does not identify the edge with `β₀`. -/
@[expose] def MhatWestBoundaryEdge (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  EdgePresent w e ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩ ∧
    ∃ n t, t ∈ (kmswStage w n).triangles ∧
      ∃ he : e < (kmswStage w n).nextEdge,
        kmswWestSideFaceIsTriangle w n ⟨e, he⟩ t ∧
        ¬ HatTriangleReachable w t

private theorem kmswLeftStepActiveWestFace (w : ℕ → Fin 3) (n : ℕ)
    (hcode : w n = 0)
    (hshape : (kmswStage w n).UL.dropLast.reverse = [] ∨
      ∃ e es, (kmswStage w n).UL.dropLast.reverse = e :: es) :
    let j : TriangleCreationTime w := ⟨n, Or.inl hcode⟩
    kmswWestSideFaceIsTriangle w (n + 1)
      ⟨(kmswStage w n).active,
        ((kmswStage_boundary_ids_lt_nextEdge w n).1).trans_le
          (kmswStage_nextEdge_mono w (Nat.le_succ n))⟩
      (stageTriangleRecord w j) ∧
    ¬ (kmswMap w (n + 1)).faceSucc.SameCycle
      ((⟨(kmswStage w n).active,
        ((kmswStage_boundary_ids_lt_nextEdge w n).1).trans_le
          (kmswStage_nextEdge_mono w (Nat.le_succ n))⟩ :
          Fin (kmswStage w (n + 1)).nextEdge), true)
      ((⟨(kmswStage w n).active,
        ((kmswStage_boundary_ids_lt_nextEdge w n).1).trans_le
          (kmswStage_nextEdge_mono w (Nat.le_succ n))⟩ :
          Fin (kmswStage w (n + 1)).nextEdge), false) := by
  dsimp only
  let j : TriangleCreationTime w := ⟨n, Or.inl hcode⟩
  let s := kmswStage w n
  change s.UL.dropLast.reverse = [] ∨
    ∃ e es, s.UL.dropLast.reverse = e :: es at hshape
  have hactiveOld : s.active < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).1
  have hactive : s.active < (kmswStage w (n + 1)).nextEdge := by
    exact (kmswStage_boundary_ids_lt_nextEdge w n).1.trans_le
      (kmswStage_nextEdge_mono w (Nat.le_succ n))
  have hj : j.val < n + 1 := by simp [j]
  have hcyc := stageTriangle_isFace w j (n + 1) hj
  have hbase :
      ((⟨s.active, hactive⟩ : Fin (kmswStage w (n + 1)).nextEdge), false) =
          stageTriangleDart₁ w (n + 1) j hj ∨
        ((⟨s.active, hactive⟩ : Fin (kmswStage w (n + 1)).nextEdge), false) =
          stageTriangleDart₂ w (n + 1) j hj ∨
        ((⟨s.active, hactive⟩ : Fin (kmswStage w (n + 1)).nextEdge), false) =
          stageTriangleDart₃ w (n + 1) j hj := by
    rcases hshape with hnil | ⟨e, es, hcons⟩
    · left
      simp [j, s, stageTriangleDart₁, stageTriangleDartAt,
        stageTriangleDartTriple_left_fresh w j hcode hnil]
    · right
      left
      simp [j, s, stageTriangleDart₂, stageTriangleDartAt,
        stageTriangleDartTriple_left_existing w j hcode e es hcons]
  have hface : kmswWestSideFaceOrbit w (n + 1) ⟨s.active, hactive⟩ =
      kmswStageTriangleFaceDarts w (n + 1) j hj :=
    kmswWestSideFaceOrbit_eq_triangleDarts w (n + 1) j hj ⟨s.active, hactive⟩ hbase
  refine ⟨⟨j, hj, rfl, hbase, hface⟩, ?_⟩
  intro hsame
  have hrightmem :
      ((⟨s.active, hactive⟩ : Fin (kmswStage w (n + 1)).nextEdge), true) ∈
        kmswWestSideFaceOrbit w (n + 1) ⟨s.active, hactive⟩ := by
    simpa only [kmswWestSideFaceOrbit, Set.mem_ofPred_eq] using hsame.symm
  rw [hface] at hrightmem
  simp only [kmswStageTriangleFaceDarts, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hrightmem
  rcases hshape with hnil | ⟨e, es, hcons⟩
  · simp [j, s, stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
      stageTriangleDartAt, stageTriangleDartTriple_left_fresh w j hcode hnil] at hrightmem
    change s.active = s.nextEdge at hrightmem
    have hold : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w n).1
    omega
  · simp [j, s, stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
      stageTriangleDartAt, stageTriangleDartTriple_left_existing w j hcode e es hcons] at hrightmem
    change s.active = s.nextEdge at hrightmem
    have hold : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w n).1
    omega

private theorem mhatWestBoundaryEdge_leftExit_succ (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) (hm : 1 ≤ m) :
    MhatWestBoundaryEdge w
      (act w (sourceFlowNL w h m - 1)) := by
  let t := sourceFlowNL w h m
  let n := t - 1
  let r := sourceFlowNR w h m
  let s := kmswStage w n
  have htpos : 0 < t := by
    dsimp [t]
    rw [sourceFlowNL_eq_walkNL]
    have hs := (walkNL_spec w h m).1
    omega
  have hindex : n + 1 = t := by
    dsimp [n]
    omega
  have hcode : w n = 0 := by
    dsimp [n, t]
    rw [sourceFlowNL_eq_walkNL]
    exact walkNL_previous_code w h m
  have hsource := sourceFlow_leftExit_triangle w h (m + 1) (by omega)
  simp only [Nat.succ_sub_one] at hsource
  rcases hsource with ⟨⟨hw, he, _, hshape⟩, hnot, _, _, _⟩
  rcases hshape with ⟨es, hUL, _, _, hnew, _, _, _⟩
  let tri := (act w n, act w t, act w (r - 1))
  let j : TriangleCreationTime w := ⟨n, Or.inl hcode⟩
  have hUL' : s.UL.dropLast.reverse = act w (r - 1) :: es := by
    simpa [s, n, t, r] using hUL
  have hnew' : act w t = s.nextEdge := by
    simpa [s, n, t] using hnew
  have hrecord : stageTriangleRecord w j = tri := by
    dsimp only [stageTriangleRecord, j]
    simp only [hcode, ↓reduceIte]
    rw [hUL']
    change (s.active, s.nextEdge, act w (r - 1)) =
      (act w n, act w t, act w (r - 1))
    rw [hnew']
    rfl
  have hmem : tri ∈ (kmswStage w (n + 1)).triangles := by
    rw [← stageTriangleTimes_records w (n + 1)]
    exact List.mem_map.mpr
      ⟨j, (mem_stageTriangleTimes w (n + 1) j).2 (by simp [j]), hrecord⟩
  have hleftface := (kmswLeftStepActiveWestFace w n hcode
    (Or.inr ⟨act w (r - 1), es, hUL⟩)).1
  have hface : kmswWestSideFaceIsTriangle w (n + 1)
      ⟨act w n, act_lt_nextEdge w (by omega)⟩ tri := by
    simpa [j, hrecord, act] using hleftface
  have holdBound : act w n < (kmswStage w n).nextEdge := act_lt_nextEdge w (le_rfl)
  have hendsOld := edge_endpoints_eq w holdBound
  have hendsNew := edge_endpoints_eq w (act_lt_nextEdge w (le_refl t))
  have hnotStage : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w t)⟩ := by
    simpa only [hindex] using hnot
  have hnotHat : ¬ HatTriangleReachable w tri := by
    intro hhat
    have hnewReach := (hhat (act w t) (by simp [tri])).1
    rw [← hendsNew.1] at hnewReach
    exact hnotStage (by simpa only [hindex] using hnewReach)
  change MhatWestBoundaryEdge w (act w n)
  refine ⟨⟨n, holdBound, kmswStage_active_present w n⟩, ?_, ?_, ?_⟩
  · rw [← hendsOld.1]
    exact hw
  · rw [← hendsOld.2]
    exact he
  · exact ⟨n + 1, tri, hmem, act_lt_nextEdge w (by omega), hface, hnotHat⟩

private theorem mhatWestBoundaryEdge_leftExit_first (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    MhatWestBoundaryEdge w
      (act w (sourceFlowNL w h 0 - 1)) := by
  let t := sourceFlowNL w h 0
  let n := t - 1
  let s := kmswStage w n
  have htpos : 0 < t := by
    dsimp [t]
    rw [sourceFlowNL_eq_walkNL]
    have hs := (walkNL_spec w h 0).1
    omega
  have hindex : n + 1 = t := by
    dsimp [n]
    omega
  have hcode : w n = 0 := by
    dsimp [n, t]
    rw [sourceFlowNL_eq_walkNL]
    exact walkNL_previous_code w h 0
  have hsource := sourceFlow_firstLeftExit_triangle w h
  rcases hsource with
    ⟨⟨_, hw, he, hUL, _, hnew, _⟩,
      _, _, _, _, _, _, _, hnot, _, _, _, _⟩
  have hUL' : s.UL.dropLast.reverse = [] := by
    simpa [s, n, t] using hUL
  have hUL'' : (kmswStage w n).UL.dropLast.reverse = [] := by
    simpa [s] using hUL'
  have hnew' : act w t = s.nextEdge := by
    simpa [s, n, t] using hnew
  let tri := (act w n, act w t, s.nextEdge + 1)
  let j : TriangleCreationTime w := ⟨n, Or.inl hcode⟩
  have hrecord : stageTriangleRecord w j = tri := by
    dsimp only [stageTriangleRecord, j]
    simp only [hcode, ↓reduceIte]
    rw [hUL'']
    change (s.active, s.nextEdge, s.nextEdge + 1) =
      (act w n, act w t, s.nextEdge + 1)
    rw [hnew']
    rfl
  have hmem : tri ∈ (kmswStage w (n + 1)).triangles := by
    rw [← stageTriangleTimes_records w (n + 1)]
    exact List.mem_map.mpr
      ⟨j, (mem_stageTriangleTimes w (n + 1) j).2 (by simp [j]), hrecord⟩
  have hleftface := (kmswLeftStepActiveWestFace w n hcode (Or.inl hUL)).1
  have hface : kmswWestSideFaceIsTriangle w (n + 1)
      ⟨act w n, act_lt_nextEdge w (by omega)⟩ tri := by
    simpa [j, hrecord, act] using hleftface
  have holdBound : act w n < (kmswStage w n).nextEdge := act_lt_nextEdge w (le_rfl)
  have hendsOld := edge_endpoints_eq w holdBound
  have hendsNew := edge_endpoints_eq w (act_lt_nextEdge w (le_refl t))
  have hnotStage : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w t)⟩ := by
    simpa only [hindex] using hnot
  have hnotHat : ¬ HatTriangleReachable w tri := by
    intro hhat
    have hnewReach := (hhat (act w t) (by simp [tri])).1
    rw [← hendsNew.1] at hnewReach
    exact hnotStage (by simpa only [hindex] using hnewReach)
  change MhatWestBoundaryEdge w (act w n)
  refine ⟨⟨n, holdBound, kmswStage_active_present w n⟩, ?_, ?_, ?_⟩
  · rw [← hendsOld.1]
    exact hw
  · rw [← hendsOld.2]
    exact he
  · exact ⟨n + 1, tri, hmem, act_lt_nextEdge w (by omega), hface, hnotHat⟩

/-- For every left exit, the old active edge has two root-reachable endpoints
and its west-side face is the newly created triangle, which has an unreachable
is the west-side B3 helper; identifying the edge with `β₀` remains separate. -/
theorem mhatWestBoundaryEdge_leftExit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 1 ≤ k) :
    MhatWestBoundaryEdge w
      (act w (sourceFlowNL w h (k - 1) - 1)) := by
  cases k with
  | zero => omega
  | succ m =>
    change MhatWestBoundaryEdge w (act w (sourceFlowNL w h m - 1))
    cases m with
    | zero => exact mhatWestBoundaryEdge_leftExit_first w h
    | succ q =>
      exact mhatWestBoundaryEdge_leftExit_succ w h (q + 1) (by omega)

end DirectedDistances.KMSW
