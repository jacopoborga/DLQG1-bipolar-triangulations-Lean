/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineReachability
public import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.KMSW.ActiveTimeMonotone
import DirectedDistances.KMSW.OutgoingInterval

/-! # Finite-stage reachability for the north flow line

Supporting stage-level reachability data toward `lem-flow-line-times`, -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- The finite-stage reachable vertex IDs, computed by inserting the terminal
vertex of each active edge when its initial vertex is already reachable.
At stage zero the root edge has endpoints `0` and `1` -/
@[expose] def stageReachableIds (w : ℕ → Fin 3) : ℕ → Finset ℕ
  | 0 => {0, 1}
  | n + 1 =>
      let old := stageReachableIds w n
      let s := kmswStage w (n + 1)
      if s.west (act w (n + 1)) ∈ old then
        insert (s.east (act w (n + 1))) old else old

/-- Vertex IDs reachable from `0` in the present-edge quiver of stage `n` -/
@[expose] def betaStageReachableVertices (w : ℕ → Fin 3) (n : ℕ) : Set ℕ :=
  {v | Reachable (⟨0⟩ : StagePresentVertex w n) ⟨v⟩}

/-- The concrete code sequence from the flow-line reachability pitfall:
`0,1,2,2` followed by periodic `0,0,0,2,2` entries. -/
@[expose] def flowLinePitfallCode (n : ℕ) : Fin 3 :=
  if n < 4 then
    if n = 0 then 0 else if n = 1 then 1 else 2
  else
    match (n - 4) % 5 with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 2
    | _ => 2

/-- At stage four in the pitfall sequence the active west vertex is the
root-edge endpoint `1`, and the current UL edge IDs are `[3,4,5]` -/
theorem flowLinePitfall_stage_four_data :
    (kmswStage flowLinePitfallCode 4).west (act flowLinePitfallCode 4) = 1 ∧
      (kmswStage flowLinePitfallCode 4).UL = [3, 4, 5] := by
  decide

/-- The root-edge closure at stage four includes the active west vertex in the -/
theorem flowLinePitfall_stage_four_reachableIds :
    stageReachableIds flowLinePitfallCode 4 = ({0, 1, 4} : Finset ℕ) := by
  decide

/-- Reachability in a finite stage maps to reachability in the limit
present-edge graph (`remark-kmsw-infinite`, -/
theorem stageReachableVertices_subset_limit (w : ℕ → Fin 3) (n : ℕ) :
    ∀ v ∈ betaStageReachableVertices w n,
      Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩ := by
  intro v hv
  change Reachable (⟨0⟩ : StagePresentVertex w n) ⟨v⟩ at hv
  exact stageToLimit_reachable w n hv

private theorem path_before_arrow {w : ℕ → Fin 3} {u v z : PresentVertex w}
    (p : Path u v) (e : v ⟶ z) :
    ∀ f ∈ pathEdgeList p, ∃ hf : EdgePresent w f,
      actTime w f hf < actTime w e.val e.property.1 := by
  induction p generalizing z with
  | nil => simp [pathEdgeList]
  | @cons a b p f ih =>
      obtain hmem := ih f
      intro g hg
      have hlt := actTime_lt_of_consecutive w f.property.1 e.property.1
        (f.property.2.2.trans e.property.2.1.symm)
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨hgp, hltp⟩ := hmem g hg
        exact ⟨hgp, hltp.trans hlt⟩
      · have hgf := List.mem_singleton.mp hg
        subst g
        exact ⟨f.property.1, hlt⟩

private noncomputable def stagePath_of_active_prefix (w : ℕ → Fin 3) (n : ℕ)
    {u v : PresentVertex w} (p : Path u v)
    (hp : ∀ e ∈ pathEdgeList p, ∃ m ≤ n, e = act w m) :
    Path (⟨u.id⟩ : StagePresentVertex w n) ⟨v.id⟩ := by
  classical
  induction p with
  | nil => exact Path.nil
  | @cons a b p e ih =>
      have hp' : ∀ f ∈ pathEdgeList p, ∃ m ≤ n, f = act w m := by
        intro f hf
        apply hp f
        simp only [pathEdgeList, List.mem_append]
        exact Or.inl hf
      have p' := ih hp'
      have hlast : e.val ∈ pathEdgeList (Path.cons p e) := by
        simp [pathEdgeList]
      let hx := hp e.val hlast
      let m := Classical.choose hx
      have hm : m ≤ n := (Classical.choose_spec hx).1
      have hme : e.val = act w m := (Classical.choose_spec hx).2
      have hstage := present_mono w
        (act_lt_nextEdge w (le_rfl : m ≤ m))
        (kmswStage_active_present w m) n hm
      have halloc : e.val < (kmswStage w n).nextEdge := by
        rw [hme]
        exact hstage.1
      have hpres : (kmswStage w n).present e.val = true := by
        rw [hme]
        exact hstage.2
      have hends := edge_endpoints_eq w halloc
      let se : (⟨a.id⟩ : StagePresentVertex w n) ⟶
          (⟨b.id⟩ : StagePresentVertex w n) :=
        ⟨e.val, halloc, hpres,
          hends.1.trans e.property.2.1,
          hends.2.trans e.property.2.2⟩
      exact p'.cons se

private def stageToNext (w : ℕ → Fin 3) (n : ℕ) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w (n + 1)) where
  obj v := ⟨v.id⟩
  map {_ _} e := by
    have halloc := e.property.1
    have hpres := e.property.2.1
    have halloc' : e.val < (kmswStage w (n + 1)).nextEdge :=
      halloc.trans_le (kmswStage_nextEdge_mono w (m := n) (n := n + 1) (by omega))
    have hpres' := (present_mono w (n := n) (e := e.val) halloc hpres
      (n + 1) (by omega)).2
    have hends := kmswStage_endpoints_stable w (m := n) (n := n + 1)
      (by omega) halloc
    exact ⟨e.val, halloc', hpres',
      hends.1.trans e.property.2.2.1,
      hends.2.trans e.property.2.2.2⟩

private def stagePathEdgeList {w : ℕ → Fin 3} {n : ℕ}
    {a : StagePresentVertex w n} :
    {b : StagePresentVertex w n} → Path a b → List ℕ
  | _, .nil => []
  | _, .cons p e => stagePathEdgeList p ++ [e.val]

private theorem stagePath_edges_activePrefix (w : ℕ → Fin 3) (n : ℕ)
    {a b : StagePresentVertex w n} (p : Path a b) :
    ∀ e ∈ stagePathEdgeList p, ∃ m ≤ n, e = act w m := by
  induction p with
  | nil => simp [stagePathEdgeList]
  | @cons a b p e ih =>
      intro f hf
      rcases (by simpa [stagePathEdgeList] using hf) with hf | hf
      · exact ih f hf
      · subst f
        exact stagePresent_exists_active w n e.val e.property.1
          e.property.2.1

/-- Every vertex inserted by the active-edge closure is reachable in the
corresponding finite-stage present graph (`def-kmsw`, -/
theorem stageReachableIds_subset_vertices (w : ℕ → Fin 3) (n : ℕ) :
    ∀ v ∈ stageReachableIds w n, v ∈ betaStageReachableVertices w n := by
  induction n with
  | zero =>
      intro v hv
      have hv' : v = 0 ∨ v = 1 := by simpa [stageReachableIds] using hv
      rcases hv' with rfl | rfl
      · exact ⟨Path.nil⟩
      · exact ⟨Hom.toPath (initialEdgeArrow w 0)⟩
  | succ n ih =>
      intro v hv
      by_cases htail :
          (kmswStage w (n + 1)).west (act w (n + 1)) ∈ stageReachableIds w n
      · simp only [stageReachableIds, htail, ↓reduceIte,
          Finset.mem_insert] at hv
        rcases hv with hnew | hold
        · subst v
          have hwest : (kmswStage w (n + 1)).west (act w (n + 1)) ∈
              betaStageReachableVertices w n := ih _ htail
          obtain ⟨p⟩ := hwest
          have p' := (stageToNext w n).mapPath p
          let a : (⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ :
              StagePresentVertex w (n + 1)) ⟶
              ⟨(kmswStage w (n + 1)).east (act w (n + 1))⟩ :=
            ⟨act w (n + 1), act_lt_nextEdge w (le_rfl),
              kmswStage_active_present w (n + 1), rfl, rfl⟩
          exact ⟨p'.cons a⟩
        · have hold' : v ∈ betaStageReachableVertices w n := ih v hold
          obtain ⟨p⟩ := hold'
          exact ⟨(stageToNext w n).mapPath p⟩
      · have hvold : v ∈ stageReachableIds w n := by
          simpa only [stageReachableIds, htail, ite_false] using hv
        obtain ⟨p⟩ := ih v hvold
        exact ⟨(stageToNext w n).mapPath p⟩

private theorem path_edges_before_activeWest (w : ℕ → Fin 3) (n : ℕ)
    (v : PresentVertex w) (hv : v.id = (kmswStage w n).west (act w n))
    (p : Path (⟨0⟩ : PresentVertex w) v) :
    v.id = 0 ∨ ∀ e ∈ pathEdgeList p, ∃ m < n, e = act w m := by
  cases p with
  | nil => exact Or.inl rfl
  | @cons a b p e =>
      right
      intro f hf
      have hactive : EdgePresent w (act w n) :=
        EdgePresent.of_stage_present (act_lt_nextEdge w (le_rfl : n ≤ n))
          (kmswStage_active_present w n)
      have hends := edge_endpoints_eq w (act_lt_nextEdge w (le_rfl : n ≤ n))
      have hact : actTime w e.val e.property.1 < n := by
        have hcon := actTime_lt_of_consecutive w e.property.1 hactive
          (e.property.2.2.trans (hv.trans hends.1))
        rw [(actTime_eq_iff w (act w n) hactive n).2 rfl] at hcon
        exact hcon
      rcases (by simpa [pathEdgeList] using hf) with hf | hf
      · obtain ⟨hfp, hlt⟩ := path_before_arrow p e f hf
        exact ⟨actTime w f hfp, hlt.trans hact, actTime_spec w f hfp⟩
      · subst f
        exact ⟨actTime w e.val e.property.1, hact,
          actTime_spec w e.val e.property.1⟩

/-- The active west vertex is reachable using stage-`n` edges exactly when it
is reachable in the limit graph. The reverse implication uses strict increase
of activation times along directed paths (`lem-flow-line-times`, -/
theorem stageReachableVertices_activeWest_iff (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).west (act w n) ∈ betaStageReachableVertices w n ↔
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west (act w n)⟩ := by
  constructor
  · exact stageReachableVertices_subset_limit w n _
  · intro hr
    obtain ⟨p⟩ := hr
    have hp := path_edges_before_activeWest w n
      (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w) rfl p
    rcases hp with hroot | hbefore
    · have hzero : (kmswStage w n).west (act w n) = 0 := hroot
      change Reachable (⟨0⟩ : StagePresentVertex w n)
        ⟨(kmswStage w n).west (act w n)⟩
      rw [hzero]
    · have hpref : ∀ e ∈ pathEdgeList p, ∃ m ≤ n, e = act w m := by
        intro e he
        obtain ⟨m, hm, hme⟩ := hbefore e he
        exact ⟨m, Nat.le_of_lt hm, hme⟩
      exact ⟨stagePath_of_active_prefix w n p hpref⟩

/-- In the pitfall prefix, the active west vertex `1` is stage-reachable through
the root edge from `0`, while none of the UL edges `[3,4,5]` touches the root
vertex `0`, so a UL-only entry argument fails -/
theorem flowLinePitfall_stage_four_activeWest_reachable :
    (kmswStage flowLinePitfallCode 4).west (act flowLinePitfallCode 4) ∈
      betaStageReachableVertices flowLinePitfallCode 4 := by
  apply (stageReachableVertices_activeWest_iff flowLinePitfallCode 4).2
  rw [flowLinePitfall_stage_four_data.1]
  exact ⟨Hom.toPath ((stageToLimit flowLinePitfallCode 4).map
    (initialEdgeArrow flowLinePitfallCode 4))⟩

end DirectedDistances.KMSW
