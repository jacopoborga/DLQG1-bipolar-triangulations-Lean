/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.CutSeparation
public import DirectedDistances.KMSW.MapCutVertices
import DirectedDistances.KMSW.CutSeparationAEPath

/-! # Undirected disconnection at map cut vertices

The right boundary identifies a cut vertex with an active initial vertex at its
first strict vertical record. Finite-stage separation then shows that every
finite undirected edge path from the old vertex range to the new vertex range
passes through that record vertex (`def-cut-vertex`, -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk

/-- One unoriented traversal of a geometric edge, retaining its edge ID. -/
@[expose] def UndirectedEdgeStep (w : ℕ → Fin 3) (x e y : ℕ) : Prop :=
  (edgeWest w e = x ∧ edgeEast w e = y) ∨
  (edgeEast w e = x ∧ edgeWest w e = y)

/-- A finite edge-ID-preserving path with each geometric edge read in either -/
inductive FiniteUndirectedEdgePath (w : ℕ → Fin 3) : ℕ → ℕ → Type where
  | nil (x : ℕ) : FiniteUndirectedEdgePath w x x
  | cons {x y z : ℕ} (e : ℕ) (hstep : UndirectedEdgeStep w x e y)
      (tail : FiniteUndirectedEdgePath w y z) : FiniteUndirectedEdgePath w x z

/-- The vertices visited by a finite undirected edge path, including both
endpoints. -/
@[expose] def FiniteUndirectedEdgePath.vertices {w : ℕ → Fin 3} {x y : ℕ}
    : FiniteUndirectedEdgePath w x y → Set ℕ
  | .nil _ => {x}
  | .cons _ _ tail => {x} ∪ tail.vertices

private theorem finiteUndirectedPath_start_mem {w : ℕ → Fin 3} {x y : ℕ}
    (p : FiniteUndirectedEdgePath w x y) : x ∈ p.vertices := by
  induction p with
  | nil x => simp [FiniteUndirectedEdgePath.vertices]
  | cons e hstep tail ih => simp [FiniteUndirectedEdgePath.vertices]

private theorem recordEastSuccessor (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) :
    (kmswStage w n).east (act w n) + 1 = (kmswStage w n).nextVertex := by
  cases n with
  | zero => rfl
  | succ n =>
    have hstep : R w (n + 1) = R w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
    have hw : w n = 2 := by
      have ha := hA n (by omega)
      rw [hstep] at ha
      by_cases h0 : w n = 0
      · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at ha
        omega
      · by_cases h1 : w n = 1
        · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at ha
          omega
        · apply Fin.ext
          have hlt := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
          omega
    have hUR : (kmswStage w n).UR = [] := by
      obtain ⟨i, hi, hmin⟩ := runningMin_attained (R w) n
      have ha := hA i (by omega)
      have hle := runningMin_le (R w) n n le_rfl
      have hlen := kmswStage_UR_length w n
      rw [hstep, hw, RandomWalk.lazyTwoDimensionalStep_two] at ha
      change minR w n = R w i at hmin
      change minR w n ≤ R w n at hle
      have hz : (kmswStage w n).UR.length = 0 := by omega
      exact List.length_eq_zero_iff.mp hz
    simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hUR,
      State.addEdge, act]

private theorem edge_no_crossing_recordBefore (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) (e : ℕ) :
    let v := (kmswStage w n).west (act w n)
    let a := (kmswStage w n).east (act w n)
    let Before := {u | u < (kmswStage w n).nextVertex ∧ u ≠ v ∧ u ≠ a}
    (¬ (edgeWest w e ∈ Before ∧ edgeEast w e ∉ Before ∧ edgeEast w e ≠ v) ∧
     ¬ (edgeEast w e ∈ Before ∧ edgeWest w e ∉ Before ∧ edgeWest w e ≠ v)) := by
  dsimp only
  let m := max n e
  have hself : e < (kmswStage w e).nextEdge := by
    have hcount := CutConverse.allocation_count w e
    omega
  have halloc : e < (kmswStage w m).nextEdge := by
    have hmono := kmswStage_nextEdge_mono w (Nat.le_max_right n e)
    exact hself.trans_le (by simpa [m] using hmono)
  have hsep := kmswFiniteStage_cutSeparation w n hA hB m
    (Nat.le_max_left n e) e halloc
  have hends := edge_endpoints_eq w halloc
  rw [hends.1, hends.2] at hsep
  exact hsep

/-- Every right-boundary vertex is an active initial vertex at a strict
vertical record time. The successor boundary edge handles the east endpoint
of each right-boundary edge (`def-cut-vertex`, -/
private theorem mapRightBoundaryVertex_eq_activeInitial (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL0 : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) {v : ℕ}
    (hv : mapRightBoundaryVertex w hfin v) :
    ∃ n, (∀ j < n, R w n ≤ R w j - 1) ∧ activeInitial w n = v := by
  have hright := (mapRightBoundaryVertex_iff w hfin hL0 hR v).mp hv
  obtain ⟨e, he, hend⟩ := hright
  obtain ⟨i, rfl⟩ := (isRightBoundaryEdge_iff w hR e).mp he
  let P : ℕ → Prop := fun m => ∀ j, j < m → R w m < R w j
  have hPinf : {m | P m}.Infinite := by
    simpa [P] using right_record_infinite w hR
  obtain ⟨hPi, _⟩ := natSelect_spec hPinf i
  let n := natSelect P i
  have hPiN : ∀ j < n, R w n < R w j := by
    simpa [P, n] using hPi
  have hA : ∀ j < n, R w n ≤ R w j - 1 := by
    intro j hj
    have hstrict := hPiN j hj
    omega
  rcases hend with hvwest | hveast
  · have hEdge : kmswRightBoundaryEdge w i = act w n := by
      dsimp [kmswRightBoundaryEdge, n, P]
    refine ⟨n, hA, ?_⟩
    change edgeWest w (act w n) = v
    rw [← hEdge]
    exact hvwest
  · obtain ⟨_, hnext, _, _⟩ := kmswRightBoundary_infinite_path w hL0 hR
    obtain ⟨hPiNext, _⟩ := natSelect_spec hPinf (i + 1)
    let n' := natSelect P (i + 1)
    have hPiNextN : ∀ j < n', R w n' < R w j := by
      simpa [P, n'] using hPiNext
    have hANext : ∀ j < n', R w n' ≤ R w j - 1 := by
      intro j hj
      have hstrict := hPiNextN j hj
      omega
    have hEdgeNext : kmswRightBoundaryEdge w (i + 1) = act w n' := by
      dsimp [kmswRightBoundaryEdge, n', P]
    refine ⟨n', hANext, ?_⟩
    calc
      activeInitial w n' = edgeWest w (act w n') := rfl
      _ = edgeWest w (kmswRightBoundaryEdge w (i + 1)) := by rw [hEdgeNext]
      _ = edgeEast w (kmswRightBoundaryEdge w i) := (hnext i).symm
      _ = v := hveast

/-- Every finite undirected edge path from the old set of vertices to the new
vertex range contains the active initial vertex. Here the old set is
`{u | u < nextVertex n ∧ u ≠ activeInitial n ∧ u ≠ east(active n)}` and the -/
theorem kmswFiniteUndirectedPath_meets_recordVertex (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {x y : ℕ} (p : FiniteUndirectedEdgePath w x y)
    (hx : x ∈ {u | u < (kmswStage w n).nextVertex ∧
      u ≠ activeInitial w n ∧ u ≠ (kmswStage w n).east (act w n)})
    (hy : (kmswStage w n).east (act w n) ≤ y) :
    activeInitial w n ∈ p.vertices := by
  let v := (kmswStage w n).west (act w n)
  let a := (kmswStage w n).east (act w n)
  let Before : Set ℕ := {u | u < (kmswStage w n).nextVertex ∧ u ≠ v ∧ u ≠ a}
  have hv : activeInitial w n = v := CutConverse.activeInitial_eq w n
  have hx' : x ∈ Before := by
    change x < (kmswStage w n).nextVertex ∧ x ≠ activeInitial w n ∧ x ≠ a at hx
    change x < (kmswStage w n).nextVertex ∧ x ≠ v ∧ x ≠ a
    simpa [v, hv] using hx
  have haSucc : a + 1 = (kmswStage w n).nextVertex := by
    dsimp [a]
    exact recordEastSuccessor w n hA
  induction p with
  | nil x =>
    simp only [FiniteUndirectedEdgePath.vertices]
    change x ∈ Before at hx'
    change a ≤ x at hy
    change x < (kmswStage w n).nextVertex ∧ x ≠ v ∧ x ≠ a at hx'
    omega
  | @cons x z y e hstep tail ih =>
    simp only [FiniteUndirectedEdgePath.vertices, Set.mem_union]
    by_cases hxv : x = v
    · exact Or.inl (hv.trans hxv.symm)
    · have hsep := edge_no_crossing_recordBefore w n hA hB e
      dsimp only at hsep
      by_cases hzv : z = v
      · have hzmem : z ∈ tail.vertices := finiteUndirectedPath_start_mem tail
        have hvz : activeInitial w n = z := hv.trans hzv.symm
        exact Or.inr (hvz ▸ hzmem)
      have hzBeforeStage : z ∈
          {u | u < (kmswStage w n).nextVertex ∧
            u ≠ (kmswStage w n).west (act w n) ∧
            u ≠ (kmswStage w n).east (act w n)} := by
        rcases hstep with ⟨hW, hE⟩ | ⟨hE, hW⟩
        · have hwest : edgeWest w e ∈
              {u | u < (kmswStage w n).nextVertex ∧
                u ≠ (kmswStage w n).west (act w n) ∧
                u ≠ (kmswStage w n).east (act w n)} := by
            simpa [Before, v, a] using hW ▸ hx'
          have heastBefore : edgeEast w e ∈
              {u | u < (kmswStage w n).nextVertex ∧
                u ≠ (kmswStage w n).west (act w n) ∧
                u ≠ (kmswStage w n).east (act w n)} := by
            by_contra hnot
            exact hsep.1 ⟨hwest, hnot, by rw [hE]; exact hzv⟩
          simpa [hE] using heastBefore
        · have heast : edgeEast w e ∈
              {u | u < (kmswStage w n).nextVertex ∧
                u ≠ (kmswStage w n).west (act w n) ∧
                u ≠ (kmswStage w n).east (act w n)} := by
            simpa [Before, v, a] using hE ▸ hx'
          have hwestBefore : edgeWest w e ∈
              {u | u < (kmswStage w n).nextVertex ∧
                u ≠ (kmswStage w n).west (act w n) ∧
                u ≠ (kmswStage w n).east (act w n)} := by
            by_contra hnot
            exact hsep.2 ⟨heast, hnot, by rw [hW]; exact hzv⟩
          simpa [hW] using hwestBefore
      have hzBefore : z ∈ Before := by
        simpa [Before, v, a] using hzBeforeStage
      have hzOld : z ∈ {u | u < (kmswStage w n).nextVertex ∧
          u ≠ activeInitial w n ∧ u ≠ (kmswStage w n).east (act w n)} := by
        simpa [Before, v, a, hv] using hzBefore
      exact Or.inr (ih hzOld hy hzBefore)

/-- Every map-level cut vertex is an active initial vertex at its first visit;
the record inequalities follow from the map boundary characterization -/
theorem mapCutVertex_firstVisit_records (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) {v : ℕ}
    (hcut : mapCutVertex w hfin v) :
    ∃ n, v = activeInitial w n ∧
      (∀ j < n, activeInitial w j ≠ activeInitial w n) ∧
      (∀ j < n, R w n ≤ R w j - 1) ∧
      (∀ j, n ≤ j → L w n ≤ L w j) ∧ OnRightBoundary w v := by
  have hright : OnRightBoundary w v :=
    (mapRightBoundaryVertex_iff w hfin hL0 hR v).mp hcut.2
  have hrightMap : mapRightBoundaryVertex w hfin v := hcut.2
  have hex := mapRightBoundaryVertex_eq_activeInitial w hfin hL0 hR hrightMap
  obtain ⟨m, hAm, hmv⟩ := hex
  let T : ℕ → Prop := fun k => activeInitial w k = v
  have hT : ∃ k, T k := ⟨m, hmv⟩
  let n := Nat.find hT
  have hn : activeInitial w n = v := Nat.find_spec hT
  have hfirst : ∀ j < n, activeInitial w j ≠ activeInitial w n := by
    intro j hj heq
    have hTj : T j := by dsimp [T]; rw [heq, hn]
    exact (Nat.find_min hT hj) hTj
  have hcutN : mapCutVertex w hfin (activeInitial w n) := by
    rw [hn]
    exact hcut
  have hrecords := (mapCutVertex_first_visit_iff w hfin htrans hR hL0 n).mp
    ⟨hcutN, hfirst⟩
  exact ⟨n, hn.symm, hfirst, hrecords.1, hrecords.2, hright⟩

/-- Every non-source map-level cut vertex separates two vertices in the
undirected geometric graph: every finite edge path between the witnesses -/
theorem mapCutVertex_removed_disconnected (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) {v : ℕ}
    (hcut : mapCutVertex w hfin v) (hv0 : v ≠ 0) :
    ∃ x y, x ≠ v ∧ y ≠ v ∧
      ∀ p : FiniteUndirectedEdgePath w x y, v ∈ p.vertices := by
  obtain ⟨n, hnv, hfirst, hA, hB, _⟩ :=
    mapCutVertex_firstVisit_records w hfin htrans hR hL0 hcut
  let a := (kmswStage w n).east (act w n)
  have hvn : activeInitial w n ≠ 0 := by
    rw [← hnv]
    exact hv0
  have haSucc := recordEastSuccessor w n hA
  have hnext : 2 ≤ (kmswStage w n).nextVertex := by
    simpa [kmswStage, kmswInit] using
      CutConverse.nextVertex_mono w (Nat.zero_le n)
  have hzeroLt : 0 < (kmswStage w n).nextVertex := by omega
  have haPos : 0 < a := by dsimp [a] at haSucc ⊢; omega
  have hzeroBefore : (0 : ℕ) ∈
      {u | u < (kmswStage w n).nextVertex ∧
        u ≠ activeInitial w n ∧ u ≠ (kmswStage w n).east (act w n)} := by
    exact ⟨hzeroLt, Ne.symm hvn, Ne.symm (Nat.ne_of_gt haPos)⟩
  have haNeV : a ≠ activeInitial w n := by
    have h := activeEast_ne_activeInitial w (j := n) (n := n) le_rfl
    simpa [a] using h
  have haNe : a ≠ v := by
    intro hav
    apply haNeV
    exact hav.trans hnv
  refine ⟨0, a, Ne.symm hv0, haNe, ?_⟩
  intro p
  have hmeet := kmswFiniteUndirectedPath_meets_recordVertex w n hA hB p
    hzeroBefore (by rfl)
  rw [← hnv] at hmeet
  exact hmeet

/-- Almost surely, every non-source map-level cut vertex of the UIQBOT
realization disconnects the undirected geometric graph. -/
theorem pitmanCodes_ae_mapCutVertex_removed_disconnected :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        Filter.Tendsto (L w) Filter.atTop Filter.atTop ∧
          (∀ a : ℤ, ∃ n, R w n ≤ a) ∧
          (∀ j, 0 ≤ L w j) ∧
          ∀ v, mapCutVertex w hfin v → v ≠ 0 →
            ∃ x y, x ≠ v ∧ y ≠ v ∧
              ∀ p : FiniteUndirectedEdgePath w x y, v ∈ p.vertices := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
  dsimp at hω
  obtain ⟨hfin, htrans, hR, hL0, _⟩ := hω
  refine ⟨hfin, htrans, hR, hL0, ?_⟩
  intro v hcut hv0
  exact mapCutVertex_removed_disconnected
    (pitmanCode (fun i => ω (i + 1))) hfin htrans hR hL0 hcut hv0

end DirectedDistances.KMSW
