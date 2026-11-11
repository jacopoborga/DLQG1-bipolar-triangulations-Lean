module

public import DirectedDistances.KMSW.CutSeparationAEPath
public import DirectedDistances.KMSW.CutEquivalenceConverse
public import DirectedDistances.KMSW.InfiniteBoundary
import DirectedDistances.KMSW.CutEquivalence
import DirectedDistances.KMSW.InfiniteGeodesic
import DirectedDistances.RandomWalk.SecondCoordinateUnbounded

/-! # Cut separation from arbitrary allocated starts

to arbitrary starts in the finite side of a record vertex. -/

public section
namespace DirectedDistances.KMSW

open Quiver
open MeasureTheory
open DirectedDistances.RandomWalk

private theorem record_stage_before_empty_UR (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) (hn : 0 < n) :
    w (n - 1) = 2 ∧ (kmswStage w (n - 1)).UR = [] := by
  let k := n - 1
  have hnk : n = k + 1 := by dsimp [k]; omega
  have hRstep : R w (k + 1) = R w k +
      (RandomWalk.lazyTwoDimensionalStep (w k)).2 := Finset.sum_range_succ _ _
  have hdown : w k = 2 := by
    have hstrict := hA k (by omega)
    rw [hnk, hRstep] at hstrict
    by_cases h2 : (w k).val = 2
    · exact Fin.ext h2
    · have hval : (w k).val = 0 ∨ (w k).val = 1 := by
        have hlt := (w k).isLt
        omega
      rcases hval with h0 | h1
      · have hc : w k = 0 := Fin.ext h0
        rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hstrict
        omega
      · have hc : w k = 1 := Fin.ext h1
        rw [hc, RandomWalk.lazyTwoDimensionalStep_one] at hstrict
        omega
  have hRdown : R w (k + 1) = R w k - 1 := by
    rw [hRstep, hdown, RandomWalk.lazyTwoDimensionalStep_two]
    ring
  have hmin : minR w k = R w k := by
    obtain ⟨i, hik, hmin⟩ := runningMin_attained (R w) k
    change minR w k = R w i at hmin
    have hlow : R w k ≤ R w i := by
      have hi := hA i (by omega)
      rw [hnk, hRdown] at hi
      omega
    have hle := runningMin_le (R w) k k (le_refl k)
    change minR w k ≤ R w k at hle
    omega
  have hlen := kmswStage_UR_length w k
  have hURlen : ((kmswStage w k).UR.length : ℤ) = 0 := by
    rw [hlen, hmin]
    ring
  have hUR : (kmswStage w k).UR.length = 0 := by omega
  simpa [k] using And.intro hdown (List.length_eq_zero_iff.mp hUR)

private theorem pending_vertex_step (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v ∈ CutConverse.pendingVertices (kmswStage w n)) :
    v ∈ CutConverse.pendingVertices (kmswStage w (n + 1)) ∨
      activeInitial w (n + 1) = v := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have he' := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      tauto)
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) he').2
  by_cases h0 : w n = 0
  · have hUR : t.UR = s.UR := by
      change (kmswStep s (w n)).UR = _
      rw [h0]
      cases hs : s.UL.dropLast.reverse <;>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
    have hEast : t.east t.active = s.east s.active := by
      change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
      rw [h0]
      cases hs : s.UL.dropLast.reverse <;>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
    left
    change v ∈ s.east s.active :: s.UR.map s.east at hv
    change v ∈ t.east t.active :: t.UR.map t.east
    rw [hEast, hUR, hmap]
    exact hv
  · by_cases h1 : w n = 1
    · have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
        change (kmswStep s (w n)).UR = _
        simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep]
      have hEast : t.east t.active = s.nextVertex := by
        change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
        simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      have hNewEast : t.east (s.nextEdge + 1) = s.east s.active := by
        change (kmswStep s (w n)).east (s.nextEdge + 1) = _
        simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      have hpending : CutConverse.pendingVertices t =
          s.nextVertex :: CutConverse.pendingVertices s := by
        simp only [CutConverse.pendingVertices, hUR, List.map_cons,
          hEast, hNewEast, hmap]
      left
      change v ∈ s.east s.active :: s.UR.map s.east at hv
      rw [hpending]
      exact List.mem_cons_of_mem _ hv
    · have h2 : w n = 2 := by
        apply Fin.ext
        have hv' := (w n).isLt
        have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
        have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
        omega
      cases hs : s.UR with
      | nil =>
        have hpending : CutConverse.pendingVertices s = [s.east s.active] := by
          simp [CutConverse.pendingVertices, hs]
        have hval : v = s.east s.active := by
          rw [hpending] at hv
          simpa using hv
        right
        rw [CutConverse.activeInitial_eq]
        change t.west t.active = v
        rw [hval]
        have ht : t = kmswStepOfStep s .down := by
          change kmswStep s (w n) = _
          rw [h2]
          rfl
        rw [ht]
        simp [kmswStepOfStep, hs, State.addEdge]
      | cons e es =>
        have hhead : s.west e = s.east s.active := by
          have hc := (CutConverse.frontier_history w n).1
          change s.UR.map s.west =
            (CutConverse.pendingVertices s).dropLast at hc
          rw [hs] at hc
          have hh := congrArg List.head? hc
          simpa [CutConverse.pendingVertices, hs] using hh
        have hInit : activeInitial w (n + 1) = s.east s.active := by
          rw [CutConverse.activeInitial_eq]
          change t.west t.active = s.east s.active
          have ht : t = kmswStepOfStep s .down := by
            change kmswStep s (w n) = _
            rw [h2]
            rfl
          rw [ht]
          simp [kmswStepOfStep, hs, hhead]
        have hpending : CutConverse.pendingVertices t =
            s.east e :: es.map s.east := by
          have ht : t = kmswStepOfStep s .down := by
            change kmswStep s (w n) = _
            rw [h2]
            rfl
          rw [ht]
          simp [CutConverse.pendingVertices, kmswStepOfStep, hs]
        have hv' : v = s.east s.active ∨ v = s.east e ∨ v ∈ es.map s.east := by
          change v ∈ s.east s.active :: s.UR.map s.east at hv
          rw [hs, List.map_cons] at hv
          simpa only [List.mem_cons] using hv
        rcases hv' with hv' | hv' | hv'
        · right
          rw [hInit, hv']
        · left
          rw [hpending]
          simp [hv']
        · left
          rw [hpending]
          simp [hv']

private theorem allocated_vertex_initial_or_pending (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    (∃ m ≤ n, activeInitial w m = v) ∨
      v ∈ CutConverse.pendingVertices (kmswStage w n) := by
  induction n with
  | zero =>
    change v < 2 at hv
    have hv' : v = 0 ∨ v = 1 := by omega
    rcases hv' with rfl | rfl
    · left
      refine ⟨0, le_rfl, ?_⟩
      simp [activeInitial, edgeWest, act, kmswStage, kmswInit]
    · right
      simp [CutConverse.pendingVertices, kmswStage, kmswInit]
  | succ n ih =>
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    change v < t.nextVertex at hv
    by_cases hold : v < s.nextVertex
    · rcases ih hold with ⟨m, hm, hinit⟩ | hpending
      · left
        exact ⟨m, by omega, hinit⟩
      · rcases pending_vertex_step w n v hpending with hpending' | hinit
        · exact Or.inr hpending'
        · exact Or.inl ⟨n + 1, le_rfl, hinit⟩
    · by_cases h0 : w n = 0
      · cases hs : s.UL.dropLast.reverse with
        | nil =>
          have hnext : t.nextVertex = s.nextVertex + 1 := by
            simp [s, t, kmswStage, kmswStep, kmswCodeStep, h0,
              kmswStepOfStep, hs, State.addEdge]
          have hvnew : v = s.nextVertex := by omega
          left
          refine ⟨n + 1, le_rfl, ?_⟩
          rw [CutConverse.activeInitial_eq]
          change t.west t.active = v
          rw [hvnew]
          simp [s, t, kmswStage, kmswStep, kmswCodeStep, h0,
            kmswStepOfStep, hs, State.addEdge]
        | cons e es =>
          have hnext : t.nextVertex = s.nextVertex := by
            simp [s, t, kmswStage, kmswStep, kmswCodeStep, h0,
              kmswStepOfStep, hs, State.addEdge]
          omega
      · by_cases h1 : w n = 1
        · have hnext : t.nextVertex = s.nextVertex + 1 := by
            simp [s, t, kmswStage, kmswStep, kmswCodeStep, h1,
              kmswStepOfStep, State.addEdge]
          have hvnew : v = s.nextVertex := by omega
          right
          have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
            change (kmswStep s (w n)).UR = _
            simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep]
          have hEast : t.east t.active = s.nextVertex := by
            change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
            simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
          have hNewEast : t.east (s.nextEdge + 1) = s.east s.active := by
            change (kmswStep s (w n)).east (s.nextEdge + 1) = _
            simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
          have hmap : s.UR.map t.east = s.UR.map s.east := by
            apply List.map_congr_left
            intro e he
            have he' := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
              simp only [List.mem_append]
              tauto)
            exact (kmswStage_endpoints_stable w (Nat.le_succ n) he').2
          have hpending : CutConverse.pendingVertices t =
              s.nextVertex :: CutConverse.pendingVertices s := by
            simp only [CutConverse.pendingVertices, hUR, List.map_cons,
              hEast, hNewEast, hmap]
          rw [hpending, hvnew]
          simp
        · have h2 : w n = 2 := by
            apply Fin.ext
            have hv' := (w n).isLt
            have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
            have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
            omega
          cases hs : s.UR with
          | nil =>
            have hnext : t.nextVertex = s.nextVertex + 1 := by
              simp [s, t, kmswStage, kmswStep, kmswCodeStep, h2,
                kmswStepOfStep, hs, State.addEdge]
            have hvnew : v = s.nextVertex := by omega
            right
            change v ∈ CutConverse.pendingVertices t
            rw [CutConverse.pendingVertices]
            simp [s, t, kmswStage, kmswStep, kmswCodeStep, h2,
              kmswStepOfStep, hs, hvnew, State.addEdge]
          | cons e es =>
            have hnext : t.nextVertex = s.nextVertex := by
              simp [s, t, kmswStage, kmswStep, kmswCodeStep, h2,
                kmswStepOfStep, hs]
            omega

private theorem pending_vertex_persists_until_visited (w : ℕ → Fin 3)
    {n m v : ℕ} (hnm : n ≤ m)
    (hv : v ∈ CutConverse.pendingVertices (kmswStage w n)) :
    (∃ k, n < k ∧ k ≤ m ∧ activeInitial w k = v) ∨
      v ∈ CutConverse.pendingVertices (kmswStage w m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact Or.inr hv
  | succ m hnm ih =>
    rcases ih with ⟨k, hnk, hkm, hinit⟩ | hpending
    · exact Or.inl ⟨k, hnk, by omega, hinit⟩
    · rcases pending_vertex_step w m v hpending with hpending' | hinit
      · exact Or.inr hpending'
      · exact Or.inl ⟨m + 1, by omega, le_rfl, hinit⟩

private theorem activeInitial_next_of_empty_UR (w : ℕ → Fin 3) (n : ℕ)
    (hdown : w n = 2) (hUR : (kmswStage w n).UR = []) :
    activeInitial w (n + 1) = (kmswStage w n).east (act w n) := by
  rw [CutConverse.activeInitial_eq]
  simp [kmswStage, kmswStep, kmswCodeStep, hdown, kmswStepOfStep,
    hUR, act, State.addEdge]

/-- Under an unbounded downward vertical coordinate, every allocated vertex
eventually becomes the initial endpoint of a present active edge -/
theorem allocated_vertex_eventually_activeInitial_of_R_unbounded
    (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (x : ℕ)
    (hx : ∃ n, x < (kmswStage w n).nextVertex) :
    ∃ m, activeInitial w m = x := by
  obtain ⟨N, hN⟩ := hx
  rcases allocated_vertex_initial_or_pending w N x hN with hinit | hpending
  · rcases hinit with ⟨m, hm, hinit⟩
    exact ⟨m, hinit⟩
  · obtain ⟨q, hqmem, hqgt⟩ := (right_record_infinite w hR).exists_gt (N + 1)
    have hA : ∀ j < q, R w q ≤ R w j - 1 := by
      intro j hj
      have hlt := hqmem j hj
      omega
    have hqpos : 0 < q := by omega
    let k := q - 1
    have hqk : q = k + 1 := by dsimp [k]; omega
    have hkN : N ≤ k := by dsimp [k]; omega
    obtain ⟨hdown, hUR⟩ := record_stage_before_empty_UR w q hA hqpos
    rcases pending_vertex_persists_until_visited w hkN hpending with
      ⟨j, hNj, hjk, hvisited⟩ | hpendingK
    · exact ⟨j, hvisited⟩
    · have hpendingSingleton : CutConverse.pendingVertices (kmswStage w k) =
        [(kmswStage w k).east (act w k)] := by
        simp [k, CutConverse.pendingVertices, hUR, act]
      have hxval : x = (kmswStage w k).east (act w k) := by
        rw [hpendingSingleton] at hpendingK
        simpa using hpendingK
      have hnew : activeInitial w (k + 1) =
          (kmswStage w k).east (act w k) :=
        activeInitial_next_of_empty_UR w k (by simpa [k] using hdown)
          (by simpa [k] using hUR)
      refine ⟨q, ?_⟩
      rw [hqk, hnew]
      exact hxval.symm

private theorem allocated_vertex_has_outgoing_present_edge_of_R_unbounded
    (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (x : ℕ)
    (hx : ∃ n, x < (kmswStage w n).nextVertex) :
    ∃ e, edgeWest w e = x ∧ EdgePresent w e := by
  obtain ⟨m, hm⟩ := allocated_vertex_eventually_activeInitial_of_R_unbounded w hR x hx
  refine ⟨act w m, hm, ?_⟩
  obtain ⟨es, hes⟩ := kmswStage_UL_last w m
  have hmem : act w m ∈ (kmswStage w m).UL := by
    rw [hes]
    change (kmswStage w m).active ∈ es ++ [(kmswStage w m).active]
    simp
  refine ⟨m, act_lt_nextEdge w (le_refl m), ?_⟩
  exact (kmswStage_status w m).2.1 _ hmem

private abbrev AllocatedVertex (w : ℕ → Fin 3) :=
  {v : ℕ // ∃ n, v < (kmswStage w n).nextVertex}

private noncomputable def selectOutgoingEdge (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : AllocatedVertex w) : ℕ :=
  Classical.choose
    (allocated_vertex_has_outgoing_present_edge_of_R_unbounded w hR v.val v.property)

private theorem selectOutgoingEdge_spec (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : AllocatedVertex w) :
    edgeWest w (selectOutgoingEdge w hR v) = v.val ∧
      EdgePresent w (selectOutgoingEdge w hR v) :=
  Classical.choose_spec
    (allocated_vertex_has_outgoing_present_edge_of_R_unbounded w hR v.val v.property)

private noncomputable def nextAllocatedVertex (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : AllocatedVertex w) :
    AllocatedVertex w := by
  let e := selectOutgoingEdge w hR v
  refine ⟨edgeEast w e, ?_⟩
  obtain ⟨_, ⟨n, he, hp⟩⟩ := selectOutgoingEdge_spec w hR v
  have hb := CutConverse.endpoint_bound w n e he
  rw [(edge_endpoints_eq w he).2] at hb
  exact ⟨n, hb.2⟩

private noncomputable def allocatedVertexSeq (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (x : AllocatedVertex w) :
    ℕ → AllocatedVertex w
  | 0 => x
  | i + 1 => nextAllocatedVertex w hR (allocatedVertexSeq w hR x i)

private noncomputable def selectedEdgeSeq (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (x : AllocatedVertex w) (i : ℕ) : ℕ :=
  selectOutgoingEdge w hR (allocatedVertexSeq w hR x i)

private def presentArrow (w : ℕ → Fin 3) (e : ℕ) (he : EdgePresent w e) :
    (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨edgeEast w e⟩ :=
  ⟨e, he, rfl, rfl⟩

private theorem presentVertex_id_eq (w : ℕ → Fin 3) {u v : ℕ} (h : u = v) :
    (⟨u⟩ : PresentVertex w) = ⟨v⟩ := congrArg (fun z => (⟨z⟩ : PresentVertex w)) h

private theorem path_cast_length {V : Type} [Quiver V] {a b c : V}
    (h : b = c) (p : Path a b) : (h ▸ p).length = p.length := by
  cases h
  rfl

private def pathCast {V : Type} [Quiver V] {a b c d : V}
    (hs : a = c) (ht : b = d) (p : Path a b) : Path c d :=
  Eq.ndrec (motive := fun c' => Path c' d)
    (Eq.ndrec (motive := fun d' => Path a d') p ht) hs

private theorem pathCast_length {V : Type} [Quiver V]
    {a b c d : V} (hs : a = c) (ht : b = d) (p : Path a b) :
    (pathCast hs ht p).length = p.length := by
  cases hs
  cases ht
  rfl

private def presentEdgeSeqPath (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (i : ℕ) : (k : ℕ) →
      Path (⟨edgeWest w (e i)⟩ : PresentVertex w) ⟨edgeEast w (e (i + k))⟩
  | 0 => (presentArrow w (e i) (hp i)).toPath
  | k + 1 => by
      simpa only [Nat.add_succ] using
        (presentVertex_id_eq w (hpath (i + k)) ▸
          presentEdgeSeqPath w e hp hpath i k).cons
          (presentArrow w (e (i + k + 1)) (hp (i + k + 1)))

private theorem presentEdgeSeqPath_length (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (i k : ℕ) : (presentEdgeSeqPath w e hp hpath i k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((presentVertex_id_eq w (hpath (i + k)) ▸
          presentEdgeSeqPath w e hp hpath i k).cons
          (presentArrow w (e (i + k + 1)) (hp (i + k + 1)))).length = (k + 1) + 1
      rw [Path.length_cons, path_cast_length, ih]

private theorem presentEdgeSeq_injective (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) :
    Function.Injective e := by
  intro i j
  have hnoRepeat {a b : ℕ} (hab : a < b) (heq : e a = e b) : False := by
    let k := b - (a + 1)
    have hidx : a + 1 + k = b := by dsimp [k]; omega
    let p := presentEdgeSeqPath w e hp hpath (a + 1) k
    have hfirst : edgeEast w (e a) = edgeWest w (e (a + 1)) := hpath a
    have hlast : edgeEast w (e b) = edgeEast w (e a) :=
      (congrArg (edgeEast w) heq).symm
    have hidxE : edgeEast w (e (a + 1 + k)) = edgeEast w (e b) :=
      congrArg (fun r => edgeEast w (e r)) hidx
    have hidxV := presentVertex_id_eq w hidxE
    have hfirstV := presentVertex_id_eq w hfirst
    have hlastV := presentVertex_id_eq w hlast
    let cycle : Path (⟨edgeEast w (e a)⟩ : PresentVertex w) ⟨edgeEast w (e a)⟩ :=
      pathCast hfirstV.symm (hidxV.trans hlastV) p
    have hlenP : p.length = k + 1 := by
      simpa [p] using presentEdgeSeqPath_length w e hp hpath (a + 1) k
    have hcycleLen : cycle.length = p.length := by
      simpa [cycle] using pathCast_length hfirstV.symm
        (hidxV.trans hlastV) p
    have hpos : 0 < cycle.length := by
      rw [hcycleLen, hlenP]
      omega
    have hzero := presentVertex_acyclic w _ cycle
    omega
  intro hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact False.elim (hnoRepeat hlt hij)
  · exact heq
  · exact False.elim (hnoRepeat hgt hij.symm)

/-- With the unbounded-below vertical coordinate, every allocated vertex starts
an injective infinite sequence of present directed edges. -/
theorem allocated_vertex_has_infinite_path_of_R_unbounded
    (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (x : ℕ)
    (hx : ∃ n, x < (kmswStage w n).nextVertex) :
    ∃ e : ℕ → ℕ,
      Function.Injective e ∧
      (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) ∧
      edgeWest w (e 0) = x ∧
      (∀ i, ∃ n, e i < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (e i) = true) := by
  classical
  let x' : AllocatedVertex w := ⟨x, hx⟩
  let e := selectedEdgeSeq w hR x'
  have hwest (i : ℕ) : edgeWest w (e i) = (allocatedVertexSeq w hR x' i).val :=
    selectOutgoingEdge_spec w hR (allocatedVertexSeq w hR x' i) |>.1
  have hpres (i : ℕ) : EdgePresent w (e i) :=
    selectOutgoingEdge_spec w hR (allocatedVertexSeq w hR x' i) |>.2
  have hstep (i : ℕ) : (allocatedVertexSeq w hR x' (i + 1)).val = edgeEast w (e i) := by
    rfl
  have hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)) := by
    intro i
    rw [← hstep i, hwest (i + 1)]
  refine ⟨e, presentEdgeSeq_injective w e hpres hpath, hpath, ?_, ?_⟩
  · simpa [e, selectedEdgeSeq, allocatedVertexSeq] using hwest 0
  · intro i
    obtain ⟨n, hn, hp⟩ := hpres i
    exact ⟨n, hn, hp⟩


/-- Every injective directed edge sequence starting in the finite old side of a
record vertex, or at the record vertex itself, visits that record vertex,
provided the map is locally finite (`def-cut-vertex`, -/
theorem kmswInfinitePath_from_record_start_meets_recordVertex
    (w : ℕ → Fin 3) (n x : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (hstart : x ∈
      ({u | u < (kmswStage w n).nextVertex ∧
        u ≠ (kmswStage w n).west (act w n) ∧
        u ≠ (kmswStage w n).east (act w n)} ∪
        {(kmswStage w n).west (act w n)}) )
    (e : ℕ → ℕ)
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (hstartEdge : edgeWest w (e 0) = x)
    (hinj : Function.Injective e)
    (hInc : ∀ v : ℕ, {f : ℕ | ∃ m, f < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west f = v ∨ (kmswStage w m).east f = v)}.Finite) :
    ∃ i, edgeWest w (e i) = (kmswStage w n).west (act w n) ∨
      edgeEast w (e i) = (kmswStage w n).west (act w n) := by
  let v := (kmswStage w n).west (act w n)
  let a := (kmswStage w n).east (act w n)
  let Before : Set ℕ := {u | u < (kmswStage w n).nextVertex ∧ u ≠ v ∧ u ≠ a}
  have hstart' : edgeWest w (e 0) ∈ Before ∨ edgeWest w (e 0) = v := by
    change x ∈ Before ∪ {v} at hstart
    rcases hstart with hb | hv
    · left
      rw [hstartEdge]
      exact hb
    · right
      rw [hstartEdge]
      exact hv
  obtain ⟨i, hlarge⟩ :=
    kmsw_distinct_edge_sequence_vertices_unbounded w hInc e hinj a
  let es : List ℕ := (List.range (i + 1)).map e
  have hne : es ≠ [] := by simp [es]
  have hchain : List.IsChain (fun f g => edgeEast w f = edgeWest w g) es := by
    change List.IsChain (fun f g => edgeEast w f = edgeWest w g)
      ((List.range (i + 1)).map e)
    rw [List.isChain_map, List.isChain_range_succ]
    intro j hj
    exact hpath j
  have hhead : edgeWest w (es.head hne) ∈ Before ∨
      edgeWest w (es.head hne) = v := by
    simpa [es, hstartEdge] using hstart'
  have hafter : ∃ f ∈ es,
      a ≤ edgeWest w f ∨ a ≤ edgeEast w f := by
    refine ⟨e i, ?_, ?_⟩
    · change e i ∈ (List.range (i + 1)).map e
      apply List.mem_map.mpr
      exact ⟨i, List.mem_range.mpr (by omega), rfl⟩
    · simpa [a] using hlarge
  obtain ⟨f, hfmem, hincident⟩ :=
    kmswFinitePath_meets_recordVertex w n hA hB es hne hchain hhead hafter
  obtain ⟨j, hjrange, hjeq⟩ := List.mem_map.mp hfmem
  refine ⟨j, ?_⟩
  have hjendpoint := hincident
  rw [← hjeq] at hjendpoint
  exact hjendpoint

/-- For the Pitman code, every allocated start admits an infinite injective path of present
directed edges, and infinitely many vertices are met by every such path -/
theorem pitmanCodes_ae_path_and_unavoidable_recordVertices_any_allocated :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ x, (∃ N, x < (kmswStage w N).nextVertex) →
        (∃ e : ℕ → ℕ,
          Function.Injective e ∧
          (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) ∧
          edgeWest w (e 0) = x ∧
          (∀ i, ∃ n, e i < (kmswStage w n).nextEdge ∧
            (kmswStage w n).present (e i) = true)) ∧
        {v : ℕ | ∀ e : ℕ → ℕ,
          (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) →
          edgeWest w (e 0) = x → Function.Injective e →
          (∀ i, ∃ n, e i < (kmswStage w n).nextEdge ∧
            (kmswStage w n).present (e i) = true) →
          ∃ i, edgeWest w (e i) = v ∨ edgeEast w (e i) = v}.Infinite := by
  have hRae := RandomWalk.pitmanCodes_ae_R_unbounded_below
  have hrecordsAE := pitmanCodes_ae_infinite_cutSeparation_records
  have hincidentAE := pitmanCodes_ae_finite_incident_edges
  filter_upwards [hRae, hrecordsAE, hincidentAE] with ω hRae hrecordsAE hincidentAE
  dsimp only
  let w : ℕ → Fin 3 := pitmanCode (fun i => ω (i + 1))
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hRae a
    exact ⟨n, by rw [RandomWalk.kmsw_R_eq]; exact hn⟩
  have hrecords :
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite := by
    simpa [w] using hrecordsAE
  have hinc : ∀ v : ℕ, {f : ℕ | ∃ m,
      f < (kmswStage w m).nextEdge ∧
        ((kmswStage w m).west f = v ∨ (kmswStage w m).east f = v)}.Finite := by
    intro v
    simpa [w] using hincidentAE v
  intro x halloc
  obtain ⟨N, hN⟩ := halloc
  obtain ⟨m, hm⟩ :=
    allocated_vertex_eventually_activeInitial_of_R_unbounded w hR x ⟨N, hN⟩
  let G : Set ℕ := {n | (∀ j < n, R w n ≤ R w j - 1) ∧
    (∀ j, n ≤ j → L w n ≤ L w j) ∧ max N m < n}
  have hG : G.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro q
    obtain ⟨n, hn, hnq⟩ :=
      (Set.infinite_iff_exists_gt.mp hrecords) (max (max N m) q)
    refine ⟨n, ?_, ?_⟩
    · have hnrec : (∀ j < n, R w n ≤ R w j - 1) ∧
          ∀ j, n ≤ j → L w n ≤ L w j := by
        simpa only [Set.mem_setOf_eq] using hn
      exact ⟨hnrec.1, hnrec.2, by omega⟩
    · omega
  have hfirst : ∀ n ∈ G, ∀ j < n, activeInitial w j ≠ activeInitial w n := by
    intro n hn j hj
    change (∀ j < n, R w n ≤ R w j - 1) ∧
      (∀ j, n ≤ j → L w n ≤ L w j) ∧ max N m < n at hn
    exact activeInitial_ne_of_right_record w n hn.1 j hj
  have hinj : Set.InjOn (activeInitial w) G := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim ((hfirst b hb a hlt) hab)
    · exact heq
    · exact False.elim ((hfirst a ha b hgt) hab.symm)
  have himage : (activeInitial w '' G).Infinite := hG.image hinj
  have hsub : activeInitial w '' G ⊆
      {v : ℕ | ∀ e : ℕ → ℕ,
        (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) →
        edgeWest w (e 0) = x → Function.Injective e →
        (∀ i, ∃ n, e i < (kmswStage w n).nextEdge ∧
          (kmswStage w n).present (e i) = true) →
        ∃ i, edgeWest w (e i) = v ∨ edgeEast w (e i) = v} := by
    rintro v ⟨n, hn, rfl⟩ e hpath hstart heinj hpresent
    change (∀ j < n, R w n ≤ R w j - 1) ∧
      (∀ j, n ≤ j → L w n ≤ L w j) ∧ max N m < n at hn
    have hmN : m < n := by omega
    have hxneActive : x ≠ activeInitial w n := by
      rw [← hm]
      exact activeInitial_ne_of_right_record w n hn.1 m hmN
    have hneWest : x ≠ (kmswStage w n).west (act w n) := by
      rw [← CutConverse.activeInitial_eq]
      exact hxneActive
    have hneEast : x ≠ (kmswStage w n).east (act w n) := by
      intro heast
      have hnot := activeEast_ne_activeInitial w
        (j := m) (n := n) (Nat.le_of_lt hmN)
      apply hnot
      rw [hm]
      exact heast.symm
    have hstart' : x ∈
        ({u | u < (kmswStage w n).nextVertex ∧
          u ≠ (kmswStage w n).west (act w n) ∧
          u ≠ (kmswStage w n).east (act w n)} ∪
          {(kmswStage w n).west (act w n)}) := by
      apply Or.inl
      refine ⟨?_, hneWest, hneEast⟩
      exact lt_of_lt_of_le hN (CutConverse.nextVertex_mono w (Nat.le_of_lt (by omega)))
    obtain ⟨i, hmeet⟩ := kmswInfinitePath_from_record_start_meets_recordVertex
      w n x hn.1 hn.2.1 hstart' e hpath hstart heinj hinc
    rw [← CutConverse.activeInitial_eq] at hmeet
    exact ⟨i, hmeet⟩
  have hpaths := allocated_vertex_has_infinite_path_of_R_unbounded w hR x ⟨N, hN⟩
  refine ⟨hpaths, ?_⟩
  exact himage.mono hsub

end DirectedDistances.KMSW

