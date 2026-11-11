module

public import DirectedDistances.KMSW.BusemannFromCut
public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.CutSeparationAnyStart
import DirectedDistances.KMSW.StageIncidenceChains

/-! # Common reachable futures from downward records

Finite-stage consequences of strict records for the common-sequence input to -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory
open scoped Classical

/-- At a strict downward-coordinate record, the preceding code is down and the -/
theorem record_stage_before_empty_UR_public (w : ℕ → Fin 3) (q : ℕ)
    (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q) :
    w (q - 1) = 2 ∧ (kmswStage w (q - 1)).UR = [] := by
  let k := q - 1
  have hqk : q = k + 1 := by dsimp [k]; omega
  have hRstep : R w (k + 1) = R w k +
      (RandomWalk.lazyTwoDimensionalStep (w k)).2 := Finset.sum_range_succ _ _
  have hdown : w k = 2 := by
    have hstrict := hA k (by omega)
    rw [hqk, hRstep] at hstrict
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
      rw [hqk, hRdown] at hi
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

/-- With empty `UR` on a down step, the next active initial vertex is the old -/
theorem activeInitial_next_of_empty_UR_public (w : ℕ → Fin 3) (n : ℕ)
    (hdown : w n = 2) (hUR : (kmswStage w n).UR = []) :
    activeInitial w (n + 1) = (kmswStage w n).east (act w n) := by
  rw [CutConverse.activeInitial_eq]
  simp [kmswStage, kmswStep, kmswCodeStep, hdown, kmswStepOfStep,
    hUR, act, State.addEdge]

private theorem pending_vertex_step_public (w : ℕ → Fin 3) (n v : ℕ)
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

/-- Every vertex allocated by stage `n` has already appeared as an active -/
theorem allocated_vertex_initial_or_pending_public (w : ℕ → Fin 3) (n v : ℕ)
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
      · rcases pending_vertex_step_public w n v hpending with hpending' | hinit
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

private theorem active_edge_present_at_later_stage (w : ℕ → Fin 3)
    {m n : ℕ} (hmn : m ≤ n) :
    (kmswStage w n).present (act w m) = true := by
  have he := act_lt_nextEdge w (le_refl m)
  obtain ⟨es, hes⟩ := kmswStage_UL_last w m
  have hmem : act w m ∈ (kmswStage w m).UL := by
    rw [hes]
    change (kmswStage w m).active ∈ es ++ [(kmswStage w m).active]
    simp
  have hp := (kmswStage_status w m).2.1 _ hmem
  exact (present_mono w he hp n hmn).2

/-- record stage has a present outgoing arrow there (`def-kmsw`, -/
theorem allocated_stage_vertex_has_outgoing_of_strict_record
    (w : ℕ → Fin 3) (q : ℕ)
    (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q)
    (v : ℕ) (hv : v < (kmswStage w (q - 1)).nextVertex)
    (hne : v ≠ (kmswStage w (q - 1)).east (act w (q - 1))) :
    ∃ z : StagePresentVertex w (q - 1),
      Nonempty ((⟨v⟩ : StagePresentVertex w (q - 1)) ⟶ z) := by
  let t := q - 1
  obtain ⟨hdown, hUR⟩ := record_stage_before_empty_UR_public w q hA hq
  have hclass := allocated_vertex_initial_or_pending_public w t v hv
  have hinit : ∃ m ≤ t, activeInitial w m = v := by
    rcases hclass with hinit | hpending
    · exact hinit
    · have hUR' : (kmswStage w t).UR = [] := by simpa [t] using hUR
      have hpending' : v ∈ [((kmswStage w t).east (act w t))] := by
        simpa [CutConverse.pendingVertices, hUR', act] using hpending
      have hvEq : v = (kmswStage w t).east (act w t) :=
        List.mem_singleton.mp hpending'
      exact False.elim (hne (by simpa [t] using hvEq))
  obtain ⟨m, hmt, hmv⟩ := hinit
  have hmt' : m ≤ q - 1 := hmt
  have he : act w m < (kmswStage w t).nextEdge := by
    exact act_lt_nextEdge w hmt'
  have hp : (kmswStage w t).present (act w m) = true := by
    exact active_edge_present_at_later_stage w hmt'
  have hmEdge : act w m < (kmswStage w m).nextEdge :=
    act_lt_nextEdge w (le_refl m)
  have hends := kmswStage_endpoints_stable w hmt' hmEdge
  have hwest : (kmswStage w t).west (act w m) = v := by
    rw [hends.1]
    exact (CutConverse.activeInitial_eq w m).symm.trans hmv
  refine ⟨⟨(kmswStage w t).east (act w m)⟩, ?_⟩
  exact ⟨⟨act w m, he, hp, hwest, rfl⟩⟩

private theorem stage_path_endpoint_allocated (w : ℕ → Fin 3) (n : ℕ)
    {a b : StagePresentVertex w n} (ha : a.id < (kmswStage w n).nextVertex)
    (p : Path a b) : b.id < (kmswStage w n).nextVertex := by
  cases p with
  | nil => exact ha
  | cons p e =>
    have hb := (CutConverse.endpoint_bound w n e.val e.property.1).2
    rw [e.property.2.2.2] at hb
    exact hb

private theorem allocated_stage_vertices_finite (w : ℕ → Fin 3) (n : ℕ) :
    {v : StagePresentVertex w n | v.id < (kmswStage w n).nextVertex}.Finite := by
  classical
  apply Set.Finite.subset (Set.finite_range
    (fun i : Fin (kmswStage w n).nextVertex =>
      (⟨i.val⟩ : StagePresentVertex w n)))
  intro v hv
  refine ⟨⟨v.id, hv⟩, ?_⟩
  cases v
  rfl

/-- At a strict record time, every allocated vertex reaches the active east
endpoint of the preceding empty-`UR` stage through present arrows -/
theorem allocated_stage_vertex_reaches_record_of_strict_record
    (w : ℕ → Fin 3) (q : ℕ)
    (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q)
    (v : ℕ) (hv : v < (kmswStage w (q - 1)).nextVertex) :
    Reachable (⟨v⟩ : StagePresentVertex w (q - 1))
      ⟨(kmswStage w (q - 1)).east (act w (q - 1))⟩ := by
  classical
  let t := q - 1
  let a : StagePresentVertex w t := ⟨v⟩
  let z : StagePresentVertex w t := ⟨(kmswStage w t).east (act w t)⟩
  let S : Set (StagePresentVertex w t) := {b | Reachable a b}
  have ha : a.id < (kmswStage w t).nextVertex := by simpa [a, t] using hv
  have hSFinite : S.Finite := by
    apply (allocated_stage_vertices_finite w t).subset
    intro b hb
    have hr : Reachable a b := by simpa [S] using hb
    obtain ⟨p⟩ := hr
    exact stage_path_endpoint_allocated w t ha p
  have hSNonempty : S.Nonempty := by
    refine ⟨a, ?_⟩
    exact ⟨Path.nil⟩
  obtain ⟨b, hbS, hmax⟩ :=
    Set.Finite.exists_maximalFor (fun x : StagePresentVertex w t =>
      kmswStageRank w t x.id) S hSFinite hSNonempty
  have hbeq : b = z := by
    by_contra hne
    have hrb : Reachable a b := by simpa [S] using hbS
    obtain ⟨pb⟩ := hrb
    have hbBound := stage_path_endpoint_allocated w t ha pb
    have hneId : b.id ≠ (kmswStage w t).east (act w t) := by
      intro heq
      apply hne
      cases b
      cases z
      simp_all [z, t]
    obtain ⟨c, hcArrow⟩ :=
      allocated_stage_vertex_has_outgoing_of_strict_record w q hA hq b.id
        (by simpa [t] using hbBound) (by simpa [t] using hneId)
    obtain ⟨e⟩ := hcArrow
    have hsource : (⟨b.id⟩ : StagePresentVertex w t) = b := by cases b; rfl
    rw [hsource] at e
    have hcS : c ∈ S := by
      change Reachable a c
      exact ⟨pb.cons e⟩
    have hrank := kmswStageRank_strict w t e.val e.property.1
    rw [e.property.2.2.1, e.property.2.2.2] at hrank
    have hback := hmax hcS hrank.le
    exact (not_lt_of_ge hback) hrank
  have hbS' : Reachable a z := by
    change Reachable a b at hbS
    simpa [hbeq] using hbS
  simpa [a, z, t] using hbS'

/-- An allocated vertex reaches the record vertex in the limit present quiver,
using only the strict vertical record (`def-infinite-geo`, -/
theorem allocated_vertex_reaches_strict_record
    (w : ℕ → Fin 3) (q : ℕ)
    (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q)
    (v : ℕ) (hv : v < (kmswStage w (q - 1)).nextVertex) :
    Reachable (⟨v⟩ : PresentVertex w) (recordVertex w q) := by
  let t := q - 1
  have hdownUR := record_stage_before_empty_UR_public w q hA hq
  have hnext : activeInitial w q = (kmswStage w t).east (act w t) := by
    have htq : t + 1 = q := by dsimp [t]; omega
    rw [← htq]
    exact activeInitial_next_of_empty_UR_public w t
      (by simpa [t] using hdownUR.1) (by simpa [t] using hdownUR.2)
  have hrecordId : (recordVertex w q).id = (kmswStage w t).east (act w t) := by
    change (kmswStage w q).west (act w q) = _
    rw [← CutConverse.activeInitial_eq w q]
    exact hnext
  have hrecord : recordVertex w q =
      (⟨(kmswStage w t).east (act w t)⟩ : PresentVertex w) := by
    exact congrArg (fun id : ℕ => (⟨id⟩ : PresentVertex w)) hrecordId
  have hstage := allocated_stage_vertex_reaches_record_of_strict_record
    w q hA hq v hv
  have hlimit := stageToLimit_reachable w t hstage
  simpa [hrecord] using hlimit

private noncomputable def rightRecordAfter (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (N : ℕ) : ℕ :=
  Classical.choose ((right_record_infinite w hR).exists_gt N)

private theorem rightRecordAfter_spec (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (N : ℕ) :
    (∀ j < rightRecordAfter w hR N, R w (rightRecordAfter w hR N) < R w j) ∧
      N < rightRecordAfter w hR N := by
  simpa only [rightRecordAfter, Set.mem_ofPred_eq] using
    (Classical.choose_spec ((right_record_infinite w hR).exists_gt N))

private noncomputable def rightRecordSequence (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (N : ℕ) : ℕ → ℕ
  | 0 => rightRecordAfter w hR N
  | i + 1 => rightRecordAfter w hR (rightRecordSequence w hR N i)

private theorem rightRecordSequence_record (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (N i : ℕ) :
    ∀ j < rightRecordSequence w hR N i,
      R w (rightRecordSequence w hR N i) < R w j := by
  cases i with
  | zero => simpa [rightRecordSequence] using (rightRecordAfter_spec w hR N).1
  | succ i =>
    simpa [rightRecordSequence] using
      (rightRecordAfter_spec w hR (rightRecordSequence w hR N i)).1

private theorem rightRecordSequence_gt (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (N i : ℕ) :
    N < rightRecordSequence w hR N i := by
  induction i with
  | zero => simpa [rightRecordSequence] using (rightRecordAfter_spec w hR N).2
  | succ i ih =>
    have hstep := (rightRecordAfter_spec w hR
      (rightRecordSequence w hR N i)).2
    have hstep' : rightRecordSequence w hR N i <
        rightRecordSequence w hR N (i + 1) := by
      simpa [rightRecordSequence] using hstep
    exact ih.trans hstep'

private theorem rightRecordSequence_strictMono (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (N : ℕ) :
    StrictMono (rightRecordSequence w hR N) :=
  strictMono_nat_of_lt_succ (fun i => by
    have hstep := (rightRecordAfter_spec w hR
      (rightRecordSequence w hR N i)).2
    simpa [rightRecordSequence] using hstep)

/-- Any enumeration by allocated present vertices has an injective sequence
reachable from each pair, assuming only that `R` is unbounded below. This is -/
theorem allocatedEnumeration_commonSequence_of_R_unbounded
    (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (x : ℤ → PresentVertex w)
    (hx : ∀ k : ℤ, ∃ n, (x k).id < (kmswStage w n).nextVertex) :
    BusemannCommonSequenceHypothesis x := by
  intro k k'
  obtain ⟨nk, hnk⟩ := hx k
  obtain ⟨nk', hnk'⟩ := hx k'
  let N := max nk nk'
  let q := rightRecordSequence w hR N
  have hqmono : StrictMono q := by
    simpa [q] using rightRecordSequence_strictMono w hR N
  have hqmem (j : ℕ) : ∀ i < q j, R w (q j) < R w i := by
    simpa [q] using rightRecordSequence_record w hR N j
  have hqgt (j : ℕ) : N < q j := by
    simpa [q] using rightRecordSequence_gt w hR N j
  refine ⟨fun j => recordVertex w (q j), ?_, ?_⟩
  · intro i j hij
    rcases lt_trichotomy i j with hij' | heq | hji
    · have hne := recordVertex_ne w (hqmono hij') (by
        intro r hr
        have h := hqmem j r hr
        omega)
      exact (hne hij).elim
    · exact heq
    · have hne := recordVertex_ne w (hqmono hji) (by
        intro r hr
        have h := hqmem i r hr
        omega)
      exact (hne hij.symm).elim
  · intro j
    have hqpos : 0 < q j := by have := hqgt j; omega
    have hA : ∀ i < q j, R w (q j) ≤ R w i - 1 := by
      intro i hi
      have h := hqmem j i hi
      omega
    have hnkq : nk ≤ q j - 1 := by have := hqgt j; dsimp [N] at this; omega
    have hnk'q : nk' ≤ q j - 1 := by have := hqgt j; dsimp [N] at this; omega
    have halloc : (x k).id < (kmswStage w (q j - 1)).nextVertex :=
      hnk.trans_le (CutConverse.nextVertex_mono w hnkq)
    have halloc' : (x k').id < (kmswStage w (q j - 1)).nextVertex :=
      hnk'.trans_le (CutConverse.nextVertex_mono w hnk'q)
    have hreach := allocated_vertex_reaches_strict_record w (q j) hA hqpos
      (x k).id halloc
    have hreach' := allocated_vertex_reaches_strict_record w (q j) hA hqpos
      (x k').id halloc'
    have hxid : x k = (⟨(x k).id⟩ : PresentVertex w) := by cases x k; rfl
    have hxid' : x k' = (⟨(x k').id⟩ : PresentVertex w) := by cases x k'; rfl
    rw [← hxid] at hreach
    rw [← hxid'] at hreach'
    exact ⟨hreach, hreach'⟩

/-- Every hit-indexed boundary vertex is allocated at its hit stage; the two
root vertices are already present at stage zero (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryVertex_allocated (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    ∃ n, boundaryVertex w h k < (kmswStage w n).nextVertex := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨0, ?_⟩
    simp [boundaryVertex, kmswStage, kmswInit]
  · by_cases hk1 : k = 1
    · subst k
      refine ⟨0, ?_⟩
      simp [boundaryVertex, kmswStage, kmswInit]
    · let m := boundaryHitTime w h k
      have hm : activeInitial w m < (kmswStage w m).nextVertex := by
        rw [CutConverse.activeInitial_eq]
        exact (CutConverse.endpoint_bound w m (act w m)
          (act_lt_nextEdge w (le_refl m))).1
      refine ⟨m, ?_⟩
      simpa [boundaryVertex, m, hk0, hk1] using hm

/-- Right-coordinate hits at all negative integer levels imply `R` is unbounded -/
theorem R_unbounded_below_of_boundaryHitWitnesses (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  let k : ℤ := max 1 (-a)
  obtain ⟨n, hn⟩ := h.rightHit k (by dsimp [k]; omega)
  refine ⟨n, ?_⟩
  rw [hn]
  dsimp [k]
  omega

/-- The hit-indexed boundary enumeration satisfies the common-sequence input
to `thm-busemann` whenever all boundary coordinate hits exist -/
theorem boundaryEnumeration_commonSequence (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    BusemannCommonSequenceHypothesis
      (fun k : ℤ => (⟨boundaryVertex w h k⟩ : PresentVertex w)) := by
  apply allocatedEnumeration_commonSequence_of_R_unbounded w
    (R_unbounded_below_of_boundaryHitWitnesses w h)
  intro k
  exact boundaryVertex_allocated w h k

/-- Almost surely the iid hit-indexed boundary enumeration has an injective -/
theorem iidCodes_ae_boundaryCommonSequence :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        BusemannCommonSequenceHypothesis
          (fun k : ℤ => (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
            PresentVertex (fun i => ω (i + 1)))) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω hω
  intro h
  exact boundaryEnumeration_commonSequence (fun i => ω (i + 1)) h

end DirectedDistances.KMSW

