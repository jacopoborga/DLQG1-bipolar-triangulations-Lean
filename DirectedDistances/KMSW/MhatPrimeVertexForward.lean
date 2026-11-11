module

public import DirectedDistances.KMSW.MhatPrimeVertexCarrier
public import DirectedDistances.KMSW.MhatPrimeGeometricCarrier

import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.SDPIdentifyBdy
import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
import DirectedDistances.KMSW.PrimedSimCrossingInvariant

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
This isolates the reachable-endpoint boundary-incidence step -/
@[expose] def reachableEndpointCrossingWestBoundaryGoal
    (w : ℕ → Fin 3) : Prop :=
  ∀ e v, ¬ MhatGeometricEdge w e → MhatVertex w v →
    (edgeWest w e = v ∨ edgeEast w e = v) →
      ∃ f, MhatWestBoundaryEdge w f ∧
        (edgeWest w f = v ∨ edgeEast w f = v)

open Quiver

/- The private local triangle argument below follows Beta0BoundarySuccessor.
It is repeated here because that module keeps its corner lemmas private; the
new scan starts from any crossing incoming edge, rather than a known β₀ edge. -/

private theorem forward_dart_record_iff (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (e : ℕ) :
    e ∈ [(stageTriangleRecord w j).1, (stageTriangleRecord w j).2.1,
      (stageTriangleRecord w j).2.2] ↔
      ∃ d ∈ stageTriangleDartList w j, d.1 = e := by
  rcases j.property with h0 | h1
  · cases hl : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple, h0, hl]
      <;> tauto
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple, h0]
    tauto

private theorem forward_present_west_triangle (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (he : EdgePresent w e) :
    ∃ j : TriangleCreationTime w, (e, false) ∈ stageTriangleDartList w j := by
  classical
  obtain ⟨N, hN⟩ := he.eventually_present
  obtain ⟨m, hm, hem⟩ := stagePresent_exists_active w N e (hN N le_rfl).1 (hN N le_rfl).2
  have hmin0 : minL w N ≤ 0 := by
    have hzero := runningMin_le (L w) N 0 (Nat.zero_le _)
    simpa [minL, L] using hzero
  obtain ⟨n, hn⟩ := hb.leftHit (minL w N - 1) (by omega)
  have hNn : N < n := by
    by_contra hh
    have hl := runningMin_le (L w) N n (by omega)
    change minL w N ≤ L w n at hl
    omega
  have hnUL : e ∉ (kmswStage w n).UL := by
    intro hmem
    rw [kmswStage_UL_eq] at hmem
    obtain ⟨m', hm', heq⟩ := List.mem_map.mp hmem
    have hmm : m' = m := CutConverse.act_injective w (heq.trans hem)
    subst m'
    have hrec := of_decide_eq_true (List.mem_filter.mp hm').2
    have hval := hrec n (by omega) le_rfl
    have hminm := runningMin_le (L w) N m hm
    change minL w N ≤ L w m at hminm
    omega
  let d : StageDart (kmswStage w n).nextEdge := (⟨e, (hN n (by omega)).1⟩, false)
  rcases stage_dart_partition w n d with hout | ⟨j, hj, _⟩
  · have houter := (stageOuterWord_mem_iff w n d).mp hout
    simp only [d, Bool.false_eq_true, false_and, or_false, true_and] at houter
    rcases houter with hUL | hUR
    · exact (hnUL hUL).elim
    · have hfalse := ((kmswStage_status w n).1 e d.1.isLt).mpr (Or.inl hUR)
      rw [(hN n (by omega)).2] at hfalse
      cases hfalse
  · exact ⟨j, hj.2⟩

private theorem forward_triangle_of_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (e : ℕ)
    (he : (e, false) ∈ stageTriangleDartList w j) :
    ∃ n t, t ∈ (kmswStage w n).triangles ∧
      ∃ he : e < (kmswStage w n).nextEdge,
        kmswWestSideFaceIsTriangle w n ⟨e, he⟩ t ∧ t = stageTriangleRecord w j := by
  let n := j.val + 1
  have hj : j.val < n := Nat.lt_succ_self _
  have hbound := stageTriangleDartList_lt w n j hj (e, false) he
  have hbase :
      ((⟨e, hbound⟩ : Fin (kmswStage w n).nextEdge), false) =
          stageTriangleDart₁ w n j hj ∨
        ((⟨e, hbound⟩ : Fin (kmswStage w n).nextEdge), false) =
          stageTriangleDart₂ w n j hj ∨
        ((⟨e, hbound⟩ : Fin (kmswStage w n).nextEdge), false) =
          stageTriangleDart₃ w n j hj := by
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h
    · exact Or.inl (Prod.ext (Fin.ext (congrArg Prod.fst h))
        (show false = _ from congrArg (fun d : ℕ × Bool => d.2) h))
    · exact Or.inr (Or.inl
        (Prod.ext (Fin.ext (congrArg Prod.fst h))
          (show false = _ from congrArg (fun d : ℕ × Bool => d.2) h)))
    · exact Or.inr (Or.inr
        (Prod.ext (Fin.ext (congrArg Prod.fst h))
          (show false = _ from congrArg (fun d : ℕ × Bool => d.2) h)))
  refine ⟨n, stageTriangleRecord w j, ?_, hbound, ?_, rfl⟩
  · rw [← stageTriangleTimes_records]
    exact List.mem_map.mpr ⟨j, (mem_stageTriangleTimes w n j).mpr hj, rfl⟩
  · exact ⟨j, hj, rfl, hbase,
      kmswWestSideFaceOrbit_eq_triangleDarts w n j hj ⟨e, hbound⟩ hbase⟩

private theorem forward_missing_LL (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (e : ℕ) (hne : ¬ EdgePresent w e) :
    ∃ n, e ∈ (kmswStage w n).LL := by
  have halloc := kmsw_edge_allocated_by_self w e
  have hfalse : (kmswStage w e).present e = false := by
    cases hp : (kmswStage w e).present e with
    | false => rfl
    | true => exact (hne ⟨e, halloc, hp⟩).elim
  have hstatus := ((kmswStage_status w e).1 e halloc).mp hfalse
  rcases hstatus with hUR | hLL
  · obtain ⟨m, hem, hpresent⟩ :=
      kmswStage_UR_edge_eventually_present_of_R_unbounded w h.R_unbounded_below e e hUR
    have hallocm : e < (kmswStage w m).nextEdge :=
      halloc.trans_le (kmswStage_nextEdge_mono w hem)
    exact (hne ⟨m, hallocm, hpresent⟩).elim
  · exact ⟨e, hLL⟩

private theorem forward_missing_endpoints
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (e : ℕ)
    (hne : ¬ EdgePresent w e) :
    (∃ k : ℤ, k ≤ -1 ∧ edgeWest w e = boundaryVertex w h k) ∧
      (∃ k : ℤ, k ≤ 0 ∧ edgeEast w e = boundaryVertex w h k) := by
  obtain ⟨n, heLL⟩ := forward_missing_LL w h e hne
  rw [kmswStage_LL_eq] at heLL
  obtain ⟨m, hm, hem⟩ := List.mem_map.mp heLL
  have hm' := List.mem_reverse.mp hm
  have hrecord : 0 < m ∧ ∀ j < m, L w m < L w j :=
    of_decide_eq_true (List.mem_filter.mp hm').2
  let k := L w m
  have hk : k ≤ -1 := by
    have hzero : L w 0 = 0 := by simp [L]
    have hlt := hrecord.2 0 (by omega)
    dsimp [k] at hlt ⊢
    omega
  have hfind : Nat.find (h.leftHit k hk) = m := by
    apply le_antisymm
    · exact Nat.find_min' (h.leftHit k hk) (show L w m = k by rfl)
    · by_contra hlt
      have hvalue := Nat.find_spec (h.leftHit k hk)
      have hstrict := hrecord.2 (Nat.find (h.leftHit k hk)) (by omega)
      change L w (Nat.find (h.leftHit k hk)) = k at hvalue
      dsimp [k] at hstrict hvalue
      omega
  have htime : boundaryHitTime w h k = m := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
    exact hfind
  have heq : e = kmswLLCreatedEdge w m := by simpa using hem.symm
  have hleft := boundaryVertex_left_missing_edge w h hk
  rw [htime] at hleft
  change (kmswStage w m).west (kmswLLCreatedEdge w m) = boundaryVertex w h k ∧
    (kmswStage w m).east (kmswLLCreatedEdge w m) = boundaryVertex w h (k + 1) ∧
    (kmswStage w m).present (kmswLLCreatedEdge w m) = false at hleft
  have hnext : 1 ≤ (kmswStage w m).nextEdge := by
    have hm := kmswStage_nextEdge_mono w (m := 0) (n := m) (Nat.zero_le _)
    simpa [kmswStage, kmswInit] using hm
  have hallocm : kmswLLCreatedEdge w m < (kmswStage w m).nextEdge := by
    simp only [kmswLLCreatedEdge]
    omega
  have hend := edge_endpoints_eq w hallocm
  refine ⟨⟨k, hk, ?_⟩, ⟨k + 1, by omega, ?_⟩⟩
  · rw [heq]
    exact hend.1.symm.trans hleft.1
  · rw [heq]
    exact hend.2.symm.trans hleft.2.1

private theorem forward_incident_present
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (v : ℕ)
    (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v)
    (d : ℕ × Bool)
    (hdv : kmswDartEndpoint w d = v) : EdgePresent w d.1 := by
  by_contra hmissing
  obtain ⟨⟨k, hk, hwest⟩, ⟨l, hl,heast⟩⟩ :=
    forward_missing_endpoints w h d.1 hmissing
  have hnoWest := boundaryVertex_nonpos_no_incoming w h (k := k) (by omega)
  have hnoEast := boundaryVertex_nonpos_no_incoming w h (k := l) hl
  rcases hin with ⟨f, hf, hfv⟩
  by_cases htag : d.2
  · have hde : edgeEast w d.1 = v := by simpa [kmswDartEndpoint, htag] using hdv
    apply hnoEast f hf
    exact hfv.trans (hde.symm.trans heast)
  · have hdw : edgeWest w d.1 = v := by simpa [kmswDartEndpoint, htag] using hdv
    apply hnoWest f hf
    exact hfv.trans (hdw.symm.trans hwest)

private theorem forward_future_hit (f : ℕ → ℤ)
    (hs : ∀ n, f n - 1 ≤ f (n + 1))
    (hu : ∀ a : ℤ, ∃ n, f n ≤ a) (n : ℕ) :
    ∃ m, n + 1 ≤ m ∧ f m = f n - 1 := by
  classical
  obtain ⟨m, hm⟩ := hu (runningMin f n - 1)
  have hmn : n < m := by
    by_contra h
    have := runningMin_le f n m (by omega)
    omega
  have hmin := runningMin_le f n n le_rfl
  have hex : ∃ m, n + 1 ≤ m ∧ f m ≤ f n - 1 :=
    ⟨m, by omega, by omega⟩
  let t := Nat.find hex
  have ht : n + 1 ≤ t ∧ f t ≤ f n - 1 := Nat.find_spec hex
  have hp : f n - 1 < f (t - 1) := by
    by_cases he : t - 1 = n
    · rw [he]
      omega
    · have hnot := Nat.find_min hex (show t - 1 < t by omega)
      by_contra h
      exact hnot ⟨by omega, by omega⟩
  have hstep := hs (t - 1)
  rw [show t - 1 + 1 = t by omega] at hstep
  exact ⟨t, ht.1, by omega⟩

private theorem forward_flow_hits (w : ℕ → Fin 3) (hb : BoundaryHitWitnesses w) :
    HasFlowLineHits w := by
  constructor
  · apply forward_future_hit (L w)
    · intro n
      have hs : L w (n + 1) = L w n +
          (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
      have hl : (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
        change (-1 : ℤ) ≤ (w n : ℤ) - 1
        omega
      omega
    · intro a
      obtain ⟨n, hn⟩ := hb.leftHit (min a (-1)) (min_le_right _ _)
      exact ⟨n, hn ▸ min_le_left _ _⟩
  · apply forward_future_hit (R w)
    · intro n
      have hs : R w (n + 1) = R w n +
          (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
      have hl : (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
        change (-1 : ℤ) ≤ if w n = 0 then 0 else if w n = 1 then 1 else -1
        split
        · omega
        · split <;> omega
      omega
    · exact hb.R_unbounded_below

private theorem forward_up_fresh_unreachable (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (n : ℕ) (hc : w n = 1)
    (hu : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).nextVertex⟩ := by
  let h := forward_flow_hits w hb
  obtain ⟨k, hk | hk⟩ := flowLine_phase_partition w h n
  · exact (hu (flowLine_phase_reachable w h k n hk.1 hk.2)).elim
  · have hlt : n + 1 < walkNR w h (k + 1) := by
      by_contra hnot
      have heq : walkNR w h (k + 1) - 1 = n := by omega
      have hcode := walkNR_succ_previous_code w h k
      rw [heq, hc] at hcode
      contradiction
    exact lPhase_up_fresh_vertex_unreachable w h k n hk.1 hlt hc

private theorem forward_missing_west_unreachable (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (he : ¬ EdgePresent w e) :
    ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ := by
  obtain ⟨⟨k, hk, hw⟩, _⟩ := forward_missing_endpoints w hb e he
  have noReach (v : PresentVertex w) (hv : v.id ≠ 0)
      (hi : ∀ f, EdgePresent w f → edgeEast w f ≠ v.id) :
      ¬ Reachable (⟨0⟩ : PresentVertex w) v := by
    intro ⟨p⟩
    cases p with
    | nil => exact hv rfl
    | cons p f => exact hi f.val f.property.1 f.property.2.2
  apply noReach
  · intro hz
    change edgeWest w e = 0 at hz
    have heq : boundaryVertex w hb k = boundaryVertex w hb 0 := by
      rw [← hw, hz, boundaryVertex_zero]
    have := boundaryVertex_injective w hb heq
    omega
  · intro f hf heq
    exact boundaryVertex_nonpos_no_incoming w hb (by omega) f hf (heq.trans hw)

section ForwardScan
variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

private theorem forward_symm_endpoint (d : ℕ × Bool) :
    kmswDartEndpoint w ((kmswInfRot w hfin).symm d) = kmswDartEndpoint w d := by
  apply (kmswInfRot_exists_pow_iff_endpoint w hfin _ _).mp
  exact ⟨1, by simp only [pow_one, Equiv.apply_symm_apply]⟩

private theorem forward_face_endpoint (d : ℕ × Bool) :
    kmswDartEndpoint w (kmswInfFaceSucc w hfin d) =
      kmswDartEndpoint w (d.1, !d.2) :=
  forward_symm_endpoint w hfin (d.1, !d.2)

private theorem forward_face_mem (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : d ∈ stageTriangleDartList w j) :
    kmswInfFaceSucc w hfin d ∈ stageTriangleDartList w j := by
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with rfl | rfl | rfl
  · exact Or.inr (Or.inl hc.1)
  · exact Or.inr (Or.inr hc.2.1)
  · exact Or.inl hc.2.2.1

private theorem forward_triangle_corner_cases (j : TriangleCreationTime w)
    (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList w j) (htag : d.2 = false)
    (hqtag : (kmswInfFaceSucc w hfin d).2 = true) :
    kmswInfFaceSucc w hfin (kmswInfFaceSucc w hfin
      (kmswInfFaceSucc w hfin d)) = d ∧
      ((kmswInfFaceSucc w hfin (kmswInfFaceSucc w hfin d)).2 = false ∨
        (w j.val = 1 ∧ d.1 = (kmswStage w j.val).active ∧
          (kmswInfFaceSucc w hfin d).1 = (kmswStage w j.val).nextEdge + 1)) := by
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · rw [hc.1, hc.2.1]
    rw [hc.1] at hqtag
    refine ⟨hc.2.2.1, ?_⟩
    rcases j.property with h0 | h1
    · cases hl : (kmswStage w j.val).UL.dropLast.reverse <;>
        simp [stageTriangleDartTriple, h0, hl] at hqtag ⊢
    · simp [stageTriangleDartTriple, h1]
  · rw [hc.2.1, hc.2.2.1]
    refine ⟨hc.1, ?_⟩
    rcases j.property with h0 | h1
    · cases hl : (kmswStage w j.val).UL.dropLast.reverse <;>
        simp [stageTriangleDartTriple, h0, hl] at htag ⊢
    · have h0 : w j.val ≠ 0 := by rw [h1]; decide
      simp [stageTriangleDartTriple, h0] at htag
  · rw [hc.2.2.1, hc.1]
    rw [hc.2.2.1] at hqtag
    refine ⟨hc.2.1, ?_⟩
    rcases j.property with h0 | h1
    · cases hl : (kmswStage w j.val).UL.dropLast.reverse <;>
        simp [stageTriangleDartTriple, h0, hl] at htag hqtag ⊢
    · have h0 : w j.val ≠ 0 := by rw [h1]; decide
      simp [stageTriangleDartTriple, h0] at htag

private theorem forward_incoming_tail_step (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime w) (p : ℕ)
    (hp : (p, false) ∈ stageTriangleDartList w j)
    (hu : ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w p⟩)
    (hqtag : (kmswInfFaceSucc w hfin (p, false)).2 = true) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨edgeWest w (kmswInfFaceSucc w hfin (p, false)).1⟩ := by
  let q := kmswInfFaceSucc w hfin (p, false)
  let z := kmswInfFaceSucc w hfin q
  obtain ⟨hcycle, hz | ⟨hc, hpact, hqedge⟩⟩ :=
    forward_triangle_corner_cases w hfin j (p, false) hp rfl hqtag
  · change z.2 = false at hz
    change q.2 = true at hqtag
    have hw : edgeWest w z.1 = edgeWest w q.1 := by
      have hh := forward_face_endpoint w hfin q
      change kmswDartEndpoint w z = kmswDartEndpoint w (q.1, !q.2) at hh
      simpa only [kmswDartEndpoint, hqtag, hz, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] using hh
    have he : edgeEast w z.1 = edgeWest w p := by
      have hh := forward_face_endpoint w hfin z
      rw [hcycle] at hh
      simpa only [kmswDartEndpoint, hz, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] using hh.symm
    intro hr
    have hrz : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w z.1⟩ := by
      rw [hw]
      exact hr
    by_cases hpz : EdgePresent w z.1
    · apply hu
      have ht := hrz.trans (Quiver.Hom.reachable
        (⟨z.1, hpz, rfl, rfl⟩ :
          (⟨edgeWest w z.1⟩ : PresentVertex w) ⟶ ⟨edgeEast w z.1⟩))
      exact he ▸ ht
    · exact forward_missing_west_unreachable w hb z.1 hpz hrz
  · have ha : p = act w j.val := hpact
    have hbound := act_lt_nextEdge w (le_refl j.val)
    have hun : ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w j.val).west (act w j.val)⟩ := by
      rw [(edge_endpoints_eq w hbound).1, ← ha]
      exact hu
    have hfresh := forward_up_fresh_unreachable w hb j.val hc hun
    have halloc : (kmswStage w j.val).nextEdge + 1 <
        (kmswStage w (j.val + 1)).nextEdge := by
      simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, State.addEdge]
    have hw : edgeWest w q.1 = (kmswStage w j.val).nextVertex := by
      rw [hqedge, ← (edge_endpoints_eq w halloc).1]
      simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, State.addEdge]
    rw [hw]
    exact hfresh


private theorem forward_unreachable_scan_step (hb : BoundaryHitWitnesses w)
    (p : ℕ) (hp : EdgePresent w p)
    (hu : ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w p⟩)
    (hv : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w p⟩) :
    let d := (kmswInfRot w hfin).symm (p, true)
    (d.2 = false → MhatWestBoundaryEdge w d.1) ∧
      (d.2 = true → ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩) := by
  let d := (kmswInfRot w hfin).symm (p, true)
  change (d.2 = false → MhatWestBoundaryEdge w d.1) ∧ _
  obtain ⟨j, hj⟩ := forward_present_west_triangle w hb p hp
  have hdface : kmswInfFaceSucc w hfin (p, false) = d := rfl
  have hdpoint : kmswDartEndpoint w d = edgeEast w p :=
    forward_symm_endpoint w hfin (p, true)
  have hpd := forward_incident_present w hb (edgeEast w p) ⟨p, hp, rfl⟩ d hdpoint
  have hdj := forward_face_mem w hfin j (p, false) hj
  rw [hdface] at hdj
  constructor
  · intro htag
    have hw : edgeWest w d.1 = edgeEast w p := by
      simpa only [kmswDartEndpoint, htag, Bool.false_eq_true, ↓reduceIte] using hdpoint
    have htail : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩ := by
      rw [hw]
      exact hv
    have hhead := htail.trans (Quiver.Hom.reachable
      (⟨d.1, hpd, rfl, rfl⟩ :
        (⟨edgeWest w d.1⟩ : PresentVertex w) ⟶ ⟨edgeEast w d.1⟩))
    have hdj' : (d.1, false) ∈ stageTriangleDartList w j := by
      exact (Prod.ext rfl htag : d = (d.1, false)) ▸ hdj
    obtain ⟨n, t, ht, hbound, hface, hrec⟩ := forward_triangle_of_mem w j d.1 hdj'
    refine ⟨hpd, htail, hhead, n, t, ht, hbound, hface, ?_⟩
    rw [hrec]
    intro hr
    exact hu (hr p ((forward_dart_record_iff w j p).mpr
      ⟨(p, false), hj, rfl⟩)).1
  · intro htag
    exact forward_incoming_tail_step w hfin hb j p hj hu htag

include hfin in
private theorem forward_crossing_incoming_boundary (hb : BoundaryHitWitnesses w)
    (p : ℕ) (hp : EdgePresent w p)
    (hu : ¬ MhatVertex w (edgeWest w p))
    (hv : MhatVertex w (edgeEast w p)) :
    ∃ f, MhatWestBoundaryEdge w f ∧ edgeWest w f = edgeEast w p := by
  classical
  let c : ℕ × Bool := (p, true)
  have hc : kmswDartEndpoint w c = edgeEast w p := rfl
  let hout := kmswM0_vertex_outgoing w hfin hb (edgeEast w p)
  let hex := kmswFirstOutgoingAtCorner_symm_exists w hfin c (edgeEast w p) hc hout
  let i := Nat.find hex
  let d (n : ℕ) := ((kmswInfRot w hfin).symm ^ n) c
  have hstep (n : ℕ) : d (n + 1) = (kmswInfRot w hfin).symm (d n) := by
    simp only [d, pow_succ', Equiv.Perm.mul_apply]
  have hpoint (n : ℕ) : kmswDartEndpoint w (d n) = edgeEast w p := by
    induction n with
    | zero => exact hc
    | succ n ih =>
      rw [hstep]
      exact (forward_symm_endpoint w hfin _).trans ih
  have hin (n : ℕ) (hn : n < i) :
      (d n).2 = true ∧ EdgePresent w (d n).1 ∧ edgeEast w (d n).1 = edgeEast w p := by
    have hpres := forward_incident_present w hb (edgeEast w p)
      ⟨p, hp, rfl⟩ (d n) (hpoint n)
    have hnot := Nat.find_min hex hn
    have htag : (d n).2 = true := by
      cases ht : (d n).2
      · exact (hnot ⟨ht, hpres⟩).elim
      · rfl
    refine ⟨htag, hpres, ?_⟩
    simpa only [kmswDartEndpoint, htag, ↓reduceIte] using hpoint n
  have hscan (n : ℕ) (hn : n < i) :
      ((d (n + 1)).2 = false → MhatWestBoundaryEdge w (d (n + 1)).1) ∧
      ((d (n + 1)).2 = true → ¬ MhatVertex w (edgeWest w (d (n + 1)).1)) := by
    induction n with
    | zero => exact forward_unreachable_scan_step w hfin hb p hp hu hv
    | succ n ih =>
      have hn' : n < i := by omega
      have hprev := hin (n + 1) hn
      have hun := (ih hn').2 hprev.1
      have hreach : MhatVertex w (edgeEast w (d (n + 1)).1) := by
        rw [hprev.2.2]
        exact hv
      have hs := forward_unreachable_scan_step w hfin hb
        (d (n + 1)).1 hprev.2.1 hun hreach
      rw [hstep (n + 1)]
      have hpair : d (n + 1) = ((d (n + 1)).1, true) := Prod.ext rfl hprev.1
      rw [hpair]
      exact hs
  have hselected : kmswPresentOutgoingDart w (d i) := Nat.find_spec hex
  have hi : 0 < i := by
    by_contra h
    have hi0 : i = 0 := by omega
    rw [hi0] at hselected
    exact Bool.noConfusion hselected.1
  have hs := (hscan (i - 1) (by omega)).1
  rw [show i - 1 + 1 = i by omega] at hs
  refine ⟨(d i).1, hs hselected.1, ?_⟩
  simpa only [kmswDartEndpoint, hselected.1, Bool.false_eq_true, ↓reduceIte]
    using hpoint i

end ForwardScan

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Every reachable endpoint of a crossing geometric edge lies on the west boundary -/
theorem reachableEndpointCrossingWestBoundaryGoal_holds (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) : reachableEndpointCrossingWestBoundaryGoal w := by
  intro e v hnot hv hend
  by_cases hv0 : v = 0
  · refine ⟨(kmswBeta0First w hfin hb).1, beta0_westBoundary_first w hfin hb, ?_⟩
    exact Or.inl ((kmswBeta0First_spec w hfin hb).2.1.trans hv0.symm)
  have hin : ∃ f, EdgePresent w f ∧ edgeEast w f = v := by
    obtain ⟨p⟩ := hv
    cases p with
    | nil => exact (hv0 rfl).elim
    | cons p f => exact ⟨f.val, f.property.1, f.property.2.2⟩
  have hp : EdgePresent w e := by
    rcases hend with hw | he
    · exact forward_incident_present w hb v hin (e, false) hw
    · exact forward_incident_present w hb v hin (e, true) he
  have heast : edgeEast w e = v := by
    rcases hend with hw | he
    · have hr : MhatVertex w (edgeWest w e) := hw ▸ hv
      have hr' := hr.trans (Quiver.Hom.reachable
        (⟨e, hp, rfl, rfl⟩ :
          (⟨edgeWest w e⟩ : PresentVertex w) ⟶ ⟨edgeEast w e⟩))
      exact (hnot ⟨hr, hr'⟩).elim
    · exact he
  have hwest : ¬ MhatVertex w (edgeWest w e) := by
    intro hr
    exact hnot ⟨hr, heast ▸ hv⟩
  obtain ⟨f, hf, hfv⟩ := forward_crossing_incoming_boundary w hfin hb e hp hwest
    (heast ▸ hv)
  exact ⟨f, hf, Or.inl (hfv.trans heast)⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
A primed vertex is unreachable or incident to a retained β₀ edge -/
theorem primeVertexSourceCharacterization_forward (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (v : ℕ) (hv : primeVertex w hfin hb v) :
    ¬ MhatVertex w v ∨
      ∃ e, primeBetaEdge w hfin hb e ∧ (edgeWest w e = v ∨ edgeEast w e = v) := by
  classical
  by_cases hr : MhatVertex w v
  · right
    obtain ⟨e, he, hend⟩ := hv
    rcases he with hnot | hbeta
    · obtain ⟨f, hf, hfv⟩ :=
        reachableEndpointCrossingWestBoundaryGoal_holds w hfin hb e v hnot hr hend
      exact ⟨f, (primeBetaEdge_iff_MhatWestBoundaryEdge w hfin hb f).mpr hf, hfv⟩
    · exact ⟨e, hbeta, hend⟩
  · exact Or.inl hr

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The primed vertex carrier has its complete reachability/boundary characterization -/
theorem primeVertexSourceCharacterizationGoal_holds (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) : primeVertexSourceCharacterizationGoal w hfin hb := by
  intro v
  exact ⟨primeVertexSourceCharacterization_forward w hfin hb v,
    primeVertexSourceCharacterization_reverse w hfin hb v⟩

end DirectedDistances.KMSW
