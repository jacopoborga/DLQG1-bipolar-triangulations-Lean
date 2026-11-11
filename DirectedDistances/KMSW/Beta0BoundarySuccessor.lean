module

public import DirectedDistances.KMSW.Beta0WestBoundary
import DirectedDistances.KMSW.OutgoingIntervalFreshLeft
import DirectedDistances.KMSW.InfiniteTriangulation
import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.SDPIdentifyBdy
import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
import DirectedDistances.KMSW.PrimedSimCrossingInvariant

/-! # Geometric successors on the M̂ west boundary

The relation below records a west-boundary edge at the head of a given
west-boundary edge which is first in the inverse-rotation scan among such
boundary edges. The scan-to-boundary identification remains a helper toward -/

public section
namespace DirectedDistances.KMSW

/-- The first M̂ west-boundary edge after `e` at its head, in the inverse
rotation scan used by β₀. Helper toward Lemma 5.12; not a paper result -/
@[expose] def MhatWestBoundarySuccessor (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (e : {f : ℕ // MhatWestBoundaryEdge w f}) (g : ℕ) : Prop :=
  MhatWestBoundaryEdge w g ∧ edgeWest w g = edgeEast w e.1 ∧
    let c := kmswBeta0IncomingCorner ⟨e.1, e.property.1⟩
    let i := kmswFirstOutgoingIndex_symm w hfin c (edgeEast w e.1)
      (kmswBeta0IncomingCorner_spec ⟨e.1, e.property.1⟩)
      (kmswM0_vertex_outgoing w hfin h (edgeEast w e.1))
    ((kmswInfRot w hfin).symm ^ i) c = (g, false) ∧
      ∀ f, MhatWestBoundaryEdge w f → edgeWest w f = edgeEast w e.1 →
        f ≠ g → ∃ j, i < j ∧ ((kmswInfRot w hfin).symm ^ j) c = (f, false)

/-- There is at most one first west-boundary successor in the inverse-rotation
scan. Helper toward Lemma 5.12; not a paper result -/
theorem MhatWestBoundarySuccessor_unique (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (e : {f : ℕ // MhatWestBoundaryEdge w f}) {g f : ℕ}
    (hg : MhatWestBoundarySuccessor w hfin h e g)
    (hf : MhatWestBoundarySuccessor w hfin h e f) :
    g = f := by
  dsimp [MhatWestBoundarySuccessor] at hg hf
  exact congrArg Prod.fst (hg.2.2.1.symm.trans hf.2.2.1)


open Quiver

private theorem boundary_dart_record_iff (w : ℕ → Fin 3)
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

private theorem boundary_present_west_triangle (w : ℕ → Fin 3)
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

private theorem boundary_triangle_of_mem (w : ℕ → Fin 3)
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

private theorem boundary_missing_LL (w : ℕ → Fin 3)
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

private theorem boundary_missing_endpoints
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (e : ℕ)
    (hne : ¬ EdgePresent w e) :
    (∃ k : ℤ, k ≤ -1 ∧ edgeWest w e = boundaryVertex w h k) ∧
      (∃ k : ℤ, k ≤ 0 ∧ edgeEast w e = boundaryVertex w h k) := by
  obtain ⟨n, heLL⟩ := boundary_missing_LL w h e hne
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

private theorem boundary_incident_present
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (v : ℕ)
    (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v)
    (d : ℕ × Bool)
    (hdv : kmswDartEndpoint w d = v) : EdgePresent w d.1 := by
  by_contra hmissing
  obtain ⟨⟨k, hk, hwest⟩, ⟨l, hl,heast⟩⟩ :=
    boundary_missing_endpoints w h d.1 hmissing
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

private theorem boundary_future_hit (f : ℕ → ℤ)
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

private theorem boundary_flow_hits (w : ℕ → Fin 3) (hb : BoundaryHitWitnesses w) :
    HasFlowLineHits w := by
  constructor
  · apply boundary_future_hit (L w)
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
  · apply boundary_future_hit (R w)
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

private theorem boundary_up_fresh_unreachable (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (n : ℕ) (hc : w n = 1)
    (hu : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).nextVertex⟩ := by
  let h := boundary_flow_hits w hb
  obtain ⟨k, hk | hk⟩ := flowLine_phase_partition w h n
  · exact (hu (flowLine_phase_reachable w h k n hk.1 hk.2)).elim
  · have hlt : n + 1 < walkNR w h (k + 1) := by
      by_contra hnot
      have heq : walkNR w h (k + 1) - 1 = n := by omega
      have hcode := walkNR_succ_previous_code w h k
      rw [heq, hc] at hcode
      contradiction
    exact lPhase_up_fresh_vertex_unreachable w h k n hk.1 hlt hc

private theorem boundary_missing_west_unreachable (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (he : ¬ EdgePresent w e) :
    ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ := by
  obtain ⟨⟨k, hk, hw⟩, _⟩ := boundary_missing_endpoints w hb e he
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

section BoundaryScan
variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

private theorem boundary_symm_endpoint (d : ℕ × Bool) :
    kmswDartEndpoint w ((kmswInfRot w hfin).symm d) = kmswDartEndpoint w d := by
  apply (kmswInfRot_exists_pow_iff_endpoint w hfin _ _).mp
  exact ⟨1, by simp only [pow_one, Equiv.apply_symm_apply]⟩

private theorem boundary_face_endpoint (d : ℕ × Bool) :
    kmswDartEndpoint w (kmswInfFaceSucc w hfin d) =
      kmswDartEndpoint w (d.1, !d.2) :=
  boundary_symm_endpoint w hfin (d.1, !d.2)

private theorem boundary_face_mem (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : d ∈ stageTriangleDartList w j) :
    kmswInfFaceSucc w hfin d ∈ stageTriangleDartList w j := by
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with rfl | rfl | rfl
  · exact Or.inr (Or.inl hc.1)
  · exact Or.inr (Or.inr hc.2.1)
  · exact Or.inl hc.2.2.1

private theorem boundary_triangle_corner_cases (j : TriangleCreationTime w)
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

private theorem boundary_incoming_tail_step (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime w) (p : ℕ)
    (hp : (p, false) ∈ stageTriangleDartList w j)
    (hu : ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w p⟩)
    (hqtag : (kmswInfFaceSucc w hfin (p, false)).2 = true) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨edgeWest w (kmswInfFaceSucc w hfin (p, false)).1⟩ := by
  let q := kmswInfFaceSucc w hfin (p, false)
  let z := kmswInfFaceSucc w hfin q
  obtain ⟨hcycle, hz | ⟨hc, hpact, hqedge⟩⟩ :=
    boundary_triangle_corner_cases w hfin j (p, false) hp rfl hqtag
  · change z.2 = false at hz
    change q.2 = true at hqtag
    have hw : edgeWest w z.1 = edgeWest w q.1 := by
      have hh := boundary_face_endpoint w hfin q
      change kmswDartEndpoint w z = kmswDartEndpoint w (q.1, !q.2) at hh
      simpa only [kmswDartEndpoint, hqtag, hz, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] using hh
    have he : edgeEast w z.1 = edgeWest w p := by
      have hh := boundary_face_endpoint w hfin z
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
    · exact boundary_missing_west_unreachable w hb z.1 hpz hrz
  · have ha : p = act w j.val := hpact
    have hbound := act_lt_nextEdge w (le_refl j.val)
    have hun : ¬ Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w j.val).west (act w j.val)⟩ := by
      rw [(edge_endpoints_eq w hbound).1, ← ha]
      exact hu
    have hfresh := boundary_up_fresh_unreachable w hb j.val hc hun
    have halloc : (kmswStage w j.val).nextEdge + 1 <
        (kmswStage w (j.val + 1)).nextEdge := by
      simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, State.addEdge]
    have hw : edgeWest w q.1 = (kmswStage w j.val).nextVertex := by
      rw [hqedge, ← (edge_endpoints_eq w halloc).1]
      simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, State.addEdge]
    rw [hw]
    exact hfresh

private theorem boundary_third_reachable (a b c : ℕ × Bool)
    (hbc : kmswInfFaceSucc w hfin b = c)
    (hca : kmswInfFaceSucc w hfin c = a)
    (ha : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w a.1⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w a.1⟩)
    (hb : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w b.1⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w b.1⟩) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w c.1⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w c.1⟩ := by
  have hhead := boundary_face_endpoint w hfin b
  have htail := boundary_face_endpoint w hfin c
  rw [hbc] at hhead
  rw [hca] at htail
  have hrhead : Reachable (⟨0⟩ : PresentVertex w) ⟨kmswDartEndpoint w c⟩ := by
    rw [hhead]
    change Reachable (⟨0⟩ : PresentVertex w)
      ⟨if !b.2 then edgeEast w b.1 else edgeWest w b.1⟩
    cases b.2
    · exact hb.2
    · exact hb.1
  have hrtail : Reachable (⟨0⟩ : PresentVertex w)
      ⟨kmswDartEndpoint w (c.1, !c.2)⟩ := by
    rw [← htail]
    cases hatag : a.2 <;> simp only [kmswDartEndpoint, hatag] <;>
      first | exact ha.1 | exact ha.2
  cases hctag : c.2
  · exact ⟨by simpa [kmswDartEndpoint, hctag] using hrhead,
      by simpa [kmswDartEndpoint, hctag] using hrtail⟩
  · exact ⟨by simpa [kmswDartEndpoint, hctag] using hrtail,
      by simpa [kmswDartEndpoint, hctag] using hrhead⟩

private theorem boundary_triangle_reachable (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : d ∈ stageTriangleDartList w j)
    (ha : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w d.1⟩)
    (hb : Reachable (⟨0⟩ : PresentVertex w)
        ⟨edgeWest w (kmswInfFaceSucc w hfin d).1⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨edgeEast w (kmswInfFaceSucc w hfin d).1⟩) :
    HatTriangleReachable w (stageTriangleRecord w j) := by
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  have hall : ∀ q ∈ stageTriangleDartList w j,
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w q.1⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w q.1⟩ := by
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with rfl | rfl | rfl
    · rw [hc.1] at hb
      have hz := boundary_third_reachable w hfin _ _ _ hc.2.1 hc.2.2.1 ha hb
      rintro q (rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact hz
    · rw [hc.2.1] at hb
      have hz := boundary_third_reachable w hfin _ _ _ hc.2.2.1 hc.1 ha hb
      rintro q (rfl | rfl | rfl)
      · exact hz
      · exact ha
      · exact hb
    · rw [hc.2.2.1] at hb
      have hz := boundary_third_reachable w hfin _ _ _ hc.1 hc.2.1 ha hb
      rintro q (rfl | rfl | rfl)
      · exact hb
      · exact hz
      · exact ha
  intro e he
  obtain ⟨q, hq, rfl⟩ := (boundary_dart_record_iff w j e).mp he
  exact hall q hq

private theorem boundary_edge_exterior_triangle (e : ℕ)
    (he : MhatWestBoundaryEdge w e) :
    ∃ j : TriangleCreationTime w, (e, false) ∈ stageTriangleDartList w j ∧
      ¬ HatTriangleReachable w (stageTriangleRecord w j) := by
  obtain ⟨n, t, _, hbound, ⟨j, hj, hrec, hbase, _⟩, hnot⟩ := he.2.2.2
  refine ⟨j, ?_, ?_⟩
  · simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false]
    rcases hbase with h | h | h
    · exact Or.inl (congrArg (fun d : StageDart (kmswStage w n).nextEdge =>
        (d.1.val, d.2)) h)
    · exact Or.inr (Or.inl
        (congrArg (fun d : StageDart (kmswStage w n).nextEdge => (d.1.val, d.2)) h))
    · exact Or.inr (Or.inr
        (congrArg (fun d : StageDart (kmswStage w n).nextEdge => (d.1.val, d.2)) h))
  · rw [hrec]
    exact hnot

/-- Helper toward Lemma 5.12; not a paper result.
The first inverse-rotation step either already gives a west-boundary edge,
or gives an incoming dart with unreachable tail. This transfers the initial -/
theorem beta0_westBoundary_first_scan_dichotomy (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    let d := (kmswInfRot w hfin).symm (e, true)
    (d.2 = false → MhatWestBoundaryEdge w d.1) ∧
      (d.2 = true →
        ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩) := by
  let d := (kmswInfRot w hfin).symm (e, true)
  change (d.2 = false → MhatWestBoundaryEdge w d.1) ∧
    (d.2 = true → ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩)
  have hdface : kmswInfFaceSucc w hfin (e, false) = d := rfl
  have hdpoint : kmswDartEndpoint w d = edgeEast w e :=
    boundary_symm_endpoint w hfin (e, true)
  have hp := boundary_incident_present w hb (edgeEast w e)
    ⟨e, he.1, rfl⟩ d hdpoint
  obtain ⟨j, hj, hnot⟩ := boundary_edge_exterior_triangle w e he
  have hdj : d ∈ stageTriangleDartList w j := by
    rw [← hdface]
    exact boundary_face_mem w hfin j (e, false) hj
  constructor
  · intro htag
    have htail : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩ := by
      have heq : edgeWest w d.1 = edgeEast w e := by
        simpa only [kmswDartEndpoint, htag, Bool.false_eq_true, ↓reduceIte] using hdpoint
      rw [heq]
      exact he.2.2.1
    have hhead := htail.trans (Quiver.Hom.reachable
      (⟨d.1, hp, rfl, rfl⟩ :
        (⟨edgeWest w d.1⟩ : PresentVertex w) ⟶ ⟨edgeEast w d.1⟩))
    have hdj' : (d.1, false) ∈ stageTriangleDartList w j := by
      have hd : d = (d.1, false) := Prod.ext rfl htag
      exact hd ▸ hdj
    obtain ⟨n, t, ht, hbound, hface, hrec⟩ := boundary_triangle_of_mem w j d.1 hdj'
    refine ⟨hp, htail, hhead, n, t, ht, hbound, hface, ?_⟩
    rw [hrec]
    exact hnot
  · intro htag hreach
    apply hnot
    apply boundary_triangle_reachable w hfin j (e, false) hj
      ⟨he.2.1, he.2.2.1⟩
    rw [hdface]
    refine ⟨hreach, ?_⟩
    have heq : edgeEast w d.1 = edgeEast w e := by
      simpa only [kmswDartEndpoint, htag, ↓reduceIte] using hdpoint
    rw [heq]
    exact he.2.2.1

private theorem boundary_unreachable_scan_step (hb : BoundaryHitWitnesses w)
    (p : ℕ) (hp : EdgePresent w p)
    (hu : ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w p⟩)
    (hv : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w p⟩) :
    let d := (kmswInfRot w hfin).symm (p, true)
    (d.2 = false → MhatWestBoundaryEdge w d.1) ∧
      (d.2 = true → ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩) := by
  let d := (kmswInfRot w hfin).symm (p, true)
  change (d.2 = false → MhatWestBoundaryEdge w d.1) ∧ _
  obtain ⟨j, hj⟩ := boundary_present_west_triangle w hb p hp
  have hdface : kmswInfFaceSucc w hfin (p, false) = d := rfl
  have hdpoint : kmswDartEndpoint w d = edgeEast w p :=
    boundary_symm_endpoint w hfin (p, true)
  have hpd := boundary_incident_present w hb (edgeEast w p) ⟨p, hp, rfl⟩ d hdpoint
  have hdj := boundary_face_mem w hfin j (p, false) hj
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
    obtain ⟨n, t, ht, hbound, hface, hrec⟩ := boundary_triangle_of_mem w j d.1 hdj'
    refine ⟨hpd, htail, hhead, n, t, ht, hbound, hface, ?_⟩
    rw [hrec]
    intro hr
    exact hu (hr p ((boundary_dart_record_iff w j p).mpr
      ⟨(p, false), hj, rfl⟩)).1
  · intro htag
    exact boundary_incoming_tail_step w hfin hb j p hj hu htag

/-- Helper toward Lemma 5.12; not a paper result.
Every scan entry before the selected outgoing dart is a present incoming
dart at the head of the boundary edge; missing geometric edges cannot be
incident to a vertex admitting an incoming edge -/
theorem beta0_westBoundary_next_scan_incoming (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) (n : ℕ)
    (hn : n < kmswFirstOutgoingIndex_symm w hfin
      (kmswBeta0IncomingCorner ⟨e, he.1⟩) (edgeEast w e)
      (kmswBeta0IncomingCorner_spec ⟨e, he.1⟩)
      (kmswM0_vertex_outgoing w hfin hb (edgeEast w e))) :
    let d := ((kmswInfRot w hfin).symm ^ n)
      (kmswBeta0IncomingCorner ⟨e, he.1⟩)
    d.2 = true ∧ EdgePresent w d.1 ∧ edgeEast w d.1 = edgeEast w e := by
  let c := kmswBeta0IncomingCorner ⟨e, he.1⟩
  let d := ((kmswInfRot w hfin).symm ^ n) c
  have hpoint : ∀ m, kmswDartEndpoint w
      (((kmswInfRot w hfin).symm ^ m) c) = edgeEast w e := by
    intro m
    induction m with
    | zero => exact kmswBeta0IncomingCorner_spec ⟨e, he.1⟩
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (boundary_symm_endpoint w hfin _).trans ih
  have hp := boundary_incident_present w hb (edgeEast w e)
    ⟨e, he.1, rfl⟩ d (hpoint n)
  have hnot := (kmswBeta0Next_spec w hfin hb ⟨e, he.1⟩).2.2 n hn
  have htag : d.2 = true := by
    cases htag : d.2
    · exact (hnot ⟨htag, hp⟩).elim
    · rfl
  refine ⟨htag, hp, ?_⟩
  have hdpoint : kmswDartEndpoint w d = edgeEast w e := hpoint n
  simpa only [kmswDartEndpoint, htag, ↓reduceIte] using hdpoint

/-- Helper toward Lemma 5.12; not a paper result.
The selected next edge has two reachable endpoints. Its exterior west-face
condition is proved separately below -/
theorem beta0_westBoundary_next_reachable (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    Reachable (⟨0⟩ : PresentVertex w)
        ⟨edgeWest w (kmswBeta0Next w hfin hb ⟨e, he.1⟩).1⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨edgeEast w (kmswBeta0Next w hfin hb ⟨e, he.1⟩).1⟩ := by
  let g := kmswBeta0Next w hfin hb ⟨e, he.1⟩
  have hgw : edgeWest w g.1 = edgeEast w e :=
    (kmswBeta0Next_spec w hfin hb ⟨e, he.1⟩).2.1
  have htail : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w g.1⟩ := by
    rw [hgw]
    exact he.2.2.1
  exact ⟨htail, htail.trans (Quiver.Hom.reachable
    (⟨g.1, g.2, rfl, rfl⟩ :
      (⟨edgeWest w g.1⟩ : PresentVertex w) ⟶ ⟨edgeEast w g.1⟩))⟩

/-- Helper toward Lemma 5.12; not a paper result.
The first outgoing edge in the inverse-rotation scan is again on the west -/
theorem beta0_westBoundary_next (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    MhatWestBoundaryEdge w (kmswBeta0Next w hfin hb ⟨e, he.1⟩).1 := by
  classical
  let c := kmswBeta0IncomingCorner ⟨e, he.1⟩
  let i := kmswFirstOutgoingIndex_symm w hfin c (edgeEast w e)
    (kmswBeta0IncomingCorner_spec ⟨e, he.1⟩)
    (kmswM0_vertex_outgoing w hfin hb (edgeEast w e))
  let d (n : ℕ) := ((kmswInfRot w hfin).symm ^ n) c
  have hstep (n : ℕ) : d (n + 1) = (kmswInfRot w hfin).symm (d n) := by
    simp only [d, pow_succ', Equiv.Perm.mul_apply]
  have hin (n : ℕ) (hn : n < i) :
      (d n).2 = true ∧ EdgePresent w (d n).1 ∧
        edgeEast w (d n).1 = edgeEast w e :=
    beta0_westBoundary_next_scan_incoming w hfin hb e he n hn
  have hscan (n : ℕ) (hn : n < i) :
      ((d (n + 1)).2 = false → MhatWestBoundaryEdge w (d (n + 1)).1) ∧
      ((d (n + 1)).2 = true →
        ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w (d (n + 1)).1⟩) := by
    induction n with
    | zero => exact beta0_westBoundary_first_scan_dichotomy w hfin hb e he
    | succ n ih =>
      have hn' : n < i := by omega
      have hprev := hin (n + 1) hn
      have hu := (ih hn').2 hprev.1
      have hv : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w (d (n + 1)).1⟩ := by
        rw [hprev.2.2]
        exact he.2.2.1
      have hs := boundary_unreachable_scan_step w hfin hb
        (d (n + 1)).1 hprev.2.1 hu hv
      rw [hstep (n + 1)]
      have hpair : d (n + 1) = ((d (n + 1)).1, true) := Prod.ext rfl hprev.1
      rw [hpair]
      exact hs
  have hout : kmswPresentOutgoingDart w (d i) := by
    exact Nat.find_spec (kmswFirstOutgoingAtCorner_symm_exists w hfin c (edgeEast w e)
      (kmswBeta0IncomingCorner_spec ⟨e, he.1⟩)
      (kmswM0_vertex_outgoing w hfin hb (edgeEast w e)))
  have hi : 0 < i := by
    by_contra h
    have hi0 : i = 0 := by omega
    rw [hi0] at hout
    have htag : (d 0).2 = true := rfl
    have hf := hout.1
    rw [htag] at hf
    exact Bool.noConfusion hf
  have hs := (hscan (i - 1) (by omega)).1
  rw [show i - 1 + 1 = i by omega] at hs
  exact hs hout.1

/-- Helper toward Lemma 5.12; not a paper result.
The selected next edge satisfies the complete west-boundary successor -/
theorem beta0_westBoundary_successor (hb : BoundaryHitWitnesses w)
    (e : {f : ℕ // MhatWestBoundaryEdge w f}) :
    MhatWestBoundarySuccessor w hfin hb e
      (kmswBeta0Next w hfin hb ⟨e.1, e.property.1⟩).1 := by
  classical
  refine ⟨beta0_westBoundary_next w hfin hb e.1 e.property,
    (kmswBeta0Next_spec w hfin hb ⟨e.1, e.property.1⟩).2.1, ?_, ?_⟩
  · apply Prod.ext
    · rfl
    · exact (Nat.find_spec (kmswFirstOutgoingAtCorner_symm_exists w hfin
        (kmswBeta0IncomingCorner ⟨e.1, e.property.1⟩) (edgeEast w e.1)
        (kmswBeta0IncomingCorner_spec ⟨e.1, e.property.1⟩)
        (kmswM0_vertex_outgoing w hfin hb (edgeEast w e.1)))).1
  · intro f hf hfv hne
    exact kmswBeta0Next_later w hfin hb ⟨e.1, e.property.1⟩ f hf.1 hfv hne

private theorem boundary_first_eq_left_exit (hb : BoundaryHitWitnesses w)
    (h : HasFlowLineHits w) :
    (kmswBeta0First w hfin hb).1 =
      act w (PaperProofs.Section5.sourceFlowNL w h 0 - 1) := by
  classical
  let t := PaperProofs.Section5.sourceFlowNL w h 0
  have hs := PaperProofs.Section5.sourceFlowNL_level_isLeast w h 0
  rw [PaperProofs.Section5.sourceFlowNR_zero] at hs
  have hL0 : L w 0 = 0 := by simp [L]
  rw [hL0] at hs
  have htpos : 0 < t := by have := hs.1.1; dsimp [t]; omega
  have htL : L w t = -1 := by simpa only [zero_sub] using hs.1.2
  have hbt : boundaryHitTime w hb (-1) = t := by
    apply le_antisymm
    · change Nat.find (hb.leftHit (-1) (by omega)) ≤ t
      exact Nat.find_min' _ htL
    · apply hs.2
      have hh := boundaryHitTime_left_spec w hb (by omega : (-1 : ℤ) ≤ -1)
      have hp : 0 < boundaryHitTime w hb (-1) := by
        by_contra hhpos
        have hz : boundaryHitTime w hb (-1) = 0 := by omega
        rw [hz, hL0] at hh
        omega
      exact ⟨by omega, by simpa only [zero_sub] using hh⟩
  have hc : w (t - 1) = 0 := by
    dsimp [t]
    rw [PaperProofs.Section5.sourceFlowNL_eq_walkNL]
    exact walkNL_previous_code w h 0
  obtain ⟨hbase, hnext, _⟩ := PaperProofs.Section5.sourceFlow_firstLeftExit_triangle w h
  have hUL : (kmswStage w (t - 1)).UL.dropLast.reverse = [] := hbase.2.2.2.1
  let j : TriangleCreationTime w := ⟨t - 1, Or.inl hc⟩
  have hcy := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  have htri := stageTriangleDartTriple_left_fresh w j hc hUL
  rw [htri] at hcy
  have hm : kmswLLCreatedEdge w t = (kmswStage w (t - 1)).nextEdge + 1 := by
    dsimp only [kmswLLCreatedEdge]
    change (kmswStage w t).nextEdge = (kmswStage w (t - 1)).nextEdge + 2 at hnext
    omega
  have hcorner : (kmswInfRot w hfin).symm (kmswBeta0RootCorner w hb) =
      (act w (t - 1), false) := by
    change (kmswInfRot w hfin).symm
      (kmswLLCreatedEdge w (boundaryHitTime w hb (-1)), true) = _
    rw [hbt, hm]
    exact hcy.2.2.1
  let c := kmswBeta0RootCorner w hb
  let hex := kmswFirstOutgoingAtCorner_symm_exists w hfin c 0
    (kmswBeta0RootCorner_endpoint w hb) (kmswM0_vertex_outgoing w hfin hb 0)
  have hi : Nat.find hex = 1 := by
    have hle : Nat.find hex ≤ 1 := by
      apply Nat.find_min'
      rw [pow_one, hcorner]
      exact ⟨rfl, ⟨t - 1, act_lt_nextEdge w le_rfl,
        kmswStage_active_present w (t - 1)⟩⟩
    have hne : Nat.find hex ≠ 0 := by
      intro hz
      have hh := (Nat.find_spec hex).1
      rw [hz] at hh
      change true = false at hh
      cases hh
    omega
  change (((kmswInfRot w hfin).symm ^ Nat.find hex) c).1 = _
  rw [hi, pow_one, hcorner]

/-- Helper toward Lemma 5.12; not a paper result.
The root-corner selector is on the west boundary of the reachable submap -/
theorem beta0_westBoundary_first (hb : BoundaryHitWitnesses w) :
    MhatWestBoundaryEdge w (kmswBeta0First w hfin hb).1 := by
  let h := boundary_flow_hits w hb
  rw [boundary_first_eq_left_exit w hfin hb h]
  exact mhatWestBoundaryEdge_leftExit w h 1 (by omega)

/-- Helper toward Lemma 5.12; not a paper result.
Every edge of the selected stream is on the west boundary of the reachable -/
theorem beta0_westBoundary_stream (hb : BoundaryHitWitnesses w) (n : ℕ) :
    MhatWestBoundaryEdge w (kmswBeta0Stream w hfin hb n).1 := by
  induction n with
  | zero => exact beta0_westBoundary_first w hfin hb
  | succ n ih => exact beta0_westBoundary_next w hfin hb _ ih

private theorem boundary_forward_not_outgoing (_hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    ¬ kmswPresentOutgoingDart w (kmswInfRot w hfin (e, false)) := by
  let d := kmswInfRot w hfin (e, false)
  obtain ⟨j, hj, hnot⟩ := boundary_edge_exterior_triangle w e he
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  have hpred : (d.1, !d.2) ∈ stageTriangleDartList w j := by
    have hinj : Function.Injective (kmswInfFaceSucc w hfin) :=
      (kmswInfFaceSucc w hfin).injective
    have hd : kmswInfFaceSucc w hfin (d.1, !d.2) = (e, false) := by
      change (kmswInfRot w hfin).symm (d.1, !(!d.2)) = _
      simp only [Bool.not_not]
      exact Equiv.symm_apply_apply _ _
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
    rcases hj with hj | hj | hj
    · exact Or.inr (Or.inr (hinj (hd.trans (hc.2.2.1.trans hj.symm).symm)))
    · exact Or.inl (hinj (hd.trans (hc.1.trans hj.symm).symm))
    · exact Or.inr (Or.inl (hinj (hd.trans (hc.2.1.trans hj.symm).symm)))
  intro hout
  have hdtag : d.2 = false := hout.1
  have hdpoint : kmswDartEndpoint w d = edgeWest w e := by
    have hh := (kmswInfRot_exists_pow_iff_endpoint w hfin (e, false) d).mp
      ⟨1, by simp only [pow_one]; rfl⟩
    exact hh.symm
  have hw : edgeWest w d.1 = edgeWest w e := by
    simpa only [kmswDartEndpoint, hdtag, Bool.false_eq_true, ↓reduceIte] using hdpoint
  have hrw : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w d.1⟩ := hw ▸ he.2.1
  have hre := hrw.trans (Quiver.Hom.reachable
    (⟨d.1, hout.2, rfl, rfl⟩ :
      (⟨edgeWest w d.1⟩ : PresentVertex w) ⟶ ⟨edgeEast w d.1⟩))
  apply hnot
  apply boundary_triangle_reachable w hfin j (d.1, !d.2) hpred ⟨hrw, hre⟩
  have hd : kmswInfFaceSucc w hfin (d.1, !d.2) = (e, false) := by
    change (kmswInfRot w hfin).symm (d.1, !(!d.2)) = _
    simp only [Bool.not_not]
    exact Equiv.symm_apply_apply _ _
  rw [hd]
  exact ⟨he.2.1, he.2.2.1⟩

include hfin in
/-- Helper toward Lemma 5.12; not a paper result.
There is at most one west-boundary edge leaving a vertex -/
theorem beta0_westBoundary_outgoing_unique (hb : BoundaryHitWitnesses w)
    (e f : ℕ) (he : MhatWestBoundaryEdge w e) (hf : MhatWestBoundaryEdge w f)
    (hv : edgeWest w e = edgeWest w f) : e = f := by
  have haux (a b : ℕ) (ha : MhatWestBoundaryEdge w a)
      (harc : RotationArc (kmswInfRot w hfin)
        (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
        (a, false) (b, false)) : a = b := by
    obtain ⟨n, hn, hall⟩ := harc
    cases n with
    | zero => exact congrArg Prod.fst hn
    | succ n =>
      have hh := hall 1 (by omega)
      rw [pow_one] at hh
      exact (boundary_forward_not_outgoing w hfin hb a ha hh).elim
  rcases kmswInfRot_outgoing_interval_all w hfin e f hv he.1 hf.1 with h | h
  · exact haux e f he h
  · exact (haux f e hf h).symm

include hfin in
private theorem boundary_is_left_exit (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    ∃ n, w n = 0 ∧ e = act w n ∧
      ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w (act w (n + 1))⟩ := by
  obtain ⟨j, hj, _⟩ := boundary_edge_exterior_triangle w e he
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  have hno := boundary_forward_not_outgoing w hfin hb e he
  have hscan := (beta0_westBoundary_first_scan_dichotomy w hfin hb e he).2
  have hp : EdgePresent w (act w (j.val + 1)) :=
    ⟨j.val + 1, act_lt_nextEdge w le_rfl, kmswStage_active_present w (j.val + 1)⟩
  have hstep : kmswStage w (j.val + 1) = kmswStep (kmswStage w j.val) (w j.val) := rfl
  rcases j.property with h0 | h1
  · cases hl : (kmswStage w j.val).UL.dropLast.reverse with
    | nil =>
      have htri := stageTriangleDartTriple_left_fresh w j h0 hl
      rw [htri] at hc
      simp only [stageTriangleDartList, htri, List.mem_cons, Prod.mk.injEq,
        Bool.false_eq_true, and_false, and_true, List.not_mem_nil, or_false, false_or] at hj
      rcases hj with heq | heq
      · refine ⟨j.val, h0, heq, ?_⟩
        have hs : (kmswInfRot w hfin).symm (e, true) =
            ((kmswStage w j.val).nextEdge, true) := by
          rw [heq]
          exact hc.1
        rw [hs] at hscan
        have ha : act w (j.val + 1) = (kmswStage w j.val).nextEdge := by
          simp [act, hstep, kmswStep, h0, kmswCodeStep, kmswStepOfStep, hl]
        rw [ha]
        exact hscan rfl
      · have hs : kmswInfRot w hfin (e, false) =
            ((kmswStage w j.val).nextEdge, false) := by
          apply (kmswInfRot w hfin).symm.injective
          rw [Equiv.symm_apply_apply, heq]
          exact hc.2.1.symm
        apply False.elim
        apply hno
        rw [hs]
        have ha : act w (j.val + 1) = (kmswStage w j.val).nextEdge := by
          simp [act, hstep, kmswStep, h0, kmswCodeStep, kmswStepOfStep, hl]
        exact ⟨rfl, ha ▸ hp⟩
    | cons f fs =>
      have htri := stageTriangleDartTriple_left_existing w j h0 f fs hl
      rw [htri] at hc
      simp only [stageTriangleDartList, htri, List.mem_cons, Prod.mk.injEq,
        Bool.false_eq_true, and_false, and_true, List.not_mem_nil, or_false] at hj
      rcases hj with heq | heq
      · have hs : kmswInfRot w hfin (e, false) =
            ((kmswStage w j.val).nextEdge, false) := by
          apply (kmswInfRot w hfin).symm.injective
          rw [Equiv.symm_apply_apply, heq]
          exact hc.2.2.1.symm
        apply False.elim
        apply hno
        rw [hs]
        have ha : act w (j.val + 1) = (kmswStage w j.val).nextEdge := by
          simp [act, hstep, kmswStep, h0, kmswCodeStep, kmswStepOfStep, hl]
        exact ⟨rfl, ha ▸ hp⟩
      · refine ⟨j.val, h0, heq, ?_⟩
        have hs : (kmswInfRot w hfin).symm (e, true) =
            ((kmswStage w j.val).nextEdge, true) := by
          rw [heq]
          exact hc.2.1
        rw [hs] at hscan
        have ha : act w (j.val + 1) = (kmswStage w j.val).nextEdge := by
          simp [act, hstep, kmswStep, h0, kmswCodeStep, kmswStepOfStep, hl]
        rw [ha]
        exact hscan rfl
  · have htri := stageTriangleDartTriple_up w j h1
    rw [htri] at hc
    simp only [stageTriangleDartList, htri, List.mem_cons, Prod.mk.injEq,
      Bool.false_eq_true, and_false, and_true, List.not_mem_nil, or_false] at hj
    have hs : kmswInfRot w hfin (e, false) =
        ((kmswStage w j.val).nextEdge, false) := by
      apply (kmswInfRot w hfin).symm.injective
      rw [Equiv.symm_apply_apply, hj]
      exact hc.2.2.1.symm
    apply False.elim
    apply hno
    rw [hs]
    have ha : act w (j.val + 1) = (kmswStage w j.val).nextEdge := by
      simp [act, hstep, kmswStep, h1, kmswCodeStep, kmswStepOfStep]
    exact ⟨rfl, ha ▸ hp⟩

include hfin in
/-- Helper toward Lemma 5.12; not a paper result.
Every west-boundary edge is the old active edge at a source left exit -/
theorem beta0_westBoundary_eq_left_exit (hb : BoundaryHitWitnesses w)
    (h : HasFlowLineHits w) (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    ∃ k, e = act w (PaperProofs.Section5.sourceFlowNL w h k - 1) := by
  obtain ⟨n, _, hen, hnot⟩ := boundary_is_left_exit w hfin hb e he
  have hr : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ := by
    rw [(edge_endpoints_eq w (act_lt_nextEdge w le_rfl)).1, ← hen]
    exact he.2.1
  obtain ⟨k, hk, hn⟩ := (flowLineTimes_iff w h n).mp hr
  have heq : n + 1 = walkNL w h k := by
    by_contra hh
    have hr' := flowLine_phase_reachable w h k (n + 1) (by omega) (by omega)
    rw [(edge_endpoints_eq w (act_lt_nextEdge w le_rfl)).1] at hr'
    exact hnot hr'
  refine ⟨k, ?_⟩
  rw [PaperProofs.Section5.sourceFlowNL_eq_walkNL, ← heq]
  simpa only [Nat.add_sub_cancel] using hen

private theorem boundary_rphase_floor (h : HasFlowLineHits w) (k n : ℕ)
    (hn : walkNR w h k ≤ n) (hlt : n < walkNL w h k) :
    L w (walkNR w h k) ≤ L w n := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have hprev := ih (by omega)
    have hs : L w (n + 1) = L w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
    have hlo : (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
      change (-1 : ℤ) ≤ (w n : ℤ) - 1
      omega
    have hmin := PaperProofs.Section5.sourceFlowNL_level_isLeast w h k
    rw [PaperProofs.Section5.sourceFlowNL_eq_walkNL,
      PaperProofs.Section5.sourceFlowNR_eq_walkNR] at hmin
    have hne : L w (n + 1) ≠ L w (walkNR w h k) - 1 := by
      intro heq
      have hh := hmin.2 ⟨by omega, heq⟩
      omega
    omega

private theorem boundary_left_exits_chain (h : HasFlowLineHits w) (k : ℕ) :
    edgeWest w (act w (walkNL w h (k + 1) - 1)) =
      edgeEast w (act w (walkNL w h k - 1)) := by
  let r := walkNR w h (k + 1)
  let n := walkNL w h (k + 1) - 1
  have hr := (walkNR_succ_spec w h k).1
  have hn := (walkNL_spec w h (k + 1)).1
  have hlevel : L w r = L w n := by
    have hs := congrArg Prod.fst (walkNL_previous_step w h (k + 1))
    have hh := (walkNL_spec w h (k + 1)).2
    dsimp [r, n]
    omega
  have hfloor : ∀ j, r ≤ j → j ≤ n → L w r ≤ L w j := by
    intro j hj hjn
    exact boundary_rphase_floor w h (k + 1) j hj (by dsimp [n] at hjn; omega)
  have heq := kmsw_west_act_eq_of_level w (by dsimp [r, n]; omega) hlevel hfloor
  have hw : edgeWest w (act w n) = edgeWest w (act w r) := by
    have hendsR := (edge_endpoints_eq w (act_lt_nextEdge w
      (show r ≤ n by dsimp [r, n]; omega))).1
    have hendsN := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl n))).1
    exact hendsN.symm.trans (heq.symm.trans hendsR)
  have hcode : w (r - 1) = 2 := walkNR_succ_previous_code w h k
  have htime : r - 1 + 1 = r := by dsimp [r]; omega
  have hstep : kmswStage w r = kmswStepOfStep (kmswStage w (r - 1)) .down := by
    rw [← htime]
    change kmswStep (kmswStage w (r - 1)) (w (r - 1)) = _
    rw [hcode]
    rfl
  have hd : (kmswStage w r).west (act w r) =
      (kmswStage w (r - 1)).east (act w (r - 1)) := by
    rw [act, hstep]
    cases hur : (kmswStage w (r - 1)).UR with
    | nil => simp [kmswStepOfStep, hur, State.addEdge, act]
    | cons e es =>
      have hh := (kmswStage_boundary_chain_invariant w (r - 1)).2.2.2.2.2.1 e es hur
      simp [kmswStepOfStep, hur, hh, act]
  have hb := (hatLPhase_right_boundary w h k).2
  calc
    edgeWest w (act w n) = edgeWest w (act w r) := hw
    _ = (kmswStage w r).west (act w r) :=
      (edge_endpoints_eq w (act_lt_nextEdge w (le_refl r))).1.symm
    _ = (kmswStage w (r - 1)).east (act w (r - 1)) := hd
    _ = (kmswStage w (walkNL w h k - 1)).east
        (act w (walkNL w h k - 1)) := hb
    _ = edgeEast w (act w (walkNL w h k - 1)) :=
      (edge_endpoints_eq w (act_lt_nextEdge w le_rfl)).2

/-- Helper toward Lemma 5.12; not a paper result.
The stream enumerates the source left exits in their source order -/
theorem beta0_westBoundary_stream_eq_left_exit (hb : BoundaryHitWitnesses w)
    (h : HasFlowLineHits w) (k : ℕ) :
    (kmswBeta0Stream w hfin hb k).1 =
      act w (PaperProofs.Section5.sourceFlowNL w h k - 1) := by
  induction k with
  | zero => exact boundary_first_eq_left_exit w hfin hb h
  | succ k ih =>
    apply beta0_westBoundary_outgoing_unique w hfin hb
      _ _ (beta0_westBoundary_stream w hfin hb (k + 1))
      (mhatWestBoundaryEdge_leftExit w h (k + 2) (by omega))
    rw [kmswBeta0Stream_chain, ih,
      PaperProofs.Section5.sourceFlowNL_eq_walkNL,
      PaperProofs.Section5.sourceFlowNL_eq_walkNL]
    exact (boundary_left_exits_chain w h k).symm

/-- Helper toward Lemma 5.12; not a paper result.
Every west-boundary edge is reached from the first edge by finitely many -/
theorem beta0_westBoundary_reached (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    ∃ j, (kmswBeta0Stream w hfin hb j).1 = e := by
  let h := boundary_flow_hits w hb
  obtain ⟨j, hj⟩ := beta0_westBoundary_eq_left_exit w hfin hb h e he
  exact ⟨j, (beta0_westBoundary_stream_eq_left_exit w hfin hb h j).trans hj.symm⟩

/-- Helper toward Lemma 5.12; not a paper result.
The entire west boundary is the forward successor orbit of its first edge -/
theorem beta0_westBoundary_iterate (hb : BoundaryHitWitnesses w)
    (e : ℕ) (he : MhatWestBoundaryEdge w e) :
    ∃ j, ((kmswBeta0Next w hfin hb)^[j] (kmswBeta0First w hfin hb)).1 = e := by
  obtain ⟨j, hj⟩ := beta0_westBoundary_reached w hfin hb e he
  refine ⟨j, ?_⟩
  have hi (n : ℕ) : (kmswBeta0Next w hfin hb)^[n] (kmswBeta0First w hfin hb) =
      kmswBeta0Stream w hfin hb n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl
  rw [hi]
  exact hj

end BoundaryScan

/-- Helper toward Lemma 5.12; not a paper result.
Every present edge has a triangular west face under the coordinate-hit
witnesses. Whether that triangle is outside the reachable submap is separate -/
theorem beta0_present_west_face_isTriangle (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (he : EdgePresent w e) :
    ∃ n t, t ∈ (kmswStage w n).triangles ∧
      ∃ he : e < (kmswStage w n).nextEdge,
        kmswWestSideFaceIsTriangle w n ⟨e, he⟩ t := by
  obtain ⟨j, hj⟩ := boundary_present_west_triangle w hb e he
  obtain ⟨n, t, ht, hbound, hface, _⟩ := boundary_triangle_of_mem w j e hj
  exact ⟨n, t, ht, hbound, hface⟩

end DirectedDistances.KMSW
