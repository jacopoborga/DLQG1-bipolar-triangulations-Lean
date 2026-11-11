module

public import DirectedDistances.KMSW.WholePlaneLeftmostIncoming
public import DirectedDistances.KMSW.WholePlaneRightBoundaryRot
import DirectedDistances.KMSW.KMSWWindowPatchRotation
import DirectedDistances.KMSW.WholePlaneRunBoundaryDegree
import DirectedDistances.KMSW.WholePlaneLLRecordEdges

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open scoped Classical

private theorem left_coordinate_succ_ge (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  have hL : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    omega
  rw [hL]
  omega

private theorem first_hit_eq_of_le (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  classical
  let m := Nat.find (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hma : f m ≤ a := Nat.find_spec (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hn⟩ : ∃ j, f j ≤ a) hn
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hma
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : a < f p := by
      have hnot := Nat.find_min (⟨n, hn⟩ : ∃ j, f j ≤ a) (by omega : p < m)
      omega
    refine ⟨m, hmn, ?_⟩
    rw [hp] at hma ⊢
    have hnext := hstep p
    omega

private theorem first_hit_strict (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) (h : ∃ n, f n = a) :
    ∀ j < Nat.find h, a < f j := by
  intro j hj
  by_contra hnot
  have hjle : f j ≤ a := by omega
  obtain ⟨m, hmj, hma⟩ := first_hit_eq_of_le f hstep hzero ha hjle
  exact (Nat.find_min h (hmj.trans_lt hj)) hma

private theorem boundaryHitTime_left_strict_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k,
      L w (boundaryHitTime w h k) < L w j := by
  have htime : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  have hspec := Nat.find_spec (h.leftHit k hk)
  have hs := first_hit_strict (L w) (left_coordinate_succ_ge w) (by simp [L])
    (by omega : k < 0) (h.leftHit k hk)
  intro j hj
  rw [htime] at hj
  rw [htime, hspec]
  exact hs j hj

private theorem left_record_step (w : ℕ → Fin 3) (n : ℕ)
    (hr : ∀ j < n + 1, L w (n + 1) < L w j) :
    w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = [] := by
  have hs : L w (n + 1) = L w n + ((w n : ℤ) - 1) :=
    Finset.sum_range_succ _ _
  have hn := hr n (by omega)
  have hc : w n = 0 := by
    apply Fin.ext
    have hb := (w n).isLt
    omega
  have hmin : L w n = minL w n := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
    change minL w n = L w j at he
    have hl := hr j (by omega)
    have hb := runningMin_le (L w) n n le_rfl
    change minL w n ≤ L w n at hb
    rw [hc] at hs
    norm_num at hs
    omega
  exact ⟨hc, (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w n).mpr hmin⟩

private theorem rot_face (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageRot w n ((kmswMap w n).faceSucc d) = edgeFlip _ d := by
  exact (stageRot w n).apply_symm_apply _

private theorem ll_created_lt (w : ℕ → Fin 3) (n : ℕ) :
    kmswLLCreatedEdge w n < (kmswStage w n).nextEdge := by
  have hmono := kmswStage_nextEdge_mono w (Nat.zero_le n)
  have hzero : (kmswStage w 0).nextEdge = 1 := rfl
  unfold kmswLLCreatedEdge
  omega

private theorem left_triangle_rot_at_stage (w : ℕ → Fin 3) (n r : ℕ)
    (hnr : n + 1 ≤ r)
    (hr : ∀ j < n + 1, L w (n + 1) < L w j) :
    stageRot w r
      (⟨act w n, (act_lt_nextEdge w (Nat.le_succ n)).trans_le
        (kmswStage_nextEdge_mono w hnr)⟩, false) =
      (⟨kmswLLCreatedEdge w (n + 1),
        (ll_created_lt w (n + 1)).trans_le (kmswStage_nextEdge_mono w hnr)⟩, true) := by
  classical
  obtain ⟨hc, hdrop⟩ := left_record_step w n hr
  let j : TriangleCreationTime w := ⟨n, Or.inl hc⟩
  have hj : j.val < r := by dsimp [j]; omega
  have hface := stageTriangle_isFace w j r hj
  have htriple := stageTriangleDartTriple_left_fresh w j hc hdrop
  have he : kmswLLCreatedEdge w (n + 1) < (kmswStage w r).nextEdge :=
    (ll_created_lt w (n + 1)).trans_le (kmswStage_nextEdge_mono w hnr)
  let ha := (act_lt_nextEdge w (Nat.le_succ n)).trans_le
    (kmswStage_nextEdge_mono w hnr)
  have hthird : stageTriangleDart₃ w r j hj =
      (⟨kmswLLCreatedEdge w (n + 1), he⟩, false) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [stageTriangleDart₃, stageTriangleDartAt]
      rw [htriple]
      simp [j, kmswLLCreatedEdge, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hc, hdrop, State.addEdge]
    · simp [stageTriangleDart₃, stageTriangleDartAt,
        stageTriangleDartTriple, j, hc, hdrop]
  have hfirst : stageTriangleDart₁ w r j hj = (⟨act w n, ha⟩, false) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [stageTriangleDart₁, stageTriangleDartAt]
      rw [htriple]
      simp [j, act]
    · simp [stageTriangleDart₁, stageTriangleDartAt,
        stageTriangleDartTriple, j, hc, hdrop]
  have hcycle : (kmswMap w r).faceSucc
      (stageTriangleDart₃ w r j hj) = stageTriangleDart₁ w r j hj := hface.2.2.1
  have hrot := rot_face w r (stageTriangleDart₃ w r j hj)
  rw [hcycle, hfirst, hthird] at hrot
  simpa [edgeFlip] using hrot

private theorem complete_exists (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (v : ℕ) : ∃ m, kmswVertexComplete w m v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  exact (hB ⟨e, kmsw_edge_allocated_by_self w e, he⟩).trans_lt
    (kmsw_edge_allocated_by_self w B)

private theorem complete_mono (w : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (hc : kmswVertexComplete w n v) : kmswVertexComplete w m v := by
  intro e he
  exact (hc e he).trans_le (kmswStage_nextEdge_mono w hnm)

private theorem activeEdgePresent (w : ℕ → Fin 3) (m : ℕ) :
    EdgePresent w (act w m) := by
  refine ⟨m, act_lt_nextEdge w le_rfl, ?_⟩
  apply (kmswStage_status w m).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)





theorem wholePlaneLeftBoundaryEdge_symm_trans (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N M : ℕ) (hNM : N ≤ M)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ 0) :
    let w := shiftedStream W N
    let m := boundaryHitTime w h (k - 1)
    (kmswInfRot (shiftedStream W M) (H.1 M)).symm
        (wholePlaneDartTrans W N M hNM (kmswLLCreatedEdge w m, true)) =
      wholePlaneDartTrans W N M hNM (act w (m - 1), false) := by
  classical
  dsimp only
  let w := shiftedStream W N
  let wM := shiftedStream W M
  let s := M - N
  let m := boundaryHitTime w h (k - 1)
  let n := m - 1
  have hkm : k - 1 ≤ -1 := by omega
  have hmval : L w m = k - 1 := boundaryHitTime_left_spec w h hkm
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    rw [hm0] at hmval
    simp [L] at hmval
    omega
  have hmn : n + 1 = m := by dsimp [n]; omega
  have hr0 := boundaryHitTime_left_strict_record w h hkm
  have hr : ∀ j < n + 1, L w (n + 1) < L w j := by
    simpa [hmn] using hr0
  let e := kmswLLCreatedEdge w m
  have he : e < (kmswStage w m).nextEdge := by
    exact ll_created_lt w m
  have hu : (fun i => wM (s + i)) = w := shiftedStream_shift W N M hNM
  let u := fun i => wM (s + i)
  have hur : ∀ j < n + 1, L u (n + 1) < L u j := by
    simpa only [u, hu] using hr
  obtain ⟨B, hB⟩ := complete_exists wM (H.1 M)
    (edgeEast wM (wholePlaneEdgeTrans W N M hNM e))
  let r := max B (n + 1)
  have hrB : B ≤ s + r := by dsimp [r]; omega
  have hcomplete := complete_mono wM hrB hB
  have hnr : n + 1 ≤ r := Nat.le_max_right _ _
  have hsourceE' : e < (kmswStage w r).nextEdge := by
    rw [← hmn] at he
    exact he.trans_le (kmswStage_nextEdge_mono w hnr)
  have hsourceE : e < (kmswStage u r).nextEdge := by
    simpa only [u, hu] using hsourceE'
  have hsourceA : act u n < (kmswStage u r).nextEdge :=
    (act_lt_nextEdge u (Nat.le_succ n)).trans_le (kmswStage_nextEdge_mono u hnr)
  let x : StageDart (kmswStage u r).nextEdge := (⟨e, hsourceE⟩, true)
  let a : StageDart (kmswStage u r).nextEdge := (⟨act u n, hsourceA⟩, false)
  have hc := (left_record_step u n hur)
  let j : TriangleCreationTime u := ⟨n, Or.inl hc.1⟩
  have hj : j.val < r := by dsimp [j]; omega
  have htriple := stageTriangleDartTriple_left_fresh u j hc.1 hc.2
  have hfirst : stageTriangleDart₁ u r j hj = (⟨act u n,
      act_lt_nextEdge u (Nat.le_succ n) |>.trans_le
        (kmswStage_nextEdge_mono u hnr)⟩, false) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [stageTriangleDart₁, stageTriangleDartAt]
      rw [htriple]
      simp [j, act]
    · simp [stageTriangleDart₁, stageTriangleDartAt,
        stageTriangleDartTriple, j, hc.1, hc.2]
  have hxtri : (act u n, false) ∈ stageTriangleDartsVal u r := by
    unfold stageTriangleDartsVal
    apply List.mem_flatMap.mpr
    refine ⟨j, (mem_stageTriangleTimes u r j).mpr hj, ?_⟩
    rw [stageTriangleDartList, htriple]
    simp [j, act]
  have hrotSrc := left_triangle_rot_at_stage u n r hnr hur
  have hrotMap := kmswWindowDartMap_rot wM s r a hxtri
  have hmapE : (kmswWindowDartMap wM s r x).1.val =
      wholePlaneEdgeTrans W N M hNM e := by
    change (kmswWindowPatchData wM s r).φ e =
      kmswWindowEdgeMapInf wM s e
    rw [← kmswWindowEdgeMapInf_eq_stage wM s r e hsourceE]
  have hmapA : (kmswWindowDartMap wM s r a).1.val =
      wholePlaneEdgeTrans W N M hNM (act w n) := by
    change (kmswWindowPatchData wM s r).φ (act u n) =
      kmswWindowEdgeMapInf wM s (act w n)
    rw [← kmswWindowEdgeMapInf_eq_stage wM s r (act u n) hsourceA]
    exact congrArg (kmswWindowEdgeMapInf wM s)
      (congrArg (fun q : ℕ → Fin 3 => act q n) hu)
  have hrotTarget : stageRot wM (s + r)
      (kmswWindowDartMap wM s r a) = kmswWindowDartMap wM s r x := by
    have hrotMap' : stageRot wM (s + r) (kmswWindowDartMap wM s r a) =
        kmswWindowDartMap wM s r (stageRot u r a) := by
      simpa only [kmswMap_rot, u] using hrotMap
    have hrotSrc' : stageRot u r a = x := by
      have hEU : kmswLLCreatedEdge u (n + 1) = e := by
        change kmswLLCreatedEdge u (n + 1) = kmswLLCreatedEdge w m
        exact (congrArg (fun q : ℕ → Fin 3 => kmswLLCreatedEdge q (n + 1)) hu).trans
          (congrArg (kmswLLCreatedEdge w) hmn)
      simpa [a, x, hEU] using hrotSrc
    rw [hrotSrc'] at hrotMap'
    exact hrotMap'
  let y : StageDart (kmswStage wM (s + r)).nextEdge :=
    kmswWindowDartMap wM s r x
  have hybase : stageEndpoint (kmswStage wM (s + r)) y =
      edgeEast wM (wholePlaneEdgeTrans W N M hNM e) := by
    change (kmswStage wM (s + r)).east
      (kmswWindowDartMap wM s r x).1.val = _
    calc
      (kmswStage wM (s + r)).east (kmswWindowDartMap wM s r x).1.val =
          edgeEast wM (kmswWindowDartMap wM s r x).1.val :=
        (edge_endpoints_eq wM y.1.isLt).2
      _ = edgeEast wM (wholePlaneEdgeTrans W N M hNM e) :=
        congrArg (edgeEast wM) hmapE
  have hycomplete : kmswVertexComplete wM (s + r) (stageEndpoint (kmswStage wM (s+r)) y) := by
    rw [hybase]
    exact hcomplete
  have hInf := kmswInfRot_symm_eq_stage wM (H.1 M) (s + r) y hycomplete
  have hInv : (stageRot wM (s + r)).symm y =
      kmswWindowDartMap wM s r a := by
    apply (stageRot wM (s + r)).injective
    rw [Equiv.apply_symm_apply]
    exact hrotTarget.symm
  rw [hInv] at hInf
  change (kmswInfRot wM (H.1 M)).symm
      ((kmswWindowDartMap wM s r x).1.val,
        (kmswWindowDartMap wM s r x).2) =
    ((kmswWindowDartMap wM s r a).1.val,
      (kmswWindowDartMap wM s r a).2) at hInf
  rw [hmapE, hmapA] at hInf
  simpa [w, wM, m, n, wholePlaneDartTrans, kmswWindowDartMap, x, a] using hInf





theorem wholePlaneLeftBoundaryEdge_symm_rotation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ 0) :
    (wholePlaneRotation W H).symm
        (wholePlaneDartι W N
          (kmswLLCreatedEdge (shiftedStream W N)
            (boundaryHitTime (shiftedStream W N) h (k - 1)), true)) =
      wholePlaneDartι W N
        (act (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (k - 1) - 1), false) := by
  let w := shiftedStream W N
  let m := boundaryHitTime w h (k - 1)
  let d := (kmswLLCreatedEdge w m, true)
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N d
  have hcross : (kmswInfRot (shiftedStream W M) (H.1 M)).symm
      (wholePlaneDartTrans W N M hNM d) =
        wholePlaneDartTrans W N M hNM (act w (m - 1), false) :=
    wholePlaneLeftBoundaryEdge_symm_trans W H N M hNM h k hk
  have hstep : (wholePlaneRotation W H).symm (wholePlaneDartι W N d) =
      wholePlaneDartι W M
        ((kmswInfRot (shiftedStream W M) (H.1 M)).symm
          (wholePlaneDartTrans W N M hNM d)) := by
    simpa only [pow_one, wholePlaneDartι] using hpow 1
  exact hstep.trans ((congrArg (wholePlaneDartι W M) hcross).trans
    (congrFun (wholePlaneDartι_trans W N M hNM) (act w (m - 1), false)))





theorem wholePlaneLeftBoundaryEdge_leftmostIncoming (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ 0)
    (hLL : wholePlaneEdgePresent W
      (wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (k - 1))))) :
    wholePlaneLeftmostIncomingAt W H
      (wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k))
      (wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (k - 1)))) ∧
    wholePlaneEdgeWest W
      (wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (k - 1)))) =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h (k - 1)) := by
  let w := shiftedStream W N
  let m := boundaryHitTime w h (k - 1)
  let e := kmswLLCreatedEdge w m
  let n := m - 1
  have hend := wholePlaneLeftBoundaryEdge_endpoints W N h k hk
  have hstep := wholePlaneLeftBoundaryEdge_symm_rotation W H N h k hk
  have hactive : wholePlaneEdgePresent W (wholePlaneEdgeι W N (act w n)) :=
    wholePlaneEdgePresent_ι_of_run_present W N (act w n) (activeEdgePresent w n)
  constructor
  · unfold wholePlaneLeftmostIncomingAt
    refine ⟨hLL, ?_, ⟨1, by omega, ?_, ?_, ?_⟩⟩
    · change wholePlaneEdgeEast W (wholePlaneEdgeι W N e) = _
      rw [wholePlaneEdgeEast_ι]
      exact congrArg (wholePlaneVertexι W N) hend.1
    · simpa only [pow_one, wholePlaneDartι] using congrArg Prod.snd hstep
    · have hp : wholePlaneEdgePresent W
          ((wholePlaneRotation W H).symm (wholePlaneDartι W N (e, true))).1 := by
        rw [hstep]
        exact hactive
      simpa only [pow_one, wholePlaneDartι] using hp
    · intro j hj hj1
      omega
  · change wholePlaneEdgeWest W (wholePlaneEdgeι W N e) = _
    rw [wholePlaneEdgeWest_ι]
    exact congrArg (wholePlaneVertexι W N) hend.2





theorem wholePlaneLeftBoundary_leftmost_chain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (k - 1))))) :
    ∃ (v : ℕ → WholePlaneVertex W) (e : ℕ → WholePlaneEdge W),
      v 0 = wholePlaneVertexι W N 0 ∧
      (∀ j : ℕ, e j = wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (-(j : ℤ) - 1)))) ∧
      ∀ j : ℕ, wholePlaneLeftmostIncomingAt W H (v j) (e j) ∧
        wholePlaneEdgeWest W (e j) = v (j + 1) := by
  let w := shiftedStream W N
  let v : ℕ → WholePlaneVertex W := fun j =>
    wholePlaneVertexι W N (boundaryVertex w h (-(j : ℤ)))
  let e : ℕ → WholePlaneEdge W := fun j =>
    wholePlaneEdgeι W N
      (kmswLLCreatedEdge w (boundaryHitTime w h (-(j : ℤ) - 1)))
  refine ⟨v, e, ?_, ?_, ?_⟩
  · change wholePlaneVertexι W N (boundaryVertex w h (-(0 : ℤ))) = _
    simp only [Int.neg_zero, boundaryVertex_zero]
  · intro j
    rfl
  · intro j
    have hleft := wholePlaneLeftBoundaryEdge_leftmostIncoming W H N h
      (-(j : ℤ)) (by omega) (hLL (-(j : ℤ)) (by omega))
    refine ⟨hleft.1, ?_⟩
    rw [hleft.2]
    apply congrArg (wholePlaneVertexι W N)
    apply congrArg (boundaryVertex w h)
    push_cast
    omega





theorem wholePlaneIID_ae_leftBoundary_leftmost_chain :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W, ∀ N : ℕ,
        ∃ h : BoundaryHitWitnesses (shiftedStream W N),
          (∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
            (wholePlaneEdgeι W N
              (kmswLLCreatedEdge (shiftedStream W N)
                (boundaryHitTime (shiftedStream W N) h (k - 1))))) ∧
          ∃ (v : ℕ → WholePlaneVertex W) (e : ℕ → WholePlaneEdge W),
            v 0 = wholePlaneVertexι W N 0 ∧
            (∀ j : ℕ, e j = wholePlaneEdgeι W N
              (kmswLLCreatedEdge (shiftedStream W N)
                (boundaryHitTime (shiftedStream W N) h (-(j : ℤ) - 1)))) ∧
            ∀ j : ℕ, wholePlaneLeftmostIncomingAt W H (v j) (e j) ∧
              wholePlaneEdgeWest W (e j) = v (j + 1) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis,
    wholePlaneIID_ae_runBoundaryDegree, wholePlaneIID_ae_LL_record_edges]
    with W H hdegree hrecords
  refine ⟨H, fun N => ?_⟩
  obtain ⟨h, _⟩ := hdegree N
  refine ⟨h, ?_⟩
  have hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (k - 1)))) := by
    intro k hk
    let w := shiftedStream W N
    let m := boundaryHitTime w h (k - 1)
    have hkm : k - 1 ≤ -1 := by omega
    have hmval : L w m = k - 1 := boundaryHitTime_left_spec w h hkm
    have hmpos : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      rw [hm0] at hmval
      simp [L] at hmval
      omega
    have hr := boundaryHitTime_left_strict_record w h hkm
    exact (hrecords N m hmpos hr).1
  exact ⟨hLL, wholePlaneLeftBoundary_leftmost_chain W H N h hLL⟩

end DirectedDistances.KMSW
