module

public import DirectedDistances.KMSW.WholePlaneRightBoundaryChain
public import DirectedDistances.KMSW.WholePlaneLeftBoundaryPresent
import DirectedDistances.KMSW.KMSWWindowPatchRotation

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW






@[expose] def wholePlaneLeftmostIncomingAt (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) : Prop :=
  wholePlaneEdgePresent W e ∧ wholePlaneEdgeEast W e = v ∧
    ∃ k : ℕ, 0 < k ∧
      (((wholePlaneRotation W H).symm ^ k) (e, true)).2 = false ∧
      wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ k) (e, true)).1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        ¬ wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ j) (e, true)).1

private theorem left_record_step (w : ℕ → Fin 3) (n : ℕ)
    (hr : ∀ j < n + 1, L w (n + 1) < L w j) :
    w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = [] := by
  have hs : L w (n + 1) = L w n + ((w n : ℤ) - 1) := Finset.sum_range_succ _ _
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





theorem kmswStage_rot_activePred_LL (w : ℕ → Fin 3) (n : ℕ)
    (hr : ∀ j < n + 1, L w (n + 1) < L w j) :
    let a := (⟨act w n, act_lt_nextEdge w (Nat.le_succ n)⟩, false)
    (stageRot w (n + 1) a).1.val = kmswLLCreatedEdge w (n + 1) ∧
      (stageRot w (n + 1) a).2 = true := by
  classical
  obtain ⟨hc, hdrop⟩ := left_record_step w n hr
  let j : TriangleCreationTime w := ⟨n, Or.inl hc⟩
  have hj : j.val < n + 1 := by dsimp [j]; omega
  have hface := stageTriangle_isFace w j (n + 1) hj
  have htriple := stageTriangleDartTriple_left_fresh w j hc hdrop
  have he : kmswLLCreatedEdge w (n + 1) < (kmswStage w (n + 1)).nextEdge := by
    simp [kmswLLCreatedEdge, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, hc, hdrop, State.addEdge]
  have hthird : stageTriangleDart₃ w (n + 1) j hj =
      (⟨kmswLLCreatedEdge w (n + 1), he⟩, false) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [stageTriangleDart₃, stageTriangleDartAt]
      rw [htriple]
      simp [j, kmswLLCreatedEdge, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hc, hdrop, State.addEdge]
    · simp [stageTriangleDart₃, stageTriangleDartAt,
        stageTriangleDartTriple, j, hc, hdrop]
  have hfirst : stageTriangleDart₁ w (n + 1) j hj =
      (⟨act w n, act_lt_nextEdge w (Nat.le_succ n)⟩, false) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [stageTriangleDart₁, stageTriangleDartAt]
      rw [htriple]
      simp [j, act]
    · simp [stageTriangleDart₁, stageTriangleDartAt,
        stageTriangleDartTriple, j, hc, hdrop]
  have hcycle : (kmswMap w (n + 1)).faceSucc
      (stageTriangleDart₃ w (n + 1) j hj) =
      stageTriangleDart₁ w (n + 1) j hj := hface.2.2.1
  have hrot := rot_face w (n + 1) (stageTriangleDart₃ w (n + 1) j hj)
  rw [hcycle, hfirst, hthird] at hrot
  have hpair : stageRot w (n + 1)
      (⟨act w n, act_lt_nextEdge w (Nat.le_succ n)⟩, false) =
      (⟨kmswLLCreatedEdge w (n + 1), he⟩, true) := by
    simpa [edgeFlip] using hrot
  exact ⟨congrArg (fun d : StageDart _ => d.1.val) hpair,
    congrArg (fun d : StageDart _ => d.2) hpair⟩

private theorem ll_created_lt (w : ℕ → Fin 3) (n : ℕ) :
    kmswLLCreatedEdge w n < (kmswStage w n).nextEdge := by
  have hmono := kmswStage_nextEdge_mono w (Nat.zero_le n)
  have hzero : (kmswStage w 0).nextEdge = 1 := rfl
  unfold kmswLLCreatedEdge
  omega

private theorem left_triangle_rot_at_stage (w : ℕ → Fin 3) (n m : ℕ)
    (hnm : n + 1 ≤ m)
    (hr : ∀ j < n + 1, L w (n + 1) < L w j) :
    (stageRot w m (⟨act w n,
      (act_lt_nextEdge w (Nat.le_succ n)).trans_le
        (kmswStage_nextEdge_mono w hnm)⟩, false)).1.val =
        kmswLLCreatedEdge w (n + 1) ∧
      (stageRot w m (⟨act w n,
        (act_lt_nextEdge w (Nat.le_succ n)).trans_le
          (kmswStage_nextEdge_mono w hnm)⟩, false)).2 = true := by
  classical
  obtain ⟨hc, hdrop⟩ := left_record_step w n hr
  let j : TriangleCreationTime w := ⟨n, Or.inl hc⟩
  have hj : j.val < m := by dsimp [j]; omega
  have hface := stageTriangle_isFace w j m hj
  have htriple := stageTriangleDartTriple_left_fresh w j hc hdrop
  have he : kmswLLCreatedEdge w (n + 1) < (kmswStage w m).nextEdge :=
    (ll_created_lt w (n + 1)).trans_le (kmswStage_nextEdge_mono w hnm)
  let ha := (act_lt_nextEdge w (Nat.le_succ n)).trans_le
    (kmswStage_nextEdge_mono w hnm)
  have hthird : stageTriangleDart₃ w m j hj =
      (⟨kmswLLCreatedEdge w (n + 1), he⟩, false) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [stageTriangleDart₃, stageTriangleDartAt]
      rw [htriple]
      simp [j, kmswLLCreatedEdge, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hc, hdrop, State.addEdge]
    · simp [stageTriangleDart₃, stageTriangleDartAt,
        stageTriangleDartTriple, j, hc, hdrop]
  have hfirst : stageTriangleDart₁ w m j hj = (⟨act w n, ha⟩, false) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [stageTriangleDart₁, stageTriangleDartAt]
      rw [htriple]
      simp [j, act]
    · simp [stageTriangleDart₁, stageTriangleDartAt,
        stageTriangleDartTriple, j, hc, hdrop]
  have hcycle : (kmswMap w m).faceSucc (stageTriangleDart₃ w m j hj) =
      stageTriangleDart₁ w m j hj := hface.2.2.1
  have hrot := rot_face w m (stageTriangleDart₃ w m j hj)
  rw [hcycle, hfirst, hthird] at hrot
  have hpair : stageRot w m (⟨act w n, ha⟩, false) =
      (⟨kmswLLCreatedEdge w (n + 1), he⟩, true) := by
    simpa [edgeFlip] using hrot
  exact ⟨congrArg (fun d : StageDart _ => d.1.val) hpair,
    congrArg (fun d : StageDart _ => d.2) hpair⟩





theorem wholePlaneLeftBoundaryEdge_endpoints (W : ℤ → Fin 3) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ 0) :
    let w := shiftedStream W N
    let e := kmswLLCreatedEdge w (boundaryHitTime w h (k - 1))
    edgeEast w e = boundaryVertex w h k ∧
      edgeWest w e = boundaryVertex w h (k - 1) := by
  dsimp only
  have hmiss := boundaryVertex_left_missing_edge (shiftedStream W N) h
    (k := k - 1) (by omega)
  have he := ll_created_lt (shiftedStream W N) (boundaryHitTime (shiftedStream W N) h (k - 1))
  obtain ⟨hw, heast⟩ := edge_endpoints_eq (shiftedStream W N) he
  constructor
  · calc
      edgeEast (shiftedStream W N) _ =
          (kmswStage (shiftedStream W N)
            (boundaryHitTime (shiftedStream W N) h (k - 1))).east _ := heast.symm
      _ = boundaryVertex (shiftedStream W N) h ((k - 1) + 1) := hmiss.2.1
      _ = boundaryVertex (shiftedStream W N) h k := by
        exact congrArg (boundaryVertex (shiftedStream W N) h) (by omega)
  · calc
      edgeWest (shiftedStream W N) _ =
          (kmswStage (shiftedStream W N)
            (boundaryHitTime (shiftedStream W N) h (k - 1))).west _ := hw.symm
      _ = boundaryVertex (shiftedStream W N) h (k - 1) := hmiss.1





theorem kmswStage_activePred_west_eq_LL_east (w : ℕ → Fin 3) (n : ℕ)
    (hr : ∀ j < n + 1, L w (n + 1) < L w j) :
    edgeWest w (act w n) = edgeEast w (kmswLLCreatedEdge w (n + 1)) := by
  obtain ⟨hc, hdrop⟩ := left_record_step w n hr
  have he := ll_created_lt w (n + 1)
  have ha := (act_lt_nextEdge w (Nat.le_succ n))
  have ha0 : (kmswStage w n).active < (kmswStage w n).nextEdge :=
    act_lt_nextEdge w (le_rfl)
  have hA0 : (kmswStage w n).active ≠ (kmswStage w n).nextEdge := by omega
  have hA1 : (kmswStage w n).active ≠ (kmswStage w n).nextEdge + 1 := by omega
  rw [← (edge_endpoints_eq w ha).1, ← (edge_endpoints_eq w he).2]
  simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
    kmswLLCreatedEdge, act, hc, hdrop, hA0, hA1, State.addEdge]

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






theorem kmswInfRot_symm_activePred_LL (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N n : ℕ)
    (hr : ∀ j < n + 1, L (shiftedStream W N) (n + 1) <
      L (shiftedStream W N) j) :
    (kmswInfRot (shiftedStream W N) (H.1 N)).symm
      (kmswLLCreatedEdge (shiftedStream W N) (n + 1), true) =
        (act (shiftedStream W N) n, false) := by
  let w := shiftedStream W N
  let e := kmswLLCreatedEdge w (n + 1)
  let v := edgeEast w e
  obtain ⟨B, hB⟩ := complete_exists w (H.1 N) v
  let m := max B (n + 1)
  have hBm : B ≤ m := Nat.le_max_left _ _
  have hnm : n + 1 ≤ m := Nat.le_max_right _ _
  have hc := complete_mono w hBm hB
  have he : e < (kmswStage w m).nextEdge :=
    (ll_created_lt w (n + 1)).trans_le (kmswStage_nextEdge_mono w hnm)
  have ha : act w n < (kmswStage w m).nextEdge :=
    (act_lt_nextEdge w (Nat.le_succ n)).trans_le
      (kmswStage_nextEdge_mono w hnm)
  let x : StageDart (kmswStage w m).nextEdge := (⟨e, he⟩, true)
  have hrot := left_triangle_rot_at_stage w n m hnm hr
  have hrot' : stageRot w m (⟨act w n, ha⟩, false) = x := by
    apply Prod.ext
    · apply Fin.ext
      exact hrot.1
    · exact hrot.2
  have hinv : (stageRot w m).symm x = (⟨act w n, ha⟩, false) := by
    have hh := congrArg (stageRot w m).symm hrot'
    simpa only [Equiv.symm_apply_apply] using hh.symm
  have hcomplete : kmswVertexComplete w m (stageEndpoint (kmswStage w m) x) := by
    change kmswVertexComplete w m ((kmswStage w m).east e)
    rw [(edge_endpoints_eq w he).2]
    exact hc
  have hInf := kmswInfRot_symm_eq_stage w (H.1 N) m x hcomplete
  rw [hinv] at hInf
  simpa [x, e, w] using hInf

end DirectedDistances.KMSW
