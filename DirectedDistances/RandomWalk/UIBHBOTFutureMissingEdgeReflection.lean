module

public import DirectedDistances.RandomWalk.UIBHBOTFutureGeometricEdges
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary
public import DirectedDistances.KMSW.PastFaceSucc
import DirectedDistances.KMSW.KMSWWindowPatchRotation
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.KMSW.RunBoundaryStackSets

/-! They retain the future-code edge ID and its missing status while identifying
its whole-plane geometric image. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5

private theorem startVertex_cofinal (W : ℤ → Fin 3) (t : ℤ) (N : ℕ)
    (hN : t.natAbs ≤ N) (v : ℕ) :
    lemma38StartVertexι W t v = wholePlaneVertexι W N
      (kmswWindowVertexMapInf (shiftedStream W N) (t + (N : ℤ)).toNat v) := by
  by_cases ht : t ≤ 0
  · rw [lemma38StartVertexι, ite_eq_left ht]
    have hc := congrFun (wholePlaneVertexι_trans W t.natAbs N hN) v
    have ha : (t + (N : ℤ)).toNat = N - t.natAbs := by
      have := Int.ofNat_natAbs_of_nonpos ht
      omega
    rw [ha]
    exact hc.symm
  · rw [lemma38StartVertexι, ite_eq_right ht]
    have hc := congrFun (wholePlaneVertexι_trans W 0 N (Nat.zero_le N))
      (kmswWindowVertexMapInf (shiftedStream W 0) t.toNat v)
    rw [← hc]
    change wholePlaneVertexι W N
      (kmswWindowVertexMapInf (shiftedStream W N) (N - 0)
        (kmswWindowVertexMapInf (shiftedStream W 0) t.toNat v)) = _
    rw [Nat.sub_zero, ← shiftedStream_shift W 0 N (Nat.zero_le N),
      Nat.sub_zero, kmswWindowVertexMapInf_comp]
    congr 2
    have := Int.toNat_of_nonneg (show 0 ≤ t by omega)
    omega

private theorem window_activeInitial (w : ℕ → Fin 3) (s n : ℕ) :
    kmswWindowVertexMapInf w s (activeInitial (fun i => w (s + i)) n) =
      activeInitial w (s + n) := by
  have hb := kmswStage_endpoints_lt_nextVertex (fun i => w (s + i)) n
    (act (fun i => w (s + i)) n) (act_lt_nextEdge _ le_rfl)
  have hb' : activeInitial (fun i => w (s + i)) n <
      (kmswStage (fun i => w (s + i)) n).nextVertex := by
    rw [CutConverse.activeInitial_eq]
    exact hb.1
  rw [kmswWindowVertexMapInf_eq_stage w s n _ hb']
  exact kmswWindowPatchVertexMap_activeInitial _ _ s n (fun _ _ => rfl)

private theorem startVertex_level (W : ℤ → Fin 3) (t s : ℤ)
    (he : lemma38StartVertexι W t 0 = lemma38StartVertexι W s 0) :
    (wholePlaneWordIntegral W t).1 = (wholePlaneWordIntegral W s).1 := by
  let N := max t.natAbs s.natAbs
  have ht : t.natAbs ≤ N := Nat.le_max_left _ _
  have hs : s.natAbs ≤ N := Nat.le_max_right _ _
  rw [startVertex_cofinal W t N ht, startVertex_cofinal W s N hs] at he
  have hf (j : ℕ) : kmswWindowVertexMapInf (shiftedStream W N) j 0 =
      activeInitial (shiftedStream W N) j := by
    exact window_activeInitial (shiftedStream W N) j 0
  rw [hf, hf] at he
  have hv := wholePlaneVertexι_injective W N he
  have hL : L (shiftedStream W N) (t + (N : ℤ)).toNat =
      L (shiftedStream W N) (s + (N : ℤ)).toNat := by
    rcases le_total (t + (N : ℤ)).toNat (s + (N : ℤ)).toNat with h | h
    · exact activeInitial_level_eq _ h hv
    · exact (activeInitial_level_eq _ h hv.symm).symm
  have ht0 : ((t + (N : ℤ)).toNat : ℤ) - N = t := by
    have := Int.natCast_natAbs t
    have := Int.toNat_of_nonneg (show 0 ≤ t + (N : ℤ) by omega)
    omega
  have hs0 : ((s + (N : ℤ)).toNat : ℤ) - N = s := by
    have := Int.natCast_natAbs s
    have := Int.toNat_of_nonneg (show 0 ≤ s + (N : ℤ) by omega)
    omega
  have hti := uibhbotStart_L W (-(N : ℤ)) (t + (N : ℤ)).toNat
  have hsi := uibhbotStart_L W (-(N : ℤ)) (s + (N : ℤ)).toNat
  have hstream : lemma38StartStream W (-(N : ℤ)) = shiftedStream W N := by
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  rw [hstream] at hti hsi
  have hargt : -(N : ℤ) + ((t + (N : ℤ)).toNat : ℤ) = t := by omega
  have hargs : -(N : ℤ) + ((s + (N : ℤ)).toNat : ℤ) = s := by omega
  rw [hargt] at hti
  rw [hargs] at hsi
  omega

private theorem present_absoluteActive (W : ℤ → Fin 3) (e : WholePlaneEdge W)
    (he : wholePlaneEdgePresent W e) : ∃ t : ℤ, uibhbotAbsoluteActiveEdge W t = e := by
  obtain ⟨N, f, hf⟩ := wholePlaneEdge_has_run_rep W e
  rw [← hf, wholePlaneEdgePresent_ι] at he
  obtain ⟨M, hNM, hp⟩ := he
  have hg := hp M le_rfl
  obtain ⟨n, hn, _⟩ := existsUnique_actTime _ _ hg
  have hι := congrFun (wholePlaneEdgeι_trans W N M hNM) f
  change wholePlaneEdgeι W M (wholePlaneEdgeTrans W N M hNM f) = _ at hι
  rw [hn] at hι
  have hc := uibhbotStartEdge_active W (-(M : ℤ)) n
  have hs : lemma38StartStream W (-(M : ℤ)) = shiftedStream W M := by
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  rw [hs] at hc
  have hi : lemma38StartEdgeι W (-(M : ℤ)) (act (shiftedStream W M) n) =
      wholePlaneEdgeι W M (act (shiftedStream W M) n) := by
    simp [lemma38StartEdgeι]
  rw [hi] at hc
  exact ⟨-(M : ℤ) + n, hc.symm.trans (hι.trans hf)⟩

private theorem boundaryHit_left_strict_before (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {j : ℤ} (hj : j ≤ -1) :
    ∀ n < boundaryHitTime w h j, j < L w n := by
  have htime : boundaryHitTime w h j = Nat.find (h.leftHit j hj) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : j ≠ 0),
      dite_eq_right (by omega : ¬ 0 < j)]
  have hspec := Nat.find_spec (h.leftHit j hj)
  have hzero : L w 0 = 0 := by simp [L]
  have hstep : ∀ n, L w n - 1 ≤ L w (n + 1) := by
    intro n
    have hL : L w (n + 1) = L w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
    have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
      unfold RandomWalk.lazyTwoDimensionalStep
      omega
    rw [hL]
    omega
  intro n hn
  rw [htime] at hn
  by_contra hnot
  have hle : L w n ≤ j := by omega
  let m := Nat.find (⟨n, hle⟩ : ∃ q, L w q ≤ j)
  have hm : L w m ≤ j := Nat.find_spec (⟨n, hle⟩ : ∃ q, L w q ≤ j)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hle⟩ : ∃ q, L w q ≤ j) hle
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hm
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : j < L w p := by
      have hnot' := Nat.find_min (⟨n, hle⟩ : ∃ q, L w q ≤ j) (by omega : p < m)
      omega
    have hfirst : ¬ L w m = j := by
      have hmfirst : m < Nat.find (h.leftHit j hj) := hmn.trans_lt hn
      exact Nat.find_min (h.leftHit j hj) hmfirst
    rw [hp] at hm
    have hstep' := hstep p
    have hmeq : L w (p + 1) = j := by omega
    exact hfirst (by simpa only [hp] using hmeq)

private theorem futureMissingEdge_boundaryLabel (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {e : ℕ} (he : ¬ EdgePresent w e) :
    ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge w h j := by
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩
  have hd := futureMap_missing_east_external w hR e he
  obtain ⟨j, hj⟩ := (futureMap_limitExternalDart_iff_boundaryDart w h
    (e, true)).mp hd
  have heq : e = boundaryOuterEdge w h j := congrArg Prod.fst hj
  refine ⟨j, ?_, heq⟩
  by_contra hjneg
  have hp := (boundaryOuterEdge_endpoints w h j).2.2.1 (by omega)
  exact he (heq ▸ hp)

private theorem futureBoundaryStart_level_strict (W : ℤ → Fin 3) (k t : ℤ)
    (ht : UIBHBOTBoundaryHit k t W)
    (hpre : ∀ s : ℤ, s < t → k < (wholePlaneWordIntegral W s).1)
    (w : ℕ → Fin 3) (hw : w = lemma38StartStream W t)
    (h : BoundaryHitWitnesses w) {j : ℤ} (hj : j ≤ -1) :
    ∀ s : ℤ, s < t + (boundaryHitTime w h j : ℤ) →
      k + j < (wholePlaneWordIntegral W s).1 := by
  intro s hs
  by_cases hst : s < t
  · have hk := hpre s hst
    omega
  · have hts : t ≤ s := by omega
    let n : ℕ := (s - t).toNat
    have hn : (n : ℤ) = s - t := Int.toNat_of_nonneg (by omega)
    have hnm : n < boundaryHitTime w h j := by
      have := hs
      dsimp [n] at *
      have hn' := Int.toNat_of_nonneg (show 0 ≤ s - t by omega)
      omega
    have hrel := boundaryHit_left_strict_before w h hj n hnm
    have hstart := uibhbotStart_L W t n
    rw [← hw] at hstart
    have htime : t + (n : ℤ) = s := by omega
    rw [htime] at hstart
    rw [ht.1] at hstart
    omega

/-- future-code edge retains its edge ID and lies on the lower-left boundary of the
future copy; the whole-plane map has no directed orientation on that edge. -/
private theorem futureMissingEdge_not_wholePlanePresent
    (W : ℤ → Fin 3) (k : ℤ) (t : ℤ)
    (htime : t = uibhbotBoundaryHitTime k W)
    (ht : UIBHBOTBoundaryHit k t W)
    (hpre : ∀ s : ℤ, s < t → k < (wholePlaneWordIntegral W s).1)
    (w : ℕ → Fin 3) (hw : w = fun i => uibhbotFutureCode k W (i + 1))
    (h : BoundaryHitWitnesses w) {e : ℕ} (he : ¬ EdgePresent w e) :
    ¬ wholePlaneEdgePresent W (uibhbotFutureEdge k W e) := by
  obtain ⟨j, hj, heLabel⟩ := futureMissingEdge_boundaryLabel w h he
  let m := boundaryHitTime w h j
  have hstartStream : w = lemma38StartStream W t := by
    rw [hw, uibhbotFutureCode_stream, htime]
  have hvertex : wholePlaneEdgeWest W (uibhbotFutureEdge k W e) =
      lemma38StartVertexι W (t + (m : ℤ)) 0 := by
    rw [uibhbotFutureEdge_west, heLabel]
    rw [← hw]
    change lemma38StartVertexι W (uibhbotBoundaryHitTime k W)
      (edgeWest w (boundaryOuterEdge w h j)) = _
    rw [← htime, (boundaryOuterEdge_endpoints w h j).1]
    rw [boundaryVertex_left_hit_eq w h hj]
    have hAI : activeInitial w m = activeInitial (lemma38StartStream W t) m :=
      congrArg (fun v : ℕ → Fin 3 => activeInitial v m) hstartStream
    calc
      lemma38StartVertexι W t (activeInitial w m) =
          lemma38StartVertexι W t (activeInitial (lemma38StartStream W t) m) :=
        congrArg (lemma38StartVertexι W t) hAI
      _ = lemma38StartVertexι W (t + (m : ℤ)) 0 :=
        uibhbotStartVertex_activeInitial W t m
  intro hp
  have he' : ¬ EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) e := by
    simpa only [hw] using he
  obtain ⟨r, hr⟩ := present_absoluteActive W (uibhbotFutureEdge k W e) hp
  by_cases hrt : t ≤ r
  · have hnot := uibhbotFutureEdge_missing_not_suffix k W he'
    apply hnot
    have hrt' : uibhbotBoundaryHitTime k W ≤ r := by
      rw [← htime]
      exact hrt
    exact ⟨r, hrt', hr⟩
  · have hwest : wholePlaneEdgeWest W (uibhbotAbsoluteActiveEdge W r) =
        lemma38StartVertexι W r 0 := by
      change wholePlaneEdgeWest W (lemma38StartEdgeι W r 0) = _
      rw [lemma38StartEdgeWest]
      simp [edgeWest, kmswStage, kmswInit]
    have hEq := congrArg (wholePlaneEdgeWest W) hr
    rw [hwest, hvertex] at hEq
    have hlevels := startVertex_level W r (t + (m : ℤ)) hEq
    have hstrict := futureBoundaryStart_level_strict W k t ht hpre w
      hstartStream h (j := j) hj r (by omega)
    have hstartLevel := uibhbotStart_L W t m
    rw [← hstartStream, boundaryHitTime_left_spec w h hj, ht.1] at hstartLevel
    have hend : (wholePlaneWordIntegral W (t + (m : ℤ))).1 = k + j := by
      omega
    have hrlevel : (wholePlaneWordIntegral W r).1 =
        (wholePlaneWordIntegral W (t + (m : ℤ))).1 := hlevels
    omega

 
theorem uibhbotFutureMissingEdgeReflection_ae :
    UIBHBOTFutureMissingEdgeReflectionAlmostSure := by
  filter_upwards [ae_uibhbotBoundaryHit, ae_uibhbotBoundaryHit_strictRecord,
    ae_uibhbotFuture_boundaryHitWitnesses] with W hhit hrecord hwitness k e
  let t := uibhbotBoundaryHitTime k W
  have ht : UIBHBOTBoundaryHit k t W := hhit k
  have hpre : ∀ s : ℤ, s < t → k < (wholePlaneWordIntegral W s).1 :=
    hrecord k
  let w : ℕ → Fin 3 := fun i => uibhbotFutureCode k W (i + 1)
  have hw : w = fun i => uibhbotFutureCode k W (i + 1) := rfl
  intro he
  exact futureMissingEdge_not_wholePlanePresent W k t rfl ht hpre w hw
    (hwitness k) he

private theorem futureDart_triangle_of_not_external (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hd : ¬ limitExternalDart w d) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  have hL : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩
  by_contra htri
  have hb := (kmswRunInfDart_boundary_iff_not_triangle w hL hR d).2 htri
  rcases hb with ⟨e, he, hde⟩ | ⟨e, he, hde⟩
  · have hrange : e ∈ Set.range (fun j : ℕ =>
        kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
      rw [← kmswRunEventuallyLL_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    have hj' : kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1))) = e := by
      simpa using hj
    have hEq : d = futureMapBoundaryDart w h (-((j : ℤ) + 1)) := by
      rw [hde, futureMapBoundaryDart]
      exact congrArg (fun q : ℕ => (q, true))
        ((boundaryOuterEdge_of_negative w h (by omega)).trans hj').symm
    exact hd (hEq ▸ futureMapBoundaryDart_external w h _)
  · have hrange : e ∈ Set.range (fun j : ℕ => kmswRightBoundaryEdge w j) := by
      rw [← kmswRunEventuallyLR_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    by_cases hj0 : j = 0
    · subst j
      have hj' : kmswRightBoundaryEdge w 0 = e := by simpa using hj
      have hEq : d = futureMapBoundaryDart w h 0 := by
        rw [hde, futureMapBoundaryDart_zero, ← hj', kmswRightBoundaryEdge_zero]
        rfl
      exact hd (hEq ▸ futureMapBoundaryDart_external w h 0)
    · have hj' : kmswRightBoundaryEdge w j = e := by simpa using hj
      have hEq : d = futureMapBoundaryDart w h (j : ℤ) := by
        rw [hde, futureMapBoundaryDart]
        have hbd : boundaryOuterEdge w h (j : ℤ) = kmswRightBoundaryEdge w j := by
          simpa using boundaryOuterEdge_of_positive w h (show 0 < (j : ℤ) by omega)
        exact congrArg (fun q : ℕ => (q, true)) (hbd.trans hj').symm
      exact hd (hEq ▸ futureMapBoundaryDart_external w h _)

private theorem futureWindow_faceSucc_of_triangle (v : ℕ → Fin 3) (s : ℕ)
    (hu : KMSWFiniteIncidence (fun i => v (s + i)))
    (hv : KMSWFiniteIncidence v) (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (fun i => v (s + i)),
      d ∈ stageTriangleDartList (fun i => v (s + i)) j) :
    (kmswWindowEdgeMapInf v s
        (kmswInfFaceSucc (fun i => v (s + i)) hu d).1,
      (kmswInfFaceSucc (fun i => v (s + i)) hu d).2) =
      kmswInfFaceSucc v hv (kmswWindowEdgeMapInf v s d.1, d.2) := by
  let u := fun i => v (s + i)
  obtain ⟨j, hdj⟩ := hd
  obtain ⟨a, ha⟩ := kmswInfFaceSucc_eventually_eq_stage u hu d
  obtain ⟨b, hb⟩ := kmswInfFaceSucc_eventually_eq_stage v hv
    (kmswWindowEdgeMapInf v s d.1, d.2)
  let m := max (max a b) (j.val + 1)
  obtain ⟨hedge, hsrc⟩ := ha m (by dsimp only [m]; omega)
  obtain ⟨himage, htgt⟩ := hb (s + m) (by dsimp only [m]; omega)
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, hedge⟩, d.2)
  have hx : (x.1.val, x.2) ∈ stageTriangleDartsVal u m := by
    apply List.mem_flatMap.mpr
    exact ⟨j, (mem_stageTriangleTimes u m j).mpr (by dsimp only [m]; omega), hdj⟩
  have hface := kmswWindowDartMap_faceSucc v s m x hx
  have hmap : kmswWindowDartMap v s m x =
      (⟨kmswWindowEdgeMapInf v s d.1, himage⟩, d.2) := by
    apply Prod.ext
    · apply Fin.ext
      exact (kmswWindowEdgeMapInf_eq_stage v s m d.1 hedge).symm
    · rfl
  rw [hsrc]
  have hout := kmswWindowEdgeMapInf_eq_stage v s m
    ((kmswMap u m).faceSucc x).1.val ((kmswMap u m).faceSucc x).1.isLt
  change (kmswWindowEdgeMapInf v s ((kmswMap u m).faceSucc x).1.val,
    ((kmswMap u m).faceSucc x).2) = _
  rw [hout]
  change ((kmswWindowDartMap v s m ((kmswMap u m).faceSucc x)).1.val,
    (kmswWindowDartMap v s m ((kmswMap u m).faceSucc x)).2) = _
  rw [← hface, hmap]
  exact htgt.symm

private theorem futureWindow_triangle_image (v : ℕ → Fin 3) (s : ℕ)
    (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (fun i => v (s + i)),
      d ∈ stageTriangleDartList (fun i => v (s + i)) j) :
    ∃ j : TriangleCreationTime v,
      (kmswWindowEdgeMapInf v s d.1, d.2) ∈ stageTriangleDartList v j := by
  obtain ⟨j, hdj⟩ := hd
  let m := j.val + 1
  have hedge : d.1 < (kmswStage (fun i => v (s + i)) m).nextEdge :=
    stageTriangleDartList_lt _ m j (by dsimp [m]; omega) d hdj
  have hval : d ∈ stageTriangleDartsVal (fun i => v (s + i)) m := by
    apply List.mem_flatMap.mpr
    exact ⟨j, (mem_stageTriangleTimes _ m j).mpr (by dsimp [m]; omega), hdj⟩
  have himage := kmswWindowPatchData_darts_mem v s m d hval
  have hmap : kmswWindowEdgeMapInf v s d.1 = (kmswWindowPatchData v s m).φ d.1 := by
    rw [kmswWindowEdgeMapInf_eq_stage v s m d.1 hedge]
  rw [hmap.symm] at himage
  obtain ⟨j', _, hmem⟩ := List.mem_flatMap.mp himage
  exact ⟨j', hmem⟩

private theorem futureInteriorFaceSucc_of_triangle (W : ℤ → Fin 3) (t : ℤ)
    (H : WholePlaneRotationHypothesis W)
    (w : ℕ → Fin 3) (hw : w = lemma38StartStream W t)
    (hfin : KMSWFiniteIncidence w) (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j) :
    wholePlaneFaceSucc W H (lemma38StartEdgeι W t d.1, d.2) =
      (lemma38StartEdgeι W t (kmswInfFaceSucc w hfin d).1,
        (kmswInfFaceSucc w hfin d).2) := by
  by_cases ht : t ≤ 0
  · let N := t.natAbs
    have hstream : lemma38StartStream W t = shiftedStream W N := by
      simpa [N] using lemma38StartStream_eq_shifted W t ht
    have htri : ∃ j : TriangleCreationTime (shiftedStream W N),
        d ∈ stageTriangleDartList (shiftedStream W N) j := by
      rw [hw, hstream] at hd
      exact hd
    have hface := wholePlaneFaceSucc_run_of_triangle W H N d htri
    have hsucc : kmswInfFaceSucc w hfin d =
        kmswInfFaceSucc (shiftedStream W N) (H.1 N) d := by
      have hwe : w = shiftedStream W N := hw.trans hstream
      cases hwe
      congr 1
    change wholePlaneFaceSucc W H (wholePlaneDartι W N d) = _ at hface
    have hleft : lemma38StartEdgeι W t d.1 = wholePlaneEdgeι W N d.1 := by
      simp [lemma38StartEdgeι, ht, N]
    rw [hleft]
    change wholePlaneFaceSucc W H (wholePlaneDartι W N d) = _
    rw [hface]
    simp [wholePlaneDartι, lemma38StartEdgeι, ht, N, hsucc]
    rfl
  · have ht' : 0 ≤ t := by omega
    let s := t.toNat
    let v := shiftedStream W 0
    let u : ℕ → Fin 3 := fun i => v (s + i)
    have hstream : lemma38StartStream W t = u := by
      rw [lemma38StartStream_eq_nonnegative W t ht']
      funext i
      change W ((i : ℤ) + (t.toNat : ℤ)) = W ((s + i : ℕ) : ℤ)
      congr 1
      simp only [Nat.cast_add]
      dsimp [s]
      omega
    have hu : KMSWFiniteIncidence u := by
      rw [← hstream, ← hw]
      exact hfin
    have htri : ∃ j : TriangleCreationTime u, d ∈ stageTriangleDartList u j := by
      rw [hw, hstream] at hd
      exact hd
    have himage := futureWindow_triangle_image v s d htri
    have hsucc := futureWindow_faceSucc_of_triangle v s hu (H.1 0) d htri
    have hface := wholePlaneFaceSucc_run_of_triangle W H 0
      (kmswWindowEdgeMapInf v s d.1, d.2) himage
    have hedge : lemma38StartEdgeι W t d.1 =
        wholePlaneEdgeι W 0 (kmswWindowEdgeMapInf v s d.1) := by
      simp [lemma38StartEdgeι, ht, v, s]
    have hwu : w = u := hw.trans hstream
    have hsucc' :
        (kmswWindowEdgeMapInf v s (kmswInfFaceSucc w hfin d).1,
          (kmswInfFaceSucc w hfin d).2) =
          kmswInfFaceSucc v (H.1 0) (kmswWindowEdgeMapInf v s d.1, d.2) := by
      simpa only [hw, hstream] using hsucc
    have hstartSucc : lemma38StartEdgeι W t (kmswInfFaceSucc w hfin d).1 =
        wholePlaneEdgeι W 0 (kmswWindowEdgeMapInf v s (kmswInfFaceSucc w hfin d).1) := by
      simp [lemma38StartEdgeι, ht, v, s]
    rw [hedge, hstartSucc]
    change wholePlaneFaceSucc W H (wholePlaneDartι W 0
      (kmswWindowEdgeMapInf v s d.1, d.2)) = _
    rw [hface]
    change (wholePlaneEdgeι W 0 ((kmswInfFaceSucc v (H.1 0)
      (kmswWindowEdgeMapInf v s d.1, d.2)).1),
      (kmswInfFaceSucc v (H.1 0) (kmswWindowEdgeMapInf v s d.1, d.2)).2) = _
    exact congrArg (fun q : ℕ × Bool => (wholePlaneEdgeι W 0 q.1, q.2)) hsucc'.symm

/-- interior future face successor is identified with its whole-plane geometric image. -/
theorem uibhbotFutureInteriorFaceCompatibility_ae :
    UIBHBOTFutureInteriorFaceCompatibilityAlmostSure := by
  filter_upwards [ae_uibhbotFuture_boundaryHitWitnesses] with W hwitness k H hfin d hd
  let w : ℕ → Fin 3 := fun i => uibhbotFutureCode k W (i + 1)
  have hfin' : KMSWFiniteIncidence w := hfin
  have htri := futureDart_triangle_of_not_external w (hwitness k) d hd
  have hstream : w = lemma38StartStream W (uibhbotBoundaryHitTime k W) := by
    simpa [w] using uibhbotFutureCode_stream k W
  have hresult := futureInteriorFaceSucc_of_triangle W
    (uibhbotBoundaryHitTime k W) H w hstream hfin' d htri
  simpa [w, uibhbotFutureEdge] using hresult

end DirectedDistances.RandomWalk
