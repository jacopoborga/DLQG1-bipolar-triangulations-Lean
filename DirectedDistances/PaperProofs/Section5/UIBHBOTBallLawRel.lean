module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLaw
public import DirectedDistances.KMSW.UIBHBOTRootRecord
import DirectedDistances.RandomWalk.ExcursionBlockUniformTail
import DirectedDistances.KMSW.KMSWWholePlaneFaces
import DirectedDistances.KMSW.MeasurableCutEvents
import DirectedDistances.KMSW.StageMapCongr
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Relaxed rooted UIBHBOT captures toward Proposition 5.16 (prop-disk-bs-conv).
The relaxed event is defined in
`DirectedDistances/KMSW/KMSWWindowCaptureEventRel.lean:38`.
Its almost-sure existence is supplied by
`DirectedDistances/KMSW/UIBHBOTAlmostSure.lean:56`. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory

private theorem record_west_active (u : ℕ → Fin 3) (k : ℕ)
    (hrec : ∀ j ≤ k, L u (k + 1) < L u j) :
    (kmswStage u (k + 1)).west (kmswLLCreatedEdge u (k + 1)) =
      activeInitial u (k + 1) := by
  have hs : L u (k + 1) = L u k + (lazyTwoDimensionalStep (u k)).1 :=
    Finset.sum_range_succ _ _
  have hl := hrec k le_rfl
  have hc : u k = 0 := by
    change L u (k + 1) = L u k + ((u k : ℤ) - 1) at hs
    apply Fin.ext
    have := (u k).isLt
    omega
  rw [hc, lazyTwoDimensionalStep_zero] at hs
  have hmin : minL u k = L u k := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L u) k
    have hjrec := hrec j hj
    have hle := runningMin_le (L u) k k le_rfl
    change minL u k = L u j at he
    change minL u k ≤ L u k at hle
    dsimp at hs
    omega
  have hlen := kmswStage_UL_length u k
  have hlen' : (kmswStage u k).UL.length = 1 := by omega
  have hempty : (kmswStage u k).UL.dropLast = [] := by
    apply List.length_eq_zero_iff.mp
    rw [List.length_dropLast, hlen']
  have hdrop : (kmswStage u k).UL.dropLast.reverse = [] := by
    rw [hempty]
    rfl
  rw [CutConverse.activeInitial_eq]
  simp [kmswStage, kmswLLCreatedEdge, kmswStep, kmswCodeStep, hc,
    kmswStepOfStep, hdrop, State.addEdge, act]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The strict record at zero supplies a missing root dart in every large enough stage,
with the active initial vertex as its first endpoint. -/
theorem uibhbotRelaxedCapture_rootDart_exists (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (N m : ℕ)
    (hN : 1 ≤ N) (hNm : N ≤ m) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    let c := activeInitial (shiftedStream W N) N
    wholePlaneVertexι W N c = uibhbotRootFirstVertex W ∧
      ∃ d : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
        stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c ∧
        wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W ∧
        (kmswStageDirectedMap (shiftedStream W N) m).missing d := by
  classical
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  let u := shiftedStream W N
  let e := kmswLLCreatedEdge u N
  have hrec : ∀ j < N, L u N < L u j := uibhbotCode_strictRecord w hw N hN
  have hll : e ∈ (kmswStage u m).LL := by
    rw [kmswStage_LL_eq]
    apply List.mem_map.mpr
    refine ⟨N, ?_, rfl⟩
    apply List.mem_reverse.mpr
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
      decide_eq_true ⟨by omega, hrec⟩⟩
  have he : e < (kmswStage u m).nextEdge :=
    stageRun_edge_bound u m e (Or.inl (Or.inr hll))
  have heN : e < (kmswStage u N).nextEdge := by
    unfold e kmswLLCreatedEdge
    have hmono := kmswStage_nextEdge_mono u (Nat.zero_le N)
    change 1 ≤ (kmswStage u N).nextEdge at hmono
    omega
  have hwest : (kmswStage u m).west e = activeInitial u N := by
    rw [(kmswStage_endpoints_stable u hNm heN).1]
    rcases N with _ | k
    · omega
    · exact record_west_active u k (fun j hj => hrec j (by omega))
  have hroot : wholePlaneEdgeι W N e = uibhbotRootEdge W :=
    (uibhbotRootEdge_eq_window_of_stopped w hw N hN).symm
  have hcenter : wholePlaneVertexι W N (activeInitial u N) =
      uibhbotRootFirstVertex W := by
    rw [← hwest, (edge_endpoints_eq u he).1]
    exact congrArg (wholePlaneEdgeWest W) hroot
  refine ⟨hcenter, (⟨e, he⟩, true), ?_, hroot, ?_⟩
  · exact hwest
  · change (kmswStage u m).present e = false
    exact ((kmswStage_status u m).1 e he).mpr (Or.inr hll)






theorem uibhbotWordFamilyLaw_ae_relaxedRootCapture :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k), ∀ r : ℕ,
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ∃ N m c,
          kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c ∧
          wholePlaneVertexι W N c = uibhbotRootFirstVertex W ∧
          ∃ d : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
            stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c ∧
            wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W ∧
            (kmswStageDirectedMap (shiftedStream W N) m).missing d := by
  filter_upwards [uibhbotWordFamilyLaw_ae_eventualWholePlaneBall] with w hevent
  obtain ⟨hw, hball⟩ := hevent
  refine ⟨hw, ?_⟩
  intro r
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨N₀, hN₀⟩ := hball (r + 1)
  let N := max N₀ 1
  have hN : 1 ≤ N := Nat.le_max_right _ _
  refine ⟨N, 2 * N, activeInitial (shiftedStream W N) N,
    (hN₀ N (Nat.le_max_left _ _)).1, ?_⟩
  exact uibhbotRelaxedCapture_rootDart_exists w hw N (2 * N) hN (by omega)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Almost surely the rooted relaxed captures can be chosen with a pre-window
prefix floor, including the seam endpoint, and global left-seam minimum certificates.
These are conclusions proved from the eventual barrier, not added assumptions. -/
theorem uibhbotWordFamilyLaw_ae_relaxedRootCapture_certified :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k), ∀ r : ℕ,
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ∃ N m c,
          kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c ∧
          (∀ M, N ≤ M →
            ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
              minL (shiftedStream W M) (M - N + k) =
                L (shiftedStream W M) (M - N + k) ∧
              ∀ j ≤ M - N,
                L (shiftedStream W M) (M - N + k) ≤ L (shiftedStream W M) j) ∧
          wholePlaneVertexι W N c = uibhbotRootFirstVertex W ∧
          ∃ d : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
            stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c ∧
            wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W ∧
            (kmswStageDirectedMap (shiftedStream W N) m).missing d := by
  filter_upwards [uibhbotWordFamilyLaw_ae_eventualWholePlaneBall,
    uibhbotWordFamilyLaw_ae_hP2, ae_uibhbotConcatWalk_snd_unbounded_below]
    with w hball hP2 hP1
  obtain ⟨hw, hball⟩ := hball
  obtain ⟨hw', hP2⟩ := hP2
  have hproof : hw' = hw := Subsingleton.elim _ _
  subst hw'
  refine ⟨hw, ?_⟩
  intro r
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨A, hA⟩ := hball (r + 1)
  obtain ⟨B, hB⟩ := uibhbotCodeWord_eventualLeftSeamBarrier w hw hP1 hP2 (r + 1)
  let N := max (max A B) 1
  have hAN : A ≤ N := (Nat.le_max_left A B).trans (Nat.le_max_left _ _)
  have hBN : B ≤ N := (Nat.le_max_right A B).trans (Nat.le_max_left _ _)
  have hN : 1 ≤ N := Nat.le_max_right _ _
  have hev := hA N hAN
  refine ⟨N, 2 * N, activeInitial (shiftedStream W N) N, hev.1, ?_, ?_⟩
  · intro M hNM k hk
    have hg := uibhbotCodeWord_minL_eq_of_leftSeamBarrier w hw N k
      (hev.2.1 k hk) (hB N hBN k hk) M hNM
    refine ⟨hg, ?_⟩
    intro j hj
    have hle := runningMin_le (L (shiftedStream W M)) (M - N + k) j (by omega)
    change minL (shiftedStream W M) (M - N + k) ≤ _ at hle
    rw [hg] at hle
    exact hle
  · exact uibhbotRelaxedCapture_rootDart_exists w hw N (2 * N) hN (by omega)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The missing-root induced framed ball constructed solely from finite local data. -/
@[expose] noncomputable def uibhbotInducedLocalFramedBallRel
    {D : Type} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hp : M.toCombinatorialMap.IsPlanar)
    (hc : (inducedCombinatorialMap M.toCombinatorialMap S hflip).IsConnected)
    (root : S) (hm : M.missing root.1) : FramedBall := by
  classical
  have hex : ∃ o : D, o ∈ S ∧ M.IsOuter o := by
    rcases M.missing_outer root.1 hm with ho | ho
    · exact ⟨root.1, root.2, ho⟩
    · exact ⟨M.edgeInv root.1, hflip root.1 root.2, ho⟩
  let o := Classical.choose hex
  have hoMem : o ∈ S := (Classical.choose_spec hex).1
  have hoOuter : M.IsOuter o := (Classical.choose_spec hex).2
  let outer : S := ⟨o, hoMem⟩
  have houter : ∀ e (he : e ∈ S), M.IsOuter e →
      CombinatorialMap.IsOuter
        (inducedCombinatorialMap M.toCombinatorialMap S hflip) outer ⟨e, he⟩ := by
    intro e he heouter
    apply inducedCombinatorialMap_face_sameCycle_of_connected_planar
    · exact hp
    · exact hc
    · exact hoOuter.symm.trans heouter
  exact inducedFramedBallOfMissingRoot M S hflip outer houter root hm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The local topology framed ball of a relaxed capture, with induced darts and first-return
rotation, inherited tags, ordered missing root, and surviving outer-face mark.
The construction uses no strict freshness assumption. -/
@[expose] noncomputable def uibhbotRelaxedCapturedStageFramedBall
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (_hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (_hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hcenterDart : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (_hrootEdge : wholePlaneEdgeι W N d.1.1 = uibhbotRootEdge W)
    (hmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    FramedBall := by
  classical
  let w := shiftedStream W N
  let s := kmswStage w m
  let M := kmswStageDirectedMap w m
  let center := stageEndpoint s (edgeFlip s.nextEdge d)
  have hcenterDart' : center = c := by
    simpa [center, s, w] using hcenterDart
  let S := kmswStageBallDarts (fun _ _ => True) s r center
  have hflip : ∀ e, e ∈ S → M.toCombinatorialMap.edgeInv e ∈ S := by
    intro e he
    change edgeFlip s.nextEdge e ∈ S
    exact (kmswStageBallDarts_edgeFlip (fun _ _ => True) s r center e).mp he
  have hroot_mem : d ∈ S := by
    exact kmswStageBallRootEdge_mem w m r d hr |>.1
  have hroot_flip_mem : edgeFlip s.nextEdge d ∈ S := by
    exact kmswStageBallRootEdge_mem w m r d hr |>.2
  have hmissing' : M.missing d := by
    simpa [M, w, kmswStageDirectedMap] using hmissing
  exact uibhbotInducedLocalFramedBallRel M S hflip (kmswMap_isPlanar w m)
    (kmswStageBallCombinatorialMap_rooted_isConnected w m r d hr)
    ⟨d, hroot_mem⟩ hmissing'

/-- The frame's first dart is the incidence at the captured center
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem uibhbotRelaxedCapturedStageFramedBall_rootDart
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hcenterDart : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hrootEdge : wholePlaneEdgeι W N d.1.1 = uibhbotRootEdge W)
    (hmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    (uibhbotRelaxedCapturedStageFramedBall W r hr N m c hevent hcenter d
      hcenterDart hrootEdge hmissing).rootDart.1 =
      edgeFlip (kmswStage (shiftedStream W N) m).nextEdge d := by
  rfl

/-- The captured frame edge and its first endpoint map to the whole-plane
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem uibhbotRelaxedCapturedStageFramedBall_rootData
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hcenterDart : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hrootEdge : wholePlaneEdgeι W N d.1.1 = uibhbotRootEdge W)
    (hmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    (wholePlaneEdgeι W N
      ((uibhbotRelaxedCapturedStageFramedBall W r hr N m c hevent hcenter d
        hcenterDart hrootEdge hmissing).rootDart.1).1 = uibhbotRootEdge W) ∧
    (wholePlaneVertexι W N (stageEndpoint (kmswStage (shiftedStream W N) m)
      (uibhbotRelaxedCapturedStageFramedBall W r hr N m c hevent hcenter d
        hcenterDart hrootEdge hmissing).rootDart.1) = uibhbotRootFirstVertex W) := by
  constructor
  · rw [uibhbotRelaxedCapturedStageFramedBall_rootDart W r hr N m c hevent hcenter d
      hcenterDart hrootEdge hmissing]
    simpa [edgeFlip] using hrootEdge
  · rw [uibhbotRelaxedCapturedStageFramedBall_rootDart W r hr N m c hevent hcenter d
      hcenterDart hrootEdge hmissing]
    exact (congrArg (wholePlaneVertexι W N) hcenterDart).trans hcenter

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The root's first endpoint determines the side of its representative dart. -/
theorem uibhbotRelaxedCapture_rootDart_side (W : ℤ → Fin 3) (N m c : ℕ)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W) : d.2 = true := by
  have hwest : wholePlaneVertexι W N
      ((kmswStage (shiftedStream W N) m).west d.1.val) = uibhbotRootFirstVertex W := by
    rw [(edge_endpoints_eq _ d.1.isLt).1]
    exact congrArg (wholePlaneEdgeWest W) hdroot
  have hend := (congrArg (wholePlaneVertexι W N) hdcenter).trans hcenter
  change wholePlaneVertexι W N
    (if !d.2 then (kmswStage (shiftedStream W N) m).east d.1.val
      else (kmswStage (shiftedStream W N) m).west d.1.val) = _ at hend
  cases hb : d.2
  · have heast : wholePlaneVertexι W N
        ((kmswStage (shiftedStream W N) m).east d.1.val) =
        uibhbotRootFirstVertex W := by
      simpa only [hb, Bool.not_false, ↓reduceIte] using hend
    have heq := wholePlaneVertexι_injective W N (hwest.trans heast.symm)
    have hrank := kmswStageRank_strict (shiftedStream W N) m d.1.val d.1.isLt
    rw [heq] at hrank
    exact (lt_irrefl _ hrank).elim
  · rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A missing rooted dart in a relaxed capture lies on the ambient outer face. -/
theorem uibhbotRelaxedCapture_rootDart_ambient_outer (W : ℤ → Fin 3) (r N m c : ℕ)
    (hev : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    (kmswStageDirectedMap (shiftedStream W N) m).IsOuter d := by
  have hside := uibhbotRelaxedCapture_rootDart_side W N m c hcenter d hdcenter hdroot
  have hcball : c ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (shiftedStream W N) m) (r + 1) c := by
    apply (kmswStageBallVertices_mem_iff_distanceLe _ _ _ _ _ _ hev.1.1).mpr
    exact ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  have hnot := hev.2 c hcball
  have hll : d.1.val ∈ (kmswStage (shiftedStream W N) m).LL := by
    rcases ((kmswStage_status (shiftedStream W N) m).1 d.1.val d.1.isLt).mp
      hdmissing with hur | hll
    · apply False.elim
      apply hnot
      left
      refine ⟨d.1.val, List.mem_append_right _ hur, Or.inl ?_⟩
      change (if !d.2 then (kmswStage (shiftedStream W N) m).east d.1.val
        else (kmswStage (shiftedStream W N) m).west d.1.val) = c at hdcenter
      simpa only [hside, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hdcenter
    · exact hll
  have hout := ((kmswStageDirectedMap_LL_east (shiftedStream W N) m d.1).mpr hll).2
  have hd : d = (d.1, true) := Prod.ext rfl hside
  exact hd.symm ▸ hout

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The other incidence of the relaxed captured frame marks its surviving outer face. -/
theorem uibhbotRelaxedCapturedStageFramedBall_outer_root
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (hev : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    let B := uibhbotRelaxedCapturedStageFramedBall W r hr N m c hev hcenter d
      hdcenter hdroot hdmissing
    B.map.IsOuter (B.map.edgeInv B.rootDart) := by
  have ho := uibhbotRelaxedCapture_rootDart_ambient_outer W r N m c hev hcenter d
    hdcenter hdroot hdmissing
  let B := uibhbotRelaxedCapturedStageFramedBall W r hr N m c hev hcenter d
    hdcenter hdroot hdmissing
  have hx : (B.map.edgeInv B.rootDart).1 = d := by
    change (d.1, !(!d.2)) = d
    exact Prod.ext rfl (Bool.not_not d.2)
  have ho' : (kmswStageDirectedMap (shiftedStream W N) m).IsOuter
      (B.map.edgeInv B.rootDart).1 := hx.symm ▸ ho
  have hex : ∃ o : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
      o ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage (shiftedStream W N) m) r
        (stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d)) ∧
      (kmswStageDirectedMap (shiftedStream W N) m).IsOuter o :=
    ⟨d, (kmswStageBallRootEdge_mem _ m r d hr).1, ho⟩
  classical
  dsimp only [uibhbotRelaxedCapturedStageFramedBall, uibhbotInducedLocalFramedBallRel,
    DirectedMapWithMissing.IsOuter,
    inducedFramedBallOfMissingRoot, inducedDirectedMapWithMissing,
    CombinatorialMap.IsOuter]
  apply inducedCombinatorialMap_face_sameCycle_of_connected_planar
  · exact kmswMap_isPlanar _ _
  · exact kmswStageBallCombinatorialMap_rooted_isConnected _ m r d hr
  · exact (Classical.choose_spec hex).2.symm.trans ho'

private theorem relSucc (u : ℕ → Fin 3) (m r c : ℕ)
    (hev : kmswWindowCaptureEventStrongRel u m (r + 1) c) :
    kmswWindowCaptureEventStrongRel u m r c := by
  have hmono : ∀ v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c,
      v ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u m) (r + 1) c :=
    fun _ hv => kmswStageBallVertices_mono _ _ (by omega) hv
  exact ⟨⟨hev.1.1, fun v hv => hev.1.2.1 v (hmono v hv),
    fun v hv => hev.2 v (hmono v (kmswStageBallVertices_mono _ _ (Nat.sub_le r 1) hv))⟩,
    fun v hv => hev.2 v (hmono v hv)⟩

private theorem relSeamMono (u : ℕ → Fin 3) (m r c k : ℕ)
    (hk : k ∈ kmswBallLeftSeamSet u m r c) :
    k ∈ kmswBallLeftSeamSet u m (r + 1) c := by
  classical
  obtain ⟨hk, ⟨v, hv, he⟩, hl, hem⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨hk,
    ⟨v, kmswStageBallVertices_mono _ _ (by omega) hv, he⟩, hl, hem⟩

private theorem relVertex_fresh (W : ℤ → Fin 3) (r N m c M v : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) = L (shiftedStream W M) (M - N + k))
    (hv : v ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (shiftedStream W N) m) r c) (hNM : N ≤ M) :
    wholePlaneFresh W N M hNM v := by
  classical
  have hv' := kmswStageBallVertices_mono (fun _ _ => True)
    (kmswStage (shiftedStream W N) m) (show r ≤ r + 1 by omega) hv
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  have hs := shiftedStream_shift W N M hNM
  have hb' : v < (kmswStage
      (fun i => shiftedStream W M (M - N + i)) m).nextVertex := by
    rw [hs]
    exact hb
  change (kmswStage (shiftedStream W M) (M - N)).nextVertex ≤
    kmswWindowVertexMapInf (shiftedStream W M) (M - N) v
  rw [kmswWindowVertexMapInf_eq_stage _ _ _ _ hb']
  apply kmswWindowPatchVertexMap_fresh_of_global_seams (shiftedStream W N) m v hb
    (hevent.1.2.1 v hv').1 _ _ (fun i _ => congrFun hs i)
  intro k hk hcreate
  refine ⟨(hevent.1.2.1 v hv').2 k hk hcreate, ?_⟩
  intro hl
  by_cases hem : (kmswStage (shiftedStream W N) k).UL.dropLast.reverse = []
  · exact Or.inr (hglob M hNM k
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ⟨v, hv', hcreate⟩, hl, hem⟩))
  · exact Or.inl hem

private theorem capturedVertex_complete (w : ℕ → Fin 3) (m v : ℕ)
    (hv : ¬ UpperFrontierEndpoint (kmswStage w m) v) :
    kmswVertexComplete w m v := by
  intro e he
  by_contra h
  let n := max m e
  have hb : e < (kmswStage w n).nextEdge :=
    (kmsw_edge_allocated_by_self w e).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_max_right m e))
  have hnew := kmswStage_no_new_incidence_of_not_upperFrontier w m v hv n
    (Nat.le_max_left m e) e hb (Nat.le_of_not_gt h)
  rw [(edge_endpoints_eq w hb).1, (edge_endpoints_eq w hb).2] at hnew
  exact he.elim hnew.1 hnew.2

private theorem firstReturn_common_embedding
    {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : Equiv.Perm α) (g : Equiv.Perm β) (R : Equiv.Perm γ)
    (S : Finset α) (T : Finset β) (U : Set α) (V : Set β)
    (i : α → γ) (j : β → γ) (hi : Function.Injective i) (hj : Function.Injective j)
    (hU : ∀ x, x ∈ U → f x ∈ U) (hV : ∀ x, x ∈ V → g x ∈ V)
    (hiR : ∀ x, x ∈ U → i (f x) = R (i x))
    (hjR : ∀ x, x ∈ V → j (g x) = R (j x))
    (e : S ≃ T) (he : ∀ x, i x.1 = j (e x).1)
    (x : S) (hx : x.1 ∈ U) (hy : (e x).1 ∈ V) :
    e (cyclicFirstReturn f S (finitePermutationReturn f S) x) =
      cyclicFirstReturn g T (finitePermutationReturn g T) (e x) := by
  have hiter (k : ℕ) :
      (f ^ k) x.1 ∈ U ∧ (g ^ k) (e x).1 ∈ V ∧
        i ((f ^ k) x.1) = j ((g ^ k) (e x).1) := by
    induction k with
    | zero => exact ⟨hx, hy, he x⟩
    | succ k ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨hU _ ih.1, hV _ ih.2.1,
        (hiR _ ih.1).trans ((congrArg R ih.2.2).trans (hjR _ ih.2.1).symm)⟩
  have hmem (k : ℕ) : (f ^ k) x.1 ∈ S ↔ (g ^ k) (e x).1 ∈ T := by
    constructor
    · intro hk
      have hq := hj ((he ⟨_, hk⟩).symm.trans (hiter k).2.2)
      exact hq ▸ (e ⟨_, hk⟩).2
    · intro hk
      let y : T := ⟨_, hk⟩
      have hq : i (e.symm y).1 = j y.1 := by
        simpa only [Equiv.apply_symm_apply] using he (e.symm y)
      have hp := hi (hq.trans (hiter k).2.2.symm)
      exact hp ▸ (e.symm y).2
  let k := cyclicFirstReturnTime f S (finitePermutationReturn f S) x
  let l := cyclicFirstReturnTime g T (finitePermutationReturn g T) (e x)
  have ht : k = l := by
    apply Nat.le_antisymm
    · exact Nat.find_min' _ ⟨(cyclicFirstReturnTime_spec g T _ (e x)).1,
        (hmem l).mpr (cyclicFirstReturnTime_spec g T _ (e x)).2.1⟩
    · exact Nat.find_min' _ ⟨(cyclicFirstReturnTime_spec f S _ x).1,
        (hmem k).mp (cyclicFirstReturnTime_spec f S _ x).2.1⟩
  apply Subtype.ext
  apply hj
  calc
    j (e (cyclicFirstReturn f S _ x)).1 = i (cyclicFirstReturn f S _ x).1 := (he _).symm
    _ = i ((f ^ k) x.1) := congrArg i (firstReturn_spec f S _ x).1
    _ = j ((g ^ l) (e x).1) := ht ▸ (hiter k).2.2
    _ = j (cyclicFirstReturn g T _ (e x)).1 :=
      congrArg j (firstReturn_spec g T _ (e x)).1.symm

private theorem relDart_rotation_agrees (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (r N m c : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hd : stageEndpoint (kmswStage (shiftedStream W N) m) d ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) m) r c) :
    wholePlaneRotation W H (wholePlaneDartι W N (d.1.val, d.2)) =
      wholePlaneDartι W N (kmswInfRot (shiftedStream W N) (H.1 N)
        (d.1.val, d.2)) := by
  apply wholePlaneRotation_ι_of_fresh
  intro M hNM
  have hfresh := relVertex_fresh W r N m c M
    (stageEndpoint (kmswStage (shiftedStream W N) m) d) hevent hglob hd hNM
  simpa only [stageEndpoint, (edge_endpoints_eq (shiftedStream W N) d.1.isLt).1,
    (edge_endpoints_eq (shiftedStream W N) d.1.isLt).2] using hfresh

/-- Each radius-`r` captured finite dart ball maps bijectively onto the
whole-plane darts with both endpoints in the ordered root ball
supplies complete capture.
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem uibhbotRelaxedCapturedStageBallDarts_bijOn
    (W : ℤ → Fin 3) (r : ℕ) (N m c : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W) :
    Set.BijOn
      (fun d : StageDart (kmswStage (shiftedStream W N) m).nextEdge =>
        wholePlaneDartι W N (d.1.val, d.2))
      (↑(kmswStageBallDarts (fun _ _ => True)
        (kmswStage (shiftedStream W N) m) r c) :
          Set (StageDart (kmswStage (shiftedStream W N) m).nextEdge))
      {d : WholePlaneDart W |
        wholePlaneEdgeWest W d.1 ∈ uibhbotRootBallVertices W r ∧
        wholePlaneEdgeEast W d.1 ∈ uibhbotRootBallVertices W r} := by
  classical
  let u := shiftedStream W N
  let s := kmswStage u m
  let S := kmswStageBallVertices (fun _ _ => True) s r c
  have hstrong := relSucc u m r c hevent
  have hedge := kmswWindowCaptureEventStrongRel_wholePlaneEdge_bijOn
    W N m r c hstrong (fun M hNM k hk =>
      hglob M hNM k (relSeamMono u m r c k hk))
  change Set.BijOn
    (fun e : Fin s.nextEdge => wholePlaneEdgeι W N e.val)
    {e | s.west e.val ∈ S ∧ s.east e.val ∈ S}
    {e | wholePlaneEdgeWest W e ∈
        wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
      wholePlaneEdgeEast W e ∈
        wholePlaneBallVertices W r (wholePlaneVertexι W N c)} at hedge
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    have hends := (kmswStageBallDarts_mem_iff (fun _ _ => True)
      s r c d).mp hd
    have heS : s.west d.1.val ∈ S ∧ s.east d.1.val ∈ S := by
      rcases d with ⟨e, b⟩
      cases b <;> simpa [stageEndpoint, edgeFlip_apply, and_comm] using hends
    have he := hedge.1 heS
    change wholePlaneEdgeWest W (wholePlaneDartι W N
        (d.1.val, d.2)).1 ∈ uibhbotRootBallVertices W r ∧
      wholePlaneEdgeEast W (wholePlaneDartι W N (d.1.val, d.2)).1 ∈
        uibhbotRootBallVertices W r
    simpa [wholePlaneDartι, uibhbotRootBallVertices, hcenter] using he
  · intro d hd e he hde
    change (wholePlaneEdgeι W N d.1.val, d.2) =
      (wholePlaneEdgeι W N e.1.val, e.2) at hde
    have hEdge : wholePlaneEdgeι W N d.1.val = wholePlaneEdgeι W N e.1.val := by
      exact congrArg (fun p : WholePlaneEdge W × Bool => p.1) hde
    have hSide : d.2 = e.2 :=
      congrArg (fun p : WholePlaneEdge W × Bool => p.2) hde
    apply Prod.ext
    · apply Fin.ext
      exact wholePlaneEdgeι_injective W N hEdge
    · exact hSide
  · intro d hd
    have hdRoot : wholePlaneEdgeWest W d.1 ∈ uibhbotRootBallVertices W r ∧
        wholePlaneEdgeEast W d.1 ∈ uibhbotRootBallVertices W r := by
      change wholePlaneEdgeWest W d.1 ∈ uibhbotRootBallVertices W r ∧
        wholePlaneEdgeEast W d.1 ∈ uibhbotRootBallVertices W r at hd
      exact hd
    have hd' : wholePlaneEdgeWest W d.1 ∈
        wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
      wholePlaneEdgeEast W d.1 ∈
        wholePlaneBallVertices W r (wholePlaneVertexι W N c) := by
      simpa [uibhbotRootBallVertices, hcenter] using hdRoot
    obtain ⟨e, heS, hEdge⟩ := hedge.2.2 hd'
    rcases d with ⟨edge, side⟩
    let x : StageDart s.nextEdge := (e, side)
    have hx : x ∈ kmswStageBallDarts (fun _ _ => True) s r c := by
      cases side
      · apply (kmswStageBallDarts_mem_iff (fun _ _ => True) s r c x).2
        simpa [x, stageEndpoint, edgeFlip_apply] using heS
      · apply (kmswStageBallDarts_mem_iff (fun _ _ => True) s r c x).2
        simpa [x, stageEndpoint, edgeFlip_apply, and_comm] using heS
    refine ⟨x, hx, ?_⟩
    apply Prod.ext
    · exact hEdge
    · rfl

/-- The two captured radius-`r` dart balls have the same whole-plane image,
namely the darts induced by the ordered root ball
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem uibhbotRelaxedCapturedStageBallDarts_sameWholePlaneImage
    (W : ℤ → Fin 3) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (hevent' : kmswWindowCaptureEventStrongRel (shiftedStream W N') m' (r + 1) c')
    (hglob' : ∀ M, N' ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N') m' (r + 1) c',
        minL (shiftedStream W M) (M - N' + k) =
          L (shiftedStream W M) (M - N' + k))
    (hcenter' : wholePlaneVertexι W N' c' = uibhbotRootFirstVertex W) :
    Set.BijOn
        (fun d : StageDart (kmswStage (shiftedStream W N) m).nextEdge =>
          wholePlaneDartι W N (d.1.val, d.2))
        (↑(kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N) m) r c) :
            Set (StageDart (kmswStage (shiftedStream W N) m).nextEdge))
        {d : WholePlaneDart W |
          wholePlaneEdgeWest W d.1 ∈ uibhbotRootBallVertices W r ∧
          wholePlaneEdgeEast W d.1 ∈ uibhbotRootBallVertices W r} ∧
      Set.BijOn
        (fun d : StageDart (kmswStage (shiftedStream W N') m').nextEdge =>
          wholePlaneDartι W N' (d.1.val, d.2))
        (↑(kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N') m') r c') :
            Set (StageDart (kmswStage (shiftedStream W N') m').nextEdge))
        {d : WholePlaneDart W |
          wholePlaneEdgeWest W d.1 ∈ uibhbotRootBallVertices W r ∧
          wholePlaneEdgeEast W d.1 ∈ uibhbotRootBallVertices W r} := by
  exact ⟨uibhbotRelaxedCapturedStageBallDarts_bijOn W r N m c hevent hglob hcenter,
    uibhbotRelaxedCapturedStageBallDarts_bijOn W r N' m' c' hevent' hglob' hcenter'⟩

/-- The two finite dart balls are equivalent by identifying each through its
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem uibhbotRelaxedCapturedStageBallDarts_equiv
    (W : ℤ → Fin 3) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (hevent' : kmswWindowCaptureEventStrongRel (shiftedStream W N') m' (r + 1) c')
    (hglob' : ∀ M, N' ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N') m' (r + 1) c',
        minL (shiftedStream W M) (M - N' + k) =
          L (shiftedStream W M) (M - N' + k))
    (hcenter' : wholePlaneVertexι W N' c' = uibhbotRootFirstVertex W) :
    ∃ e :
        {d : StageDart (kmswStage (shiftedStream W N) m).nextEdge //
          d ∈ kmswStageBallDarts (fun _ _ => True)
            (kmswStage (shiftedStream W N) m) r c} ≃
        {d : StageDart (kmswStage (shiftedStream W N') m').nextEdge //
          d ∈ kmswStageBallDarts (fun _ _ => True)
            (kmswStage (shiftedStream W N') m') r c'},
      ∀ d,
        wholePlaneDartι W N (d.1.1.val, d.1.2) =
          wholePlaneDartι W N' ((e d).1.1.val, (e d).1.2) := by
  classical
  let A := {d : StageDart (kmswStage (shiftedStream W N) m).nextEdge //
    d ∈ kmswStageBallDarts (fun _ _ => True)
      (kmswStage (shiftedStream W N) m) r c}
  let A' := {d : StageDart (kmswStage (shiftedStream W N') m').nextEdge //
    d ∈ kmswStageBallDarts (fun _ _ => True)
      (kmswStage (shiftedStream W N') m') r c'}
  let T := {d : WholePlaneDart W |
    wholePlaneEdgeWest W d.1 ∈ uibhbotRootBallVertices W r ∧
    wholePlaneEdgeEast W d.1 ∈ uibhbotRootBallVertices W r}
  obtain ⟨hN, hN'⟩ := uibhbotRelaxedCapturedStageBallDarts_sameWholePlaneImage
    W r N m c N' m' c' hevent hglob hcenter hevent' hglob' hcenter'
  let f : A → T := fun d =>
    ⟨wholePlaneDartι W N (d.1.1.val, d.1.2), hN.1 d.2⟩
  let f' : A' → T := fun d =>
    ⟨wholePlaneDartι W N' (d.1.1.val, d.1.2), hN'.1 d.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact hN.2.1 a.2 b.2 (congrArg Subtype.val hab)
    · intro q
      obtain ⟨d, hd, hq⟩ := hN.2.2 q.2
      exact ⟨⟨d, hd⟩, Subtype.ext hq⟩
  have hf' : Function.Bijective f' := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact hN'.2.1 a.2 b.2 (congrArg Subtype.val hab)
    · intro q
      obtain ⟨d, hd, hq⟩ := hN'.2.2 q.2
      exact ⟨⟨d, hd⟩, Subtype.ext hq⟩
  let E := (Equiv.ofBijective f hf).trans (Equiv.ofBijective f' hf').symm
  refine ⟨E, ?_⟩
  intro d
  change (Equiv.ofBijective f hf d).val =
    (Equiv.ofBijective f' hf' ((Equiv.ofBijective f' hf').symm
      (Equiv.ofBijective f hf d))).val
  exact congrArg Subtype.val
    ((Equiv.ofBijective f' hf').apply_symm_apply (Equiv.ofBijective f hf d)).symm


/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Captured rotations are first returns of the same whole-plane rotation -/
theorem uibhbotRelaxedCapturedStageBallDarts_equiv_rot
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (hevent' : kmswWindowCaptureEventStrongRel (shiftedStream W N') m' (r + 1) c')
    (hglob' : ∀ M, N' ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N') m' (r + 1) c',
        minL (shiftedStream W M) (M - N' + k) =
          L (shiftedStream W M) (M - N' + k))
    (hcenter' : wholePlaneVertexι W N' c' = uibhbotRootFirstVertex W)
    (e :
      {d : StageDart (kmswStage (shiftedStream W N) m).nextEdge //
        d ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N) m) r c} ≃
      {d : StageDart (kmswStage (shiftedStream W N') m').nextEdge //
        d ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N') m') r c'})
    (he : ∀ d,
      wholePlaneDartι W N (d.1.1.val, d.1.2) =
        wholePlaneDartι W N' ((e d).1.1.val, (e d).1.2)) :
    ∀ d, e (kmswStageBallRot (fun _ _ => True) (shiftedStream W N) m r c d) =
      kmswStageBallRot (fun _ _ => True) (shiftedStream W N') m' r c' (e d) := by
  classical
  have hdata (A t b : ℕ)
      (hev : kmswWindowCaptureEventStrongRel (shiftedStream W A) t (r + 1) b)
      (hg : ∀ M, A ≤ M →
        ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W A) t (r + 1) b,
          minL (shiftedStream W M) (M - A + k) =
            L (shiftedStream W M) (M - A + k)) :
      let s := kmswStage (shiftedStream W A) t
      let U : Set (StageDart s.nextEdge) :=
        {d | stageEndpoint s d ∈ kmswStageBallVertices (fun _ _ => True) s r b}
      (∀ d, d ∈ U → stageRot (shiftedStream W A) t d ∈ U) ∧
      (∀ d, d ∈ U →
        wholePlaneDartι W A ((stageRot (shiftedStream W A) t d).1.val,
          (stageRot (shiftedStream W A) t d).2) =
        wholePlaneRotation W H (wholePlaneDartι W A (d.1.val, d.2))) := by
    dsimp only
    constructor
    · intro d hd
      have hep := (stageRot_sameCycle_iff_endpoint_eq (shiftedStream W A) t d
        (stageRot (shiftedStream W A) t d)).mp ⟨1, rfl⟩
      change stageEndpoint (kmswStage (shiftedStream W A) t) d ∈
        kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W A) t) r b at hd
      change stageEndpoint (kmswStage (shiftedStream W A) t)
        (stageRot (shiftedStream W A) t d) ∈
        kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W A) t) r b
      exact hep ▸ hd
    · intro d hd
      rw [relDart_rotation_agrees W H r A t b hev hg d hd,
        kmswInfRot_eq_stage (shiftedStream W A) (H.1 A) t d
          (capturedVertex_complete _ _ _
            ((relSucc _ _ _ _ hev).2 _ hd))]
  have hinj (A t : ℕ) : Function.Injective
      (fun d : StageDart (kmswStage (shiftedStream W A) t).nextEdge =>
        wholePlaneDartι W A (d.1.val, d.2)) := by
    intro a b hab
    change (wholePlaneEdgeι W A a.1.val, a.2) =
      (wholePlaneEdgeι W A b.1.val, b.2) at hab
    apply Prod.ext
    · exact Fin.ext (wholePlaneEdgeι_injective W A (congrArg Prod.fst hab))
    · exact congrArg (fun q : WholePlaneDart W => q.2) hab
  have hsource := hdata N m c hevent hglob
  have htarget := hdata N' m' c' hevent' hglob'
  have _hcenters := hcenter.trans hcenter'.symm
  intro d
  exact firstReturn_common_embedding _ _ (wholePlaneRotation W H) _ _ _ _
    _ _ (hinj N m) (hinj N' m') hsource.1 htarget.1 hsource.2 htarget.2 e he d
    ((kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2).1
    ((kmswStageBallDarts_mem_iff _ _ _ _ _).mp (e d).2).1

private theorem capturedStage_present_iff (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge)
    (hv : ¬ UpperFrontierEndpoint (kmswStage w m) (stageEndpoint (kmswStage w m) d)) :
    EdgePresent w d.1.val ↔ (kmswStage w m).present d.1.val = true := by
  have hstable (n : ℕ) (hmn : m ≤ n) :
      (kmswStage w n).present d.1.val = (kmswStage w m).present d.1.val := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      have hne : d.1.val ≠ (kmswStage w (n + 1)).active := by
        intro heq
        obtain ⟨xs, hxs⟩ := kmswStage_UL_last w (n + 1)
        have hmem : (kmswStage w (n + 1)).active ∈
            (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR := by
          rw [hxs]
          simp
        have hf := kmswStage_upperFrontier_endpoints w m (n + 1)
          (by omega) _ hmem
        rw [← heq] at hf
        have hs := kmswStage_endpoints_stable w (m := m) (n := n + 1)
          (by omega) d.1.isLt
        rw [hs.1, hs.2] at hf
        cases hb : d.2
        · exact hv (by simpa only [stageEndpoint, hb, Bool.false_eq_true,
            ↓reduceIte] using hf.1)
        · exact hv (by simpa only [stageEndpoint, hb, ↓reduceIte] using hf.2)
      change (kmswStep (kmswStage w n) (w n)).present d.1.val = _
      rw [kmswStep_present_existing _ _
        (d.1.isLt.trans_le (kmswStage_nextEdge_mono w hmn))]
      change (if d.1.val = (kmswStage w (n + 1)).active then true
        else (kmswStage w n).present d.1.val) = _
      rw [ite_eq_right hne]
      exact ih
  constructor
  · rintro ⟨n, hn, hp⟩
    have hp' := (present_mono w hn hp (max m n) (Nat.le_max_right m n)).2
    rw [hstable _ (Nat.le_max_left m n)] at hp'
    exact hp'
  · exact fun hp => ⟨m, d.1.isLt, hp⟩

private theorem relStage_wholePlane_present (W : ℤ → Fin 3) (r N m c : ℕ)
    (hev : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (d : KMSWStageBallDart (fun _ _ => True) (kmswStage (shiftedStream W N) m) r c) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N d.1.1.val) ↔
      (kmswStage (shiftedStream W N) m).present d.1.1.val = true := by
  have hd := ((kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2).1
  have hf (M : ℕ) (hNM : N ≤ M) :=
    relVertex_fresh W r N m c M _ hev hglob hd hNM
  have hf' : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (if d.1.2 then edgeEast (shiftedStream W N) d.1.1.val
        else edgeWest (shiftedStream W N) d.1.1.val) := by
    intro M hNM
    simpa only [stageEndpoint, (edge_endpoints_eq _ d.1.1.isLt).1,
      (edge_endpoints_eq _ d.1.1.isLt).2] using hf M hNM
  exact (wholePlaneEdgePresent_ι_of_fresh W N d.1.1.val d.1.2 hf').trans
    (capturedStage_present_iff _ m d.1
      ((relSucc _ _ _ _ hev).2 _ hd))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Capture-choice equivalences preserve present and missing tags and dart tails -/
theorem uibhbotRelaxedCapturedStageBallDarts_equiv_tags
    (W : ℤ → Fin 3) (r : ℕ) (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (hevent' : kmswWindowCaptureEventStrongRel (shiftedStream W N') m' (r + 1) c')
    (hglob' : ∀ M, N' ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N') m' (r + 1) c',
        minL (shiftedStream W M) (M - N' + k) =
          L (shiftedStream W M) (M - N' + k))
    (e : KMSWStageBallDart (fun _ _ => True) (kmswStage (shiftedStream W N) m) r c ≃
      KMSWStageBallDart (fun _ _ => True) (kmswStage (shiftedStream W N') m') r c')
    (he : ∀ d, wholePlaneDartι W N (d.1.1.val, d.1.2) =
      wholePlaneDartι W N' ((e d).1.1.val, (e d).1.2)) :
    ∀ d, (kmswStage (shiftedStream W N) m).present d.1.1.val =
        (kmswStage (shiftedStream W N') m').present (e d).1.1.val ∧
      ((kmswStageDirectedMap (shiftedStream W N') m').missing (e d).1 ↔
        (kmswStageDirectedMap (shiftedStream W N) m).missing d.1) ∧
      ((kmswStageDirectedMap (shiftedStream W N') m').tail (e d).1 ↔
        (kmswStageDirectedMap (shiftedStream W N) m).tail d.1) := by
  intro d
  obtain ⟨hedge, hside⟩ := uibhbotCapturedStageBallDarts_equiv_edgeIdentity_orientation
    W r N m c N' m' c' e he d
  have hp := relStage_wholePlane_present W r N m c hevent hglob d
  have hp' := relStage_wholePlane_present W r N' m' c' hevent' hglob' (e d)
  rw [hedge] at hp
  have ht := hp.symm.trans hp'
  have hbool : (kmswStage (shiftedStream W N) m).present d.1.1.val =
      (kmswStage (shiftedStream W N') m').present (e d).1.1.val := by
    cases h : (kmswStage (shiftedStream W N) m).present d.1.1.val <;>
      cases h' : (kmswStage (shiftedStream W N') m').present (e d).1.1.val <;>
      simp_all only [Bool.false_eq_true, iff_false, iff_true, not_true_eq_false]
  refine ⟨hbool, ?_, ?_⟩
  · change (_ = false ↔ _ = false)
    rw [hbool]
  · change (_ = true ∧ _ = false ↔ _ = true ∧ _ = false)
    rw [hbool, hside]

private theorem sameCycle_equiv_iff {α β : Type*} [Finite α] [Finite β]
    (e : α ≃ β) (f : Equiv.Perm α) (g : Equiv.Perm β)
    (hc : ∀ x, e (f x) = g (e x)) (x y : α) :
    f.SameCycle x y ↔ g.SameCycle (e x) (e y) := by
  have hp (n : ℕ) (a : α) : e ((f ^ n) a) = (g ^ n) (e a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply]
      exact (hc _).trans (congrArg g ih)
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, (hp n x).symm.trans (congrArg e hn)⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, e.injective ((hp n x).trans hn)⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Captured framed balls at the same missing whole-plane root are isomorphic -/
theorem uibhbotRelaxedCapturedStageFramedBall_captureChoice
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (r : ℕ) (hr : 0 < r)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d)
    (hevent' : kmswWindowCaptureEventStrongRel (shiftedStream W N') m' (r + 1) c')
    (hglob' : ∀ M, N' ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N') m' (r + 1) c',
        minL (shiftedStream W M) (M - N' + k) =
          L (shiftedStream W M) (M - N' + k))
    (hcenter' : wholePlaneVertexι W N' c' = uibhbotRootFirstVertex W)
    (d' : StageDart (kmswStage (shiftedStream W N') m').nextEdge)
    (hdcenter' : stageEndpoint (kmswStage (shiftedStream W N') m')
      (edgeFlip _ d') = c')
    (hdroot' : wholePlaneEdgeι W N' d'.1.val = uibhbotRootEdge W)
    (hdmissing' : (kmswStageDirectedMap (shiftedStream W N') m').missing d') :
    Nonempty (FramedBallIso
      (uibhbotRelaxedCapturedStageFramedBall W r hr N m c hevent hcenter d
        hdcenter hdroot hdmissing)
      (uibhbotRelaxedCapturedStageFramedBall W r hr N' m' c' hevent' hcenter' d'
        hdcenter' hdroot' hdmissing')) := by
  classical
  subst c
  subst c'
  let A := uibhbotRelaxedCapturedStageFramedBall W r hr N m _ hevent hcenter d
    rfl hdroot hdmissing
  let B := uibhbotRelaxedCapturedStageFramedBall W r hr N' m' _ hevent' hcenter' d'
    rfl hdroot' hdmissing'
  obtain ⟨e, he⟩ := uibhbotRelaxedCapturedStageBallDarts_equiv W r N m _ N' m' _
    hevent hglob hcenter hevent' hglob' hcenter'
  let E : A.D ≃ B.D := e
  let a0 : A.D := ⟨d, (kmswStageBallRootEdge_mem _ m r d hr).1⟩
  let b0 : B.D := ⟨d', (kmswStageBallRootEdge_mem _ m' r d' hr).1⟩
  have hrot : ∀ x, E (A.map.rot x) = B.map.rot (E x) :=
    uibhbotRelaxedCapturedStageBallDarts_equiv_rot W H r N m _ N' m' _
      hevent hglob hcenter hevent' hglob' hcenter' e he
  have hflip : ∀ x, E (A.map.edgeInv x) = B.map.edgeInv (E x) :=
    uibhbotCapturedStageBallDarts_equiv_edgeFlip W r N m _ N' m' _ e he
  have htags := uibhbotRelaxedCapturedStageBallDarts_equiv_tags W r N m _ N' m' _
    hevent hglob hevent' hglob' e he
  have hs := uibhbotRelaxedCapture_rootDart_side W N m _ hcenter d rfl hdroot
  have hs' := uibhbotRelaxedCapture_rootDart_side W N' m' _ hcenter' d' rfl hdroot'
  have hbase : E a0 = b0 := by
    have h := he a0
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      apply wholePlaneEdgeι_injective W N'
      calc
        wholePlaneEdgeι W N' (E a0).1.1.val =
            wholePlaneEdgeι W N d.1.val := (congrArg Prod.fst h).symm
        _ = uibhbotRootEdge W := hdroot
        _ = wholePlaneEdgeι W N' d'.1.val := hdroot'.symm
    · change (E a0).1.2 = d'.2
      have hb : d.2 = (E a0).1.2 :=
        congrArg (fun q : WholePlaneDart W => q.2) h
      exact hb.symm.trans (hs.trans hs'.symm)
  have hroot : E A.rootDart = B.rootDart := by
    exact (hflip a0).trans (congrArg B.map.edgeInv hbase)
  have hsym (x : A.D) : E (A.map.rot.symm x) = B.map.rot.symm (E x) := by
    apply B.map.rot.injective
    rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hface (x : A.D) : E (A.map.faceSucc x) = B.map.faceSucc (E x) := by
    change E (A.map.rot.symm (A.map.edgeInv x)) =
      B.map.rot.symm (B.map.edgeInv (E x))
    rw [hsym, hflip]
  have hoA := uibhbotRelaxedCapturedStageFramedBall_outer_root W r hr N m _ hevent hcenter d
    rfl hdroot hdmissing
  have hoB := uibhbotRelaxedCapturedStageFramedBall_outer_root W r hr N' m' _ hevent' hcenter' d'
    rfl hdroot' hdmissing'
  change A.map.IsOuter (A.map.edgeInv (A.map.edgeInv a0)) at hoA
  rw [A.map.edgeInv_invol] at hoA
  change B.map.IsOuter (B.map.edgeInv (B.map.edgeInv b0)) at hoB
  rw [B.map.edgeInv_invol] at hoB
  have houter (x : A.D) : B.map.IsOuter (E x) ↔ A.map.IsOuter x := by
    have hcycle := sameCycle_equiv_iff E A.map.faceSucc B.map.faceSucc hface
      a0 x
    rw [hbase] at hcycle
    constructor
    · intro hx
      exact hoA.trans (hcycle.mpr (hoB.symm.trans hx))
    · intro hx
      exact hoB.trans (hcycle.mp (hoA.symm.trans hx))
  let I : DirectedMapWithMissingIso A.map B.map :=
    { toEquiv := E
      rot_comm := hrot
      edgeInv_comm := hflip
      missing_iff := fun x => (htags x).2.1
      tail_iff := fun x => (htags x).2.2
      outer_iff := houter }
  refine ⟨{ mapIso := I
            root_vertex := ?_
            frameEdge_comm := hroot
            frameOther_comm := ?_ }⟩
  · exact hroot.sameCycle B.map.rot
  · right
    refine ⟨E a0, b0, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact hbase.sameCycle B.map.rot


/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The certified rooted capture data supplied almost surely above, including both
seam certificates and prefix floors. -/
structure UIBHBOTCertifiedRootCapture (W : ℤ → Fin 3) (r : ℕ) where
  N : ℕ
  m : ℕ
  c : ℕ
  event : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c
  seams : ∀ M, N ≤ M →
    ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
      minL (shiftedStream W M) (M - N + k) =
        L (shiftedStream W M) (M - N + k) ∧
      ∀ j ≤ M - N,
        L (shiftedStream W M) (M - N + k) ≤ L (shiftedStream W M) j
  center : wholePlaneVertexι W N c = uibhbotRootFirstVertex W
  dart : StageDart (kmswStage (shiftedStream W N) m).nextEdge
  dart_center : stageEndpoint (kmswStage (shiftedStream W N) m)
    (edgeFlip _ dart) = c
  root : wholePlaneEdgeι W N dart.1.val = uibhbotRootEdge W
  missing : (kmswStageDirectedMap (shiftedStream W N) m).missing dart

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The framed ball determined by certified capture data. -/
@[expose] noncomputable def UIBHBOTCertifiedRootCapture.framedBall
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r) (hr : 0 < r) :
    FramedBall :=
  uibhbotRelaxedCapturedStageFramedBall W r hr C.N C.m C.c C.event C.center C.dart
    C.dart_center C.root C.missing

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Any two certified captures of the same word and positive radius give isomorphic
framed balls on the rotation event. -/
theorem UIBHBOTCertifiedRootCapture.nonempty_iso {W : ℤ → Fin 3} {r : ℕ}
    (H : WholePlaneRotationHypothesis W) (hr : 0 < r)
    (C D : UIBHBOTCertifiedRootCapture W r) :
    Nonempty (FramedBallIso (C.framedBall hr) (D.framedBall hr)) := by
  exact uibhbotRelaxedCapturedStageFramedBall_captureChoice W H r hr
    C.N C.m C.c D.N D.m D.c C.event (fun M h k hk => (C.seams M h k hk).1)
    C.center C.dart C.dart_center C.root C.missing
    D.event (fun M h k hk => (D.seams M h k hk).1)
    D.center D.dart D.dart_center D.root D.missing

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Certified capture choices have the same framed class. -/
theorem UIBHBOTCertifiedRootCapture.class_eq {W : ℤ → Fin 3} {r : ℕ}
    (H : WholePlaneRotationHypothesis W) (hr : 0 < r)
    (C D : UIBHBOTCertifiedRootCapture W r) :
    uibhbotCapturedStageBallClass (C.framedBall hr) =
      uibhbotCapturedStageBallClass (D.framedBall hr) := by
  exact Quotient.sound (C.nonempty_iso H hr D)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Almost surely the rotation hypothesis and certified rooted captures hold together. -/
theorem uibhbotWordFamilyLaw_ae_certifiedRootCapture :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        WholePlaneRotationHypothesis W ∧
          ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r) := by
  filter_upwards [uibhbotWordFamilyLaw_ae_relaxedRootCapture_certified,
    uibhbotWordFamilyLaw_ae_rotationHypothesis] with w hcap hrot
  obtain ⟨hw, hcap⟩ := hcap
  obtain ⟨hw', hrot⟩ := hrot
  have hproof : hw' = hw := Subsingleton.elim _ _
  subst hw'
  refine ⟨hw, hrot, ?_⟩
  intro r
  obtain ⟨N, m, c, hev, hseam, hc, d, hd, he, hm⟩ := hcap r
  exact ⟨⟨N, m, c, hev, hseam, hc, d, hd, he, hm⟩⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The almost-sure certified radius-one captures prove that the framed class space -/
theorem uibhbotFramedBallClass_nonempty : Nonempty FramedBallClass := by
  obtain ⟨w, hw, _, hcap⟩ := uibhbotWordFamilyLaw_ae_certifiedRootCapture.exists
  obtain ⟨C⟩ := hcap 1
  exact ⟨uibhbotCapturedStageBallClass (C.framedBall Nat.zero_lt_one)⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A fixed off-event class, chosen from a class space proved nonempty using an
almost-sure certified radius-one capture. Its use is almost surely excluded by
`uibhbotWordFamilyLaw_ae_ballClassRel`. -/
@[expose] noncomputable def uibhbotOffCaptureClassRel : FramedBallClass :=
  Classical.choice uibhbotFramedBallClass_nonempty

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Choose a certified capture class only when rotation and capture existence hold.
Off this event use a
fixed class chosen from the nonempty class space, whose nonemptiness is proved
using an almost-sure radius-one certified capture. The almost-sure agreement with
every certified capture is `uibhbotWordFamilyLaw_ae_ballClassRel` below. -/
@[expose] noncomputable def uibhbotBallClassRel (W : ℤ → Fin 3) (r : ℕ)
    (hr : 0 < r) : FramedBallClass := by
  classical
  exact if h : WholePlaneRotationHypothesis W ∧
      Nonempty (UIBHBOTCertifiedRootCapture W r) then
    uibhbotCapturedStageBallClass ((Classical.choice h.2).framedBall hr)
  else uibhbotOffCaptureClassRel

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
On the rotation event the chosen class equals that of every certified capture. -/
theorem uibhbotBallClassRel_eq_capture (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (r : ℕ) (hr : 0 < r)
    (C : UIBHBOTCertifiedRootCapture W r) :
    uibhbotBallClassRel W r hr = uibhbotCapturedStageBallClass (C.framedBall hr) := by
  classical
  rw [uibhbotBallClassRel, dite_eq_left ⟨H, ⟨C⟩⟩]
  exact UIBHBOTCertifiedRootCapture.class_eq H hr _ C

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Almost surely all positive-radius classes use the capture branch and equal the
class of every certified rooted capture. This also specifies the probability-one
meaning of the otherwise arbitrary off-event class. -/
theorem uibhbotWordFamilyLaw_ae_ballClassRel :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ∀ r : ℕ, ∀ hr : 0 < r,
          Nonempty (UIBHBOTCertifiedRootCapture W r) ∧
          ∀ C : UIBHBOTCertifiedRootCapture W r,
            uibhbotBallClassRel W r hr =
              uibhbotCapturedStageBallClass (C.framedBall hr) := by
  filter_upwards [uibhbotWordFamilyLaw_ae_certifiedRootCapture] with w hcap
  obtain ⟨hw, H, hcap⟩ := hcap
  exact ⟨hw, fun r hr => ⟨hcap r, fun C => uibhbotBallClassRel_eq_capture _ H r hr C⟩⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The value outside the certified-capture event is the specified fixed class. -/
theorem uibhbotBallClassRel_eq_offCapture (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r)
    (h : ¬ Nonempty (UIBHBOTCertifiedRootCapture W r)) :
    uibhbotBallClassRel W r hr = uibhbotOffCaptureClassRel := by
  classical
  exact dite_eq_right (fun hh => h hh.2)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The selector uses the explicit default whenever rotation fails. -/
theorem uibhbotBallClassRel_eq_offRotation (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r)
    (h : ¬ WholePlaneRotationHypothesis W) :
    uibhbotBallClassRel W r hr = uibhbotOffCaptureClassRel := by
  classical
  exact dite_eq_right (fun hh => h hh.1)

private theorem measurable_relShift (N : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => shiftedStream W N) :=
  Measurable.of_eval (fun i => measurable_pi_apply ((i : ℤ) - N))

private theorem measurable_relL (N n : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => L (shiftedStream W N) n) := by
  have hL : Measurable (fun u : ℕ → Fin 3 => L u n) :=
    measurable_to_countable' (fun a => measurableSet_L n (fun b => b = a))
  exact hL.comp (measurable_relShift N)

private theorem measurable_relMinL (N n : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => minL (shiftedStream W N) n) := by
  induction n with
  | zero => exact measurable_relL N 0
  | succ n ih => exact ih.min (measurable_relL N (n + 1))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The global seam and prefix-floor certificate for fixed capture indices is a
measurable event in the bi-infinite word. This is one ingredient of class-law
measurability, not a measurability theorem for the chosen class. -/
theorem measurableSet_uibhbotRelaxedCapture_certificates (N m r c : ℕ) :
    MeasurableSet {W : ℤ → Fin 3 | ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k) ∧
        ∀ j ≤ M - N,
          L (shiftedStream W M) (M - N + k) ≤ L (shiftedStream W M) j} := by
  have hS : Measurable (fun W : ℤ → Fin 3 =>
      kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c) :=
    (measurable_to_countable' (measurableSet_kmswBallLeftSeamSet m (r + 1) c)).comp
      (measurable_relShift N)
  have hmem (k : ℕ) : MeasurableSet {W : ℤ → Fin 3 |
      k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c} := by
    exact hS ((Set.to_countable {S : Finset ℕ | k ∈ S}).measurableSet)
  have heq : {W : ℤ → Fin 3 | ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k) ∧
        ∀ j ≤ M - N,
          L (shiftedStream W M) (M - N + k) ≤ L (shiftedStream W M) j} =
      ⋂ M : ℕ, ⋂ (_ : N ≤ M), ⋂ k : ℕ,
        ({W | k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c}ᶜ ∪
          ({W | minL (shiftedStream W M) (M - N + k) =
              L (shiftedStream W M) (M - N + k)} ∩
            ⋂ j : ℕ, ⋂ (_ : j ≤ M - N),
              {W | L (shiftedStream W M) (M - N + k) ≤
                L (shiftedStream W M) j})) := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      Set.mem_inter_iff, ← imp_iff_not_or]
  rw [heq]
  exact MeasurableSet.iInter (fun M => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun k => (hmem k).compl.union
      ((measurableSet_eq_fun (measurable_relMinL M _) (measurable_relL M _)).inter
        (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
          measurableSet_le (measurable_relL M _) (measurable_relL M j))))))))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Read a block-concatenation letter, using zero only beyond the finite concatenation. -/
@[expose] def uibhbotDefaultBlockLetterRel (f : ℕ → List (Fin 3)) (n : ℕ) : Fin 3 :=
  (((List.range (n + 1)).flatMap f)[n]?).getD 0

private theorem measurable_uibhbotDefaultBlockLetterRel (n : ℕ) :
    Measurable (fun f : ℕ → List (Fin 3) => uibhbotDefaultBlockLetterRel f n) := by
  let pref : (ℕ → List (Fin 3)) → (Fin (n + 1) → List (Fin 3)) :=
    fun f i => f i.val
  let ext : (Fin (n + 1) → List (Fin 3)) → ℕ → List (Fin 3) :=
    fun a i => if hi : i < n + 1 then a ⟨i, hi⟩ else []
  have hp : Measurable pref := Measurable.of_eval (fun i => measurable_pi_apply i.val)
  have he : (fun f => uibhbotDefaultBlockLetterRel f n) =
      (fun a => uibhbotDefaultBlockLetterRel (ext a) n) ∘ pref := by
    funext f
    apply congrArg (fun xs : List (Fin 3) => (xs[n]?).getD 0)
    apply List.flatMap_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    dsimp only [ext, pref]
    rw [dite_eq_left hi']
  rw [he]
  exact (measurable_of_countable _).comp hp





@[expose] def uibhbotCodeWordRel (w : ℤ → List (Fin 3)) (t : ℤ) : Fin 3 :=
  if 0 ≤ t then
    uibhbotDefaultBlockLetterRel (fun k => w (k : ℤ)) t.toNat
  else
    uibhbotDefaultBlockLetterRel (fun k => (w (-(k : ℤ) - 1)).reverse) (-t - 1).toNat

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The total code extension is measurable on the word-family law's actual carrier. -/
theorem measurable_uibhbotCodeWordRel : Measurable uibhbotCodeWordRel := by
  apply Measurable.of_eval
  intro t
  by_cases ht : 0 ≤ t
  · have hp : Measurable (fun w : ℤ → List (Fin 3) => fun k : ℕ => w (k : ℤ)) :=
      Measurable.of_eval (fun k => measurable_pi_apply (k : ℤ))
    simpa only [uibhbotCodeWordRel, ite_eq_left ht, Function.comp_def] using
      (measurable_uibhbotDefaultBlockLetterRel t.toNat).comp hp
  · have hp : Measurable (fun w : ℤ → List (Fin 3) =>
        fun k : ℕ => (w (-(k : ℤ) - 1)).reverse) :=
      Measurable.of_eval (fun k => (measurable_of_countable List.reverse).comp
        (measurable_pi_apply (-(k : ℤ) - 1)))
    simpa only [uibhbotCodeWordRel, ite_eq_right ht, Function.comp_def] using
      (measurable_uibhbotDefaultBlockLetterRel (-t - 1).toNat).comp hp

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The total measurable extension agrees with the nonempty-block code construction. -/
theorem uibhbotCodeWordRel_eq (w : ℤ → List (Fin 3))
    (hw : ∀ k : ℤ, 1 ≤ (w k).length) :
    uibhbotCodeWordRel w = uibhbotCodeWord w hw := by
  have hblock (f : ℕ → List (Fin 3)) (hf : ∀ k, 1 ≤ (f k).length) (n : ℕ) :
      uibhbotDefaultBlockLetterRel f n = uibhbotBlockLetter f hf n := by
    unfold uibhbotDefaultBlockLetterRel uibhbotBlockLetter
    have hlen (k : ℕ) : k ≤ ((List.range k).flatMap f).length := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [List.range_succ, List.flatMap_append]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
          have := hf k
          omega
    rw [List.getElem?_eq_getElem (by have := hlen (n + 1); omega)]
    rfl
  funext t
  by_cases ht : 0 ≤ t
  · simp only [uibhbotCodeWordRel, uibhbotCodeWord, ite_eq_left ht]
    exact hblock _ _ _
  · simp only [uibhbotCodeWordRel, uibhbotCodeWord, ite_eq_right ht]
    exact hblock _ _ _

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Almost surely the measurable code extension is the original stopped-block code. -/
theorem uibhbotWordFamilyLaw_ae_codeWordRel :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        uibhbotCodeWordRel w = uibhbotCodeWord w (fun k => (hw k).1) := by
  filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw
  exact ⟨hw, uibhbotCodeWordRel_eq w (fun k => (hw k).1)⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The code-space pushforward of the word-family probability law, using its total
measurable extension. This is an encoding law, not the framed-ball law. -/
@[expose] noncomputable def uibhbotCodeLawRel : ProbabilityMeasure (ℤ → Fin 3) := by
  exact ⟨uibhbotWordFamilyLaw.map uibhbotCodeWordRel, inferInstance⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The encoding probability measure is the genuine measurable pushforward. -/
theorem uibhbotCodeLawRel_apply (A : Set (ℤ → Fin 3)) (hA : MeasurableSet A) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) A =
      uibhbotWordFamilyLaw (uibhbotCodeWordRel ⁻¹' A) := by
  exact Measure.map_apply measurable_uibhbotCodeWordRel hA

private theorem relDirectedMap_heq {s t : State} (hs : s = t)
    (M : DirectedMapWithMissing (StageDart s.nextEdge))
    (T : DirectedMapWithMissing (StageDart t.nextEdge))
    (I : DirectedMapWithMissingIso M T)
    (hI : ∀ d, (I.toEquiv d).1.val = d.1.val ∧ (I.toEquiv d).2 = d.2)
    (ho : HEq M.outer T.outer) : HEq M T := by
  cases hs
  have hi : I.toEquiv = Equiv.refl _ := by
    apply Equiv.ext
    intro d
    apply Prod.ext
    · exact Fin.ext (hI d).1
    · exact (hI d).2
  have hr : M.rot = T.rot := by
    apply Equiv.ext
    intro d
    simpa only [hi, Equiv.refl_apply] using I.rot_comm d
  have he : M.edgeInv = T.edgeInv := by
    apply Equiv.ext
    intro d
    simpa only [hi, Equiv.refl_apply] using I.edgeInv_comm d
  have hm : M.missing = T.missing := by
    funext d
    exact propext (by simpa only [hi, Equiv.refl_apply] using (I.missing_iff d).symm)
  have ht : M.tail = T.tail := by
    funext d
    exact propext (by simpa only [hi, Equiv.refl_apply] using (I.tail_iff d).symm)
  have ho' : M.outer = T.outer := eq_of_heq ho
  have hcomb (A B : CombinatorialMap (StageDart s.nextEdge))
      (he : A.edgeInv = B.edgeInv) (hr : A.rot = B.rot) : A = B := by
    cases A
    cases B
    cases he
    cases hr
    rfl
  have hc := hcomb _ _ he hr
  cases M
  cases T
  cases hc
  cases hm
  cases ht
  cases ho'
  rfl

private theorem relStageMap_data_eq (u v : ℕ → Fin 3) (m : ℕ)
    (h : ∀ i < m, u i = v i) :
    (⟨kmswStage u m, kmswStageDirectedMap u m⟩ :
      Σ s : State, DirectedMapWithMissing (StageDart s.nextEdge)) =
        ⟨kmswStage v m, kmswStageDirectedMap v m⟩ := by
  have hs := kmswStage_congr h
  apply Sigma.ext hs
  apply relDirectedMap_heq hs _ _ (kmswStageDirectedMapIsoOfPrefix u v m h)
  · exact kmswStageDirectedMapIsoOfPrefix_val u v m h
  · change HEq (stageULHeadDart u m) (stageULHeadDart v m)
    have hhead {s t : State} (h : s = t) (hn : s.UL ≠ []) (hn' : t.UL ≠ [])
        (hb : s.UL.head hn < s.nextEdge) (hb' : t.UL.head hn' < t.nextEdge) :
        HEq ((⟨s.UL.head hn, hb⟩, false) : StageDart s.nextEdge)
          ((⟨t.UL.head hn', hb'⟩, false) : StageDart t.nextEdge) := by
      cases h
      rfl
    exact hhead hs _ _ _ _

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A total class function on finite stage data. Invalid local data use the fixed
class; valid data use the induced framed ball at the specified missing dart. -/
@[expose] noncomputable def uibhbotStageDataBallClassRel
    (p : Σ s : State, DirectedMapWithMissing (StageDart s.nextEdge))
    (r e : ℕ) (b : Bool) : FramedBallClass := by
  classical
  let s := p.1
  let M := p.2
  exact if he : e < s.nextEdge then
    let d : StageDart s.nextEdge := (⟨e, he⟩, b)
    let S := kmswStageBallDarts (fun _ _ => True) s r (stageEndpoint s (edgeFlip _ d))
    if hf : ∀ x, x ∈ S → M.edgeInv x ∈ S then
      if hv : M.toCombinatorialMap.IsPlanar ∧
          (@CombinatorialMap.IsConnected {x : StageDart s.nextEdge // x ∈ S}
            (Finset.Subtype.fintype S) (fun a b => a.instDecidableEq b)
            (inducedCombinatorialMap M.toCombinatorialMap S hf)) ∧
          d ∈ S ∧ M.missing d then
        uibhbotCapturedStageBallClass
          (uibhbotInducedLocalFramedBallRel M S hf hv.1 hv.2.1 ⟨d, hv.2.2.1⟩ hv.2.2.2)
      else uibhbotOffCaptureClassRel
    else uibhbotOffCaptureClassRel
  else uibhbotOffCaptureClassRel

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A certified capture's class equals the class computed from its finite stage and
the raw index of its root dart. No global rotation hypothesis is needed. -/
theorem UIBHBOTCertifiedRootCapture.class_eq_stageData {W : ℤ → Fin 3} {r : ℕ}
    (C : UIBHBOTCertifiedRootCapture W r) (hr : 0 < r) :
    uibhbotCapturedStageBallClass (C.framedBall hr) =
      uibhbotStageDataBallClassRel
        ⟨kmswStage (shiftedStream W C.N) C.m,
          kmswStageDirectedMap (shiftedStream W C.N) C.m⟩ r C.dart.1.val C.dart.2 := by
  classical
  let u := shiftedStream W C.N
  let s := kmswStage u C.m
  let M := kmswStageDirectedMap u C.m
  let d := C.dart
  let S := kmswStageBallDarts (fun _ _ => True) s r (stageEndpoint s (edgeFlip _ d))
  have hf : ∀ x, x ∈ S → M.edgeInv x ∈ S := by
    intro x hx
    exact (kmswStageBallDarts_edgeFlip (fun _ _ => True) s r
      (stageEndpoint s (edgeFlip _ d)) x).mp hx
  have hv : M.toCombinatorialMap.IsPlanar ∧
      (@CombinatorialMap.IsConnected {x : StageDart s.nextEdge // x ∈ S}
            (Finset.Subtype.fintype S) (fun a b => a.instDecidableEq b)
            (inducedCombinatorialMap M.toCombinatorialMap S hf)) ∧
      d ∈ S ∧ M.missing d :=
    ⟨kmswMap_isPlanar u C.m,
      kmswStageBallCombinatorialMap_rooted_isConnected u C.m r d hr,
      (kmswStageBallRootEdge_mem u C.m r d hr).1, C.missing⟩
  unfold uibhbotStageDataBallClassRel
  rw [dite_eq_left C.dart.1.isLt]
  dsimp only
  rw [dite_eq_left hf, dite_eq_left hv]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Equality on the stage window preserves the finite-stage class, including its
rotation, tags, frame and surviving outer face. -/
theorem uibhbotStageDataBallClassRel_eq_of_window (W V : ℤ → Fin 3)
    (N m r e : ℕ) (b : Bool)
    (h : ∀ i < m, W ((i : ℤ) - N) = V ((i : ℤ) - N)) :
    uibhbotStageDataBallClassRel
        ⟨kmswStage (shiftedStream W N) m, kmswStageDirectedMap (shiftedStream W N) m⟩
        r e b =
      uibhbotStageDataBallClassRel
        ⟨kmswStage (shiftedStream V N) m, kmswStageDirectedMap (shiftedStream V N) m⟩
        r e b := by
  exact congrArg (fun p => uibhbotStageDataBallClassRel p r e b)
    (relStageMap_data_eq (shiftedStream W N) (shiftedStream V N) m h)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The finite-stage class depends only on the stage window, so it is measurable
for every fixed window and raw dart index, with no rotation hypothesis. -/
theorem measurable_uibhbotStageDataBallClassRel (N m r e : ℕ) (b : Bool) :
    Measurable (fun W : ℤ → Fin 3 => uibhbotStageDataBallClassRel
      ⟨kmswStage (shiftedStream W N) m, kmswStageDirectedMap (shiftedStream W N) m⟩
      r e b) := by
  have hm : Measurable (fun u : ℕ → Fin 3 => uibhbotStageDataBallClassRel
      ⟨kmswStage u m, kmswStageDirectedMap u m⟩ r e b) := by
    apply measurable_of_factors_prefix m
    intro u v h
    exact congrArg (fun p => uibhbotStageDataBallClassRel p r e b)
      (relStageMap_data_eq u v m h)
  exact hm.comp (measurable_relShift N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
For fixed indices the relaxed event, seam certificates and local class fibre
have a measurable intersection. The global root-identification clauses remain
separate from this event. -/
theorem measurableSet_uibhbotRelaxedCapture_stageClass
    (N m r c e : ℕ) (b : Bool) (B : FramedBallClass) :
    MeasurableSet {W : ℤ → Fin 3 |
      kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c ∧
      (∀ M, N ≤ M →
        ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
          minL (shiftedStream W M) (M - N + k) =
            L (shiftedStream W M) (M - N + k) ∧
          ∀ j ≤ M - N,
            L (shiftedStream W M) (M - N + k) ≤ L (shiftedStream W M) j) ∧
      uibhbotStageDataBallClassRel
        ⟨kmswStage (shiftedStream W N) m, kmswStageDirectedMap (shiftedStream W N) m⟩
        r e b = B} := by
  have he := (measurableSet_kmswWindowCaptureEventStrongRel m (r + 1) c).preimage
    (measurable_relShift N)
  have hc : MeasurableSet {W : ℤ → Fin 3 | uibhbotStageDataBallClassRel
      ⟨kmswStage (shiftedStream W N) m, kmswStageDirectedMap (shiftedStream W N) m⟩
      r e b = B} :=
    (measurable_uibhbotStageDataBallClassRel N m r e b)
      ((Set.to_countable {B}).measurableSet)
  exact he.inter ((measurableSet_uibhbotRelaxedCapture_certificates N m r c).inter hc)

private theorem relPatch_congr (u v : ℕ → Fin 3) (s m : ℕ)
    (h : ∀ i < s + m, u i = v i) :
    kmswWindowPatchData u s m = kmswWindowPatchData v s m := by
  induction m with
  | zero =>
    simp only [kmswWindowPatchData,
      kmswStage_congr (w := u) (w' := v) (n := s) (fun i hi => h i (by omega))]
  | succ m ih =>
    have hg := kmswStage_congr (w := u) (w' := v) (n := s + m)
      (fun i hi => h i (by omega))
    have hf := kmswStage_congr (w := fun i => u (s + i))
      (w' := fun i => v (s + i)) (n := m) (fun i hi => h _ (by omega))
    simp only [kmswWindowPatchData, hg, hf, h (s + m) (by omega),
      ih (fun i hi => h i (by omega))]

private theorem relPatchVertex_congr (u v : ℕ → Fin 3) (s m : ℕ)
    (h : ∀ i < s + m, u i = v i) :
    kmswWindowPatchVertexMap u s m = kmswWindowPatchVertexMap v s m := by
  induction m with
  | zero =>
    simp only [kmswWindowPatchVertexMap,
      kmswStage_congr (w := u) (w' := v) (n := s) (fun i hi => h i (by omega))]
  | succ m ih =>
    have hg := kmswStage_congr (w := u) (w' := v) (n := s + m)
      (fun i hi => h i (by omega))
    have hf := kmswStage_congr (w := fun i => u (s + i))
      (w' := fun i => v (s + i)) (n := m) (fun i hi => h _ (by omega))
    simp only [kmswWindowPatchVertexMap, hg, hf, h (s + m) (by omega),
      relPatch_congr u v s m (fun i hi => h i (by omega)),
      ih (fun i hi => h i (by omega))]

private theorem measurable_relStageFn {β : Type*} [MeasurableSpace β]
    (f : State → β) (N m : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => f (kmswStage (shiftedStream W N) m)) :=
  (measurable_of_factors_prefix m _ (fun _ _ h => congrArg f (kmswStage_congr h))).comp
    (measurable_relShift N)

private theorem measurable_relEdgeTrans (N M e : ℕ) (h : N ≤ M) :
    Measurable (fun W : ℤ → Fin 3 => wholePlaneEdgeTrans W N M h e) := by
  change Measurable ((fun u => kmswWindowEdgeMapInf u (M - N) e) ∘
    (fun W => shiftedStream W M))
  apply Measurable.comp _ (measurable_relShift M)
  apply measurable_of_factors_prefix (M - N + e)
  intro u v huv
  exact congrArg (fun d : KMSWWindowPatchData => d.φ e)
    (relPatch_congr u v (M - N) e huv)

private theorem measurable_relVertexTrans (N M v : ℕ) (h : N ≤ M) :
    Measurable (fun W : ℤ → Fin 3 => wholePlaneVertexTrans W N M h v) := by
  change Measurable ((fun u => kmswWindowVertexMapInf u (M - N) v) ∘
    (fun W => shiftedStream W M))
  apply Measurable.comp _ (measurable_relShift M)
  apply measurable_of_factors_prefix (M - N + (4 * v + 1))
  intro u u' huu
  exact congrFun (relPatchVertex_congr u u' (M - N) (4 * v + 1) huu) v

private theorem measurable_relEdgeEq (N M e f : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => wholePlaneEdgeι W N e = wholePlaneEdgeι W M f) := by
  have heq : (fun W : ℤ → Fin 3 =>
      wholePlaneEdgeι W N e = wholePlaneEdgeι W M f) =
      (fun W => ∃ K, ∃ hN : N ≤ K, ∃ hM : M ≤ K,
        wholePlaneEdgeTrans W N K hN e = wholePlaneEdgeTrans W M K hM f) := by
    funext W
    exact propext ⟨fun h => Quotient.exact h, fun h =>
      Quotient.sound (s := wholePlaneEdgeSetoid W) h⟩
  rw [heq]
  exact Measurable.exists (fun K => Measurable.exists (fun hN =>
    Measurable.exists (fun hM => measurableSet_setOfPred.mp
      (measurableSet_eq_fun (measurable_relEdgeTrans N K e hN)
        (measurable_relEdgeTrans M K f hM)))))

private theorem measurable_relVertexEq (N M v z : ℕ) :
    Measurable (fun W : ℤ → Fin 3 =>
      wholePlaneVertexι W N v = wholePlaneVertexι W M z) := by
  have heq : (fun W : ℤ → Fin 3 =>
      wholePlaneVertexι W N v = wholePlaneVertexι W M z) =
      (fun W => ∃ K, ∃ hN : N ≤ K, ∃ hM : M ≤ K,
        wholePlaneVertexTrans W N K hN v = wholePlaneVertexTrans W M K hM z) := by
    funext W
    exact propext ⟨fun h => Quotient.exact h, fun h =>
      Quotient.sound (s := wholePlaneVertexSetoid W) h⟩
  rw [heq]
  exact Measurable.exists (fun K => Measurable.exists (fun hN =>
    Measurable.exists (fun hM => measurableSet_setOfPred.mp
      (measurableSet_eq_fun (measurable_relVertexTrans N K v hN)
        (measurable_relVertexTrans M K z hM)))))

private theorem measurable_relIndexed {β : Type*} [MeasurableSpace β]
    (f : ℕ → (ℤ → Fin 3) → β) (g : (ℤ → Fin 3) → ℕ)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) :
    Measurable (fun W => f (g W) W) :=
  (measurable_from_prod_countable_left
    (f := fun p : (ℤ → Fin 3) × ℕ => f p.2 p.1) hf).comp
      (measurable_id.prodMk hg)

private theorem measurable_relRootIndex :
    Measurable (fun W : ℤ → Fin 3 => kmswLLCreatedEdge (shiftedStream W 1) 1) :=
  measurable_relStageFn (fun s => s.nextEdge - 1) 1 1

private theorem measurable_relRootWest :
    Measurable (fun W : ℤ → Fin 3 =>
      edgeWest (shiftedStream W 1) (kmswLLCreatedEdge (shiftedStream W 1) 1)) := by
  exact measurable_relIndexed (fun e W => edgeWest (shiftedStream W 1) e) _
    (fun e => measurable_relStageFn (fun s => s.west e) 1 e)
    measurable_relRootIndex

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The two global root-identification clauses are measurable at fixed raw indices. -/
theorem measurableSet_uibhbotRootIdentificationRel (N c e : ℕ) :
    MeasurableSet {W : ℤ → Fin 3 |
      wholePlaneVertexι W N c = uibhbotRootFirstVertex W ∧
      wholePlaneEdgeι W N e = uibhbotRootEdge W} := by
  have hv := measurable_relIndexed
    (fun z W => wholePlaneVertexι W N c = wholePlaneVertexι W 1 z) _
    (fun z => measurable_relVertexEq N 1 c z) measurable_relRootWest
  have he := measurable_relIndexed
    (fun f W => wholePlaneEdgeι W N e = wholePlaneEdgeι W 1 f) _
    (fun f => measurable_relEdgeEq N 1 e f) measurable_relRootIndex
  exact (hv.and he).setOf

private theorem measurable_relFiniteIncidence (N : ℕ) :
    Measurable (fun W : ℤ → Fin 3 => KMSWFiniteIncidence (shiftedStream W N)) := by
  have heq : (fun W : ℤ → Fin 3 => KMSWFiniteIncidence (shiftedStream W N)) =
      (fun W => ∀ v : ℕ, ∃ b : ℕ, ∀ e n : ℕ,
        e < (kmswStage (shiftedStream W N) n).nextEdge ∧
          ((kmswStage (shiftedStream W N) n).west e = v ∨
            (kmswStage (shiftedStream W N) n).east e = v) → e ≤ b) := by
    funext W
    apply propext
    simp only [KMSWFiniteIncidence, Set.finite_iff_bddAbove, BddAbove,
      upperBounds, Set.Nonempty, Set.mem_ofPred_eq, forall_exists_index]
  rw [heq]
  apply Measurable.forall
  intro v
  apply Measurable.exists
  intro b
  apply Measurable.forall
  intro e
  apply Measurable.forall
  intro n
  exact (measurable_relStageFn (fun s =>
    e < s.nextEdge ∧ (s.west e = v ∨ s.east e = v)) N n).imp measurable_const

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The deterministic rotation gate is measurable in the bi-infinite code. -/
theorem measurableSet_uibhbotRotationHypothesisRel :
    MeasurableSet {W : ℤ → Fin 3 | WholePlaneRotationHypothesis W} := by
  apply Measurable.setOf
  apply Measurable.and (Measurable.forall measurable_relFiniteIncidence)
  apply Measurable.forall
  intro N
  apply Measurable.forall
  intro v
  apply Measurable.exists
  intro M
  apply Measurable.exists
  intro hNM
  apply Measurable.forall
  intro M'
  apply Measurable.forall
  intro hMM'
  have hv := measurable_relIndexed
    (fun z W => wholePlaneVertexTrans W M M' hMM' z) _
    (fun z => measurable_relVertexTrans M M' z hMM')
    (measurable_relVertexTrans N M v hNM)
  exact measurableSet_setOfPred.mp (measurableSet_le
    (measurable_relStageFn State.nextVertex M' (M' - M))
    hv)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The complete certified-capture event at fixed countable raw indices. -/
@[expose] def uibhbotFixedCaptureRel (W : ℤ → Fin 3) (r N m c e : ℕ)
    (b : Bool) : Prop :=
  kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c ∧
  (∀ M, N ≤ M →
    ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
      minL (shiftedStream W M) (M - N + k) =
        L (shiftedStream W M) (M - N + k) ∧
      ∀ j ≤ M - N,
        L (shiftedStream W M) (M - N + k) ≤ L (shiftedStream W M) j) ∧
  (wholePlaneVertexι W N c = uibhbotRootFirstVertex W ∧
    wholePlaneEdgeι W N e = uibhbotRootEdge W) ∧
  (e < (kmswStage (shiftedStream W N) m).nextEdge ∧
    (if b then (kmswStage (shiftedStream W N) m).west e
      else (kmswStage (shiftedStream W N) m).east e) = c ∧
    (kmswStage (shiftedStream W N) m).present e = false)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The fixed-index event includes all certificate fields, including global roots. -/
theorem uibhbotFixedCaptureRel_iff (W : ℤ → Fin 3) (r N m c e : ℕ) (b : Bool) :
    uibhbotFixedCaptureRel W r N m c e b ↔
      ∃ C : UIBHBOTCertifiedRootCapture W r,
        C.N = N ∧ C.m = m ∧ C.c = c ∧ C.dart.1.val = e ∧ C.dart.2 = b := by
  constructor
  · rintro ⟨hev, hs, ⟨hc, hroot⟩, he, hd, hm⟩
    have hd' : stageEndpoint (kmswStage (shiftedStream W N) m)
        (edgeFlip _ ((⟨e, he⟩, b) : StageDart _)) = c := by
      cases b <;> exact hd
    exact ⟨⟨N, m, c, hev, hs, hc, (⟨e, he⟩, b), hd', hroot, hm⟩,
      rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨C, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨C.event, C.seams, ⟨C.center, C.root⟩, C.dart.1.isLt, ?_, C.missing⟩
    have hd := C.dart_center
    change (if !C.dart.2 then (kmswStage (shiftedStream W C.N) C.m).east C.dart.1.val
      else (kmswStage (shiftedStream W C.N) C.m).west C.dart.1.val) = C.c at hd
    cases hb : C.dart.2 <;> simpa [hb] using hd

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every complete fixed-index certified-capture event is measurable. -/
theorem measurableSet_uibhbotFixedCaptureRel (r N m c e : ℕ) (b : Bool) :
    MeasurableSet {W : ℤ → Fin 3 | uibhbotFixedCaptureRel W r N m c e b} := by
  have he := (measurableSet_kmswWindowCaptureEventStrongRel m (r + 1) c).preimage
    (measurable_relShift N)
  have hl := (measurable_relStageFn (fun s => e < s.nextEdge ∧
    (if b then s.west e else s.east e) = c ∧ s.present e = false) N m).setOf
  exact he.inter ((measurableSet_uibhbotRelaxedCapture_certificates N m r c).inter
    ((measurableSet_uibhbotRootIdentificationRel N c e).inter hl))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Certified capture existence is a countable union of complete fixed-index events. -/
theorem uibhbotCertifiedRootCapture_nonempty_iff (W : ℤ → Fin 3) (r : ℕ) :
    Nonempty (UIBHBOTCertifiedRootCapture W r) ↔
      ∃ N m c e b, uibhbotFixedCaptureRel W r N m c e b := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.N, C.m, C.c, C.dart.1.val, C.dart.2,
      (uibhbotFixedCaptureRel_iff W r _ _ _ _ _).mpr
        ⟨C, rfl, rfl, rfl, rfl, rfl⟩⟩
  · rintro ⟨N, m, c, e, b, h⟩
    obtain ⟨C, _⟩ := (uibhbotFixedCaptureRel_iff W r N m c e b).mp h
    exact ⟨C⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The selector's rotation-and-capture event is measurable on code space. -/
theorem measurableSet_uibhbotBallClassRel_event (r : ℕ) :
    MeasurableSet {W : ℤ → Fin 3 | WholePlaneRotationHypothesis W ∧
      Nonempty (UIBHBOTCertifiedRootCapture W r)} := by
  have hc : MeasurableSet {W : ℤ → Fin 3 |
      Nonempty (UIBHBOTCertifiedRootCapture W r)} := by
    simp_rw [uibhbotCertifiedRootCapture_nonempty_iff]
    exact (Measurable.exists (fun N => Measurable.exists (fun m =>
      Measurable.exists (fun c => Measurable.exists (fun e =>
        Measurable.exists (fun b => measurableSet_setOfPred.mp
          (measurableSet_uibhbotFixedCaptureRel r N m c e b))))))).setOf
  exact measurableSet_uibhbotRotationHypothesisRel.inter hc

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
On the measurable rotation-and-capture event, class fibres are countable unions
of complete fixed-index capture events intersected with finite-window fibres. -/
theorem uibhbotBallClassRel_event_fibre (r : ℕ) (hr : 0 < r) (B : FramedBallClass) :
    {W : ℤ → Fin 3 | (WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧ uibhbotBallClassRel W r hr = B} =
      ⋃ N : ℕ, ⋃ m : ℕ, ⋃ c : ℕ, ⋃ e : ℕ, ⋃ b : Bool,
        ({W | uibhbotFixedCaptureRel W r N m c e b} ∩
          {W | WholePlaneRotationHypothesis W ∧
            Nonempty (UIBHBOTCertifiedRootCapture W r)}) ∩
          {W | uibhbotStageDataBallClassRel
            ⟨kmswStage (shiftedStream W N) m,
              kmswStageDirectedMap (shiftedStream W N) m⟩ r e b = B} := by
  ext W
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨H, ⟨C⟩⟩, hB⟩
    refine ⟨C.N, C.m, C.c, C.dart.1.val, C.dart.2, ⟨?_, H, ⟨C⟩⟩, ?_⟩
    · exact (uibhbotFixedCaptureRel_iff W r _ _ _ _ _).mpr
        ⟨C, rfl, rfl, rfl, rfl, rfl⟩
    · exact (C.class_eq_stageData hr).symm.trans
        ((uibhbotBallClassRel_eq_capture W H r hr C).symm.trans hB)
  · rintro ⟨N, m, c, e, b, ⟨hcap, H, hne⟩, hB⟩
    rcases (uibhbotFixedCaptureRel_iff W r N m c e b).mp hcap with
      ⟨C, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨⟨H, hne⟩, (uibhbotBallClassRel_eq_capture W H r hr C).trans
      ((C.class_eq_stageData hr).trans hB)⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The total canonical class selector, with its explicit off-event default, is measurable. -/
theorem measurable_uibhbotBallClassRel (r : ℕ) (hr : 0 < r) :
    Measurable (fun W : ℤ → Fin 3 => uibhbotBallClassRel W r hr) := by
  apply measurable_to_countable'
  intro B
  have hE := measurableSet_uibhbotBallClassRel_event r
  have hf : MeasurableSet {W : ℤ → Fin 3 | (WholePlaneRotationHypothesis W ∧
      Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧ uibhbotBallClassRel W r hr = B} := by
    rw [uibhbotBallClassRel_event_fibre r hr B]
    exact MeasurableSet.iUnion (fun N => MeasurableSet.iUnion (fun m =>
      MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun e =>
        MeasurableSet.iUnion (fun b =>
          ((measurableSet_uibhbotFixedCaptureRel r N m c e b).inter hE).inter
            ((measurable_uibhbotStageDataBallClassRel N m r e b)
              ((Set.to_countable {B}).measurableSet)))))))
  have hd : MeasurableSet {W : ℤ → Fin 3 | uibhbotOffCaptureClassRel = B} :=
    (measurable_const : Measurable (fun _ : ℤ → Fin 3 =>
      uibhbotOffCaptureClassRel = B)).setOf
  have heq : {W : ℤ → Fin 3 | uibhbotBallClassRel W r hr = B} =
      {W | (WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧ uibhbotBallClassRel W r hr = B} ∪
      ({W | WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)}ᶜ ∩
        {W | uibhbotOffCaptureClassRel = B}) := by
    ext W
    classical
    by_cases h : WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, h, true_and, not_true, false_and, or_false]
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, h, false_and, not_false_eq_true, true_and, false_or]
      have hoff : uibhbotBallClassRel W r hr = uibhbotOffCaptureClassRel :=
        dite_eq_right h
      rw [hoff]
  change MeasurableSet {W : ℤ → Fin 3 | uibhbotBallClassRel W r hr = B}
  rw [heq]
  exact hf.union (hE.compl.inter hd)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The probability law of the positive-radius canonical framed class, obtained from
its measurable code-space selector. This is not a convergence theorem. -/
@[expose] noncomputable def uibhbotBSBallLaw (r : ℕ) (hr : 0 < r) :
    ProbabilityMeasure FramedBallClass :=
  uibhbotCodeLawRel.map (fun W => uibhbotBallClassRel W r hr)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The ball law evaluates by the measurable code-space pushforward formula. -/
theorem uibhbotBSBallLaw_apply (r : ℕ) (hr : 0 < r)
    (A : Set FramedBallClass) (hA : MeasurableSet A) :
    (uibhbotBSBallLaw r hr : Measure FramedBallClass) A =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3))
        ((fun W => uibhbotBallClassRel W r hr) ⁻¹' A) :=
  Measure.map_apply (measurable_uibhbotBallClassRel r hr) hA

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The measurable rotation-and-capture event has full code-law measure. -/
theorem uibhbotCodeLawRel_ae_ballClassRel_event (r : ℕ) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      WholePlaneRotationHypothesis W ∧ Nonempty (UIBHBOTCertifiedRootCapture W r) := by
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel,
    WholePlaneRotationHypothesis W ∧ Nonempty (UIBHBOTCertifiedRootCapture W r)
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable
    (measurableSet_uibhbotBallClassRel_event r)).mpr
  filter_upwards [uibhbotWordFamilyLaw_ae_certifiedRootCapture] with w hw
  obtain ⟨hw, H, hcap⟩ := hw
  rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
  exact ⟨H, hcap r⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The ball law is also the pushforward of the original word-family law. -/
theorem uibhbotBSBallLaw_apply_wordFamily (r : ℕ) (hr : 0 < r)
    (A : Set FramedBallClass) (hA : MeasurableSet A) :
    (uibhbotBSBallLaw r hr : Measure FramedBallClass) A =
      uibhbotWordFamilyLaw {w | uibhbotBallClassRel (uibhbotCodeWordRel w) r hr ∈ A} := by
  rw [uibhbotBSBallLaw_apply r hr A hA,
    uibhbotCodeLawRel_apply _ (measurable_uibhbotBallClassRel r hr hA)]
  rfl

end DirectedDistances.PaperProofs.Section5
