module

public import DirectedDistances.KMSW.KMSWWholePlaneBallCapture
public import DirectedDistances.KMSW.KMSWWholePlaneRotation
public import DirectedDistances.KMSW.UIBHBOTWholePlaneWord
public import DirectedDistances.KMSW.UIBHBOTAlmostSure
public import DirectedDistances.PlanarMap.KMSWStageFramedBall
public import DirectedDistances.PlanarMap.FramedBallCountable
import DirectedDistances.KMSW.KMSWWholePlaneFaces
import DirectedDistances.KMSW.StageBoundaryMap

/-! Positive-radius rooted UIBHBOT vertex balls toward Proposition 5.16 under local topology.
The whole-plane colimit supplies all-geometric vertex balls and a root-edge
candidate; it does not yet supply the finite rooted plane-map ball or its law. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk MeasureTheory

private theorem uibhbotCaptureSucc_event (u : ℕ → Fin 3) (m r c : ℕ)
    (hevent : kmswWindowCaptureEvent u m (r + 1) c) :
    kmswWindowCaptureEvent u m r c := by
  rcases hevent with ⟨hc, hball, hinner⟩
  refine ⟨hc, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) (r + 1) c := by
      exact kmswStageBallVertices_mono (fun _ _ => True) (kmswStage u m)
        (c := c) (by omega) hv
    exact hball v hv'
  · intro v hv
    have hv' : v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) ((r + 1) - 1) c := by
      rw [show (r + 1) - 1 = r by omega]
      exact kmswStageBallVertices_mono (fun _ _ => True) (kmswStage u m)
        (c := c) (Nat.sub_le r 1) hv
    exact hinner v hv'

private theorem uibhbotCaptureSucc_strongRel (u : ℕ → Fin 3) (m r c : ℕ)
    (hevent : kmswWindowCaptureEvent u m (r + 1) c) :
    kmswWindowCaptureEventStrongRel u m r c := by
  refine ⟨kmswWindowCaptureEventRel_of_captureEvent u m r c
    (uibhbotCaptureSucc_event u m r c hevent), ?_⟩
  intro v hv
  have hv' : v ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage u m) ((r + 1) - 1) c := by
    rw [show (r + 1) - 1 = r by omega]
    exact hv
  exact hevent.2.2 v hv'

private theorem uibhbotCaptureSucc_strong (u : ℕ → Fin 3) (m r c : ℕ)
    (hevent : kmswWindowCaptureEvent u m (r + 1) c) :
    kmswWindowCaptureEventStrong u m r c := by
  refine ⟨uibhbotCaptureSucc_event u m r c hevent, ?_⟩
  intro v hv
  have hv' : v ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage u m) ((r + 1) - 1) c := by
    rw [show (r + 1) - 1 = r by omega]
    exact hv
  exact hevent.2.2 v hv'

private theorem uibhbotCapturedVertex_fresh (W : ℤ → Fin 3) (r N m c M v : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hv : v ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (shiftedStream W N) m) r c) (hNM : N ≤ M) :
    wholePlaneFresh W N M hNM v := by
  classical
  have hcapture := uibhbotCaptureSucc_event (shiftedStream W N) m r c hevent
  have hvertex := hcapture.2.1 v hv
  have hvbound : v < (kmswStage (shiftedStream W N) m).nextVertex :=
    Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  by_contra hnot
  rcases (wholePlaneFresh_iff_windowSeam W N M hNM v).mp hnot with
    hsmall | ⟨k, hk, hcreate, hstep⟩
  · exact (Nat.not_lt_of_ge hvertex.1) hsmall
  · rcases hstep with hdown | hleft
    · by_cases hkm : k < m
      · exact ((hvertex.2 k hkm hcreate).1 hdown.1) hdown.2.1
      · have hmono := CutConverse.nextVertex_mono (shiftedStream W N)
          (Nat.le_of_not_gt hkm)
        omega
    · by_cases hkm : k < m
      · exact ((hvertex.2 k hkm hcreate).2 hleft.1) hleft.2.1
      · have hmono := CutConverse.nextVertex_mono (shiftedStream W N)
          (Nat.le_of_not_gt hkm)
        omega

private theorem uibhbotCapturedStageDart_rotation_agrees (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (r N m c : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hd : stageEndpoint (kmswStage (shiftedStream W N) m) d ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) m) r c) :
    wholePlaneRotation W H (wholePlaneDartι W N (d.1.val, d.2)) =
      wholePlaneDartι W N (kmswInfRot (shiftedStream W N) (H.1 N)
        (d.1.val, d.2)) := by
  apply wholePlaneRotation_ι_of_fresh
  intro M hNM
  have hfresh := uibhbotCapturedVertex_fresh W r N m c M
    (stageEndpoint (kmswStage (shiftedStream W N) m) d) hevent hd hNM
  simpa only [stageEndpoint, (edge_endpoints_eq (shiftedStream W N) d.1.isLt).1,
    (edge_endpoints_eq (shiftedStream W N) d.1.isLt).2] using hfresh

/- Copied verbatim from PaperProofs/Section5/DiskWindowFramedCapture.lean. -/
private theorem firstReturn_map_congr_of_invariant
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : Equiv.Perm α) (g : Equiv.Perm β) (S : Finset α) (T : Finset β)
    (U : Set α) (e : α → β)
    (hU : ∀ x, x ∈ U → f x ∈ U)
    (hcomm : ∀ x, x ∈ U → e (f x) = g (e x))
    (hmem : ∀ x, x ∈ U → (x ∈ S ↔ e x ∈ T))
    (x : S) (hxU : x.1 ∈ U) :
    e ((cyclicFirstReturn f S (finitePermutationReturn f S) x).1) =
      (cyclicFirstReturn g T (finitePermutationReturn g T)
        ⟨e x.1, (hmem x.1 hxU).mp x.2⟩).1 := by
  classical
  let hf := finitePermutationReturn f S
  let hg := finitePermutationReturn g T
  let y : T := ⟨e x.1, (hmem x.1 hxU).mp x.2⟩
  have hiterU : ∀ j, (f ^ j) x.1 ∈ U := by
    intro j
    induction j with
    | zero => simpa using hxU
    | succ j ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hU _ ih
  have hiter : ∀ j, e ((f ^ j) x.1) = (g ^ j) y.1 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply]
        rw [hcomm _ (hiterU j), ih]
  let kf := cyclicFirstReturnTime f S hf x
  let kg := cyclicFirstReturnTime g T hg y
  have htime : kf = kg := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : kg < kf := by omega
      have hspec := cyclicFirstReturnTime_spec g T hg y
      have hreturn : (f ^ kg) x.1 ∈ S := by
        apply (hmem _ (hiterU kg)).mpr
        rw [hiter kg]
        exact hspec.2.1
      exact (cyclicFirstReturnTime_spec f S hf x).2.2 kg hspec.1 hlt hreturn
    · by_contra hnot
      have hlt : kf < kg := by omega
      have hspec := cyclicFirstReturnTime_spec f S hf x
      have hreturn : (g ^ kf) y.1 ∈ T := by
        have h := (hmem _ (hiterU kf)).mp hspec.2.1
        rw [hiter kf] at h
        exact h
      exact (cyclicFirstReturnTime_spec g T hg y).2.2 kf hspec.1 hlt hreturn
  calc
    e ((cyclicFirstReturn f S hf x).1) = e ((f ^ kf) x.1) := by
      rw [(firstReturn_spec f S hf x).1]
    _ = (g ^ kf) y.1 := hiter kf
    _ = (g ^ kg) y.1 := by rw [htime]
    _ = (cyclicFirstReturn g T hg y).1 := (firstReturn_spec g T hg y).1.symm

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

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
Almost surely, every radius request has a captured radius-`r+1`
window for the UIBHBOT word. This repackages the existing eventual-capture -/
theorem uibhbotWordFamilyLaw_ae_radiusSuccCapture :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, DirectedDistances.RandomWalk.IsStoppedExcursionWord (w k),
        ∀ r : ℕ,
        ∃ N m c,
          kmswWindowCaptureEventStrongRel
            (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) m
            (r + 1) c := by
  filter_upwards [uibhbotWordFamilyLaw_ae_eventualWholePlaneBall] with w hevent
  rcases hevent with ⟨hw, hball⟩
  refine ⟨hw, ?_⟩
  intro r
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨N₀, hN₀⟩ := hball (r + 1)
  refine ⟨N₀, 2 * N₀, activeInitial (shiftedStream W N₀) N₀, ?_⟩
  have h := hN₀ N₀ le_rfl
  exact h.1

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The first endpoint of the whole-plane geometric root-edge candidate, using
the west-to-east boundary order of Definition 5.8
missing for arbitrary code words. -/
@[expose] def uibhbotRootFirstVertex (W : ℤ → Fin 3) : WholePlaneVertex W :=
  wholePlaneEdgeWest W (uibhbotRootEdge W)

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The second endpoint of the whole-plane geometric root-edge candidate, using
the west-to-east boundary order of Definition 5.8
missing for arbitrary code words. -/
@[expose] def uibhbotRootSecondVertex (W : ℤ → Fin 3) : WholePlaneVertex W :=
  wholePlaneEdgeEast W (uibhbotRootEdge W)

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The all-geometric radius-`r` vertex ball about the first endpoint of the
The induced dart map, faces, ordered frame class and law remain separate. -/
@[expose] def uibhbotRootBallVertices (W : ℤ → Fin 3) (r : ℕ) :
    Set (WholePlaneVertex W) :=
  wholePlaneBallVertices W r (uibhbotRootFirstVertex W)

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The ordered root's first endpoint belongs to every nonnegative-radius -/
theorem uibhbotRootFirstVertex_mem_rootBall (W : ℤ → Fin 3) (r : ℕ) :
    uibhbotRootFirstVertex W ∈ uibhbotRootBallVertices W r := by
  change wholePlaneDistanceLe W r (uibhbotRootFirstVertex W)
    (uibhbotRootFirstVertex W)
  exact ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
At positive radius, both ordered endpoints of the geometric root edge occur
in the all-geometric ball, including when the edge is missing -/
theorem uibhbotRootSecondVertex_mem_rootBall (W : ℤ → Fin 3) (r : ℕ)
    (hr : 0 < r) :
    uibhbotRootSecondVertex W ∈ uibhbotRootBallVertices W r := by
  change wholePlaneDistanceLe W r (uibhbotRootFirstVertex W)
    (uibhbotRootSecondVertex W)
  refine ⟨1, by omega, ?_⟩
  refine .snoc (.nil (Set.mem_univ _)) (Set.mem_univ _) (Set.mem_univ _) ?_
  exact ⟨uibhbotRootEdge W, Or.inl ⟨rfl, rfl⟩⟩

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
On a radius-`r+1` window-capture event centered at the first root endpoint,
the colimit radius-`r` vertex ball is the image of the finite-stage ball
does not identify induced darts, rotations, original faces or framed classes. -/
theorem uibhbotRootBallVertices_eq_capture (W : ℤ → Fin 3) (r : ℕ)
    (_hr : 0 < r) (N m c : ℕ)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c) :
    uibhbotRootBallVertices W r =
      (fun v => wholePlaneVertexι W N v) ''
        (↑(kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W N) m) r c) : Set ℕ) := by
  unfold uibhbotRootBallVertices
  rw [← hcenter]
  exact wholePlaneBallVertices_eq_image_of_windowCaptureEvent W N m r c
    (uibhbotCaptureSucc_event (shiftedStream W N) m r c hevent)

/-- Each radius-`r` captured finite dart ball maps bijectively onto the
whole-plane darts with both endpoints in the ordered root ball
supplies complete capture. Helper toward Proposition 5.16 (local topology ruling);
not a paper result. -/
theorem uibhbotCapturedStageBallDarts_bijOn
    (W : ℤ → Fin 3) (r : ℕ) (N m c : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
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
  have hstrong : kmswWindowCaptureEventStrong u m r c :=
    uibhbotCaptureSucc_strong u m r c hevent
  have hedge := kmswWindowCaptureEventStrong_wholePlaneEdge_bijOn
    W N m r c hstrong
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
Helper toward Proposition 5.16 (local topology ruling); not a paper result. -/
theorem uibhbotCapturedStageBallDarts_sameWholePlaneImage
    (W : ℤ → Fin 3) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (hevent' : kmswWindowCaptureEvent (shiftedStream W N') m' (r + 1) c')
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
  exact ⟨uibhbotCapturedStageBallDarts_bijOn W r N m c hevent hcenter,
    uibhbotCapturedStageBallDarts_bijOn W r N' m' c' hevent' hcenter'⟩

/-- The two finite dart balls are equivalent by identifying each through its
Helper toward Proposition 5.16 (local topology ruling); not a paper result. -/
theorem uibhbotCapturedStageBallDarts_equiv
    (W : ℤ → Fin 3) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (hevent' : kmswWindowCaptureEvent (shiftedStream W N') m' (r + 1) c')
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
  obtain ⟨hN, hN'⟩ := uibhbotCapturedStageBallDarts_sameWholePlaneImage
    W r N m c N' m' c' hevent hcenter hevent' hcenter'
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

/-- The capture-choice dart equivalence preserves reversal of each geometric
(local topology ruling); not a paper result. -/
theorem uibhbotCapturedStageBallDarts_equiv_edgeFlip
    (W : ℤ → Fin 3) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (e : {d : StageDart (kmswStage (shiftedStream W N) m).nextEdge //
        d ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N) m) r c} ≃
      {d : StageDart (kmswStage (shiftedStream W N') m').nextEdge //
        d ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N') m') r c'})
    (he : ∀ d,
      wholePlaneDartι W N (d.1.1.val, d.1.2) =
        wholePlaneDartι W N' ((e d).1.1.val, (e d).1.2)) :
    ∀ d,
      e ⟨edgeFlip (kmswStage (shiftedStream W N) m).nextEdge d.1,
        (kmswStageBallDarts_edgeFlip (fun _ _ => True)
          (kmswStage (shiftedStream W N) m) r c d.1).mp d.2⟩ =
        (⟨edgeFlip (kmswStage (shiftedStream W N') m').nextEdge (e d).1,
          (kmswStageBallDarts_edgeFlip (fun _ _ => True)
            (kmswStage (shiftedStream W N') m') r c' (e d).1).mp (e d).2⟩ :
          {x : StageDart (kmswStage (shiftedStream W N') m').nextEdge //
            x ∈ kmswStageBallDarts (fun _ _ => True)
              (kmswStage (shiftedStream W N') m') r c'}) := by
  intro d
  let dflip : {x : StageDart (kmswStage (shiftedStream W N) m).nextEdge //
      x ∈ kmswStageBallDarts (fun _ _ => True)
        (kmswStage (shiftedStream W N) m) r c} :=
    ⟨edgeFlip (kmswStage (shiftedStream W N) m).nextEdge d.1,
    (kmswStageBallDarts_edgeFlip (fun _ _ => True)
      (kmswStage (shiftedStream W N) m) r c d.1).mp d.2⟩
  have hflip := he dflip
  have hbase := he d
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    have hEdgeImage : wholePlaneEdgeι W N' (e dflip).1.1.val =
        wholePlaneEdgeι W N' (e d).1.1.val := by
      calc
        wholePlaneEdgeι W N' (e dflip).1.1.val =
            wholePlaneEdgeι W N dflip.1.1.val := (congrArg Prod.fst hflip).symm
        _ = wholePlaneEdgeι W N d.1.1.val := rfl
        _ = wholePlaneEdgeι W N' (e d).1.1.val := congrArg Prod.fst hbase
    exact (wholePlaneEdgeι_injective W N') hEdgeImage
  · cases hsource : d.1.2 <;> cases htarget : (e d).1.2 <;>
      cases hflipped : (e dflip).1.2 <;>
      simp_all [wholePlaneDartι, edgeFlip, dflip]

/-- A capture-choice dart equivalence preserves the geometric edge identity
5.16 (local topology ruling); not a paper result. -/
theorem uibhbotCapturedStageBallDarts_equiv_edgeIdentity_orientation
    (W : ℤ → Fin 3) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (e : {d : StageDart (kmswStage (shiftedStream W N) m).nextEdge //
        d ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N) m) r c} ≃
      {d : StageDart (kmswStage (shiftedStream W N') m').nextEdge //
        d ∈ kmswStageBallDarts (fun _ _ => True)
          (kmswStage (shiftedStream W N') m') r c'})
    (he : ∀ d,
      wholePlaneDartι W N (d.1.1.val, d.1.2) =
        wholePlaneDartι W N' ((e d).1.1.val, (e d).1.2)) :
    ∀ d,
      wholePlaneEdgeι W N d.1.1.val = wholePlaneEdgeι W N' (e d).1.1.val ∧
        (e d).1.2 = d.1.2 := by
  intro d
  have h := he d
  change (wholePlaneEdgeι W N d.1.1.val, d.1.2) =
    (wholePlaneEdgeι W N' (e d).1.1.val, (e d).1.2) at h
  exact ⟨congrArg Prod.fst h, (congrArg Prod.snd h).symm⟩

/-- Helper toward Proposition 5.16 (prop-disk-ball-law); not a paper result.
Captured rotations are first returns of the same whole-plane rotation -/
theorem uibhbotCapturedStageBallDarts_equiv_rot
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (r : ℕ)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (hevent' : kmswWindowCaptureEvent (shiftedStream W N') m' (r + 1) c')
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
      (hev : kmswWindowCaptureEvent (shiftedStream W A) t (r + 1) b) :
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
      rw [uibhbotCapturedStageDart_rotation_agrees W H r A t b hev d hd,
        kmswInfRot_eq_stage (shiftedStream W A) (H.1 A) t d
          (capturedVertex_complete _ _ _
            ((uibhbotCaptureSucc_strong _ _ _ _ hev).2 _ hd))]
  have hinj (A t : ℕ) : Function.Injective
      (fun d : StageDart (kmswStage (shiftedStream W A) t).nextEdge =>
        wholePlaneDartι W A (d.1.val, d.2)) := by
    intro a b hab
    change (wholePlaneEdgeι W A a.1.val, a.2) =
      (wholePlaneEdgeι W A b.1.val, b.2) at hab
    apply Prod.ext
    · exact Fin.ext (wholePlaneEdgeι_injective W A (congrArg Prod.fst hab))
    · exact congrArg (fun q : WholePlaneDart W => q.2) hab
  have hsource := hdata N m c hevent
  have htarget := hdata N' m' c' hevent'
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

private theorem capturedStage_wholePlane_present (W : ℤ → Fin 3) (r N m c : ℕ)
    (hev : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (d : KMSWStageBallDart (fun _ _ => True) (kmswStage (shiftedStream W N) m) r c) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N d.1.1.val) ↔
      (kmswStage (shiftedStream W N) m).present d.1.1.val = true := by
  have hd := ((kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2).1
  have hf (M : ℕ) (hNM : N ≤ M) :=
    uibhbotCapturedVertex_fresh W r N m c M _ hev hd hNM
  have hf' : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (if d.1.2 then edgeEast (shiftedStream W N) d.1.1.val
        else edgeWest (shiftedStream W N) d.1.1.val) := by
    intro M hNM
    simpa only [stageEndpoint, (edge_endpoints_eq _ d.1.1.isLt).1,
      (edge_endpoints_eq _ d.1.1.isLt).2] using hf M hNM
  exact (wholePlaneEdgePresent_ι_of_fresh W N d.1.1.val d.1.2 hf').trans
    (capturedStage_present_iff _ m d.1
      ((uibhbotCaptureSucc_strong _ _ _ _ hev).2 _ hd))

/-- Helper toward Proposition 5.16 (prop-disk-ball-law); not a paper result.
Capture-choice equivalences preserve present and missing tags and dart tails -/
theorem uibhbotCapturedStageBallDarts_equiv_tags
    (W : ℤ → Fin 3) (r : ℕ) (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hevent' : kmswWindowCaptureEvent (shiftedStream W N') m' (r + 1) c')
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
  have hp := capturedStage_wholePlane_present W r N m c hevent d
  have hp' := capturedStage_wholePlane_present W r N' m' c' hevent' (e d)
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

/-- Construct the finite-stage framed ball at a captured UIBHBOT root edge.
The representative, center orientation and missing status are explicit inputs;
the radius-`r+1` event supplies upper-frontier avoidance for the full radius-`r` ball.
the induced darts, first-return rotation, inherited decoration and outer-face
mark are built from the validated generic construction
Helper toward Proposition 5.16 (local topology ruling); not a paper result. -/
@[expose] noncomputable def uibhbotCapturedStageFramedBall
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (_hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
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
  have houter_exists : ∃ o : StageDart s.nextEdge, o ∈ S ∧ M.IsOuter o := by
    rcases M.missing_outer d hmissing' with ho | ho
    · exact ⟨d, hroot_mem, ho⟩
    · exact ⟨edgeFlip s.nextEdge d, hroot_flip_mem, ho⟩
  let o := Classical.choose houter_exists
  have hoMem : o ∈ S := (Classical.choose_spec houter_exists).1
  have hoOuter : M.IsOuter o := (Classical.choose_spec houter_exists).2
  let root : S := ⟨d, hroot_mem⟩
  let outer : S := ⟨o, hoMem⟩
  have houterSurvives' : ∀ e (he : e ∈ S), M.IsOuter e →
      @CombinatorialMap.IsOuter
        {e : StageDart s.nextEdge // e ∈ S}
        (Finset.Subtype.fintype S) (fun a b => a.instDecidableEq b)
        (inducedCombinatorialMap M.toCombinatorialMap S hflip)
        outer ⟨e, he⟩ := by
    intro e he heouter
    apply inducedCombinatorialMap_face_sameCycle_of_connected_planar
    · exact kmswMap_isPlanar w m
    · exact kmswStageBallCombinatorialMap_rooted_isConnected w m r d hr
    · change M.toCombinatorialMap.faceSucc.SameCycle M.outer o at hoOuter
      change M.toCombinatorialMap.faceSucc.SameCycle M.outer e at heouter
      exact hoOuter.symm.trans heouter
  exact inducedFramedBallOfMissingRoot M S hflip outer houterSurvives' root hmissing

/-- The frame's first dart is the incidence at the captured center
Helper toward Proposition 5.16 (local topology ruling); not a paper result. -/
theorem uibhbotCapturedStageFramedBall_rootDart
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hcenterDart : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hrootEdge : wholePlaneEdgeι W N d.1.1 = uibhbotRootEdge W)
    (hmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    (uibhbotCapturedStageFramedBall W r hr N m c hevent hcenter d
      hcenterDart hrootEdge hmissing).rootDart.1 =
      edgeFlip (kmswStage (shiftedStream W N) m).nextEdge d := by
  rfl

/-- The captured frame edge and its first endpoint map to the whole-plane
Helper toward Proposition 5.16 (local topology ruling); not a paper result. -/
theorem uibhbotCapturedStageFramedBall_rootData
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hcenterDart : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hrootEdge : wholePlaneEdgeι W N d.1.1 = uibhbotRootEdge W)
    (hmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    (wholePlaneEdgeι W N
      ((uibhbotCapturedStageFramedBall W r hr N m c hevent hcenter d
        hcenterDart hrootEdge hmissing).rootDart.1).1 = uibhbotRootEdge W) ∧
    (wholePlaneVertexι W N (stageEndpoint (kmswStage (shiftedStream W N) m)
      (uibhbotCapturedStageFramedBall W r hr N m c hevent hcenter d
        hcenterDart hrootEdge hmissing).rootDart.1) = uibhbotRootFirstVertex W) := by
  constructor
  · rw [uibhbotCapturedStageFramedBall_rootDart W r hr N m c hevent hcenter d
      hcenterDart hrootEdge hmissing]
    simpa [edgeFlip] using hrootEdge
  · rw [uibhbotCapturedStageFramedBall_rootDart W r hr N m c hevent hcenter d
      hcenterDart hrootEdge hmissing]
    exact (congrArg (wholePlaneVertexι W N) hcenterDart).trans hcenter

private theorem capturedRoot_side (W : ℤ → Fin 3) (N m c : ℕ)
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

private theorem capturedRoot_ambient_outer (W : ℤ → Fin 3) (r N m c : ℕ)
    (hev : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    (kmswStageDirectedMap (shiftedStream W N) m).IsOuter d := by
  have hside := capturedRoot_side W N m c hcenter d hdcenter hdroot
  have hcball : c ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (shiftedStream W N) m) r c := by
    apply (kmswStageBallVertices_mem_iff_distanceLe _ _ _ _ _ _ hev.1).mpr
    exact ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  have hnot := (uibhbotCaptureSucc_strong _ _ _ _ hev).2 c hcball
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

private theorem capturedFramedBall_outer_root
    (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) (N m c : ℕ)
    (hev : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m) (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d) :
    let B := uibhbotCapturedStageFramedBall W r hr N m c hev hcenter d
      hdcenter hdroot hdmissing
    B.map.IsOuter (B.map.edgeInv B.rootDart) := by
  have ho := capturedRoot_ambient_outer W r N m c hev hcenter d hdcenter hdroot hdmissing
  let B := uibhbotCapturedStageFramedBall W r hr N m c hev hcenter d
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
  dsimp only [uibhbotCapturedStageFramedBall, DirectedMapWithMissing.IsOuter,
    inducedFramedBallOfMissingRoot, inducedDirectedMapWithMissing,
    CombinatorialMap.IsOuter]
  apply inducedCombinatorialMap_face_sameCycle_of_connected_planar
  · exact kmswMap_isPlanar _ _
  · exact kmswStageBallCombinatorialMap_rooted_isConnected _ m r d hr
  · exact (Classical.choose_spec hex).2.symm.trans ho'

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

/-- Helper toward Proposition 5.16 (prop-disk-ball-law); not a paper result.
Captured framed balls at the same missing whole-plane root are isomorphic -/
theorem uibhbotCapturedStageFramedBall_captureChoice
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (r : ℕ) (hr : 0 < r)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d)
    (hevent' : kmswWindowCaptureEvent (shiftedStream W N') m' (r + 1) c')
    (hcenter' : wholePlaneVertexι W N' c' = uibhbotRootFirstVertex W)
    (d' : StageDart (kmswStage (shiftedStream W N') m').nextEdge)
    (hdcenter' : stageEndpoint (kmswStage (shiftedStream W N') m')
      (edgeFlip _ d') = c')
    (hdroot' : wholePlaneEdgeι W N' d'.1.val = uibhbotRootEdge W)
    (hdmissing' : (kmswStageDirectedMap (shiftedStream W N') m').missing d') :
    Nonempty (FramedBallIso
      (uibhbotCapturedStageFramedBall W r hr N m c hevent hcenter d
        hdcenter hdroot hdmissing)
      (uibhbotCapturedStageFramedBall W r hr N' m' c' hevent' hcenter' d'
        hdcenter' hdroot' hdmissing')) := by
  classical
  subst c
  subst c'
  let A := uibhbotCapturedStageFramedBall W r hr N m _ hevent hcenter d
    rfl hdroot hdmissing
  let B := uibhbotCapturedStageFramedBall W r hr N' m' _ hevent' hcenter' d'
    rfl hdroot' hdmissing'
  obtain ⟨e, he⟩ := uibhbotCapturedStageBallDarts_equiv W r N m _ N' m' _
    hevent hcenter hevent' hcenter'
  let E : A.D ≃ B.D := e
  let a0 : A.D := ⟨d, (kmswStageBallRootEdge_mem _ m r d hr).1⟩
  let b0 : B.D := ⟨d', (kmswStageBallRootEdge_mem _ m' r d' hr).1⟩
  have hrot : ∀ x, E (A.map.rot x) = B.map.rot (E x) :=
    uibhbotCapturedStageBallDarts_equiv_rot W H r N m _ N' m' _
      hevent hcenter hevent' hcenter' e he
  have hflip : ∀ x, E (A.map.edgeInv x) = B.map.edgeInv (E x) :=
    uibhbotCapturedStageBallDarts_equiv_edgeFlip W r N m _ N' m' _ e he
  have htags := uibhbotCapturedStageBallDarts_equiv_tags W r N m _ N' m' _
    hevent hevent' e he
  have hs := capturedRoot_side W N m _ hcenter d rfl hdroot
  have hs' := capturedRoot_side W N' m' _ hcenter' d' rfl hdroot'
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
  have hoA := capturedFramedBall_outer_root W r hr N m _ hevent hcenter d
    rfl hdroot hdmissing
  have hoB := capturedFramedBall_outer_root W r hr N' m' _ hevent' hcenter' d'
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

/-- Helper toward Proposition 5.16 (prop-disk-ball-law); not a paper result.
The captured framed-map isomorphism, including tags, outer face and ordered root -/
@[expose] noncomputable def uibhbotCapturedStageFramedBall_iso
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (r : ℕ) (hr : 0 < r)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEvent (shiftedStream W N) m (r + 1) c)
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d)
    (hevent' : kmswWindowCaptureEvent (shiftedStream W N') m' (r + 1) c')
    (hcenter' : wholePlaneVertexι W N' c' = uibhbotRootFirstVertex W)
    (d' : StageDart (kmswStage (shiftedStream W N') m').nextEdge)
    (hdcenter' : stageEndpoint (kmswStage (shiftedStream W N') m')
      (edgeFlip _ d') = c')
    (hdroot' : wholePlaneEdgeι W N' d'.1.val = uibhbotRootEdge W)
    (hdmissing' : (kmswStageDirectedMap (shiftedStream W N') m').missing d') :
    FramedBallIso
      (uibhbotCapturedStageFramedBall W r hr N m c hevent hcenter d
        hdcenter hdroot hdmissing)
      (uibhbotCapturedStageFramedBall W r hr N' m' c' hevent' hcenter' d'
        hdcenter' hdroot' hdmissing') :=
  Classical.choice (uibhbotCapturedStageFramedBall_captureChoice W H r hr
    N m c N' m' c' hevent hcenter d hdcenter hdroot hdmissing
    hevent' hcenter' d' hdcenter' hdroot' hdmissing')

/-- View a finite framed ball as its isomorphism class
Helper toward Proposition 5.16 (local topology ruling); not a paper result. -/
@[expose] def uibhbotCapturedStageBallClass (B : FramedBall) : FramedBallClass :=
  Quotient.mk FramedBall.setoid B

end DirectedDistances.PaperProofs.Section5
