module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementMirrorSdp
public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableClose
public import DirectedDistances.RandomWalk.UIBHBOTBusemannIncrementSdp








public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter Quiver
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The topology of the existing faced-map law. -/
noncomputable local instance incrementCloseSdpTopology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel structure of the existing faced-map law. -/
noncomputable local instance incrementCloseSdpMeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Strict-record geometry used to identify the boundary traversal. -/
private theorem closeSdpRecordCreation (w : ℕ → Fin 3) (n : ℕ)
    (hrec : ∀ j ≤ n, L w (n + 1) < L w j) :
    w n = 0 ∧ (kmswStage w n).UL.length = 1 := by
  have hlast := hrec n le_rfl
  have hstep : L w (n + 1) =
      L w n + (lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  have hc : w n = 0 := by
    change L w (n + 1) = L w n + ((w n : ℤ) - 1) at hstep
    apply Fin.ext
    have hv := (w n).isLt
    omega
  have hmin : minL w n = L w n := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
    change minL w n = L w j at he
    have hjrec := hrec j hj
    have hle := runningMin_le (L w) n n le_rfl
    change minL w n ≤ L w n at hle
    rw [hc, lazyTwoDimensionalStep_zero] at hstep
    omega
  refine ⟨hc, ?_⟩
  have hlen := kmswStage_UL_length w n
  rw [hmin] at hlen
  omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Strict-record geometry used to identify the boundary traversal. -/
private theorem closeSdpDropLast (xs : List ℕ)
    (h : xs.length = 1) : xs.dropLast.reverse = [] := by
  have hd : xs.dropLast = [] := List.length_eq_zero_iff.mp (by
    rw [List.length_dropLast, h])
  rw [hd]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Strict-record geometry used to identify the boundary traversal. -/
private theorem closeSdpWindowRecord (w : ℕ → Fin 3) (s n : ℕ)
    (hrec : ∀ j < s + (n + 1), L w (s + (n + 1)) < L w j) :
    kmswWindowEdgeMapInf w s (kmswLLCreatedEdge (fun i => w (s + i)) (n + 1)) =
      kmswLLCreatedEdge w (s + (n + 1)) := by
  let v := fun i => w (s + i)
  let pre := kmswStage v n
  let globalPre := kmswStage w (s + n)
  let data := kmswWindowPatchData w s n
  have hcreation := closeSdpRecordCreation w (s + n) (by
    intro j hj
    simpa only [Nat.add_assoc] using hrec j (by omega))
  have hcode : w (s + n) = 0 := hcreation.1
  have hglobalLen : globalPre.UL.length = 1 := hcreation.2
  have hrel := kmswWindowPatchData_rel w s n
  change KMSWWindowPatchRel (kmswStage w s) globalPre pre data.φ
    data.A data.B data.YL data.YR data.XL data.XR at hrel
  have hprePos : 0 < pre.UL.length :=
    List.length_pos_of_ne_nil (kmswStage_UL_nonempty_active_last v n).1
  have hlength := congrArg List.length hrel.ul
  simp only [List.length_append, List.length_map] at hlength
  have hALen : data.A.length = 0 := by omega
  have hA : data.A = [] := List.length_eq_zero_iff.mp hALen
  have hpreLen : pre.UL.length = 1 := by omega
  have hdrop := closeSdpDropLast pre.UL hpreLen
  have hglobalDrop := closeSdpDropLast globalPre.UL hglobalLen
  have hlocalCode : v n = 0 := hcode
  have hlocalNext : (kmswStage v (n + 1)).nextEdge = pre.nextEdge + 2 := by
    change (kmswStep pre (v n)).nextEdge = pre.nextEdge + 2
    rw [hlocalCode]
    simp [kmswStep, kmswStepOfStep, kmswCodeStep, hdrop, State.addEdge]
  have hglobalNext : (kmswStage w (s + (n + 1))).nextEdge =
      globalPre.nextEdge + 2 := by
    rw [← Nat.add_assoc]
    change (kmswStep globalPre (w (s + n))).nextEdge = globalPre.nextEdge + 2
    rw [hcode]
    simp [kmswStep, kmswStepOfStep, kmswCodeStep, hglobalDrop, State.addEdge]
  have hlocalId : kmswLLCreatedEdge v (n + 1) = pre.nextEdge + 1 := by
    simp only [kmswLLCreatedEdge, hlocalNext]
    omega
  have hglobalId : kmswLLCreatedEdge w (s + (n + 1)) = globalPre.nextEdge + 1 := by
    simp only [kmswLLCreatedEdge, hglobalNext]
    omega
  have he : kmswLLCreatedEdge v (n + 1) < (kmswStage v (n + 1)).nextEdge := by
    rw [hlocalId, hlocalNext]
    omega
  rw [kmswWindowEdgeMapInf_eq_stage w s (n + 1) _ he, hlocalId, hglobalId]
  change (KMSWWindowPatchData.step globalPre pre
    (kmswCodeStep (w (s + n))) data).φ (pre.nextEdge + 1) = globalPre.nextEdge + 1
  rw [hcode]
  simp [kmswCodeStep, KMSWWindowPatchData.step, hdrop, hA]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
SDP and LDP use the same geometric boundary labels, identified through index one. -/
theorem ae_intrinsicSdpIncrementSource_le_one_identification :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ), k ≤ 1 →
        incrementOrbitVertex W H
            (intrinsicSdpIncrementSource
              (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) =
          uibhbotBusemannSourceSdp k W := by
  exact ae_intrinsicIncrementSource_le_one_identification

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
An absolute strict record remains a strict record in every earlier-start run,
so its geometric edge is globally missing. -/
private theorem closeSdpAbsoluteRecordMissing (W : ℤ → Fin 3) (N m : ℕ)
    (hm : 0 < m)
    (hr : ∀ M : ℕ, N ≤ M → ∀ i < M - N + m,
      L (shiftedStream W M) (M - N + m) < L (shiftedStream W M) i) :
    ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m)) := by
  intro hp
  obtain ⟨M, hNM, hM⟩ := (wholePlaneEdgePresent_ι W N _).mp hp
  have hrec := hr M hNM
  have hm' : m - 1 + 1 = m := by omega
  have he := closeSdpWindowRecord (shiftedStream W M) (M - N) (m - 1)
    (by simpa only [hm'] using hrec)
  rw [hm', shiftedStream_shift W N M hNM] at he
  have hp' := hM M le_rfl
  change EdgePresent (shiftedStream W M)
    (kmswWindowEdgeMapInf (shiftedStream W M) (M - N)
      (kmswLLCreatedEdge (shiftedStream W N) m)) at hp'
  rw [he] at hp'
  exact kmswLLCreatedEdge_not_present_of_record (shiftedStream W M)
    (M - N + m) (by omega) hrec hp'

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Repeated opposite-face inverse steps stay on the globally missing boundary chain. -/
private theorem closeSdpBoundaryDescend (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (j : ℤ) (hj : j ≤ -1)
    (hm : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h j))) (n : ℕ) :
    let e := wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h (j - n))
    ¬ wholePlaneEdgePresent W e ∧
      ((wholePlaneRotation W H * wholePlaneDartFlip W) ^ (-(n : ℤ)))
        ((wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h j), false) :
          WholePlaneDart W) =
        (e, false) := by
  induction n with
  | zero =>
    dsimp only
    simp only [Nat.cast_zero, sub_zero]
    exact ⟨hm, rfl⟩
  | succ n ih =>
    dsimp only at ih ⊢
    obtain ⟨hm', hf⟩ := wholePlane_missing_boundary_faceSucc W H N h (j - n)
      (by omega) ih.1
    have he : j - ((n + 1 : ℕ) : ℤ) = (j - n) - 1 := by omega
    rw [he]
    refine ⟨hm', ?_⟩
    have hp : -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) := by omega
    rw [hp, zpow_add]
    change ((wholePlaneRotation W H * wholePlaneDartFlip W) ^ (-1 : ℤ))
      (((wholePlaneRotation W H * wholePlaneDartFlip W) ^ (-(n : ℤ)))
        ((wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h j), false) :
          WholePlaneDart W)) = _
    have hc := congrArg
      (fun d : WholePlaneDart W =>
        ((wholePlaneRotation W H * wholePlaneDartFlip W) ^ (-1 : ℤ)) d) ih.2
    refine hc.trans ?_
    change wholePlaneDartFlip W ((wholePlaneRotation W H).symm
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h (j - n)), false)) = _
    have hf' := congrArg (wholePlaneDartFlip W) hf
    change wholePlaneDartFlip W
      ((wholePlaneRotation W H).symm
        (wholePlaneEdgeι W N
          (boundaryOuterEdge (shiftedStream W N) h (j - n)), false)) =
      (wholePlaneEdgeι W N
        (boundaryOuterEdge (shiftedStream W N) h (j - n - 1)), false) at hf'
    exact hf'

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every nonnegative boundary label is obtained from the actual missing-edge traversal. -/
private theorem closeSdpNonnegBoundary (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    (hz : uibhbotBoundaryHitTime 0 W = 0)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1)
    (hi : ∀ K : ℤ, ∀ h : BoundaryHitWitnesses
      (fun i => uibhbotFutureCode K W (i + 1)), ∀ j : ℤ, j ≤ 0 →
      uibhbotFutureVertex K W
          (boundaryVertex (fun i => uibhbotFutureCode K W (i + 1)) h j) =
        uibhbotFutureVertex (K + j) W 0) (n : ℕ) :
    incrementOrbitVertex W H
        (intrinsicSdpIncrementSource
          (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) (n : ℤ)) =
      uibhbotBusemannSourceSdp (n : ℤ) W := by
  let K : ℤ := n + 1
  have ht : uibhbotBoundaryHitTime K W < 0 := by
    by_contra hn
    by_cases he : uibhbotBoundaryHitTime K W = 0
    · have hv := (hh K).1
      rw [he] at hv
      norm_num [wholePlaneWordIntegral] at hv
      dsimp [K] at hv
      omega
    · have hp := hr K 0 (by omega)
      norm_num [wholePlaneWordIntegral] at hp
      dsimp [K] at hp
      omega
  let N := (uibhbotBoundaryHitTime K W).natAbs
  have hN : 1 ≤ N := by dsimp [N]; omega
  have htime : -(N : ℤ) = uibhbotBoundaryHitTime K W := by
    have he := Int.ofNat_natAbs_of_nonpos (le_of_lt ht)
    dsimp [N]
    omega
  have hval : L (shiftedStream W N) N = -K := by
    rw [incrementClose_run_L, sub_self, htime, (hh K).1]
    norm_num [wholePlaneWordIntegral]
  have hbefore : ∀ i < N, -K < L (shiftedStream W N) i := by
    intro i hi'
    rw [incrementClose_run_L, htime, (hh K).1]
    have hp := hr 0 ((i : ℤ) - N) (by omega)
    omega
  have hrootHit := incrementClose_left_hit_eq (shiftedStream W N) (hhit N)
    (-K) (by dsimp [K]; omega) N hval hbefore
  have hroot : wholePlaneEdgeι W N
      (boundaryOuterEdge (shiftedStream W N) (hhit N) (-K)) = uibhbotRootEdge W := by
    rw [boundaryOuterEdge_of_negative _ _ (by dsimp [K]; omega), hrootHit]
    exact (uibhbotRootEdge_eq_window W N hN (by
      intro i hi'
      rw [hval]
      exact hbefore i hi')).symm
  have htn : uibhbotBoundaryHitTime K W < uibhbotBoundaryHitTime (n : ℤ) W := by
    by_contra hn
    rcases lt_or_eq_of_le (by omega :
      uibhbotBoundaryHitTime (n : ℤ) W ≤ uibhbotBoundaryHitTime K W) with hlt | heq
    · have hp := hr K _ hlt
      rw [(hh (n : ℤ)).1] at hp
      dsimp [K] at hp
      omega
    · have hp := (hh (n : ℤ)).1
      rw [heq, (hh K).1] at hp
      dsimp [K] at hp
      omega
  let m := (uibhbotBoundaryHitTime (n : ℤ) W + N).toNat
  have hm : 0 < m := by dsimp [m]; omega
  have hmi : (m : ℤ) - N = uibhbotBoundaryHitTime (n : ℤ) W := by
    dsimp [m]
    omega
  have hmval : L (shiftedStream W N) m = -1 := by
    rw [incrementClose_run_L, hmi, htime, (hh (n : ℤ)).1, (hh K).1]
    dsimp [K]
    omega
  have hmbefore : ∀ i < m, (-1 : ℤ) < L (shiftedStream W N) i := by
    intro i hi'
    rw [incrementClose_run_L, htime, (hh K).1]
    have hp := hr (n : ℤ) ((i : ℤ) - N) (by omega)
    dsimp [K]
    omega
  have hhitm := incrementClose_left_hit_eq (shiftedStream W N) (hhit N)
    (-1) (by omega) m hmval hmbefore
  have hem : boundaryOuterEdge (shiftedStream W N) (hhit N) (-1) =
      kmswLLCreatedEdge (shiftedStream W N) m := by
    rw [boundaryOuterEdge_of_negative _ _ (by omega), hhitm]
  have hmissing : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N
      (boundaryOuterEdge (shiftedStream W N) (hhit N) (-1))) := by
    rw [hem]
    apply closeSdpAbsoluteRecordMissing W N m hm
    intro M hNM i hi'
    rw [incrementClose_run_L, incrementClose_run_L]
    have he : ((M - N + m : ℕ) : ℤ) - M =
        uibhbotBoundaryHitTime (n : ℤ) W := by omega
    rw [he, (hh (n : ℤ)).1]
    have hp := hr (n : ℤ) ((i : ℤ) - M) (by omega)
    omega
  have hback := (closeSdpBoundaryDescend W H N (hhit N) (-1) (by omega) hmissing n).2
  have heq : -1 - (n : ℤ) = -K := by dsimp [K]; omega
  rw [heq, hroot] at hback
  let F := wholePlaneRotation W H * wholePlaneDartFlip W
  have hforward : (F ^ (n : ℤ)) (uibhbotWholePlaneFrameEdgeDart W) =
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) (hhit N) (-1)),
        false) := by
    calc
      _ = (F ^ (n : ℤ)) ((F ^ (-(n : ℤ)))
          ((wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) (hhit N) (-1)),
            false) : WholePlaneDart W)) := congrArg (F ^ (n : ℤ)) hback.symm
      _ = _ := by
        have hp := congrArg (fun G : Equiv.Perm (WholePlaneDart W) =>
          G ((wholePlaneEdgeι W N
            (boundaryOuterEdge (shiftedStream W N) (hhit N) (-1)), false) :
              WholePlaneDart W)) (zpow_add F (n : ℤ) (-(n : ℤ)))
        simp only [add_neg_cancel, zpow_zero] at hp
        exact hp.symm
  apply congrArg UIBHBOTPresentVertex.mk
  change wholePlaneDartVertex W ((F ^ (n : ℤ)) (uibhbotWholePlaneFrameEdgeDart W)) = _
  rw [hforward]
  change wholePlaneEdgeWest W (wholePlaneEdgeι W N
    (boundaryOuterEdge (shiftedStream W N) (hhit N) (-1))) = _
  rw [wholePlaneEdgeWest_ι, (boundaryOuterEdge_endpoints _ _ _).1]
  have hstream : (fun i => uibhbotFutureCode K W (i + 1)) = shiftedStream W N := by
    rw [uibhbotFutureCode_stream, ← htime]
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  let hb : BoundaryHitWitnesses (fun i => uibhbotFutureCode K W (i + 1)) :=
    hstream.symm ▸ hhit N
  have hsource := hi K hb (-1) (by omega)
  have hK : K + -1 = (n : ℤ) := by dsimp [K]; omega
  rw [hK] at hsource
  have hv : uibhbotFutureVertex K W = wholePlaneVertexι W N := by
    change lemma38StartVertexι W (uibhbotBoundaryHitTime K W) = _
    funext v
    rw [lemma38StartVertexι, ite_eq_left (le_of_lt ht)]
  rw [hv] at hsource
  simpa only [hstream] using hsource

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Boundary identification holds simultaneously at every integer index. -/
theorem ae_intrinsicSdpIncrementSource_identification :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        incrementOrbitVertex W H
            (intrinsicSdpIncrementSource
              (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) =
          uibhbotBusemannSourceSdp k W := by
  filter_upwards [ae_intrinsicSdpIncrementSource_le_one_identification,
    ae_incrementClose_root_code, ae_uibhbotBoundaryHit,
    ae_uibhbotBoundaryHit_strictRecord, ae_uibhbotFutureBoundary_index]
    with W hn hz hh hr hi H hhit C k
  by_cases hk : k ≤ 1
  · exact hn H hhit C k hk
  · have he : (k.toNat : ℤ) = k := by omega
    simpa only [he] using closeSdpNonnegBoundary W H hhit C hz.1 hh hr hi k.toNat

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The original boundary-identification obligation is closed at every index at most one. -/
theorem intrinsicSdpIncrementBoundaryIdentificationAt_of_le_one (k : ℤ) (hk : k ≤ 1) :
    UIBHBOTIntrinsicSdpIncrementBoundaryIdentificationAt k := by
  filter_upwards [ae_intrinsicSdpIncrementSource_le_one_identification]
    with W hW H hhit C
  exact hW H hhit C k hk

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The original boundary obligation is proved at every index, including zero and two. -/
theorem intrinsicSdpIncrementBoundaryIdentificationAt_proved (k : ℤ) :
    UIBHBOTIntrinsicSdpIncrementBoundaryIdentificationAt k := by
  filter_upwards [ae_intrinsicSdpIncrementSource_identification] with W hW H hhit C
  exact hW H hhit C k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The infimum over ambient directed walks confined to the radius ball. This retains
ambient endpoints and is not yet the finite representative's simple-path SDP. -/
@[expose] noncomputable def incrementCloseSdp_ballDistance (M : RootedLocallyFiniteMap)
    (r : ℕ) (s t : RootedLocallyFiniteVertex M.D M.rot) : ℕ∞ :=
  ⨅ ds : List M.D, ⨅ (_ : incrementSdpDartWalk M ds s t),
    ⨅ (_ : ∀ d ∈ ds, d ∈ rootedLocallyFiniteBallDarts M r), (ds.length : ℕ∞)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Removing walks can only increase the shortest distance. -/
theorem incrementCloseSdp_le_ballDistance (M : RootedLocallyFiniteMap) (r : ℕ)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    intrinsicIncrementSdp M s t ≤ incrementCloseSdp_ballDistance M r s t := by
  apply le_iInf
  intro ds
  apply le_iInf
  intro hw
  apply le_iInf
  intro _hd
  exact iInf_le_of_le ds (iInf_le_of_le hw le_rfl)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Larger radii allow more directed walks and cannot increase the shortest distance. -/
theorem incrementCloseSdp_ballDistance_antitone (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    Antitone (fun r => incrementCloseSdp_ballDistance M r s t) := by
  intro r R hr
  apply le_iInf
  intro ds
  apply le_iInf
  intro hw
  apply le_iInf
  intro hd
  exact iInf_le_of_le ds (iInf_le_of_le hw
    (iInf_le_of_le (fun d hds => rootedLocallyFiniteBallDarts_mono M hr (hd d hds))
      le_rfl))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Unreachable ambient pairs have infinite SDP in every restricted ball. -/
theorem incrementCloseSdp_ballDistance_eq_top_of_unreachable
    (M : RootedLocallyFiniteMap) (s t : RootedLocallyFiniteVertex M.D M.rot)
    (h : ¬ ∃ ds, incrementSdpDartWalk M ds s t) (r : ℕ) :
    incrementCloseSdp_ballDistance M r s t = ⊤ := by
  apply top_unique
  rw [← (intrinsicIncrementSdp_eq_top_iff M s t).2 h]
  exact incrementCloseSdp_le_ballDistance M r s t

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every fixed pair has eventual radius equality. For reachable pairs a shortest
walk is finite and captured by a ball; unreachable pairs stay infinite throughout. -/
theorem incrementCloseSdp_ballDistance_stabilizes (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) (r₀ : ℕ) :
    ∃ R : ℕ, r₀ ≤ R ∧ ∀ r ≥ R,
      incrementCloseSdp_ballDistance M r s t = intrinsicIncrementSdp M s t := by
  by_cases h : ∃ ds, incrementSdpDartWalk M ds s t
  · obtain ⟨ds, hw, ha⟩ := intrinsicIncrementSdp_attained M s t h
    obtain ⟨R, hR, hd⟩ := incrementSdpDartList_captured M r₀ ds
    refine ⟨R, hR, fun r hr => le_antisymm ?_ (incrementCloseSdp_le_ballDistance M r s t)⟩
    rw [← ha]
    exact iInf_le_of_le ds (iInf_le_of_le hw
      (iInf_le_of_le (fun d hds => rootedLocallyFiniteBallDarts_mono M hr (hd d hds))
        le_rfl))
  · refine ⟨r₀, le_rfl, fun r _hr => ?_⟩
    rw [incrementCloseSdp_ballDistance_eq_top_of_unreachable M s t h r,
      (intrinsicIncrementSdp_eq_top_iff M s t).2 h]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
For a finite target set, one enclosing radius works simultaneously for both sources
and every target. Infinite distances retain their original values. -/
theorem incrementCloseSdp_ballDistance_stabilizes_on_finset
    (M : RootedLocallyFiniteMap) (s s' : RootedLocallyFiniteVertex M.D M.rot)
    (T : Finset (RootedLocallyFiniteVertex M.D M.rot)) (r₀ : ℕ) :
    ∃ R : ℕ, r₀ ≤ R ∧ ∀ r ≥ R, ∀ t ∈ T,
      incrementCloseSdp_ballDistance M r s t = intrinsicIncrementSdp M s t ∧
      incrementCloseSdp_ballDistance M r s' t = intrinsicIncrementSdp M s' t := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨r₀, le_rfl, fun _ _ t ht => (Finset.notMem_empty t ht).elim⟩
  | @insert t T _ht ih =>
    obtain ⟨R, hR, htargets⟩ := ih
    obtain ⟨R0, hR0, h0⟩ := incrementCloseSdp_ballDistance_stabilizes M s t R
    obtain ⟨R1, hR1, h1⟩ := incrementCloseSdp_ballDistance_stabilizes M s' t R0
    refine ⟨R1, hR.trans (hR0.trans hR1), fun r hr u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ⟨h0 r (hR1.trans hr), h1 r hr⟩
    · exact htargets r (hR0.trans (hR1.trans hr)) u hu

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
At each fixed target-shell scale, one radius stabilizes both full intrinsic SDPs
simultaneously for all ambient vertices in that geometric ball. This is the
radius quantifier needed before sending the shell scale to infinity. -/
theorem incrementCloseSdp_ballDistance_stabilizes_on_radius
    (M : RootedLocallyFiniteMap) (s s' : RootedLocallyFiniteVertex M.D M.rot)
    (m r₀ : ℕ) :
    ∃ R : ℕ, r₀ ≤ R ∧ ∀ r ≥ R,
      ∀ t ∈ rootedLocallyFiniteRadiusVertices M m,
        incrementCloseSdp_ballDistance M r s t = intrinsicIncrementSdp M s t ∧
        incrementCloseSdp_ballDistance M r s' t = intrinsicIncrementSdp M s' t :=
  incrementCloseSdp_ballDistance_stabilizes_on_finset M s s'
    (rootedLocallyFiniteRadiusVertices M m) r₀

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
OPEN local comparison: the finite representative's simple SDP must equal the
restricted ambient SDP at corresponding dart endpoints, including infinity.
This proposition is defined, not proved or assumed by any theorem in this file. -/
@[expose] def FiniteBallSdpDistanceIdentification
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r) : Prop :=
  ∀ d e : (rootedLocallyFiniteFramedBall M r hr).D,
    (show ℕ∞ from simpleDirectedPathSDPLength
      (rootedLocallyFiniteFramedBall M r hr).map
      (vertexClass (rootedLocallyFiniteFramedBall M r hr).map.toCombinatorialMap d)
      (vertexClass (rootedLocallyFiniteFramedBall M r hr).map.toCombinatorialMap e)) =
      incrementCloseSdp_ballDistance M.toRootedLocallyFiniteMap r
        (rootedLocallyFiniteVertexClass M.rot d.1)
        (rootedLocallyFiniteVertexClass M.rot e.1)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
At each fixed label, the finite boundary traversal eventually agrees with the
ambient traversal. This concerns restriction of the rotation permutation,
separately from the code-boundary identification. Proved below for every map and label. -/
@[expose] def FiniteBallSdpBoundarySourceIdentificationAt
    (M : RootedLocallyFinitePlanarMap) (k : ℤ) : Prop :=
  ∃ R : ℕ, ∀ r ≥ R, ∀ hr : 0 < r,
    let B := rootedLocallyFiniteFramedBall M r hr
    rootedLocallyFiniteVertexClass M.rot
        ((((B.map.rot * B.map.edgeInv) ^ k) B.frameEdgeDart).1) =
      intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A retained opposite-face successor is unchanged by cyclic restriction. -/
private theorem closeSdpBallOppositeStep (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (d : (rootedLocallyFiniteFramedBall M r hr).D)
    (hd : M.rot (M.edgeInv d.1) ∈
      rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r) :
    let B := rootedLocallyFiniteFramedBall M r hr
    ((B.map.rot * B.map.edgeInv) d).1 = M.rot (M.edgeInv d.1) := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let S := rootedLocallyFiniteBallDarts A r
  have hret : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (A.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, he⟩ := rootedLocallyFiniteRotationReturn A x.1
    exact ⟨k, hk, by rw [he]; exact x.2⟩
  let e : S := ⟨M.edgeInv d.1, rootedLocallyFiniteBallDarts_edgeInv_closed A r d.1 d.2⟩
  have ht : cyclicFirstReturnTime A.rot S hret e = 1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (hret e) ⟨Nat.one_pos, by simpa only [pow_one] using hd⟩
    · exact (cyclicFirstReturnTime_spec A.rot S hret e).1
  change (cyclicFirstReturn A.rot S hret e).1 = _
  rw [(firstReturn_spec A.rot S hret e).1, ht, pow_one]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A retained opposite-face predecessor is unchanged by cyclic restriction. -/
private theorem closeSdpBallOppositeInverseStep (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (d : (rootedLocallyFiniteFramedBall M r hr).D)
    (hd : M.edgeInv (M.rot.symm d.1) ∈
      rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r) :
    let B := rootedLocallyFiniteFramedBall M r hr
    ((B.map.rot * B.map.edgeInv).symm d).1 = M.edgeInv (M.rot.symm d.1) := by
  let B := rootedLocallyFiniteFramedBall M r hr
  let e : B.D := ⟨M.edgeInv (M.rot.symm d.1), hd⟩
  have he : M.rot (M.edgeInv e.1) ∈
      rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r := by
    simpa only [e, M.edgeInv_invol, Equiv.apply_symm_apply] using d.2
  have hstep : (B.map.rot * B.map.edgeInv) e = d := by
    apply Subtype.ext
    simpa only [e, M.edgeInv_invol, Equiv.apply_symm_apply] using
      closeSdpBallOppositeStep M r hr e he
  have hi := congrArg (B.map.rot * B.map.edgeInv).symm hstep
  rw [Equiv.symm_apply_apply] at hi
  exact congrArg Subtype.val hi.symm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The geometric edge involution is its own inverse. -/
private theorem closeSdpEdgeInvSymm (M : RootedLocallyFiniteMap) (d : M.D) :
    M.edgeInv.symm d = M.edgeInv d := by
  apply M.edgeInv.injective
  rw [Equiv.apply_symm_apply, M.edgeInv_invol]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every fixed positive or negative frame iterate is eventually retained exactly. -/
private theorem closeSdpBallFramePower (M : RootedLocallyFinitePlanarMap) (k : ℤ) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ hr : 0 < r,
      let B := rootedLocallyFiniteFramedBall M r hr
      ((((B.map.rot * B.map.edgeInv) ^ k) B.frameEdgeDart).1) =
        ((M.rot * M.edgeInv) ^ k) M.frameEdgeDart := by
  classical
  let F := M.rot * M.edgeInv
  induction k using Int.induction_on with
  | zero => exact ⟨0, fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih
    obtain ⟨S, hS, hcap⟩ := incrementSdpDartList_captured M.toRootedLocallyFiniteMap R
      [((F ^ ((n : ℤ) + 1)) M.frameEdgeDart)]
    refine ⟨S, fun r hr hpos => ?_⟩
    let B := rootedLocallyFiniteFramedBall M r hpos
    let d := ((B.map.rot * B.map.edgeInv) ^ (n : ℤ)) B.frameEdgeDart
    have hd := hR r (hS.trans hr) hpos
    have hnxt : M.rot (M.edgeInv d.1) ∈
        rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r := by
      rw [hd]
      have hc := rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hr
        (hcap _ (List.mem_singleton_self _))
      simpa only [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply, F]
        using hc
    dsimp only
    simp only [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    exact (closeSdpBallOppositeStep M r hpos d hnxt).trans
      (congrArg (fun x => M.rot (M.edgeInv x)) hd)
  | pred n ih =>
    obtain ⟨R, hR⟩ := ih
    obtain ⟨S, hS, hcap⟩ := incrementSdpDartList_captured M.toRootedLocallyFiniteMap R
      [((F ^ (-(n : ℤ) - 1)) M.frameEdgeDart)]
    refine ⟨S, fun r hr hpos => ?_⟩
    let B := rootedLocallyFiniteFramedBall M r hpos
    let d := ((B.map.rot * B.map.edgeInv) ^ (-(n : ℤ))) B.frameEdgeDart
    have hd := hR r (hS.trans hr) hpos
    have hnxt : M.edgeInv (M.rot.symm d.1) ∈
        rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r := by
      rw [hd]
      have hc := rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hr
        (hcap _ (List.mem_singleton_self _))
      have hp : -(n : ℤ) - 1 = -1 + -(n : ℤ) := by omega
      simp only [hp, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply] at hc
      change M.edgeInv.symm (M.rot.symm ((F ^ (-(n : ℤ))) M.frameEdgeDart)) ∈
        rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r at hc
      rw [closeSdpEdgeInvSymm M.toRootedLocallyFiniteMap] at hc
      exact hc
    have hp : -(n : ℤ) - 1 = -1 + -(n : ℤ) := by omega
    dsimp only
    simp only [hp, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
    change _ = M.edgeInv.symm (M.rot.symm _)
    rw [closeSdpEdgeInvSymm M.toRootedLocallyFiniteMap]
    exact (closeSdpBallOppositeInverseStep M r hpos d hnxt).trans
      (congrArg (fun x => M.edgeInv (M.rot.symm x)) hd)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite boundary labels eventually equal their ambient boundary labels. -/
theorem finiteBallSdpBoundarySourceIdentificationAt_proved
    (M : RootedLocallyFinitePlanarMap) (k : ℤ) :
    FiniteBallSdpBoundarySourceIdentificationAt M k := by
  obtain ⟨R, hR⟩ := closeSdpBallFramePower M k
  exact ⟨R, fun r hr hpos => congrArg (rootedLocallyFiniteVertexClass M.rot)
    (hR r hr hpos)⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
An explicit ambient target representative, using the actual active geometric edge. -/
@[expose] noncomputable def incrementCloseSdp_intrinsicTarget (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (k : ℤ) (m : ℕ) :
    RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) :=
  incrementClose_intrinsicTarget W H k m

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The explicit ambient target is exactly the SDP code target. -/
theorem incrementCloseSdp_intrinsicTarget_image (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (k : ℤ) (m : ℕ) :
    incrementOrbitVertex W H (incrementCloseSdp_intrinsicTarget W H k m) =
      uibhbotBusemannTargetSdp k W m := by
  exact incrementClose_intrinsicTarget_image W H k m

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Along the supplied distinct targets, every integer increment is realized
by finite restricted SDPs once the radius is large enough for that target. This
does not assert uniform consensus over all targets in a finite faced-ball shell. -/
theorem ae_incrementCloseSdp_target_radius_stabilization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        ∃ B : ℕ, ∀ m ≥ B,
          ∃ t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H),
            incrementOrbitVertex W H t = uibhbotBusemannTargetSdp k W m ∧
            ∃ a b : ℕ, ∃ R : ℕ, ∀ r ≥ R,
              incrementCloseSdp_ballDistance
                  (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r
                  (intrinsicSdpIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) t =
                (a : ℕ∞) ∧
              incrementCloseSdp_ballDistance
                  (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r
                  (intrinsicSdpIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) (k - 1)) t =
                (b : ℕ∞) ∧
              uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ) := by
  filter_upwards [ae_intrinsicSdpIncrementSource_identification,
    ae_uibhbotBusemannIncrementSdp_distance_realization] with W hs hreal H hhit C k
  obtain ⟨_, B, hB⟩ := hreal k
  refine ⟨B, fun m hm => ?_⟩
  let t := incrementCloseSdp_intrinsicTarget W H k m
  have ht := incrementCloseSdp_intrinsicTarget_image W H k m
  refine ⟨t, ht, ?_⟩
  obtain ⟨_, _, a, b, ha, hb, hi⟩ := hB m hm
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  let s := intrinsicSdpIncrementSource M k
  let s' := intrinsicSdpIncrementSource M (k - 1)
  have hs0 : incrementOrbitVertex W H s = uibhbotBusemannSourceSdp k W :=
    hs H hhit C k
  have hs1 : incrementOrbitVertex W H s' = uibhbotBusemannSourceSdp (k - 1) W :=
    hs H hhit C (k - 1)
  have hf0 : intrinsicIncrementSdp M s t = (a : ℕ∞) := by
    rw [intrinsicIncrementSdp_eq_codeSdp W H hhit C s t, hs0, ht]
    exact ha
  have hf1 : intrinsicIncrementSdp M s' t = (b : ℕ∞) := by
    rw [intrinsicIncrementSdp_eq_codeSdp W H hhit C s' t, hs1, ht]
    exact hb
  obtain ⟨R0, _, hR0⟩ := incrementCloseSdp_ballDistance_stabilizes M s t 0
  obtain ⟨R1, _, hR1⟩ := incrementCloseSdp_ballDistance_stabilizes M s' t 0
  refine ⟨a, b, max R0 R1, fun r hr => ?_⟩
  exact ⟨(hR0 r ((le_max_left _ _).trans hr)).trans hf0,
    (hR1 r ((le_max_right _ _).trans hr)).trans hf1, hi⟩





theorem hsymSdp_of_remaining_ballShell_and_reflection
    (h0 : UIBHBOTSdpIncrementBallShellStabilizationAt 0)
    (h2 : UIBHBOTSdpIncrementBallShellStabilizationAt 2)
    (href : UIBHBOTSdpIncrementObservableReflection finiteBallSdpIncrementObservable) :
    iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω) := by
  exact hsymSdp_of_uibhbot_mirror_invariance
    (finiteBallSdpIncrementObservable_realization_of_ballShellStabilization 0 h0)
    (finiteBallSdpIncrementObservable_realization_of_ballShellStabilization 2 h2) href

end DirectedDistances.PaperProofs.Section5
