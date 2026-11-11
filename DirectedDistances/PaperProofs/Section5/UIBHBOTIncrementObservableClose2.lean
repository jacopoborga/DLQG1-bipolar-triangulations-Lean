module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableClose
public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorFacedCompat
public import DirectedDistances.PaperProofs.Section3.BSTopologyGenericMetrizable
import DirectedDistances.KMSW.WholePlaneLLRecordEdges
















public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW Quiver
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The helper topology of the rooted-map law. -/
noncomputable local instance incrementClose2Topology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel structure of the rooted-map law. -/
noncomputable local instance incrementClose2MeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Strict-record creation and its window transport. -/
private theorem incrementClose2_left_record_creation (w : ℕ → Fin 3) (n : ℕ)
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
Strict-record creation and its window transport. -/
private theorem incrementClose2_dropLast_reverse_eq_nil_of_length_one (xs : List ℕ)
    (h : xs.length = 1) : xs.dropLast.reverse = [] := by
  have hd : xs.dropLast = [] := List.length_eq_zero_iff.mp (by
    rw [List.length_dropLast, h])
  rw [hd]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Strict-record creation and its window transport. -/
private theorem incrementClose2_windowMap_LL_created (w : ℕ → Fin 3) (s n : ℕ)
    (hrec : ∀ j < s + (n + 1), L w (s + (n + 1)) < L w j) :
    kmswWindowEdgeMapInf w s (kmswLLCreatedEdge (fun i => w (s + i)) (n + 1)) =
      kmswLLCreatedEdge w (s + (n + 1)) := by
  let v := fun i => w (s + i)
  let pre := kmswStage v n
  let globalPre := kmswStage w (s + n)
  let data := kmswWindowPatchData w s n
  have hcreation := incrementClose2_left_record_creation w (s + n) (by
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
  have hdrop := incrementClose2_dropLast_reverse_eq_nil_of_length_one pre.UL hpreLen
  have hglobalDrop := incrementClose2_dropLast_reverse_eq_nil_of_length_one globalPre.UL hglobalLen
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
A record that remains strict in every earlier window is globally missing. -/
private theorem incrementClose2_record_missing (W : ℤ → Fin 3) (N n : ℕ)
    (hn : 0 < n)
    (hr : ∀ M, N ≤ M → ∀ j < M - N + n,
      L (shiftedStream W M) (M - N + n) < L (shiftedStream W M) j) :
    ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n)) := by
  intro hp
  obtain ⟨M, hNM, hM⟩ := (wholePlaneEdgePresent_ι W N _).mp hp
  have hpres := hM M le_rfl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hmap := incrementClose2_windowMap_LL_created (shiftedStream W M) (M - N) m
    (hr M hNM)
  rw [shiftedStream_shift W N M hNM] at hmap
  change EdgePresent (shiftedStream W M)
    (kmswWindowEdgeMapInf (shiftedStream W M) (M - N)
      (kmswLLCreatedEdge (shiftedStream W N) (m + 1))) at hpres
  rw [hmap] at hpres
  exact kmswLLCreatedEdge_not_present_of_record _ _ (by omega) (hr M hNM) hpres

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Absolute strict records fix one-sided hit times in a larger-cutoff window. -/
private theorem incrementClose2_hit (W : ℤ → Fin 3) (N : ℕ) (A j : ℤ)
    (hstart : (wholePlaneWordIntegral W (-(N : ℤ))).1 = A)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hj : j < A) (ht : -(N : ℤ) < uibhbotBoundaryHitTime j W) :
    boundaryHitTime (shiftedStream W N) h (j - A) =
      (uibhbotBoundaryHitTime j W + N).toNat := by
  apply incrementClose_left_hit_eq _ h _ (by omega)
  · rw [incrementClose_run_L, hstart,
      show (((uibhbotBoundaryHitTime j W + N).toNat : ℤ) - N) =
        uibhbotBoundaryHitTime j W by omega, (hh j).1]
  · intro i hi
    rw [incrementClose_run_L, hstart]
    have hp := hr j ((i : ℤ) - N) (by omega)
    omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The west incidence of an explicitly labelled run boundary edge. -/
private noncomputable def incrementClose2_boundaryDart (W : ℤ → Fin 3)
    (N : ℕ) (h : BoundaryHitWitnesses (shiftedStream W N)) (j : ℤ) : WholePlaneDart W :=
  (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h j), false)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The negative opposite-face traversal descends from any globally missing edge. -/
private theorem incrementClose2_descend (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (j : ℤ) (hj : j ≤ -1)
    (hm : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h j))) (n : ℕ) :
    ¬ wholePlaneEdgePresent W
        (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h (j - n))) ∧
      ((wholePlaneRotation W H * wholePlaneDartFlip W) ^ (-(n : ℤ)))
          (incrementClose2_boundaryDart W N h j) =
        (incrementClose2_boundaryDart W N h (j - n)) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, neg_zero, zpow_zero, Equiv.Perm.one_apply]
    exact ⟨hm, trivial⟩
  | succ n ih =>
    obtain ⟨hm', hf⟩ := wholePlane_missing_boundary_faceSucc W H N h (j - n)
      (by omega) ih.1
    have he : j - ((n + 1 : ℕ) : ℤ) = (j - (n : ℤ)) - 1 := by omega
    rw [he]
    refine ⟨hm', ?_⟩
    rw [show -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) by omega,
      zpow_add, Equiv.Perm.mul_apply, ih.2, zpow_neg_one]
    have hhf := congrArg (wholePlaneDartFlip W) hf
    change wholePlaneDartFlip W
      ((wholePlaneRotation W H).symm
        (wholePlaneEdgeι W N
          (boundaryOuterEdge (shiftedStream W N) h (j - n)), false)) =
      (wholePlaneEdgeι W N
        (boundaryOuterEdge (shiftedStream W N) h (j - n - 1)), false) at hhf
    exact hhf

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Larger absolute boundary levels have strictly earlier first hits. -/
private theorem incrementClose2_hit_order (W : ℤ → Fin 3)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1) (a b : ℤ) (hab : a < b) :
    uibhbotBoundaryHitTime b W < uibhbotBoundaryHitTime a W := by
  by_contra hn
  by_cases he : uibhbotBoundaryHitTime a W = uibhbotBoundaryHitTime b W
  · have ha := (hh a).1
    rw [he, (hh b).1] at ha
    omega
  · have hp := hr b (uibhbotBoundaryHitTime a W) (by omega)
    rw [(hh a).1] at hp
    omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A larger-cutoff run's nonpositive boundary source has its absolute label. -/
private theorem incrementClose2_source (W : ℤ → Fin 3) (N : ℕ) (A j : ℤ)
    (hstart : (wholePlaneWordIntegral W (-(N : ℤ))).1 = A)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hj : j < A) (ht : -(N : ℤ) < uibhbotBoundaryHitTime j W) :
    wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h (j - A)) =
      (uibhbotBusemannSource j W).id := by
  rw [boundaryVertex_eq_activeInitial _ h (by omega) (by omega),
    incrementClose2_hit W N A j hstart hh hr h hj ht]
  have ha := uibhbotStartVertex_activeInitial W (-(N : ℤ))
    (uibhbotBoundaryHitTime j W + N).toNat
  have hs : lemma38StartStream W (-(N : ℤ)) = shiftedStream W N := by
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  rw [hs, show -(N : ℤ) + (uibhbotBoundaryHitTime j W + N).toNat =
    uibhbotBoundaryHitTime j W by omega] at ha
  simpa [lemma38StartVertexι, uibhbotBusemannSource, uibhbotFutureVertex] using ha

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Boundary labels above one are identified using the run at cutoff `k + 1`.
Its globally strict record at level `k` supplies a missing edge, and descending
along the same boundary reaches the original ordered root edge. -/
theorem UIBHBOTIntrinsicIncrementBoundaryAboveOneIdentification_proved :
    UIBHBOTIntrinsicIncrementBoundaryAboveOneIdentification := by
  filter_upwards [ae_incrementClose_root_code, ae_uibhbotBoundaryHit,
    ae_uibhbotBoundaryHit_strictRecord] with W hW hh hr H hhit C k hk
  let A := k + 1
  have htA : uibhbotBoundaryHitTime A W < 0 := by
    have ho := incrementClose2_hit_order W hh hr 0 A (by dsimp [A]; omega)
    rwa [hW.1] at ho
  let N := (uibhbotBoundaryHitTime A W).natAbs
  have hN : 1 ≤ N := by dsimp [N]; omega
  have htime : -(N : ℤ) = uibhbotBoundaryHitTime A W := by
    have he := Int.ofNat_natAbs_of_nonpos (le_of_lt htA)
    dsimp only [N]
    omega
  have hstart : (wholePlaneWordIntegral W (-(N : ℤ))).1 = A := by
    rw [htime, (hh A).1]
  have ht (j : ℤ) (hj : j < A) : -(N : ℤ) < uibhbotBoundaryHitTime j W := by
    rw [htime]
    exact incrementClose2_hit_order W hh hr j A hj
  have hrootHit := incrementClose2_hit W N A 0 hstart hh hr (hhit N)
    (by dsimp [A]; omega) (ht 0 (by dsimp [A]; omega))
  rw [hW.1] at hrootHit
  simp only [zero_sub, zero_add, Int.toNat_natCast] at hrootHit
  have hrootRec : ∀ j < N, L (shiftedStream W N) N < L (shiftedStream W N) j := by
    intro j hj
    rw [incrementClose_run_L, incrementClose_run_L, sub_self]
    have hp := hr 0 ((j : ℤ) - N) (by rw [hW.1]; omega)
    have hz : (wholePlaneWordIntegral W 0).1 = 0 := by
      simp [wholePlaneWordIntegral]
    rw [hz]
    omega
  have hroot : wholePlaneEdgeι W N
      (boundaryOuterEdge (shiftedStream W N) (hhit N) (-A)) = uibhbotRootEdge W := by
    rw [boundaryOuterEdge_of_negative _ _ (by dsimp [A]; omega), hrootHit]
    exact (uibhbotRootEdge_eq_window W N hN hrootRec).symm
  have hkA : k - A = -1 := by dsimp [A]; omega
  have htargetHit := incrementClose2_hit W N A k hstart hh hr (hhit N)
    (by dsimp [A]; omega) (ht k (by dsimp [A]; omega))
  rw [hkA] at htargetHit
  let n := (uibhbotBoundaryHitTime k W + N).toNat
  have hn : 0 < n := by
    have hp := ht k (by dsimp [A]; omega)
    dsimp [n]
    omega
  have hnval : (n : ℤ) - N = uibhbotBoundaryHitTime k W := by
    have hp := ht k (by dsimp [A]; omega)
    dsimp [n]
    omega
  have hmissing : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N
        (boundaryOuterEdge (shiftedStream W N) (hhit N) (-1))) := by
    rw [boundaryOuterEdge_of_negative _ _ (by omega), htargetHit]
    apply incrementClose2_record_missing W N n hn
    intro M hNM j hj
    rw [incrementClose_run_L, incrementClose_run_L]
    have he : ((M - N + n : ℕ) : ℤ) - M = uibhbotBoundaryHitTime k W := by
      omega
    rw [he, (hh k).1]
    have hp := hr k ((j : ℤ) - M) (by omega)
    omega
  have hd := (incrementClose2_descend W H N (hhit N) (-1) (by omega)
    hmissing k.toNat).2
  have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
  rw [hkn, show -1 - k = -A by dsimp [A]; omega] at hd
  have hrootDart : incrementClose2_boundaryDart W N (hhit N) (-A) =
      uibhbotWholePlaneFrameEdgeDart W :=
    congrArg (fun e => ((e, false) : WholePlaneDart W)) hroot
  rw [hrootDart] at hd
  let f := wholePlaneRotation W H * wholePlaneDartFlip W
  have hforward : (f ^ k) (uibhbotWholePlaneFrameEdgeDart W) =
      incrementClose2_boundaryDart W N (hhit N) (-1) := by
    apply (f ^ (-k)).injective
    rw [← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
      Equiv.Perm.one_apply]
    exact hd.symm
  apply congrArg UIBHBOTPresentVertex.mk
  change wholePlaneDartVertex W ((f ^ k) (uibhbotWholePlaneFrameEdgeDart W)) = _
  rw [hforward]
  change wholePlaneEdgeWest W (wholePlaneEdgeι W N
    (boundaryOuterEdge (shiftedStream W N) (hhit N) (-1))) = _
  rw [wholePlaneEdgeWest_ι, (boundaryOuterEdge_endpoints _ _ _).1]
  have hs := incrementClose2_source W N A k hstart hh hr (hhit N)
    (by dsimp [A]; omega) (ht k (by dsimp [A]; omega))
  rwa [hkA] at hs

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
All integer boundary labels now have their intrinsic identification. -/
theorem UIBHBOTIntrinsicIncrementBoundaryIdentification_proved :
    UIBHBOTIntrinsicIncrementBoundaryIdentification := by
  exact UIBHBOTIntrinsicIncrementBoundaryIdentification_iff_aboveOne.mpr
    UIBHBOTIntrinsicIncrementBoundaryAboveOneIdentification_proved

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
At every integer source index, the explicit code targets realize the increment
in restricted intrinsic balls. The radius may depend on the target; this does not
assert consensus over finite faced-ball shells. -/
theorem ae_incrementClose2_target_radius_stabilization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        ∃ B : ℕ, ∀ m ≥ B,
          ∃ t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H),
            incrementOrbitVertex W H t = uibhbotBusemannTarget k W m ∧
            ∃ a b : ℕ, ∃ R : ℕ, ∀ r ≥ R,
              incrementClose_ballLdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r
                  (intrinsicIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) t =
                ((a : ℕ∞) : WithBot ℕ∞) ∧
              incrementClose_ballLdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r
                  (intrinsicIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) (k - 1)) t =
                ((b : ℕ∞) : WithBot ℕ∞) ∧
              uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ) := by
  filter_upwards [UIBHBOTIntrinsicIncrementBoundaryIdentification_proved,
    ae_uibhbotBusemannIncrement_distance_realization] with W hs hreal H hhit C k
  obtain ⟨_, B, hB⟩ := hreal k
  refine ⟨B, fun m hm => ?_⟩
  let t := incrementClose_intrinsicTarget W H k m
  have ht : incrementOrbitVertex W H t = uibhbotBusemannTarget k W m :=
    incrementClose_intrinsicTarget_image W H k m
  refine ⟨t, ht, ?_⟩
  obtain ⟨hr0, hr1, a, b, ha, hb, hi⟩ := hB m hm
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  let s := intrinsicIncrementSource M k
  let s' := intrinsicIncrementSource M (k - 1)
  have hs0 : incrementOrbitVertex W H s = uibhbotBusemannSource k W :=
    hs H hhit C k
  have hs1 : incrementOrbitVertex W H s' = uibhbotBusemannSource (k - 1) W :=
    hs H hhit C (k - 1)
  have hreach0 : Reachable (incrementOrbitVertex W H s) (incrementOrbitVertex W H t) := by
    rw [hs0, ht]
    exact hr0
  have hreach1 : Reachable (incrementOrbitVertex W H s') (incrementOrbitVertex W H t) := by
    rw [hs1, ht]
    exact hr1
  have hfinite0 : uibhbotLdp (incrementOrbitVertex W H s) (incrementOrbitVertex W H t) =
      ((a : ℕ∞) : WithBot ℕ∞) := by rw [hs0, ht]; exact ha
  have hfinite1 : uibhbotLdp (incrementOrbitVertex W H s') (incrementOrbitVertex W H t) =
      ((b : ℕ∞) : WithBot ℕ∞) := by rw [hs1, ht]; exact hb
  obtain ⟨ds, hd, hlen⟩ :=
    incrementClose_intrinsic_attaining W H hhit C s t a hreach0 hfinite0
  obtain ⟨es, he, elen⟩ :=
    incrementClose_intrinsic_attaining W H hhit C s' t b hreach1 hfinite1
  have hfull0 : intrinsicIncrementLdp M s t = ((a : ℕ∞) : WithBot ℕ∞) :=
    (intrinsicIncrementLdp_eq_uibhbotLdp W H hhit C s t).trans hfinite0
  have hfull1 : intrinsicIncrementLdp M s' t = ((b : ℕ∞) : WithBot ℕ∞) :=
    (intrinsicIncrementLdp_eq_uibhbotLdp W H hhit C s' t).trans hfinite1
  obtain ⟨R0, _, hR0⟩ := incrementClose_ballLdp_stabilizes_of_attaining M s t ds hd
    (hfull0.trans (congrArg (fun l : ℕ => ((l : ℕ∞) : WithBot ℕ∞)) hlen.symm)) 0
  obtain ⟨R1, _, hR1⟩ := incrementClose_ballLdp_stabilizes_of_attaining M s' t es he
    (hfull1.trans (congrArg (fun l : ℕ => ((l : ℕ∞) : WithBot ℕ∞)) elen.symm)) 0
  refine ⟨a, b, max R0 R1, fun r hr => ?_⟩
  exact ⟨(hR0 r ((le_max_left _ _).trans hr)).trans hfull0,
    (hR1 r ((le_max_right _ _).trans hr)).trans hfull1, hi⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The proved mirror-law invariance discharges the former transport premise. -/
theorem uibhbotIncrementClose2_law_mirror_invariant :
    (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
      mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw := by
  exact uibhbotLaw_mirror_invariant
    DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed




theorem hsym_ldp_proved
    (hshell : UIBHBOTIncrementBallShellStabilization)
    (hreflect : UIBHBOTIncrementObservableReflection finiteBallIncrementObservable) :
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) := by
  exact hsym_of_uibhbot_mirror_invariance finiteBallIncrementObservable
    finiteBallIncrementObservable_measurable
    (finiteBallIncrementObservable_realization_of_ballShellStabilization hshell)
    hreflect UIBHBOTIncrementMirrorMeasurable_proved
    uibhbotIncrementClose2_law_mirror_invariant

end DirectedDistances.PaperProofs.Section5
