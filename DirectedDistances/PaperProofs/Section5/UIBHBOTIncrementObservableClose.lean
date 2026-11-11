module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservable
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorContinuity
import DirectedDistances.KMSW.BoundaryVertexVisits








public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW Quiver
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The helper faced-ball topology used by the rooted-map law. -/
noncomputable local instance incrementCloseTopology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel measurable structure used by the rooted-map law. -/
noncomputable local instance incrementCloseMeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The mirror's measure-transport obligation follows from its proved Borel measurability. -/
theorem UIBHBOTIncrementMirrorMeasurable_proved : UIBHBOTIncrementMirrorMeasurable := by
  exact measurable_mirrorRootedLocallyFinitePlanarMap.aemeasurable

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The index-zero intrinsic source is the first ordered frame endpoint. -/
theorem intrinsicIncrementSource_zero (M : RootedLocallyFiniteMap) :
    intrinsicIncrementSource M 0 = rootedLocallyFiniteVertexClass M.rot M.frameEdgeDart := by
  simp only [intrinsicIncrementSource, zpow_zero, Equiv.Perm.one_apply]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The index-one intrinsic source is the opposite endpoint of the actual frame edge. -/
theorem intrinsicIncrementSource_one (M : RootedLocallyFiniteMap) :
    intrinsicIncrementSource M 1 =
      rootedLocallyFiniteVertexClass M.rot (M.edgeInv M.frameEdgeDart) := by
  apply Quotient.sound
  refine ⟨-1, ?_⟩
  simp only [zpow_one, Equiv.Perm.mul_apply, zpow_neg_one,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The source code almost surely hits boundary level zero at zero, with a left step
immediately before that hit. This fixes the ordered frame's first endpoint. -/
theorem ae_incrementClose_root_code :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      uibhbotBoundaryHitTime 0 W = 0 ∧ W (-1) = 0 := by
  have hm : MeasurableSet {W : ℤ → Fin 3 |
      uibhbotBoundaryHitTime 0 W = 0 ∧ W (-1) = 0} :=
    (measurableSet_eq_fun (measurable_uibhbotBoundaryHitTime 0) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply (-1)) measurable_const)
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable hm).mpr
  filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw
  constructor
  · rw [uibhbotBoundaryHitTime_codeWordRel 0 w hw]
    simp only [neg_zero, uibhbotBlockBoundary_zero]
  · rw [uibhbotCodeWordRel_eq w (fun j => (hw j).1)]
    have hr := uibhbotCode_strictRecord w hw 1 (by omega) 0 (by omega)
    simp only [L, Finset.sum_range_one, Finset.sum_range_zero, shiftedStream,
      Nat.cast_zero, zero_sub, Nat.cast_one] at hr
    change ((uibhbotCodeWord w (fun j => (hw j).1) (-1) : ℤ) - 1) < 0 at hr
    apply Fin.ext
    omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
At a left step immediately before zero, the first root endpoint is the initial
vertex of the future starting at zero. No boundary traversal is presumed. -/
theorem incrementClose_rootFirstVertex (W : ℤ → Fin 3) (hc : W (-1) = 0) :
    uibhbotRootFirstVertex W = lemma38StartVertexι W 0 0 := by
  let w := shiftedStream W 1
  have hw : w 0 = 0 := by simpa [w, shiftedStream] using hc
  have hr : ∀ j < 1, L w 1 < L w j := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simp only [L, Finset.sum_range_one, Finset.sum_range_zero, hw]
    decide
  have hb : kmswLLCreatedEdge w 1 < (kmswStage w 1).nextEdge := by
    simp [kmswLLCreatedEdge, kmswStage, kmswStep, hw, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge]
  have he : edgeWest w (kmswLLCreatedEdge w 1) = activeInitial w 1 := by
    rw [← (edge_endpoints_eq w hb).1, kmswLLCreatedEdge_west_eq_act w (by omega) hr]
    exact (CutConverse.activeInitial_eq w 1).symm
  change wholePlaneEdgeWest W
    (wholePlaneEdgeι W 1 (kmswLLCreatedEdge w 1)) = _
  rw [wholePlaneEdgeWest_ι, he]
  have ha := uibhbotStartVertex_activeInitial W (-1) 1
  have hs : lemma38StartStream W (-1) = w := by
    funext i
    simp only [lemma38StartStream, w, shiftedStream, Nat.cast_one, sub_eq_add_neg]
  rw [hs] at ha
  simpa [lemma38StartVertexι] using ha

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The boundary identification is proved at index zero, simultaneously for every
choice of the construction certificates. The remaining indices stay open. -/
theorem ae_intrinsicIncrementSource_zero_identification :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0),
        incrementOrbitVertex W H
            (intrinsicIncrementSource (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              0) = uibhbotBusemannSource 0 W := by
  filter_upwards [ae_incrementClose_root_code] with W hW H hhit C
  rw [intrinsicIncrementSource_zero]
  apply congrArg UIBHBOTPresentVertex.mk
  change uibhbotRootFirstVertex W = uibhbotFutureVertex 0 W 0
  rw [incrementClose_rootFirstVertex W hW.2]
  simp only [uibhbotFutureVertex, hW.1]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The run starting at minus one has the absolute horizontal coordinate shifted by one
when its first step is left. -/
theorem incrementClose_runOne_L (W : ℤ → Fin 3) (hc : W (-1) = 0) (n : ℕ) :
    L (shiftedStream W 1) n = (wholePlaneWordIntegral W ((n : ℤ) - 1)).1 - 1 := by
  have hs : lemma38StartStream W (-1) = shiftedStream W 1 := by
    funext i
    simp [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  have ha : (wholePlaneWordIntegral W (-1)).1 = 1 := by
    simp [wholePlaneWordIntegral, hc, lazyTwoDimensionalStep]
  have he := uibhbotStart_L W (-1) n
  rw [hs, ha] at he
  simpa only [sub_eq_add_neg, add_comm (-1 : ℤ)] using he

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Absolute first-hit times at nonpositive levels equal the left boundary hit times
in the run starting at minus one, with the precise index and time shifts. -/
theorem incrementClose_runOne_hit (W : ℤ → Fin 3) (hc : W (-1) = 0)
    (hz : uibhbotBoundaryHitTime 0 W = 0)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1)
    (h : BoundaryHitWitnesses (shiftedStream W 1)) (k : ℤ) (hk : k ≤ 0) :
    boundaryHitTime (shiftedStream W 1) h (k - 1) =
      (uibhbotBoundaryHitTime k W + 1).toNat := by
  have ht : 0 ≤ uibhbotBoundaryHitTime k W := by
    by_contra hn
    have hp := hr 0 (uibhbotBoundaryHitTime k W) (by omega)
    rw [(hh k).1] at hp
    omega
  have hj : k - 1 ≤ -1 := by omega
  have hhit : L (shiftedStream W 1) (uibhbotBoundaryHitTime k W + 1).toNat = k - 1 := by
    rw [incrementClose_runOne_L W hc]
    have he : ((uibhbotBoundaryHitTime k W + 1).toNat : ℤ) - 1 =
        uibhbotBoundaryHitTime k W := by omega
    rw [he, (hh k).1]
  have hfind : boundaryHitTime (shiftedStream W 1) h (k - 1) =
      Nat.find (h.leftHit (k - 1) hj) := by
    unfold boundaryHitTime
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  apply le_antisymm
  · rw [hfind]
    exact Nat.find_min' _ hhit
  · by_contra hn
    have hs := boundaryHitTime_left_spec (shiftedStream W 1) h hj
    rw [incrementClose_runOne_L W hc] at hs
    have hp := hr k
      ((boundaryHitTime (shiftedStream W 1) h (k - 1) : ℤ) - 1) (by omega)
    omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The negative boundary vertices of the run starting at minus one coincide with the
specified absolute code boundary sources. -/
theorem incrementClose_runOne_source (W : ℤ → Fin 3) (hc : W (-1) = 0)
    (hz : uibhbotBoundaryHitTime 0 W = 0)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1)
    (h : BoundaryHitWitnesses (shiftedStream W 1)) (k : ℤ) (hk : k ≤ 0) :
    wholePlaneVertexι W 1 (boundaryVertex (shiftedStream W 1) h (k - 1)) =
      (uibhbotBusemannSource k W).id := by
  rw [boundaryVertex_eq_activeInitial _ h (by omega) (by omega),
    incrementClose_runOne_hit W hc hz hh hr h k hk]
  have ha := uibhbotStartVertex_activeInitial W (-1)
    (uibhbotBoundaryHitTime k W + 1).toNat
  have hs : lemma38StartStream W (-1) = shiftedStream W 1 := by
    funext i
    simp [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  rw [hs] at ha
  have ht : 0 ≤ uibhbotBoundaryHitTime k W := by
    by_contra hn
    have hp := hr 0 (uibhbotBoundaryHitTime k W) (by omega)
    rw [(hh k).1] at hp
    omega
  have he : (-1 : ℤ) + (uibhbotBoundaryHitTime k W + 1).toNat =
      uibhbotBoundaryHitTime k W := by omega
  rw [he] at ha
  simpa [lemma38StartVertexι, uibhbotBusemannSource, uibhbotFutureVertex] using ha

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Negative powers of the opposite-face traversal follow the actual missing-edge
chain. Every edge stays globally missing throughout this induction. -/
theorem incrementClose_negative_dart (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    (hc : W (-1) = 0) (hz : uibhbotBoundaryHitTime 0 W = 0)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1) (n : ℕ) :
    let e := wholePlaneEdgeι W 1
      (boundaryOuterEdge (shiftedStream W 1) (hhit 1) (-1 - (n : ℤ)))
    ¬ wholePlaneEdgePresent W e ∧
      ((wholePlaneRotation W H * wholePlaneDartFlip W) ^ (-(n : ℤ)))
        (uibhbotWholePlaneFrameEdgeDart W) = (e, false) := by
  have he0 : wholePlaneEdgeι W 1
      (boundaryOuterEdge (shiftedStream W 1) (hhit 1) (-1)) = uibhbotRootEdge W := by
    rw [boundaryOuterEdge_of_negative _ _ (by omega)]
    have ht := incrementClose_runOne_hit W hc hz hh hr (hhit 1) 0 le_rfl
    rw [hz] at ht
    norm_num only [zero_sub, zero_add, Int.toNat_one] at ht
    rw [ht]
    rfl
  induction n with
  | zero =>
    dsimp only
    simp only [Nat.cast_zero, sub_zero, he0]
    exact ⟨C.root_missing_wholePlane, rfl⟩
  | succ n ih =>
    dsimp only at ih ⊢
    obtain ⟨hm, hf⟩ := wholePlane_missing_boundary_faceSucc W H 1 (hhit 1)
      (-1 - (n : ℤ)) (by omega) ih.1
    have he : -1 - ((n + 1 : ℕ) : ℤ) = (-1 - (n : ℤ)) - 1 := by omega
    rw [he]
    refine ⟨hm, ?_⟩
    have hp : -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) := by omega
    rw [hp, zpow_add, Equiv.Perm.mul_apply, ih.2, zpow_neg_one]
    have hhf := congrArg (wholePlaneDartFlip W) hf
    change wholePlaneDartFlip W
      ((wholePlaneRotation W H).symm
        (wholePlaneEdgeι W 1
          (boundaryOuterEdge (shiftedStream W 1) (hhit 1) (-1 - (n : ℤ))), false)) =
      (wholePlaneEdgeι W 1
        (boundaryOuterEdge (shiftedStream W 1) (hhit 1) (-1 - (n : ℤ) - 1)), false)
      at hhf
    exact hhf

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic and code boundary labels agree simultaneously at every nonpositive
integer. Positive boundary indices remain a separate geometric obligation. -/
theorem ae_intrinsicIncrementSource_nonpos_identification :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ), k ≤ 0 →
        incrementOrbitVertex W H
            (intrinsicIncrementSource (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              k) = uibhbotBusemannSource k W := by
  filter_upwards [ae_incrementClose_root_code, ae_uibhbotBoundaryHit,
    ae_uibhbotBoundaryHit_strictRecord] with W hW hh hr H hhit C k hk
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
  subst k
  have hd := (incrementClose_negative_dart W H hhit C hW.2 hW.1 hh hr n).2
  apply congrArg UIBHBOTPresentVertex.mk
  change wholePlaneDartVertex W
    (((wholePlaneRotation W H * wholePlaneDartFlip W) ^ (-(n : ℤ)))
      (uibhbotWholePlaneFrameEdgeDart W)) = _
  rw [hd]
  change wholePlaneEdgeWest W
    (wholePlaneEdgeι W 1
      (boundaryOuterEdge (shiftedStream W 1) (hhit 1) (-1 - (n : ℤ)))) = _
  rw [wholePlaneEdgeWest_ι, (boundaryOuterEdge_endpoints _ _ _).1]
  have he : -1 - (n : ℤ) = -(n : ℤ) - 1 := by omega
  rw [he]
  exact incrementClose_runOne_source W hW.2 hW.1 hh hr (hhit 1) (-(n : ℤ)) (by omega)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Absolute coordinates determine the horizontal coordinate in any earlier-start run. -/
theorem incrementClose_run_L (W : ℤ → Fin 3) (N n : ℕ) :
    L (shiftedStream W N) n =
      (wholePlaneWordIntegral W ((n : ℤ) - N)).1 -
        (wholePlaneWordIntegral W (-(N : ℤ))).1 := by
  have hs : lemma38StartStream W (-(N : ℤ)) = shiftedStream W N := by
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  have he := uibhbotStart_L W (-(N : ℤ)) n
  rw [hs] at he
  simpa only [sub_eq_add_neg, add_comm (-(N : ℤ))] using he

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A negative-coordinate strict record identifies its exact one-sided boundary hit time. -/
theorem incrementClose_left_hit_eq (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (j : ℤ) (hj : j ≤ -1) (n : ℕ) (hn : L w n = j)
    (hb : ∀ i < n, j < L w i) : boundaryHitTime w h j = n := by
  have hf : boundaryHitTime w h j = Nat.find (h.leftHit j hj) := by
    unfold boundaryHitTime
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  apply le_antisymm
  · rw [hf]
    exact Nat.find_min' _ hn
  · by_contra hn'
    have hs := boundaryHitTime_left_spec w h hj
    have hh := hb (boundaryHitTime w h j) (by omega)
    omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The second ordered frame endpoint is the absolute source with boundary index one.
The proof uses the run starting exactly at the first absolute hit of level one. -/
theorem incrementClose_rootSecondVertex (W : ℤ → Fin 3)
    (hz : uibhbotBoundaryHitTime 0 W = 0)
    (hh : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hr : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N)) :
    uibhbotRootSecondVertex W = (uibhbotBusemannSource 1 W).id := by
  have ht : uibhbotBoundaryHitTime 1 W < 0 := by
    by_contra hn
    by_cases he : uibhbotBoundaryHitTime 1 W = 0
    · have hv := (hh 1).1
      rw [he] at hv
      norm_num [wholePlaneWordIntegral] at hv
    · have hp := hr 1 0 (by omega)
      norm_num [wholePlaneWordIntegral] at hp
  let N := (uibhbotBoundaryHitTime 1 W).natAbs
  have hN : 1 ≤ N := by dsimp [N]; omega
  have htime : -(N : ℤ) = uibhbotBoundaryHitTime 1 W := by
    have he := Int.ofNat_natAbs_of_nonpos (le_of_lt ht)
    dsimp only [N]
    omega
  have hval : L (shiftedStream W N) N = -1 := by
    rw [incrementClose_run_L, sub_self, htime, (hh 1).1]
    norm_num [wholePlaneWordIntegral]
  have hbefore : ∀ i < N, (-1 : ℤ) < L (shiftedStream W N) i := by
    intro i hi
    rw [incrementClose_run_L, htime, (hh 1).1]
    have hp := hr 0 ((i : ℤ) - N) (by omega)
    omega
  have hrec : ∀ i < N, L (shiftedStream W N) N < L (shiftedStream W N) i := by
    intro i hi
    rw [hval]
    exact hbefore i hi
  have hboundary := incrementClose_left_hit_eq (shiftedStream W N) (hhit N)
    (-1) (by omega) N hval hbefore
  have hedge : boundaryOuterEdge (shiftedStream W N) (hhit N) (-1) =
      kmswLLCreatedEdge (shiftedStream W N) N := by
    rw [boundaryOuterEdge_of_negative _ _ (by omega), hboundary]
  change wholePlaneEdgeEast W (uibhbotRootEdge W) = _
  rw [uibhbotRootEdge_eq_window W N hN hrec, wholePlaneEdgeEast_ι, ← hedge,
    (boundaryOuterEdge_endpoints _ _ _).2.1]
  simp only [neg_add_cancel, boundaryVertex_zero]
  change wholePlaneVertexι W N 0 = lemma38StartVertexι W (uibhbotBoundaryHitTime 1 W) 0
  rw [lemma38StartVertexι, ite_eq_left (le_of_lt ht)]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic and code boundary labels agree also at the second ordered frame endpoint. -/
theorem ae_intrinsicIncrementSource_one_identification :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0),
        incrementOrbitVertex W H
            (intrinsicIncrementSource (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              1) = uibhbotBusemannSource 1 W := by
  filter_upwards [ae_incrementClose_root_code, ae_uibhbotBoundaryHit,
    ae_uibhbotBoundaryHit_strictRecord] with W hW hh hr H hhit C
  rw [intrinsicIncrementSource_one]
  apply congrArg UIBHBOTPresentVertex.mk
  exact incrementClose_rootSecondVertex W hW.1 hh hr hhit

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The simultaneous boundary identification includes both ordered frame endpoints and
all indices to their west. Indices above one are not claimed here. -/
theorem ae_intrinsicIncrementSource_le_one_identification :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ), k ≤ 1 →
        incrementOrbitVertex W H
            (intrinsicIncrementSource (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              k) = uibhbotBusemannSource k W := by
  filter_upwards [ae_intrinsicIncrementSource_nonpos_identification,
    ae_intrinsicIncrementSource_one_identification] with W hn hp H hhit C k hk
  by_cases hk0 : k ≤ 0
  · exact hn H hhit C k hk0
  · have he : k = 1 := by omega
    subst k
    exact hp H hhit C





@[expose] noncomputable def incrementClose_ballLdp (M : RootedLocallyFiniteMap)
    (r : ℕ) (s t : RootedLocallyFiniteVertex M.D M.rot) : WithBot ℕ∞ :=
  ⨆ ds : List M.D, ⨆ (_ : incrementDartWalk M ds s t),
    ⨆ (_ : ∀ d ∈ ds, d ∈ rootedLocallyFiniteBallDarts M r),
      ((ds.length : ℕ∞) : WithBot ℕ∞)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Restricting admissible dart lists cannot increase the full extended LDP. -/
theorem incrementClose_ballLdp_le (M : RootedLocallyFiniteMap) (r : ℕ)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    incrementClose_ballLdp M r s t ≤ intrinsicIncrementLdp M s t := by
  apply iSup_le
  intro ds
  apply iSup_le
  intro hw
  apply iSup_le
  intro _hd
  exact le_iSup_of_le ds (le_iSup_of_le hw le_rfl)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A genuinely attaining walk is contained in a finite ball, after which every
larger restricted distance equals the full distance. No subtraction of infinite
distances or replacement of an unreachable distance occurs. -/
theorem incrementClose_ballLdp_stabilizes_of_attaining (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) (ds : List M.D)
    (hw : incrementDartWalk M ds s t)
    (ha : intrinsicIncrementLdp M s t = ((ds.length : ℕ∞) : WithBot ℕ∞)) (r₀ : ℕ) :
    ∃ R : ℕ, r₀ ≤ R ∧ ∀ r ≥ R,
      incrementClose_ballLdp M r s t = intrinsicIncrementLdp M s t := by
  obtain ⟨R, hR, hd⟩ := incrementDartList_captured M r₀ ds
  refine ⟨R, hR, fun r hr => le_antisymm (incrementClose_ballLdp_le M r s t) ?_⟩
  rw [ha]
  exact le_iSup_of_le ds (le_iSup_of_le hw
    (le_iSup_of_le (fun d hds => rootedLocallyFiniteBallDarts_mono M hr (hd d hds))
      le_rfl))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every reachable finite code LDP is attained by an intrinsic walk of precisely
that finite length. Boundedness follows from the stated full extended distance. -/
theorem incrementClose_intrinsic_attaining (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    (s t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H))
    (n : ℕ) (hr : Reachable (incrementOrbitVertex W H s) (incrementOrbitVertex W H t))
    (hn : uibhbotLdp (incrementOrbitVertex W H s) (incrementOrbitVertex W H t) =
      ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ ds : List (WholePlaneDart W),
      incrementDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) ds s t ∧
        ds.length = n := by
  have hb : BddAbove (pathLengths (incrementOrbitVertex W H s)
      (incrementOrbitVertex W H t)) := by
    refine ⟨n, ?_⟩
    rintro l ⟨p, rfl⟩
    have hp : ((p.length : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) :=
      (le_iSup (fun q : Path (incrementOrbitVertex W H s)
        (incrementOrbitVertex W H t) => ((q.length : ℕ∞) : WithBot ℕ∞)) p).trans_eq hn
    exact_mod_cast hp
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove hb hr
  have he : uibhbotLdp (incrementOrbitVertex W H s) (incrementOrbitVertex W H t) =
      ((p.length : ℕ∞) : WithBot ℕ∞) := by
    apply le_antisymm
    · apply iSup_le
      intro q
      exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (hp q))
    · exact le_iSup (fun q : Path (incrementOrbitVertex W H s)
        (incrementOrbitVertex W H t) => ((q.length : ℕ∞) : WithBot ℕ∞)) p
  have hlen : p.length = n := by exact_mod_cast he.symm.trans hn
  obtain ⟨ds, hd, hl⟩ := codePath_to_incrementDartWalk W H hhit C p s t rfl rfl
  exact ⟨ds, hd, hl.trans hlen⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
An explicit intrinsic representative of the existing code target, using the
actual active edge at its totalized hit time. No preimage is chosen. -/
@[expose] noncomputable def incrementClose_intrinsicTarget (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (k : ℤ) (m : ℕ) :
    RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) :=
  rootedLocallyFiniteVertexClass (wholePlaneRotation W H)
    (uibhbotFutureEdge k W
      (act (fun i => uibhbotFutureCode k W (i + 1))
        (boundaryHitTimeTotal (uibhbotFutureCode k W) (m : ℤ)).toNat), false)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The specified intrinsic target represents exactly the supplied code target,
including before restriction to the probability-one hit-witness event. -/
theorem incrementClose_intrinsicTarget_image (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (k : ℤ) (m : ℕ) :
    incrementOrbitVertex W H (incrementClose_intrinsicTarget W H k m) =
      uibhbotBusemannTarget k W m := by
  apply congrArg UIBHBOTPresentVertex.mk
  change wholePlaneEdgeWest W (uibhbotFutureEdge k W
    (act (fun i => uibhbotFutureCode k W (i + 1))
      (boundaryHitTimeTotal (uibhbotFutureCode k W) (m : ℤ)).toNat)) =
    uibhbotFutureVertex k W (busemannBoundaryIdTotal (uibhbotFutureCode k W) (m : ℤ))
  rw [uibhbotFutureEdge_west]
  apply congrArg (uibhbotFutureVertex k W)
  exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1.symm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
For source indices at most one, the explicit code target sequence realizes the
increment using finite restricted intrinsic distances at every sufficiently large
radius. Targets have explicit intrinsic representatives. This does not prove consensus
over every common reachable target in a shell of a finite faced-ball representative. -/
theorem ae_incrementClose_target_radius_stabilization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ), k ≤ 1 →
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
  filter_upwards [ae_intrinsicIncrementSource_le_one_identification,
    ae_uibhbotBusemannIncrement_distance_realization] with W hs hreal H hhit C k hk
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
    hs H hhit C k hk
  have hs1 : incrementOrbitVertex W H s' = uibhbotBusemannSource (k - 1) W :=
    hs H hhit C (k - 1) (by omega)
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
Two-stage shell stabilization suffices for code realization. The geometric
stabilization proposition remains an explicit open premise of this helper. -/
theorem finiteBallIncrementObservable_realization_of_ballShellStabilization
    (h : UIBHBOTIncrementBallShellStabilization) :
    UIBHBOTIncrementObservableRealization finiteBallIncrementObservable := by
  filter_upwards [h] with W hW k
  have he := (finiteBallIncrementCandidate_eq_some_iff k
    (uibhbotRootedPlanarMapOfCode W) (uibhbotBusemannIncrement k W)).2 (hW k)
  simp only [finiteBallIncrementObservable, he, Option.getD_some]




@[expose] def UIBHBOTIntrinsicIncrementBoundaryAboveOneIdentification : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∀ (H : WholePlaneRotationHypothesis W)
      (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ), 1 < k →
      incrementOrbitVertex W H
          (intrinsicIncrementSource (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) =
        uibhbotBusemannSource k W

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The full open boundary obligation reduces exactly to the remaining indices above
one. This equivalence does not prove either of the open propositions. -/
theorem UIBHBOTIntrinsicIncrementBoundaryIdentification_iff_aboveOne :
    UIBHBOTIntrinsicIncrementBoundaryIdentification ↔
      UIBHBOTIntrinsicIncrementBoundaryAboveOneIdentification := by
  constructor
  · intro h
    filter_upwards [h] with W hW H hhit C k _hk
    exact hW H hhit C k
  · intro h
    filter_upwards [h, ae_intrinsicIncrementSource_le_one_identification]
      with W hW hl H hhit C k
    by_cases hk : k ≤ 1
    · exact hl H hhit C k hk
    · exact hW H hhit C k (by omega)




theorem hsym_of_uibhbot_law_mirror_invariant_of_open_obligations
    (hshell : UIBHBOTIncrementBallShellStabilization)
    (hreflect : UIBHBOTIncrementObservableReflection finiteBallIncrementObservable)
    (hinv : (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
      mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw) :
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) := by
  exact hsym_of_uibhbot_mirror_invariance finiteBallIncrementObservable
    finiteBallIncrementObservable_measurable
    (finiteBallIncrementObservable_realization_of_ballShellStabilization hshell)
    hreflect UIBHBOTIncrementMirrorMeasurable_proved hinv

end DirectedDistances.PaperProofs.Section5
