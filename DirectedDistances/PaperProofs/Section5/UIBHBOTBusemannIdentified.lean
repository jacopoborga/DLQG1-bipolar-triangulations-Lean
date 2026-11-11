/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBusemannFunction
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryLabels
public import DirectedDistances.KMSW.BoundaryLabelling
public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified
import DirectedDistances.KMSW.WholePlaneLLRecordEdges

/-! Boundary-edge identification and helpers for Proposition 5.11. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory Filter Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7

 
private theorem prop511_left_record_creation (w : ℕ → Fin 3) (n : ℕ)
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

 
private theorem prop511_dropLast_reverse_eq_nil_of_length_one (xs : List ℕ)
    (h : xs.length = 1) : xs.dropLast.reverse = [] := by
  have hd : xs.dropLast = [] := List.length_eq_zero_iff.mp (by
    rw [List.length_dropLast, h])
  rw [hd]
  rfl

 
private theorem prop511_windowMap_LL_created (w : ℕ → Fin 3) (s n : ℕ)
    (hrec : ∀ j < s + (n + 1), L w (s + (n + 1)) < L w j) :
    kmswWindowEdgeMapInf w s (kmswLLCreatedEdge (fun i => w (s + i)) (n + 1)) =
      kmswLLCreatedEdge w (s + (n + 1)) := by
  let v := fun i => w (s + i)
  let pre := kmswStage v n
  let globalPre := kmswStage w (s + n)
  let data := kmswWindowPatchData w s n
  have hcreation := prop511_left_record_creation w (s + n) (by
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
  have hdrop := prop511_dropLast_reverse_eq_nil_of_length_one pre.UL hpreLen
  have hglobalDrop := prop511_dropLast_reverse_eq_nil_of_length_one globalPre.UL hglobalLen
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

 
private theorem prop511_record_missing (W : ℤ → Fin 3) (N n : ℕ)
    (hn : 0 < n)
    (hr : ∀ M, N ≤ M → ∀ j < M - N + n,
      L (shiftedStream W M) (M - N + n) < L (shiftedStream W M) j) :
    ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n)) := by
  intro hp
  obtain ⟨M, hNM, hM⟩ := (wholePlaneEdgePresent_ι W N _).mp hp
  have hpres := hM M le_rfl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hmap := prop511_windowMap_LL_created (shiftedStream W M) (M - N) m
    (hr M hNM)
  rw [shiftedStream_shift W N M hNM] at hmap
  change EdgePresent (shiftedStream W M)
    (kmswWindowEdgeMapInf (shiftedStream W M) (M - N)
      (kmswLLCreatedEdge (shiftedStream W N) (m + 1))) at hpres
  rw [hmap] at hpres
  exact kmswLLCreatedEdge_not_present_of_record _ _ (by omega) (hr M hNM) hpres

 
private theorem prop511_startEdge_cofinal (W : ℤ → Fin 3) (t : ℤ) (N : ℕ)
    (hN : t.natAbs ≤ N) (e : ℕ) :
    lemma38StartEdgeι W t e = wholePlaneEdgeι W N
      (kmswWindowEdgeMapInf (shiftedStream W N) (t + (N : ℤ)).toNat e) := by
  by_cases ht : t ≤ 0
  · rw [lemma38StartEdgeι, ite_eq_left ht]
    have hc := congrFun (wholePlaneEdgeι_trans W t.natAbs N hN) e
    have ha : (t + (N : ℤ)).toNat = N - t.natAbs := by
      have := Int.ofNat_natAbs_of_nonpos ht
      omega
    rw [ha]
    exact hc.symm
  · rw [lemma38StartEdgeι, ite_eq_right ht]
    have hc := congrFun (wholePlaneEdgeι_trans W 0 N (Nat.zero_le N))
      (kmswWindowEdgeMapInf (shiftedStream W 0) t.toNat e)
    rw [← hc]
    change wholePlaneEdgeι W N
      (kmswWindowEdgeMapInf (shiftedStream W N) (N - 0)
        (kmswWindowEdgeMapInf (shiftedStream W 0) t.toNat e)) = _
    rw [Nat.sub_zero, ← shiftedStream_shift W 0 N (Nat.zero_le N),
      Nat.sub_zero, kmswWindowEdgeMapInf_comp]
    congr 2
    have := Int.toNat_of_nonneg (show 0 ≤ t by omega)
    omega

 
private theorem prop511_run_L (W : ℤ → Fin 3) (N n : ℕ) :
    L (shiftedStream W N) n =
      (wholePlaneWordIntegral W ((n : ℤ) - N)).1 -
        (wholePlaneWordIntegral W (-(N : ℤ))).1 := by
  have hs : lemma38StartStream W (-(N : ℤ)) = shiftedStream W N := by
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  have he := uibhbotStart_L W (-(N : ℤ)) n
  rw [hs] at he
  simpa only [neg_add_eq_sub] using he



private theorem prop511_relative_hit (W : ℤ → Fin 3) (k : ℤ)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode (k + 1) W (i + 1)))
    (hh : ∀ i, UIBHBOTBoundaryHit i (uibhbotBoundaryHitTime i W) W)
    (ha : StrictAnti (fun i => uibhbotBoundaryHitTime i W)) :
    boundaryHitTime (fun i => uibhbotFutureCode (k + 1) W (i + 1)) h (-1) =
      (uibhbotBoundaryHitTime k W - uibhbotBoundaryHitTime (k + 1) W).toNat := by
  have hlt : uibhbotBoundaryHitTime (k + 1) W < uibhbotBoundaryHitTime k W :=
    ha (show k < k + 1 by omega)
  unfold boundaryHitTime
  rw [dite_eq_right (by omega : (-1 : ℤ) ≠ 0),
    dite_eq_right (by omega : ¬ 0 < (-1 : ℤ))]
  apply (Nat.find_eq_iff _).mpr
  constructor
  · rw [uibhbotFutureCode_stream, uibhbotStart_L,
      show uibhbotBoundaryHitTime (k + 1) W +
        ((uibhbotBoundaryHitTime k W - uibhbotBoundaryHitTime (k + 1) W).toNat : ℤ) =
          uibhbotBoundaryHitTime k W by omega, (hh k).1, (hh (k + 1)).1]
    omega
  · intro n hn he
    rw [uibhbotFutureCode_stream, uibhbotStart_L, (hh (k + 1)).1] at he
    apply (hh k).2 (uibhbotBoundaryHitTime (k + 1) W + n) (by omega)
    omega



private theorem prop511_edge_window (W : ℤ → Fin 3) (k : ℤ)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode (k + 1) W (i + 1)))
    (hh : ∀ i, UIBHBOTBoundaryHit i (uibhbotBoundaryHitTime i W) W)
    (hr : ∀ i s, s < uibhbotBoundaryHitTime i W →
      i < (wholePlaneWordIntegral W s).1)
    (ha : StrictAnti (fun i => uibhbotBoundaryHitTime i W))
    (N : ℕ) (hN : (uibhbotBoundaryHitTime (k + 1) W).natAbs ≤ N) :
    uibhbotFutureEdge (k + 1) W
        (boundaryOuterEdge (fun i => uibhbotFutureCode (k + 1) W (i + 1)) h (-1)) =
      wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (uibhbotBoundaryHitTime k W + N).toNat) := by
  let t := uibhbotBoundaryHitTime (k + 1) W
  let s := uibhbotBoundaryHitTime k W
  have hlt : t < s := ha (by omega : k < k + 1)
  have ht : 0 ≤ t + (N : ℤ) := by
    have := Int.natCast_natAbs t
    change t.natAbs ≤ N at hN
    omega
  have hn : 0 < (s - t).toNat := by omega
  obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hs : ((n + 1 : ℕ) : ℤ) = s - t := by omega
  rw [boundaryOuterEdge_of_negative _ _ (by omega),
    prop511_relative_hit W k h hh ha]
  change lemma38StartEdgeι W t
    (kmswLLCreatedEdge (fun i => uibhbotFutureCode (k + 1) W (i + 1)) (s-t).toNat) = _
  rw [uibhbotFutureCode_stream, prop511_startEdge_cofinal W t N hN]
  have hc : lemma38StartStream W t =
      fun i => shiftedStream W N ((t + (N : ℤ)).toNat + i) := by
    funext i
    simp only [lemma38StartStream, shiftedStream]
    congr 1
    have := Int.toNat_of_nonneg ht
    push_cast
    omega
  rw [hc, hn']
  have hrec : ∀ j < (t + (N : ℤ)).toNat + (n + 1),
      L (shiftedStream W N) ((t + (N : ℤ)).toNat + (n + 1)) <
        L (shiftedStream W N) j := by
    intro j hj
    rw [prop511_run_L, prop511_run_L]
    have he : (((t + (N : ℤ)).toNat + (n + 1) : ℕ) : ℤ) - N = s := by omega
    rw [he, (hh k).1]
    have hp := hr k ((j : ℤ) - N) (by omega)
    omega
  rw [prop511_windowMap_LL_created _ _ n hrec]
  congr 2
  omega



theorem ae_uibhbotBusemannSource_missing_edges :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ e : ℤ → WholePlaneEdge W,
        (∀ k : ℤ,
          wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k) ∧
          ∃ N n : ℕ, 0 < n ∧ (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
            e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n)) ∧
        Function.Injective e ∧ e 0 = uibhbotRootEdge W := by
  classical
  filter_upwards [ae_uibhbotFuture_boundaryHitWitnesses, ae_uibhbotFutureBoundary_index,
    ae_uibhbotBoundaryHit, ae_uibhbotBoundaryHit_strictRecord,
    ae_uibhbotBoundaryHitTime_strictAnti, ae_uibhbotBoundaryHitTime_zero]
      with W h hi hh hr ha hz
  let e : ℤ → WholePlaneEdge W := fun k => uibhbotFutureEdge (k + 1) W
    (boundaryOuterEdge (fun i => uibhbotFutureCode (k + 1) W (i + 1)) (h (k + 1)) (-1))
  have hw (k : ℤ) : wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id := by
    rw [show e k = _ from rfl, uibhbotFutureEdge_west,
      (boundaryOuterEdge_endpoints _ (h (k + 1)) (-1)).1]
    have he := hi (k + 1) (h (k + 1)) (-1) (by omega)
    change uibhbotFutureVertex (k + 1) W _ = uibhbotFutureVertex k W 0
    simpa only [show k + 1 + -1 = k by omega] using he
  have he (k : ℤ) : wholePlaneEdgeEast W (e k) =
      (uibhbotBusemannSource (k + 1) W).id := by
    rw [show e k = _ from rfl, uibhbotFutureEdge_east,
      (boundaryOuterEdge_endpoints _ (h (k + 1)) (-1)).2.1]
    simp only [show (-1 : ℤ) + 1 = 0 by omega, boundaryVertex_zero]
    rfl
  have hrep (k : ℤ) (N : ℕ)
      (hN : (uibhbotBoundaryHitTime (k + 1) W).natAbs ≤ N) :
      e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N)
        (uibhbotBoundaryHitTime k W + N).toNat) :=
    prop511_edge_window W k (h (k + 1)) hh hr ha N hN
  have hmissing (k : ℤ) : ¬ wholePlaneEdgePresent W (e k) := by
    let N := (uibhbotBoundaryHitTime (k + 1) W).natAbs
    rw [hrep k N le_rfl]
    have hlt : uibhbotBoundaryHitTime (k + 1) W < uibhbotBoundaryHitTime k W :=
      ha (by omega : k < k + 1)
    have ht : 0 ≤ uibhbotBoundaryHitTime (k + 1) W + (N : ℤ) := by
      have := Int.natCast_natAbs (uibhbotBoundaryHitTime (k + 1) W)
      dsimp only [N]
      omega
    apply prop511_record_missing W N _ (by omega)
    intro M hNM j hj
    rw [prop511_run_L, prop511_run_L]
    have ht' : ((M - N + (uibhbotBoundaryHitTime k W + N).toNat : ℕ) : ℤ) - M =
        uibhbotBoundaryHitTime k W := by omega
    rw [ht', (hh k).1]
    have hp := hr k ((j : ℤ) - M) (by omega)
    omega
  refine ⟨e, ?_, ?_, ?_⟩
  · intro k
    refine ⟨hw k, he k, hmissing k, ?_⟩
    let N := (uibhbotBoundaryHitTime (k + 1) W).natAbs
    have hlt : uibhbotBoundaryHitTime (k + 1) W < uibhbotBoundaryHitTime k W :=
      ha (by omega : k < k + 1)
    have ht := Int.natCast_natAbs (uibhbotBoundaryHitTime (k + 1) W)
    refine ⟨N, (uibhbotBoundaryHitTime k W + N).toNat, ?_, ?_, hrep k N le_rfl⟩ <;>
      dsimp only [N] at * <;> omega
  · intro a b hab
    let K := max a b
    have hsa := hi K (h K) (a - K) (by dsimp [K]; omega)
    have hsb := hi K (h K) (b - K) (by dsimp [K]; omega)
    simp only [add_sub_cancel] at hsa hsb
    have hv : uibhbotFutureVertex a W 0 = uibhbotFutureVertex b W 0 := by
      exact (hw a).symm.trans ((congrArg (wholePlaneEdgeWest W) hab).trans (hw b))
    rw [← hsa, ← hsb] at hv
    have hb := boundaryVertex_injective _ (h K) (uibhbotFutureVertex_injective K W hv)
    omega
  · let N := (uibhbotBoundaryHitTime 1 W).natAbs + 1
    have hN : (uibhbotBoundaryHitTime (0 + 1) W).natAbs ≤ N := by dsimp [N]; omega
    rw [hrep 0 N hN, hz, zero_add, Int.toNat_natCast]
    apply (uibhbotRootEdge_eq_window W N (by dsimp [N]; omega) ?_).symm
    intro j hj
    rw [prop511_run_L, prop511_run_L]
    have hp := hr 0 ((j : ℤ) - N) (by rw [hz]; omega)
    simp only [sub_self] 
    have h0 := (hh 0).1
    rw [hz] at h0
    rw [h0]
    omega



private theorem ae_prop511_sdp_data :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∃ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        IsBoundaryBusemannSDP (boundaryPresentVertex _ h)
          (busemannSDPMeasurableVersion (uibhbotFutureCode k W)) := by
  apply ae_all_iff.mpr
  intro k
  have h := iidCodes_ae_busemannSDPMeasurableVersion
  rw [← uibhbotFutureCode_law k] at h
  exact ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h

 
private theorem prop511_sdp_eq_of_pathLengths
    {α β : Type*} [Quiver α] [Quiver β] {a b : α}
    (F : Prefunctor α β)
    (h : pathLengths (F.obj a) (F.obj b) = pathLengths a b) :
    DirectedDistances.sdp (F.obj a) (F.obj b) = DirectedDistances.sdp a b := by
  change (⨅ p : Quiver.Path (F.obj a) (F.obj b), (p.length : ℕ∞)) = _
  apply le_antisymm
  · apply le_iInf
    intro p
    have hp : p.length ∈ pathLengths a b := ⟨p, rfl⟩
    rw [← h] at hp
    obtain ⟨q, hq⟩ := hp
    have hq' : q.length = p.length := hq
    exact (iInf_le _ q).trans (by exact_mod_cast hq'.le)
  · apply le_iInf
    intro q
    have hq : q.length ∈ pathLengths (F.obj a) (F.obj b) := ⟨q, rfl⟩
    rw [h] at hq
    obtain ⟨p, hp⟩ := hq
    have hp' : p.length = q.length := hp
    exact (iInf_le _ p).trans (by exact_mod_cast hp'.le)

 
private theorem uibhbotBusemannFnSdp_future_difference_of_le
    (W : ℤ → Fin 3) (K k : ℤ) (n : ℕ)
    (hn : k + (n : ℤ) ≤ K)
    (hinc : ∀ i : ℤ, ∀ _hi : i ≤ K,
      uibhbotBusemannIncrementSdp i W =
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion (i - K) (uibhbotFutureCode K W)) :
    uibhbotBusemannFnSdp W (k + (n : ℤ)) - uibhbotBusemannFnSdp W k =
      busemannSDPMeasurableVersion (uibhbotFutureCode K W) (k + (n : ℤ) - K) -
        busemannSDPMeasurableVersion (uibhbotFutureCode K W) (k - K) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnk : k + (n : ℤ) ≤ K := by omega
      have hnext : k + ((n + 1 : ℕ) : ℤ) ≤ K := hn
      have hindex : k + ((n + 1 : ℕ) : ℤ) - 1 = k + (n : ℤ) := by omega
      have hrec := uibhbotBusemannFnSdp_sub_prev W (k + ((n + 1 : ℕ) : ℤ))
      rw [hindex] at hrec
      have hi : k + ((n + 1 : ℕ) : ℤ) ≤ K := hnext
      rw [hinc _ hi, SDPMasterFromLaw.increment] at hrec
      have harg : k + ((n + 1 : ℕ) : ℤ) - K - 1 = k + (n : ℤ) - K := by omega
      rw [harg] at hrec
      calc
        uibhbotBusemannFnSdp W (k + ((n + 1 : ℕ) : ℤ)) - uibhbotBusemannFnSdp W k =
            (uibhbotBusemannFnSdp W (k + ((n + 1 : ℕ) : ℤ)) -
              uibhbotBusemannFnSdp W (k + (n : ℤ))) +
                (uibhbotBusemannFnSdp W (k + (n : ℤ)) - uibhbotBusemannFnSdp W k) := by ring
        _ = (busemannSDPMeasurableVersion (uibhbotFutureCode K W)
              (k + ((n + 1 : ℕ) : ℤ) - K) -
              busemannSDPMeasurableVersion (uibhbotFutureCode K W)
                (k + (n : ℤ) - K)) +
                (busemannSDPMeasurableVersion (uibhbotFutureCode K W)
                  (k + (n : ℤ) - K) -
                  busemannSDPMeasurableVersion (uibhbotFutureCode K W) (k - K)) := by
              rw [hrec, ih hnk]
        _ = busemannSDPMeasurableVersion (uibhbotFutureCode K W)
              (k + ((n + 1 : ℕ) : ℤ) - K) -
              busemannSDPMeasurableVersion (uibhbotFutureCode K W) (k - K) := by ring




theorem ae_uibhbotBusemannFnSdp_distance_characterization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k k' : ℤ,
      ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSource k W) (z m) ∧
        Reachable (uibhbotBusemannSource k' W) (z m)) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
        DirectedDistances.sdp (uibhbotBusemannSource k' W) (z m) =
          (a : ℕ∞) ∧
        DirectedDistances.sdp (uibhbotBusemannSource k W) (z m) =
          (b : ℕ∞) ∧
        uibhbotBusemannFnSdp W k' - uibhbotBusemannFnSdp W k = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [ae_prop511_sdp_data,
    ae_uibhbotFutureBoundary_index, ae_uibhbotFuture_boundary_pathLengths,
    ae_uibhbotFuture_boundary_path_lift,
    ae_uibhbotBusemannIncrementSdp_future_identity] with W hdata hi hpaths hl hinc
  intro k k' z hz hr
  let K := max k k'
  have hk : k ≤ K := le_max_left _ _
  have hk' : k' ≤ K := le_max_right _ _
  obtain ⟨h, hX⟩ := hdata K
  let w := fun i => uibhbotFutureCode K W (i + 1)
  let x := boundaryPresentVertex w h
  let F := uibhbotFutureToGlobal K W
  let j := k - K
  let j' := k' - K
  have hj : j ≤ 0 := by dsimp [j]; omega
  have hj' : j' ≤ 0 := by dsimp [j']; omega
  have hs (i : ℤ) (hi' : i ≤ 0) : F.obj (x i) = uibhbotBusemannSource (K + i) W := by
    apply congrArg UIBHBOTPresentVertex.mk
    exact hi K h i hi'
  have hs0 : F.obj (x j) = uibhbotBusemannSource k W := by
    simpa only [j, add_sub_cancel] using hs j hj
  have hs1 : F.obj (x j') = uibhbotBusemannSource k' W := by
    simpa only [j', add_sub_cancel] using hs j' hj'
  have hp : ∀ m, ∃ c : PresentVertex w, F.obj c = z m ∧ Reachable (x j) c := by
    intro m
    have hrm := (hr m).1
    rw [← hs0] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h j hj (z m) p
    exact ⟨c, hc, ⟨q⟩⟩
  choose y hy hy0 using hp
  have hy1 : ∀ m, Reachable (x j') (y m) := by
    intro m
    have hrm := (hr m).2
    rw [← hs1] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h j' hj' (z m) p
    have he : c = y m := uibhbotFutureToGlobal_obj_injective K W
      (hc.trans (hy m).symm)
    subst c
    exact ⟨q⟩
  have hiy : Function.Injective y := by
    intro a b hab
    apply hz
    rw [← hy a, ← hy b, hab]
  obtain ⟨N, hN⟩ := hX.2 j j' y hiy (fun m => ⟨hy0 m, hy1 m⟩)
  have htel : uibhbotBusemannFnSdp W k' - uibhbotBusemannFnSdp W k =
      busemannSDPMeasurableVersion (uibhbotFutureCode K W) j' -
        busemannSDPMeasurableVersion (uibhbotFutureCode K W) j := by
    by_cases hkk : k ≤ k'
    · have hn : (k' - k).toNat = (k' - k) := Int.toNat_of_nonneg (by omega)
      have hsum := uibhbotBusemannFnSdp_future_difference_of_le W K k
        (k' - k).toNat (by omega) (fun i hi' => hinc K i hi')
      have harg : k + ((k' - k).toNat : ℤ) = k' := by omega
      rw [harg] at hsum
      simpa only [j, j'] using hsum
    · have hn : (k - k').toNat = (k - k') := Int.toNat_of_nonneg (by omega)
      have hsum := uibhbotBusemannFnSdp_future_difference_of_le W K k'
        (k - k').toNat (by omega) (fun i hi' => hinc K i hi')
      have harg : k' + ((k - k').toNat : ℤ) = k := by omega
      rw [harg] at hsum
      have hsum' := congrArg Neg.neg hsum
      calc
        uibhbotBusemannFnSdp W k' - uibhbotBusemannFnSdp W k =
            -(uibhbotBusemannFnSdp W k - uibhbotBusemannFnSdp W k') := by ring
        _ = -(busemannSDPMeasurableVersion (uibhbotFutureCode K W) (k - K) -
              busemannSDPMeasurableVersion (uibhbotFutureCode K W) (k' - K)) := by
            rw [hsum']
        _ = busemannSDPMeasurableVersion (uibhbotFutureCode K W) j' -
              busemannSDPMeasurableVersion (uibhbotFutureCode K W) j := by
            dsimp [j, j']
            ring
  refine ⟨N, fun m hm => ?_⟩
  let a := (DirectedDistances.sdp (x j') (y m)).toNat
  let b := (DirectedDistances.sdp (x j) (y m)).toNat
  have hd0 : DirectedDistances.sdp (uibhbotBusemannSource k W) (z m) = (b : ℕ∞) := by
    have he := prop511_sdp_eq_of_pathLengths F (hpaths K h j hj (y m))
    change DirectedDistances.sdp (F.obj (x j)) (F.obj (y m)) =
      DirectedDistances.sdp (x j) (y m) at he
    rw [hs0, hy m] at he
    have hne : DirectedDistances.sdp (x j) (y m) ≠ ⊤ :=
      fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) (hy0 m)
    exact he.trans (ENat.natCast_toNat hne).symm
  have hd1 : DirectedDistances.sdp (uibhbotBusemannSource k' W) (z m) = (a : ℕ∞) := by
    have he := prop511_sdp_eq_of_pathLengths F (hpaths K h j' hj' (y m))
    change DirectedDistances.sdp (F.obj (x j')) (F.obj (y m)) =
      DirectedDistances.sdp (x j') (y m) at he
    rw [hs1, hy m] at he
    have hne : DirectedDistances.sdp (x j') (y m) ≠ ⊤ :=
      fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) (hy1 m)
    exact he.trans (ENat.natCast_toNat hne).symm
  refine ⟨a, b, hd1, hd0, ?_⟩
  rw [htel]
  exact hN m hm





theorem ae_existsUnique_uibhbotBusemannFnSdp :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∃! X : ℤ → ℤ,
      X 0 = 0 ∧
      ∀ k k' : ℤ, ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
        (∀ m, Reachable (uibhbotBusemannSource k W) (z m) ∧
          Reachable (uibhbotBusemannSource k' W) (z m)) →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
          DirectedDistances.sdp (uibhbotBusemannSource k' W) (z m) = (a : ℕ∞) ∧
          DirectedDistances.sdp (uibhbotBusemannSource k W) (z m) = (b : ℕ∞) ∧
          X k' - X k = (a : ℤ) - (b : ℤ) := by
  filter_upwards [ae_uibhbotBusemannFnSdp_distance_characterization,
    ae_uibhbotBusemannFnSdp_unique] with W hc hu
  refine ⟨uibhbotBusemannFnSdp W, ⟨uibhbotBusemannFnSdp_zero W, hc⟩, ?_⟩
  intro X hX
  exact hu X hX.1 hX.2

 
private theorem prop511_identified_increment_law (X : (ℤ → Fin 3) → ℤ → ℤ)
    (Y : (ℕ → Fin 3) → ℤ → ℤ) (hY : ∀ k, Measurable (fun ω => Y ω k))
    (heq : X =ᵐ[wholePlaneIIDCodeMeasure] (fun W => Y (shiftedCodePath W 0)))
    (k : ℤ) :
    IdentDistrib (fun W => X W k - X W (k - 1)) (ldpIncrement Y k)
      wholePlaneIIDCodeMeasure iidCodeMeasure := by
  have hc : Measurable (ldpIncrement Y k) := (hY k).sub (hY (k - 1))
  have hm := hc.comp (measurable_shiftedCodePath 0)
  have he : (fun W => X W k - X W (k - 1)) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => ldpIncrement Y k (shiftedCodePath W 0)) := by
    filter_upwards [heq] with W hW
    simp only [hW, ldpIncrement]
  refine ⟨hm.aemeasurable.congr he.symm, hc.aemeasurable, ?_⟩
  calc
    _ = wholePlaneIIDCodeMeasure.map
        (ldpIncrement Y k ∘ (fun W => shiftedCodePath W 0)) := Measure.map_congr he
    _ = (wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0)).map
        (ldpIncrement Y k) :=
      (Measure.map_map hc (measurable_shiftedCodePath 0)).symm
    _ = _ := by rw [wholePlaneIIDCodeMeasure_map_shiftedPath 0]



theorem uibhbotBusemannFn_increment_identDistrib (k : ℤ) :
    IdentDistrib
      (fun W => uibhbotBusemannFn W k - uibhbotBusemannFn W (k - 1))
      (fun W => identifiedLDPBusemann W 0 - identifiedLDPBusemann W (0 - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) wholePlaneIIDCodeMeasure := by
  have hm : Measurable
      (fun W => uibhbotBusemannFn W k - uibhbotBusemannFn W (k - 1)) := by
    simpa only [uibhbotBusemannFn_sub_prev] using measurable_uibhbotBusemannIncrement k
  have hc : Measurable (ldpIncrement busemannLDPMeasurableVersion 0) :=
    (measurable_busemannLDPMeasurableVersion 0).sub
      (measurable_busemannLDPMeasurableVersion (0 - 1))
  exact (IdentDistrib.mk hm.aemeasurable hc.aemeasurable
    (uibhbotBusemannFn_increment_law k)).trans
      (prop511_identified_increment_law identifiedLDPBusemann busemannLDPMeasurableVersion
        measurable_busemannLDPMeasurableVersion identifiedLDPBusemann_eq_carrier_ae 0).symm



theorem uibhbotBusemannFnSdp_increment_identDistrib (k : ℤ) :
    IdentDistrib
      (fun W => uibhbotBusemannFnSdp W k - uibhbotBusemannFnSdp W (k - 1))
      (fun W => identifiedSDPBusemann W 0 - identifiedSDPBusemann W (0 - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) wholePlaneIIDCodeMeasure := by
  have hm : Measurable
      (fun W => uibhbotBusemannFnSdp W k - uibhbotBusemannFnSdp W (k - 1)) := by
    simpa only [uibhbotBusemannFnSdp_sub_prev] using measurable_uibhbotBusemannIncrementSdp k
  have hc : Measurable (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) :=
    (measurable_busemannSDPMeasurableVersion 0).sub
      (measurable_busemannSDPMeasurableVersion (0 - 1))
  exact (IdentDistrib.mk hm.aemeasurable hc.aemeasurable
    (uibhbotBusemannFnSdp_increment_law k)).trans
      (prop511_identified_increment_law identifiedSDPBusemann busemannSDPMeasurableVersion
        measurable_busemannSDPMeasurableVersion identifiedSDPBusemann_eq_carrier_ae 0).symm




@[expose] def IsUIBHBOTBusemannLDP (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSource k W) (z m) ∧
        Reachable (uibhbotBusemannSource k' W) (z m)) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
        uibhbotLdp (uibhbotBusemannSource k' W) (z m) = ((a : ℕ∞) : WithBot ℕ∞) ∧
        uibhbotLdp (uibhbotBusemannSource k W) (z m) = ((b : ℕ∞) : WithBot ℕ∞) ∧
        X k' - X k = (a : ℤ) - (b : ℤ)




@[expose] def IsUIBHBOTBusemannSDP (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSource k W) (z m) ∧
        Reachable (uibhbotBusemannSource k' W) (z m)) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
        DirectedDistances.sdp (uibhbotBusemannSource k' W) (z m) = (a : ℕ∞) ∧
        DirectedDistances.sdp (uibhbotBusemannSource k W) (z m) = (b : ℕ∞) ∧
        X k' - X k = (a : ℤ) - (b : ℤ)





@[expose] def prop511Statement : Prop :=
  (∃ X : (ℤ → Fin 3) → ℤ → ℤ,
    (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      IsUIBHBOTBusemannLDP W (X W) ∧
        ∀ Y : ℤ → ℤ, IsUIBHBOTBusemannLDP W Y → Y = X W) ∧
    iIndepFun (fun k W => X W k - X W (k - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) ∧
    ∀ k : ℤ, IdentDistrib (fun W => X W k - X W (k - 1))
      (fun W => identifiedLDPBusemann W 0 - identifiedLDPBusemann W (0 - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) wholePlaneIIDCodeMeasure) ∧
  (∃ X : (ℤ → Fin 3) → ℤ → ℤ,
    (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      IsUIBHBOTBusemannSDP W (X W) ∧
        ∀ Y : ℤ → ℤ, IsUIBHBOTBusemannSDP W Y → Y = X W) ∧
    iIndepFun (fun k W => X W k - X W (k - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) ∧
    ∀ k : ℤ, IdentDistrib (fun W => X W k - X W (k - 1))
      (fun W => identifiedSDPBusemann W 0 - identifiedSDPBusemann W (0 - 1))
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) wholePlaneIIDCodeMeasure)

/-- The complete incidence-carrier statement of Proposition 5.11 -/
theorem prop511_holds : prop511Statement := by
  constructor
  · refine ⟨uibhbotBusemannFn, ?_, uibhbotBusemannFn_iIndep,
      uibhbotBusemannFn_increment_identDistrib⟩
    filter_upwards [ae_uibhbotBusemannFn_distance_characterization,
      ae_uibhbotBusemannFn_unique] with W hc hu
    exact ⟨⟨uibhbotBusemannFn_zero W, hc⟩, fun Y hY => hu Y hY.1 hY.2⟩
  · refine ⟨uibhbotBusemannFnSdp, ?_, uibhbotBusemannFnSdp_iIndep,
      uibhbotBusemannFnSdp_increment_identDistrib⟩
    filter_upwards [ae_uibhbotBusemannFnSdp_distance_characterization,
      ae_uibhbotBusemannFnSdp_unique] with W hc hu
    exact ⟨⟨uibhbotBusemannFnSdp_zero W, hc⟩, fun Y hY => hu Y hY.1 hY.2⟩

end DirectedDistances.PaperProofs.Section5
