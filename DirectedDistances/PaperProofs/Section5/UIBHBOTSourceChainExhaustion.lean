/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryExhaustive

/-! Source-chain exhaustion helpers for Definition 5.8 -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk



private theorem boundaryHitTime_eq_of_no_earlier_hit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {q : ℤ} (hq : q ≤ -1) {m : ℕ}
    (hvalue : L w m = q) (hfirst : ∀ i < m, L w i ≠ q) :
    boundaryHitTime w h q = m := by
  have hq0 : q ≠ 0 := by omega
  have hqpos : ¬ 0 < q := by omega
  have hle : boundaryHitTime w h q ≤ m := by
    unfold boundaryHitTime
    simp only [dite_eq_right hq0, dite_eq_right hqpos]
    exact Nat.find_min' (h.leftHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hhit := boundaryHitTime_left_spec w h hq
    exact (hfirst (boundaryHitTime w h q) hlt) hhit
  omega

 
private theorem sourceChain_run_L (W : ℤ → Fin 3) (N n : ℕ) :
    L (shiftedStream W N) n =
      (wholePlaneWordIntegral W ((n : ℤ) - N)).1 -
        (wholePlaneWordIntegral W (-(N : ℤ))).1 := by
  have hs : lemma38StartStream W (-(N : ℤ)) = shiftedStream W N := by
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  have he := uibhbotStart_L W (-(N : ℤ)) n
  rw [hs] at he
  simpa only [neg_add_eq_sub] using he



private theorem sourceChain_left_record_creation (w : ℕ → Fin 3) (n : ℕ)
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



private theorem sourceChain_dropLast_reverse_eq_nil_of_length_one (xs : List ℕ)
    (h : xs.length = 1) : xs.dropLast.reverse = [] := by
  have hd : xs.dropLast = [] := List.length_eq_zero_iff.mp (by
    rw [List.length_dropLast, h])
  rw [hd]
  rfl



private theorem sourceChain_windowMap_LL_created (w : ℕ → Fin 3) (s n : ℕ)
    (hrec : ∀ j < s + (n + 1), L w (s + (n + 1)) < L w j) :
    kmswWindowEdgeMapInf w s (kmswLLCreatedEdge (fun i => w (s + i)) (n + 1)) =
      kmswLLCreatedEdge w (s + (n + 1)) := by
  let v := fun i => w (s + i)
  let pre := kmswStage v n
  let globalPre := kmswStage w (s + n)
  let data := kmswWindowPatchData w s n
  have hcreation := sourceChain_left_record_creation w (s + n) (by
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
  have hdrop := sourceChain_dropLast_reverse_eq_nil_of_length_one pre.UL hpreLen
  have hglobalDrop := sourceChain_dropLast_reverse_eq_nil_of_length_one globalPre.UL hglobalLen
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

 
private theorem sourceChain_windowMap_LL_created_of_pos (w : ℕ → Fin 3)
    (s m : ℕ) (hm : 0 < m)
    (hrec : ∀ j < s + m, L w (s + m) < L w j) :
    kmswWindowEdgeMapInf w s
        (kmswLLCreatedEdge (fun i => w (s + i)) m) =
      kmswLLCreatedEdge w (s + m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact sourceChain_windowMap_LL_created w s n (by
    simpa only [Nat.add_assoc] using hrec)



private theorem sourceChain_missing_record_stays_record (W : ℤ → Fin 3) (N m : ℕ)
    (hm : 0 < m)
    (hr : ∀ j < m, L (shiftedStream W N) m < L (shiftedStream W N) j)
    (hmiss : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m)))
    (M : ℕ) (hNM : N ≤ M) :
    ∀ j < M - N + m,
      L (shiftedStream W M) (M - N + m) < L (shiftedStream W M) j := by
  by_contra hn
  have hp := wholePlaneLLCreatedEdge_present_of_nonrecord W N M hNM m hm hr hn
  have hc := wholePlaneEdgePresent_ι_of_run_present W M _ hp
  have hi : wholePlaneEdgeι W M
      (wholePlaneEdgeTrans W N M hNM (kmswLLCreatedEdge (shiftedStream W N) m)) =
      wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m) :=
    congrFun (wholePlaneEdgeι_trans W N M hNM) _
  rw [hi] at hc
  exact hmiss hc



private theorem sourceChain_missingEdge_sourceIndex
    (W : ℤ → Fin 3) (e : ℤ → WholePlaneEdge W)
    (hhit : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (hchain : ∀ k : ℤ,
      ∃ N n : ℕ, 0 < n ∧ (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
        e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n))
    (hrecord : ∀ k s : ℤ, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1)
    (f : WholePlaneEdge W) (hf : ¬ wholePlaneEdgePresent W f) :
    ∃ k : ℤ, f = e k := by
  obtain ⟨⟨N, edgeN⟩, hrepr⟩ := Quotient.exists_rep f
  change wholePlaneEdgeι W N edgeN = f at hrepr
  have hmissRep : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N edgeN) := by
    rw [hrepr]
    exact hf
  let w := shiftedStream W N
  have hmissRun : ¬ EdgePresent w edgeN := by
    intro hp
    exact hmissRep (wholePlaneEdgePresent_ι_of_run_present W N edgeN hp)
  obtain ⟨stage, hstage⟩ := futureMap_missing_eventually_LL w
    (hhit N).R_unbounded_below edgeN hmissRun
  obtain ⟨m, hm, -, hr, hedgeN⟩ := kmswStage_LL_edge_created_at_record w stage edgeN
    (hstage stage le_rfl).2
  have hmissLL : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m)) := by
    rw [← hedgeN]
    exact hmissRep
  have hreprLL : wholePlaneEdgeι W N
      (kmswLLCreatedEdge (shiftedStream W N) m) = f := by
    rw [← hedgeN]
    exact hrepr
  let t : ℤ := (m : ℤ) - N
  let k : ℤ := (wholePlaneWordIntegral W t).1
  have hfirst : ∀ s : ℤ, s < t →
      (wholePlaneWordIntegral W s).1 ≠ k := by
    intro s hst hsame
    let M := max N s.natAbs
    have hNM : N ≤ M := Nat.le_max_left _ _
    have hsM : 0 ≤ s + (M : ℤ) := by
      have hsNat := Int.natCast_natAbs s
      dsimp [M]
      omega
    let j := (s + (M : ℤ)).toNat
    have hj : (j : ℤ) - M = s := by
      dsimp [j]
      have hsNat := Int.toNat_of_nonneg hsM
      omega
    have hend : ((M - N + m : ℕ) : ℤ) - M = t := by
      dsimp [t]
      omega
    have hjlt : j < M - N + m := by
      have hjNat := Int.toNat_of_nonneg hsM
      dsimp [j, t] at *
      omega
    have hrecM := sourceChain_missing_record_stays_record W N m hm hr hmissLL M hNM
    have hlt := hrecM j hjlt
    rw [sourceChain_run_L W M (M - N + m), hend,
      sourceChain_run_L W M j, hj, hsame] at hlt
    exact (lt_irrefl _) hlt
  have hglobalHit : UIBHBOTBoundaryHit k t W := by
    change (wholePlaneWordIntegral W t).1 = k ∧ _
    exact ⟨rfl, hfirst⟩
  have htime : uibhbotBoundaryHitTime k W = t := uibhbotBoundaryHitTime_eq hglobalHit
  obtain ⟨N', n', hn', hsourceTime, hsourceEdge⟩ := hchain k
  rw [htime] at hsourceTime
  let M := max N N'
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hN'M : N' ≤ M := Nat.le_max_right _ _
  let r := M - N + m
  let r' := M - N' + n'
  have hrr : r = r' := by
    dsimp [r, r']
    dsimp [t] at hsourceTime
    omega
  have hrecordM : ∀ j < r, L (shiftedStream W M) r < L (shiftedStream W M) j := by
    dsimp [r]
    exact sourceChain_missing_record_stays_record W N m hm hr hmissLL M hNM
  have hsourceRecordM : ∀ j < r',
      L (shiftedStream W M) r' < L (shiftedStream W M) j := by
    intro j hj
    have htimeR : ((r' : ℕ) : ℤ) - M = t := by
      dsimp [r', t]
      omega
    have htimeJ : ((j : ℕ) : ℤ) - M < uibhbotBoundaryHitTime k W := by
      rw [htime]
      rw [← htimeR]
      dsimp [r'] at hj
      omega
    have hstrict := hrecord k ((j : ℤ) - M) htimeJ
    have hrunR := sourceChain_run_L W M r'
    have hrunJ := sourceChain_run_L W M j
    rw [htimeR] at hrunR
    have hlev : (wholePlaneWordIntegral W t).1 = k := rfl
    rw [hlev] at hrunR
    calc
      L (shiftedStream W M) r' = k - (wholePlaneWordIntegral W (-(M : ℤ))).1 := hrunR
      _ < (wholePlaneWordIntegral W ((j : ℤ) - M)).1 -
          (wholePlaneWordIntegral W (-(M : ℤ))).1 := by omega
      _ = L (shiftedStream W M) j := hrunJ.symm
  have htransN : wholePlaneEdgeTrans W N M hNM
      (kmswLLCreatedEdge (shiftedStream W N) m) =
        kmswLLCreatedEdge (shiftedStream W M) r := by
    change kmswWindowEdgeMapInf (shiftedStream W M) (M - N)
      (kmswLLCreatedEdge (shiftedStream W N) m) = _
    rw [← shiftedStream_shift W N M hNM]
    simpa only [r] using sourceChain_windowMap_LL_created_of_pos
      (shiftedStream W M) (M - N) m hm (by simpa only [r] using hrecordM)
  have htransN' : wholePlaneEdgeTrans W N' M hN'M
      (kmswLLCreatedEdge (shiftedStream W N') n') =
        kmswLLCreatedEdge (shiftedStream W M) r' := by
    change kmswWindowEdgeMapInf (shiftedStream W M) (M - N')
      (kmswLLCreatedEdge (shiftedStream W N') n') = _
    rw [← shiftedStream_shift W N' M hN'M]
    simpa only [r'] using sourceChain_windowMap_LL_created_of_pos
      (shiftedStream W M) (M - N') n' hn' hsourceRecordM
  have hcanN := congrFun (wholePlaneEdgeι_trans W N M hNM)
    (kmswLLCreatedEdge (shiftedStream W N) m)
  have hcanN' := congrFun (wholePlaneEdgeι_trans W N' M hN'M)
    (kmswLLCreatedEdge (shiftedStream W N') n')
  refine ⟨k, ?_⟩
  calc
    f = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m) := hreprLL.symm
    _ = wholePlaneEdgeι W M
        (wholePlaneEdgeTrans W N M hNM (kmswLLCreatedEdge (shiftedStream W N) m)) := hcanN.symm
    _ = wholePlaneEdgeι W M (kmswLLCreatedEdge (shiftedStream W M) r) :=
      congrArg (wholePlaneEdgeι W M) htransN
    _ = wholePlaneEdgeι W M (kmswLLCreatedEdge (shiftedStream W M) r') :=
      congrArg (wholePlaneEdgeι W M) (congrArg (kmswLLCreatedEdge (shiftedStream W M)) hrr)
    _ = wholePlaneEdgeι W M
        (wholePlaneEdgeTrans W N' M hN'M
          (kmswLLCreatedEdge (shiftedStream W N') n')) :=
      congrArg (wholePlaneEdgeι W M) htransN'.symm
    _ = wholePlaneEdgeι W N' (kmswLLCreatedEdge (shiftedStream W N') n') := hcanN'
    _ = e k := hsourceEdge.symm

/-- A source edge at level `k`, when represented in the run starting at `−N`, is the LL edge
created at the first hit of the local level `−j`, with the exact offset
are stated explicitly because the latter certifies the local hit is the first one. -/
theorem uibhbotBusemannSourceEdge_firstHitLL
    (W : ℤ → Fin 3) (e : ℤ → WholePlaneEdge W)
    (hsource : ∀ k : ℤ,
      ∃ N n : ℕ, 0 < n ∧ (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
        e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n))
    (hhit : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (hglobal : ∀ k : ℤ,
      UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hrecord : ∀ k s : ℤ, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1) :
    ∀ k : ℤ, ∃ N n j : ℕ,
      0 < n ∧ 0 < j ∧
      (j : ℤ) = (wholePlaneWordIntegral W (-(N : ℤ))).1 - k ∧
      (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
      e k = wholePlaneEdgeι W N
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) (hhit N) (-(j : ℤ)))) := by
  intro k
  obtain ⟨N, n, hn, htime, hedge⟩ := hsource k
  let j : ℕ := ((wholePlaneWordIntegral W (-(N : ℤ))).1 - k).toNat
  have hbase : k < (wholePlaneWordIntegral W (-(N : ℤ))).1 := by
    apply hrecord k (-(N : ℤ))
    rw [← htime]
    have hn' : (0 : ℤ) < (n : ℤ) := by omega
    omega
  have hjpos : 0 < j := by
    dsimp [j]
    have hnat := Int.toNat_of_nonneg (show 0 ≤
      (wholePlaneWordIntegral W (-(N : ℤ))).1 - k by omega)
    omega
  have hrun (i : ℕ) : L (shiftedStream W N) i =
      (wholePlaneWordIntegral W ((i : ℤ) - N)).1 -
        (wholePlaneWordIntegral W (-(N : ℤ))).1 := by
    have hs : lemma38StartStream W (-(N : ℤ)) = shiftedStream W N := by
      funext r
      simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
    have he := uibhbotStart_L W (-(N : ℤ)) i
    rw [hs] at he
    simpa only [neg_add_eq_sub] using he
  have hvalue : L (shiftedStream W N) n = -(j : ℤ) := by
    rw [hrun, htime, (hglobal k).1]
    dsimp [j]
    have hnat := Int.toNat_of_nonneg (show 0 ≤
      (wholePlaneWordIntegral W (-(N : ℤ))).1 - k by omega)
    omega
  have hfirst : ∀ i < n, L (shiftedStream W N) i ≠ -(j : ℤ) := by
    intro i hi heq
    have hlevel : (wholePlaneWordIntegral W ((i : ℤ) - N)).1 = k := by
      rw [hrun] at heq
      dsimp [j] at heq
      have hnat := Int.toNat_of_nonneg (show 0 ≤
        (wholePlaneWordIntegral W (-(N : ℤ))).1 - k by omega)
      omega
    have hbefore : (i : ℤ) - N < uibhbotBoundaryHitTime k W := by
      rw [← htime]
      omega
    exact (hglobal k).2 _ hbefore hlevel
  have hhitTime := boundaryHitTime_eq_of_no_earlier_hit
    (shiftedStream W N) (hhit N) (by omega) hvalue hfirst
  refine ⟨N, n, j, hn, hjpos, ?_, htime, ?_⟩
  · dsimp [j]
    have hnat := Int.toNat_of_nonneg (show 0 ≤
      (wholePlaneWordIntegral W (-(N : ℤ))).1 - k by omega)
    omega
  · rw [hhitTime]
    exact hedge




theorem ae_uibhbotBusemannSource_edges_firstHitLL :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hhit : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N),
        ∃ e : ℤ → WholePlaneEdge W,
          (∀ k : ℤ,
            wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
            wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
            ¬ wholePlaneEdgePresent W (e k) ∧
            ∃ N n : ℕ, 0 < n ∧
              (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
              e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n)) ∧
          Function.Injective e ∧ e 0 = uibhbotRootEdge W ∧
        (∀ k : ℤ, ∃ N n j : ℕ,
          0 < n ∧ 0 < j ∧
          (j : ℤ) = (wholePlaneWordIntegral W (-(N : ℤ))).1 - k ∧
          (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
          e k = wholePlaneEdgeι W N
            (kmswLLCreatedEdge (shiftedStream W N)
              (boundaryHitTime (shiftedStream W N) (hhit N) (-(j : ℤ))))) := by
  filter_upwards [ae_uibhbotBusemannSource_missing_edges,
    uibhbotCodeLawRel_ae_missing_edges_firstHitLL, ae_uibhbotBoundaryHit,
    ae_uibhbotBoundaryHit_strictRecord] with W hsource hfuture hglobal hrecord
  obtain ⟨e, hedge, hinj, hroot⟩ := hsource
  obtain ⟨hhit, -⟩ := hfuture
  refine ⟨hhit, e, hedge, hinj, hroot, ?_⟩
  exact uibhbotBusemannSourceEdge_firstHitLL W e
    (fun k => (hedge k).2.2.2) hhit hglobal hrecord



theorem ae_uibhbotBusemannSource_edges_ordered :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ e : ℤ → WholePlaneEdge W, ∀ k : ℤ,
        wholePlaneEdgeEast W (e k) = wholePlaneEdgeWest W (e (k + 1)) := by
  filter_upwards [ae_uibhbotBusemannSource_missing_edges] with W hsource
  obtain ⟨e, hedge, -, -⟩ := hsource
  refine ⟨e, fun k => ?_⟩
  exact ((hedge k).2.1).trans (hedge (k + 1)).1.symm



theorem uibhbotCodeLawRel_ae_missing_edges_eq_range :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ e : ℤ → WholePlaneEdge W,
        ∀ f : WholePlaneEdge W,
          ¬ wholePlaneEdgePresent W f ↔ ∃! k : ℤ, f = e k := by
  filter_upwards [ae_uibhbotBusemannSource_missing_edges,
    uibhbotCodeLawRel_ae_missing_edges_firstHitLL,
    ae_uibhbotBoundaryHit_strictRecord] with W hsource hfuture hrecord
  obtain ⟨e, hchain, hinj, hroot⟩ := hsource
  obtain ⟨hhit, -⟩ := hfuture
  refine ⟨e, fun f => ?_⟩
  constructor
  · intro hmiss
    obtain ⟨k, hfk⟩ := sourceChain_missingEdge_sourceIndex W e hhit
      (fun k => (hchain k).2.2.2) hrecord f hmiss
    refine ⟨k, hfk, ?_⟩
    intro k' hk'
    apply hinj
    exact hk'.symm.trans hfk
  · rintro ⟨k, hfk, -⟩
    rw [hfk]
    exact (hchain k).2.2.1

end DirectedDistances.PaperProofs.Section5
