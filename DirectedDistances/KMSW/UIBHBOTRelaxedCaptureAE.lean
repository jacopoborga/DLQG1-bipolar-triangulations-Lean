module

public import DirectedDistances.KMSW.UIBHBOTEventualCapture
public import DirectedDistances.KMSW.KMSWWindowRelaxedCapture
public import DirectedDistances.KMSW.UIBHBOTBackwardNonrecord
public import DirectedDistances.RandomWalk.UIBHBOTForwardPrefixLaw

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk MeasureTheory

private theorem cast_list (xs : List ℕ) :
    (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl

private theorem range_fst (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum.1 =
      ∑ i ∈ Finset.range n, (f i).1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem window_integral_fst (W : ℤ → Fin 3) (N j : ℕ) :
    L (shiftedStream W N) N +
      (wholePlaneWordIntegral W ((j : ℤ) - N)).1 =
      L (shiftedStream W N) j := by
  by_cases hj : j < N
  · have hd : ((j : ℤ) - N) < 0 := by omega
    have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
    simp only [wholePlaneWordIntegral, ite_eq_right (not_le.mpr hd), Prod.fst_neg,
      hc, bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_fst]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).1) j (N - j)
    have ht : (∑ i ∈ Finset.range (N - j),
        (lazyTwoDimensionalStep (shiftedStream W N (j + i))).1) =
        ∑ i ∈ Finset.range (N - j),
          (lazyTwoDimensionalStep (W (-(i : ℤ) - 1))).1 := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show j + (N - j) = N by omega, ht] at he
    change L (shiftedStream W N) N = L (shiftedStream W N) j + _ at he
    omega
  · have hd : 0 ≤ (j : ℤ) - N := by omega
    have hc : ((j : ℤ) - N).toNat = j - N := by omega
    simp only [wholePlaneWordIntegral, ite_eq_left hd, hc,
      bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_fst]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).1) N (j - N)
    have ht : (∑ i ∈ Finset.range (j - N),
        (lazyTwoDimensionalStep (shiftedStream W N (N + i))).1) =
        ∑ i ∈ Finset.range (j - N), (lazyTwoDimensionalStep (W (i : ℤ))).1 := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show N + (j - N) = j by omega, ht] at he
    exact he.symm

private theorem shifted_L (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    L (shiftedStream W M) (M - N + k) =
      L (shiftedStream W M) (M - N) + L (shiftedStream W N) k := by
  unfold L
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun (shiftedStream_shift W N M h) i]




theorem uibhbotCodeWord_minL_eq_of_leftSeamBarrier (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (N k : ℕ)
    (hrec : minL (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) k =
      L (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) k)
    (hbar : ∀ s : ℤ, s < -(N : ℤ) →
      (uibhbotConcatWalk w ((k : ℤ) - N)).1 ≤ (uibhbotConcatWalk w s).1)
    (M : ℕ) (hNM : N ≤ M) :
    minL (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) (M - N + k) =
      L (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) (M - N + k) := by
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  change minL (shiftedStream W N) k = L (shiftedStream W N) k at hrec
  change minL (shiftedStream W M) (M - N + k) = L (shiftedStream W M) (M - N + k)
  apply le_antisymm (runningMin_le _ _ _ le_rfl)
  obtain ⟨i, hi, he⟩ := runningMin_attained (L (shiftedStream W M)) (M - N + k)
  change minL (shiftedStream W M) (M - N + k) = _ at he
  change L (shiftedStream W M) (M - N + k) ≤ minL (shiftedStream W M) (M - N + k)
  rw [he]
  by_cases his : i < M - N
  · have hb := hbar ((i : ℤ) - M) (by omega)
    have hi' := window_integral_fst W M i
    have hk' := window_integral_fst W M (M - N + k)
    have hkabs : ((M - N + k : ℕ) : ℤ) - M = (k : ℤ) - N := by omega
    rw [hkabs, wholePlaneWordIntegral_uibhbotCodeWord] at hk'
    rw [wholePlaneWordIntegral_uibhbotCodeWord] at hi'
    omega
  · have hid : i = M - N + (i - (M - N)) := by omega
    have hr := runningMin_le (L (shiftedStream W N)) k (i - (M - N)) (by omega)
    change minL (shiftedStream W N) k ≤ _ at hr
    rw [hrec] at hr
    rw [hid, shifted_L W N M hNM, shifted_L W N M hNM]
    omega




theorem uibhbotCodeWord_eventualWholePlaneBall (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a)
    (hP2 : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k)) (r : ℕ) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    ∃ N₀, ∀ N ≥ N₀,
      let c := activeInitial (shiftedStream W N) N
      let S := kmswStageBallVertices (fun _ _ => True)
        (kmswStage (shiftedStream W N) (2 * N)) r c
      kmswWindowCaptureEventStrongRel (shiftedStream W N) (2 * N) r c ∧
        (∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r c,
          minL (shiftedStream W N) k = L (shiftedStream W N) k) ∧
        wholePlaneBallVertices W r (wholePlaneVertexι W N c) =
          (wholePlaneVertexι W N) '' (S : Set ℕ) ∧
        Set.BijOn (fun e : Fin (kmswStage (shiftedStream W N) (2 * N)).nextEdge =>
          wholePlaneEdgeι W N e.val)
          {e | (kmswStage (shiftedStream W N) (2 * N)).west e.val ∈ S ∧
            (kmswStage (shiftedStream W N) (2 * N)).east e.val ∈ S}
          {e | wholePlaneEdgeWest W e ∈
              wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
            wholePlaneEdgeEast W e ∈
              wholePlaneBallVertices W r (wholePlaneVertexι W N c)} := by
  obtain ⟨A, hA⟩ := uibhbotCodeWord_eventualRelaxedCapture w hw hP1 hP2 r
  obtain ⟨B, hB⟩ := uibhbotCodeWord_eventualLeftSeamBarrier w hw hP1 hP2 r
  refine ⟨max A B, ?_⟩
  intro N hN
  have hAN : A ≤ N := (Nat.le_max_left _ _).trans hN
  have hBN : B ≤ N := (Nat.le_max_right _ _).trans hN
  have hev := hA N hAN
  have hbar := hB N hBN
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  let c := activeInitial (shiftedStream W N) N
  have hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k) := by
    intro M hNM k hk
    exact uibhbotCodeWord_minL_eq_of_leftSeamBarrier w hw N k
      (hev.2 k hk) (hbar k hk) M hNM
  exact ⟨hev.1, hev.2,
    wholePlaneBallVertices_eq_image_of_windowCaptureEventRel W N (2 * N) r c hev.1.1 hglob,
    kmswWindowCaptureEventStrongRel_wholePlaneEdge_bijOn W N (2 * N) r c hev.1 hglob⟩





theorem uibhbotWordFamilyLaw_ae_eventualWholePlaneBall_of_pos
    (h : 0 < uibhbotWordFamilyLaw
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k}) :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k), ∀ r : ℕ,
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ∃ N₀, ∀ N ≥ N₀,
          let c := activeInitial (shiftedStream W N) N
          let S := kmswStageBallVertices (fun _ _ => True)
            (kmswStage (shiftedStream W N) (2 * N)) r c
          kmswWindowCaptureEventStrongRel (shiftedStream W N) (2 * N) r c ∧
            (∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r c,
              minL (shiftedStream W N) k = L (shiftedStream W N) k) ∧
            wholePlaneBallVertices W r (wholePlaneVertexι W N c) =
              (wholePlaneVertexι W N) '' (S : Set ℕ) ∧
            Set.BijOn (fun e : Fin (kmswStage (shiftedStream W N) (2 * N)).nextEdge =>
              wholePlaneEdgeι W N e.val)
              {e | (kmswStage (shiftedStream W N) (2 * N)).west e.val ∈ S ∧
                (kmswStage (shiftedStream W N) (2 * N)).east e.val ∈ S}
              {e | wholePlaneEdgeWest W e ∈
                  wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
                wholePlaneEdgeEast W e ∈
                  wholePlaneBallVertices W r (wholePlaneVertexι W N c)} := by
  filter_upwards [uibhbotWordFamilyLaw_ae_hP2_of_pos h,
    ae_uibhbotConcatWalk_snd_unbounded_below] with w hP2 hP1
  obtain ⟨hw, hP2⟩ := hP2
  exact ⟨hw, fun r => uibhbotCodeWord_eventualWholePlaneBall w hw hP1 hP2 r⟩

end DirectedDistances.KMSW
