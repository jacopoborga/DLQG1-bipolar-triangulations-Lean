module

public import DirectedDistances.KMSW.UIBHBOTEventualCapture
public import DirectedDistances.KMSW.KMSWWindowSeamLevel

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem windowEdgeMapInf_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem wholePlaneEdgeTrans_act (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M)
    (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    windowEdgeMapInf_act (shiftedStream W M) (M - N) k

private def absoluteActiveEdge (W : ℤ → Fin 3) (t : ℤ) : WholePlaneEdge W :=
  wholePlaneEdgeι W (-t).toNat
    (act (shiftedStream W (-t).toNat) (t + ((-t).toNat : ℤ)).toNat)

private theorem absoluteActiveEdge_eq (W : ℤ → Fin 3) (N k : ℕ) :
    absoluteActiveEdge W ((k : ℤ) - N) =
      wholePlaneEdgeι W N (act (shiftedStream W N) k) := by
  unfold absoluteActiveEdge
  apply Quotient.sound
  let A := (-((k : ℤ) - N)).toNat
  refine ⟨max A N, Nat.le_max_left _ _, Nat.le_max_right _ _, ?_⟩
  change wholePlaneEdgeTrans W A (max A N) _
      (act (shiftedStream W A) ((k : ℤ) - N + (A : ℤ)).toNat) =
    wholePlaneEdgeTrans W N (max A N) _ (act (shiftedStream W N) k)
  rw [wholePlaneEdgeTrans_act, wholePlaneEdgeTrans_act]
  congr 1
  dsimp only [A]
  omega

private theorem absoluteActiveEdge_injective (W : ℤ → Fin 3) :
    Function.Injective (absoluteActiveEdge W) := by
  intro t u he
  obtain ⟨M, ht, hu, h⟩ := Quotient.exact he
  change wholePlaneEdgeTrans W (-t).toNat M ht
      (act (shiftedStream W (-t).toNat) (t + ((-t).toNat : ℤ)).toNat) =
    wholePlaneEdgeTrans W (-u).toNat M hu
      (act (shiftedStream W (-u).toNat) (u + ((-u).toNat : ℤ)).toNat) at h
  rw [wholePlaneEdgeTrans_act, wholePlaneEdgeTrans_act] at h
  have hk := CutConverse.act_injective (shiftedStream W M) h
  change (-t).toNat ≤ M at ht
  change (-u).toNat ≤ M at hu
  change M - (-t).toNat + (t + ((-t).toNat : ℤ)).toNat =
    M - (-u).toNat + (u + ((-u).toNat : ℤ)).toNat at hk
  omega

private theorem incident_active_time_bounds (W : ℤ → Fin 3)
    (V : WholePlaneVertex W)
    (hfin : {e : WholePlaneEdge W |
      wholePlaneEdgeWest W e = V ∨ wholePlaneEdgeEast W e = V}.Finite) :
    ∃ a b : ℤ, ∀ M k : ℕ,
      (wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).west
          (act (shiftedStream W M) k)) = V ∨
        wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).east
          (act (shiftedStream W M) k)) = V) →
      a ≤ (k : ℤ) - M ∧ (k : ℤ) - M ≤ b := by
  have hf := hfin.preimage (absoluteActiveEdge_injective W).injOn
  obtain ⟨a, ha⟩ := hf.bddBelow
  obtain ⟨b, hb⟩ := hf.bddAbove
  refine ⟨a, b, ?_⟩
  intro M k hk
  have hmem : absoluteActiveEdge W ((k : ℤ) - M) ∈
      {e : WholePlaneEdge W |
        wholePlaneEdgeWest W e = V ∨ wholePlaneEdgeEast W e = V} := by
    change wholePlaneEdgeWest W (absoluteActiveEdge W ((k : ℤ) - M)) = V ∨
      wholePlaneEdgeEast W (absoluteActiveEdge W ((k : ℤ) - M)) = V
    rw [absoluteActiveEdge_eq, wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι]
    have he := edge_endpoints_eq (shiftedStream W M)
      (kmswStage_boundary_ids_lt_nextEdge (shiftedStream W M) k).1
    simpa only [act, he.1, he.2] using hk
  exact ⟨ha hmem, hb hmem⟩

private theorem stage_path_into_colimit (W : ℤ → Fin 3) (N n : ℕ)
    {c k v : ℕ}
    (hp : KMSWStagePath (fun _ _ => True) (kmswStage (shiftedStream W N) n)
      Set.univ c k v) :
    WholePlanePath W Set.univ (wholePlaneVertexι W N c) k
      (wholePlaneVertexι W N v) := by
  induction hp with
  | nil _ => exact .nil (Set.mem_univ _)
  | snoc hp _ _ ha ih =>
    obtain ⟨⟨e, b⟩, _, hx, hy⟩ := ha
    have hs := edge_endpoints_eq (shiftedStream W N) e.isLt
    apply WholePlanePath.snoc ih (Set.mem_univ _) (Set.mem_univ _)
    refine ⟨wholePlaneEdgeι W N e.val, ?_⟩
    rw [wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι]
    cases b
    · exact Or.inl ⟨congrArg _ (hs.1.symm.trans hx),
        congrArg _ (hs.2.symm.trans hy)⟩
    · exact Or.inr ⟨congrArg _ (hs.1.symm.trans hy),
        congrArg _ (hs.2.symm.trans hx)⟩

private theorem initial_trans (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneVertexTrans W N M h (activeInitial (shiftedStream W N) k) =
      activeInitial (shiftedStream W M) (M - N + k) := by
  have he : wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
    simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
      windowEdgeMapInf_act (shiftedStream W M) (M - N) k
  unfold activeInitial
  rw [← wholePlaneEdgeTrans_west, he]

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




theorem uibhbotCodeWord_eventualCreationTimes (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a)
    (hP2 : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k)) (r : ℕ) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    ∃ a b : ℤ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r
        (activeInitial (shiftedStream W N) N),
        a ≤ (k : ℤ) - N ∧ (k : ℤ) - N ≤ b := by
  classical
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  have H := uibhbotCodeWord_rotationHypothesis w hw hP1 hP2
  let x := wholePlaneVertexι W 0 (activeInitial (shiftedStream W 0) 0)
  let B := wholePlaneBallVertices W r x
  have hBfin := wholePlaneBallVertices_finite W H r x
  have hx (y : WholePlaneVertex W) : ∃ a b : ℤ, ∀ M k : ℕ,
      (wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).west
          (act (shiftedStream W M) k)) = y ∨
        wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).east
          (act (shiftedStream W M) k)) = y) →
        a ≤ (k : ℤ) - M ∧ (k : ℤ) - M ≤ b :=
    incident_active_time_bounds W y (wholePlane_incidentEdges_finite W H y)
  choose f g hfg using hx
  obtain ⟨a, ha⟩ := (hBfin.image f).bddBelow
  obtain ⟨b, hb⟩ := (hBfin.image g).bddAbove
  refine ⟨a - 1, b - 1, 0, ?_⟩
  intro N _ k hk
  obtain ⟨⟨v, hv, hcreate⟩, hl, hUL⟩ := (Finset.mem_filter.mp hk).2
  have hc : wholePlaneVertexι W N (activeInitial (shiftedStream W N) N) = x := by
    have ht := congrFun (wholePlaneVertexι_trans W 0 N (Nat.zero_le N))
      (activeInitial (shiftedStream W 0) 0)
    simp only [Function.comp_apply] at ht
    rw [initial_trans] at ht
    simpa only [Nat.sub_zero, Nat.add_zero] using ht
  obtain ⟨j, hj, hp⟩ := (Finset.mem_filter.mp hv).2
  have hball : wholePlaneVertexι W N v ∈ B := by
    have hp' := stage_path_into_colimit W N (2 * N) hp
    rw [hc] at hp'
    exact ⟨j, hj, hp'⟩
  change kmswCodeStep (shiftedStream W N k) = .left at hl
  change (kmswStage (shiftedStream W N) k).UL.dropLast.reverse = [] at hUL
  have he : (kmswStage (shiftedStream W N) (k + 1)).west
      (act (shiftedStream W N) (k + 1)) =
      (kmswStage (shiftedStream W N) k).nextVertex := by
    simp [act, kmswStage, kmswStep, hl, kmswStepOfStep, hUL, State.addEdge]
  have ht := hfg (wholePlaneVertexι W N v) N (k + 1)
    (Or.inl (by rw [he, ← hcreate]))
  have hlow := ha (Set.mem_image_of_mem f hball)
  have hhigh := hb (Set.mem_image_of_mem g hball)
  constructor <;> omega




theorem uibhbotCodeWord_window_level (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (N k : ℕ) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    L (shiftedStream W N) k - L (shiftedStream W N) N =
      (uibhbotConcatWalk w ((k : ℤ) - N)).1 := by
  have he := window_integral_fst (uibhbotCodeWord w (fun k => (hw k).1)) N k
  rw [wholePlaneWordIntegral_uibhbotCodeWord] at he
  dsimp only
  omega




theorem uibhbotCodeWord_eventualCaptureK (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a)
    (hP2 : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k)) (r : ℕ) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    ∃ K0 N₀ : ℕ, ∀ N ≥ N₀,
      kmswWindowCaptureEventK N r K0 (shiftedStream W N) ∧
        ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r
          (activeInitial (shiftedStream W N) N),
          ∀ s : ℤ, s < -(N : ℤ) →
            (uibhbotConcatWalk w ((k : ℤ) - N)).1 ≤ (uibhbotConcatWalk w s).1 := by
  classical
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨a, b, A, hA⟩ := uibhbotCodeWord_eventualCreationTimes w hw hP1 hP2 r
  obtain ⟨B, hB⟩ := uibhbotCodeWord_eventualRelaxedCapture w hw hP1 hP2 r
  obtain ⟨C, hC⟩ := uibhbotCodeWord_eventualLeftSeamBarrier w hw hP1 hP2 r
  let K0 := (Finset.Icc a b).sup (fun t => ((uibhbotConcatWalk w t).1).toNat)
  refine ⟨K0, max A (max B C), ?_⟩
  intro N hN
  have hAN : A ≤ N := (Nat.le_max_left _ _).trans hN
  have hBN : B ≤ N := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hN)
  have hCN : C ≤ N := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hN)
  refine ⟨⟨(hB N hBN).1, ?_⟩, hC N hCN⟩
  apply (kmswBallLeftSeamKmax_le_iff (shiftedStream W N) (2 * N) r
    (activeInitial (shiftedStream W N) N) N K0).mpr
  intro k hk
  rw [uibhbotCodeWord_window_level w hw N k]
  have hmem : (k : ℤ) - N ∈ Finset.Icc a b := Finset.mem_Icc.mpr (hA N hAN k hk)
  have hle : ((uibhbotConcatWalk w ((k : ℤ) - N)).1).toNat ≤ K0 :=
    Finset.le_sup (f := fun t : ℤ => ((uibhbotConcatWalk w t).1).toNat) hmem
  omega

end DirectedDistances.KMSW
