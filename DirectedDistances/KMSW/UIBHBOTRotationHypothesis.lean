module

public import DirectedDistances.KMSW.WholePlaneLeftRecordFresh
public import DirectedDistances.KMSW.UIBHBOTLevelBarrier
public import DirectedDistances.KMSW.ActiveInitialOrigin
import DirectedDistances.RandomWalk.UIBHBOTForwardUnbounded
import DirectedDistances.KMSW.AllocatedVertices
import DirectedDistances.KMSW.CutSeparationAnyStart
import Mathlib.Algebra.BigOperators.Intervals






public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped Classical

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

private theorem range_snd (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum.2 =
      ∑ i ∈ Finset.range n, (f i).2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem window_integral_snd (W : ℤ → Fin 3) (N j : ℕ) :
    R (shiftedStream W N) N +
      (wholePlaneWordIntegral W ((j : ℤ) - N)).2 =
      R (shiftedStream W N) j := by
  by_cases hj : j < N
  · have hd : ((j : ℤ) - N) < 0 := by omega
    have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
    simp only [wholePlaneWordIntegral, ite_eq_right (not_le.mpr hd), Prod.snd_neg,
      hc, bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_snd]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).2) j (N - j)
    have ht : (∑ i ∈ Finset.range (N - j),
        (lazyTwoDimensionalStep (shiftedStream W N (j + i))).2) =
        ∑ i ∈ Finset.range (N - j),
          (lazyTwoDimensionalStep (W (-(i : ℤ) - 1))).2 := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show j + (N - j) = N by omega, ht] at he
    change R (shiftedStream W N) N = R (shiftedStream W N) j + _ at he
    omega
  · have hd : 0 ≤ (j : ℤ) - N := by omega
    have hc : ((j : ℤ) - N).toNat = j - N := by omega
    simp only [wholePlaneWordIntegral, ite_eq_left hd, hc,
      bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_snd]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).2) N (j - N)
    have ht : (∑ i ∈ Finset.range (j - N),
        (lazyTwoDimensionalStep (shiftedStream W N (N + i))).2) =
        ∑ i ∈ Finset.range (j - N), (lazyTwoDimensionalStep (W (i : ℤ))).2 := by
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





theorem uibhbotFresh_of_left_record_barrier (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (M d u : ℕ)
    (hu : u = (kmswStage (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M)
      d).nextVertex)
    (hleft : shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M d = 0)
    (hrec : minL (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) d =
      L (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) d)
    (hbar : ∀ s : ℤ, s < -(M : ℤ) →
      (uibhbotConcatWalk w ((d : ℤ) - M)).1 ≤ (uibhbotConcatWalk w s).1)
    (M' : ℕ) (hMM' : M ≤ M') :
    wholePlaneFresh (uibhbotCodeWord w (fun k => (hw k).1)) M M' hMM' u := by
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  change u = (kmswStage (shiftedStream W M) d).nextVertex at hu
  change shiftedStream W M d = 0 at hleft
  change minL (shiftedStream W M) d = L (shiftedStream W M) d at hrec
  have hUL : (kmswStage (shiftedStream W M) d).UL.dropLast.reverse = [] :=
    (kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ d).mpr hrec.symm
  have hc : kmswCodeStep (shiftedStream W M d) = .left := by
    simp [hleft, kmswCodeStep]
  have hbase : 2 ≤ u := by
    have hm := CutConverse.nextVertex_mono (shiftedStream W M) (Nat.zero_le d)
    change 2 ≤ (kmswStage (shiftedStream W M) d).nextVertex at hm
    omega
  have hmin : minL (shiftedStream W M') (M' - M + d) =
      L (shiftedStream W M') (M' - M + d) := by
    apply le_antisymm (runningMin_le _ _ _ le_rfl)
    obtain ⟨i, hi, he⟩ := runningMin_attained (L (shiftedStream W M')) (M' - M + d)
    change minL (shiftedStream W M') (M' - M + d) = _ at he
    change L (shiftedStream W M') (M' - M + d) ≤
      minL (shiftedStream W M') (M' - M + d)
    rw [he]
    by_cases his : i < M' - M
    · have hb := hbar ((i : ℤ) - M') (by omega)
      have hi' := window_integral_fst W M' i
      have hd' := window_integral_fst W M' (M' - M + d)
      have hdabs : ((M' - M + d : ℕ) : ℤ) - M' = (d : ℤ) - M := by omega
      rw [hdabs, wholePlaneWordIntegral_uibhbotCodeWord] at hd'
      rw [wholePlaneWordIntegral_uibhbotCodeWord] at hi'
      omega
    · have hid : i = M' - M + (i - (M' - M)) := by omega
      have hr := runningMin_le (L (shiftedStream W M)) d
        (i - (M' - M)) (by omega)
      change minL (shiftedStream W M) d ≤ _ at hr
      rw [hrec] at hr
      rw [hid, shifted_L W M M' hMM', shifted_L W M M' hMM']
      omega
  have hlen := kmswStage_UL_length (shiftedStream W M') (M' - M + d)
  rw [hmin] at hlen
  have hrel := kmswWindowPatchData_rel (shiftedStream W M') (M' - M) d
  have hlength := congrArg List.length hrel.ul
  have hpos := List.length_pos_of_ne_nil
    (kmswStage_UL_nonempty_active_last (shiftedStream W M) d).1
  rw [shiftedStream_shift W M M' hMM'] at hlength
  simp only [List.length_append, List.length_map] at hlength
  have hA : (kmswWindowPatchData (shiftedStream W M') (M' - M) d).A = [] :=
    List.length_eq_zero_iff.mp (by omega)
  by_contra hf
  rcases (wholePlaneFresh_iff_windowSeam W M M' hMM' u).mp hf with
    hsmall | ⟨j, _, hju, hdown | hleft'⟩
  · omega
  · have hj := kmswCreationStage_unique (shiftedStream W M) u d j hu.symm
        (Or.inr ⟨hc, hUL⟩) hju.symm (Or.inl ⟨hdown.1, hdown.2.1⟩)
    subst j
    rw [hc] at hdown
    cases hdown.1
  · have hj := kmswCreationStage_unique (shiftedStream W M) u d j hu.symm
        (Or.inr ⟨hc, hUL⟩) hju.symm (Or.inr ⟨hleft'.1, hleft'.2.1⟩)
    subst j
    exact hleft'.2.2 (by rw [hA]; rfl)

private theorem up_nonrecord (w : ℕ → Fin 3) (k : ℕ) (hk : w k = 1) :
    KMSWNonrecordVertex w (kmswStage w k).nextVertex := by
  have hbase : 2 ≤ (kmswStage w k).nextVertex :=
    CutConverse.nextVertex_mono w (Nat.zero_le k)
  have hup : (kmswStage w (k + 1)).nextVertex =
      (kmswStage w k).nextVertex + 1 := by
    simp [kmswStage, kmswStep, kmswCodeStep, hk, kmswStepOfStep, State.addEdge]
  refine ⟨hbase, ?_⟩
  intro j hj
  have exclude (halloc : (kmswStage w j).nextVertex <
      (kmswStage w (j + 1)).nextVertex) : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · have hm := CutConverse.nextVertex_mono w (Nat.succ_le_of_lt h)
      change (kmswStage w (j + 1)).nextVertex ≤ (kmswStage w k).nextVertex at hm
      omega
    · exact h
    · have hm := CutConverse.nextVertex_mono w (Nat.succ_le_of_lt h)
      change (kmswStage w (k + 1)).nextVertex ≤ (kmswStage w j).nextVertex at hm
      omega
  constructor
  · intro hd hr
    have hu := (kmswStage_UR_eq_nil_iff_record w j).mpr hr
    have he : j = k := exclude (by simp [kmswStage, kmswStep, hd, kmswStepOfStep, hu])
    subst j
    simp [kmswCodeStep, hk] at hd
  · intro hl hr
    have hu := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w j).mpr hr
    have he : j = k := exclude (by
      simp [kmswStage, kmswStep, hl, kmswStepOfStep, hu, State.addEdge])
    subst j
    simp [kmswCodeStep, hk] at hl

private theorem windowEdgeMapInf_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem initial_trans (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneVertexTrans W N M h (activeInitial (shiftedStream W N) k) =
      activeInitial (shiftedStream W M) (M - N + k) := by
  have he : wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
    simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
      windowEdgeMapInf_act (shiftedStream W M) (M - N) k
  unfold activeInitial
  rw [← wholePlaneEdgeTrans_west, he]

private theorem run_R_unbounded (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a) (N : ℕ) :
    ∀ a : ℤ, ∃ n, R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) n ≤ a := by
  intro a
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨n, hn⟩ := hP1 (a - R (shiftedStream W N) N)
  refine ⟨N + n, ?_⟩
  have he := window_integral_snd W N (N + n)
  have ha : ((N + n : ℕ) : ℤ) - N = (n : ℤ) := by omega
  rw [ha, wholePlaneWordIntegral_uibhbotCodeWord] at he
  change R (shiftedStream W N) (N + n) ≤ a
  omega





theorem uibhbotCodeWord_finiteIncidence (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a) (N : ℕ) :
    KMSWFiniteIncidence (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) := by
  apply kmsw_finite_incident_edges_of_unbounded_below
  · intro a
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    obtain ⟨n, hn⟩ := uibhbotConcatWalk_fst_unbounded_below_of_stopped w hw
      (a - L (shiftedStream W N) N)
    refine ⟨N + n, ?_⟩
    have he := window_integral_fst W N (N + n)
    have ha : ((N + n : ℕ) : ℤ) - N = (n : ℤ) := by omega
    rw [ha, wholePlaneWordIntegral_uibhbotCodeWord] at he
    change L (shiftedStream W N) (N + n) ≤ a
    omega
  · exact run_R_unbounded w hw hP1 N








theorem uibhbotCodeWord_cofinalFreshness (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a)
    (hP2 : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k)) :
    ∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
      wholePlaneFresh (uibhbotCodeWord w (fun k => (hw k).1)) M M' hMM'
        (wholePlaneVertexTrans (uibhbotCodeWord w (fun k => (hw k).1)) N M hNM v) := by
  classical
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  intro N v
  obtain ⟨k, hk⟩ := allocated_vertex_eventually_activeInitial_of_R_unbounded
    (shiftedStream W N) (run_R_unbounded w hw hP1 N) v
    (kmsw_vertex_allocated_of_finite_incidence _ (uibhbotCodeWord_finiteIncidence w hw hP1 N) v)
  let t : ℤ := (k : ℤ) - N
  obtain ⟨s₀, hs₀⟩ := uibhbotConcatWalk_D2 w hw t
  let J := Finset.Icc (s₀ - 1) t
  let f : ℤ → ℕ := fun j => Classical.choose (hP2 j)
  let M := max N (max (1 - s₀).toNat (J.sup f))
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hlarge : (1 - s₀).toNat ≤ M :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsup : J.sup f ≤ M :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstart : -(M : ℤ) < s₀ := by omega
  let m := M - N + k
  have hmabs : (m : ℤ) - M = t := by dsimp [m, t]; omega
  have htrans : wholePlaneVertexTrans W N M hNM v = activeInitial (shiftedStream W M) m := by
    rw [← hk, initial_trans]
  let P := fun a => activeInitial (shiftedStream W M) a = activeInitial (shiftedStream W M) m
  have hex : ∃ a, P a := ⟨m, rfl⟩
  let a := Nat.find hex
  have ha : P a := Nat.find_spec hex
  have ham : a ≤ m := Nat.find_min' hex rfl
  have hlev := activeInitial_level_eq (shiftedStream W M) ham ha
  have hea := window_integral_fst W M a
  have hem := window_integral_fst W M m
  rw [wholePlaneWordIntegral_uibhbotCodeWord] at hea
  rw [hmabs, wholePlaneWordIntegral_uibhbotCodeWord] at hem
  have habs : s₀ ≤ (a : ℤ) - M := by
    by_contra h
    have hb := hs₀ ((a : ℤ) - M) (by omega)
    omega
  have ha0 : 0 < a := by omega
  have hfirst : ∀ b, b < a → activeInitial (shiftedStream W M) b ≠
      activeInitial (shiftedStream W M) m := by
    intro b hb he
    have hmin := Nat.find_min' hex he
    change a ≤ b at hmin
    omega
  have hrecords : ∀ d, a - 1 ≤ d → d < m →
      minR (shiftedStream W M) d < R (shiftedStream W M) d := by
    intro d had hdm
    have hj : (d : ℤ) - M ∈ J := by
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    have hf : f ((d : ℤ) - M) ≤ M := (Finset.le_sup hj).trans hsup
    have hb := Classical.choose_spec (hP2 ((d : ℤ) - M)) M hf
    have hd : ((d : ℤ) - M + (M : ℤ)).toNat = d := by omega
    simpa only [hd] using hb.2
  rcases activeInitial_origin_dichotomy (shiftedStream W M) ha0 ham hfirst
    (hfirst (a - 1) (by omega)) ha hrecords with ⟨i, hi, hv⟩ | ⟨d, hdm, hd, hrec, hv⟩
  · refine ⟨M, hNM, ?_⟩
    intro M' hMM'
    rw [htrans, hv]
    exact wholePlaneFresh_of_nonrecord W M M' hMM' _ (up_nonrecord _ i hi)
  · have hUL := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record
      (shiftedStream W M) d).mpr hrec.symm
    have hnew : activeInitial (shiftedStream W M) (d + 1) =
        (kmswStage (shiftedStream W M) d).nextVertex := by
      rw [CutConverse.activeInitial_eq]
      simp [act, kmswStage, kmswStep, hd, kmswCodeStep, kmswStepOfStep, hUL, State.addEdge]
    have hlevel := activeInitial_level_eq (shiftedStream W M) (show d + 1 ≤ m by omega)
      (hnew.trans hv.symm)
    have hstep : L (shiftedStream W M) (d + 1) = L (shiftedStream W M) d - 1 := by
      simp only [L, Finset.sum_range_succ, hd, lazyTwoDimensionalStep_zero]
      omega
    have hed := window_integral_fst W M d
    rw [wholePlaneWordIntegral_uibhbotCodeWord] at hed
    have hbar : ∀ s : ℤ, s < -(M : ℤ) →
        (uibhbotConcatWalk w ((d : ℤ) - M)).1 ≤ (uibhbotConcatWalk w s).1 := by
      intro s hs
      have hb := hs₀ s (by omega)
      omega
    refine ⟨M, hNM, ?_⟩
    intro M' hMM'
    rw [htrans, hv]
    exact uibhbotFresh_of_left_record_barrier w hw M d _ rfl hd hrec hbar M' hMM'








theorem uibhbotCodeWord_rotationHypothesis (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a)
    (hP2 : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k)) :
    WholePlaneRotationHypothesis (uibhbotCodeWord w (fun k => (hw k).1)) :=
  ⟨uibhbotCodeWord_finiteIncidence w hw hP1,
    uibhbotCodeWord_cofinalFreshness w hw hP1 hP2⟩

end DirectedDistances.KMSW
