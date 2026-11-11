module

public import DirectedDistances.RandomWalk.UIBHBOTBoundaryFutureCodeLaw
public import DirectedDistances.KMSW.DirectedContainHat
public import DirectedDistances.KMSW.KMSWWindowActiveRoot
public import DirectedDistances.KMSW.LimitExternalFace
import DirectedDistances.KMSW.ActiveInitialOrigin

/-! Boundary alignment for the future carrier in `lem-uihbot-future`.
All statements concern the existing combinatorial colimit carrier. Identification with the
embedded manuscript map and reverse path transport are separate obligations. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory DirectedDistances.KMSW Quiver
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem cast_list (xs : List ℕ) :
    (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem range_fst (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum.1 = ∑ i ∈ Finset.range n, (f i).1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem window_integral_fst (W : ℤ → Fin 3) (N j : ℕ) :
    L (shiftedStream W N) N +
      (wholePlaneWordIntegral W ((j : ℤ) - N)).1 = L (shiftedStream W N) j := by
  by_cases hj : j < N
  · have hd : ¬ 0 ≤ (j : ℤ) - N := by omega
    have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
    simp only [wholePlaneWordIntegral, ite_eq_right hd, Prod.fst_neg, hc,
      bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_fst]
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

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotStart_L (W : ℤ → Fin 3) (t : ℤ) (n : ℕ) :
    L (lemma38StartStream W t) n =
      (wholePlaneWordIntegral W (t + n)).1 - (wholePlaneWordIntegral W t).1 := by
  let N := t.natAbs
  let s := (t + (N : ℤ)).toNat
  have hs : (s : ℤ) = t + N := Int.toNat_of_nonneg (by
    have := Int.natCast_natAbs t
    omega)
  have hc : (fun i => shiftedStream W N (s + i)) = lemma38StartStream W t := by
    funext i
    unfold shiftedStream lemma38StartStream
    congr 1
    push_cast
    omega
  have ha := L_window_additivity (lemma38StartStream W t) (shiftedStream W N)
    s n n le_rfl (fun i _ => congrFun hc i)
  have h0 := window_integral_fst W N s
  have h1 := window_integral_fst W N (s + n)
  have ht0 : (s : ℤ) - N = t := by omega
  have ht1 : ((s + n : ℕ) : ℤ) - N = t + n := by omega
  rw [ht0] at h0
  rw [ht1] at h1
  omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem startVertex_cofinal (W : ℤ → Fin 3) (t : ℤ) (N : ℕ)
    (hN : t.natAbs ≤ N) (v : ℕ) :
    lemma38StartVertexι W t v = wholePlaneVertexι W N
      (kmswWindowVertexMapInf (shiftedStream W N) (t + (N : ℤ)).toNat v) := by
  by_cases ht : t ≤ 0
  · rw [lemma38StartVertexι, ite_eq_left ht]
    have hc := congrFun (wholePlaneVertexι_trans W t.natAbs N hN) v
    have ha : (t + (N : ℤ)).toNat = N - t.natAbs := by
      have := Int.ofNat_natAbs_of_nonpos ht
      omega
    rw [ha]
    exact hc.symm
  · rw [lemma38StartVertexι, ite_eq_right ht]
    have hc := congrFun (wholePlaneVertexι_trans W 0 N (Nat.zero_le N))
      (kmswWindowVertexMapInf (shiftedStream W 0) t.toNat v)
    rw [← hc]
    change wholePlaneVertexι W N
      (kmswWindowVertexMapInf (shiftedStream W N) (N - 0)
        (kmswWindowVertexMapInf (shiftedStream W 0) t.toNat v)) = _
    rw [Nat.sub_zero, ← shiftedStream_shift W 0 N (Nat.zero_le N),
      Nat.sub_zero, kmswWindowVertexMapInf_comp]
    congr 2
    have := Int.toNat_of_nonneg (show 0 ≤ t by omega)
    omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem window_activeInitial (w : ℕ → Fin 3) (s n : ℕ) :
    kmswWindowVertexMapInf w s (activeInitial (fun i => w (s + i)) n) =
      activeInitial w (s + n) := by
  have hb := (kmswStage_endpoints_lt_nextVertex (fun i => w (s + i)) n
    (act (fun i => w (s + i)) n) (act_lt_nextEdge _ le_rfl)).1
  have hb' : activeInitial (fun i => w (s + i)) n <
      (kmswStage (fun i => w (s + i)) n).nextVertex := by
    rw [CutConverse.activeInitial_eq]
    exact hb
  rw [kmswWindowVertexMapInf_eq_stage w s n _ hb']
  exact kmswWindowPatchVertexMap_activeInitial _ _ s n (fun _ _ => rfl)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotStartVertex_activeInitial (W : ℤ → Fin 3) (t : ℤ) (n : ℕ) :
    lemma38StartVertexι W t (activeInitial (lemma38StartStream W t) n) =
      lemma38StartVertexι W (t + n) 0 := by
  let N := max t.natAbs (t + (n : ℤ)).natAbs
  have ht : t.natAbs ≤ N := Nat.le_max_left _ _
  have hs : (t + (n : ℤ)).natAbs ≤ N := Nat.le_max_right _ _
  rw [startVertex_cofinal W t N ht, startVertex_cofinal W (t + n) N hs]
  have htn : 0 ≤ t + (N : ℤ) := by
    have := Int.natCast_natAbs t
    omega
  have hc : lemma38StartStream W t =
      fun i => shiftedStream W N ((t + (N : ℤ)).toNat + i) := by
    funext i
    unfold lemma38StartStream shiftedStream
    congr 1
    have := Int.toNat_of_nonneg htn
    push_cast
    omega
  rw [hc, window_activeInitial]
  have hz : 0 = activeInitial
      (fun i => shiftedStream W N ((t + (n : ℤ) + N).toNat + i)) 0 := by
    rw [CutConverse.activeInitial_eq]
    rfl
  rw [hz, window_activeInitial]
  congr 2
  have := Int.toNat_of_nonneg htn
  have := Int.toNat_of_nonneg (show 0 ≤ t + (n : ℤ) + N by omega)
  omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem measurable_integral (t : ℤ) :
    Measurable (fun W : ℤ → Fin 3 => wholePlaneWordIntegral W t) := by
  have hm (xs : List ℤ) (f : ℤ → ℤ) : Measurable (fun W : ℤ → Fin 3 =>
      (xs.map (fun i => lazyTwoDimensionalStep (W (f i)))).sum) := by
    induction xs with
    | nil => exact measurable_const
    | cons a xs ih =>
        exact ((measurable_of_countable lazyTwoDimensionalStep).comp
          (measurable_pi_apply (f a))).add ih
  unfold wholePlaneWordIntegral
  split
  · exact hm _ id
  · exact (hm _ (fun i => -i - 1)).neg

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem ae_uibhbotBoundaryHit_strictRecord :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k s : ℤ,
      s < uibhbotBoundaryHitTime k W → k < (wholePlaneWordIntegral W s).1 := by
  have hS : MeasurableSet {W : ℤ → Fin 3 | ∀ k t s : ℤ,
      ¬ UIBHBOTBoundaryHit k t W ∨ ¬ s < t ∨ k < (wholePlaneWordIntegral W s).1} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun t =>
      MeasurableSet.iInter fun s => ?_
    simp only [Set.ofPred_or]
    refine MeasurableSet.union ?_ ?_
    · exact (measurableSet_uibhbotBoundaryHit k t).compl
    · by_cases hs : s < t
      · simp only [hs, not_true_eq_false, Set.ofPred_false, Set.empty_union]
        exact measurableSet_lt measurable_const (measurable_integral s).fst
      · simp only [hs, not_false_eq_true, Set.ofPred_true, Set.univ_union]
        exact MeasurableSet.univ
  have he : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k t s : ℤ,
      ¬ UIBHBOTBoundaryHit k t W ∨ ¬ s < t ∨ k < (wholePlaneWordIntegral W s).1 := by
    change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
    apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable hS).mpr
    filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw k t s
    by_cases hh : UIBHBOTBoundaryHit k t (uibhbotCodeWordRel w)
    · by_cases hs : s < t
      · apply Or.inr ∘ Or.inr
        have ht := (uibhbotBoundaryHitTime_eq hh).symm.trans
          (uibhbotBoundaryHitTime_codeWordRel k w hw)
        subst t
        rw [uibhbotCodeWordRel_eq w (fun j => (hw j).1),
          wholePlaneWordIntegral_uibhbotCodeWord]
        have hrec := uibhbotConcatWalk_blockEndpoint_strictRecord w hw (-k - 1) s
          (by simpa only [sub_add_cancel] using hs)
        rw [show -k - 1 + 1 = -k by omega,
          uibhbotConcatWalk_stopped_blockBoundary_fst w hw] at hrec
        omega
      · exact Or.inr (Or.inl hs)
    · exact Or.inl hh
  filter_upwards [he, ae_uibhbotBoundaryHit] with W hW hhit k s hs
  rcases hW k (uibhbotBoundaryHitTime k W) s with h | h | h
  · exact (h (hhit k)).elim
  · exact (h hs).elim
  · exact h

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem alignment_of_records (W : ℤ → Fin 3)
    (hhit : ∀ k, UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    (hrec : ∀ k s, s < uibhbotBoundaryHitTime k W →
      k < (wholePlaneWordIntegral W s).1) :
    ∀ k, UIBHBOTFutureBoundaryAlignment k W := by
  intro k h ℓ hℓ
  by_cases heq : ℓ = k
  · subst ℓ
    rw [sub_self, boundaryVertex_zero]
  · have hlt : ℓ < k := by omega
    let t := uibhbotBoundaryHitTime k W
    let s := uibhbotBoundaryHitTime ℓ W
    have hts : t ≤ s := by
      by_contra hn
      have hr := hrec k s (by omega)
      rw [(hhit ℓ).1] at hr
      omega
    have hn : ((s - t).toNat : ℤ) = s - t := Int.toNat_of_nonneg (by omega)
    let u := fun i => uibhbotFutureCode k W (i + 1)
    have hu : u = lemma38StartStream W t := uibhbotFutureCode_stream k W
    have htime : boundaryHitTime u h (ℓ - k) = (s - t).toNat := by
      unfold boundaryHitTime
      rw [dite_eq_right (by omega : ℓ - k ≠ 0), dite_eq_right (by omega : ¬ 0 < ℓ - k)]
      apply (Nat.find_eq_iff _).mpr
      constructor
      · rw [hu, uibhbotStart_L, show t + ((s - t).toNat : ℤ) = s by omega]
        rw [(hhit ℓ).1, (hhit k).1]
      · intro n hnlt hlevel
        rw [hu, uibhbotStart_L] at hlevel
        have hbad : (wholePlaneWordIntegral W (t + n)).1 = ℓ := by
          rw [(hhit k).1] at hlevel
          omega
        exact (hhit ℓ).2 (t + n) (by omega) hbad
    have hv : boundaryVertex u h (ℓ - k) = activeInitial u (s - t).toNat := by
      rw [boundaryVertex_eq_activeInitial u h (by omega) (by omega), htime]
    change uibhbotFutureVertex k W (boundaryVertex u h (ℓ - k)) = _
    rw [hv, hu]
    change lemma38StartVertexι W t (activeInitial (lemma38StartStream W t)
      (s - t).toNat) = lemma38StartVertexι W s 0
    rw [uibhbotStartVertex_activeInitial, show t + ((s - t).toNat : ℤ) = s by omega]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
This closes the existing combinatorial boundary-alignment obligation. -/
theorem uibhbotFutureBoundaryAlignment_ae : UIBHBOTFutureBoundaryAlignmentAlmostSure := by
  filter_upwards [ae_uibhbotBoundaryHit, ae_uibhbotBoundaryHit_strictRecord] with W hh hr
  exact alignment_of_records W hh hr

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem ae_uibhbotFutureBoundary_index :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ j : ℤ, j ≤ 0 →
          uibhbotFutureVertex k W
            (boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j) =
              uibhbotFutureVertex (k + j) W 0 := by
  filter_upwards [uibhbotFutureBoundaryAlignment_ae] with W hW k h j hj
  have ha := hW k h (k + j) (by omega)
  simpa only [add_sub_cancel_left] using ha

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem ae_uibhbotFuture_boundaryHitWitnesses :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)) := by
  apply ae_all_iff.mpr
  intro k
  have h := iidCodes_ae_boundaryHitWitnesses
  rw [← uibhbotFutureCode_law k] at h
  exact ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Geometric missing edges have no activation time. -/
@[expose] def uibhbotAbsoluteActiveEdge (W : ℤ → Fin 3) (t : ℤ) : WholePlaneEdge W :=
  lemma38StartEdgeι W t 0

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem startEdge_cofinal (W : ℤ → Fin 3) (t : ℤ) (N : ℕ)
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

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem window_active (w : ℕ → Fin 3) (s n : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) n) = act w (s + n) := by
  rw [kmswWindowEdgeMapInf_eq_stage w s n _ (act_lt_nextEdge _ le_rfl)]
  exact (kmswWindowPatchData_rel w s n).active

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem absoluteActive_cofinal (W : ℤ → Fin 3) (t : ℤ) (N : ℕ)
    (hN : t.natAbs ≤ N) :
    uibhbotAbsoluteActiveEdge W t =
      wholePlaneEdgeι W N (act (shiftedStream W N) (t + (N : ℤ)).toNat) := by
  rw [uibhbotAbsoluteActiveEdge, startEdge_cofinal W t N hN]
  have hz : 0 = act
      (fun i => shiftedStream W N ((t + (N : ℤ)).toNat + i)) 0 := rfl
  rw [hz, window_active, Nat.add_zero]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotStartEdge_active (W : ℤ → Fin 3) (t : ℤ) (n : ℕ) :
    lemma38StartEdgeι W t (act (lemma38StartStream W t) n) =
      uibhbotAbsoluteActiveEdge W (t + n) := by
  let N := max t.natAbs (t + (n : ℤ)).natAbs
  have ht : t.natAbs ≤ N := Nat.le_max_left _ _
  have hs : (t + (n : ℤ)).natAbs ≤ N := Nat.le_max_right _ _
  rw [startEdge_cofinal W t N ht, absoluteActive_cofinal W (t + n) N hs]
  have htn : 0 ≤ t + (N : ℤ) := by
    have := Int.natCast_natAbs t
    omega
  have hc : lemma38StartStream W t =
      fun i => shiftedStream W N ((t + (N : ℤ)).toNat + i) := by
    funext i
    unfold lemma38StartStream shiftedStream
    congr 1
    have := Int.toNat_of_nonneg htn
    push_cast
    omega
  rw [hc, window_active]
  congr 2
  have := Int.toNat_of_nonneg htn
  have := Int.toNat_of_nonneg (show 0 ≤ t + (n : ℤ) + N by omega)
  omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
missing geometric edges are excluded from both sides. -/
theorem uibhbotFuture_presentEdge_image (k : ℤ) (W : ℤ → Fin 3) :
    (uibhbotFutureEdge k W) '' {e | EdgePresent
      (fun i => uibhbotFutureCode k W (i + 1)) e} =
        {e | ∃ t : ℤ, uibhbotBoundaryHitTime k W ≤ t ∧
          uibhbotAbsoluteActiveEdge W t = e} := by
  ext e
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨n, hn, _⟩ := existsUnique_actTime _ f hf
    refine ⟨uibhbotBoundaryHitTime k W + n, by omega, ?_⟩
    rw [hn]
    change _ = lemma38StartEdgeι W (uibhbotBoundaryHitTime k W)
      (act (fun i => uibhbotFutureCode k W (i + 1)) n)
    rw [uibhbotFutureCode_stream, uibhbotStartEdge_active]
  · rintro ⟨t, ht, rfl⟩
    let n := (t - uibhbotBoundaryHitTime k W).toNat
    have hn : (n : ℤ) = t - uibhbotBoundaryHitTime k W :=
      Int.toNat_of_nonneg (by omega)
    refine ⟨act (fun i => uibhbotFutureCode k W (i + 1)) n, ?_, ?_⟩
    · change EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) _
      simpa only [Nat.zero_add] using kmswShift_active_edge_present_limit
        (fun i => uibhbotFutureCode k W (i + 1)) 0 n
    · change lemma38StartEdgeι W (uibhbotBoundaryHitTime k W)
        (act (fun i => uibhbotFutureCode k W (i + 1)) n) = _
      rw [uibhbotFutureCode_stream, uibhbotStartEdge_active]
      congr 1
      omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
ones, are exactly the images of finite suffix allocations. This does not identify faces. -/
theorem uibhbotFuture_geometricEdge_image (k : ℤ) (W : ℤ → Fin 3) :
    Set.range (uibhbotFutureEdge k W) = {e | ∃ n f,
      f < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
        uibhbotFutureEdge k W f = e} := by
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, f, kmsw_edge_allocated_by_self _ f, rfl⟩
  · rintro ⟨_, f, _, hf⟩
    exact ⟨f, hf⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem absoluteActive_west (W : ℤ → Fin 3) (t : ℤ) :
    wholePlaneEdgeWest W (uibhbotAbsoluteActiveEdge W t) =
      lemma38StartVertexι W t 0 := lemma38StartEdgeWest W t 0

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem present_absoluteActive (W : ℤ → Fin 3) (e : WholePlaneEdge W)
    (he : wholePlaneEdgePresent W e) : ∃ t : ℤ, uibhbotAbsoluteActiveEdge W t = e := by
  obtain ⟨N, f, hf⟩ := wholePlaneEdge_has_run_rep W e
  rw [← hf, wholePlaneEdgePresent_ι] at he
  obtain ⟨M, hNM, hp⟩ := he
  have hg := hp M le_rfl
  obtain ⟨n, hn, _⟩ := existsUnique_actTime _ _ hg
  have hι := congrFun (wholePlaneEdgeι_trans W N M hNM) f
  change wholePlaneEdgeι W M (wholePlaneEdgeTrans W N M hNM f) = _ at hι
  rw [hn] at hι
  have hc := uibhbotStartEdge_active W (-(M : ℤ)) n
  have hs : lemma38StartStream W (-(M : ℤ)) = shiftedStream W M := by
    funext i
    simp only [lemma38StartStream, shiftedStream, sub_eq_add_neg]
  rw [hs] at hc
  have hi : lemma38StartEdgeι W (-(M : ℤ)) (act (shiftedStream W M) n) =
      wholePlaneEdgeι W M (act (shiftedStream W M) n) := by
    simp [lemma38StartEdgeι]
  rw [hi] at hc
  exact ⟨-(M : ℤ) + n, hc.symm.trans (hι.trans hf)⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem startVertex_level (W : ℤ → Fin 3) (t s : ℤ)
    (he : lemma38StartVertexι W t 0 = lemma38StartVertexι W s 0) :
    (wholePlaneWordIntegral W t).1 = (wholePlaneWordIntegral W s).1 := by
  let N := max t.natAbs s.natAbs
  have ht : t.natAbs ≤ N := Nat.le_max_left _ _
  have hs : s.natAbs ≤ N := Nat.le_max_right _ _
  rw [startVertex_cofinal W t N ht, startVertex_cofinal W s N hs] at he
  have hf (j : ℕ) : kmswWindowVertexMapInf (shiftedStream W N) j 0 =
      activeInitial (shiftedStream W N) j := by
    exact window_activeInitial (shiftedStream W N) j 0
  rw [hf, hf] at he
  have hv := wholePlaneVertexι_injective W N he
  have hL : L (shiftedStream W N) (t + (N : ℤ)).toNat =
      L (shiftedStream W N) (s + (N : ℤ)).toNat := by
    rcases le_total (t + (N : ℤ)).toNat (s + (N : ℤ)).toNat with h | h
    · exact activeInitial_level_eq _ h hv
    · exact (activeInitial_level_eq _ h hv.symm).symm
  have ht0 : ((t + (N : ℤ)).toNat : ℤ) - N = t := by
    have := Int.natCast_natAbs t
    have := Int.toNat_of_nonneg (show 0 ≤ t + (N : ℤ) by omega)
    omega
  have hs0 : ((s + (N : ℤ)).toNat : ℤ) - N = s := by
    have := Int.natCast_natAbs s
    have := Int.toNat_of_nonneg (show 0 ≤ s + (N : ℤ) by omega)
    omega
  have hti := window_integral_fst W N (t + (N : ℤ)).toNat
  have hsi := window_integral_fst W N (s + (N : ℤ)).toNat
  rw [ht0] at hti
  rw [hs0] at hsi
  omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem absoluteActive_consecutive (W : ℤ → Fin 3) (t s : ℤ)
    (he : wholePlaneEdgeEast W (uibhbotAbsoluteActiveEdge W t) =
      wholePlaneEdgeWest W (uibhbotAbsoluteActiveEdge W s)) : t < s := by
  let N := max t.natAbs s.natAbs
  have ht : t.natAbs ≤ N := Nat.le_max_left _ _
  have hs : s.natAbs ≤ N := Nat.le_max_right _ _
  rw [absoluteActive_cofinal W t N ht, absoluteActive_cofinal W s N hs,
    wholePlaneEdgeEast_ι, wholePlaneEdgeWest_ι] at he
  have hv := wholePlaneVertexι_injective W N he
  have hp (n : ℕ) : EdgePresent (shiftedStream W N) (act (shiftedStream W N) n) := by
    simpa only [Nat.zero_add] using
      kmswShift_active_edge_present_limit (shiftedStream W N) 0 n
  have hlt := actTime_lt_of_consecutive _ (hp (t + (N : ℤ)).toNat)
    (hp (s + (N : ℤ)).toNat) hv
  rw [(actTime_eq_iff _ _ _ _).mpr rfl, (actTime_eq_iff _ _ _ _).mpr rfl] at hlt
  have := Int.natCast_natAbs t
  have := Int.natCast_natAbs s
  have := Int.toNat_of_nonneg (show 0 ≤ t + (N : ℤ) by omega)
  have := Int.toNat_of_nonneg (show 0 ≤ s + (N : ℤ) by omega)
  omega

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
geometric edge; parallel edges retain their identities. -/
structure UIBHBOTPresentVertex (W : ℤ → Fin 3) where
  /-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
  id : WholePlaneVertex W

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
instance uibhbotPresentQuiver (W : ℤ → Fin 3) : Quiver (UIBHBOTPresentVertex W) where
  Hom a b := {e : WholePlaneEdge W // wholePlaneEdgePresent W e ∧
    wholePlaneEdgeWest W e = a.id ∧ wholePlaneEdgeEast W e = b.id}

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
@[expose] noncomputable def uibhbotFutureToGlobal (k : ℤ) (W : ℤ → Fin 3) :
    Prefunctor (PresentVertex (fun i => uibhbotFutureCode k W (i + 1)))
      (UIBHBOTPresentVertex W) where
  obj a := ⟨uibhbotFutureVertex k W a.id⟩
  map e := ⟨uibhbotFutureEdge k W e.val, uibhbotFutureEdge_present k W _ e.property.1,
    (uibhbotFutureEdge_west k W _).trans (congrArg _ e.property.2.1),
    (uibhbotFutureEdge_east k W _).trans (congrArg _ e.property.2.2)⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureToGlobal_length (k : ℤ) (W : ℤ → Fin 3)
    {a b : PresentVertex (fun i => uibhbotFutureCode k W (i + 1))}
    (p : Quiver.Path a b) : ((uibhbotFutureToGlobal k W).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
@[expose] def uibhbotPathEdges {W : ℤ → Fin 3} {a : UIBHBOTPresentVertex W} :
    {b : UIBHBOTPresentVertex W} → Quiver.Path a b → List (WholePlaneEdge W)
  | _, .nil => []
  | _, .cons p e => uibhbotPathEdges p ++ [e.val]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem path_future_times (W : ℤ → Fin 3) (k : ℤ)
    (hhit : UIBHBOTBoundaryHit k (uibhbotBoundaryHitTime k W) W)
    {a b : UIBHBOTPresentVertex W} (p : Quiver.Path a b)
    (ha : a.id = uibhbotFutureVertex k W 0) :
    ∀ e ∈ uibhbotPathEdges p, ∃ t : ℤ, uibhbotBoundaryHitTime k W ≤ t ∧
      uibhbotAbsoluteActiveEdge W t = e := by
  induction p with
  | nil => simp only [uibhbotPathEdges, List.not_mem_nil, false_implies, implies_true]
  | @cons a b p f ih =>
    obtain ⟨t, ht⟩ := present_absoluteActive W f.val f.property.1
    have htime : uibhbotBoundaryHitTime k W ≤ t := by
      cases p with
      | nil =>
        by_contra hn
        have hw : lemma38StartVertexι W t 0 =
            lemma38StartVertexι W (uibhbotBoundaryHitTime k W) 0 :=
          (absoluteActive_west W t).symm.trans
            ((congrArg (wholePlaneEdgeWest W) ht).trans (f.property.2.1.trans ha))
        have hlevel := startVertex_level W t (uibhbotBoundaryHitTime k W) hw
        exact hhit.2 t (by omega) (hlevel.trans hhit.1)
      | cons q g =>
        obtain ⟨s, hs, hsg⟩ := ih g.val
          (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hcon := absoluteActive_consecutive W s t (by
          rw [hsg, ht]
          exact g.property.2.2.trans f.property.2.1.symm)
        omega
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih e he
    · have hef := List.mem_singleton.mp he
      exact ⟨t, htime, ht.trans hef.symm⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
belongs to the directed future carrier. No incoming missing edge is oriented. -/
theorem ae_uibhbot_paths_from_boundary_in_future :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ b : UIBHBOTPresentVertex W,
        ∀ p : Quiver.Path (⟨uibhbotFutureVertex k W 0⟩ : UIBHBOTPresentVertex W) b,
          ∀ e ∈ uibhbotPathEdges p, e ∈ (uibhbotFutureEdge k W) ''
            {f | EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f} := by
  filter_upwards [ae_uibhbotBoundaryHit] with W hW k b p e he
  rw [uibhbotFuture_presentEdge_image]
  exact path_future_times W k (hW k) p rfl e he

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
private theorem future_path_lift (k : ℤ) (W : ℤ → Fin 3)
    {a : PresentVertex (fun i => uibhbotFutureCode k W (i + 1))}
    {b : UIBHBOTPresentVertex W} (p : Quiver.Path ((uibhbotFutureToGlobal k W).obj a) b)
    (hE : ∀ e ∈ uibhbotPathEdges p, ∃ f,
      EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f ∧
        uibhbotFutureEdge k W f = e) :
    ∃ c, ∃ q : Quiver.Path a c, (uibhbotFutureToGlobal k W).obj c = b ∧
      uibhbotPathEdges p = (pathEdgeList q).map (uibhbotFutureEdge k W) ∧
        q.length = p.length := by
  induction p with
  | nil => exact ⟨a, .nil, rfl, rfl, rfl⟩
  | @cons x y p e ih =>
    obtain ⟨c, q, hc, hq, hlen⟩ := ih (fun f hf =>
      hE f (List.mem_append_left _ hf))
    obtain ⟨f, hf, hfe⟩ := hE e.val
      (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    let z : PresentVertex (fun i => uibhbotFutureCode k W (i + 1)) :=
      ⟨edgeEast (fun i => uibhbotFutureCode k W (i + 1)) f⟩
    have hw : edgeWest (fun i => uibhbotFutureCode k W (i + 1)) f = c.id := by
      apply uibhbotFutureVertex_injective k W
      exact (uibhbotFutureEdge_west k W f).symm.trans
        ((congrArg (wholePlaneEdgeWest W) hfe).trans
          (e.property.2.1.trans (congrArg UIBHBOTPresentVertex.id hc).symm))
    let ef : c ⟶ z := ⟨f, hf, hw, rfl⟩
    refine ⟨z, q.cons ef, ?_, ?_, ?_⟩
    · apply congrArg UIBHBOTPresentVertex.mk
      exact (uibhbotFutureEdge_east k W f).symm.trans
        ((congrArg (wholePlaneEdgeEast W) hfe).trans e.property.2.2)
    · simp only [uibhbotPathEdges, pathEdgeList, List.map_append, List.map_singleton]
      rw [hq]
      exact congrArg (fun l => (pathEdgeList q).map (uibhbotFutureEdge k W) ++ l)
        (congrArg List.singleton hfe.symm)
    · simp only [Quiver.Path.length_cons, hlen]

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
`ℓ ≤ k`, lifts into the future carrier, with the same ordered geometric edge IDs and length.
The start is supplied as its future-carrier representative, not as an additional path premise. -/
theorem ae_uibhbotFuture_boundary_path_lift :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ j : ℤ, j ≤ 0 → ∀ b : UIBHBOTPresentVertex W,
          ∀ p : Quiver.Path ((uibhbotFutureToGlobal k W).obj
            (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩)) b,
              ∃ c, ∃ q : Quiver.Path
                (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ :
                  PresentVertex (fun i => uibhbotFutureCode k W (i + 1))) c,
                (uibhbotFutureToGlobal k W).obj c = b ∧
                  uibhbotPathEdges p = (pathEdgeList q).map (uibhbotFutureEdge k W) ∧
                    q.length = p.length := by
  filter_upwards [ae_uibhbotBoundaryHit, ae_uibhbotBoundaryHit_strictRecord,
    ae_uibhbotFutureBoundary_index] with W hh hr hi k h j hj b p
  apply future_path_lift k W p
  intro e he
  have ha := path_future_times W (k + j) (hh (k + j)) p (hi k h j hj) e he
  obtain ⟨t, ht, hte⟩ := ha
  have htime : uibhbotBoundaryHitTime k W ≤ uibhbotBoundaryHitTime (k + j) W := by
    by_contra hn
    have hbad := hr k (uibhbotBoundaryHitTime (k + j) W) (by omega)
    rw [(hh (k + j)).1] at hbad
    omega
  have hm : e ∈ (uibhbotFutureEdge k W) ''
      {f | EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f} := by
    rw [uibhbotFuture_presentEdge_image]
    exact ⟨t, htime.trans ht, hte⟩
  obtain ⟨f, hf, hfe⟩ := hm
  exact ⟨f, hf, hfe⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureToGlobal_obj_injective (k : ℤ) (W : ℤ → Fin 3) :
    Function.Injective (uibhbotFutureToGlobal k W).obj := by
  intro a b hab
  have hi := uibhbotFutureVertex_injective k W (congrArg UIBHBOTPresentVertex.id hab)
  cases a
  cases b
  cases hi
  rfl

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem uibhbotFutureToGlobal_pathEdges (k : ℤ) (W : ℤ → Fin 3)
    {a b : PresentVertex (fun i => uibhbotFutureCode k W (i + 1))}
    (p : Quiver.Path a b) :
    uibhbotPathEdges ((uibhbotFutureToGlobal k W).mapPath p) =
      (pathEdgeList p).map (uibhbotFutureEdge k W) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, uibhbotPathEdges, pathEdgeList,
      List.map_append, List.map_singleton, ih]
    rfl

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
from any future boundary index `j ≤ 0` to every vertex of the future carrier. -/
theorem ae_uibhbotFuture_boundary_pathSets :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ j : ℤ, j ≤ 0 →
          ∀ b : PresentVertex (fun i => uibhbotFutureCode k W (i + 1)),
            Set.range (fun p : Quiver.Path ((uibhbotFutureToGlobal k W).obj
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩))
              ((uibhbotFutureToGlobal k W).obj b) => uibhbotPathEdges p) =
            Set.range (fun q : Quiver.Path
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ :
                PresentVertex (fun i => uibhbotFutureCode k W (i + 1))) b =>
                  (pathEdgeList q).map (uibhbotFutureEdge k W)) := by
  filter_upwards [ae_uibhbotFuture_boundary_path_lift] with W hW k h j hj b
  ext es
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨c, q, hc, hq, _⟩ := hW k h j hj _ p
    have hcb := uibhbotFutureToGlobal_obj_injective k W hc
    subst c
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(uibhbotFutureToGlobal k W).mapPath q,
      uibhbotFutureToGlobal_pathEdges k W q⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result. -/
theorem ae_uibhbotFuture_boundary_pathLengths :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ j : ℤ, j ≤ 0 →
          ∀ b : PresentVertex (fun i => uibhbotFutureCode k W (i + 1)),
            pathLengths ((uibhbotFutureToGlobal k W).obj
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩))
              ((uibhbotFutureToGlobal k W).obj b) =
            pathLengths
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ :
                PresentVertex (fun i => uibhbotFutureCode k W (i + 1))) b := by
  filter_upwards [ae_uibhbotFuture_boundary_path_lift] with W hW k h j hj b
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨c, q, hc, _, hlen⟩ := hW k h j hj _ p
    have hcb := uibhbotFutureToGlobal_obj_injective k W hc
    subst c
    exact ⟨q, hlen⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(uibhbotFutureToGlobal k W).mapPath q, uibhbotFutureToGlobal_length k W q⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
pairs and top for unbounded lengths. Finite values require attainment, proved separately. -/
@[expose] noncomputable def uibhbotLdp {W : ℤ → Fin 3}
    (a b : UIBHBOTPresentVertex W) : WithBot ℕ∞ :=
  ⨆ p : Quiver.Path a b, ((p.length : ℕ∞) : WithBot ℕ∞)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
in particular it may be any other future boundary vertex. -/
theorem ae_uibhbotFuture_boundary_ldp :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ j : ℤ, j ≤ 0 →
          ∀ b : PresentVertex (fun i => uibhbotFutureCode k W (i + 1)),
            uibhbotLdp ((uibhbotFutureToGlobal k W).obj
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩))
              ((uibhbotFutureToGlobal k W).obj b) =
            presentLdp
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ :
                PresentVertex (fun i => uibhbotFutureCode k W (i + 1))) b := by
  filter_upwards [ae_uibhbotFuture_boundary_pathLengths] with W hW k h j hj b
  have heq := hW k h j hj b
  unfold uibhbotLdp presentLdp
  apply le_antisymm
  · apply iSup_le
    intro p
    have hn : p.length ∈ pathLengths
        (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ :
          PresentVertex (fun i => uibhbotFutureCode k W (i + 1))) b := by
      rw [← heq]
      exact ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hn
    rw [← hq]
    exact le_iSup (fun r : Quiver.Path _ _ =>
      ((r.length : ℕ∞) : WithBot ℕ∞)) q
  · apply iSup_le
    intro q
    rw [← uibhbotFutureToGlobal_length k W q]
    exact le_iSup (fun r : Quiver.Path _ _ =>
      ((r.length : ℕ∞) : WithBot ℕ∞)) ((uibhbotFutureToGlobal k W).mapPath q)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
allocation time, simultaneously over all boundary starts. -/
theorem ae_uibhbotFuture_vertex_allocated :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ, ∀ v : ℕ,
      ∃ n, v < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextVertex := by
  apply ae_all_iff.mpr
  intro k
  have h := iidCodes_ae_finite_incident_edges
  rw [← uibhbotFutureCode_law k] at h
  have he := ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h
  filter_upwards [he] with W hW v
  exact kmsw_vertex_allocated_of_finite_incidence _ hW v

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
finite suffix allocations. Together with the edge image and endpoint equations this identifies
the incidence submap, without asserting its embedded face structure. -/
theorem ae_uibhbotFuture_vertex_image :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      Set.range (uibhbotFutureVertex k W) = {v | ∃ n a,
        a < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextVertex ∧
          uibhbotFutureVertex k W a = v} := by
  filter_upwards [ae_uibhbotFuture_vertex_allocated] with W hW k
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨n, hn⟩ := hW k a
    exact ⟨n, a, hn, rfl⟩
  · rintro ⟨_, a, _, ha⟩
    exact ⟨a, ha⟩

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
lengths, so reachable pairs have finite LDP before any subtraction is considered. -/
theorem ae_uibhbotFuture_boundary_ldp_finite :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ j : ℤ, j ≤ 0 →
          ∀ b : PresentVertex (fun i => uibhbotFutureCode k W (i + 1)),
            BddAbove (pathLengths ((uibhbotFutureToGlobal k W).obj
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩))
              ((uibhbotFutureToGlobal k W).obj b)) ∧
            (Reachable ((uibhbotFutureToGlobal k W).obj
              (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩))
              ((uibhbotFutureToGlobal k W).obj b) →
                ∃ n : ℕ, uibhbotLdp ((uibhbotFutureToGlobal k W).obj
                  (⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩))
                  ((uibhbotFutureToGlobal k W).obj b) = ((n : ℕ∞) : WithBot ℕ∞)) := by
  have hall : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ a b : PresentVertex (fun i => uibhbotFutureCode k W (i + 1)),
        BddAbove (pathLengths a b) ∧
          (Reachable a b → ∃ n : ℕ, presentLdp a b = ((n : ℕ∞) : WithBot ℕ∞)) := by
    apply ae_all_iff.mpr
    intro k
    have h := iidCodes_ae_paths_finite_bounded_attained
    rw [← uibhbotFutureCode_law k] at h
    have he := ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h
    filter_upwards [he] with W hW a b
    exact ⟨(hW a b).2.1, fun hr => by
      obtain ⟨p, _, hp⟩ := (hW a b).2.2 hr
      exact ⟨p.length, hp⟩⟩
  filter_upwards [hall, ae_uibhbotFuture_boundary_pathLengths,
    ae_uibhbotFuture_boundary_ldp] with W hW hl hd k h j hj b
  let a : PresentVertex (fun i => uibhbotFutureCode k W (i + 1)) :=
    ⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩
  constructor
  · rw [hl k h j hj b]
    exact (hW k a b).1
  · rintro ⟨p⟩
    have hp : p.length ∈ pathLengths a b := by
      rw [← hl k h j hj b]
      exact ⟨p, rfl⟩
    obtain ⟨q, _⟩ := hp
    obtain ⟨n, hn⟩ := (hW k a b).2 ⟨q⟩
    exact ⟨n, (hd k h j hj b).trans hn⟩



@[expose] def UIBHBOTFutureMissingEdgeReflectionAlmostSure : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ, ∀ e : ℕ,
    ¬ EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) e →
      ¬ wholePlaneEdgePresent W (uibhbotFutureEdge k W e)

/-- Helper toward Proposition 5.11 (prop-busemann-uihbot) and Theorem 1.7(iv); not a paper result.
Outer-face successors are excluded since a submap's outer face need not be an ambient face.
This obligation is never assumed by any theorem in this file. -/
@[expose] def UIBHBOTFutureInteriorFaceCompatibilityAlmostSure : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
    ∀ H : WholePlaneRotationHypothesis W,
      ∀ hfin : ∀ v : ℕ,
        {e : ℕ | ∃ n, e < (kmswStage
          (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
            (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite,
        ∀ d : ℕ × Bool,
          ¬ limitExternalDart (fun i => uibhbotFutureCode k W (i + 1)) d →
            wholePlaneFaceSucc W H (uibhbotFutureEdge k W d.1, d.2) =
              (uibhbotFutureEdge k W
                (kmswInfFaceSucc (fun i => uibhbotFutureCode k W (i + 1)) hfin d).1,
                  (kmswInfFaceSucc (fun i => uibhbotFutureCode k W (i + 1)) hfin d).2)

end DirectedDistances.RandomWalk
