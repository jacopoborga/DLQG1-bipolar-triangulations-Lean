module

public import DirectedDistances.KMSW.WholePlaneRightmostDescent
public import DirectedDistances.KMSW.WholePlaneRightmostRays
import DirectedDistances.KMSW.KMSWWindowPatchInjective

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open scoped Classical

private def value {n : ℕ} (d : StageDart n) : ℕ × Bool := (d.1.val, d.2)

private theorem value_injective (n : ℕ) : Function.Injective (@value n) := by
  intro a b h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (congrArg (fun z : ℕ × Bool => z.2) h)

private theorem symm_endpoint (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) :
    stageEndpoint (kmswStage w m) ((stageRot w m).symm d) =
      stageEndpoint (kmswStage w m) d := by
  exact (stageRot_sameCycle_iff_endpoint_eq w m _ _).mp
    ⟨1, (stageRot w m).apply_symm_apply d⟩

private theorem symm_pow_endpoint (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) (k : ℕ) :
    stageEndpoint (kmswStage w m) (((stageRot w m).symm ^ k) d) =
      stageEndpoint (kmswStage w m) d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, symm_endpoint, ih]

private def base (u : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast u d.1 else edgeWest u d.1

private theorem stage_base (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage u m).nextEdge) :
    stageEndpoint (kmswStage u m) d = base u (value d) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq u d.1.isLt
  cases hb : d.2 <;> simp only [stageEndpoint, base, value, hb,
    Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem complete_exists (u : ℕ → Fin 3) (hfin : KMSWFiniteIncidence u)
    (v : ℕ) : ∃ m, kmswVertexComplete u m v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  exact (hB ⟨e, kmsw_edge_allocated_by_self u e, he⟩).trans_lt
    (kmsw_edge_allocated_by_self u B)

private theorem complete_mono (u : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (hc : kmswVertexComplete u n v) : kmswVertexComplete u m v := by
  intro e he
  exact (hc e he).trans_le (kmswStage_nextEdge_mono u hnm)

private theorem inf_pow_stage (u : ℕ → Fin 3) (hfin : KMSWFiniteIncidence u)
    (m : ℕ) (d : StageDart (kmswStage u m).nextEdge)
    (hc : kmswVertexComplete u m (stageEndpoint (kmswStage u m) d)) (k : ℕ) :
    ((kmswInfRot u hfin).symm ^ k) (value d) =
      value (((stageRot u m).symm ^ k) d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact kmswInfRot_symm_eq_stage u hfin m _ (by
      rw [symm_pow_endpoint]
      exact hc)

private theorem active_present (w : ℕ → Fin 3) (m : ℕ) :
    (kmswStage w m).present (act w m) = true := by
  apply (kmswStage_status w m).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem window_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem trans_act (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    window_act (shiftedStream W M) (M - N) k

private theorem active_terminal_outgoing_lift (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N t : ℕ) (e : WholePlaneEdge W)
    (hp : wholePlaneEdgePresent W e)
    (hw : wholePlaneEdgeWest W e = wholePlaneVertexι W N
      (edgeEast (shiftedStream W N) (act (shiftedStream W N) t))) :
    ∃ f : ℕ, EdgePresent (shiftedStream W N) f ∧
      edgeWest (shiftedStream W N) f =
        edgeEast (shiftedStream W N) (act (shiftedStream W N) t) ∧ wholePlaneEdgeι W N f = e := by
  let v := edgeEast (shiftedStream W N) (act (shiftedStream W N) t)
  change wholePlaneEdgeWest W e = wholePlaneVertexι W N v at hw

  obtain ⟨⟨K, g⟩, he⟩ := Quotient.exists_rep e
  change wholePlaneEdgeι W K g = e at he
  obtain ⟨A, hKA, hA⟩ := wholePlaneEdgePresent_eventually W H K g
  let M := max N A
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hAM : A ≤ M := Nat.le_max_right _ _
  let f := wholePlaneEdgeTrans W K M (hKA.trans hAM) g
  have hfp : EdgePresent (shiftedStream W M) f :=
    (hA M hAM).mpr (he.symm ▸ hp)
  have hfι : wholePlaneEdgeι W M f = e :=
    (congrFun (wholePlaneEdgeι_trans W K M (hKA.trans hAM)) g).trans he
  have hfw : wholePlaneEdgeWest W (wholePlaneEdgeι W M f) =
      wholePlaneVertexι W N v := hfι ▸ hw
  obtain ⟨n, hft, hpt⟩ := hfp
  obtain ⟨m, _, hfm⟩ := stagePresent_exists_active (shiftedStream W M) n f hft hpt
  have hmb : f < (kmswStage (shiftedStream W M) m).nextEdge := by
    rw [hfm]
    exact act_lt_nextEdge _ le_rfl
  have hmp : (kmswStage (shiftedStream W M) m).present f = true := by
    rw [hfm]
    exact active_present _ _
  have hs : M - N ≤ m := by
    by_contra hn
    have hms : m ≤ M - N + t := by omega
    obtain ⟨hb, hpast⟩ := present_mono (shiftedStream W M) hmb hmp (M - N + t) hms
    have hfront := stageOutgoing_active_east_empty (shiftedStream W M) (M - N + t)
      (⟨⟨f, hb⟩, false⟩) ⟨rfl, hpast⟩
    apply hfront
    change (kmswStage (shiftedStream W M) (M - N + t)).west f = _
    rw [(edge_endpoints_eq (shiftedStream W M) hb).1]
    have hv : edgeWest (shiftedStream W M) f = wholePlaneVertexTrans W N M hNM v := by
      apply wholePlaneVertexι_injective W M
      rw [← wholePlaneEdgeWest_ι]
      exact hfw.trans (congrFun (wholePlaneVertexι_trans W N M hNM) v).symm
    rw [hv]
    have ht := trans_act W N M hNM t
    have he := wholePlaneEdgeTrans_east W N M hNM (act (shiftedStream W N) t)
    rw [ht] at he
    exact he.symm.trans
      (edge_endpoints_eq (shiftedStream W M) (act_lt_nextEdge _ le_rfl)).2.symm
  let q := act (shiftedStream W N) (m - (M - N))
  have hq : wholePlaneEdgeTrans W N M hNM q = f := by
    dsimp only [q]
    rw [trans_act, show M - N + (m - (M - N)) = m by omega]
    exact hfm.symm
  have hv : edgeWest (shiftedStream W M) f = wholePlaneVertexTrans W N M hNM v := by
    apply wholePlaneVertexι_injective W M
    rw [← wholePlaneEdgeWest_ι]
    exact hfw.trans (congrFun (wholePlaneVertexι_trans W N M hNM) v).symm
  have hqw : edgeWest (shiftedStream W N) q = v := by
    apply wholePlaneVertexTrans_injective W N M hNM
    rw [← wholePlaneEdgeTrans_west, hq, hv]
  refine ⟨q, ⟨m - (M - N), act_lt_nextEdge _ le_rfl, active_present _ _⟩, hqw, ?_⟩
  calc
    wholePlaneEdgeι W N q =
        wholePlaneEdgeι W M (wholePlaneEdgeTrans W N M hNM q) :=
      (congrFun (wholePlaneEdgeι_trans W N M hNM) q).symm
    _ = e := by rw [hq]; exact hfι

private def ambientBase (W : ℤ → Fin 3) (d : WholePlaneDart W) : WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1

private theorem base_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    ambientBase W (wholePlaneDartι W N d) =
      wholePlaneVertexι W N (base (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [ambientBase, base, wholePlaneDartι, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeWest_ι W N d.1
  · exact wholePlaneEdgeEast_ι W N d.1

private theorem symm_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) :
    base w ((kmswInfRot w hfin).symm d) = base w d := by
  obtain ⟨n, hn⟩ := kmswInfRot_symm_eventually_eq_stage w hfin d
  obtain ⟨hd, he⟩ := hn n le_rfl
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  have hb (z : StageDart (kmswStage w n).nextEdge) :
      stageEndpoint (kmswStage w n) z = base w (z.1.val, z.2) := by
    obtain ⟨hw, he⟩ := edge_endpoints_eq w z.1.isLt
    cases hs : z.2 <;> simp only [stageEndpoint, base, hs,
      Bool.false_eq_true, ↓reduceIte, hw, he]
  have hr := ((stageRot_sameCycle_iff_endpoint_eq w n
    ((stageRot w n).symm x) x).mp
      ⟨1, (stageRot w n).apply_symm_apply x⟩)
  rw [he, ← hb ((stageRot w n).symm x), ← hb x]
  exact hr

private theorem symm_pow_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    base w (((kmswInfRot w hfin).symm ^ k) d) = base w d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, symm_base, ih]

private theorem ambient_symm_pow_base (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) (k : ℕ) :
    ambientBase W (((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N d)) =
      ambientBase W (wholePlaneDartι W N d) := by
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N d
  rw [hpow k, base_ι, symm_pow_base, ← base_ι]
  exact congrArg (ambientBase W) (congrFun (wholePlaneDartι_trans W N M hNM) d)

private def windowDart (w : ℕ → Fin 3) (s : ℕ) (d : ℕ × Bool) : ℕ × Bool :=
  (kmswWindowEdgeMapInf w s d.1, d.2)

private theorem window_base (w : ℕ → Fin 3) (s : ℕ) (d : ℕ × Bool) :
    base w (windowDart w s d) =
      kmswWindowVertexMapInf w s (base (fun i => w (s + i)) d) := by
  let u := fun i => w (s + i)
  have he := kmsw_edge_allocated_by_self u d.1
  have hb := (kmswWindowPatchData_rel w s d.1).edge_bound d.1 he
  rw [← kmswWindowEdgeMapInf_eq_stage w s d.1 d.1 he] at hb
  obtain ⟨hw, ht⟩ := edge_endpoints_eq u he
  obtain ⟨hw', ht'⟩ := edge_endpoints_eq w hb
  cases hs : d.2
  · simp only [base, windowDart, hs, Bool.false_eq_true, ↓reduceIte]
    change edgeWest w (kmswWindowEdgeMapInf w s d.1) =
      kmswWindowVertexMapInf w s (edgeWest u d.1)
    rw [← hw', ← hw]
    exact kmswWindowEdgeMapInf_west w s d.1 d.1 he
  · simp only [base, windowDart, hs, ↓reduceIte]
    change edgeEast w (kmswWindowEdgeMapInf w s d.1) =
      kmswWindowVertexMapInf w s (edgeEast u d.1)
    rw [← ht', ← ht]
    exact kmswWindowEdgeMapInf_east w s d.1 d.1 he

private theorem shift_finite (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w) (s : ℕ) :
    KMSWFiniteIncidence (fun i => w (s + i)) := by
  intro v
  let u := fun i => w (s + i)
  apply Set.Finite.subset
    (Set.Finite.preimage (kmswWindowEdgeMapInf_injective w s).injOn
      (hfin (kmswWindowVertexMapInf w s v)))
  rintro e ⟨n, he, hw | ht⟩
  · refine ⟨s + n, ?_, Or.inl ?_⟩
    · rw [kmswWindowEdgeMapInf_eq_stage w s n e he]
      exact (kmswWindowPatchData_rel w s n).edge_bound e he
    · rw [kmswWindowEdgeMapInf_west w s n e he, hw]
  · refine ⟨s + n, ?_, Or.inr ?_⟩
    · rw [kmswWindowEdgeMapInf_eq_stage w s n e he]
      exact (kmswWindowPatchData_rel w s n).edge_bound e he
    · rw [kmswWindowEdgeMapInf_east w s n e he, ht]

private theorem window_firstReturn (w : ℕ → Fin 3) (s : ℕ)
    (hw : KMSWFiniteIncidence w) (d : ℕ × Bool)
    (hd : base (fun i => w (s + i)) d = 1) :
    ∃ k : ℕ, 0 < k ∧
      ((kmswInfRot w hw).symm ^ k) (windowDart w s d) =
        windowDart w s ((kmswInfRot (fun i => w (s + i)) (shift_finite w hw s)).symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswInfRot w hw).symm ^ j) (windowDart w s d) ∉
          Set.range (windowDart w s) := by
  let u := fun i => w (s + i)
  let hu := shift_finite w hw s
  let I := windowDart w s
  obtain ⟨n, hn⟩ := complete_exists u hu 1
  obtain ⟨q, hq⟩ := complete_exists w hw (kmswWindowVertexMapInf w s 1)
  let m := max n (max q d.1)
  have hnm : n ≤ m := Nat.le_max_left _ _
  have hqm : q ≤ s + m := by
    have := (Nat.le_max_left q d.1).trans (Nat.le_max_right n (max q d.1))
    omega
  have hdm : d.1 ≤ m :=
    (Nat.le_max_right q d.1).trans (Nat.le_max_right n (max q d.1))
  have hcs := complete_mono u hnm hn
  have hcw := complete_mono w hqm hq
  have halloc : d.1 < (kmswStage u m).nextEdge :=
    (kmsw_edge_allocated_by_self u d.1).trans_le (kmswStage_nextEdge_mono u hdm)
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, halloc⟩, d.2)
  let y := kmswWindowDartMap w s m x
  have hmap (z : StageDart (kmswStage u m).nextEdge) :
      value (kmswWindowDartMap w s m z) = I (value z) := by
    apply Prod.ext
    · exact (kmswWindowEdgeMapInf_eq_stage w s m z.1.val z.1.isLt).symm
    · rfl
  have hx : stageEndpoint (kmswStage u m) x = 1 := (stage_base u m x).trans hd
  have hcx : kmswVertexComplete u m (stageEndpoint (kmswStage u m) x) := hx ▸ hcs
  have hy : value y = I d := hmap x
  have hybase : stageEndpoint (kmswStage w (s + m)) y =
      kmswWindowVertexMapInf w s 1 := by
    rw [stage_base, hy, window_base, hd]
  have hcy : kmswVertexComplete w (s + m) (stageEndpoint (kmswStage w (s + m)) y) := by
    rw [hybase]
    exact hcw
  have hiter (j : ℕ) : ((kmswInfRot w hw).symm ^ j) (I d) =
      value (((stageRot w (s + m)).symm ^ j) y) := by
    rw [← hy]
    exact inf_pow_stage w hw (s + m) y hcy j
  obtain ⟨k, hk, hreturn, hgap⟩ :=
    kmswWindowDartMap_symm_firstReturn_at_one w s m x hx
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hiter, hreturn, hmap]
    exact congrArg I (kmswInfRot_symm_eq_stage u hu m x hcx).symm
  · intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    have hep : base w (I e) = base w (I d) := by
      calc
        base w (I e) = base w (value (((stageRot w (s + m)).symm ^ j) y)) :=
          congrArg (base w) (he.trans (hiter j))
        _ = stageEndpoint (kmswStage w (s + m))
            (((stageRot w (s + m)).symm ^ j) y) := (stage_base w _ _).symm
        _ = stageEndpoint (kmswStage w (s + m)) y := symm_pow_endpoint w _ y j
        _ = base w (I d) := (stage_base w _ y).trans (congrArg (base w) hy)
    have heone : base u e = 1 := by
      rw [window_base, window_base] at hep
      exact (kmswWindowVertexMapInf_injective w s hep).trans hd
    have heb : e.1 < (kmswStage u m).nextEdge := by
      apply hcs e.1
      cases hb : e.2
      · exact Or.inl (by simpa only [base, hb, Bool.false_eq_true, ↓reduceIte] using heone)
      · exact Or.inr (by simpa only [base, hb, ↓reduceIte] using heone)
    let z : StageDart (kmswStage u m).nextEdge := (⟨e.1, heb⟩, e.2)
    apply hgap j hj hjk
    refine ⟨z, value_injective _ ?_⟩
    exact (hmap z).trans (he.trans (hiter j))

private theorem R_shift_add (w : ℕ → Fin 3) (t n : ℕ) :
    R w (t + n) = R w t + R (fun i => w (t + i)) n := by
  induction n with
  | zero => simp [R]
  | succ n ih =>
    have hg : R w (t + n + 1) = R w (t + n) +
        (RandomWalk.lazyTwoDimensionalStep (w (t + n))).2 :=
      Finset.sum_range_succ _ _
    have hs : R (fun i => w (t + i)) (n + 1) =
        R (fun i => w (t + i)) n +
          (RandomWalk.lazyTwoDimensionalStep (w (t + n))).2 :=
      Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hs, ih]
    omega

private theorem shift_unbounded (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ) :
    ∀ a : ℤ, ∃ n, R (fun i => w (t + i)) n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := hR (min (a + R w t) (minR w t - 1))
  have htn : t ≤ n := by
    by_contra h
    have hh := runningMin_le (R w) t n (by omega)
    change minR w t ≤ R w n at hh
    have := min_le_right (a + R w t) (minR w t - 1)
    omega
  refine ⟨n - t, ?_⟩
  have hh := R_shift_add w t (n - t)
  rw [Nat.add_sub_of_le htn] at hh
  have := min_le_left (a + R w t) (minR w t - 1)
  omega

private theorem first_record_corner (u : ℕ → Fin 3) (hf : KMSWFiniteIncidence u)
    (hR : ∀ a : ℤ, ∃ n, R u n ≤ a) (d : ℕ) (hd : 0 < d)
    (hdrop : R u d = -1) (hgap : ∀ j, 0 < j → j < d → -1 < R u j) :
    (kmswInfRot u hf).symm (act u d, false) = (0, true) := by
  let P := fun m => ∀ j, j < m → R u m < R u j
  have hzero : R u 0 = 0 := by simp [R]
  have hPd : P d := by
    intro j hj
    rw [hdrop]
    by_cases hj0 : j = 0
    · rw [hj0, hzero]
      omega
    · exact hgap j (by omega) hj
  have hcount : Nat.count P d = 1 := by
    rw [Nat.count_eq_card_filter_range]
    have heq : Finset.filter P (Finset.range d) = {0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hp⟩
        by_contra hn
        have h1 := hp 0 (by omega)
        have h2 := hgap j (by omega) hj
        rw [hzero] at h1
        omega
      · rintro rfl
        exact ⟨hd, fun j hj => (Nat.not_lt_zero j hj).elim⟩
    rw [heq]
    simp
  have hselect := natSelect_count hPd
  rw [hcount] at hselect
  have he : kmswRightBoundaryEdge u 1 = act u d := by
    unfold kmswRightBoundaryEdge
    exact congrArg (act u) hselect
  have hh := kmswInfFaceSucc_right_of_unbounded_below u hf hR 0
  change (kmswInfRot u hf).symm (kmswRightBoundaryEdge u 1, false) =
    (kmswRightBoundaryEdge u 0, true) at hh
  simpa only [he, kmswRightBoundaryEdge_zero] using hh

private theorem window_root (w : ℕ → Fin 3) (s : ℕ) :
    kmswWindowEdgeMapInf w s 0 = act w s := by
  simpa only [show act (fun i => w (s + i)) 0 = 0 from rfl, Nat.add_zero] using
    window_act w s 0

private theorem descent_rightmost (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N t d : ℕ)
    (hR : ∀ a : ℤ, ∃ n, R (fun i => shiftedStream W N (t + i)) n ≤ a)
    (hd : 0 < d) (hdrop : R (fun i => shiftedStream W N (t + i)) d = -1)
    (hgap : ∀ j, 0 < j → j < d → -1 < R (fun i => shiftedStream W N (t + i)) j)
    (hwest : edgeWest (shiftedStream W N) (act (shiftedStream W N) (t + d)) =
      edgeEast (shiftedStream W N) (act (shiftedStream W N) t)) :
    wholePlaneRightmostOutgoingAt W H
      (wholePlaneVertexι W N (edgeEast (shiftedStream W N) (act (shiftedStream W N) t)))
      (wholePlaneEdgeι W N (act (shiftedStream W N) (t + d))) := by
  let w := shiftedStream W N
  let u₀ := fun i => w (t + i)
  let e := act w (t + d)
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N (e, false)
  let wM := shiftedStream W M
  let s := M - N + t
  let u := fun i => wM (s + i)
  have hu : u = u₀ := by
    funext i
    have hh := congrFun (shiftedStream_shift W N M hNM) (t + i)
    simpa only [u, u₀, s, wM, w, Nat.add_assoc] using hh
  have hRu : ∀ a : ℤ, ∃ n, R u n ≤ a := by rw [hu]; exact hR
  have hdu : R u d = -1 := by rw [hu]; exact hdrop
  have hgu : ∀ j, 0 < j → j < d → -1 < R u j := by rw [hu]; exact hgap
  have hcorner := first_record_corner u (shift_finite wM (H.1 M) s) hRu d hd hdu hgu
  have hroot : edgeEast u (act u 0) = 1 := by
    rw [← (edge_endpoints_eq u (act_lt_nextEdge u (le_refl 0))).2]
    rfl
  have hlocal : base u (act u d, false) = 1 := by
    obtain ⟨q, hq, hqd, hqgap, hqw, _⟩ := kmswActiveTerminal_firstDescent u hRu 0
    have hqdrop : R u q = -1 := by
      rw [show R u 0 = 0 by simp [R]] at hqd
      omega
    have hqd' : q = d := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · have := hgu q hq hlt
        omega
      · have := hqgap d hd hgt
        simp only [show R u 0 = 0 by simp [R]] at this
        omega
    simpa only [base, Bool.false_eq_true, ↓reduceIte, hqd', hroot] using hqw
  obtain ⟨k, hk, hret, hmiss⟩ := window_firstReturn wM s (H.1 M) (act u d, false) hlocal
  rw [hcorner] at hret
  have hstart : windowDart wM s (act u d, false) =
      wholePlaneDartTrans W N M hNM (e, false) := by
    apply Prod.ext
    · change kmswWindowEdgeMapInf wM s (act u d) = wholePlaneEdgeTrans W N M hNM e
      rw [window_act, show e = act w (t + d) from rfl, trans_act]
      congr 1
      omega
    · rfl
  have hend : windowDart wM s (0, true) = (act wM s, true) :=
    Prod.ext (window_root wM s) rfl
  rw [hstart, hend] at hret
  rw [hstart] at hmiss
  have hambret : ((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N (e, false)) =
      wholePlaneDartι W M (act wM s, true) := by
    rw [hpow k, hret]
  let Q := fun j : ℕ => 0 < j ∧ wholePlaneEdgePresent W
    (((wholePlaneRotation W H).symm ^ j) (wholePlaneDartι W N (e, false))).1
  have hex : ∃ j, Q j := ⟨k, hk, by
    rw [hambret]
    exact wholePlaneEdgePresent_ι_of_run_present W M _
      ⟨s, act_lt_nextEdge wM le_rfl, active_present wM s⟩⟩
  let m := Nat.find hex
  have hm : Q m := Nat.find_spec hex
  have hmk : m ≤ k := Nat.find_min' hex (by
    refine ⟨hk, ?_⟩
    rw [hambret]
    exact wholePlaneEdgePresent_ι_of_run_present W M _
      ⟨s, act_lt_nextEdge wM le_rfl, active_present wM s⟩)
  have hv : wholePlaneVertexι W M (edgeEast wM (act wM s)) =
      wholePlaneVertexι W N (edgeEast w (act w t)) := by
    have hh := wholePlaneEdgeTrans_east W N M hNM (act w t)
    rw [trans_act] at hh
    exact (congrArg (wholePlaneVertexι W M) hh).trans
      (congrFun (wholePlaneVertexι_trans W N M hNM) _)
  have hside : (((wholePlaneRotation W H).symm ^ m)
      (wholePlaneDartι W N (e, false))).2 = true := by
    by_cases heq : m = k
    · rw [heq, hambret]
      rfl
    · let z := ((wholePlaneRotation W H).symm ^ m) (wholePlaneDartι W N (e, false))
      have hb := ambient_symm_pow_base W H N (e, false) m
      have hzw : z.2 = false → wholePlaneEdgeWest W z.1 =
          wholePlaneVertexι W M (edgeEast wM (act wM s)) := by
        intro hz
        change ambientBase W z = _ at hb
        rw [hv]
        simpa only [ambientBase, hz, wholePlaneDartι, Bool.false_eq_true,
          ↓reduceIte, wholePlaneEdgeWest_ι, e, w, hwest] using hb
      cases hs : z.2 with
      | true => rfl
      | false =>
        obtain ⟨f, hfp, hfw, hfι⟩ := active_terminal_outgoing_lift W H M s z.1
          hm.2 (hzw hs)
        obtain ⟨q, hsq, hfq, _⟩ := (kmswActiveTerminal_outgoing_iff wM s f).mp ⟨hfp, hfw⟩
        have himage : windowDart wM s (act u (q - s), false) = (f, false) := by
          apply Prod.ext
          · change kmswWindowEdgeMapInf wM s (act u (q - s)) = f
            rw [window_act, Nat.add_sub_of_le hsq.le, ← hfq]
          · rfl
        apply False.elim
        apply hmiss m hm.1 (by omega)
        refine ⟨(act u (q - s), false), ?_⟩
        apply Prod.ext
        · apply wholePlaneEdgeι_injective W M
          have hz := congrArg Prod.fst (hpow m)
          change z.1 = wholePlaneEdgeι W M
            (((kmswInfRot wM (H.1 M)).symm ^ m)
              (wholePlaneDartTrans W N M hNM (e, false))).1 at hz
          exact (congrArg (wholePlaneEdgeι W M) (congrArg Prod.fst himage)).trans
            (hfι.trans hz)
        · have hz := congrArg Prod.snd (hpow m)
          change z.2 = (((kmswInfRot wM (H.1 M)).symm ^ m)
            (wholePlaneDartTrans W N M hNM (e, false))).2 at hz
          exact hs.symm.trans hz
  refine ⟨wholePlaneEdgePresent_ι_of_run_present W N e
    ⟨t + d, act_lt_nextEdge w le_rfl, active_present w (t + d)⟩, ?_,
    m, hm.1, hside, hm.2, ?_⟩
  · rw [wholePlaneEdgeWest_ι, hwest]
  · intro j hj hjm hpj
    exact Nat.find_min hex hjm ⟨hj, hpj⟩




theorem wholePlaneRightmost_descent_at_active (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a) (t : ℕ) :
    ∃ t', t < t' ∧ R (shiftedStream W N) t' = R (shiftedStream W N) t - 1 ∧
      (∀ s, t < s → s < t' → R (shiftedStream W N) t - 1 < R (shiftedStream W N) s) ∧
      edgeWest (shiftedStream W N) (act (shiftedStream W N) t') =
        edgeEast (shiftedStream W N) (act (shiftedStream W N) t) ∧
      wholePlaneRightmostOutgoingAt W H
        (wholePlaneVertexι W N
          (edgeEast (shiftedStream W N) (act (shiftedStream W N) t)))
        (wholePlaneEdgeι W N (act (shiftedStream W N) t')) := by
  let w := shiftedStream W N
  obtain ⟨q, htq, hdrop, hgap, hw, _⟩ := kmswActiveTerminal_firstDescent w hR t
  have hsum := R_shift_add w t (q - t)
  rw [Nat.add_sub_of_le htq.le] at hsum
  have hd : 0 < q - t := by omega
  have hdu : R (fun i => w (t + i)) (q - t) = -1 := by omega
  have hgu : ∀ j, 0 < j → j < q - t → -1 < R (fun i => w (t + i)) j := by
    intro j hj hjq
    have hh := hgap (t + j) (by omega) (by omega)
    have hs := R_shift_add w t j
    omega
  refine ⟨q, htq, hdrop, hgap, hw, ?_⟩
  have hh := descent_rightmost W H N t (q - t) (shift_unbounded w hR t) hd hdu hgu
    (by simpa only [Nat.add_sub_of_le htq.le] using hw)
  simpa only [Nat.add_sub_of_le htq.le] using hh





theorem wholePlaneRightmost_descent (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a) (t : ℕ) (e : WholePlaneEdge W)
    (he : wholePlaneRightmostOutgoingAt W H
      (wholePlaneVertexι W N (edgeEast (shiftedStream W N) (act (shiftedStream W N) t))) e) :
    ∃ t', t < t' ∧ R (shiftedStream W N) t' = R (shiftedStream W N) t - 1 ∧
      (∀ s, t < s → s < t' → R (shiftedStream W N) t - 1 < R (shiftedStream W N) s) ∧
      e = wholePlaneEdgeι W N (act (shiftedStream W N) t') ∧
      wholePlaneEdgeEast W e = wholePlaneVertexι W N
        (edgeEast (shiftedStream W N) (act (shiftedStream W N) t')) := by
  obtain ⟨q, htq, hdrop, hgap, _, hright⟩ :=
    wholePlaneRightmost_descent_at_active W H N hR t
  have heq := wholePlaneRightmostOutgoingAt_unique W H _ he hright
  refine ⟨q, htq, hdrop, hgap, heq, ?_⟩
  rw [heq, wholePlaneEdgeEast_ι]

end DirectedDistances.KMSW
