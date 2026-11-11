module

public import DirectedDistances.KMSW.RunRightmostRay
public import DirectedDistances.KMSW.WholePlaneRightmostDescent
public import DirectedDistances.KMSW.RightDescentPotential
public import DirectedDistances.KMSW.StageActiveEdges
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




private theorem descent_rightmost (w : ℕ → Fin 3) (hf : KMSWFiniteIncidence w)
    (t d : ℕ) (hR : ∀ a : ℤ, ∃ n, R (fun i => w (t + i)) n ≤ a)
    (hd : 0 < d) (hdrop : R (fun i => w (t + i)) d = -1)
    (hgap : ∀ j, 0 < j → j < d → -1 < R (fun i => w (t + i)) j)
    (hwest : edgeWest w (act w (t + d)) = edgeEast w (act w t)) :
    kmswRunRightmostOutAt w hf (edgeEast w (act w t)) (act w (t + d)) := by
  let u := fun i => w (t + i)
  let e := act w (t + d)
  change R u d = -1 at hdrop
  change ∀ j, 0 < j → j < d → -1 < R u j at hgap
  have hcorner := first_record_corner u (shift_finite w hf t) hR d hd hdrop hgap
  have hroot : edgeEast u (act u 0) = 1 := by
    rw [← (edge_endpoints_eq u (act_lt_nextEdge u (le_refl 0))).2]
    rfl
  have hlocal : base u (act u d, false) = 1 := by
    obtain ⟨q, hq, hqd, hqgap, hqw, _⟩ := kmswActiveTerminal_firstDescent u hR 0
    have hqdrop : R u q = -1 := by
      rw [show R u 0 = 0 by simp [R]] at hqd
      omega
    have hqd' : q = d := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · have := hgap q hq hlt
        omega
      · have := hqgap d hd hgt
        simp only [show R u 0 = 0 by simp [R]] at this
        omega
    simpa only [base, Bool.false_eq_true, ↓reduceIte, hqd', hroot] using hqw
  obtain ⟨k, hk, hret, hmiss⟩ := window_firstReturn w t hf (act u d, false) hlocal
  rw [hcorner] at hret
  have hstart : windowDart w t (act u d, false) = (e, false) :=
    Prod.ext (window_act w t d) rfl
  have hend : windowDart w t (0, true) = (act w t, true) :=
    Prod.ext (window_root w t) rfl
  rw [hstart, hend] at hret
  rw [hstart] at hmiss
  have hn : ¬ futureMapTail w ((kmswInfRot w hf).symm (e, false)) := by
    intro ht
    by_cases hk1 : k = 1
    · rw [hk1, pow_one] at hret
      have hb := ht.1
      rw [hret] at hb
      cases hb
    · let z := (kmswInfRot w hf).symm (e, false)
      have hv : kmswLimitDartVertex w z = edgeWest w e := by
        have hh := kmswLimitDartVertex_rot w hf z
        rw [Equiv.apply_symm_apply] at hh
        exact hh.symm
      have hzb : z.2 = false := ht.1
      have hzw : edgeWest w z.1 = edgeEast w (act w t) := by
        simpa only [kmswLimitDartVertex, hzb, Bool.false_eq_true, ↓reduceIte,
          e, hwest] using hv
      obtain ⟨q, htq, hfq, _⟩ := (kmswActiveTerminal_outgoing_iff w t z.1).mp
        ⟨ht.2, hzw⟩
      apply hmiss 1 (by omega) (by omega)
      refine ⟨(act u (q - t), false), ?_⟩
      rw [pow_one]
      apply Prod.ext
      · change kmswWindowEdgeMapInf w t (act u (q - t)) = z.1
        rw [window_act, Nat.add_sub_of_le htq.le, ← hfq]
      · exact ht.1.symm
  refine ⟨⟨t + d, act_lt_nextEdge w le_rfl, active_present w (t + d)⟩,
    hwest, 1, by omega, ?_, ?_⟩
  · simpa only [pow_one] using hn
  · intro j hj hj1
    omega





theorem kmswRunRightmost_descent_at_active (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ) :
    ∃ t', t < t' ∧ R w t' = R w t - 1 ∧
      (∀ s, t < s → s < t' → R w t - 1 < R w s) ∧
      edgeWest w (act w t') = edgeEast w (act w t) ∧
      kmswRunRightmostOutAt w hfin (edgeEast w (act w t)) (act w t') := by
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
  have hh := descent_rightmost w hfin t (q - t) (shift_unbounded w hR t) hd hdu hgu
    (by simpa only [Nat.add_sub_of_le htq.le] using hw)
  simpa only [Nat.add_sub_of_le htq.le] using hh




theorem kmswRunRightmost_descent (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t e : ℕ)
    (he : kmswRunRightmostOutAt w hfin (edgeEast w (act w t)) e) :
    ∃ t', t < t' ∧ R w t' = R w t - 1 ∧
      (∀ s, t < s → s < t' → R w t - 1 < R w s) ∧ e = act w t' := by
  obtain ⟨q, htq, hdrop, hgap, _, hr⟩ :=
    kmswRunRightmost_descent_at_active w hfin hR t
  exact ⟨q, htq, hdrop, hgap,
    kmswRunRightmostOutAt_unique w hfin _ he hr⟩




theorem kmswRunRightmostRay_hits_rightBoundary (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w)
    (P : KMSWRunRightmostRay w hfin) (t : ℕ)
    (h0 : P.vertex 0 = edgeEast w (act w t)) :
    ∃ i j, i ≤ Int.toNat (R w t - minR w t) + 1 ∧
      P.vertex i = edgeEast w (kmswRightBoundaryEdge w j) := by
  have hR := h.R_unbounded_below
  let next := fun a => Classical.choose (kmswRunRightmost_descent_at_active w hfin hR a)
  have hn (a : ℕ) := Classical.choose_spec
    (kmswRunRightmost_descent_at_active w hfin hR a)
  let s : ℕ → ℕ := fun i => Nat.rec t (fun _ a => next a) i
  have hs (i : ℕ) : s i < s (i + 1) ∧ R w (s (i + 1)) = R w (s i) - 1 ∧
      ∀ q, s i < q → q < s (i + 1) → R w (s i) - 1 < R w q :=
    ⟨(hn (s i)).1, (hn (s i)).2.1, (hn (s i)).2.2.1⟩
  have hv (i : ℕ) : P.vertex i = edgeEast w (act w (s i)) := by
    induction i with
    | zero => exact h0
    | succ i ih =>
      have hr := P.rightmost i
      rw [ih] at hr
      have he := kmswRunRightmostOutAt_unique w hfin _ hr (hn (s i)).2.2.2.2
      exact (P.target i).symm.trans (congrArg (edgeEast w) he)
  obtain ⟨i, hi, hrec⟩ := descentChain_hits_record w s hs
  obtain ⟨j, hj⟩ := hrec i le_rfl
  exact ⟨i, j, hi, (hv i).trans (congrArg (edgeEast w) hj)⟩

end DirectedDistances.KMSW
