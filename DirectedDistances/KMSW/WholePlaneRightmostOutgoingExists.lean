module

public import DirectedDistances.KMSW.WholePlaneRightmostRays




public section
namespace DirectedDistances.KMSW

private theorem inverse_pow_forward {α : Type*} (τ : Equiv.Perm α) (a : α)
    {i k : ℕ} (hki : k ≤ i) :
    (τ.symm ^ k) ((τ ^ i) a) = (τ ^ (i - k)) a := by
  have hc (l : ℕ) (x : α) : (τ.symm ^ l) ((τ ^ l) x) = x := by
    induction l with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
        Equiv.symm_apply_apply, ih]
  have he : (τ ^ i) a = (τ ^ k) ((τ ^ (i - k)) a) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hki]
  rw [he]
  exact hc k _

private theorem first_present_on_orbit {α : Type*} (τ : Equiv.Perm α)
    (P O : α → Prop) (a : α) (m : ℕ) (ha : P a ∧ ¬ O a)
    (hb : P ((τ ^ m) a) ∧ O ((τ ^ m) a)) :
    ∃ d k, (∃ i : ℕ, d = (τ ^ i) a) ∧
      P d ∧ O d ∧ 0 < k ∧ P ((τ.symm ^ k) d) ∧
      ¬ O ((τ.symm ^ k) d) ∧
      ∀ j, 0 < j → j < k → ¬ P ((τ.symm ^ j) d) := by
  classical
  have hex : ∃ i : ℕ, P ((τ ^ i) a) ∧ O ((τ ^ i) a) := ⟨m, hb⟩
  let i := Nat.find hex
  have hi : P ((τ ^ i) a) ∧ O ((τ ^ i) a) := Nat.find_spec hex
  have hip : 0 < i := by
    by_contra h
    have hz : i = 0 := by omega
    rw [hz] at hi
    exact ha.2 hi.2
  have hback : ∃ k : ℕ, 0 < k ∧ P ((τ.symm ^ k) ((τ ^ i) a)) := by
    refine ⟨i, hip, ?_⟩
    simpa only [inverse_pow_forward τ a le_rfl, Nat.sub_self, pow_zero,
      Equiv.Perm.one_apply] using ha.1
  let k := Nat.find hback
  have hk : 0 < k ∧ P ((τ.symm ^ k) ((τ ^ i) a)) := Nat.find_spec hback
  have hki : k ≤ i := Nat.find_min' hback ⟨hip, by
    simpa only [inverse_pow_forward τ a le_rfl, Nat.sub_self, pow_zero,
      Equiv.Perm.one_apply] using ha.1⟩
  refine ⟨(τ ^ i) a, k, ⟨i, rfl⟩, hi.1, hi.2, hk.1, hk.2, ?_, ?_⟩
  · intro ho
    have hp := hk.2
    rw [inverse_pow_forward τ a hki] at hp ho
    exact Nat.find_min hex (by dsimp only [i, k] at *; omega) ⟨hp, ho⟩
  · intro j hj hjk hp
    exact Nat.find_min hback hjk ⟨hj, hp⟩




theorem exists_first_present_after_incoming {α : Type*} (τ : Equiv.Perm α)
    (P O : α → Prop) (a : α) (m : ℕ) (ha : P a ∧ ¬ O a)
    (hb : P ((τ ^ m) a) ∧ O ((τ ^ m) a)) :
    ∃ d k, P d ∧ O d ∧ 0 < k ∧ P ((τ.symm ^ k) d) ∧
      ¬ O ((τ.symm ^ k) d) ∧
      ∀ j, 0 < j → j < k → ¬ P ((τ.symm ^ j) d) := by
  obtain ⟨d, k, _, hd⟩ := first_present_on_orbit τ P O a m ha hb
  exact ⟨d, k, hd⟩

private def runBase (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private def ambientBase (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1

private theorem stage_base (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) x = runBase w (x.1.val, x.2) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w x.1.isLt
  cases hs : x.2 <;>
    simp only [stageEndpoint, runBase, hs, Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem runBase_rot (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) : runBase w (kmswInfRot w hfin d) = runBase w d := by
  obtain ⟨n, hn⟩ := kmswInfRot_eventually_eq_stage w hfin d
  obtain ⟨hd, he⟩ := hn n le_rfl
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  rw [he, ← stage_base w n (stageRot w n x), ← stage_base w n x]
  exact ((stageRot_sameCycle_iff_endpoint_eq w n x (stageRot w n x)).mp
    ⟨1, rfl⟩).symm

private theorem runBase_pow (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    runBase w ((kmswInfRot w hfin ^ k) d) = runBase w d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, runBase_rot, ih]

private theorem run_pow_stage (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (n : ℕ) (x : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) x)) (k : ℕ) :
    ((kmswInfRot w hfin) ^ k) (x.1.val, x.2) =
      (((stageRot w n ^ k) x).1.val, ((stageRot w n ^ k) x).2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    have he : stageEndpoint (kmswStage w n) ((stageRot w n ^ k) x) =
        stageEndpoint (kmswStage w n) x :=
      ((stageRot_sameCycle_iff_endpoint_eq w n x ((stageRot w n ^ k) x)).mp
        ⟨(k : ℤ), by simp only [zpow_natCast]⟩).symm
    rw [kmswInfRot_eq_stage w hfin n _ (he ▸ hc),
      pow_succ', Equiv.Perm.mul_apply]

private theorem run_exists_pow (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d d' : ℕ × Bool) (h : runBase w d = runBase w d') :
    (∃ m : ℕ, ((kmswInfRot w hfin) ^ m) d = d') ∧
      ∃ n : ℕ, 0 < n ∧ ((kmswInfRot w hfin) ^ n) d = d := by
  obtain ⟨B, hB⟩ := (hfin (runBase w d)).bddAbove
  have hc : kmswVertexComplete w B (runBase w d) := by
    intro e he
    apply (hB (show e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = runBase w d ∨
        (kmswStage w n).east e = runBase w d)} from
      ⟨e, kmsw_edge_allocated_by_self w e, he⟩)).trans_lt
    exact kmsw_edge_allocated_by_self w B
  have bound (z : ℕ × Bool) (hz : runBase w z = runBase w d) :
      z.1 < (kmswStage w B).nextEdge := by
    apply hc z.1
    cases hs : z.2
    · exact Or.inl (by simpa only [runBase, hs, Bool.false_eq_true, ↓reduceIte] using hz)
    · exact Or.inr (by simpa only [runBase, hs, ↓reduceIte] using hz)
  let x : StageDart (kmswStage w B).nextEdge := (⟨d.1, bound d rfl⟩, d.2)
  let y : StageDart (kmswStage w B).nextEdge := (⟨d'.1, bound d' h.symm⟩, d'.2)
  have hcx : kmswVertexComplete w B (stageEndpoint (kmswStage w B) x) := by
    rw [stage_base]
    exact hc
  have hxy : (stageRot w B).SameCycle x y := by
    apply (stageRot_sameCycle_iff_endpoint_eq w B x y).mpr
    rw [stage_base, stage_base]
    exact h
  obtain ⟨m, hm⟩ := hxy.exists_nat_pow_eq
  constructor
  · refine ⟨m, ?_⟩
    rw [show d = (x.1.val, x.2) from rfl, run_pow_stage w hfin B x hcx m, hm]
  · refine ⟨orderOf (stageRot w B), orderOf_pos _, ?_⟩
    rw [show d = (x.1.val, x.2) from rfl, run_pow_stage w hfin B x hcx,
      pow_orderOf_eq_one]
    rfl

private theorem base_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    ambientBase W (wholePlaneDartι W N d) =
      wholePlaneVertexι W N (runBase (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [ambientBase, runBase, wholePlaneDartι, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeWest_ι W N d.1
  · exact wholePlaneEdgeEast_ι W N d.1

private theorem trans_base (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M)
    (d : ℕ × Bool) :
    runBase (shiftedStream W M) (wholePlaneDartTrans W N M h d) =
      wholePlaneVertexTrans W N M h (runBase (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [runBase, wholePlaneDartTrans, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeTrans_west W N M h d.1
  · exact wholePlaneEdgeTrans_east W N M h d.1

private theorem fresh_pow (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (d : ℕ × Bool)
    (hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (runBase (shiftedStream W N) d)) (k : ℕ) :
    (wholePlaneRotation W H ^ k) (wholePlaneDartι W N d) =
      wholePlaneDartι W N ((kmswInfRot (shiftedStream W N) (H.1 N) ^ k) d) := by
  let σ := kmswInfRot (shiftedStream W N) (H.1 N)
  let τ := wholePlaneRotation W H
  let I : (ℕ × Bool) → WholePlaneDart W := wholePlaneDartι W N
  change (τ ^ k) (I d) = I ((σ ^ k) d)
  induction k with
  | zero => rfl
  | succ k ih =>
    have hf' : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
        (runBase (shiftedStream W N) ((σ ^ k) d)) := by
      intro M hNM
      rw [runBase_pow]
      exact hf M hNM
    have hstep : τ (I ((σ ^ k) d)) = I (σ ((σ ^ k) d)) :=
      wholePlaneRotation_ι_of_fresh W H N _ hf'
    calc
      (τ ^ (k + 1)) (I d) = τ ((τ ^ k) (I d)) :=
        Equiv.congr_fun (pow_succ' τ k) (I d)
      _ = τ (I ((σ ^ k) d)) := congrArg τ ih
      _ = I (σ ((σ ^ k) d)) := hstep
      _ = I ((σ ^ (k + 1)) d) :=
        congrArg I (Equiv.congr_fun (pow_succ' σ k) d).symm

private theorem common_run_pow (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (d d' : ℕ × Bool)
    (h : runBase (shiftedStream W N) d = runBase (shiftedStream W N) d') :
    (∃ m : ℕ, (wholePlaneRotation W H ^ m) (wholePlaneDartι W N d) =
      wholePlaneDartι W N d') ∧
    ∃ n : ℕ, 0 < n ∧ (wholePlaneRotation W H ^ n) (wholePlaneDartι W N d) =
      wholePlaneDartι W N d := by
  obtain ⟨M, hNM, hf⟩ := H.2 N (runBase (shiftedStream W N) d)
  let p := wholePlaneDartTrans W N M hNM d
  let q := wholePlaneDartTrans W N M hNM d'
  have hp : ∀ L (hML : M ≤ L), wholePlaneFresh W M L hML
      (runBase (shiftedStream W M) p) := by
    intro L hML
    rw [trans_base]
    exact hf L hML
  have hpq : runBase (shiftedStream W M) p = runBase (shiftedStream W M) q := by
    rw [trans_base, trans_base, h]
  obtain ⟨⟨m, hm⟩, n, hn, hperiod⟩ := run_exists_pow (shiftedStream W M) (H.1 M) p q hpq
  have hi := congrFun (wholePlaneDartι_trans W N M hNM) d
  have hi' := congrFun (wholePlaneDartι_trans W N M hNM) d'
  change wholePlaneDartι W M p = wholePlaneDartι W N d at hi
  change wholePlaneDartι W M q = wholePlaneDartι W N d' at hi'
  constructor
  · refine ⟨m, ?_⟩
    rw [← hi, fresh_pow W H M p hp, hm, hi']
  · refine ⟨n, hn, ?_⟩
    rw [← hi, fresh_pow W H M p hp, hperiod]

private theorem ambient_exists_pow (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d d' : WholePlaneDart W) (h : ambientBase W d = ambientBase W d') :
    (∃ m : ℕ, (wholePlaneRotation W H ^ m) d = d') ∧
      ∃ n : ℕ, 0 < n ∧ (wholePlaneRotation W H ^ n) d = d := by
  obtain ⟨e, s⟩ := d
  obtain ⟨e', s'⟩ := d'
  obtain ⟨⟨A, a⟩, rfl⟩ := Quotient.exists_rep e
  obtain ⟨⟨B, b⟩, rfl⟩ := Quotient.exists_rep e'
  let C := max A B
  have hAC : A ≤ C := Nat.le_max_left _ _
  have hBC : B ≤ C := Nat.le_max_right _ _
  let c := wholePlaneDartTrans W A C hAC (a, s)
  let c' := wholePlaneDartTrans W B C hBC (b, s')
  have hc := congrFun (wholePlaneDartι_trans W A C hAC) (a, s)
  have hc' := congrFun (wholePlaneDartι_trans W B C hBC) (b, s')
  change wholePlaneDartι W C c = wholePlaneDartι W A (a, s) at hc
  change wholePlaneDartι W C c' = wholePlaneDartι W B (b, s') at hc'
  have hbase : runBase (shiftedStream W C) c = runBase (shiftedStream W C) c' := by
    apply wholePlaneVertexι_injective W C
    rw [← base_ι, ← base_ι, hc, hc']
    exact h
  have hh := common_run_pow W H C c c' hbase
  rw [hc, hc'] at hh
  exact hh




theorem wholePlaneRotation_exists_pow_of_base (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d d' : WholePlaneDart W)
    (h : (if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1) =
      (if d'.2 then wholePlaneEdgeEast W d'.1 else wholePlaneEdgeWest W d'.1)) :
    ∃ m : ℕ, (wholePlaneRotation W H ^ m) d = d' :=
  (ambient_exists_pow W H d d' h).1



theorem wholePlaneRotation_exists_period (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : WholePlaneDart W) :
    ∃ n : ℕ, 0 < n ∧ (wholePlaneRotation W H ^ n) d = d :=
  (ambient_exists_pow W H d d rfl).2

private theorem ambient_pow_base (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) (k : ℕ) :
    ambientBase W ((wholePlaneRotation W H ^ k) d) = ambientBase W d := by
  obtain ⟨e, s⟩ := d
  obtain ⟨⟨N, a⟩, rfl⟩ := Quotient.exists_rep e
  obtain ⟨M, hNM, hf⟩ := H.2 N (runBase (shiftedStream W N) (a, s))
  let p := wholePlaneDartTrans W N M hNM (a, s)
  have hp : ∀ L (hML : M ≤ L), wholePlaneFresh W M L hML
      (runBase (shiftedStream W M) p) := by
    intro L hML
    rw [trans_base]
    exact hf L hML
  have hi := congrFun (wholePlaneDartι_trans W N M hNM) (a, s)
  change wholePlaneDartι W M p = wholePlaneDartι W N (a, s) at hi
  change ambientBase W ((wholePlaneRotation W H ^ k)
    (wholePlaneDartι W N (a, s))) = ambientBase W (wholePlaneDartι W N (a, s))
  rw [← hi, fresh_pow W H M p hp, base_ι, base_ι, runBase_pow]



theorem wholePlaneRightmostOutgoingAt_exists_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) :
    (∃ e, wholePlaneRightmostOutgoingAt W H v e) ↔
      (∃ f, wholePlaneEdgePresent W f ∧ wholePlaneEdgeEast W f = v) ∧
      ∃ e, wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨wholePlaneRightmostOutgoingAt_incoming W H v he, e, he.1, he.2.1⟩
  · rintro ⟨⟨f, hfp, hfv⟩, e, hep, hev⟩
    let τ := wholePlaneRotation W H
    have hbase : ambientBase W (f, true) = ambientBase W (e, false) :=
      hfv.trans hev.symm
    obtain ⟨m, hm⟩ := ambient_exists_pow W H (f, true) (e, false) hbase |>.1
    have hb : wholePlaneEdgePresent W ((τ ^ m) (f, true)).1 ∧
        ((τ ^ m) (f, true)).2 = false := by
      rw [hm]
      exact ⟨hep, rfl⟩
    obtain ⟨d, k, ⟨i, hi⟩, hdp, hdo, hk, hkp, hko, hgap⟩ :=
      first_present_on_orbit τ (fun d => wholePlaneEdgePresent W d.1)
        (fun d => d.2 = false) (f, true) m ⟨hfp, Bool.noConfusion⟩ hb
    have hdv : wholePlaneEdgeWest W d.1 = v := by
      have hh := ambient_pow_base W H (f, true) i
      rw [← hi] at hh
      simpa only [ambientBase, hdo, Bool.false_eq_true, ↓reduceIte] using hh.trans hfv
    have hd : d = (d.1, false) := Prod.ext rfl hdo
    have hside : ((τ.symm ^ k) d).2 = true := by
      cases hs : ((τ.symm ^ k) d).2
      · exact (hko hs).elim
      · rfl
    refine ⟨d.1, hdp, hdv, k, hk, ?_, ?_, ?_⟩
    · simpa only [← hd] using hside
    · simpa only [← hd] using hkp
    · simpa only [← hd] using hgap




theorem wholePlaneRightmostOutgoingAt_existsUnique_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) :
    (∃! e, wholePlaneRightmostOutgoingAt W H v e) ↔
      (∃ f, wholePlaneEdgePresent W f ∧ wholePlaneEdgeEast W f = v) ∧
      ∃ e, wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v := by
  constructor
  · intro h
    exact (wholePlaneRightmostOutgoingAt_exists_iff W H v).mp h.exists
  · intro h
    obtain ⟨e, he⟩ := (wholePlaneRightmostOutgoingAt_exists_iff W H v).mpr h
    exact ⟨e, he, fun f hf => wholePlaneRightmostOutgoingAt_unique W H v hf he⟩

end DirectedDistances.KMSW
