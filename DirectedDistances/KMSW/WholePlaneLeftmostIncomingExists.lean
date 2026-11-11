module

public import DirectedDistances.KMSW.WholePlaneLeftmostIncoming
import DirectedDistances.KMSW.WholePlaneRightmostOutgoingExists
import DirectedDistances.KMSW.OutgoingIntervalFreshLeft

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW

private def runBase (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private def base (W : ℤ → Fin 3) (d : WholePlaneDart W) : WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1

private theorem runBase_rot (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) : runBase w (kmswInfRot w hfin d) = runBase w d := by
  obtain ⟨n, hn⟩ := kmswInfRot_eventually_eq_stage w hfin d
  obtain ⟨hd, he⟩ := hn n le_rfl
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  have hb (z : StageDart (kmswStage w n).nextEdge) :
      stageEndpoint (kmswStage w n) z = runBase w (z.1.val, z.2) := by
    obtain ⟨hw, he⟩ := edge_endpoints_eq w z.1.isLt
    cases hs : z.2 <;>
      simp only [stageEndpoint, runBase, hs, Bool.false_eq_true, ↓reduceIte, hw, he]
  rw [he, ← hb (stageRot w n x), ← hb x]
  exact ((stageRot_sameCycle_iff_endpoint_eq w n x (stageRot w n x)).mp
    ⟨1, rfl⟩).symm

private theorem runBase_symm_pow (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    runBase w (((kmswInfRot w hfin).symm ^ k) d) = runBase w d := by
  have hs (x : ℕ × Bool) : runBase w ((kmswInfRot w hfin).symm x) = runBase w x := by
    have h := runBase_rot w hfin ((kmswInfRot w hfin).symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hs, ih]

private theorem base_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    base W (wholePlaneDartι W N d) =
      wholePlaneVertexι W N (runBase (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [base, runBase, wholePlaneDartι, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeWest_ι W N d.1
  · exact wholePlaneEdgeEast_ι W N d.1

private theorem base_symm_pow (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) (k : ℕ) :
    base W (((wholePlaneRotation W H).symm ^ k) d) = base W d := by
  obtain ⟨e, s⟩ := d
  obtain ⟨⟨N, a⟩, rfl⟩ := Quotient.exists_rep e
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N (a, s)
  change base W (((wholePlaneRotation W H).symm ^ k)
    (wholePlaneDartι W N (a, s))) = base W (wholePlaneDartι W N (a, s))
  rw [hpow k, base_ι, runBase_symm_pow, ← base_ι]
  exact congrArg (base W) (congrFun (wholePlaneDartι_trans W N M hNM) (a, s))




theorem wholePlaneLeftmostIncomingAt_outgoing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    {e : WholePlaneEdge W} (he : wholePlaneLeftmostIncomingAt W H v e) :
    ∃ f, wholePlaneEdgePresent W f ∧ wholePlaneEdgeWest W f = v := by
  obtain ⟨_, hev, k, _, hs, hp, _⟩ := he
  refine ⟨(((wholePlaneRotation W H).symm ^ k) (e, true)).1, hp, ?_⟩
  have hb := base_symm_pow W H (e, true) k
  simpa only [base, hs, Bool.false_eq_true, ↓reduceIte] using hb.trans hev




theorem wholePlaneLeftmostIncomingAt_exists_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) :
    (∃ e, wholePlaneLeftmostIncomingAt W H v e) ↔
      (∃ f, wholePlaneEdgePresent W f ∧ wholePlaneEdgeEast W f = v) ∧
      ∃ e, wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨⟨e, he.1, he.2.1⟩, wholePlaneLeftmostIncomingAt_outgoing W H v he⟩
  · rintro ⟨⟨f, hfp, hfv⟩, e, hep, hev⟩
    let τ := wholePlaneRotation W H
    let P : WholePlaneDart W → Prop := fun d =>
      wholePlaneEdgePresent W d.1 ∧ base W d = v
    have hbase : base W (e, false) = base W (f, true) := hev.trans hfv.symm
    obtain ⟨m, hm⟩ := wholePlaneRotation_exists_pow_of_base W H
      (e, false) (f, true) hbase
    have hb : P ((τ ^ m) (e, false)) ∧ ((τ ^ m) (e, false)).2 = true := by
      rw [hm]
      exact ⟨⟨hfp, hfv⟩, rfl⟩
    obtain ⟨d, k, hdp, hdo, hk, hkp, hko, hgap⟩ :=
      exists_first_present_after_incoming τ P (fun d => d.2 = true)
        (e, false) m ⟨⟨hep, hev⟩, Bool.noConfusion⟩ hb
    have hdv : wholePlaneEdgeEast W d.1 = v := by
      simpa only [base, hdo, ↓reduceIte] using hdp.2
    have hd : d = (d.1, true) := Prod.ext rfl hdo
    have hside : ((τ.symm ^ k) d).2 = false := by
      cases hs : ((τ.symm ^ k) d).2
      · rfl
      · exact (hko hs).elim
    refine ⟨d.1, hdp.1, hdv, k, hk, ?_, ?_, ?_⟩
    · simpa only [← hd] using hside
    · simpa only [← hd] using hkp.1
    · intro j hj hjk hp
      apply hgap j hj hjk
      refine ⟨?_, (base_symm_pow W H d j).trans hdp.2⟩
      simpa only [← hd] using hp

private theorem runBase_pow (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    runBase w ((kmswInfRot w hfin ^ k) d) = runBase w d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, runBase_rot, ih]

private theorem fresh_arc (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (a b : ℕ)
    (hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (edgeWest (shiftedStream W N) a))
    (ha : EdgePresent (shiftedStream W N) a)
    (hb : EdgePresent (shiftedStream W N) b)
    (hv : edgeWest (shiftedStream W N) a = edgeWest (shiftedStream W N) b) :
    RotationArc (wholePlaneRotation W H)
      (fun d => d.2 = false ∧ wholePlaneEdgePresent W d.1)
      (wholePlaneEdgeι W N a, false) (wholePlaneEdgeι W N b, false) ∨
    RotationArc (wholePlaneRotation W H)
      (fun d => d.2 = false ∧ wholePlaneEdgePresent W d.1)
      (wholePlaneEdgeι W N b, false) (wholePlaneEdgeι W N a, false) := by
  let w := shiftedStream W N
  let σ := kmswInfRot w (H.1 N)
  let τ := wholePlaneRotation W H
  let I : (ℕ × Bool) → WholePlaneDart W := wholePlaneDartι W N
  have lift (d : ℕ × Bool)
      (hd : runBase w d = edgeWest w a) (k : ℕ) :
      (τ ^ k) (I d) = I ((σ ^ k) d) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hstep : τ (I ((σ ^ k) d)) = I (σ ((σ ^ k) d)) := by
        apply wholePlaneRotation_ι_of_fresh W H N ((σ ^ k) d)
        intro M hNM
        change wholePlaneFresh W N M hNM (runBase w ((σ ^ k) d))
        rw [runBase_pow, hd]
        exact hf M hNM
      calc
        (τ ^ (k + 1)) (I d) = τ ((τ ^ k) (I d)) :=
          Equiv.congr_fun (pow_succ' τ k) (I d)
        _ = τ (I ((σ ^ k) d)) := congrArg τ ih
        _ = I (σ ((σ ^ k) d)) := hstep
        _ = I ((σ ^ (k + 1)) d) :=
          congrArg I (Equiv.congr_fun (pow_succ' σ k) d).symm
  have arc (d e : ℕ × Bool) (hd : runBase w d = edgeWest w a)
      (h : RotationArc σ (fun x => x.2 = false ∧ EdgePresent w x.1) d e) :
      RotationArc τ (fun x => x.2 = false ∧ wholePlaneEdgePresent W x.1)
        (I d) (I e) := by
    obtain ⟨k, hk, hm⟩ := h
    refine ⟨k, (lift d hd k).trans (congrArg I hk), ?_⟩
    intro j hj
    rw [lift d hd j]
    exact ⟨(hm j hj).1,
      wholePlaneEdgePresent_ι_of_run_present W N _ (hm j hj).2⟩
  rcases kmswInfRot_outgoing_interval_all w (H.1 N) a b hv ha hb with h | h
  · exact Or.inl (arc (a, false) (b, false) rfl h)
  · exact Or.inr (arc (b, false) (a, false) hv.symm h)

private theorem ambient_outgoing_arc (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (e f : WholePlaneEdge W)
    (he : wholePlaneEdgePresent W e) (hf : wholePlaneEdgePresent W f)
    (hv : wholePlaneEdgeWest W e = wholePlaneEdgeWest W f) :
    RotationArc (wholePlaneRotation W H)
      (fun d => d.2 = false ∧ wholePlaneEdgePresent W d.1) (e, false) (f, false) ∨
    RotationArc (wholePlaneRotation W H)
      (fun d => d.2 = false ∧ wholePlaneEdgePresent W d.1) (f, false) (e, false) := by
  obtain ⟨⟨A, a⟩, rfl⟩ := Quotient.exists_rep e
  obtain ⟨⟨B, b⟩, rfl⟩ := Quotient.exists_rep f
  let C := max A B
  have hAC : A ≤ C := Nat.le_max_left _ _
  have hBC : B ≤ C := Nat.le_max_right _ _
  let c := wholePlaneEdgeTrans W A C hAC a
  let d := wholePlaneEdgeTrans W B C hBC b
  have hc : wholePlaneEdgeι W C c = wholePlaneEdgeι W A a :=
    congrFun (wholePlaneEdgeι_trans W A C hAC) a
  have hd : wholePlaneEdgeι W C d = wholePlaneEdgeι W B b :=
    congrFun (wholePlaneEdgeι_trans W B C hBC) b
  have hcd : edgeWest (shiftedStream W C) c = edgeWest (shiftedStream W C) d := by
    apply wholePlaneVertexι_injective W C
    rw [← wholePlaneEdgeWest_ι, ← wholePlaneEdgeWest_ι, hc, hd]
    exact hv
  obtain ⟨M, hCM, hM⟩ := H.2 C (edgeWest (shiftedStream W C) c)
  let p := wholePlaneEdgeTrans W C M hCM c
  let q := wholePlaneEdgeTrans W C M hCM d
  have hp : wholePlaneEdgeι W M p = wholePlaneEdgeι W A a :=
    (congrFun (wholePlaneEdgeι_trans W C M hCM) c).trans hc
  have hq : wholePlaneEdgeι W M q = wholePlaneEdgeι W B b :=
    (congrFun (wholePlaneEdgeι_trans W C M hCM) d).trans hd
  have hvpq : edgeWest (shiftedStream W M) p = edgeWest (shiftedStream W M) q := by
    exact (wholePlaneEdgeTrans_west W C M hCM c).trans
      ((congrArg (wholePlaneVertexTrans W C M hCM) hcd).trans
        (wholePlaneEdgeTrans_west W C M hCM d).symm)
  have fresh : ∀ L (hML : M ≤ L), wholePlaneFresh W M L hML
      (edgeWest (shiftedStream W M) p) := by
    intro L hML
    dsimp only [p]
    rw [wholePlaneEdgeTrans_west]
    exact hM L hML
  have hpp : EdgePresent (shiftedStream W M) p :=
    (wholePlaneEdgePresent_ι_of_fresh W M p false fresh).mp (hp.symm ▸ he)
  have hqp : EdgePresent (shiftedStream W M) q := by
    apply (wholePlaneEdgePresent_ι_of_fresh W M q false _).mp (hq.symm ▸ hf)
    change ∀ L (hML : M ≤ L), wholePlaneFresh W M L hML
      (edgeWest (shiftedStream W M) q)
    rw [← hvpq]
    exact fresh
  have h := fresh_arc W H M p q fresh hpp hqp hvpq
  rw [hp, hq] at h
  exact h

private theorem forward_inverse_pow {α : Type*} (τ : Equiv.Perm α) (b : α)
    {j k : ℕ} (hjk : j ≤ k) :
    (τ ^ j) ((τ.symm ^ k) b) = (τ.symm ^ (k - j)) b := by
  have hc (l : ℕ) (x : α) : (τ ^ l) ((τ.symm ^ l) x) = x := by
    induction l with
    | zero => rfl
    | succ l ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
        Equiv.apply_symm_apply, ih]
  have he : (τ.symm ^ k) b = (τ.symm ^ j) ((τ.symm ^ (k - j)) b) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hjk]
  rw [he]
  exact hc j _

private theorem forward_of_inverse {α : Type*} (τ : Equiv.Perm α)
    (P : α → Prop) (a b : α) (k : ℕ)
    (hback : (τ.symm ^ k) b = a)
    (hgap : ∀ j, 0 < j → j < k → ¬ P ((τ.symm ^ j) b)) :
    (τ ^ k) a = b ∧ ∀ j, 0 < j → j < k → ¬ P ((τ ^ j) a) := by
  constructor
  · rw [← hback, forward_inverse_pow τ b le_rfl, Nat.sub_self]
    rfl
  · intro j hj hjk hp
    rw [← hback, forward_inverse_pow τ b (by omega)] at hp
    exact hgap (k - j) (by omega) (by omega) hp

private theorem next_present_unique {α : Type*} (τ : Equiv.Perm α)
    (P : α → Prop) (a b c : α) (hb : P b) (hc : P c)
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hkb : (τ ^ k) a = b) (hlc : (τ ^ l) a = c)
    (hkgap : ∀ j, 0 < j → j < k → ¬ P ((τ ^ j) a))
    (hlgap : ∀ j, 0 < j → j < l → ¬ P ((τ ^ j) a)) : b = c := by
  rcases lt_trichotomy k l with h | h | h
  · exact (hlgap k hk h (hkb.symm ▸ hb)).elim
  · subst l
    exact hkb.symm.trans hlc
  · exact (hkgap l hl h (hlc.symm ▸ hc)).elim

private theorem outgoing_arc_start_eq {E : Type*} (τ : Equiv.Perm (E × Bool))
    (P : E × Bool → Prop) (a b c : E × Bool) (hc : c.2 = true)
    (k : ℕ) (hk : 0 < k) (hkc : (τ ^ k) a = c)
    (hgap : ∀ j, 0 < j → j < k → ¬ P ((τ ^ j) a))
    (harc : RotationArc τ (fun d => d.2 = false ∧ P d) a b) : a = b := by
  obtain ⟨n, hn, hm⟩ := harc
  cases n with
  | zero => exact hn
  | succ n =>
    have hp := hm 1 (by omega)
    by_cases hk1 : k = 1
    · have hh : (τ ^ 1) a = c := hk1 ▸ hkc
      have hs : c.2 = false := hh ▸ hp.1
      exact Bool.noConfusion (hs.symm.trans hc)
    · exact (hgap 1 (by omega) (by omega) hp.2).elim




theorem wholePlaneLeftmostIncomingAt_unique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    {e f : WholePlaneEdge W} (he : wholePlaneLeftmostIncomingAt W H v e)
    (hf : wholePlaneLeftmostIncomingAt W H v f) : e = f := by
  obtain ⟨hep, hev, k, hk, hks, hkp, hkg⟩ := he
  obtain ⟨hfp, hfv, l, hl, hls, hlp, hlg⟩ := hf
  let τ := wholePlaneRotation W H
  let P : WholePlaneDart W → Prop := fun d => wholePlaneEdgePresent W d.1
  let a := (τ.symm ^ k) (e, true)
  let b := (τ.symm ^ l) (f, true)
  have ha : a = (a.1, false) := Prod.ext rfl hks
  have hb : b = (b.1, false) := Prod.ext rfl hls
  have hav : wholePlaneEdgeWest W a.1 = v := by
    have hh := base_symm_pow W H (e, true) k
    simpa only [base, hks, Bool.false_eq_true, ↓reduceIte] using hh.trans hev
  have hbv : wholePlaneEdgeWest W b.1 = v := by
    have hh := base_symm_pow W H (f, true) l
    simpa only [base, hls, Bool.false_eq_true, ↓reduceIte] using hh.trans hfv
  have hnext := forward_of_inverse τ P a (e, true) k rfl hkg
  have hnext' := forward_of_inverse τ P b (f, true) l rfl hlg
  have hab : a = b := by
    rcases ambient_outgoing_arc W H a.1 b.1 hkp hlp (hav.trans hbv.symm) with h | h
    · rw [← ha, ← hb] at h
      exact outgoing_arc_start_eq τ P a b (e, true) rfl k hk hnext.1 hnext.2 h
    · rw [← ha, ← hb] at h
      exact (outgoing_arc_start_eq τ P b a (f, true) rfl l hl
        hnext'.1 hnext'.2 h).symm
  rw [← hab] at hnext'
  exact congrArg Prod.fst (next_present_unique τ P a (e, true) (f, true)
    hep hfp k l hk hl hnext.1 hnext'.1 hnext.2 hnext'.2)




theorem wholePlaneLeftmostIncomingAt_existsUnique_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) :
    (∃! e, wholePlaneLeftmostIncomingAt W H v e) ↔
      (∃ f, wholePlaneEdgePresent W f ∧ wholePlaneEdgeEast W f = v) ∧
      ∃ e, wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v := by
  constructor
  · intro h
    exact (wholePlaneLeftmostIncomingAt_exists_iff W H v).mp h.exists
  · intro h
    obtain ⟨e, he⟩ := (wholePlaneLeftmostIncomingAt_exists_iff W H v).mpr h
    exact ⟨e, he, fun f hf => wholePlaneLeftmostIncomingAt_unique W H v hf he⟩

end DirectedDistances.KMSW
