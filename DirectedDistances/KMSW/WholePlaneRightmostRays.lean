module

public import DirectedDistances.KMSW.WholePlaneRightBoundaryChain
import DirectedDistances.KMSW.OutgoingIntervalFreshLeft

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW

private def rayBase (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private theorem rayBase_rot (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) :
    rayBase w (kmswInfRot w hfin d) = rayBase w d := by
  obtain ⟨n, hn⟩ := kmswInfRot_eventually_eq_stage w hfin d
  obtain ⟨hd, he⟩ := hn n le_rfl
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  have hb (z : StageDart (kmswStage w n).nextEdge) :
      stageEndpoint (kmswStage w n) z = rayBase w (z.1.val, z.2) := by
    obtain ⟨hw, he⟩ := edge_endpoints_eq w z.1.isLt
    cases hs : z.2 <;>
      simp only [stageEndpoint, rayBase, hs, Bool.false_eq_true, ↓reduceIte, hw, he]
  rw [he, ← hb (stageRot w n x), ← hb x]
  exact ((stageRot_sameCycle_iff_endpoint_eq w n x (stageRot w n x)).mp
    ⟨1, rfl⟩).symm

private theorem rayBase_pow (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    rayBase w ((kmswInfRot w hfin ^ k) d) = rayBase w d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, rayBase_rot, ih]

private theorem rayBase_symm_pow (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    rayBase w (((kmswInfRot w hfin).symm ^ k) d) = rayBase w d := by
  have hs (x : ℕ × Bool) : rayBase w ((kmswInfRot w hfin).symm x) = rayBase w x := by
    have h := rayBase_rot w hfin ((kmswInfRot w hfin).symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hs, ih]

private def rayAmbientBase (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1

private theorem rayBase_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    rayAmbientBase W (wholePlaneDartι W N d) =
      wholePlaneVertexι W N (rayBase (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [rayAmbientBase, rayBase, wholePlaneDartι, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeWest_ι W N d.1
  · exact wholePlaneEdgeEast_ι W N d.1

private theorem rayAmbientBase_symm_pow (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) (k : ℕ) :
    rayAmbientBase W (((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N d)) =
      rayAmbientBase W (wholePlaneDartι W N d) := by
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N d
  rw [hpow k, rayBase_ι, rayBase_symm_pow, ← rayBase_ι]
  exact congrArg (rayAmbientBase W) (congrFun (wholePlaneDartι_trans W N M hNM) d)

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
      (hd : rayBase w d = edgeWest w a) (k : ℕ) :
      (τ ^ k) (I d) = I ((σ ^ k) d) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hstep : τ (I ((σ ^ k) d)) = I (σ ((σ ^ k) d)) := by
        apply wholePlaneRotation_ι_of_fresh W H N ((σ ^ k) d)
        intro M hNM
        change wholePlaneFresh W N M hNM (rayBase w ((σ ^ k) d))
        rw [rayBase_pow, hd]
        exact hf M hNM
      calc
        (τ ^ (k + 1)) (I d) = τ ((τ ^ k) (I d)) :=
          Equiv.congr_fun (pow_succ' τ k) (I d)
        _ = τ (I ((σ ^ k) d)) := congrArg τ ih
        _ = I (σ ((σ ^ k) d)) := hstep
        _ = I ((σ ^ (k + 1)) d) :=
          congrArg I (Equiv.congr_fun (pow_succ' σ k) d).symm
  have arc (d e : ℕ × Bool) (hd : rayBase w d = edgeWest w a)
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

private theorem rightmost_arc_eq (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    (e f : WholePlaneEdge W) (hf : wholePlaneRightmostOutgoingAt W H v f)
    (h : RotationArc (wholePlaneRotation W H)
      (fun d => d.2 = false ∧ wholePlaneEdgePresent W d.1) (e, false) (f, false)) :
    e = f := by
  obtain ⟨k, hk, hm⟩ := h
  cases k with
  | zero => exact congrArg Prod.fst hk
  | succ k =>
    have hpred : (wholePlaneRotation W H).symm (f, false) =
        (wholePlaneRotation W H ^ k) (e, false) := by
      let σ := wholePlaneRotation W H
      have hstep : (σ ^ (k + 1)) (e, false) = σ ((σ ^ k) (e, false)) :=
        Equiv.congr_fun (pow_succ' σ k) (e, false)
      exact (congrArg σ.symm (hk.symm.trans hstep)).trans (σ.symm_apply_apply _)
    have hp := hm k (by omega)
    obtain ⟨_, _, n, hn, hs, _, hgap⟩ := hf
    have hpresent : wholePlaneEdgePresent W
        ((wholePlaneRotation W H).symm (f, false)).1 := hpred.symm ▸ hp.2
    have hside : ((wholePlaneRotation W H).symm (f, false)).2 = false :=
      hpred.symm ▸ hp.1
    by_cases hn1 : n = 1
    · rw [hn1, pow_one] at hs
      exact Bool.noConfusion (hside.symm.trans hs)
    · exact (hgap 1 (by omega) (by omega) (by
        simpa only [pow_one] using hpresent)).elim




theorem wholePlaneRightmostOutgoingAt_unique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    {e f : WholePlaneEdge W} (he : wholePlaneRightmostOutgoingAt W H v e)
    (hf : wholePlaneRightmostOutgoingAt W H v f) : e = f := by
  rcases ambient_outgoing_arc W H e f he.1 hf.1 (he.2.1.trans hf.2.1.symm) with h | h
  · exact rightmost_arc_eq W H v e f hf h
  · exact (rightmost_arc_eq W H v f e he h).symm





theorem wholePlaneRightmostOutgoingAt_incoming (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    {e : WholePlaneEdge W} (he : wholePlaneRightmostOutgoingAt W H v e) :
    ∃ f : WholePlaneEdge W, wholePlaneEdgePresent W f ∧ wholePlaneEdgeEast W f = v := by
  obtain ⟨⟨N, a⟩, rfl⟩ := Quotient.exists_rep e
  obtain ⟨_, hw, k, _, hs, hp, _⟩ := he
  refine ⟨(((wholePlaneRotation W H).symm ^ k) (wholePlaneEdgeι W N a, false)).1,
    hp, ?_⟩
  have hb := rayAmbientBase_symm_pow W H N (a, false) k
  change (((wholePlaneRotation W H).symm ^ k) (wholePlaneEdgeι W N a, false)).2 = true
    at hs
  change rayAmbientBase W
    (((wholePlaneRotation W H).symm ^ k) (wholePlaneEdgeι W N a, false)) =
      wholePlaneEdgeWest W (wholePlaneEdgeι W N a) at hb
  rw [rayAmbientBase, hs] at hb
  exact hb.trans hw




structure WholePlaneRightmostRay (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) where
  vertex : ℕ → WholePlaneVertex W
  edge : ℕ → WholePlaneEdge W
  rightmost : ∀ i, wholePlaneRightmostOutgoingAt W H (vertex i) (edge i)
  target : ∀ i, wholePlaneEdgeEast W (edge i) = vertex (i + 1)




theorem wholePlaneRightmostRays_coalesce_of_common_vertex
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (P Q : WholePlaneRightmostRay W H) (i j : ℕ)
    (h : P.vertex i = Q.vertex j) :
    ∀ t, P.vertex (i + t) = Q.vertex (j + t) := by
  intro t
  induction t with
  | zero => exact h
  | succ t ih =>
    have he : P.edge (i + t) = Q.edge (j + t) := by
      apply wholePlaneRightmostOutgoingAt_unique W H (P.vertex (i + t))
        (P.rightmost (i + t))
      rw [ih]
      exact Q.rightmost (j + t)
    exact (P.target (i + t)).symm.trans
      ((congrArg (wholePlaneEdgeEast W) he).trans (Q.target (j + t)))





theorem wholePlaneRightmostOutgoingAt_existsUnique_root_terminal
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) :
    ∃! e : WholePlaneEdge W,
      wholePlaneRightmostOutgoingAt W H (wholePlaneVertexι W N 1) e := by
  obtain ⟨v, e, hv, _, hs⟩ := wholePlaneRightBoundary_rightmost_chain W H N h
  have he : wholePlaneRightmostOutgoingAt W H (wholePlaneVertexι W N 1) (e 0) := by
    rw [← hv]
    exact (hs 0).1
  exact ⟨e 0, he, fun f hf =>
    wholePlaneRightmostOutgoingAt_unique W H (wholePlaneVertexι W N 1) hf he⟩





theorem wholePlaneRightmostRay_exists_root_terminal
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) :
    ∃ P : WholePlaneRightmostRay W H,
      P.vertex 0 = wholePlaneVertexι W N 1 ∧
      ∀ j, P.edge j =
        wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) (j + 1)) := by
  obtain ⟨v, e, hv, he, hs⟩ := wholePlaneRightBoundary_rightmost_chain W H N h
  exact ⟨⟨v, e, fun j => (hs j).1, fun j => (hs j).2⟩, hv, he⟩

end DirectedDistances.KMSW
