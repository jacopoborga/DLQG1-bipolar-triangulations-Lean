module

public import DirectedDistances.KMSW.KMSWWholePlaneRotation
public import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.KMSW.KMSWWindowFreshPresence

/-! Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
14–19 missing-edge conventions): face successor and eventual present/missing status
of edges on the colimit carrier under the deterministic hypothesis
WholePlaneRotationHypothesis (a.s. discharge separate); orientation of directed edges,
β_0^{L,R}, the cut and the source identification (Q-F4c, unanswered) are not treated;
not the paper result. -/

public section
namespace DirectedDistances.KMSW

/-- including missing edges; not the paper result. -/
@[expose] def wholePlaneDartFlip (W : ℤ → Fin 3) : Equiv.Perm (WholePlaneDart W) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl

/-- vertex rotation after geometric dart reversal; not the paper result. -/
@[expose] noncomputable def wholePlaneFaceSucc (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Equiv.Perm (WholePlaneDart W) :=
  (wholePlaneRotation W H).symm * wholePlaneDartFlip W

/-- Face agreement at a cofinally fresh opposite endpoint, toward F4c -/
theorem wholePlaneFaceSucc_ι_of_fresh (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool)
    (hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (if !d.2 then edgeEast (shiftedStream W N) d.1
        else edgeWest (shiftedStream W N) d.1)) :
    wholePlaneFaceSucc W H (wholePlaneDartι W N d) =
      wholePlaneDartι W N (kmswInfFaceSucc (shiftedStream W N) (H.1 N) d) := by
  exact wholePlaneRotation_symm_ι_of_fresh W H N (d.1, !d.2) hf

private theorem window_stage_present_iff (w : ℕ → Fin 3) (s m e : ℕ) (b : Bool)
    (he : e < (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hf : (kmswStage w s).nextVertex ≤ kmswWindowVertexMapInf w s
      (if b then edgeEast (fun i => w (s + i)) e
        else edgeWest (fun i => w (s + i)) e)) :
    (kmswStage (fun i => w (s + i)) m).present e = true ↔
      (kmswStage w (s + m)).present (kmswWindowEdgeMapInf w s e) = true := by
  let u := fun i => w (s + i)
  let d : StageDart (kmswStage u m).nextEdge := (⟨e, he⟩, b)
  let v := stageEndpoint (kmswStage u m) d
  have hv : v < (kmswStage u m).nextVertex := by
    have hb := kmswStage_endpoints_lt_nextVertex u m e he
    cases b
    · exact hb.1
    · exact hb.2
  have hend : v = (if b then edgeEast u e else edgeWest u e) := by
    obtain ⟨hw, heast⟩ := edge_endpoints_eq u he
    cases b
    · exact hw
    · exact heast
  have hf' : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
    rw [← kmswWindowVertexMapInf_eq_stage w s m v hv, hend]
    exact hf
  have hp := kmswWindowDartMap_present_iff_of_fresh w s m v hv hf' d rfl
  change (kmswStage u m).present e = true ↔
    (kmswStage w (s + m)).present ((kmswWindowPatchData w s m).φ e) = true at hp
  rw [← kmswWindowEdgeMapInf_eq_stage w s m e he] at hp
  exact hp

private theorem window_present_iff (w : ℕ → Fin 3) (s e : ℕ) (b : Bool)
    (hf : (kmswStage w s).nextVertex ≤ kmswWindowVertexMapInf w s
      (if b then edgeEast (fun i => w (s + i)) e
        else edgeWest (fun i => w (s + i)) e)) :
    EdgePresent (fun i => w (s + i)) e ↔
      EdgePresent w (kmswWindowEdgeMapInf w s e) := by
  constructor
  · rintro ⟨m, he, hp⟩
    have hb := (kmswWindowPatchData_rel w s m).edge_bound e he
    rw [← kmswWindowEdgeMapInf_eq_stage w s m e he] at hb
    exact ⟨s + m, hb, (window_stage_present_iff w s m e b he hf).mp hp⟩
  · rintro ⟨n, he, hp⟩
    let m := max n e
    have he' : e < (kmswStage (fun i => w (s + i)) m).nextEdge :=
      (kmsw_edge_allocated_by_self _ e).trans_le
        (kmswStage_nextEdge_mono _ (Nat.le_max_right n e))
    have hp' := (present_mono w he hp (s + m) (by dsimp [m]; omega)).2
    exact ⟨m, he', (window_stage_present_iff w s m e b he' hf).mpr hp'⟩

/-- Presence transports when either chosen endpoint is fresh, toward F4c
endpoint is needed; not the paper result. -/
theorem wholePlaneEdgeTrans_present_iff_of_fresh (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M) (e : ℕ) (b : Bool)
    (hf : wholePlaneFresh W N M hNM
      (if b then edgeEast (shiftedStream W N) e
        else edgeWest (shiftedStream W N) e)) :
    EdgePresent (shiftedStream W N) e ↔
      EdgePresent (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M hNM]
    using window_present_iff (shiftedStream W M) (M - N) e b
      (by simpa only [wholePlaneFresh, wholePlaneVertexTrans,
        shiftedStream_shift W N M hNM] using hf)

/-- Eventual constancy of one-sided presence along each edge representative,
eventual freshness is supplied by `H`; not the paper result. -/
theorem wholePlaneEdgePresent_eventually_constant (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N e : ℕ) :
    ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
      (EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W N L (hNM.trans hML) e) ↔
        EdgePresent (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e)) := by
  obtain ⟨M, hNM, hf⟩ := H.2 N (edgeWest (shiftedStream W N) e)
  refine ⟨M, hNM, fun L hML => ?_⟩
  have hf' : wholePlaneFresh W M L hML
      (edgeWest (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e)) := by
    rw [wholePlaneEdgeTrans_west]
    exact hf L hML
  have hp := wholePlaneEdgeTrans_present_iff_of_fresh W M L hML
    (wholePlaneEdgeTrans W N M hNM e) false hf'
  rw [show wholePlaneEdgeTrans W M L hML (wholePlaneEdgeTrans W N M hNM e) =
    wholePlaneEdgeTrans W N L (hNM.trans hML) e from
      congrFun (wholePlaneEdgeTrans_comp W N M L hNM hML) e] at hp
  exact hp.symm

private def eventualPresence (W : ℤ → Fin 3) (N e : ℕ) : Prop :=
  ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
    EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W N L (hNM.trans hML) e)

private theorem eventualPresence_trans (W : ℤ → Fin 3) (N M : ℕ)
    (hNM : N ≤ M) (e : ℕ) :
    eventualPresence W M (wholePlaneEdgeTrans W N M hNM e) ↔
      eventualPresence W N e := by
  constructor
  · rintro ⟨L, hML, hp⟩
    refine ⟨L, hNM.trans hML, fun K hLK => ?_⟩
    rw [← congrFun (wholePlaneEdgeTrans_comp W N M K hNM (hML.trans hLK)) e]
    exact hp K hLK
  · rintro ⟨L, hNL, hp⟩
    refine ⟨max M L, Nat.le_max_left M L, fun K hK => ?_⟩
    have hc := congrFun (wholePlaneEdgeTrans_comp W N M K hNM
      ((Nat.le_max_left M L).trans hK)) e
    change wholePlaneEdgeTrans W M K ((Nat.le_max_left M L).trans hK)
      (wholePlaneEdgeTrans W N M hNM e) = _ at hc
    rw [hc]
    exact hp K ((Nat.le_max_right M L).trans hK)

private theorem eventualPresence_rel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    eventualPresence W a.1 a.2 = eventualPresence W b.1 b.2 := by
  obtain ⟨M, ha, hb, he⟩ := hab
  apply propext
  apply (eventualPresence_trans W a.1 M ha a.2).symm.trans
  rw [he]
  exact eventualPresence_trans W b.1 M hb b.2





@[expose] def wholePlaneEdgePresent (W : ℤ → Fin 3) : WholePlaneEdge W → Prop :=
  Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
      EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W a.1 L (hNM.trans hML) a.2))
    (by
      intro a b hab
      exact eventualPresence_rel W a b hab)

/-- Representative-independent tail characterization toward F4c -/
theorem wholePlaneEdgePresent_ι (W : ℤ → Fin 3) (N e : ℕ) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N e) ↔
      ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
        EdgePresent (shiftedStream W L)
          (wholePlaneEdgeTrans W N L (hNM.trans hML) e) := Iff.rfl

/-- Agreement at any representative with a cofinally fresh chosen endpoint, -/
theorem wholePlaneEdgePresent_ι_of_fresh (W : ℤ → Fin 3) (N e : ℕ) (b : Bool)
    (hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (if b then edgeEast (shiftedStream W N) e
        else edgeWest (shiftedStream W N) e)) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N e) ↔
      EdgePresent (shiftedStream W N) e := by
  rw [wholePlaneEdgePresent_ι]
  constructor
  · rintro ⟨M, hNM, hp⟩
    exact (wholePlaneEdgeTrans_present_iff_of_fresh W N M hNM e b (hf M hNM)).mpr
      (hp M (Nat.le_refl M))
  · intro hp
    exact ⟨N, Nat.le_refl N, fun M hNM =>
      (wholePlaneEdgeTrans_present_iff_of_fresh W N M hNM e b (hf M hNM)).mp hp⟩

/-- Every edge representative eventually agrees with the colimit presence status, -/
theorem wholePlaneEdgePresent_eventually (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N e : ℕ) :
    ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
      (EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W N L (hNM.trans hML) e) ↔
        wholePlaneEdgePresent W (wholePlaneEdgeι W N e)) := by
  obtain ⟨M, hNM, hc⟩ := wholePlaneEdgePresent_eventually_constant W H N e
  have hs : wholePlaneEdgePresent W (wholePlaneEdgeι W N e) ↔
      EdgePresent (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e) := by
    rw [wholePlaneEdgePresent_ι]
    constructor
    · rintro ⟨K, hNK, hp⟩
      exact (hc (max M K) (Nat.le_max_left M K)).mp
        (hp (max M K) (Nat.le_max_right M K))
    · intro hp
      exact ⟨M, hNM, fun L hML => (hc L hML).mpr hp⟩
  exact ⟨M, hNM, fun L hML => (hc L hML).trans hs.symm⟩

end DirectedDistances.KMSW
