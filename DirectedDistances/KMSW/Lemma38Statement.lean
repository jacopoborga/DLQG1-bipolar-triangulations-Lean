module

public import DirectedDistances.KMSW.Lemma38SourceZero
public import DirectedDistances.KMSW.Lemma38DegreeZero
public import DirectedDistances.KMSW.RunRightmostCoalesce
public import DirectedDistances.KMSW.RunRightmostRootTie
public import DirectedDistances.KMSW.WholePlaneLemma38IntegerStart
public import DirectedDistances.KMSW.WholePlaneStartIsoTransport
public import DirectedDistances.KMSW.WholePlaneIntegerRuns
import DirectedDistances.KMSW.WholePlaneBoundaryRayCoalescence

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open DirectedDistances.PlanarMap




theorem kmswRunRightmostRay_proof_independent (w : ℕ → Fin 3)
    (hf hf' : KMSWFiniteIncidence w) :
    KMSWRunRightmostRay w hf = KMSWRunRightmostRay w hf' := rfl



theorem kmswRunRightmostOutAt_proof_independent (w : ℕ → Fin 3)
    (hf hf' : KMSWFiniteIncidence w) (v e : ℕ) :
    kmswRunRightmostOutAt w hf v e ↔ kmswRunRightmostOutAt w hf' v e := Iff.rfl




theorem lemma38_incident_present_of_incoming (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : ℕ)
    (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v)
    (d : ℕ × Bool) (hd : kmswLimitDartVertex w d = v) :
    EdgePresent w d.1 := by
  classical
  by_contra hm
  have hLL := (m0Cut_not_present_iff_eventually_LL w h d.1).mp hm
  have hrange : d.1 ∈ Set.range (fun j : ℕ =>
      kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
    rw [← kmswRunEventuallyLL_eq_range w h]
    exact hLL
  obtain ⟨j, hj⟩ := hrange
  let k : ℤ := -((j : ℤ) + 1)
  have hk : k ≤ -1 := by dsimp [k]; omega
  have heq : boundaryOuterEdge w h k = d.1 :=
    (boundaryOuterEdge_of_negative w h hk).trans hj
  have hend := boundaryOuterEdge_endpoints w h k
  rw [heq] at hend
  obtain ⟨f, hf, hfv⟩ := hin
  cases hb : d.2
  · have hw : edgeWest w d.1 = v := by
      simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte] using hd
    exact boundaryVertex_nonpos_no_incoming w h (by omega : k ≤ 0) f hf
      (hfv.trans (hw.symm.trans hend.1))
  · have he : edgeEast w d.1 = v := by
      simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using hd
    exact boundaryVertex_nonpos_no_incoming w h (by omega : k + 1 ≤ 0) f hf
      (hfv.trans (he.symm.trans hend.2.1))





theorem kmswRunRightmostOutAt_iff_clockwise_incoming (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w) (v e : ℕ)
    (hin : ∃ f, EdgePresent w f ∧ edgeEast w f = v) :
    kmswRunRightmostOutAt w hfin v e ↔
      EdgePresent w e ∧ edgeWest w e = v ∧
        ∃ f, EdgePresent w f ∧ edgeEast w f = v ∧
          (kmswInfRot w hfin).symm (e, false) = (f, true) := by
  have hvertex (he : edgeWest w e = v) :
      kmswLimitDartVertex w ((kmswInfRot w hfin).symm (e, false)) = v := by
    have hr := kmswLimitDartVertex_rot w hfin
      ((kmswInfRot w hfin).symm (e, false))
    rw [Equiv.apply_symm_apply] at hr
    exact hr.symm.trans he
  constructor
  · rintro ⟨hp, he, k, hk, hstop, hgap⟩
    have hd := hvertex he
    have hpresent := lemma38_incident_present_of_incoming w h v hin _ hd
    have hk1 : k = 1 := by
      by_contra hne
      have hbad := hgap 1 (by omega) (by omega)
      simp only [pow_one] at hbad
      exact hbad hpresent
    rw [hk1, pow_one] at hstop
    have hb : ((kmswInfRot w hfin).symm (e, false)).2 = true := by
      cases hb' : ((kmswInfRot w hfin).symm (e, false)).2
      · exact (hstop ⟨hb', hpresent⟩).elim
      · rfl
    refine ⟨hp, he, ((kmswInfRot w hfin).symm (e, false)).1, hpresent, ?_, ?_⟩
    · simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using hd
    · exact Prod.ext rfl hb
  · rintro ⟨hp, he, f, _hf, _hfv, hrot⟩
    refine ⟨hp, he, 1, by omega, ?_, ?_⟩
    · rw [pow_one, hrot]
      simp only [futureMapTail, Bool.true_eq_false, false_and, not_false_eq_true]
    · intro j hj hj1
      omega




@[expose] def RunBoundaryVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ e ∈ kmswRunBoundaryEdges w, edgeWest w e = v ∨ edgeEast w e = v



theorem runBoundaryVertex_iff_mem_range (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : ℕ) :
    RunBoundaryVertex w v ↔ v ∈ Set.range (boundaryVertex w h) := by
  rw [RunBoundaryVertex, kmswRunBoundaryEdges_eq_boundaryOuterEdgeSet w h,
    ← boundaryOuterEdge_range w h]
  constructor
  · rintro ⟨e, ⟨k, rfl⟩, hv | hv⟩
    · exact ⟨k, (boundaryOuterEdge_endpoints w h k).1.symm.trans hv⟩
    · exact ⟨k + 1, (boundaryOuterEdge_endpoints w h k).2.1.symm.trans hv⟩
  · rintro ⟨k, rfl⟩
    exact ⟨boundaryOuterEdge w h k, ⟨k, rfl⟩,
      Or.inl (boundaryOuterEdge_endpoints w h k).1⟩



theorem lemma38_boundary_vertices_zero
    (V : ℤ → Fin 3) (H : WholePlaneRotationHypothesis V)
    (h : BoundaryHitWitnesses (shiftedStream V 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent V
      (wholePlaneEdgeι V 0
        (kmswLLCreatedEdge (shiftedStream V 0)
          (boundaryHitTime (shiftedStream V 0) h (k - 1)))))
    (P : WholePlaneRightmostRay V H)
    (hP : P.vertex 0 = wholePlaneEdgeEast V (m0CutLambdaZero V))
    (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V (m0CutLambdaZero V))) :
    wholePlaneVertexι V 0 '' {v | RunBoundaryVertex (shiftedStream V 0) v} =
      Set.range P.vertex ∪ Set.range Q.vertex := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, rfl⟩ := (runBoundaryVertex_iff_mem_range _ h v).mp hv
    by_cases hk : 1 ≤ k
    · left
      refine ⟨(k - 1).toNat, ?_⟩
      rw [m0Cut_betaR_vertices V H h P hP]
      have hi : ((k - 1).toNat : ℤ) + 1 = k := by omega
      rw [hi]
    · right
      refine ⟨(-k).toNat, ?_⟩
      rw [m0Cut_betaL_vertices V H h hLL Q]
      have hi : -((-k).toNat : ℤ) = k := by omega
      rw [hi]
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨boundaryVertex (shiftedStream V 0) h ((j : ℤ) + 1), ?_, ?_⟩
      · exact (runBoundaryVertex_iff_mem_range _ h _).mpr ⟨(j : ℤ) + 1, rfl⟩
      · exact (m0Cut_betaR_vertices V H h P hP j).symm
    · refine ⟨boundaryVertex (shiftedStream V 0) h (-(j : ℤ)), ?_, ?_⟩
      · exact (runBoundaryVertex_iff_mem_range _ h _).mpr ⟨-(j : ℤ), rfl⟩
      · exact (m0Cut_betaL_vertices V H h hLL Q j).symm



private theorem lemma38_ambient_ray_exists_active
    (V : ℤ → Fin 3) (H : WholePlaneRotationHypothesis V) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream V N)) (t : ℕ) :
    ∃ P : WholePlaneRightmostRay V H,
      P.vertex 0 = wholePlaneVertexι V N
        (edgeEast (shiftedStream V N) (act (shiftedStream V N) t)) := by
  classical
  let w := shiftedStream V N
  let next := fun a => Classical.choose
    (wholePlaneRightmost_descent_at_active V H N h.R_unbounded_below a)
  have hn (a : ℕ) := Classical.choose_spec
    (wholePlaneRightmost_descent_at_active V H N h.R_unbounded_below a)
  let times : ℕ → ℕ := fun i => Nat.rec t (fun _ a => next a) i
  let P : WholePlaneRightmostRay V H := {
    vertex := fun i => wholePlaneVertexι V N (edgeEast w (act w (times i)))
    edge := fun i => wholePlaneEdgeι V N (act w (times (i + 1)))
    rightmost := fun i => (hn (times i)).2.2.2.2
    target := fun i => wholePlaneEdgeEast_ι V N (act w (times (i + 1))) }
  exact ⟨P, rfl⟩





theorem lemma38_ambient_ray_exists_boundary
    (V : ℤ → Fin 3) (H : WholePlaneRotationHypothesis V)
    (h : BoundaryHitWitnesses (shiftedStream V 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent V
      (wholePlaneEdgeι V 0
        (kmswLLCreatedEdge (shiftedStream V 0)
          (boundaryHitTime (shiftedStream V 0) h (k - 1)))))
    (x : ℕ) (hx : RunBoundaryVertex (shiftedStream V 0) x) :
    ∃ P : WholePlaneRightmostRay V H, P.vertex 0 = wholePlaneVertexι V 0 x := by
  classical
  obtain ⟨k, hk⟩ := (runBoundaryVertex_iff_mem_range _ h x).mp hx
  by_cases hk0 : k ≤ 0
  · obtain ⟨M, hM, t, ht⟩ :=
      wholePlane_leftBoundary_vertex_terminal V 0 h k hk0 (hLL k hk0)
    obtain ⟨P, hP⟩ := lemma38_ambient_ray_exists_active V H M
      (boundaryHitWitnesses_of_le V hM h) t
    exact ⟨P, hP.trans (ht.symm.trans (congrArg (wholePlaneVertexι V 0) hk))⟩
  · obtain ⟨B, hB, _, _⟩ :=
      wholePlaneRightmostRay_exists_rightBoundary_chain V H 0 h
    let j := (k - 1).toNat
    let P : WholePlaneRightmostRay V H := {
      vertex := fun i => B.vertex (j + i)
      edge := fun i => B.edge (j + i)
      rightmost := fun i => B.rightmost (j + i)
      target := fun i => by
        simpa only [Nat.add_assoc] using B.target (j + i) }
    refine ⟨P, ?_⟩
    change B.vertex (j + 0) = wholePlaneVertexι V 0 x
    rw [hB]
    have hj : ((j + 0 + 1 : ℕ) : ℤ) = k := by dsimp [j]; omega
    rw [hj, hk]

























@[expose] def Lemma38At (V : ℤ → Fin 3) : Prop :=
  ∃ (H : WholePlaneRotationHypothesis V)
    (_h : BoundaryHitWitnesses (shiftedStream V 0)),
    let w := shiftedStream V 0
    let incl := wholePlaneEdgeι V 0
    let lam := m0CutLambdaZero V
    ∃ (P : WholePlaneRightmostRay V H)
      (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam)),
      lam = wholePlaneEdgeι V 0 0 ∧
      P.vertex 0 = wholePlaneEdgeEast V lam ∧
      (∀ P' : WholePlaneRightmostRay V H,
        P'.vertex 0 = wholePlaneEdgeEast V lam →
          P'.vertex = P.vertex ∧ P'.edge = P.edge) ∧
      (∀ Q' : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam),
        Q'.vertex = Q.vertex ∧ Q'.edge = Q.edge) ∧
      incl '' kmswRunBoundaryEdges w =
        {lam} ∪ Set.range P.edge ∪ Set.range Q.edge ∧
      (∀ v : ℕ, RunBoundaryVertex w v ↔
        wholePlaneVertexι V 0 v ∈ Set.range P.vertex ∪ Set.range Q.vertex) ∧
      EdgePresent w 0 ∧
      (∀ e ∈ kmswRunBoundaryEdges w,
        (incl e ∈ ({lam} ∪ Set.range P.edge) → EdgePresent w e) ∧
        (incl e ∈ Set.range Q.edge → ¬ EdgePresent w e)) ∧
      (∀ j : ℕ, wholePlaneEdgePresent V (Q.edge j) ∧
        wholePlaneLeftmostIncomingAt V H (Q.vertex j) (Q.edge j) ∧
        wholePlaneEdgeEast V (Q.edge j) = Q.vertex j) ∧
      (∀ j : ℕ, wholePlaneEdgeWest V (Q.edge j) = Q.vertex (j + 1)) ∧
      (∀ v : ℕ,
        (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
        ((∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
          wholePlaneVertexι V 0 v ∉ Set.range Q.vertex)) ∧
      (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0), R.vertex 0 = v) ∧
      (∀ R R' : KMSWRunRightmostRay w (H.1 0),
        R.vertex 0 = R'.vertex 0 → R.vertex = R'.vertex ∧ R.edge = R'.edge) ∧
      (∀ R : KMSWRunRightmostRay w (H.1 0),
        wholePlaneVertexι V 0 (R.vertex 0) = P.vertex 0 →
          ∀ i, wholePlaneVertexι V 0 (R.vertex i) = P.vertex i ∧
            incl (R.edge i) = P.edge i) ∧
      (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
        ∀ R R' : KMSWRunRightmostRay w (H.1 0),
          R.vertex 0 = x → R'.vertex 0 = x' →
            ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
              R.vertex (s + t) = R'.vertex (s' + t) ∧
              R.edge (s + t) = R'.edge (s' + t)) ∧
      (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
        ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
          edgeWest w e = x → edgeWest w e' = x' →
          ∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
              ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                R.vertex (s - 1 + t) = R'.vertex (s' - 1 + t) ∧
                R.edge (s - 1 + t) = R'.edge (s' - 1 + t)) ∧
      (∀ x : ℕ, RunBoundaryVertex w x →
        ∃ P1 : WholePlaneRightmostRay V H,
          P1.vertex 0 = wholePlaneVertexι V 0 x) ∧
      (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
        ∀ P1 P2 : WholePlaneRightmostRay V H,
          P1.vertex 0 = wholePlaneVertexι V 0 x →
          P2.vertex 0 = wholePlaneVertexι V 0 x' →
            ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
              P1.vertex (s + t) = P2.vertex (s' + t))




theorem lemma38At_of_hyps
    (V : ℤ → Fin 3) (H : WholePlaneRotationHypothesis V)
    (h : BoundaryHitWitnesses (shiftedStream V 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent V
      (wholePlaneEdgeι V 0
        (kmswLLCreatedEdge (shiftedStream V 0)
          (boundaryHitTime (shiftedStream V 0) h (k - 1))))) :
    Lemma38At V := by
  classical
  let w := shiftedStream V 0
  obtain ⟨_, ⟨P, hP⟩, Q, _⟩ := kmswRunBoundaryEdges_sourceZero_seam V H h hLL
  obtain ⟨hroot, hright, hPedge, hrightImage, hmissing, hleftPresent,
    hQedge, hleftImage⟩ := kmswRunBoundaryEdges_sourceZero_status V H h hLL P hP Q
  have hboundary : wholePlaneEdgeι V 0 '' kmswRunBoundaryEdges w =
      {m0CutLambdaZero V} ∪ Set.range P.edge ∪ Set.range Q.edge := by
    rw [kmswRunBoundaryEdges_eq_eventuallyStacks w h, Set.image_union,
      hleftImage, hrightImage, Set.union_comm]
  have hdegree := lemma38_degree_zero V H h hLL Q
  refine ⟨H, h, P, Q, rfl, hP, ?_, ?_, hboundary, ?_, hroot,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P' hP'
    exact m0Cut_betaR_unique V H P' P hP' hP
  · intro Q'
    exact m0Cut_betaL_unique V H h hLL Q' Q
  · intro v
    have hb := lemma38_boundary_vertices_zero V H h hLL P hP Q
    constructor
    · intro hv
      rw [← hb]
      exact Set.mem_image_of_mem _ hv
    · intro hv
      rw [← hb] at hv
      obtain ⟨v', hv', heq⟩ := hv
      have he : v' = v := wholePlaneVertexι_injective V 0 heq
      exact he ▸ hv'
  · intro e _he
    constructor
    · rintro (he | ⟨j, hj⟩)
      · have he0 : e = 0 := wholePlaneEdgeι_injective V 0 he
        rw [he0]
        exact hroot
      · have heq : kmswRightBoundaryEdge w (j + 1) = e :=
          wholePlaneEdgeι_injective V 0 ((hPedge j).symm.trans hj)
        rw [← heq]
        exact hright j
    · rintro ⟨j, hj⟩
      have heq : kmswLLCreatedEdge w
          (boundaryHitTime w h (-((j : ℤ) + 1))) = e :=
        wholePlaneEdgeι_injective V 0 ((hQedge j).symm.trans hj)
      rw [← heq]
      exact hmissing j
  · intro j
    exact ⟨hleftPresent j, Q.leftmost j, (Q.leftmost j).2.1⟩
  · exact Q.westEndpoint
  · intro v
    refine ⟨hdegree.1 v, ?_⟩
    have hi := not_congr (hdegree.2.1 v)
    simpa only [not_not] using hi
  · intro v
    exact kmswRunRightmostRay_exists' V H h hLL Q v
  · intro R R' hR
    have hh := kmswRunRightmostRays_agree_full_after_common_vertex R R' 0 0 hR
    constructor
    · funext i
      simpa only [Nat.zero_add] using (hh i).1
    · funext i
      simpa only [Nat.zero_add] using (hh i).2
  · intro R hR
    have hstart : R.vertex 0 = boundaryVertex w h 1 :=
      wholePlaneVertexι_injective V 0
        (hR.trans (hP.trans (m0Cut_lambdaZero_endpoints V h).2))
    exact kmswRunRightmostRay_tied_to_ambient V H h R hstart P hP
  · intro x x' _hx _hx' R R' _hR _hR'
    exact kmswRunRightmostRays_coalesce w (H.1 0) h R R'
  · intro x x' _hx _hx' e e' _he _he' _hw _hw' R R' _hR _hR'
    obtain ⟨s, s', hs, hs', htail⟩ :=
      kmswRunRightmostRays_coalesce w (H.1 0) h R R'
    refine ⟨s + 1, s' + 1, by omega, by omega, ?_⟩
    simpa only [Nat.add_sub_cancel] using htail
  · exact lemma38_ambient_ray_exists_boundary V H h hLL
  · intro x x' hx hx' P1 P2 hP1 hP2
    obtain ⟨k, hk⟩ := (runBoundaryVertex_iff_mem_range w h x).mp hx
    obtain ⟨k', hk'⟩ := (runBoundaryVertex_iff_mem_range w h x').mp hx'
    exact wholePlaneRightmostRays_coalesce_from_boundary_pos V H 0 h hLL k k' P1 P2
      (hP1.trans (congrArg (wholePlaneVertexι V 0) hk.symm))
      (hP2.trans (congrArg (wholePlaneVertexι V 0) hk'.symm))


















theorem lemma38_uibot_bdy_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      Lemma38At (shiftWordInt W n) ∧ Nonempty (WholePlaneStartIso W n) := by
  have hzero : ∀ᵐ V ∂wholePlaneIIDCodeMeasure, Lemma38At V := by
    filter_upwards [wholePlaneIID_ae_lemma38_integer_starts] with V hV
    obtain ⟨H, hall⟩ := hV
    have hstart := hall 0
    have hstream : lemma38StartStream V 0 = shiftedStream V 0 :=
      lemma38StartStream_eq_shifted V 0 le_rfl
    rw [hstream] at hstart
    obtain ⟨h, _, _, _, hmissing, _⟩ := hstart
    apply lemma38At_of_hyps V H h
    intro k hk
    have hp := (hmissing k hk).1
    simpa only [lemma38StartEdgeι, le_refl, ↓reduceIte, Int.natAbs_zero] using hp
  filter_upwards [wholePlaneIID_ae_shift_all Lemma38At hzero] with W hW
  intro n
  exact ⟨hW n, wholePlaneStartIso_nonempty W n⟩

end DirectedDistances.KMSW
