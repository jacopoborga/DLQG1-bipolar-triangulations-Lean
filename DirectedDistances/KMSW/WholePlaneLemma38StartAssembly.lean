module

public import DirectedDistances.KMSW.WholePlaneLemma38Assembly
public import DirectedDistances.KMSW.WholePlaneShiftTransfer

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk







theorem wholePlaneLeftBoundary_leftmost_chain_start (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (h : BoundaryHitWitnesses (shiftedStream (shiftWord W n) 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent (shiftWord W n)
      (wholePlaneEdgeι (shiftWord W n) 0
        (kmswLLCreatedEdge (shiftedStream (shiftWord W n) 0)
          (boundaryHitTime (shiftedStream (shiftWord W n) 0) h (k - 1))))) :
    ∃ (v : ℕ → WholePlaneVertex W) (e : ℕ → WholePlaneEdge W),
      v 0 = wholePlaneVertexι W 0
        (kmswWindowVertexMapInf (shiftedStream W 0) n 0) ∧
      (∀ j : ℕ, e j = wholePlaneEdgeι W 0
        (kmswWindowEdgeMapInf (shiftedStream W 0) n
          (kmswLLCreatedEdge (shiftedStream (shiftWord W n) 0)
            (boundaryHitTime (shiftedStream (shiftWord W n) 0) h (-(j : ℤ) - 1))))) ∧
      ∀ j : ℕ, wholePlaneLeftmostIncomingAt W H (v j) (e j) ∧
        wholePlaneEdgeWest W (e j) = v (j + 1) := by
  obtain ⟨v', e', hvzero, he', hchain⟩ :=
    wholePlaneLeftBoundary_leftmost_chain (shiftWord W n) H' 0 h hLL
  let v := fun j => (wholePlaneVertexShiftEquiv W n).symm (v' j)
  let e := fun j => (wholePlaneEdgeShiftEquiv W n).symm (e' j)
  have hv (j : ℕ) : wholePlaneVertexShift W n (v j) = v' j :=
    (wholePlaneVertexShiftEquiv W n).apply_symm_apply _
  have he (j : ℕ) : wholePlaneEdgeShift W n (e j) = e' j :=
    (wholePlaneEdgeShiftEquiv W n).apply_symm_apply _
  refine ⟨v, e, ?_, ?_, ?_⟩
  · apply (wholePlaneVertexShift_bijective W n).1
    rw [wholePlaneVertexShift_runEmbed, hv, hvzero]
  · intro j
    apply (wholePlaneEdgeShift_bijective W n).1
    rw [wholePlaneEdgeShift_runEmbed, he, he']
  · intro j
    constructor
    · apply (wholePlaneLeftmostIncomingAt_shift W n H H' _ _).mpr
      rw [hv, he]
      exact (hchain j).1
    · apply (wholePlaneVertexShift_bijective W n).1
      rw [← wholePlaneEdgeShift_west, he, hv]
      exact (hchain j).2

private theorem edge_present_start_iff (W : ℤ → Fin 3) (n e : ℕ) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W 0
      (kmswWindowEdgeMapInf (shiftedStream W 0) n e)) ↔
      wholePlaneEdgePresent (shiftWord W n) (wholePlaneEdgeι (shiftWord W n) 0 e) := by
  rw [← wholePlaneEdgeShift_runEmbed W n e, wholePlaneEdgePresent_shift]






theorem wholePlaneBoundary_edges_present_start (W : ℤ → Fin 3) (n : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream (shiftWord W n) 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent (shiftWord W n)
      (wholePlaneEdgeι (shiftWord W n) 0
        (kmswLLCreatedEdge (shiftedStream (shiftWord W n) 0)
          (boundaryHitTime (shiftedStream (shiftWord W n) 0) h (k - 1))))) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W 0
      (kmswWindowEdgeMapInf (shiftedStream W 0) n 0)) ∧
    (∀ j : ℕ, wholePlaneEdgePresent W (wholePlaneEdgeι W 0
      (kmswWindowEdgeMapInf (shiftedStream W 0) n
        (kmswRightBoundaryEdge (shiftedStream (shiftWord W n) 0) j)))) ∧
    (∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W (wholePlaneEdgeι W 0
      (kmswWindowEdgeMapInf (shiftedStream W 0) n
        (kmswLLCreatedEdge (shiftedStream (shiftWord W n) 0)
          (boundaryHitTime (shiftedStream (shiftWord W n) 0) h (k - 1)))))) := by
  refine ⟨(edge_present_start_iff W n 0).mpr
    (wholePlaneRootEdge_present (shiftWord W n) 0), ?_, ?_⟩
  · intro j
    exact (edge_present_start_iff W n _).mpr
      (wholePlaneRightBoundaryEdge_present (shiftWord W n) 0 h j)
  · intro k hk
    exact (edge_present_start_iff W n _).mpr (hLL k hk)






theorem wholePlaneIID_ae_lemma38_clauses_start :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W, ∀ n : ℕ,
        let u := fun i : ℕ => W ((i : ℤ) + n)
        ∃ h : BoundaryHitWitnesses u,
          (∃ v : ℕ → WholePlaneVertex W, ∃ e : ℕ → WholePlaneEdge W,
            v 0 = wholePlaneVertexι W 0
              (kmswWindowVertexMapInf (shiftedStream W 0) n 1) ∧
            (∀ j : ℕ, e j = wholePlaneEdgeι W 0
              (kmswWindowEdgeMapInf (shiftedStream W 0) n
                (kmswRightBoundaryEdge u (j + 1)))) ∧
            ∀ j : ℕ, wholePlaneRightmostOutgoingAt W H (v j) (e j) ∧
              wholePlaneEdgeEast W (e j) = v (j + 1)) ∧
          wholePlaneEdgePresent W (wholePlaneEdgeι W 0
            (kmswWindowEdgeMapInf (shiftedStream W 0) n 0)) ∧
          (∀ j : ℕ, wholePlaneEdgePresent W (wholePlaneEdgeι W 0
            (kmswWindowEdgeMapInf (shiftedStream W 0) n (kmswRightBoundaryEdge u j)))) ∧
          (∀ k : ℤ, k ≤ 0 →
            wholePlaneEdgePresent W (wholePlaneEdgeι W 0
              (kmswWindowEdgeMapInf (shiftedStream W 0) n
                (kmswLLCreatedEdge u (boundaryHitTime u h (k - 1))))) ∧
            ¬ EdgePresent u (kmswLLCreatedEdge u (boundaryHitTime u h (k - 1)))) ∧
          (∃ v : ℕ → WholePlaneVertex W, ∃ e : ℕ → WholePlaneEdge W,
            v 0 = wholePlaneVertexι W 0
              (kmswWindowVertexMapInf (shiftedStream W 0) n 0) ∧
            (∀ j : ℕ, e j = wholePlaneEdgeι W 0
              (kmswWindowEdgeMapInf (shiftedStream W 0) n
                (kmswLLCreatedEdge u (boundaryHitTime u h (-(j : ℤ) - 1))))) ∧
            ∀ j : ℕ, wholePlaneLeftmostIncomingAt W H (v j) (e j) ∧
              wholePlaneEdgeWest W (e j) = v (j + 1)) ∧
          {e | ∃ n₀, ∀ m ≥ n₀, e ∈ (kmswStage u m).LR} =
            Set.range (fun j : ℕ => kmswRightBoundaryEdge u j) ∧
          {e | ∃ n₀, ∀ m ≥ n₀, e ∈ (kmswStage u m).LL} =
            Set.range (fun j : ℕ =>
              kmswLLCreatedEdge u (boundaryHitTime u h (-((j : ℤ) + 1)))) ∧
          Disjoint
            {e | ∃ n₀, ∀ m ≥ n₀, e ∈ (kmswStage u m).LR}
            {e | ∃ n₀, ∀ m ≥ n₀, e ∈ (kmswStage u m).LL} ∧
          (∀ v, (∃ m, v < (kmswStage u m).nextVertex) →
            (∃ e, EdgePresent u e ∧ edgeWest u e = v) ∧
            ((¬ ∃ e, EdgePresent u e ∧ edgeEast u e = v) ↔
              ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex u h k)) ∧
          (∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay W H),
            P.vertex 0 = wholePlaneVertexι W 0
              (kmswWindowVertexMapInf (shiftedStream W 0) n (boundaryVertex u h k)) →
            Q.vertex 0 = wholePlaneVertexι W 0
              (kmswWindowVertexMapInf (shiftedStream W 0) n (boundaryVertex u h k')) →
            ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t)) := by
  have hzero := wholePlaneIID_ae_lemma38_clauses.mono
    (fun _ hW => Exists.imp (fun _ hH => hH 0) hW)
  have hall := wholePlaneIID_ae_shift_all _ hzero
  filter_upwards [wholePlaneIID_ae_rotationHypothesis, hall] with W H hh
  refine ⟨H, fun n => ?_⟩
  dsimp only
  rw [integerRun_eq_shiftedStream_zero W (n : ℤ)]
  have hn := hh (n : ℤ)
  change ∃ H' : WholePlaneRotationHypothesis (shiftWord W n), _ at hn
  obtain ⟨H', h, _hrightChain, _hroot, _hrightPresent, hmissing,
    _hleftChain, hLR, hLLset, hdisjoint, hdegree, _hcoalesce⟩ := hn
  have hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent (shiftWord W n)
      (wholePlaneEdgeι (shiftWord W n) 0
        (kmswLLCreatedEdge (shiftedStream (shiftWord W n) 0)
          (boundaryHitTime (shiftedStream (shiftWord W n) 0) h (k - 1)))) :=
    fun k hk => (hmissing k hk).1
  obtain ⟨hroot, hright, hleft⟩ := wholePlaneBoundary_edges_present_start W n h hLL
  refine ⟨h, wholePlaneRightBoundary_rightmost_chain_start W n H H' h,
    hroot, hright, ?_, wholePlaneLeftBoundary_leftmost_chain_start W n H H' h hLL,
    hLR, hLLset, hdisjoint, hdegree, ?_⟩
  · intro k hk
    exact ⟨hleft k hk, (hmissing k hk).2⟩
  · intro k k' P Q hP hQ
    obtain ⟨s, s', _hs, _hs', ht⟩ :=
      wholePlaneRightmostRays_coalesce_from_boundary_start W n H H' h hLL
        k k' P Q hP hQ
    exact ⟨s, s', ht⟩

end DirectedDistances.KMSW
