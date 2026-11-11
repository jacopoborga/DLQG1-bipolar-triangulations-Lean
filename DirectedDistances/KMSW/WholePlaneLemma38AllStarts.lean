module

public import DirectedDistances.KMSW.WholePlaneLemma38Faithful

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

/- Single probability-one event toward Lemma 3.10 (lem-uibot-bdy; original
(n = −N ≤ 0 and n ≥ 0), positive coalescence shifts. The iid-scope (probability-one scope) versioned
(eventual LL/LR stack sets; see RunInfDartPartition) and the whole-plane carrier

| Conjunct | Lemma 3.10 source sentences | Helper |
|---|---|---|
| Every N : ℕ | 210: boundary paths and present/missing statuses; 212: incidence;
  212: coalescence with s,s' > 0 | wholePlaneIID_ae_lemma38_clauses_pos |
| Every n : ℕ | 210: boundary paths and present/missing statuses; 212: incidence;
  212: coalescence with s,s' > 0 | wholePlaneIID_ae_lemma38_clauses_start_pos | -/
theorem wholePlaneIID_ae_lemma38_all_starts :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
        (∀ N : ℕ,
          ∃ h : BoundaryHitWitnesses (shiftedStream W N),
            (∃ v : ℕ → WholePlaneVertex W, ∃ e : ℕ → WholePlaneEdge W,
              v 0 = wholePlaneVertexι W N 1 ∧
                (∀ j : ℕ, e j = wholePlaneEdgeι W N
                  (kmswRightBoundaryEdge (shiftedStream W N) (j + 1))) ∧
                ∀ j : ℕ, wholePlaneRightmostOutgoingAt W H (v j) (e j) ∧
                  wholePlaneEdgeEast W (e j) = v (j + 1)) ∧
            wholePlaneEdgePresent W (wholePlaneEdgeι W N 0) ∧
            (∀ j : ℕ, wholePlaneEdgePresent W
              (wholePlaneEdgeι W N
                (kmswRightBoundaryEdge (shiftedStream W N) j))) ∧
            (∀ k : ℤ, k ≤ 0 →
              wholePlaneEdgePresent W
                (wholePlaneEdgeι W N
                  (kmswLLCreatedEdge (shiftedStream W N)
                    (boundaryHitTime (shiftedStream W N) h (k - 1)))) ∧
              ¬ EdgePresent (shiftedStream W N)
                (kmswLLCreatedEdge (shiftedStream W N)
                  (boundaryHitTime (shiftedStream W N) h (k - 1)))) ∧
            (∃ v : ℕ → WholePlaneVertex W, ∃ e : ℕ → WholePlaneEdge W,
              v 0 = wholePlaneVertexι W N 0 ∧
                (∀ j : ℕ, e j = wholePlaneEdgeι W N
                  (kmswLLCreatedEdge (shiftedStream W N)
                    (boundaryHitTime (shiftedStream W N) h (-(j : ℤ) - 1)))) ∧
                ∀ j : ℕ, wholePlaneLeftmostIncomingAt W H (v j) (e j) ∧
                  wholePlaneEdgeWest W (e j) = v (j + 1)) ∧
            {e | ∃ n₀, ∀ n ≥ n₀, e ∈ (kmswStage (shiftedStream W N) n).LR} =
              Set.range (fun j : ℕ =>
                kmswRightBoundaryEdge (shiftedStream W N) j) ∧
            {e | ∃ n₀, ∀ n ≥ n₀, e ∈ (kmswStage (shiftedStream W N) n).LL} =
              Set.range (fun j : ℕ => kmswLLCreatedEdge (shiftedStream W N)
                (boundaryHitTime (shiftedStream W N) h (-((j : ℤ) + 1)))) ∧
            Disjoint
              {e | ∃ n₀, ∀ n ≥ n₀,
                e ∈ (kmswStage (shiftedStream W N) n).LR}
              {e | ∃ n₀, ∀ n ≥ n₀,
                e ∈ (kmswStage (shiftedStream W N) n).LL} ∧
            (∀ v, (∃ m, v < (kmswStage (shiftedStream W N) m).nextVertex) →
              (∃ e, EdgePresent (shiftedStream W N) e ∧
                edgeWest (shiftedStream W N) e = v) ∧
                ((¬ ∃ e, EdgePresent (shiftedStream W N) e ∧
                  edgeEast (shiftedStream W N) e = v) ↔
                  ∃ k : ℤ, k ≤ 0 ∧
                    v = boundaryVertex (shiftedStream W N) h k)) ∧
            (∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay W H),
              P.vertex 0 = wholePlaneVertexι W N
                (boundaryVertex (shiftedStream W N) h k) →
              Q.vertex 0 = wholePlaneVertexι W N
                (boundaryVertex (shiftedStream W N) h k') →
              ∃ s s', 0 < s ∧ 0 < s' ∧
                ∀ t, P.vertex (s + t) = Q.vertex (s' + t))) ∧
        (∀ n : ℕ,
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
              (kmswWindowEdgeMapInf (shiftedStream W 0) n
                (kmswRightBoundaryEdge u j)))) ∧
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
                (kmswWindowVertexMapInf (shiftedStream W 0) n
                  (boundaryVertex u h k)) →
              Q.vertex 0 = wholePlaneVertexι W 0
                (kmswWindowVertexMapInf (shiftedStream W 0) n
                  (boundaryVertex u h k')) →
              ∃ s s', 0 < s ∧ 0 < s' ∧
                ∀ t, P.vertex (s + t) = Q.vertex (s' + t))) := by
  filter_upwards
    [wholePlaneIID_ae_lemma38_clauses_pos, wholePlaneIID_ae_lemma38_clauses_start_pos]
    with W hPos hStart
  rcases hPos with ⟨H₁, hN⟩
  rcases hStart with ⟨H₂, hn⟩
  have hEq : H₁ = H₂ := Subsingleton.elim _ _
  subst H₂
  exact ⟨H₁, hN, hn⟩

end DirectedDistances.KMSW
