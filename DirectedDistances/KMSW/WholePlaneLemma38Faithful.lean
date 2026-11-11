module

public import DirectedDistances.KMSW.WholePlaneLemma38Assembly
public import DirectedDistances.KMSW.WholePlaneLemma38StartAssembly

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

/-- Advancing both starting indices preserves a common tail and makes them positive. -/
theorem exists_pos_shifts_of_exists_shifts {α : Sort*} (f g : ℕ → α)
    (h : ∃ s s', ∀ t, f (s + t) = g (s' + t)) :
    ∃ s s', 0 < s ∧ 0 < s' ∧ ∀ t, f (s + t) = g (s' + t) := by
  rcases h with ⟨s, s', h⟩
  refine ⟨s + 1, s' + 1, Nat.zero_lt_succ s, Nat.zero_lt_succ s', ?_⟩
  intro t
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (t + 1)





theorem wholePlaneIID_ae_lemma38_clauses_pos :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W, ∀ N : ℕ,
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
            ∃ s s', 0 < s ∧ 0 < s' ∧ ∀ t, P.vertex (s + t) = Q.vertex (s' + t)) := by
  filter_upwards [wholePlaneIID_ae_lemma38_clauses] with W hW
  rcases hW with ⟨H, hN⟩
  refine ⟨H, fun N => ?_⟩
  rcases hN N with ⟨h, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  refine ⟨h, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  intro k k' P Q hP hQ
  exact exists_pos_shifts_of_exists_shifts P.vertex Q.vertex
    (h10 k k' P Q hP hQ)





theorem wholePlaneIID_ae_lemma38_clauses_start_pos :
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
            ∃ s s', 0 < s ∧ 0 < s' ∧ ∀ t, P.vertex (s + t) = Q.vertex (s' + t)) := by
  filter_upwards [wholePlaneIID_ae_lemma38_clauses_start] with W hW
  rcases hW with ⟨H, hn⟩
  refine ⟨H, fun n => ?_⟩
  dsimp only
  rcases hn n with ⟨h, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  refine ⟨h, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  intro k k' P Q hP hQ
  exact exists_pos_shifts_of_exists_shifts P.vertex Q.vertex
    (h10 k k' P Q hP hQ)

end DirectedDistances.KMSW
