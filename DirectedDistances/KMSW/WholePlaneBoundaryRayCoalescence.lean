module

public import DirectedDistances.KMSW.WholePlaneRightmostDescentAmbient
public import DirectedDistances.KMSW.WholePlaneLeftBoundaryTerminal
import DirectedDistances.KMSW.RightDescentPotential

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open scoped Classical

private theorem right_unbounded (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.rightHit (max 1 (-a)) (le_max_left _ _)
  have hm : -a ≤ max (1 : ℤ) (-a) := le_max_right _ _
  exact ⟨n, by omega⟩





theorem wholePlaneRightmostRay_hits_run_rightBoundary (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a)
    (P : WholePlaneRightmostRay W H) (t : ℕ)
    (h0 : P.vertex 0 = wholePlaneVertexι W N
      (edgeEast (shiftedStream W N) (act (shiftedStream W N) t))) :
    ∃ i j, P.vertex i = wholePlaneVertexι W N
      (edgeEast (shiftedStream W N) (kmswRightBoundaryEdge (shiftedStream W N) j)) := by
  let w := shiftedStream W N
  let next := fun a => Classical.choose (wholePlaneRightmost_descent_at_active W H N hR a)
  have hn (a : ℕ) :=
    Classical.choose_spec (wholePlaneRightmost_descent_at_active W H N hR a)
  let s : ℕ → ℕ := fun i => Nat.rec t (fun _ a => next a) i
  have hs (i : ℕ) : s i < s (i + 1) ∧ R w (s (i + 1)) = R w (s i) - 1 ∧
      ∀ q, s i < q → q < s (i + 1) → R w (s i) - 1 < R w q :=
    ⟨(hn (s i)).1, (hn (s i)).2.1, (hn (s i)).2.2.1⟩
  have hv (i : ℕ) : P.vertex i = wholePlaneVertexι W N (edgeEast w (act w (s i))) := by
    induction i with
    | zero => exact h0
    | succ i ih =>
      have hr := P.rightmost i
      rw [ih] at hr
      have he := wholePlaneRightmostOutgoingAt_unique W H _ hr (hn (s i)).2.2.2.2
      calc
        P.vertex (i + 1) = wholePlaneEdgeEast W (P.edge i) := (P.target i).symm
        _ = wholePlaneVertexι W N (edgeEast w (act w (s (i + 1)))) := by
          rw [he, wholePlaneEdgeEast_ι]
  obtain ⟨i, _, hi⟩ := descentChain_hits_record w s hs
  obtain ⟨j, hj⟩ := hi i le_rfl
  exact ⟨i, j, (hv i).trans (congrArg (fun e => wholePlaneVertexι W N (edgeEast w e)) hj)⟩

private theorem root_east (w : ℕ → Fin 3) : edgeEast w 0 = 1 := by
  have he := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl 0))).2
  exact he.symm.trans rfl






theorem wholePlaneRightmostRay_exists_rightBoundary_chain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) :
    ∃ B : WholePlaneRightmostRay W H,
      (∀ j, B.vertex j = wholePlaneVertexι W N
        (boundaryVertex (shiftedStream W N) h ((j + 1 : ℕ) : ℤ))) ∧
      (∀ j, B.edge j =
        wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) (j + 1))) ∧
      ∀ j, ∃ i, wholePlaneVertexι W N
        (edgeEast (shiftedStream W N) (kmswRightBoundaryEdge (shiftedStream W N) j)) =
          B.vertex i := by
  let w := shiftedStream W N
  obtain ⟨B, hzero, hedge⟩ := wholePlaneRightmostRay_exists_root_terminal W H N h
  have hv (j : ℕ) : B.vertex j =
      wholePlaneVertexι W N (boundaryVertex w h ((j + 1 : ℕ) : ℤ)) := by
    calc
      B.vertex j = wholePlaneEdgeWest W (B.edge j) := (B.rightmost j).2.1.symm
      _ = wholePlaneVertexι W N (boundaryVertex w h ((j + 1 : ℕ) : ℤ)) := by
        rw [hedge j, wholePlaneEdgeWest_ι,
          (boundaryVertex_right_edge_present_source w h (k := j + 1) (by omega)).2.1]
  refine ⟨B, hv, hedge, ?_⟩
  intro j
  cases j with
  | zero =>
    refine ⟨0, ?_⟩
    rw [kmswRightBoundaryEdge_zero, root_east]
    exact hzero.symm
  | succ j =>
    refine ⟨j + 1, ?_⟩
    rw [hv]
    apply congrArg (wholePlaneVertexι W N)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (boundaryVertex_right_edge_present_source w h (k := j + 1) (by omega)).2.2

private theorem common_of_hits_ray {W : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} (P Q B : WholePlaneRightmostRay W H)
    (hP : ∃ i a, P.vertex i = B.vertex a)
    (hQ : ∃ j b, Q.vertex j = B.vertex b) :
    ∃ i j, P.vertex i = Q.vertex j := by
  obtain ⟨i, a, hi⟩ := hP
  obtain ⟨j, b, hj⟩ := hQ
  let c := max a b
  have ha : a ≤ c := Nat.le_max_left _ _
  have hb : b ≤ c := Nat.le_max_right _ _
  have hp := wholePlaneRightmostRays_coalesce_of_common_vertex P B i a hi (c - a)
  have hq := wholePlaneRightmostRays_coalesce_of_common_vertex Q B j b hj (c - b)
  rw [Nat.add_sub_of_le ha] at hp
  rw [Nat.add_sub_of_le hb] at hq
  exact ⟨i + (c - a), j + (c - b), hp.trans hq.symm⟩





theorem wholePlaneRightmostRay_hits_rightChain_of_active (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (M : ℕ) (hNM : N ≤ M)
    (P : WholePlaneRightmostRay W H) (t : ℕ)
    (h0 : P.vertex 0 = wholePlaneVertexι W M
      (edgeEast (shiftedStream W M) (act (shiftedStream W M) t))) :
    ∃ i j, P.vertex i = wholePlaneVertexι W N
      (boundaryVertex (shiftedStream W N) h ((j + 1 : ℕ) : ℤ)) := by
  let hM := boundaryHitWitnesses_of_le W hNM h
  have hR := right_unbounded (shiftedStream W M) hM
  obtain ⟨BN, hBN, _, _⟩ := wholePlaneRightmostRay_exists_rightBoundary_chain W H N h
  obtain ⟨BM, _, _, hBM⟩ := wholePlaneRightmostRay_exists_rightBoundary_chain W H M hM
  have hroot : BN.vertex 0 = wholePlaneVertexι W M
      (edgeEast (shiftedStream W M) (act (shiftedStream W M) (M - N))) := by
    calc
      BN.vertex 0 = wholePlaneVertexι W N 1 := by
        rw [hBN, show ((0 + 1 : ℕ) : ℤ) = 1 from rfl, boundaryVertex_one]
      _ = wholePlaneVertexι W M (wholePlaneVertexTrans W N M hNM 1) :=
        (congrFun (wholePlaneVertexι_trans W N M hNM) 1).symm
      _ = wholePlaneVertexι W M
          (edgeEast (shiftedStream W M) (act (shiftedStream W M) (M - N))) := by
        rw [wholePlaneVertexTrans_root_terminal]
        exact congrArg (wholePlaneVertexι W M)
          (edge_endpoints_eq _ (act_lt_nextEdge _ (le_refl (M - N)))).2
  obtain ⟨i, a, hi⟩ := wholePlaneRightmostRay_hits_run_rightBoundary W H M hR P t h0
  obtain ⟨b, hb⟩ := hBM a
  obtain ⟨j, c, hj⟩ :=
    wholePlaneRightmostRay_hits_run_rightBoundary W H M hR BN (M - N) hroot
  obtain ⟨d, hd⟩ := hBM c
  obtain ⟨p, q, hpq⟩ := common_of_hits_ray P BN BM
    ⟨i, b, hi.trans hb⟩ ⟨j, d, hj.trans hd⟩
  exact ⟨p, q, hpq.trans (hBN q)⟩






theorem wholePlaneRightmostRay_hits_rightChain_from_leftBoundary (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ 0)
    (hLLPresent : wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N)
        (boundaryHitTime (shiftedStream W N) h (k - 1)))))
    (P : WholePlaneRightmostRay W H)
    (h0 : P.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k)) :
    ∃ i j, P.vertex i = wholePlaneVertexι W N
      (boundaryVertex (shiftedStream W N) h ((j + 1 : ℕ) : ℤ)) := by
  obtain ⟨M, hNM, t, ht⟩ :=
    wholePlane_leftBoundary_vertex_terminal W N h k hk hLLPresent
  exact wholePlaneRightmostRay_hits_rightChain_of_active W H N h M hNM P t (h0.trans ht)

private theorem hits_chain_from_terminal_boundary (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hterminal : ∀ k : ℤ, k ≤ 0 → ∃ M, N ≤ M ∧ ∃ t,
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k) =
        wholePlaneVertexι W M
          (edgeEast (shiftedStream W M) (act (shiftedStream W M) t)))
    (k : ℤ) (P : WholePlaneRightmostRay W H)
    (h0 : P.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k)) :
    ∃ i j, P.vertex i = wholePlaneVertexι W N
      (boundaryVertex (shiftedStream W N) h ((j + 1 : ℕ) : ℤ)) := by
  by_cases hk : k ≤ 0
  · obtain ⟨M, hNM, t, ht⟩ := hterminal k hk
    exact wholePlaneRightmostRay_hits_rightChain_of_active W H N h M hNM P t
      (h0.trans ht)
  · refine ⟨0, k.toNat - 1, ?_⟩
    have hindex : ((k.toNat - 1 + 1 : ℕ) : ℤ) = k := by omega
    rw [hindex]
    exact h0

private theorem coalesce_from_terminal_boundary (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hterminal : ∀ k : ℤ, k ≤ 0 → ∃ M, N ≤ M ∧ ∃ t,
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k) =
        wholePlaneVertexι W M
          (edgeEast (shiftedStream W M) (act (shiftedStream W M) t)))
    (k k' : ℤ) (P Q : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k))
    (hQ : Q.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k')) :
    ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
  obtain ⟨B, hB, _, _⟩ := wholePlaneRightmostRay_exists_rightBoundary_chain W H N h
  obtain ⟨i, a, hi⟩ := hits_chain_from_terminal_boundary W H N h hterminal k P hP
  obtain ⟨j, b, hj⟩ := hits_chain_from_terminal_boundary W H N h hterminal k' Q hQ
  obtain ⟨s, s', hss⟩ := common_of_hits_ray P Q B
    ⟨i, a, hi.trans (hB a).symm⟩ ⟨j, b, hj.trans (hB b).symm⟩
  exact ⟨s, s', wholePlaneRightmostRays_coalesce_of_common_vertex P Q s s' hss⟩






theorem wholePlaneRightmostRays_coalesce_from_boundary (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N)
        (boundaryHitTime (shiftedStream W N) h (k - 1)))))
    (k k' : ℤ) (P Q : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k))
    (hQ : Q.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k')) :
    ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
  exact coalesce_from_terminal_boundary W H N h
    (fun a ha => wholePlane_leftBoundary_vertex_terminal W N h a ha (hLL a ha))
    k k' P Q hP hQ






theorem wholePlaneRightmostRays_coalesce_from_boundary_pos (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N)
        (boundaryHitTime (shiftedStream W N) h (k - 1)))))
    (k k' : ℤ) (P Q : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k))
    (hQ : Q.vertex 0 =
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k')) :
    ∃ s s', 0 < s ∧ 0 < s' ∧ ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
  obtain ⟨s, s', hs⟩ :=
    wholePlaneRightmostRays_coalesce_from_boundary W H N h hLL k k' P Q hP hQ
  refine ⟨s + 1, s' + 1, by omega, by omega, ?_⟩
  intro t
  simpa only [Nat.add_assoc] using hs (1 + t)






theorem wholePlaneIID_ae_rightmostRays_coalesce_from_boundary :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∃ H : WholePlaneRotationHypothesis W,
      ∀ N : ℕ, ∃ h : BoundaryHitWitnesses (shiftedStream W N),
        ∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay W H),
          P.vertex 0 =
            wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k) →
          Q.vertex 0 =
            wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k') →
          ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis,
    wholePlaneIID_ae_leftBoundary_vertex_terminal] with W H hterminal
  refine ⟨H, fun N => ?_⟩
  obtain ⟨h, ht⟩ := hterminal N
  exact ⟨h, fun k k' P Q hP hQ =>
    coalesce_from_terminal_boundary W H N h ht k k' P Q hP hQ⟩

end DirectedDistances.KMSW
