module

public import DirectedDistances.KMSW.WholePlaneRotationAE
public import DirectedDistances.KMSW.WholePlaneRightBoundaryChain
public import DirectedDistances.KMSW.WholePlaneLeftBoundaryMissing
public import DirectedDistances.KMSW.WholePlaneLeftmostIncomingAmbient
public import DirectedDistances.KMSW.RunBoundaryStackSets
public import DirectedDistances.KMSW.WholePlaneRunBoundaryDegree
public import DirectedDistances.KMSW.WholePlaneLLRecordEdges
public import DirectedDistances.KMSW.WholePlaneBoundaryRayCoalescence
public import DirectedDistances.KMSW.WholePlaneRightmostOutgoingExists
public import DirectedDistances.KMSW.WholePlaneLeftmostIncomingExists

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open scoped Classical

private theorem assembly_left_coordinate_succ_ge (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  have hL : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    omega
  rw [hL]
  omega

private theorem assembly_first_hit_eq_of_le (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  classical
  let m := Nat.find (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hma : f m ≤ a := Nat.find_spec (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hn⟩ : ∃ j, f j ≤ a) hn
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hma
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : a < f p := by
      have hnot := Nat.find_min (⟨n, hn⟩ : ∃ j, f j ≤ a) (by omega : p < m)
      omega
    refine ⟨m, hmn, ?_⟩
    rw [hp] at hma ⊢
    have hnext := hstep p
    omega

private theorem assembly_first_hit_strict (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) (h : ∃ n, f n = a) :
    ∀ j < Nat.find h, a < f j := by
  intro j hj
  by_contra hnot
  have hjle : f j ≤ a := by omega
  obtain ⟨m, hmj, hma⟩ := assembly_first_hit_eq_of_le f hstep hzero ha hjle
  exact (Nat.find_min h (hmj.trans_lt hj)) hma

private theorem assembly_boundaryHitTime_left_strict_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k,
      L w (boundaryHitTime w h k) < L w j := by
  have htime : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  have hspec := Nat.find_spec (h.leftHit k hk)
  have hs := assembly_first_hit_strict (L w) (assembly_left_coordinate_succ_ge w)
    (by simp [L]) (by omega : k < 0) (h.leftHit k hk)
  intro j hj
  rw [htime] at hj
  rw [htime, hspec]
  exact hs j hj





theorem wholePlaneIID_ae_lemma38_clauses :
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
            ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t)) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis,
    wholePlaneIID_ae_rotation_boundary_status,
    wholePlaneIID_ae_leftBoundary_leftmost_chain,
    wholePlaneIID_ae_LL_record_edges,
    wholePlaneIID_ae_runBoundaryDegree,
    wholePlaneIID_ae_rightmostRays_coalesce_from_boundary] with
    W H hstatus hleft hrecords hdegree hcoalesce
  rcases hleft with ⟨Hleft, hleft⟩
  have hHleft : Hleft = H := Subsingleton.elim _ _
  rw [hHleft] at hleft
  rcases hcoalesce with ⟨Hcoalesce, hcoalesce⟩
  have hHcoalesce : Hcoalesce = H := Subsingleton.elim _ _
  rw [hHcoalesce] at hcoalesce
  refine ⟨H, fun N => ?_⟩
  obtain ⟨h, hdegreeN⟩ := hdegree N
  obtain ⟨hleftN, hleftClauses⟩ := hleft N
  have hLeftWitness : hleftN = h := Subsingleton.elim _ _
  rw [hLeftWitness] at hleftClauses
  obtain ⟨hLLPresent, hleftChain⟩ := hleftClauses
  obtain ⟨hcoalesceN, hcoalesceNClauses⟩ := hcoalesce N
  have hCoalesceWitness : hcoalesceN = h := Subsingleton.elim _ _
  rw [hCoalesceWitness] at hcoalesceNClauses
  rcases hstatus.2 N with ⟨hroot, hrightPresent, _hstageMissing⟩
  obtain ⟨vR, eR, hvR0, heR, hrightChain⟩ :=
    wholePlaneRightBoundary_rightmost_chain W H N h
  have hleftMissing : ∀ k : ℤ, k ≤ 0 →
      wholePlaneEdgePresent W
        (wholePlaneEdgeι W N
          (kmswLLCreatedEdge (shiftedStream W N)
            (boundaryHitTime (shiftedStream W N) h (k - 1)))) ∧
      ¬ EdgePresent (shiftedStream W N)
        (kmswLLCreatedEdge (shiftedStream W N)
          (boundaryHitTime (shiftedStream W N) h (k - 1))) := by
    intro k hk
    let w := shiftedStream W N
    have hq : k - 1 ≤ -1 := by omega
    let m := boundaryHitTime w h (k - 1)
    have hmval : L w m = k - 1 := boundaryHitTime_left_spec w h hq
    have hmpos : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      rw [hm0] at hmval
      simp [L] at hmval
      omega
    have hrecord := assembly_boundaryHitTime_left_strict_record w h hq
    have hrec : ∀ j < m, L w m < L w j := by
      simpa only [m] using hrecord
    have hresult := hrecords N m hmpos hrec
    simpa only [w, m] using hresult
  have hLR := kmswRunEventuallyLR_eq_range (shiftedStream W N) h
  have hLL := kmswRunEventuallyLL_eq_range (shiftedStream W N) h
  have hdisjoint := kmswRunEventuallyLR_disjoint_LL (shiftedStream W N)
  refine ⟨h, ?_⟩
  exact ⟨⟨vR, eR, hvR0, heR, hrightChain⟩,
    hroot, hrightPresent, hleftMissing, hleftChain, hLR, hLL, hdisjoint,
    hdegreeN, hcoalesceNClauses⟩

/-- The two deterministic selector existence and uniqueness characterizations
under the same whole-plane rotation hypothesis. -/
theorem wholePlane_selectors_existsUnique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) :
    ((∃! e, wholePlaneRightmostOutgoingAt W H v e) ↔
      ((∃ f, wholePlaneEdgePresent W f ∧ wholePlaneEdgeEast W f = v) ∧
        ∃ e, wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v)) ∧
    ((∃! e, wholePlaneLeftmostIncomingAt W H v e) ↔
      ((∃ f, wholePlaneEdgePresent W f ∧ wholePlaneEdgeEast W f = v) ∧
        ∃ e, wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v)) := by
  exact ⟨wholePlaneRightmostOutgoingAt_existsUnique_iff W H v,
    wholePlaneLeftmostIncomingAt_existsUnique_iff W H v⟩

end DirectedDistances.KMSW
