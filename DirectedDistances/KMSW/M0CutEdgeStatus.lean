module

public import DirectedDistances.KMSW.M0CutFreshOffSeam
public import DirectedDistances.KMSW.M0CutPresence

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: edge status of the future map); not a paper result. Source:
hit-indexed boundary edge. -/
theorem m0Cut_nonpresent_implies_negative_boundaryOuterEdge (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ)
    (hn : ¬ EdgePresent (shiftedStream W 0) e) :
    ∃ k : ℤ, k ≤ -1 ∧
      e = boundaryOuterEdge (shiftedStream W 0) h0 k := by
  have hEvent := (m0Cut_not_present_iff_eventually_LL
    (shiftedStream W 0) h0 e).mp hn
  have hRange : e ∈ Set.range (fun j : ℕ =>
      kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h0 (-((j : ℤ) + 1)))) := by
    rw [← kmswRunEventuallyLL_eq_range (shiftedStream W 0) h0]
    exact hEvent
  obtain ⟨j, hj⟩ := hRange
  let k : ℤ := -((j : ℤ) + 1)
  have hk : k ≤ -1 := by
    dsimp [k]
    omega
  refine ⟨k, hk, ?_⟩
  rw [boundaryOuterEdge_of_negative (shiftedStream W 0) h0 hk]
  dsimp [k]
  exact hj.symm

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: edge status of the future map); not a paper result. Source:
from run zero into the whole-plane colimit. -/
theorem m0Cut_seam_present_wholePlane (W : ℤ → Fin 3)
    (_H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) (hk : 0 ≤ k) :
    wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k)) := by
  have hEnds := boundaryOuterEdge_endpoints (shiftedStream W 0) h0 k
  exact wholePlaneEdgePresent_ι_of_run_present W 0 _ (hEnds.2.2.1 hk)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: edge status of the future map); not a paper result. Source:
presence agrees with colimit presence, including edges with two seam endpoints. -/
theorem m0Cut_nonseam_status (W : ℤ → Fin 3)
    (_H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ)
    (he : ∀ k : ℤ,
      e ≠ boundaryOuterEdge (shiftedStream W 0) h0 k) :
    EdgePresent (shiftedStream W 0) e ↔
      wholePlaneEdgePresent W (wholePlaneEdgeι W 0 e) := by
  have hp : EdgePresent (shiftedStream W 0) e := by
    by_contra hn
    obtain ⟨k, hk, hEdge⟩ :=
      m0Cut_nonpresent_implies_negative_boundaryOuterEdge W h0 e hn
    exact he k hEdge
  constructor
  · intro _
    exact wholePlaneEdgePresent_ι_of_run_present W 0 e hp
  · intro _
    exact hp

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: edge status of the future map); not a paper result. Source:
its colimit edge is present and it is not a negative left-boundary edge. -/
theorem m0Cut_edgeStatus (W : ℤ → Fin 3)
    (_H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ) :
    EdgePresent (shiftedStream W 0) e ↔
      (wholePlaneEdgePresent W (wholePlaneEdgeι W 0 e) ∧
        ¬ ∃ k : ℤ, k ≤ -1 ∧
          e = boundaryOuterEdge (shiftedStream W 0) h0 k) := by
  by_cases hNegative : ∃ k : ℤ, k ≤ -1 ∧
      e = boundaryOuterEdge (shiftedStream W 0) h0 k
  · have hMissing : ¬ EdgePresent (shiftedStream W 0) e := by
      intro hp
      obtain ⟨k, hk, hEdge⟩ := hNegative
      rw [hEdge] at hp
      exact (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 k).2.2.2 hk hp
    constructor
    · intro hp
      exact (hMissing hp).elim
    · rintro ⟨_, hNotNegative⟩
      exact (hNotNegative hNegative).elim
  · have hPresent : EdgePresent (shiftedStream W 0) e := by
      by_contra hn
      obtain ⟨k, hk, hEdge⟩ :=
        m0Cut_nonpresent_implies_negative_boundaryOuterEdge W h0 e hn
      exact hNegative ⟨k, hk, hEdge⟩
    have hColimit := wholePlaneEdgePresent_ι_of_run_present W 0 e hPresent
    constructor
    · intro _
      exact ⟨hColimit, hNegative⟩
    · intro _
      exact hPresent

end DirectedDistances.KMSW
