module

public import DirectedDistances.KMSW.RunRightmostRay
public import DirectedDistances.KMSW.RightBoundaryRightmost

/-! Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading: right boundary -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading: right boundary
edge meets the preceding incoming boundary edge immediately. -/
theorem kmswRunRightBoundaryEdge_rightmost (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k) :
    kmswRunRightmostOutAt w hfin
      (boundaryVertex w h (k : ℤ)) (kmswRightBoundaryEdge w k) := by
  change (∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) at hfin
  have hp := boundaryVertex_right_edge_present_source w h hk
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (1 : ℤ) (-a)) (le_max_left _ _)
    exact ⟨n, by
      rw [hn]
      omega⟩
  have hface : kmswInfFaceSucc w hfin
      (kmswRightBoundaryEdge w k, true) =
        (kmswRightBoundaryEdge w (k - 1), true) := by
    simpa [Nat.sub_add_cancel hk] using
      kmswInfFaceSucc_right_of_unbounded_below w hfin hR (k - 1)
  have hscan : (kmswInfRot w hfin).symm
      (kmswRightBoundaryEdge w k, false) =
        (kmswRightBoundaryEdge w (k - 1), true) := by
    simpa [kmswInfFaceSucc, Equiv.Perm.mul_apply] using hface
  refine ⟨hp.1, hp.2.1, 1, by omega, ?_, ?_⟩
  · rw [pow_one, hscan]
    simp [futureMapTail]
  · intro j hj hjk
    omega

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading: right boundary
edge identity. -/
@[expose] noncomputable def kmswRunRightBoundaryRay (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w) :
    KMSWRunRightmostRay w hfin :=
  { vertex := fun j => boundaryVertex w h ((j : ℤ) + 1)
    edge := fun j => kmswRightBoundaryEdge w (j + 1)
    rightmost := by
      intro j
      have hidx : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by omega
      rw [hidx]
      exact kmswRunRightBoundaryEdge_rightmost w hfin h (j + 1) (by omega)
    target := by
      intro j
      have hp := boundaryVertex_right_edge_present_source w h
        (k := j + 1) (by omega)
      change edgeEast w (kmswRightBoundaryEdge w (j + 1)) =
        boundaryVertex w h (((j + 1 : ℕ) : ℤ) + 1)
      exact hp.2.2 }

end DirectedDistances.KMSW
