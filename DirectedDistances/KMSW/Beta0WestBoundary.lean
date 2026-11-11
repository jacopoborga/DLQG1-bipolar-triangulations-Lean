/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.Beta0LeftmostPath
public import DirectedDistances.KMSW.MhatWestBoundarySide

/-! # The β₀ and west-boundary interface -/

public section
namespace DirectedDistances.KMSW

/-- In the inverse-rotation scan, the face successor of the dart reversed
from a scan entry is the next dart at that vertex. This identifies the
intervening face as an orbit of the infinite face successor; it does not
assert that the face is triangular. Helper toward Lemma 5.12 B3 (β₀); not the -/
theorem beta0_scan_consecutive_darts_bound_face (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (n : ℕ) :
    let d := ((kmswInfRot w hfin).symm ^ n) corner
    kmswInfFaceSucc w hfin (d.1, !d.2) = (kmswInfRot w hfin).symm d := by
  let d := ((kmswInfRot w hfin).symm ^ n) corner
  change kmswInfFaceSucc w hfin (d.1, !d.2) = (kmswInfRot w hfin).symm d
  rw [kmswInfFaceSucc, Equiv.Perm.mul_apply]
  change (kmswInfRot w hfin).symm (d.1, !(!d.2)) =
    (kmswInfRot w hfin).symm d
  simp only [Bool.not_not]

/-- At an edge recorded on the west boundary of M̂, the β₀ selector at its
head is the first present outgoing dart in the inverse rotation scan. The
claim that this selected dart is itself the next west-boundary edge is the
remaining planar identification for Lemma 5.12 B3. Helper toward Lemma 5.12 -/
theorem beta0_westBoundary_next_scan (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (e : ℕ)
    (he : MhatWestBoundaryEdge w e) :
    let ein : {f : ℕ // EdgePresent w f} := ⟨e, he.1⟩
    EdgePresent w (kmswBeta0Next w hfin h ein).1 ∧
      edgeWest w (kmswBeta0Next w hfin h ein).1 = edgeEast w e ∧
      (∀ n, n < kmswFirstOutgoingIndex_symm w hfin
          (kmswBeta0IncomingCorner ein) (edgeEast w e)
          (kmswBeta0IncomingCorner_spec ein)
          (kmswM0_vertex_outgoing w hfin h (edgeEast w e)) →
        ¬ kmswPresentOutgoingDart w
          (((kmswInfRot w hfin).symm ^ n)
            (kmswBeta0IncomingCorner ein))) ∧
      (∀ g, EdgePresent w g → edgeWest w g = edgeEast w e →
        g ≠ (kmswBeta0Next w hfin h ein).1 →
        ∃ m, kmswFirstOutgoingIndex_symm w hfin
            (kmswBeta0IncomingCorner ein) (edgeEast w e)
            (kmswBeta0IncomingCorner_spec ein)
            (kmswM0_vertex_outgoing w hfin h (edgeEast w e)) < m ∧
          ((kmswInfRot w hfin).symm ^ m)
            (kmswBeta0IncomingCorner ein) = (g, false)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (kmswBeta0Next_spec w hfin h ⟨e, he.1⟩).1
  · simpa using (kmswBeta0Next_spec w hfin h ⟨e, he.1⟩).2.1
  · exact (kmswBeta0Next_spec w hfin h ⟨e, he.1⟩).2.2
  · intro g hg hgv hne
    exact kmswBeta0Next_later w hfin h ⟨e, he.1⟩ g hg hgv hne

end DirectedDistances.KMSW
