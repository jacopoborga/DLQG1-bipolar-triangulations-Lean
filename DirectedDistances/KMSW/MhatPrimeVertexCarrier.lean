module

public import DirectedDistances.KMSW.MhatPrimeGeometricCarrier

public section
namespace DirectedDistances.KMSW

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
variable (hb : BoundaryHitWitnesses w)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
An unreachable vertex is incident to a retained geometric edge -/
theorem primeVertex_of_unreachable (v : ℕ)
    (hv : ¬ MhatVertex w v) : primeVertex w hfin hb v := by
  obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v hn
  let e := d.1.val
  have he : e < (kmswStage w n).nextEdge := d.1.isLt
  have hend := edge_endpoints_eq w he
  have hincident : edgeWest w e = v ∨ edgeEast w e = v := by
    cases hbdir : d.2
    · left
      have hstage : (kmswStage w n).west e = v := by
        simpa [stageEndpoint, e, hbdir] using hd
      exact hend.1.symm.trans hstage
    · right
      have hstage : (kmswStage w n).east e = v := by
        simpa [stageEndpoint, e, hbdir] using hd
      exact hend.2.symm.trans hstage
  have hnot : ¬ MhatGeometricEdge w e := by
    rintro ⟨hwest, heast⟩
    rcases hincident with hincident | hincident
    · exact hv (hincident ▸ hwest)
    · exact hv (hincident ▸ heast)
  exact ⟨e, Or.inl hnot, hincident⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
An endpoint of a retained β₀ edge is a primed vertex -/
theorem primeVertex_of_primeBetaEdge_endpoint (e v : ℕ)
    (he : primeBetaEdge w hfin hb e)
    (hend : edgeWest w e = v ∨ edgeEast w e = v) :
    primeVertex w hfin hb v := by
  exact ⟨e, Or.inr he, hend⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The proposed source characterization's reverse implication -/
theorem primeVertexSourceCharacterization_reverse (v : ℕ)
    (hv : ¬ MhatVertex w v ∨
      ∃ e, primeBetaEdge w hfin hb e ∧
        (edgeWest w e = v ∨ edgeEast w e = v)) :
    primeVertex w hfin hb v := by
  rcases hv with hunreachable | ⟨e, he, hend⟩
  · exact primeVertex_of_unreachable w hfin hb v hunreachable
  · exact primeVertex_of_primeBetaEdge_endpoint w hfin hb e v he hend

end DirectedDistances.KMSW
