module

public import DirectedDistances.KMSW.Beta0BoundarySuccessor
public import DirectedDistances.KMSW.MhatPrimeFaceSource

public section
namespace DirectedDistances.KMSW

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
variable (hb : BoundaryHitWitnesses w)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def primeBetaEdge (e : ℕ) : Prop :=
  ∃ n, (kmswBeta0Stream w hfin hb n).val = e

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def primeGeomEdge (e : ℕ) : Prop :=
  ¬ MhatGeometricEdge w e ∨ primeBetaEdge w hfin hb e

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def primePresentEdge (e : ℕ) : Prop :=
  EdgePresent w e ∧ ¬ MhatGeometricEdge w e

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Geometric prime edges absent from its directed edge set -/
@[expose] def primeMissingEdge (e : ℕ) : Prop :=
  primeGeomEdge w hfin hb e ∧ ¬ primePresentEdge w e

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The edge-ID carrier of the primed geometry -/
abbrev PrimeEdge := {e : ℕ // primeGeomEdge w hfin hb e}

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Vertices incident to retained primed geometry -/
@[expose] def primeVertex (v : ℕ) : Prop :=
  ∃ e, primeGeomEdge w hfin hb e ∧
    (edgeWest w e = v ∨ edgeEast w e = v)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The vertex-ID carrier of the primed geometry -/
abbrev PrimeVertex := {v : ℕ // primeVertex w hfin hb v}

/- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def primeVertexSourceCharacterizationGoal : Prop :=
  ∀ v, primeVertex w hfin hb v ↔
    (¬ MhatVertex w v ∨
      ∃ e, primeBetaEdge w hfin hb e ∧
        (edgeWest w e = v ∨ edgeEast w e = v))

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
An unoriented geometric dart of a prime edge -/
abbrev PrimeDart := PrimeEdge w hfin hb × Bool

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The stream edges are exactly the existing M-hat west-boundary edges -/
theorem primeBetaEdge_iff_MhatWestBoundaryEdge (e : ℕ) :
    primeBetaEdge w hfin hb e ↔ MhatWestBoundaryEdge w e := by
  constructor
  · rintro ⟨n, rfl⟩
    exact beta0_westBoundary_stream w hfin hb n
  · intro he
    obtain ⟨n, hn⟩ := beta0_westBoundary_reached w hfin hb e he
    exact ⟨n, hn⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Every β₀ edge remains in the prime geometric carrier -/
theorem primeBetaEdge_primeGeomEdge (e : ℕ)
    (he : primeBetaEdge w hfin hb e) : primeGeomEdge w hfin hb e :=
  Or.inr he

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Every β₀ edge is missing from the primed directed edge set -/
theorem primeBetaEdge_primeMissingEdge (e : ℕ)
    (he : primeBetaEdge w hfin hb e) : primeMissingEdge w hfin hb e := by
  refine ⟨primeBetaEdge_primeGeomEdge w hfin hb e he, ?_⟩
  intro hpresent
  have hboundary := (primeBetaEdge_iff_MhatWestBoundaryEdge w hfin hb e).mp he
  have hgeom : MhatGeometricEdge w e := ⟨hboundary.2.1, hboundary.2.2.1⟩
  exact hpresent.2 hgeom

end DirectedDistances.KMSW
