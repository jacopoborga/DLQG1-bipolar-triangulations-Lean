module

public import DirectedDistances.KMSW.MhatPrimeGeometricCarrier
public import DirectedDistances.KMSW.PrimedComplementEdgeEquiv
import DirectedDistances.KMSW.PrimedComplementCoverageCrossing
import DirectedDistances.KMSW.PrimedReachabilityUnion

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Present primed limit edges lie in the geometric complement -/
theorem primedPresentLimitEdge_primeGeomEdge (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) {a : ℕ}
    (ha : PrimedEdgePresent w h a) :
    primeGeomEdge w hfin hb (primedLimitEdgeMap w h a) := by
  have hdata := primedLimitEdge_data w h ha
  apply Or.inl
  intro hgeom
  have hmem : ∃ n, primedLimitEdgeMap w h a ∈
      stageReachablePresentEdges w n := by
    apply (stageReachablePresentEdges_iUnion_iff w
      (primedLimitEdgeMap w h a)).2
    exact ⟨hdata.1, hgeom.1, hgeom.2⟩
  obtain ⟨n, hn⟩ := hmem
  exact hdata.2.1 n hn

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every present edge outside the reachable geometric submap has a primed limit -/
theorem primedLimitEdge_preimage_of_present_nonMhat (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) (hp : EdgePresent w e)
    (hgeom : ¬ MhatGeometricEdge w e) :
    ∃ a, primedLimitEdgeMap w h a = e := by
  have hnever : ∀ n, e ∉ stageReachablePresentEdges w n := by
    intro n hn
    apply hgeom
    obtain ⟨_, hwest, heast⟩ :=
      (stageReachablePresentEdges_iUnion_iff w e).mp ⟨n, hn⟩
    exact ⟨hwest, heast⟩
  obtain ⟨a, _, heq⟩ := primedLimitEdgeComplement w h e hp hnever
  exact ⟨a, heq⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Unresolved coverage for geometric edges absent from the primed directed
carrier, including the retained β₀ geometry and C18 root -/
@[expose] def primeMissingEdge_primedLimitEdgeCoverageGoal (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) : Prop :=
  ∀ e, primeMissingEdge w hfin hb e →
    ∃ a, primedLimitEdgeMap w h a = e




@[expose] def primeGeomEdge_iff_primedLimitEdgeGoal (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) : Prop :=
  ∀ e, primeGeomEdge w hfin hb e ↔
    ∃ a, primedLimitEdgeMap w h a = e

end DirectedDistances.KMSW
