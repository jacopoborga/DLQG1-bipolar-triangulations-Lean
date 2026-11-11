module

public import DirectedDistances.KMSW.PrimedGeometricEdgeCoverage
public import DirectedDistances.KMSW.HatMissingEdgeExclusion
public import DirectedDistances.KMSW.PrimedLimitDartIdentification

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every missing retained edge is either a present β₀ boundary edge excluded
from the primed directed carrier, or an ambient missing edge outside M-hat. -/
theorem primeMissingEdge_source_cases (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (e : ℕ)
    (he : primeMissingEdge w hfin hb e) :
    (MhatWestBoundaryEdge w e ∧ EdgePresent w e) ∨
      (¬ EdgePresent w e ∧ ¬ MhatGeometricEdge w e) := by
  rcases he with ⟨hgeom, hmissing⟩
  rcases hgeom with houtside | hbeta
  · right
    refine ⟨?_, houtside⟩
    intro hp
    exact hmissing ⟨hp, houtside⟩
  · left
    have hboundary :=
      (primeBetaEdge_iff_MhatWestBoundaryEdge w hfin hb e).mp hbeta
    have hgeomM : MhatGeometricEdge w e :=
      ⟨hboundary.2.1, hboundary.2.2.1⟩
    exact ⟨hboundary, mhatGeometricEdge_edgePresent w hb e hgeomM⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The beta_0 image goal is proved separately as `primedBeta0MissingEdgeImage`.
The ambient-missing and nonroot image goals are also proved in
`KMSW/PrimedMissingEdgeImages.lean` as `primedAmbientMissingEdgeImage` and
`primedMissingNonrootImage`; the nonroot goal is declared in
`KMSW/PrimedLimitDartIdentification.lean`. -/
@[expose] def primedBeta0MissingEdgeImageGoal (w : ℕ → Fin 3)
    (_hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) : Prop :=
  ∀ e, MhatWestBoundaryEdge w e → ∃ a, primedLimitEdgeMap w h a = e

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The remaining ambient-missing image-coverage proposition handles edges that
are missing in M and lie outside M-hat. -/
@[expose] def primedAmbientMissingEdgeImageGoal (w : ℕ → Fin 3)
    (_hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) : Prop :=
  ∀ e, ¬ EdgePresent w e → ¬ MhatGeometricEdge w e →
    ∃ a, primedLimitEdgeMap w h a = e

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The C18 missing root is covered by its own geometric edge-map index. -/
theorem primedMissingEdge_C18_root_coverage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (h : HasFlowLineHits w) :
    primeMissingEdge w hfin hb (primedLimitEdgeMap w h 0) ∧
      ∃ a, primedLimitEdgeMap w h a = primedLimitEdgeMap w h 0 := by
  exact ⟨primedLimitRoot_primeMissingEdge w h hfin hb, ⟨0, rfl⟩⟩

end DirectedDistances.KMSW
