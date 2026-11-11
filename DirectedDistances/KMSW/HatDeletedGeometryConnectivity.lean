module

public import DirectedDistances.KMSW.HatRealizedFacesComplete
public import DirectedDistances.KMSW.Beta0LeftmostPath
public import DirectedDistances.KMSW.Beta0BoundarySuccessor
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary
public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification
public import DirectedDistances.PlanarMap.PlaneFaceSurvival

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The drawn trace of the source's leftmost path beta_0 in the ambient realization. -/
@[expose] noncomputable def hatBeta0Trace (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) : Set ℂ :=
  ⋃ n, ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
    ((kmswBeta0Stream w hfin (hatBoundaryHitWitnesses w h) n).1, false)).image

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every arc of the leftmost path beta_0 is retained in the reachable drawing. -/
theorem hatBeta0Trace_subset_hatRealizedImage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatBeta0Trace w h hfin ⊆ (hatRealizedDrawing w hfin).image := by
  intro z hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  let e := (kmswBeta0Stream w hfin (hatBoundaryHitWitnesses w h) n).1
  have hboundary := beta0_westBoundary_stream w hfin (hatBoundaryHitWitnesses w h) n
  have hretained : MhatGeometricEdge w e := by
    exact ⟨hboundary.2.1, hboundary.2.2.1⟩
  change z ∈ (restrictDrawing
    (monotoneFamilyDrawing w hfin (monotone_family_all w))
    {d : ℕ × Bool | MhatGeometricEdge w d.1} (fun _ => Iff.rfl)).image
  rw [restrictDrawing_image_eq]
  exact Or.inr ⟨⟨(e, false), hretained⟩, hn⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The remaining infinite-curve separation obligation, isolated without assuming it:
every deleted ambient point can be joined in the complement of the reachable
drawing to an unbounded ambient face. The beta_0 trace is the retained boundary
curve; proving this path statement requires its Jordan-type separation from the -/
@[expose] def hatDeletedGeometryPathToAmbientExteriorGoal (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  ∀ E : P.Face, P.IsUnbounded E → ∀ z, z ∈ P.image → z ∉ Q.image →
    ∃ q ∈ E.val, ∃ γ : Set.Icc (0 : ℝ) 1 → ℂ,
      Continuous γ ∧ γ 0 = z ∧ γ 1 = q ∧ ∀ t, γ t ∉ Q.image

end DirectedDistances.KMSW
