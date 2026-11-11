module

public import DirectedDistances.KMSW.HatRealizedFacesComplete

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The remaining pointwise deletion-to-exterior connectivity step. Each point of
the ambient image removed by the reachable restriction must lie in the same
complement component as the ambient exterior and the root's east dart. This
Prop is isolated and is not assumed. -/
@[expose] def hatDeletedGeometryRootFaceConnectivityGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  ∀ E : P.Face, ∀ U : Q.Face,
    P.IsUnbounded E → E.val ⊆ U.val → Q.IsUnbounded U →
      Q.dartBorders (hatLimitDartEquiv w h futureMapOuterDart) U →
        ∀ z, z ∈ P.image → z ∉ Q.image → z ∈ U.val

end DirectedDistances.KMSW
