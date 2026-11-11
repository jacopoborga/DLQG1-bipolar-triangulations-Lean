module

public import DirectedDistances.KMSW.PrimedRealizedFaces
public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
This isolates the combinatorial missing-tag step before geometric transport. -/
@[expose] def primedExternalOrbitCodeMissingGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (_hb : BoundaryHitWitnesses w) : Prop :=
  ∀ d, (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d →
    ¬ PrimedEdgePresent w h d.1



theorem primedExternalOrbitMissing_iff_codeMissing (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedExternalOrbitMissingGoal w h hfin hb ↔
      primedExternalOrbitCodeMissingGoal w h hfin hb := by
  constructor
  · intro hmissing d hd
    have himage : primeMissingEdge w hfin hb (primedLimitEdgeMap w h d.1) := by
      simpa only [primedExternalOrbitMissingGoal, primedGeometricDartEquiv_apply,
        primedLimitDartMap] using hmissing d hd
    exact (primedLimitEdgeMap_missing w h hfin hb d.1).mpr himage
  · intro hmissing d hd
    have hcode : ¬ PrimedEdgePresent w h d.1 := hmissing d hd
    have himage : primeMissingEdge w hfin hb (primedLimitEdgeMap w h d.1) :=
      (primedLimitEdgeMap_missing w h hfin hb d.1).mp hcode
    simpa only [primedExternalOrbitMissingGoal, primedGeometricDartEquiv_apply,
      primedLimitDartMap] using himage

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The primed drawing has an unbounded complementary component inherited from -/
theorem primedExternalOrbitBorders_unboundedFace_exists (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    ∃ U : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face,
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded U := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  have hsub : Q.image ⊆ P.image :=
    mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)
  obtain ⟨E, hE, _, _⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided w hfin
      (hatBoundaryHitWitnesses w h)
  obtain ⟨z, hz, hEset⟩ := E.property
  have hzQ : z ∉ Q.image := fun hzQ => hz (hsub hzQ)
  let U : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  have hcompl : P.imageᶜ ⊆ Q.imageᶜ := by
    intro x hx hQ
    exact hx (hsub hQ)
  have hEU : E.val ⊆ U.val := by
    rw [hEset]
    exact connectedComponentIn_mono z hcompl
  have hU : Q.IsUnbounded U := by
    intro R
    obtain ⟨x, hx, hxR⟩ := hE R
    exact ⟨x, hEU hx, hxR⟩
  exact ⟨U, hU⟩



theorem primedExternalOrbitMissing_root (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primeMissingEdge w hfin hb
      (primedGeometricDartEquiv w h hfin hb futureMapOuterDart).val.1 := by
  simpa only [primedGeometricDartEquiv_apply, primedLimitDartMap,
    futureMapOuterDart] using primedLimitRoot_primeMissingEdge w h hfin hb

end DirectedDistances.KMSW
