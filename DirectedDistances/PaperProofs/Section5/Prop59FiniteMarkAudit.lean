module

public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorFacedCompat
public import DirectedDistances.PlanarMap.BdyReverseBijective
public import DirectedDistances.PlanarMap.BdyReverseSizedSlices
public import DirectedDistances.PlanarMap.Prop59RootMarkFacts
public import DirectedDistances.PaperProofs.Section5.Prop59OrderedRootIndexing

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3.RootedBallSystem






/-- Helper toward Proposition 5.9 (prop-uihbot-sym, convention B ordered root: finite mark
compatibility); not a paper result. This proves the all-radii finite faced-class
compatibility for the exact sample encoded by `diskRootedPlanarMapLaw`: its KMSW class has
`n + ell + 1` total edges and boundary length sum `ell + 2`, so its printed non-boundary
mirrored parameter retains that same grade. The Proposition 5.9 proof separately prints
identify those distinct grades. The mark is indexed by `Fin ell` and reindexed by `Fin.rev`.
The root and edge facts concern the combinatorial rooted-map mirror; no plane realization
or complementary-component correspondence is asserted. -/
theorem prop59_finite_B_mark_compat (n ell : ℕ) (hell : 0 < ell) :
    let Q :=
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    (∀ p : Q × Fin ell,
      let A := diskRootedPlanarMapOfSample n ell hell p
      let R := A.toRootedLocallyFiniteMap
      let M := mirrorRootedLocallyFiniteMap R
      (M.rootDart = R.edgeInv R.frameEdgeDart ∧
        M.frameEdgeDart = R.edgeInv R.frameEdgeDart ∧
        M.frameOtherDart = R.frameOtherDart.map (fun _ => R.frameEdgeDart)) ∧
      R.edgeInv M.frameEdgeDart = R.frameEdgeDart ∧
      (∀ d, M.edgeInv d = R.edgeInv d) ∧
      (∀ d, M.missing d ↔ R.missing d) ∧
      (∀ d, M.tail d ↔ R.tail d) ∧
      (diskRootedPlanarSampleMirror n ell hell p).2 = p.2.rev ∧
      (diskRootedPlanarSampleMirror n ell hell p).2.val =
        ell - 1 - p.2.val ∧
      (∀ r, rootedLocallyFiniteFacedBallClass r
          (mirrorRootedLocallyFinitePlanarMap A) =
        rootedLocallyFiniteFacedBallClass r
          (diskRootedPlanarMapOfMirroredSample n ell hell p))) ∧
    (((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
      (diskRootedPlanarSampleMirror n ell hell) =
        (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))) := by
  constructor
  · intro p
    let A := diskRootedPlanarMapOfSample n ell hell p
    let R := A.toRootedLocallyFiniteMap
    let M := mirrorRootedLocallyFiniteMap R
    change
      ((M.rootDart = R.edgeInv R.frameEdgeDart ∧
        M.frameEdgeDart = R.edgeInv R.frameEdgeDart ∧
        M.frameOtherDart = R.frameOtherDart.map (fun _ => R.frameEdgeDart)) ∧
        R.edgeInv M.frameEdgeDart = R.frameEdgeDart ∧
        (∀ d, M.edgeInv d = R.edgeInv d) ∧
        (∀ d, M.missing d ↔ R.missing d) ∧
        (∀ d, M.tail d ↔ R.tail d) ∧
        (diskRootedPlanarSampleMirror n ell hell p).2 = p.2.rev ∧
        (diskRootedPlanarSampleMirror n ell hell p).2.val =
          ell - 1 - p.2.val ∧
        (∀ r, rootedLocallyFiniteFacedBallClass r
            (mirrorRootedLocallyFinitePlanarMap A) =
          rootedLocallyFiniteFacedBallClass r
            (diskRootedPlanarMapOfMirroredSample n ell hell p)))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mirrorRootedLocallyFiniteMap_rootMark_swap R
    · exact (prop59_mirrorFrameEdge_sameGeometricEdge R).2
    · intro d
      rfl
    · intro d
      exact mirrorRootedLocallyFiniteMap_missing_iff R d
    · intro d
      exact mirrorRootedLocallyFiniteMap_tail_iff R d
    · rfl
    · simp only [diskRootedPlanarSampleMirror, Fin.rev]
      omega
    · exact diskRootedPlanarSampleMirrorFacedClassCompatibility_proved
        n ell hell p
  · exact diskRootedPlanarSampleMirror_uniform n ell hell

end DirectedDistances.PaperProofs.Section5
