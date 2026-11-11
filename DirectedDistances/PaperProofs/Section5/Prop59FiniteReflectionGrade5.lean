module

public import DirectedDistances.PaperProofs.Section5.Prop59FiniteReflectionGrade4

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory

/-- Helper toward Proposition 5.9. The radius-r faced-ball law of the
reflected left finite sample equals that of the right finite sample, by the
proved reflection transport on finite channeled classes and boundary marks. -/
theorem diskRootedPlanarMapOfRightSample_facedBallClass_law
    (n ell : ℕ) (hell : 0 < ell) (r : ℕ) :
    let Qₗ := Prop59LeftFiniteClass n ell
    let Qᵣ := Prop59RightFiniteClass n ell
    letI : Fintype Qₗ := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : Fintype Qᵣ := Fintype.ofEquiv Qₗ
      (prop59FiniteReflectionClassEquiv n ell hell)
    letI : MeasurableSpace Qₗ := ⊤
    letI : MeasurableSpace Qᵣ := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    let μₗ := (uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))
    let μᵣ := (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell))
    μₗ.map (fun p => rootedLocallyFiniteFacedBallClass r
        (mirrorRootedLocallyFinitePlanarMap
          (diskRootedPlanarMapOfSample n ell hell p))) =
      μᵣ.map (fun p => rootedLocallyFiniteFacedBallClass r
        (diskRootedPlanarMapOfRightSample n ell hell p)) := by
  classical
  let Qₗ := Prop59LeftFiniteClass n ell
  let Qᵣ := Prop59RightFiniteClass n ell
  letI : Fintype Qₗ := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
  letI : Fintype Qᵣ := Fintype.ofEquiv Qₗ
    (prop59FiniteReflectionClassEquiv n ell hell)
  letI : MeasurableSpace Qₗ := ⊤
  letI : MeasurableSpace Qᵣ := ⊤
  letI : MeasurableSpace (Fin ell) := ⊤
  letI : MeasurableSpace FacedFramedBallClass := ⊤
  let μₗ := (uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))
  let μᵣ := (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell))
  let T : Qₗ × Fin ell → Qᵣ × Fin ell := fun p =>
    (prop59FiniteReflectionClassEquiv n ell hell p.1, p.2.rev)
  let R : Qᵣ × Fin ell → FacedFramedBallClass := fun p =>
    rootedLocallyFiniteFacedBallClass r
      (diskRootedPlanarMapOfRightSample n ell hell p)
  let L : Qₗ × Fin ell → FacedFramedBallClass := fun p =>
    rootedLocallyFiniteFacedBallClass r
      (mirrorRootedLocallyFinitePlanarMap
        (diskRootedPlanarMapOfSample n ell hell p))
  have hmarked : μₗ.map T = μᵣ := by
    simpa [μₗ, μᵣ, Qₗ, Qᵣ, T] using
      (prop59FiniteReflectionMarkedUniform n ell hell)
  have hpoint : R ∘ T = L := by
    funext p
    simp [R, L, T, diskRootedPlanarMapOfRightSample, Fin.rev_rev]
  have hmap := congrArg (fun ν : Measure (Qᵣ × Fin ell) => ν.map R) hmarked
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hmap
  rw [hpoint] at hmap
  simpa [μₗ, μᵣ, R, L] using hmap



























end DirectedDistances.PaperProofs.Section5

