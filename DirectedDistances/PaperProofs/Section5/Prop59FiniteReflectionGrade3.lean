module

public import DirectedDistances.PaperProofs.Section5.Prop59FiniteReflectionGrade2

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory

/-- Helper toward Proposition 5.9. The right-side rooted sample indexed by a
finite channeled class and a reversed boundary mark is realized by transporting
the class back through the proved finite reflection equivalence, applying the
existing Proposition 5.16 finite-sample construction, and reflecting its
oriented rooted planar map. -/
@[expose] noncomputable def diskRootedPlanarMapOfRightSample
    (n ell : ℕ) (hell : 0 < ell)
    (p : Prop59RightFiniteClass n ell × Fin ell) : RootedLocallyFinitePlanarMap :=
  mirrorRootedLocallyFinitePlanarMap
    (diskRootedPlanarMapOfSample n ell hell
      ((prop59FiniteReflectionClassEquiv n ell hell).symm p.1, p.2.rev))

/-- Helper toward Proposition 5.9. At the local topology combinatorial planar rooted-map
class level, the right-side sample indexed by the image class and reversed mark
is the actual geometric reflection of the existing left-side sample. -/
theorem diskRootedPlanarMapOfRightSample_d39PlanarClass_eq_mirror
    (n ell : ℕ) (hell : 0 < ell)
    (p : Prop59LeftFiniteClass n ell × Fin ell) :
    Quotient.mk D39PlanarRootedMap.setoid
        ((diskRootedPlanarMapOfRightSample n ell hell
          (prop59FiniteReflectionClassEquiv n ell hell p.1, p.2.rev)).toD39PlanarRootedMap) =
      Quotient.mk D39PlanarRootedMap.setoid
        ((mirrorRootedLocallyFinitePlanarMap
          (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap) := by
  apply congrArg
  simp [diskRootedPlanarMapOfRightSample, Fin.rev_rev]

/-- Helper toward Proposition 5.9. The law of the geometrically reflected
left-side finite rooted sample is the law of the right-side rooted sample
indexed by the proved finite class reflection and reversed boundary mark, when
both laws are viewed in the local topology combinatorial planar rooted-map class space. -/
theorem diskRootedPlanarMapOfRightSample_d39PlanarClass_law
    (n ell : ℕ) (hell : 0 < ell) :
    let Qₗ := Prop59LeftFiniteClass n ell
    let Qᵣ := Prop59RightFiniteClass n ell
    letI : Fintype Qₗ := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
    letI : Fintype Qᵣ := Fintype.ofEquiv Qₗ
      (prop59FiniteReflectionClassEquiv n ell hell)
    letI : MeasurableSpace Qₗ := ⊤
    letI : MeasurableSpace Qᵣ := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace (Quotient D39PlanarRootedMap.setoid) := ⊤
    let μₗ := (uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))
    let μᵣ := (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell))
    μₗ.map (fun p => Quotient.mk D39PlanarRootedMap.setoid
        ((mirrorRootedLocallyFinitePlanarMap
          (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap)) =
      μᵣ.map (fun p => Quotient.mk D39PlanarRootedMap.setoid
        ((diskRootedPlanarMapOfRightSample n ell hell p).toD39PlanarRootedMap)) := by
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
  letI : MeasurableSpace (Quotient D39PlanarRootedMap.setoid) := ⊤
  let μₗ := (uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))
  let μᵣ := (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell))
  let T : Qₗ × Fin ell → Qᵣ × Fin ell := fun p =>
    (prop59FiniteReflectionClassEquiv n ell hell p.1, p.2.rev)
  let R : Qᵣ × Fin ell → Quotient D39PlanarRootedMap.setoid := fun p =>
    Quotient.mk D39PlanarRootedMap.setoid
      ((diskRootedPlanarMapOfRightSample n ell hell p).toD39PlanarRootedMap)
  let L : Qₗ × Fin ell → Quotient D39PlanarRootedMap.setoid := fun p =>
    Quotient.mk D39PlanarRootedMap.setoid
      ((mirrorRootedLocallyFinitePlanarMap
        (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap)
  have hmarked : μₗ.map T = μᵣ := by
    simpa [μₗ, μᵣ, Qₗ, Qᵣ, T] using
      (prop59FiniteReflectionMarkedUniform n ell hell)
  have hpoint : R ∘ T = L := by
    funext p
    exact diskRootedPlanarMapOfRightSample_d39PlanarClass_eq_mirror
      n ell hell p
  have hmap := congrArg (fun ν : Measure (Qᵣ × Fin ell) => ν.map R) hmarked
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hmap
  rw [hpoint] at hmap
  simpa [μₗ, μᵣ, R, L] using hmap





















end DirectedDistances.PaperProofs.Section5
