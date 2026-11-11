module

public import DirectedDistances.PaperProofs.Section5.Prop59FiniteReflectionGrade3
public import DirectedDistances.PlanarMap.D39RootedMapIsoBall

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory

/-- Helper toward Proposition 5.9. The radius-r+1 local topology faced-ball class
depends only on the whole rooted planar-map isomorphism class. -/
@[expose] noncomputable def prop59D39RootedMapClassBall
    (r : ℕ) : D39PlanarRootedMapClass → D39BallClass :=
  D39PlanarRootedMapClass.lift
    (fun M => d39BallClass M.toD39RootedMap (r + 1) (by omega))
    (by
      intro M N h
      obtain ⟨I⟩ := h
      exact Quotient.sound ⟨I.ballIso (r + 1) (by omega)⟩)

/-- Helper toward Proposition 5.9. The radius-r+1 local topology faced-ball class
map is measurable for the discrete measurable structures used on the class
spaces. -/
theorem measurable_prop59D39RootedMapClassBall
    (r : ℕ) :
    letI : MeasurableSpace D39PlanarRootedMapClass := ⊤
    letI : MeasurableSpace D39BallClass := ⊤
    Measurable (prop59D39RootedMapClassBall r) := by
  intro s hs
  exact MeasurableSpace.measurableSet_top

/-- Helper toward Proposition 5.9. On locally finite planar maps, the local topology
ball-class coordinate is the existing conversion of the faced-ball class. -/
theorem prop59D39RootedMapClassBall_mk
    (r : ℕ) (M : RootedLocallyFinitePlanarMap) :
    prop59D39RootedMapClassBall r
        (Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap) =
      facedFramedBallClassToD39BallClass
        (rootedLocallyFiniteFacedBallClass r M) := by
  simpa [prop59D39RootedMapClassBall,
    RootedLocallyFinitePlanarMap.toD39PlanarRootedMap] using
    d39PlanarRootedMap_ballClass_eq_facedFramedBallClassToD39BallClass M r

/-- Helper toward Proposition 5.9. At every positive finite boundary length,
the law of the radius-r+1 local topology faced-ball class of the reflected left
sample equals that of the right finite sample. This is the push-forward of
the full rooted local topology class-law equality. -/
theorem diskRootedPlanarMapOfRightSample_d39BallClass_law
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
    letI : MeasurableSpace D39PlanarRootedMapClass := ⊤
    letI : MeasurableSpace D39BallClass := ⊤
    let μₗ := (uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))
    let μᵣ := (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell))
    μₗ.map (fun p => prop59D39RootedMapClassBall r
        (Quotient.mk D39PlanarRootedMap.setoid
          ((mirrorRootedLocallyFinitePlanarMap
            (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap))) =
      μᵣ.map (fun p => prop59D39RootedMapClassBall r
        (Quotient.mk D39PlanarRootedMap.setoid
          ((diskRootedPlanarMapOfRightSample n ell hell p).toD39PlanarRootedMap))) := by
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
  letI : MeasurableSpace D39PlanarRootedMapClass := ⊤
  letI : MeasurableSpace D39BallClass := ⊤
  let μₗ := (uniformCountingMeasure Qₗ).prod (uniformCountingMeasure (Fin ell))
  let μᵣ := (uniformCountingMeasure Qᵣ).prod (uniformCountingMeasure (Fin ell))
  let ball := prop59D39RootedMapClassBall r
  let fₗ : Qₗ × Fin ell → D39PlanarRootedMapClass := fun p =>
    Quotient.mk D39PlanarRootedMap.setoid
      ((mirrorRootedLocallyFinitePlanarMap
        (diskRootedPlanarMapOfSample n ell hell p)).toD39PlanarRootedMap)
  let fᵣ : Qᵣ × Fin ell → D39PlanarRootedMapClass := fun p =>
    Quotient.mk D39PlanarRootedMap.setoid
      ((diskRootedPlanarMapOfRightSample n ell hell p).toD39PlanarRootedMap)
  have hfₗ : Measurable fₗ := measurable_of_countable _
  have hfᵣ : Measurable fᵣ := measurable_of_countable _
  have hball : Measurable ball := measurable_prop59D39RootedMapClassBall r
  have hclass := diskRootedPlanarMapOfRightSample_d39PlanarClass_law
    n ell hell
  change μₗ.map (ball ∘ fₗ) = μᵣ.map (ball ∘ fᵣ)
  calc
    μₗ.map (ball ∘ fₗ) = (μₗ.map fₗ).map ball :=
      (Measure.map_map hball hfₗ).symm
    _ = (μᵣ.map fᵣ).map ball :=
      congrArg (fun ν : Measure D39PlanarRootedMapClass => ν.map ball) hclass
    _ = μᵣ.map (ball ∘ fᵣ) := Measure.map_map hball hfᵣ





























end DirectedDistances.PaperProofs.Section5
