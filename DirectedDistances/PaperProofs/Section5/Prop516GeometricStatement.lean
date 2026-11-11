module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassBorel
public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarLaw
public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.Probability.BSLocalCriterionSubspace

/- # Candidate geometric-class formulation of Proposition 5.16

PL construction. No geometric-to-combinatorial ball identification or
weak-convergence claim is asserted here. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-! ## Totalized UIBHBOT geometric class law -/

/-- Helper toward Proposition 5.16. Totalize the option-valued canonical
geometric class by a fixed default class. -/
noncomputable def uibhbotD39ClassTotal
    (defaultClass : D39GeomRootedMapClass) (W : ℤ → Fin 3) :
    D39GeomRootedMapClass :=
  (uibhbotD39CanonicalClass W).getD defaultClass

/-- Helper toward Proposition 5.16. Candidate Definition 5.8 geometric class
law as a measure. `Measure.map` has no measurability premise. -/
noncomputable def uibhbotDef58GeomClassMeasure
    (defaultClass : D39GeomRootedMapClass) :
    letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
    Measure D39GeomRootedMapClass :=
  letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
  letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    (uibhbotD39ClassTotal defaultClass)

/-- Helper toward Proposition 5.16. Probability-measure form of the
candidate Definition 5.8 law, with measurability stated explicitly. -/
noncomputable def uibhbotDef58GeomClassLaw
    (defaultClass : D39GeomRootedMapClass)
    (hF :
      letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
      letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
      letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
      Measurable (uibhbotD39ClassTotal defaultClass)) :
    letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
    ProbabilityMeasure D39GeomRootedMapClass := by
  letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
  letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  let μ : ProbabilityMeasure (ℤ → Fin 3) := ⟨uibhbotCodeLawRel, inferInstance⟩
  letI : Measurable (uibhbotD39ClassTotal defaultClass) := hF
  exact μ.map (uibhbotD39ClassTotal defaultClass)

/-- Helper toward Proposition 5.16. Almost surely the totalized canonical
class is independent of the chosen default. -/
theorem uibhbotD39ClassTotal_ae_eq
    (defaultClass₁ defaultClass₂ : D39GeomRootedMapClass) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      uibhbotD39ClassTotal defaultClass₁ W =
        uibhbotD39ClassTotal defaultClass₂ W := by
  filter_upwards [uibhbotCodeLawRel_ae_uibhbotD39CanonicalClass_isSome] with W hW
  cases hopt : uibhbotD39CanonicalClass W with
  | none => simp [Option.isSome, hopt] at hW
  | some c => simp [uibhbotD39ClassTotal, hopt]

/-- Helper toward Proposition 5.16. The totalized geometric class measure is
independent of the default because the canonical class is defined almost
surely. -/
theorem uibhbotDef58GeomClassMeasure_default_eq
    (defaultClass₁ defaultClass₂ : D39GeomRootedMapClass) :
    letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
    uibhbotDef58GeomClassMeasure defaultClass₁ =
      uibhbotDef58GeomClassMeasure defaultClass₂ := by
  letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
  letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  exact Measure.map_congr
    (uibhbotD39ClassTotal_ae_eq defaultClass₁ defaultClass₂)

/-! ## Finite disk law parameterized by its canonical class map -/

/-- Helper toward Proposition 5.16. Push a finite disk-rooted planar-map law
through an explicitly supplied candidate canonical geometric-class map.
On the image of `diskRootedPlanarMapOfSample`, the map must return the quotient
class of the source-faithful finite PL drawing, retaining the ordered root,
missing-edge identities, orientation and face structure. Off that finite
support it must return one fixed default class. Measurability remains an
obligation for the probability-measure form below. -/
noncomputable def diskRootedGeometricClassMeasure
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (finiteCanonicalClass : RootedLocallyFinitePlanarMap → D39GeomRootedMapClass) :
    letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    Measure D39GeomRootedMapClass :=
  letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
  letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure.map finiteCanonicalClass

/-- Helper toward Proposition 5.16. Probability-measure form of the finite
geometric-class push-forward, conditional on measurability of its supplied
canonical map. -/
noncomputable def diskRootedGeometricClassLaw
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (finiteCanonicalClass : RootedLocallyFinitePlanarMap → D39GeomRootedMapClass)
    (hcanonical :
      letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
        bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
      letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
        borel RootedLocallyFinitePlanarMap
      letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
      letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
      letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
      letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
      Measurable finiteCanonicalClass) :
    letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    ProbabilityMeasure D39GeomRootedMapClass := by
  letI : TopologicalSpace D39GeomRootedMapClass := inferInstance
  letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : Measurable finiteCanonicalClass := hcanonical
  exact (diskRootedPlanarMapLaw n ell hell hle hmod).map
    finiteCanonicalClass

/-! ## PL-representable subspace and the local-class step -/

/-- Helper toward Proposition 5.16. Candidate predicate that a geometric
class has a domain representative whose plane drawing is heterogeneously
equal to the drawing of a PLDrawing. The edge-carrier identification is part
of this witness and must be supplied by the finite drawing construction. -/
def IsPLRepresentable (x : D39GeomRootedMapClass) : Prop :=
  ∃ A : D39DomainRootedMap,
    Quotient.mk d39DomainSetoid A = x ∧
      ∃ (D : Type) (flip : D → D) (rot : Equiv.Perm D)
        (vert : D → A.V) (P : PLDrawing D A.V flip rot vert),
        HEq A.map.toPlaneMapWithMissing.toPlaneGraphDrawing
          P.toPlaneGraphDrawing

/-- Helper toward Proposition 5.16. The subtype of geometric classes with a
PL-drawing representative. -/
def X_PL := {x : D39GeomRootedMapClass // IsPLRepresentable x}

/- Helper toward Proposition 5.16; the intended cylinder map has these full
binders once `IsPLRepresentable` is strengthened with the combinatorial map
and its rooted drawing representation:

  noncomputable def b (r : ℕ) (x : X_PL) : D39BallClass :=
    d39BallClass (Classical.choose (representation x)) (r + 1)
      (Nat.succ_pos r)

The missing witness fields are a `RootedLocallyFinitePlanarMap` and a proof
that its directed darts, geometric edge identities, missing tags, orientation,
faces and ordered root are represented by the selected PL drawing.

The independence obligation has full binders:

  ∀ (r : ℕ) (x : X_PL) (R₁ R₂ : PLCombinatorialRepresentation x),
    d39BallClass (R₁.map.toD39RootedMap) (r + 1) (Nat.succ_pos r) =
      d39BallClass (R₂.map.toD39RootedMap) (r + 1) (Nat.succ_pos r)

Three proof routes were considered: (1) finite PL drawing uniqueness and
induced rooted-map equality; (2) a rooted geometric dart isomorphism between
the two representatives and transport of finite balls; (3) establish the
`hball` metric characterization first and deduce the cylinder equality.
All three currently stop at the open PL uniqueness and
geometric-to-combinatorial ball isomorphism.

The required `hball` and compatibility binders are:

  ∀ (r : ℕ) (x y : X_PL),
    edist (x.1 : D39GeomRootedMapClass) y.1 ≤
        (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔ b r x = b r y

  ∀ (r : ℕ) (x y : X_PL),
    b (r + 1) x = b (r + 1) y → b r x = b r y -/


























end DirectedDistances.PaperProofs.Section5

end
