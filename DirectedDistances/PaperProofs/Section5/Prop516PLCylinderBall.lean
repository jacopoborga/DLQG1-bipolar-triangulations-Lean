/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.BSLocalCriterionSubspace
public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso
public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso2
public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso4
public import DirectedDistances.PaperProofs.Section5.Prop516GeometricStatement
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassMetric







public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.PLCylinderBall

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.Probability
open Set Filter TopologicalSpace MeasureTheory
open scoped ENNReal Topology

universe u



structure Representation (M : D39RootedMap) (B : D39DomainRootedMapV2.{u}) where
  /-- Helper toward Proposition 5.16: the underlying drawing representation. -/
  data : D39DrawingRepresentationData3 M B
  /-- Helper toward Proposition 5.16: the compatible PL drawing. -/
  drawing : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
    M.core.edgeInv M.core.rot (d39VertexClass M)
  /-- Helper toward Proposition 5.16: compatibility of vertex positions. -/
  pos_eq : ∀ v, drawing.pos v = B.map.toPlaneMapWithMissing.pos (data.vertexEquiv v)
  /-- Helper toward Proposition 5.16: compatibility of ordered dart paths. -/
  arc_eq : ∀ d t, (drawing.arc d).toPath t =
    d39DrawingDartArc B data.toD39DrawingRepresentationData d t

/-- Helper toward Proposition 5.16: forget only the duplicate domain-record
type, retaining the geometric map, root, and proved domain witness. -/
@[expose] def domainMap (B : D39DomainRootedMapV2.{u}) : D39DomainRootedMap.{u} :=
  ⟨B.V, B.E, B.map, B.root, B.domain⟩

/-- Helper toward Proposition 5.16: the geometric class of a represented map. -/
@[expose] def geometricClass (B : D39DomainRootedMapV2.{u}) : D39GeomRootedMapClass.{u} :=
  Quotient.mk d39DomainSetoid (domainMap B)

/-- Helper toward Proposition 5.16: all representation data for one geometric
class, without choosing a preferred combinatorial or geometric representative. -/
structure Representative (c : D39GeomRootedMapClass.{u}) where
  /-- Helper toward Proposition 5.16: the combinatorial rooted map. -/
  map : D39RootedMap
  /-- Helper toward Proposition 5.16: the geometric domain map. -/
  geometric : D39DomainRootedMapV2.{u}
  /-- Helper toward Proposition 5.16: the compatible representation. -/
  representation : Representation map geometric
  /-- Helper toward Proposition 5.16: membership in the specified class. -/
  class_eq : geometricClass geometric = c

/-- Helper toward Proposition 5.16: representability by the candidate PL
representation data. This is a literal existence predicate, not a theorem. -/
@[expose] def IsPLRepresentable (c : D39GeomRootedMapClass.{u}) : Prop :=
  Nonempty (Representative c)

/-- Helper toward Proposition 5.16: the subspace of candidate PL-representable
geometric rooted-map classes. -/
@[expose] def X_PL : Set D39GeomRootedMapClass.{u} := {c | IsPLRepresentable c}

section Comparison

variable
    (hProp516GeomToCombBallIso4 :
      ∀ {M N : D39RootedMap} {B C : D39DomainRootedMapV2.{u}}
        (_x : D39DrawingRepresentationData3 M B)
        (_y : D39DrawingRepresentationData3 N C) (r : ℕ) (hr : 0 < r),
        Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) →
        Nonempty (D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)))
    (hProp516PLBallIso2 :
      ∀ {M N : D39RootedMap} {B C : D39DomainRootedMapV2.{u}}
        (_x : Representation M B) (_y : Representation N C) (r : ℕ) (hr : 0 < r),
        Nonempty (D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) →
        Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root))

include hProp516GeomToCombBallIso4 hProp516PLBallIso2 in
/-- Helper toward Proposition 5.16: the two displayed general comparison
dependencies identify geometric positive-radius balls with full faced ball
classes, preserving all retained data. Both directions remain conditional. -/
theorem geomBallIso_iff_ballClass_eq
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2.{u}}
    (x : Representation M B) (y : Representation N C) (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) ↔
      d39BallClass M r hr = d39BallClass N r hr := by
  constructor
  · intro h
    exact (d39BallClass_eq_iff M N r hr).2
      (hProp516GeomToCombBallIso4 x.data y.data r hr h)
  · intro h
    exact hProp516PLBallIso2 x y r hr ((d39BallClass_eq_iff M N r hr).1 h)

include hProp516GeomToCombBallIso4 in
/-- Helper toward Proposition 5.16: two PL representations of the same
geometric class have identical faced ball classes at every positive radius.
Only the displayed geometric-to-combinatorial dependency is consumed. -/
theorem representative_independent {c : D39GeomRootedMapClass.{u}}
    (x y : Representative c) (r : ℕ) (hr : 0 < r) :
    d39BallClass x.map r hr = d39BallClass y.map r hr := by
  have hd : edist (geometricClass x.geometric) (geometricClass y.geometric) = 0 := by
    rw [x.class_eq, y.class_eq, edist_self]
  have hg : Nonempty (D39GeomBallIsoV2 r x.geometric.map x.geometric.root
      y.geometric.map y.geometric.root) :=
    (d39ClassDistance_le_pow_iff_nonempty hr (domainMap x.geometric)
      (domainMap y.geometric)).1 (by
        change edist (geometricClass x.geometric) (geometricClass y.geometric) ≤ _
        rw [hd]
        exact bot_le)
  exact (d39BallClass_eq_iff x.map y.map r hr).2
    (hProp516GeomToCombBallIso4 x.representation.data y.representation.data r hr hg)

include hProp516GeomToCombBallIso4 in
/-- Helper toward Proposition 5.16: positive-radius ball classes exist
uniquely on each PL-representable geometric class, before choosing them. -/
theorem ballClass_existsUnique {c : D39GeomRootedMapClass.{u}}
    (hc : IsPLRepresentable c) (r : ℕ) (hr : 0 < r) :
    ∃! k : D39BallClass, ∀ x : Representative c, d39BallClass x.map r hr = k := by
  obtain ⟨x⟩ := hc
  refine ⟨d39BallClass x.map r hr, ?_, ?_⟩
  · intro y
    exact representative_independent hProp516GeomToCombBallIso4 y x r hr
  · intro k hk
    exact (hk x).symm

/-- Helper toward Proposition 5.16: index `r` denotes the source ball of
positive radius `r + 1`. Choice is made only after conditional existence and
uniqueness have been proved. -/
@[expose] def b (r : ℕ) (x : X_PL) : D39BallClass :=
  Classical.choose (ballClass_existsUnique hProp516GeomToCombBallIso4
    x.property (r + 1) (Nat.succ_pos r))

/-- Helper toward Proposition 5.16: the complete representative-independent
characterization of the chosen ball class at index `r`. -/
theorem b_eq (r : ℕ) (x : X_PL) (y : Representative x.val) :
    b hProp516GeomToCombBallIso4 r x =
      d39BallClass y.map (r + 1) (Nat.succ_pos r) :=
  ((Classical.choose_spec (ballClass_existsUnique hProp516GeomToCombBallIso4
    x.property (r + 1) (Nat.succ_pos r))).1 y).symm

include hProp516PLBallIso2 in
/-- Helper toward Proposition 5.16: agreement of the chosen ball classes
is precisely the required dyadic closed-distance condition. -/
theorem hball (r : ℕ) (x y : X_PL) :
    edist (x : D39GeomRootedMapClass.{u}) y ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔
      b hProp516GeomToCombBallIso4 r x = b hProp516GeomToCombBallIso4 r y := by
  obtain ⟨R⟩ := x.property
  obtain ⟨S⟩ := y.property
  rw [b_eq hProp516GeomToCombBallIso4 r x R, b_eq hProp516GeomToCombBallIso4 r y S]
  conv_lhs => rw [← R.class_eq, ← S.class_eq]
  exact (d39ClassDistance_le_pow_iff_nonempty (Nat.succ_pos r)
    (domainMap R.geometric) (domainMap S.geometric)).trans
      (geomBallIso_iff_ballClass_eq hProp516GeomToCombBallIso4 hProp516PLBallIso2
        R.representation S.representation (r + 1) (Nat.succ_pos r))

/-- Helper toward Proposition 5.16: source ball restriction proves
successor compatibility without the combinatorial-to-geometric premise. -/
theorem hcompat (r : ℕ) (x y : X_PL)
    (h : b hProp516GeomToCombBallIso4 (r + 1) x =
      b hProp516GeomToCombBallIso4 (r + 1) y) :
    b hProp516GeomToCombBallIso4 r x = b hProp516GeomToCombBallIso4 r y := by
  obtain ⟨R⟩ := x.property
  obtain ⟨S⟩ := y.property
  rw [b_eq hProp516GeomToCombBallIso4 (r + 1) x R,
    b_eq hProp516GeomToCombBallIso4 (r + 1) y S] at h
  rw [b_eq hProp516GeomToCombBallIso4 r x R, b_eq hProp516GeomToCombBallIso4 r y S]
  exact d39BallClass_restriction_compatible R.map S.map (r + 1) (Nat.succ_pos r) h

include hProp516PLBallIso2 in
/-- Helper toward Proposition 5.16: the candidate PL cylinder topology is
the geometric class subspace topology, conditional on the two displayed
general comparison dependencies. -/
theorem localClassTopology_eq_subspace :
    localClassTopology (b hProp516GeomToCombBallIso4) =
      (inferInstance : TopologicalSpace X_PL) :=
  localClassTopology_eq_induced (b hProp516GeomToCombBallIso4)
    (hball hProp516GeomToCombBallIso4 hProp516PLBallIso2)
    (hcompat hProp516GeomToCombBallIso4)

include hProp516PLBallIso2 in
/-- Helper toward Proposition 5.16: on the actual geometric subspace with
its Borel sigma algebra, weak convergence is equivalent to convergence of
every faced-ball cylinder mass. The filter is countably generated. -/
theorem tendsto_iff_cylinderMass :
    letI : MeasurableSpace X_PL.{u} := borel X_PL
    letI : BorelSpace X_PL.{u} := ⟨rfl⟩
    ∀ {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
      {μs : ι → ProbabilityMeasure X_PL.{u}} {μ : ProbabilityMeasure X_PL.{u}},
      Tendsto μs L (𝓝 μ) ↔
        ∀ r c, Tendsto (fun i => μs i (b hProp516GeomToCombBallIso4 r ⁻¹' {c})) L
          (𝓝 (μ (b hProp516GeomToCombBallIso4 r ⁻¹' {c}))) := by
  have h := @tendsto_iff_localCylinder X_PL.{u} (fun _ => D39BallClass)
    (b hProp516GeomToCombBallIso4) (fun _ => inferInstance)
    (hcompat hProp516GeomToCombBallIso4)
  rw [localClassTopology_eq_subspace hProp516GeomToCombBallIso4 hProp516PLBallIso2] at h
  exact @h

include hProp516PLBallIso2 in
/-- Helper toward Proposition 5.16: convergence of faced-ball cylinder
masses gives weak convergence on the geometric subspace and after inclusion
into the ambient geometric class space, each with its Borel sigma algebra. -/
theorem tendsto_of_cylinderMass :
    letI : MeasurableSpace D39GeomRootedMapClass.{u} := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass.{u} := ⟨rfl⟩
    letI : MeasurableSpace X_PL.{u} := borel X_PL
    letI : BorelSpace X_PL.{u} := ⟨rfl⟩
    ∀ {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
      {μs : ι → ProbabilityMeasure X_PL.{u}} {μ : ProbabilityMeasure X_PL.{u}},
      (∀ r c, Tendsto (fun i => μs i (b hProp516GeomToCombBallIso4 r ⁻¹' {c})) L
        (𝓝 (μ (b hProp516GeomToCombBallIso4 r ⁻¹' {c})))) →
      Tendsto μs L (𝓝 μ) ∧
        Tendsto (fun i => (μs i).map Subtype.val) L (𝓝 (μ.map Subtype.val)) := by
  let : MeasurableSpace D39GeomRootedMapClass.{u} := borel D39GeomRootedMapClass
  let : BorelSpace D39GeomRootedMapClass.{u} := ⟨rfl⟩
  have h := @tendsto_of_localCylinder_subspace D39GeomRootedMapClass.{u} _ _ _
    X_PL (fun _ => D39BallClass) (b hProp516GeomToCombBallIso4)
    (hball hProp516GeomToCombBallIso4 hProp516PLBallIso2)
    (hcompat hProp516GeomToCombBallIso4) (fun _ => inferInstance)
  rw [localClassTopology_eq_subspace hProp516GeomToCombBallIso4 hProp516PLBallIso2] at h
  exact @h

end Comparison

























































end DirectedDistances.PaperProofs.Section5.PLCylinderBall

end
