/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59Part1

/-! The canonical mirrored representation is supplied as data, exactly as in
OPEN 1. No law equality or external-orbit identification is a premise. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. On the code construction event, the
reverse-root face orbit of the canonical code map is infinite. -/
theorem prop59_code_rootSideOrbit_infinite
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) :
    let M := (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap.toD39RootedMap
    {d | Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv)
      (M.core.edgeInv M.rootMark.dart) d}.Infinite := by
  obtain ⟨Hc, hhit, C₀, hcap, hEq⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hW).1
  have hHc : Hc = H := Subsingleton.elim _ _
  subst Hc
  dsimp only
  rw [hEq]
  exact prop59_canonical_outerOrbit_infinite W H h0 hL hR hfin hRpos

/-- Helper toward Proposition 5.9. The mirrored canonical code has an
infinite reverse-root face orbit on the same construction event. -/
theorem prop59_mirroredCode_rootSideOrbit_infinite
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) :
    let M := (mirrorRootedLocallyFinitePlanarMap
      (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap
    {d | Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv)
      (M.core.edgeInv M.rootMark.dart) d}.Infinite := by
  exact prop59_mirror_rootSideOrbit_infinite
    (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap
    (prop59_code_rootSideOrbit_infinite W hW H h0 hL hR hfin hRpos)

section CanonicalPair

variable
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)


variable
    (hA : D39GeomDomain
      (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos)
      (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin))
    (hmirrorDomain : D39GeomDomain
      (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos).geomMirror
      (d39GeomMirrorRoot (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin)))
    (canonical : D39DrawingRepresentationData3
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
      ⟨_, _, (uibhbotD39CanonicalAssemblyMap W H h0 hL hR hfin hRpos).geomMirror,
        d39GeomMirrorRoot (uibhbotD39CanonicalAssemblyRoot W H h0 hL hR hfin),
        hmirrorDomain⟩)

include H h0 hL hR hfin hRpos hA hmirrorDomain canonical

/-- Helper toward Proposition 5.9. A representation of the mirrored code by
the canonical infinite assembly forces membership in the construction event:
the finite null default cannot have its infinitely many distinct darts. -/
theorem prop59_mirroredRepresentation_on_event :
    W ∈ uibhbotRootedPlanarMapConullEvent := by
  have _hA := hA
  by_contra hW
  let E := uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin
    (uibhbotD39PastCanonicalDrawing W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
    (uibhbotD39FutureCanonicalDrawing W H h0)
    (uibhbotD39FutureCanonicalDrawing_pos W H h0)
    (uibhbotD39FutureCanonicalDrawing_image W H h0)
    (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)
  let f : ℕ → (uibhbotRootedPlanarMapOfCode W).D := fun n =>
    canonical.dartEquiv.symm (E (wholePlaneDartι W 0 (n, false)))
  have hf : Function.Injective f := by
    intro n m hnm
    exact congrArg Prod.fst (wholePlaneDartι_injective W 0
      (E.injective (canonical.dartEquiv.symm.injective hnm)))
  have hfinite : Finite (uibhbotRootedPlanarMapOfCode W).D := by
    rw [uibhbotRootedPlanarMapOfCode_off_event W hW]
    unfold uibhbotRootedPlanarMapNullDefault
    change Finite (StageDart _)
    infer_instance
  let prop59Part2_finiteCodeDarts : Finite (uibhbotRootedPlanarMapOfCode W).D := hfinite
  exact (Set.infinite_range_of_injective hf) (Set.toFinite _)

/-- Helper toward Proposition 5.9. In every PL representation of the
canonical mirrored code, the reverse-root side lies in the selected
unbounded orbit of each positive-radius ball. OPEN 1 is used only through
the displayed canonical representation data. -/
theorem prop59_mirroredRepresentation_rootSide_mem_external
    {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) B)
    (r : ℕ) (hr : 0 < r) :
    let M := (mirrorRootedLocallyFinitePlanarMap
      (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap
    (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart ∈
      (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit.val := by
  apply prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
  exact prop59_mirroredCode_rootSideOrbit_infinite W
    (prop59_mirroredRepresentation_on_event W H h0 hL hR hfin hRpos
      hA hmirrorDomain canonical) H h0 hL hR hfin hRpos

/-- Helper toward Proposition 5.9. OPEN 2 holds for any two PL
representations of the canonical mirrored code, including the mirrored
canonical assembly representation. No exterior transport is assumed. -/
theorem prop59_canonicalPair_externalOrbit_eq
    {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) B)
    (y : PLCylinderBall.Representation
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso
      (d39FacedBall ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) r hr)
      (d39FacedBall ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) r hr)) :
    let M := (mirrorRootedLocallyFinitePlanarMap
      (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap
    plBallFaceOrbitMap I
        (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
      (d39FacedBallPLWithExternal M y.drawing r hr).externalOrbit := by
  exact prop59_representedExternalOrbit_eq_of_missingRootSide_mem x y r hr I
    (mirrorRootedLocallyFiniteMap
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap).frameEdge_missing
    (mirrorRootedLocallyFiniteMap
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap).frameEdge_missing
    (prop59_mirroredRepresentation_rootSide_mem_external
      W H h0 hL hR hfin hRpos hA hmirrorDomain canonical x r hr)
    (prop59_mirroredRepresentation_rootSide_mem_external
      W H h0 hL hR hfin hRpos hA hmirrorDomain canonical y r hr)


/-- Helper toward Proposition 5.9. The unmirrored canonical code also has
its reverse-root side in the restricted exterior in every PL representation.
The supplied mirrored assembly data rules out the finite null default. -/
theorem prop59_assemblyRepresentation_rootSide_mem_external
    {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation
      (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap.toD39RootedMap B)
    (r : ℕ) (hr : 0 < r) :
    let N := (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap.toD39RootedMap
    (d39FacedBall N r hr).map.edgeInv (d39FacedBall N r hr).rootDart ∈
      (d39FacedBallPLWithExternal N x.drawing r hr).externalOrbit.val := by
  apply prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
  exact prop59_code_rootSideOrbit_infinite W
    (prop59_mirroredRepresentation_on_event W H h0 hL hR hfin hRpos
      hA hmirrorDomain canonical) H h0 hL hR hfin hRpos

/-- Helper toward Proposition 5.9. The proved canonical OPEN 2 comparison
supplies the plane homeomorphism, vertex positions, ordered dart paths and
restricted orbit-face images of the existing reverse comparison. This does
not assert the additional retained ambient-face fields of OPEN 3. -/
theorem prop59_canonicalPair_planeHomeomorph
    {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) B)
    (y : PLCylinderBall.Representation
      ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso
      (d39FacedBall ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) r hr)
      (d39FacedBall ((mirrorRootedLocallyFinitePlanarMap
        (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) r hr)) :
    let M := (mirrorRootedLocallyFinitePlanarMap
      (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap
    ∃ G : ℂ ≃ₜ ℂ, OrientationPreserving G ∧
      (∀ d : (d39FacedBall M r hr).D,
        G (B.map.toPlaneMapWithMissing.pos
          (x.data.vertexEquiv (d39VertexClass M d.1))) =
          C.map.toPlaneMapWithMissing.pos
            (y.data.vertexEquiv (d39VertexClass M (I.toEquiv d).1))) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, G (d39DrawingDartArc B x.data.toD39DrawingRepresentationData
              d.1 t) =
            d39DrawingDartArc C y.data.toD39DrawingRepresentationData
              (I.toEquiv d).1 (φ t)) ∧
      (∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        G '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
          ((d39FacedBall M r hr).plOrbitFace
            (restrictedVertex y.drawing (d39BallDarts M r : Set M.core.D))
            (d39FacedBallPLDrawing M y.drawing r hr)
            (d39FacedBallPLDrawing_vertex_surjective M y.drawing r hr)
            (plBallFaceOrbitMap I O)).val) := by
  exact prop59_representedPlaneHomeomorph_of_open2 x y r hr I
    (prop59_canonicalPair_externalOrbit_eq
      W H h0 hL hR hfin hRpos hA hmirrorDomain canonical x y r hr I)

end CanonicalPair


























































end DirectedDistances.PaperProofs.Section5

end
