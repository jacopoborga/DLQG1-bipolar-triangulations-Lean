/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59Part2
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedComparison

/-! The signed PL side theorem now identifies the retained ambient face of a
specified restricted orbit. This closes the face-identification obstruction
recorded in `Prop59Part2` and adds ambient-face transport to its canonical -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3




theorem prop59_representation_original_orbitFace
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) (hdO : d ∈ O.val) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
        (x.data.faceOfDart d.1).val := by
  exact exteriorMarkedComparison_original_orbitFace x r hr d hd O hdO

section CanonicalPair

variable
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
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





theorem prop59_canonicalPair_planeHomeomorph_with_ambientFaces
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
          ∀ t, G (d39DrawingDartArc B x.data.toD39DrawingRepresentationData d.1 t) =
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
            (plBallFaceOrbitMap I O)).val) ∧
      (∀ d : (d39FacedBall M r hr).D,
        d ∈ (d39FacedBall M r hr).original →
          G '' (x.data.faceOfDart d.1).val =
            (y.data.faceOfDart (I.toEquiv d).1).val) := by
  obtain ⟨G, hG, hpos, harc, hfaces⟩ :=
    prop59_canonicalPair_planeHomeomorph
      W H h0 hL hR hfin hRpos hA hmirrorDomain canonical x y r hr I
  refine ⟨G, hG, hpos, harc, hfaces, ?_⟩
  intro d hd
  let O := plBallDartOrbit _ d
  have hdO : d ∈ O.val := Equiv.Perm.SameCycle.rfl
  have hIdO : I.toEquiv d ∈ (plBallFaceOrbitMap I O).val :=
    (plBallFaceOrbitMap_mem_iff I O d).mpr hdO
  have hId := (I.original_iff d).mpr hd
  rw [← prop59_representation_original_orbitFace x r hr d hd O hdO,
    ← prop59_representation_original_orbitFace y r hr (I.toEquiv d) hId
      (plBallFaceOrbitMap I O) hIdO]
  exact hfaces O

end CanonicalPair

end DirectedDistances.PaperProofs.Section5

end
