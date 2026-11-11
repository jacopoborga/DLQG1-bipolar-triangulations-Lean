/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparison3








public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.ReverseComparison4

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

private theorem strictMono_endpoints (φ : unitInterval ≃ₜ unitInterval)
    (hφ : StrictMono φ) : φ 0 = 0 ∧ φ 1 = 1 := by
  have h0 := hφ.monotone (show (0 : unitInterval) ≤ φ.symm 0 from
    (φ.symm 0).property.1)
  have h1 := hφ.monotone (show φ.symm 1 ≤ (1 : unitInterval) from
    (φ.symm 1).property.2)
  rw [φ.apply_symm_apply] at h0 h1
  exact ⟨le_antisymm h0 (φ 0).property.1,
    le_antisymm (φ 1).property.2 h1⟩




theorem represented_orbitFace_leftAtOn
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr))
    (d : (d39FacedBall M r hr).D) (hdO : d ∈ O.val)
    (s : {t : unitInterval // t ∈ openParams}) :
    LeftAtOn
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M x.drawing r hr)
        (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val
      (x.drawing.arc d.1).toPath s := by
  have hborder := ((d39FacedBall M r hr).dartBorders_plOrbitFace_iff
    (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
    (d39FacedBallPLDrawing M x.drawing r hr)
    (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
    (d39FacedBall_connected M r hr) O d).mpr hdO
  have hl := (d39FacedBallPLDrawing M x.drawing r hr).dartBorders_toPath_leftAtOn
    (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) d _ hborder s
  apply (leftAtOn_congr_fun _ _ _ s _).mp hl
  intro t
  exact congrArg (fun p : Polyline => p.toPath t)
    (d39FacedBallPLDrawing_arc M x.drawing r hr d)

/-- Helper toward Proposition 5.16: different restricted face orbits have
different open faces; in particular the two sides cannot be identified by
discarding the reverse alternative when their orbits differ. -/
theorem represented_orbitFace_ne_of_ne
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r)
    (O Q : D39BallFaceCycleOrbit (d39FacedBall M r hr)) (hne : O ≠ Q) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val ≠
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) Q).val := by
  intro heq
  exact hne ((d39FacedBall M r hr).plOrbitFace_injective
    (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
    (d39FacedBallPLDrawing M x.drawing r hr)
    (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
    (d39FacedBall_connected M r hr) (Subtype.ext heq))

/-- Helper toward Proposition 5.16: exterior transport supplies one plane
homeomorphism transporting all restricted orbit faces. Along every image
dart, both the transported source ambient face and the target ambient face
satisfy their own left-side tests. No uniqueness of winding-side faces is
assumed or concluded. -/
theorem exists_represented_left_side_transport_of_external_transport
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (hexterior_transport :
      plBallFaceOrbitMap I
          (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
        (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        H '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
        ((d39FacedBall N r hr).plOrbitFace
          (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N y.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
          (plBallFaceOrbitMap I O)).val) ∧
      ∀ (d : (d39FacedBall M r hr).D)
        (s : {t : unitInterval // t ∈ openParams}),
        LeftAtOn (H '' (x.data.faceOfDart d.1).val)
          (y.drawing.arc (I.toEquiv d).1).toPath s ∧
        LeftAtOn (y.data.faceOfDart (I.toEquiv d).1).val
          (y.drawing.arc (I.toEquiv d).1).toPath s := by
  obtain ⟨H, hor, _hp, ha, hfaces⟩ :=
    ReverseComparison2.exists_represented_plane_homeomorph_of_external_transport
      x y r hr I hexterior_transport
  refine ⟨H, hor, hfaces, ?_⟩
  intro d s
  obtain ⟨φ, hφ, hpath⟩ := ha d
  obtain ⟨h0, h1⟩ := strictMono_endpoints φ hφ
  have hsource : ∀ t : {t : unitInterval // t ∈ openParams},
      LeftAtOn (H '' (x.data.faceOfDart d.1).val)
        ((y.drawing.arc (I.toEquiv d).1).toPath.reparam
          φ φ.continuous h0 h1) t := by
    intro t
    have hl := (leftAtOn_map_iff _ _ t H hor).mp
      (d39PLRepresentation_face_leftAtOn x.data.toD39DrawingRepresentationData
        x.drawing x.arc_eq d.1 t)
    apply (leftAtOn_congr_fun _ _ _ t _).mp hl
    intro u
    change H ((x.drawing.arc d.1).toPath u) =
      (y.drawing.arc (I.toEquiv d).1).toPath (φ u)
    rw [x.arc_eq, y.arc_eq]
    exact hpath u
  exact ⟨(forall_leftAtOn_reparam_iff _ _ φ h0 h1).mp hsource s,
    d39PLRepresentation_face_leftAtOn y.data.toD39DrawingRepresentationData
      y.drawing y.arc_eq (I.toEquiv d).1 s⟩
















































































































end DirectedDistances.PaperProofs.Section5.ReverseComparison4

end
