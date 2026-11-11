/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorTransportSettle2
public import DirectedDistances.PaperProofs.Section5.Prop516HballForward
public import DirectedDistances.PaperProofs.Section5.Prop516GeometricAssembly




public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open scoped ENNReal

/-- Helper toward Proposition 5.16: forgetting the selected exterior gives
the existing full faced-ball class, without changing any other retained data. -/
@[expose] def ExteriorMarkedBallClass.forget : ExteriorMarkedBallClass → D39BallClass :=
  Quotient.lift (fun A => Quotient.mk D39FiniteBall.setoid A.toD39FiniteBall)
    (fun _ _ ⟨I⟩ => Quotient.sound ⟨I.toD39BallIso⟩)

/-- Helper toward Proposition 5.16: on an actual represented restriction,
forgetting the exterior is exactly the existing faced-ball class. -/
theorem representedExteriorMarkedBallClass_forget
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r) :
    (representedExteriorMarkedBallClass x r hr).forget = d39BallClass M r hr := rfl

private def markedClassOfOrbit
    (q : D39BallClass) (O : D39BallFaceCycleOrbit (Quotient.out q)) :
    ExteriorMarkedBallClass :=
  Quotient.mk exteriorMarkedBallSetoid ⟨Quotient.out q, O⟩

private theorem markedClassOfOrbit_surjective :
    Function.Surjective (fun p : (q : D39BallClass) ×
      D39BallFaceCycleOrbit (Quotient.out q) => markedClassOfOrbit p.1 p.2) := by
  intro a
  induction a using Quotient.inductionOn with
  | _ A =>
    let q : D39BallClass := Quotient.mk D39FiniteBall.setoid A.toD39FiniteBall
    obtain ⟨I⟩ : Nonempty (D39BallIso (Quotient.out q) A.toD39FiniteBall) :=
      Quotient.exact (Quotient.out_eq q)
    obtain ⟨O, hO⟩ := plBallFaceOrbitMap_surjective I A.externalOrbit
    refine ⟨⟨q, O⟩, Quotient.sound ⟨⟨I, ?_⟩⟩⟩
    exact (plBallFaceOrbitMap_eq_iff I O A.externalOrbit).mp hO

/-- Helper toward Proposition 5.16: exterior marking preserves countability.
Over a chosen representative of each countable unmarked class there are
only finitely many face-cycle orbits. No countability of the map carrier
or identification of the marker with a source exterior is assumed. -/
instance instCountableExteriorMarkedBallClass : Countable ExteriorMarkedBallClass := by
  let (q : D39BallClass) : Finite (D39BallFaceCycleOrbit (Quotient.out q)) :=
    Finite.of_injective (fun O => O.val) Subtype.val_injective
  exact Function.Surjective.countable markedClassOfOrbit_surjective

/-- Helper toward Proposition 5.16: the plane homeomorphism of a geometric
ball isomorphism carries the complete restricted PL drawing image to the
target image. Missing geometric edges are included. No original-face input
or correspondence of face-cycle orbits is used. -/
theorem geomBallIso_restricted_drawing_image
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    e.h '' (d39FacedBallPLDrawing M x.drawing r hr).image =
      (d39FacedBallPLDrawing N y.drawing r hr).image := by
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x.data y.data e
  have harc (d : (d39FacedBall M r hr).D) :
      e.h '' ((d39FacedBallPLDrawing M x.drawing r hr).arc d).image =
        ((d39FacedBallPLDrawing N y.drawing r hr).arc (E d)).image := by
    change e.h '' (x.drawing.arc d.1).image = (y.drawing.arc (E d).1).image
    rw [← Polyline.range_toPath, ← Polyline.range_toPath]
    let φ := d39GeomBallIsoV2DartParam e
      ⟨(x.data.dartEquiv d.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x.data r d.1).mp d.2⟩
      (x.data.dartEquiv d.1).2
    have heq (t : unitInterval) :
        e.h ((x.drawing.arc d.1).toPath t) =
          (y.drawing.arc (E d).1).toPath (φ t) := by
      rw [x.arc_eq, y.arc_eq]
      exact d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_arc_map
        x.data y.data e d t
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨φ t, (heq t).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨(x.drawing.arc d.1).toPath (φ.symm t), ⟨φ.symm t, rfl⟩, ?_⟩
      simpa only [φ.apply_symm_apply] using heq (φ.symm t)
  rw [(d39FacedBallPLDrawing M x.drawing r hr).image_eq_union_arcs
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr),
    (d39FacedBallPLDrawing N y.drawing r hr).image_eq_union_arcs
      (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hw
    exact Set.mem_iUnion.mpr ⟨E d, (harc d) ▸ Set.mem_image_of_mem e.h hd⟩
  · intro hz
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hz
    obtain ⟨a, rfl⟩ := E.surjective d
    rw [← harc a] at hd
    obtain ⟨w, hw, rfl⟩ := hd
    exact ⟨w, Set.mem_iUnion.mpr ⟨a, hw⟩, rfl⟩

/-- Helper toward Proposition 5.16: a geometric ball isomorphism preserves
the actual unbounded complementary face of the restricted drawing. This
point-set assertion does not yet identify the induced combinatorial orbit
map with that geometric face transport. -/
theorem geomBallIso_restricted_external_face_image
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    e.h '' ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
      (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit).val =
    ((d39FacedBall N r hr).plOrbitFace
      (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
      (d39FacedBallPLDrawing N y.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
      (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit).val := by
  let P := d39FacedBallPLDrawing M x.drawing r hr
  let Q := d39FacedBallPLDrawing N y.drawing r hr
  let F := (d39FacedBall M r hr).plOrbitFace
    (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D)) P
    (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
    (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit
  have himage : e.h '' P.image = Q.image :=
    geomBallIso_restricted_drawing_image x y r hr e
  let F' : Q.Face := ⟨e.h '' F.val, by
    obtain ⟨z, hz, hF⟩ := F.property
    refine ⟨e.h z, ?_, ?_⟩
    · rw [← himage]
      rintro ⟨w, hw, heq⟩
      exact hz (e.h.injective heq ▸ hw)
    · rw [hF, ← himage]
      exact Homeomorph.image_connectedComponentIn_compl e.h P.image z⟩
  have hnot : ¬ Bornology.IsBounded F'.val := by
    intro hbounded
    exact d39FacedBallPLWithExternal_unbounded M x.drawing r hr
      ((isBounded_planeHomeomorph_image_iff e.h F.val).mp hbounded)
  obtain ⟨O, hO⟩ := (d39FacedBall N r hr).plOrbitFace_surjective
    (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D)) Q
    (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr) F'
  have hext : O = (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit := by
    apply (d39FacedBallPLWithExternal_external_iff N y.drawing r hr O).mpr
    change ¬ Bornology.IsBounded
      ((d39FacedBall N r hr).plOrbitFace
        (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D)) Q
        (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr) O).val
    rw [hO]
    exact hnot
  change F'.val = _
  rw [← hO, hext]





















































































































































































end DirectedDistances.PaperProofs.Section5

end
