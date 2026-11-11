/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly
public import DirectedDistances.PaperProofs.Section5.Prop516BallMarkerPreservation
public import DirectedDistances.PaperProofs.Section3.BSTopologyConcreteSystem









public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16: two face-cycle orbits containing one
common dart are equal. This is the orbit-identification step available from
the ball marker lemmas once a common incidence has been identified. -/
theorem d39GeomBallIso_faceOrbit_eq_of_common_dart {A : D39FiniteBall}
    (O S : D39BallFaceCycleOrbit A) (d : A.D)
    (hdO : d ∈ O.val) (hdS : d ∈ S.val) : O = S :=
  plBallFaceCycleOrbit_eq_of_mem O S d hdO hdS

/-- Helper toward Proposition 5.16: ambient face-orbit vertex containment
implies that every dart of the face, including both endpoint incidences, is
retained. -/
private theorem d39BallContainsOriginalFace_of_faceOrbitVertices
    (M : D39RootedMap) (r : ℕ) (d : M.core.D)
    (hvertices : ∀ e,
      Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e →
        d39VertexClass M e ∈ d39BallVertices M r) :
    d39BallContainsOriginalFace M r d := by
  apply (d39BallContainsOriginalFace_iff M r d).2
  exact hvertices

/-- Helper toward Proposition 5.16: a retained geometric face and its image
under `D39GeomBallIsoV2.faceEquiv` each have original-face incidence darts in
their represented combinatorial balls. The statement follows from the two
retained-face/orbit characterizations; it does not identify those witnesses
under the ball-dart equivalence. -/
theorem d39DrawingRepresentationData3_geomBallIso_retainedFace_original_incidence_witnesses
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (F : {F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces B.map B.root r}) :
    (∃ d : {d : M.core.D // d ∈ d39BallDarts M r},
      x.faceOfDart d.1 = F.1 ∧ d ∈ (d39FacedBall M r e.radius_pos).original) ∧
    (∃ q : {q : N.core.D // q ∈ d39BallDarts N r},
      y.faceOfDart q.1 = (e.faceEquiv F).1 ∧
        q ∈ (d39FacedBall N r e.radius_pos).original) := by
  obtain ⟨d, hd⟩ := x.face_surjective F.1
  have hdret : x.faceOfDart d ∈ d39GeomRetainedFaces B.map B.root r := by
    simpa only [hd] using F.2
  have hvertices :=
    (d39DrawingRepresentationData3_retainedFace_iff_ballOrbitVertices x r d).mp hdret
  have horiginal := d39BallContainsOriginalFace_of_faceOrbitVertices M r d hvertices
  have hdBall : d ∈ d39BallDarts M r :=
    horiginal d Equiv.Perm.SameCycle.rfl
  refine ⟨⟨⟨d, hdBall⟩, hd, ?_⟩, ?_⟩
  · change d39BallContainsOriginalFace M r d
    exact horiginal
  · obtain ⟨q, hq⟩ := y.face_surjective (e.faceEquiv F).1
    have hqret : y.faceOfDart q ∈ d39GeomRetainedFaces C.map C.root r := by
      simpa only [hq] using (e.faceEquiv F).2
    have hqvertices :=
      (d39DrawingRepresentationData3_retainedFace_iff_ballOrbitVertices y r q).mp hqret
    have hqoriginal :=
      d39BallContainsOriginalFace_of_faceOrbitVertices N r q hqvertices
    have hqBall : q ∈ d39BallDarts N r :=
      hqoriginal q Equiv.Perm.SameCycle.rfl
    refine ⟨⟨q, hqBall⟩, hq, ?_⟩
    change d39BallContainsOriginalFace N r q
    exact hqoriginal

/-- Helper toward Proposition 5.16: an equivalence of complete finite stars
that intertwines ambient rotation and preserves the retained subsets also
intertwines their first-return rotations. This is the precise generic
reduction for a ball boundary; it does not supply the required star map or
ambient-successor compatibility for the geometric ball equivalence. -/
theorem d39BallFirstReturn_comm_of_completeStar_rotation_comm
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (S : Finset α) (T : Finset β) (E : α ≃ β)
    (hmem : ∀ z, z ∈ S ↔ E z ∈ T)
    (hcomm : ∀ z, E (σ z) = τ (E z))
    (hreturnS : ∀ z : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) z.1 ∈ S)
    (hreturnT : ∀ z : T, ∃ k : ℕ, 0 < k ∧ (τ ^ k) z.1 ∈ T)
    (d : S) :
    E ((cyclicFirstReturn σ S hreturnS d).1) =
      (cyclicFirstReturn τ T hreturnT
        ⟨E d.1, (hmem d.1).mp d.2⟩).1 := by
  exact cyclicFirstReturn_map_of_equiv σ τ S T E hmem hcomm
    hreturnS hreturnT d













































end DirectedDistances.PaperProofs.Section5

end
