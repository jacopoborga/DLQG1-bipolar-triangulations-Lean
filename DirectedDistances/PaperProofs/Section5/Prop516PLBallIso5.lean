/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso4
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness5

/- # Positive winding and intrinsic exterior tests -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology Metric
open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: the closed full-period walk of a
bounded orbit face has winding one on that face when the walk is cyclically
simple. This combines the proved positive angle-sum theorem with the exact
closed-polyline winding bridge. -/
theorem faceWalkPolyline_fullPeriod_hasWinding_one_of_isBounded
    {V : Type*} (A : D39FiniteBall) (vert : A.D → V)
    (P : PLDrawing A.D V A.map.edgeInv A.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : A.D, Relation.EqvGen
      (fun x y => A.map.rot x = y ∨ A.map.edgeInv x = y) d e)
    (O : D39BallFaceCycleOrbit A)
    (hbounded : Bornology.IsBounded (A.plOrbitFace vert P hvert O).val)
    (d : A.D) (hd : d ∈ O.val)
    (hc : (faceWalkPolyline A vert P d
      (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).IsCyclicSimple) :
    ∀ z ∈ (A.plOrbitFace vert P hvert O).val,
      HasWinding
        ((faceWalkPolyline A vert P d
          (Function.minimalPeriod (A.map.faceSucc : A.D → A.D) d - 1)).toPath.cast
          rfl (faceWalkPolyline_closed A vert P d)) z 1 := by
  intro z hz
  exact (A.faceWalkPolyline_fullPeriod_hasWinding_iff_angleSum_eq_one
    vert P hvert hconn O hbounded d hd (faceWalkPolyline_closed A vert P d) hc z hz).mpr
      (A.faceWalkPolyline_fullPeriod_angleSum_eq_one_of_isBounded
        vert P hvert hconn O hbounded d hd (faceWalkPolyline_closed A vert P d) hc z hz)

/-- Helper toward Proposition 5.16: a face with winding one for a
cyclically simple polygon starting along a dart cannot border its reversal.
The signed edge jump would otherwise force winding two on the left. -/
theorem not_dartBorders_flip_of_polygon_angleSum_one
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (q : Polyline) (hc : q.IsCyclicSimple)
    (hzero : q.point 0 = (P.arc d).point 0)
    (hone : q.point 1 = (P.arc d).point 1)
    (himage : q.image ⊆ P.image)
    (hwind : ∀ z ∈ F.val, q.angleSum z = 1) :
    ¬ P.dartBorders (flip d) F := by
  intro hflip
  have hi : 0 + 1 < (P.arc d).points.length := P.arc_length d
  have hqi : 0 + 1 < q.points.length := by have := hc.1; omega
  let x := midpoint ℝ (q.point 0) (q.point 1)
  have hxopen : x ∈ openSegment ℝ (q.point 0) (q.point 1) :=
    midpoint_mem_openSegment (𝕜 := ℝ) _ _
  have hne : q.point 0 ≠ q.point 1 := hc.2.2.1 0 hqi
  have hx0 : x ≠ q.point 0 := by
    intro h
    exact hne (left_mem_openSegment_iff.mp (h ▸ hxopen))
  have hx1 : x ≠ q.point 1 := by
    intro h
    exact hne (right_mem_openSegment_iff.mp (h ▸ hxopen))
  have hxarc : x ∈ openSegment ℝ ((P.arc d).point 0) ((P.arc d).point 1) := by
    simpa only [hzero, hone] using hxopen
  obtain ⟨r, hr, hright⟩ :=
    P.exists_ball_right_subset_of_dartBorders_flip hvert d F hflip hi hxarc
  obtain ⟨s, hs, hjump⟩ := q.angleSum_edge_jump_cyclic_signed hc 0 hqi x
    (openSegment_subset_segment ℝ _ _ hxopen) hx0 hx1
  obtain ⟨l, hl, hleftoff⟩ := q.exists_leftHalfDisc_disjoint_image_cyclic hc 0 hqi x
    (openSegment_subset_segment ℝ _ _ hxopen) hx0 hx1
  have hdir : q.point 1 - q.point 0 ≠ 0 := sub_ne_zero.mpr hne.symm
  obtain ⟨u, hu⟩ := Polyline.leftHalfDisc_nonempty x (q.point 1 - q.point 0)
    (min s l) hdir (lt_min hs hl)
  obtain ⟨v, hv⟩ := Polyline.rightHalfDisc_nonempty x (q.point 1 - q.point 0)
    (min s r) hdir (lt_min hs hr)
  have hvF : v ∈ F.val := hright v
    (ball_subset_ball (min_le_right s r) hv.1) (by
      simpa only [hzero, hone, Nat.zero_add, Set.mem_ofPred_eq] using hv.2)
  have hvoff : v ∉ q.image := fun h => P.face_subset_compl F hvF (himage h)
  have huoff : u ∉ q.image := fun h => Set.disjoint_left.mp hleftoff
    ⟨ball_subset_ball (min_le_right s l) hu.1, hu.2⟩ h
  have hvone := hwind v hvF
  have hvinside : v ∈ q.inside := ⟨hvoff, by rw [hvone]; norm_num⟩
  obtain ⟨ε, hε, hsign⟩ := q.exists_inside_angleSum_sign hc
  have hεone : ε = 1 := (hsign v hvinside).symm.trans hvone
  have hccw : ∀ z ∈ q.inside, q.angleSum z = 1 := by
    intro z hz
    exact (hsign z hz).trans hεone
  have hvalues := (q.angleSum_zero_or_one_of_counterclockwise hccw u huoff).1
  have hj := hjump u v huoff hvoff
    (ball_subset_ball (min_le_left s l) hu.1)
    (ball_subset_ball (min_le_left s r) hv.1) hu.2 hv.2
  rcases hvalues with h | h <;> linarith only [hj, h, hvone]

/-- Helper toward Proposition 5.16: positive polygon winding resolves
the represented dart's forward-versus-reverse incidence alternative.
The polygon simplicity and winding hypotheses remain explicit; they are
not asserted for every represented face. -/
theorem d39PLRepresentation_dartBorders_of_polygon_angleSum_one
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (d : M.core.D) (q : Polyline) (hc : q.IsCyclicSimple)
    (hzero : q.point 0 = (P.arc d).point 0)
    (hone : q.point 1 = (P.arc d).point 1)
    (himage : q.image ⊆ P.image)
    (hwind : ∀ z ∈ (x.faceOfDart d).val, q.angleSum z = 1) :
    P.dartBorders d (d39PLRepresentationFace x P hpos harc (x.faceOfDart d)) := by
  rcases d39PLRepresentation_dartBorders_or_flip x P hpos harc d with h | h
  · exact h
  · exact (not_dartBorders_flip_of_polygon_angleSum_one P
      (fun v => Quotient.exists_rep v) d
      (d39PLRepresentationFace x P hpos harc (x.faceOfDart d))
      q hc hzero hone himage hwind h).elim





theorem d39PLRepresentation_original_orbitFace_of_faceWalk_angleSum_one
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t =
      d39DrawingDartArc B x.toD39DrawingRepresentationData d t)
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) (hdO : d ∈ O.val)
    (n : ℕ)
    (hc : (faceWalkPolyline (d39FacedBall M r hr)
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr) d n).IsCyclicSimple)
    (hwind : ∀ z ∈ (x.faceOfDart d.1).val,
      (faceWalkPolyline (d39FacedBall M r hr)
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr) d n).angleSum z = 1) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val =
        (x.faceOfDart d.1).val := by
  apply (d39PLRepresentation_original_orbitFace_iff_dartBorders
    x P hpos harc r hr d hd O hdO).mpr
  let q := faceWalkPolyline (d39FacedBall M r hr)
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (d39FacedBallPLDrawing M P r hr) d n
  apply d39PLRepresentation_dartBorders_of_polygon_angleSum_one
    x.toD39DrawingRepresentationData P hpos harc d.1 q hc _ _ _ hwind
  · exact (Polyline.point_zero_eq_start q).trans
      ((start_faceWalkPolyline (d39FacedBall M r hr)
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr) d n).trans
          ((congrArg Polyline.start (d39FacedBallPLDrawing_arc M P r hr d)).trans
            (Polyline.point_zero_eq_start (P.arc d.1)).symm))
  · exact (D39FiniteBall.faceWalkPolyline_point_one (d39FacedBall M r hr)
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr) (d39FacedBall_connected M r hr) d n).trans
        (congrArg (fun p : Polyline => p.point 1)
          (d39FacedBallPLDrawing_arc M P r hr d))
  · intro z hz
    have hz' := (image_faceWalkPolyline (d39FacedBall M r hr)
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr) d n).subset hz
    obtain ⟨i, _, hi⟩ := hz'
    exact Or.inr ⟨((d39FacedBall M r hr).map.faceSucc^[i] d).1, by
      simpa only [d39FacedBallPLDrawing_arc] using hi⟩

/-- Helper toward Proposition 5.16: transporting face orbits along a ball
isomorphism is injective, independently of which orbit is exterior. -/
theorem plBallFaceOrbitMap_injective
    {A B : D39FiniteBall} (I : D39BallIso A B) :
    Function.Injective (plBallFaceOrbitMap I) := by
  intro O S h
  apply Subtype.ext
  ext d
  exact (plBallFaceOrbitMap_mem_iff I O d).symm.trans
    ((congrArg (fun T : D39BallFaceCycleOrbit B => I.toEquiv d ∈ T.val) h).to_iff.trans
      (plBallFaceOrbitMap_mem_iff I S d))

/-- Helper toward Proposition 5.16: preservation of the exterior marker
is equivalent to preserving boundedness of every orbit face. The proof
uses the intrinsic unique unbounded orbit in each drawing and introduces
no homeomorphism or augmentation premise. -/
theorem d39FacedBallPLDrawing_external_iff_orbitFace_boundedness
    {M N : D39RootedMap}
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) :
    (∀ d : (d39FacedBall M r hr).D,
      I.toEquiv d ∈ (d39FacedBallPLWithExternal N Q r hr).externalOrbit.val ↔
        d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val) ↔
    ∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      Bornology.IsBounded
        ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val ↔
      Bornology.IsBounded
        ((d39FacedBall N r hr).plOrbitFace
          (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N Q r hr)
          (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
          (plBallFaceOrbitMap I O)).val := by
  classical
  constructor
  · intro hext O
    have he := (plBallFaceOrbitMap_eq_iff I
      (d39FacedBallPLWithExternal M P r hr).externalOrbit
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit).mpr hext
    have hmatch : plBallFaceOrbitMap I O =
        (d39FacedBallPLWithExternal N Q r hr).externalOrbit ↔
        O = (d39FacedBallPLWithExternal M P r hr).externalOrbit := by
      rw [← he]
      exact (plBallFaceOrbitMap_injective I).eq_iff
    have hu := (d39FacedBallPLWithExternal_external_iff N Q r hr
      (plBallFaceOrbitMap I O)).symm.trans
        (hmatch.trans (d39FacedBallPLWithExternal_external_iff M P r hr O))
    simpa only [not_not] using (not_congr hu).symm
  · intro h
    apply (d39FacedBallPLDrawing_external_iff_unbounded P Q r hr I).mpr
    intro hb
    exact d39FacedBallPLWithExternal_unbounded M P r hr
      ((h (d39FacedBallPLWithExternal M P r hr).externalOrbit).mpr hb)































































































































































end DirectedDistances.PaperProofs.Section5

end
