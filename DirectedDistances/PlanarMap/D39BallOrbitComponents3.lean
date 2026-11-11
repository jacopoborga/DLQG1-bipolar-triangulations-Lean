/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents2

/- # Geometric frontiers toward face-orbit identification

Helpers toward Proposition 5.16. Frontiers are described using actual dart
arcs, without assuming uniqueness of a face-successor orbit. Independent -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Metric Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: a bordering dart's entire arc lies on
the geometric frontier, including its endpoints and all polyline bends. -/
theorem dartBorders_arc_subset_frontier (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) :
    (P.arc d).image ⊆ frontier F.val := by
  intro z hz
  rw [frontier, (P.face_open_frontier_subset_image hvert F).1.interior_eq]
  exact ⟨P.dartBorders_arc_subset_closure hvert d F hF hz,
    fun hzF => P.face_subset_compl F hzF (Or.inr ⟨d, hz⟩)⟩

/-- Helper toward Proposition 5.16: at an open point of a dart segment,
a face accumulates precisely when it borders one of the two original darts.
The two alternatives may coincide, as they do along a bridge. -/
theorem mem_closure_face_openSegment_iff_dartBorders
    (hvert : Function.Surjective vert) (d : D) (F : P.Face) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {q : ℂ}
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    q ∈ closure F.val ↔ P.dartBorders d F ∨ P.dartBorders (flip d) F := by
  constructor
  · intro hqF
    obtain ⟨G, hG⟩ := P.dartBorders_exists_of_wedge_compl d
      (P.wedgeIn_compl_image hvert (P.arc d).start
        (P.arc d).initialDirection (P.initial_nonzero d))
    obtain ⟨H, hH⟩ := P.dartBorders_exists_of_wedge_compl (flip d)
      (P.wedgeIn_compl_image hvert (P.arc (flip d)).start
        (P.arc (flip d)).initialDirection (P.initial_nonzero (flip d)))
    obtain ⟨r, hr, hleft⟩ := P.exists_ball_left_subset_of_dartBorders hvert d G hG hi hq
    obtain ⟨s, hs, hright⟩ :=
      P.exists_ball_right_subset_of_dartBorders_flip hvert d H hH hi hq
    let U := F.val ∩ ball q (min r s)
    have hU : IsOpen U :=
      (P.face_open_frontier_subset_image hvert F).1.inter isOpen_ball
    have hUne : U.Nonempty := by
      obtain ⟨y, hyF, hyq⟩ := Metric.mem_closure_iff.mp hqF (min r s) (lt_min hr hs)
      exact ⟨y, hyF, by simpa only [mem_ball, dist_comm] using hyq⟩
    let u := (P.arc d).point (i + 1) - (P.arc d).point i
    have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
    obtain ⟨y, ⟨hyF, hyball⟩, hyline⟩ :=
      (Polyline.dense_compl_edgeLine q u hu).inter_open_nonempty U hU hUne
    have hside : (star u * (y - q)).im ≠ 0 := hyline
    rcases lt_or_gt_of_ne hside with hneg | hpos
    · have hyH : y ∈ H.val := hright y
        (ball_subset_ball (min_le_right r s) hyball) hneg
      exact Or.inr ((P.faces_eq_of_mem hyH hyF) ▸ hH)
    · have hyG : y ∈ G.val := hleft y
        (ball_subset_ball (min_le_left r s) hyball) hpos
      exact Or.inl ((P.faces_eq_of_mem hyG hyF) ▸ hG)
  · rintro (hF | hF)
    · exact P.dartBorders_arc_subset_closure hvert d F hF
        ((P.arc d).segmentAt_subset_image hi (openSegment_subset_segment ℝ _ _ hq))
    · apply P.dartBorders_arc_subset_closure hvert (flip d) F hF
      rw [P.arc_image_flip]
      exact (P.arc d).segmentAt_subset_image hi (openSegment_subset_segment ℝ _ _ hq)

/-- Helper toward Proposition 5.16: a face accumulating at a segment
endpoint has regular frontier points in every prescribed ball about that
endpoint. Regular means avoiding all polyline vertices, including bends. -/
theorem face_endpoint_frontier_not_vertex_mem_ball
    (hvert : Function.Surjective vert) (F : P.Face) (q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1))
    (hqcl : q ∈ closure F.val) {s : ℝ} (hs : 0 < s) :
    ∃ x ∈ frontier F.val, x ∈ ball q s ∧ ∀ (e : D) (j : ℕ),
      j < (P.arc e).points.length → x ≠ (P.arc e).point j := by
  obtain ⟨r₀, hr₀, hisolate⟩ := P.polyline_vertices_locally_isolated q
  let r := min r₀ s
  have hr : 0 < r := lt_min hr₀ hs
  have hopen := (P.face_open_frontier_subset_image hvert F).1
  have hqimage : q ∈ P.image := by
    rcases hq with rfl | rfl
    · exact Or.inr ⟨d, (P.arc d).point_mem_image (by omega)⟩
    · exact Or.inr ⟨d, (P.arc d).point_mem_image hi⟩
  obtain ⟨w, hwF, hwr⟩ := Metric.mem_closure_iff.mp hqcl r hr
  have hwU : w ∈ ball q r \ {q} := by
    refine ⟨?_, ?_⟩
    · rwa [mem_ball, dist_comm]
    · intro he
      exact P.face_subset_compl F hwF (he ▸ hqimage)
  obtain ⟨y, hyseg, hyball, hyne⟩ := segment_endpoint_nearby _ _ q
    ((P.arc_simple d).1 i hi) hq r hr
  have hyimage : y ∈ P.image :=
    Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hyseg⟩
  have hfront : ∃ x ∈ ball q r \ {q}, x ∈ frontier F.val := by
    by_contra hnone
    have hsubset : ball q r \ {q} ⊆ F.val := by
      apply (punctured_ball_isPreconnected q r hr).subset_of_closure_inter_subset
        hopen ⟨w, hwU, hwF⟩
      intro x hx
      by_contra hxF
      apply hnone
      refine ⟨x, hx.2, hx.1, ?_⟩
      rw [hopen.interior_eq]
      exact hxF
    exact P.face_subset_compl F (hsubset ⟨hyball, hyne⟩) hyimage
  obtain ⟨x, hxU, hxfront⟩ := hfront
  refine ⟨x, hxfront, ball_subset_ball (min_le_right r₀ s) hxU.1, ?_⟩
  intro e j hj he
  have hxq : x = q := by
    rw [he]
    exact hisolate e j hj (he ▸ ball_subset_ball (min_le_left r₀ s) hxU.1)
  exact hxU.2 hxq

/-- Helper toward Proposition 5.16: a regular frontier point belongs to
an actual arc whose oriented dart borders that very face. -/
theorem exists_mem_arc_dartBorders_of_frontier_not_vertex
    (hvert : Function.Surjective vert) (F : P.Face) {x : ℂ}
    (hx : x ∈ frontier F.val)
    (hnot : ∀ (e : D) (j : ℕ), j < (P.arc e).points.length →
      x ≠ (P.arc e).point j) :
    ∃ d : D, x ∈ (P.arc d).image ∧ P.dartBorders d F := by
  have hximage := (P.face_open_frontier_subset_image hvert F).2 hx
  have harc : ∃ d, x ∈ (P.arc d).image := by
    rcases hximage with ⟨v, rfl⟩ | h
    · obtain ⟨d, rfl⟩ := hvert v
      exact ⟨d, Or.inl (P.arc_start d).symm⟩
    · exact h
  obtain ⟨d, hd⟩ := harc
  rcases hd with hstart | ⟨i, hi, hseg⟩
  · exact (hnot d 0 (by have := P.arc_length d; omega)
      (hstart.trans (P.arc d).point_zero_eq_start.symm)).elim
  · have hq := mem_openSegment_of_ne_left_right
      (hnot d i (by omega)).symm (hnot d (i + 1) hi).symm hseg
    rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hq).mp
        (frontier_subset_closure hx) with hF | hF
    · exact ⟨d, (P.arc d).segmentAt_subset_image hi hseg, hF⟩
    · refine ⟨flip d, ?_, hF⟩
      rw [P.arc_image_flip]
      exact (P.arc d).segmentAt_subset_image hi hseg

/-- Helper toward Proposition 5.16: the frontier of any face of a finite
PL drawing is exactly the union of the closed arcs of darts bordering it.
This includes all graph vertices and polyline bends, and does not assert
that the bordering darts form just one face-successor orbit. -/
theorem frontier_face_eq_iUnion_dartBorders_arcs [Finite D]
    (hvert : Function.Surjective vert) (F : P.Face) :
    frontier F.val = ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image := by
  let K := ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
  have hclosed : IsClosed K := isClosed_iUnion_of_finite fun d =>
    isClosed_iUnion_of_finite fun _ => (P.arc d).isCompact_image.isClosed
  apply Subset.antisymm
  · intro q hqfront
    by_contra hqK
    obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp
      (hclosed.isOpen_compl.mem_nhds hqK)
    have hqimage := (P.face_open_frontier_subset_image hvert F).2 hqfront
    have harc : ∃ d, q ∈ (P.arc d).image := by
      rcases hqimage with ⟨v, rfl⟩ | h
      · obtain ⟨d, rfl⟩ := hvert v
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact h
    obtain ⟨d, hd⟩ := harc
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hd with hstart | ⟨i, hi, hqi⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hqi⟩
    obtain ⟨i, hi, hqi⟩ := hseg
    by_cases hqend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
    · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
        hvert F q d hi hqend (frontier_subset_closure hqfront) hs
      obtain ⟨e, hxe, heF⟩ :=
        P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
      exact hsafe hxball (mem_iUnion₂.mpr ⟨e, heF, hxe⟩)
    · have hqopen := mem_openSegment_of_ne_left_right
        (fun he => hqend (Or.inl he.symm)) (fun he => hqend (Or.inr he.symm)) hqi
      rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hqopen).mp
          (frontier_subset_closure hqfront) with hF | hF
      · exact hqK (mem_iUnion₂.mpr
          ⟨d, hF, (P.arc d).segmentAt_subset_image hi hqi⟩)
      · apply hqK
        apply mem_iUnion₂.mpr
        refine ⟨flip d, hF, ?_⟩
        rw [P.arc_image_flip]
        exact (P.arc d).segmentAt_subset_image hi hqi
  · intro q hq
    obtain ⟨d, hd, hqd⟩ := mem_iUnion₂.mp hq
    exact P.dartBorders_arc_subset_frontier hvert d F hd hqd

/-- Helper toward Proposition 5.16: any two points of a geometric face
are joined by a finite polyline lying wholly in that face. This gives a
finite polygonal connecting path without asserting boundary tracing. -/
theorem exists_polyline_in_face (hvert : Function.Surjective vert) (F : P.Face)
    (x y : ℂ) (hx : x ∈ F.val) (hy : y ∈ F.val) :
    ∃ p : Polyline, p.start = x ∧ p.finish = y ∧ p.image ⊆ F.val := by
  let R : Set ℂ := {z | ∃ p : Polyline,
    p.start = x ∧ p.finish = z ∧ p.image ⊆ F.val}
  have hext (z w : ℂ) (hz : z ∈ R) (hzw : segment ℝ z w ⊆ F.val) : w ∈ R := by
    obtain ⟨p, hpx, hpz, hpF⟩ := hz
    let q := Polyline.ofHead z [w]
    have hqs : q.start = z := rfl
    have hqf : q.finish = w := rfl
    have hqi : q.image = segment ℝ z w := by
      rw [← Polyline.range_toPath]
      exact Path.range_segment z w
    have hjoin : p.finish = q.start := hpz.trans hqs.symm
    refine ⟨Polyline.boundaryConcat p q, ?_, ?_, ?_⟩
    · exact (Polyline.start_boundaryConcat p q).trans hpx
    · exact (Polyline.finish_boundaryConcat p q (show 2 ≤ 2 from le_rfl)).trans hqf
    · rw [Polyline.image_boundaryConcat p q hjoin, hqi]
      exact union_subset hpF hzw
  have hRF : R ⊆ F.val := by
    rintro z ⟨p, _, hpz, hpF⟩
    have hpfinish : p.finish ∈ p.image := by
      rw [← Polyline.range_toPath]
      exact ⟨1, p.toPath.target⟩
    exact hpz ▸ hpF hpfinish
  have hopen := (P.face_open_frontier_subset_image hvert F).1
  have hRopen : IsOpen R := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds (hRF hz))
    refine ⟨r, hr, ?_⟩
    intro w hw
    exact hext z w hz (fun u hu => hball
      ((convex_ball z r).segment_subset (mem_ball_self hr) hw hu))
  have hxR : x ∈ R := by
    refine ⟨Polyline.ofHead x [], rfl, rfl, ?_⟩
    intro z hz
    have hzx : z = x := by simpa [Polyline.image, Polyline.ofHead, Polyline.start] using hz
    exact hzx ▸ hx
  have hconn : IsPreconnected F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF]
    exact isPreconnected_connectedComponentIn
  have hsub : F.val ⊆ R := by
    apply hconn.subset_of_closure_inter_subset hRopen ⟨x, hx, hxR⟩
    rintro z ⟨hzcl, hzF⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzF)
    obtain ⟨w, hwR, hwz⟩ := Metric.mem_closure_iff.mp hzcl r hr
    have hwball : w ∈ ball z r := by simpa only [mem_ball, dist_comm] using hwz
    exact hext w z hwR (fun u hu => hball
      ((convex_ball z r).segment_subset hwball (mem_ball_self hr) hu))
  exact hsub hy

/-- Helper toward Proposition 5.16: each complementary face is path
connected; its connectedness and openness follow from its actual component
definition and the closedness of the drawing. -/
theorem face_isPathConnected (hvert : Function.Surjective vert) (F : P.Face) :
    IsPathConnected F.val := by
  obtain ⟨z, hz, hF⟩ := F.property
  have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
  refine ⟨z, hzF, ?_⟩
  intro y hy
  obtain ⟨p, hpz, hpy, hpF⟩ := P.exists_polyline_in_face hvert F z y hzF hy
  refine ⟨p.toPath.cast hpz.symm hpy.symm, ?_⟩
  intro t
  apply hpF
  rw [← Polyline.range_toPath]
  exact ⟨t, rfl⟩

/-- Helper toward Proposition 5.16: a dart bordering a specified face
has a whole sufficiently small initial sector in that face. -/
theorem exists_initialSector_subset_of_dartBorders [Finite D]
    (hvert : Function.Surjective vert) (d : D) (F : P.Face)
    (hd : P.dartBorders d F) :
    ∃ r : ℝ, 0 < r ∧ P.initialSector d r ⊆ F.val := by
  obtain ⟨r, hr, G, hG, _⟩ := P.exists_ball_initialSector_subset_unique_face hvert d
  have hGF : G = F := P.dartBorders_face_unique d G F
    (P.dartBorders_of_initialSector_subset hvert d hr G hG) hd
  exact ⟨r, hr, hGF ▸ hG⟩

/-- Helper toward Proposition 5.16: initial sectors of any two darts
bordering the same face can be joined inside that face, uniformly for all
choices of the two points in the sectors. Boundary tracing remains separate. -/
theorem exists_joinedIn_initialSectors_of_dartBorders [Finite D]
    (hvert : Function.Surjective vert) (d e : D) (F : P.Face)
    (hd : P.dartBorders d F) (he : P.dartBorders e F) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      P.initialSector d r ⊆ F.val ∧ P.initialSector e s ⊆ F.val ∧
      ∀ x ∈ P.initialSector d r, ∀ y ∈ P.initialSector e s, JoinedIn F.val x y := by
  obtain ⟨r, hr, hdF⟩ := P.exists_initialSector_subset_of_dartBorders hvert d F hd
  obtain ⟨s, hs, heF⟩ := P.exists_initialSector_subset_of_dartBorders hvert e F he
  exact ⟨r, s, hr, hs, hdF, heF, fun x hx y hy =>
    (P.face_isPathConnected hvert F).joinedIn x (hdF hx) y (heF hy)⟩


end PLDrawing

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)

/-- Helper toward Proposition 5.16: the actual geometric boundary traced
by one face-successor orbit, indexed by actual darts, including both
darts of a traversed bridge. -/
@[expose] def plOrbitBoundary (O : D39BallFaceCycleOrbit B) : Set ℂ :=
  ⋃ d ∈ O.val, (P.arc d).image

/-- Helper toward Proposition 5.16: an orbit boundary is precisely the
image of a closed polyline, with no simplicity assumption on that walk. -/
theorem exists_closed_polyline_plOrbitBoundary (O : D39BallFaceCycleOrbit B) :
    ∃ c : Polyline, c.start = c.finish ∧ c.image = B.plOrbitBoundary vert P O := by
  obtain ⟨d, hO⟩ := O.property
  obtain ⟨c, hc, himage⟩ := exists_closed_faceCyclePolyline B vert P d
  exact ⟨c, hc, by simpa only [plOrbitBoundary, hO] using himage⟩

/-- Helper toward Proposition 5.16: every orbit boundary is compact,
including repeated-vertex and repeated-edge boundary walks. -/
theorem isCompact_plOrbitBoundary (O : D39BallFaceCycleOrbit B) :
    IsCompact (B.plOrbitBoundary vert P O) := by
  obtain ⟨c, _, hc⟩ := B.exists_closed_polyline_plOrbitBoundary vert P O
  rw [← hc]
  exact c.isCompact_image

/-- Helper toward Proposition 5.16: every orbit boundary is connected
and nonempty, because its polyline traversal has connected nonempty range. -/
theorem isConnected_plOrbitBoundary (O : D39BallFaceCycleOrbit B) :
    IsConnected (B.plOrbitBoundary vert P O) := by
  obtain ⟨c, _, hc⟩ := B.exists_closed_polyline_plOrbitBoundary vert P O
  rw [← hc, ← Polyline.range_toPath]
  exact isConnected_range c.toPath.continuous



theorem plOrbitBoundary_subset_frontier (O : D39BallFaceCycleOrbit B) :
    B.plOrbitBoundary vert P O ⊆ frontier (B.plOrbitFace vert P hvert O).val := by
  intro z hz
  obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hz
  exact P.dartBorders_arc_subset_frontier hvert d _
    ((B.plOrbitFace_eq_iff vert P hvert O d hd _).mp rfl) hzd




theorem frontier_plFace_eq_iUnion_plOrbitBoundary (F : P.Face) :
    frontier F.val = ⋃ O : D39BallFaceCycleOrbit B,
      ⋃ (_ : B.plOrbitFace vert P hvert O = F), B.plOrbitBoundary vert P O := by
  rw [P.frontier_face_eq_iUnion_dartBorders_arcs hvert F]
  apply Subset.antisymm
  · intro z hz
    obtain ⟨d, hdF, hzd⟩ := mem_iUnion₂.mp hz
    let O : D39BallFaceCycleOrbit B :=
      ⟨{e | B.map.faceSucc.SameCycle d e}, d, rfl⟩
    have hd : d ∈ O.val := Equiv.Perm.SameCycle.rfl
    have hOF : B.plOrbitFace vert P hvert O = F :=
      (B.plOrbitFace_eq_iff vert P hvert O d hd F).mpr hdF
    exact mem_iUnion₂.mpr ⟨O, hOF, mem_iUnion₂.mpr ⟨d, hd, hzd⟩⟩
  · intro z hz
    obtain ⟨O, hOF, hzO⟩ := mem_iUnion₂.mp hz
    obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hzO
    exact mem_iUnion₂.mpr
      ⟨d, (B.plOrbitFace_eq_iff vert P hvert O d hd F).mp hOF, hzd⟩

end D39FiniteBall


































































end DirectedDistances.PlanarMap

end

