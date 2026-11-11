/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLRegularNeighborhood2
public import DirectedDistances.PlanarMap.D39BallOrbitComponents12

/-! # Vertex corner sectors at the separation radius

The sector is the existing `PLDrawing.initialSector`: its angular parameter
runs strictly counterclockwise from a dart to its rotation successor. Its
face is to the left of the departing dart and of the reversed successor. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Metric Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: at the supplied separation radius,
the entire open corner sector avoids the drawing, including singleton stars. -/
theorem initialSector_disjoint_image [Finite D]
    {hvert : Function.Surjective vert} (S : P.D39PLSeparationData hvert) (d : D) :
    Disjoint (P.initialSector d S.radius) P.image := by
  apply Set.disjoint_left.mpr
  intro z hz hzimage
  have hzball := P.initialSector_subset_ball d S.radius hz
  obtain ⟨e, he, hze⟩ := (S.vertex_local (vert d) z
    (ball_subset_closedBall hzball)).mp hzimage
  exact Set.disjoint_left.mp (P.initialSector_disjoint_initial_segment d e S.radius he)
    hz hze

/-- Helper toward Proposition 5.16: the supplied vertex-ball sector lies
in a unique face; that face borders both the dart and its reversed successor. -/
theorem exists_initialSector_subset_unique_face [Finite D]
    (hvert : Function.Surjective vert) (S : P.D39PLSeparationData hvert) (d : D) :
    ∃! F : P.Face, P.initialSector d S.radius ⊆ F.val ∧
      P.dartBorders d F ∧ P.dartBorders (flip (rot d)) F := by
  have hc := P.isConnected_initialSector d S.radius_pos
  have hsafe : P.initialSector d S.radius ⊆ P.imageᶜ := by
    intro z hz
    exact Set.disjoint_left.mp (P.initialSector_disjoint_image S d) hz
  obtain ⟨z, hz⟩ := hc.nonempty
  obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr (hsafe hz)
  have hsub : P.initialSector d S.radius ⊆ F.val := by
    obtain ⟨w, _, hF⟩ := F.property
    rw [hF] at hzF ⊢
    exact (hc.isPreconnected.subset_connectedComponentIn hz hsafe).trans
      (connectedComponentIn_eq hzF).symm.subset
  refine ⟨F, ⟨hsub, P.dartBorders_of_initialSector_subset hvert d S.radius_pos F hsub,
    P.dartBorders_flip_rot_of_initialSector_subset hvert d S.radius_pos F hsub⟩, ?_⟩
  intro G hG
  exact P.faces_eq_of_mem (hG.1 hz) (hsub hz)

/-- Helper toward Proposition 5.16: any face bordering the departing
dart contains the entire corner sector at the supplied separation radius. -/
theorem initialSector_subset_of_dartBorders [Finite D]
    (hvert : Function.Surjective vert) (S : P.D39PLSeparationData hvert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) :
    P.initialSector d S.radius ⊆ F.val := by
  obtain ⟨G, hG, _⟩ := P.exists_initialSector_subset_unique_face hvert S d
  exact (P.dartBorders_face_unique d G F hG.2.1 hborder) ▸ hG.1

/-- Helper toward Proposition 5.16: moving a positive fraction of the way
from the vertex to a sector point stays in the same sector. -/
theorem affine_mem_initialSector (d : D) (r : ℝ) {z : ℂ}
    (hz : z ∈ P.initialSector d r) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    P.pos (vert d) + t • (z - P.pos (vert d)) ∈ P.initialSector d r := by
  obtain ⟨⟨ρ, θ⟩, ⟨hρ, hθ⟩, rfl⟩ := hz
  refine ⟨(t * ρ, θ), ⟨⟨mul_pos ht hρ.1, ?_⟩, hθ⟩, ?_⟩
  · exact (mul_le_of_le_one_left hρ.1.le ht1).trans_lt hρ.2
  · simp only [Complex.ofReal_mul, add_sub_cancel_left, Complex.real_smul, mul_assoc]

/-- Helper toward Proposition 5.16: every point of the straight segment
from the vertex to a sector point, except the vertex, stays in the sector. -/
theorem segment_diff_vertex_subset_initialSector (d : D) (r : ℝ) {z : ℂ}
    (hz : z ∈ P.initialSector d r) :
    segment ℝ (P.pos (vert d)) z \ {P.pos (vert d)} ⊆ P.initialSector d r := by
  intro w hw
  rw [segment_eq_image'] at hw
  obtain ⟨t, ht, rfl⟩ := hw.1
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro ht0
    apply hw.2
    simp only [← ht0, zero_smul, add_zero, mem_singleton_iff])
  exact P.affine_mem_initialSector d r hz htpos ht.2

include P in
/-- Helper toward Proposition 5.16: a rotation-fixed dart is the only
outgoing dart at its vertex, by the singleton clause of rotation agreement. -/
theorem eq_of_vert_eq_of_rotation_fixed (d e : D) (hrot : rot d = d)
    (he : vert e = vert d) : e = d := by
  rcases P.rotation_agreement d with ⟨_, _, _, hs | hs⟩
  · exact Set.mem_singleton_iff.mp (hs.2 ▸ he)
  · exact (hs.1 hrot).elim

/-- Helper toward Proposition 5.16: at a degree-one vertex the full ball
is in the closure of the slit sector, including its excluded radial ray. -/
theorem ball_subset_closure_initialSector_of_rotation_fixed (d : D)
    (hrot : rot d = d) {r : ℝ} (hr : 0 < r) :
    ball (P.pos (vert d)) r ⊆ closure (P.initialSector d r) := by
  intro z hz
  let u := (P.arc d).initialDirection
  let f : ℝ × ℝ → ℂ := fun p => P.pos (vert d) + (p.1 : ℂ) *
    Complex.exp ((((u.arg + p.2 : ℝ) : ℂ)) * Complex.I)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hznorm : ‖z - P.pos (vert d)‖ < r := by
    simpa only [mem_ball, dist_eq_norm] using hz
  have hp : (‖z - P.pos (vert d)‖, ccwTurn u (z - P.pos (vert d))) ∈
      closure (Ioo 0 r ×ˢ Ioo 0
        (ccwTurn (P.arc d).initialDirection (P.arc (rot d)).initialDirection)) := by
    rw [hrot, (ccwTurn_eq_two_pi_iff _ _).mpr rfl, closure_prod_eq,
      closure_Ioo hr.ne, closure_Ioo Real.two_pi_pos.ne]
    exact ⟨⟨norm_nonneg _, hznorm.le⟩,
      (ccwTurn_pos _ _).le, ccwTurn_le_two_pi _ _⟩
  have hmem := hf.continuousAt.continuousWithinAt.mem_closure_image hp
  change f (‖z - P.pos (vert d)‖, ccwTurn u (z - P.pos (vert d))) ∈
    closure (P.initialSector d r) at hmem
  dsimp only [f] at hmem
  rw [d39_exp_arg_add_ccwTurn, Complex.norm_mul_exp_arg_mul_I,
    add_sub_cancel] at hmem
  exact hmem

/-- Helper toward Proposition 5.16: the punctured vertex ball minus the
single initial segment is connected when rotation fixes the dart. -/
theorem isConnected_ball_diff_initial_segment_of_rotation_fixed (d : D)
    (hrot : rot d = d) {r : ℝ} (hr : 0 < r) :
    IsConnected (ball (P.pos (vert d)) r \ (P.arc d).segmentAt 0) := by
  apply (P.isConnected_initialSector d hr).subset_closure
  · intro z hz
    exact ⟨P.initialSector_subset_ball d r hz,
      Set.disjoint_left.mp (P.initialSector_disjoint_initial_segment d d r rfl) hz⟩
  · exact fun _ hz => P.ball_subset_closure_initialSector_of_rotation_fixed d hrot hr hz.1

/-- Helper toward Proposition 5.16: in a supplied degree-one vertex ball,
removing the single initial segment leaves only points of one bordering face. -/
theorem ball_diff_initial_segment_subset_face_of_rotation_fixed [Finite D]
    (hvert : Function.Surjective vert) (S : P.D39PLSeparationData hvert)
    (d : D) (hrot : rot d = d) :
    ∃ F : P.Face, P.dartBorders d F ∧
      ball (P.pos (vert d)) S.radius \ (P.arc d).segmentAt 0 ⊆ F.val := by
  obtain ⟨F, hF, _⟩ := P.exists_initialSector_subset_unique_face hvert S d
  refine ⟨F, hF.2.1, ?_⟩
  have hsafe : ball (P.pos (vert d)) S.radius \ (P.arc d).segmentAt 0 ⊆ P.imageᶜ := by
    intro z hz hzimage
    obtain ⟨e, he, hze⟩ :=
      (S.vertex_local (vert d) z (ball_subset_closedBall hz.1)).mp hzimage
    rw [P.eq_of_vert_eq_of_rotation_fixed d e hrot he] at hze
    exact hz.2 hze
  obtain ⟨z, hz⟩ := (P.isConnected_initialSector d S.radius_pos).nonempty
  have hzslit : z ∈ ball (P.pos (vert d)) S.radius \ (P.arc d).segmentAt 0 :=
    ⟨P.initialSector_subset_ball d S.radius hz,
      Set.disjoint_left.mp (P.initialSector_disjoint_initial_segment d d S.radius rfl) hz⟩
  have hzF := hF.1 hz
  obtain ⟨w, _, hface⟩ := F.property
  rw [hface] at hzF ⊢
  rw [connectedComponentIn_eq hzF]
  exact (P.isConnected_ball_diff_initial_segment_of_rotation_fixed d hrot S.radius_pos).isPreconnected.subset_connectedComponentIn hzslit hsafe

end PLDrawing

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)

/-- Helper toward Proposition 5.16: the corner sector at the supplied
radius is contained in the chosen left face of its departing dart. -/
theorem initialSector_subset_plDartFace (S : P.D39PLSeparationData hvert) (d : B.D) :
    P.initialSector d S.radius ⊆ (B.plDartFace vert P hvert d).val := by
  obtain ⟨F, hF, _⟩ := P.exists_initialSector_subset_unique_face hvert S d
  rw [(B.plDartFace_eq_iff vert P hvert d F).mpr hF.2.1]
  exact hF.1



theorem initialSector_subset_plOrbitFace (S : P.D39PLSeparationData hvert)
    (O : D39BallFaceCycleOrbit B) (d : B.D) (hd : d ∈ O.val) :
    P.initialSector d S.radius ⊆ (B.plOrbitFace vert P hvert O).val := by
  rw [B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d hd]
  exact B.initialSector_subset_plDartFace vert P hvert S d

/-- Helper toward Proposition 5.16: the punctured straight segment to
each sector point lies in the dart's geometric face. -/
theorem segment_diff_vertex_subset_plDartFace (S : P.D39PLSeparationData hvert)
    (d : B.D) {z : ℂ} (hz : z ∈ P.initialSector d S.radius) :
    segment ℝ (P.pos (vert d)) z \ {P.pos (vert d)} ⊆
      (B.plDartFace vert P hvert d).val :=
  (P.segment_diff_vertex_subset_initialSector d S.radius hz).trans
    (B.initialSector_subset_plDartFace vert P hvert S d)

/-- Helper toward Proposition 5.16: at degree one the entire punctured
ball minus its single initial segment lies in the face of its unique dart. -/
theorem ball_diff_initial_segment_subset_plDartFace_of_rotation_fixed
    (S : P.D39PLSeparationData hvert) (d : B.D) (hrot : B.map.rot d = d) :
    ball (P.pos (vert d)) S.radius \ (P.arc d).segmentAt 0 ⊆
      (B.plDartFace vert P hvert d).val := by
  obtain ⟨F, hborder, hsub⟩ :=
    P.ball_diff_initial_segment_subset_face_of_rotation_fixed hvert S d hrot
  rw [(B.plDartFace_eq_iff vert P hvert d F).mpr hborder]
  exact hsub

end D39FiniteBall
end DirectedDistances.PlanarMap
