/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization13

/-! # Face succession in arbitrary whole-plane drawings

Local finiteness gives the full local star without a finite total dart carrier.
The results below do not assume a glued drawing or a geometric comparison. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set Metric Topology

section LocalStar
variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 3.9: local finiteness isolates the entire
initial star of a vertex even when the total dart carrier is infinite. -/
theorem uibotPLDrawing_local_initial_segments (hvert : Function.Surjective vert)
    (v : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball (P.pos v) r,
      (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0) := by
  classical
  let A : Set D := {d | (closedBall (P.pos v) 1 ∩ (P.arc d).image).Nonempty}
  have hA : A.Finite := P.locally_finite _ isBounded_closedBall
  let : Finite A := hA.to_subtype
  let J := (d : A) × Fin ((P.arc d.val).points.length - 1)
  let S : J → Set ℂ := fun j =>
    if P.pos v ∈ (P.arc j.1.val).segmentAt j.2.val then ∅
    else (P.arc j.1.val).segmentAt j.2.val
  have hclosed : IsClosed (⋃ j, S j) := by
    apply isClosed_iUnion_of_finite
    intro j
    dsimp [S]
    split_ifs
    · exact isClosed_empty
    · change IsClosed (segment ℝ _ _)
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hv : P.pos v ∉ ⋃ j, S j := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    dsimp [S] at hj
    split_ifs at hj with hmem
    · exact notMem_empty _ hj
    · exact hmem hj
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hv)
  refine ⟨min r 1, lt_min hr zero_lt_one, ?_⟩
  intro y hyr
  have hyr' : y ∈ ball (P.pos v) r :=
    Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hyr) (min_le_left _ _))
  have hy1 : y ∈ closedBall (P.pos v) 1 :=
    Metric.mem_closedBall.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp hyr) (min_le_right _ _)).le
  constructor
  · intro hy
    have harc : ∃ d, y ∈ (P.arc d).image := by
      rcases hy with ⟨w, rfl⟩ | ⟨d, hd⟩
      · obtain ⟨d, rfl⟩ := hvert w
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact ⟨d, hd⟩
    obtain ⟨d, hd⟩ := harc
    have hdA : d ∈ A := ⟨y, hy1, hd⟩
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        y ∈ (P.arc d).segmentAt i := by
      rcases hd with hd | ⟨i, hi, hd⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [mem_singleton_iff] at hd
        rw [hd, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hd⟩
    obtain ⟨i, hi, hyi⟩ := hseg
    have hvi : P.pos v ∈ (P.arc d).segmentAt i := by
      by_contra hnot
      apply hball hyr'
      apply mem_iUnion.mpr
      refine ⟨⟨⟨d, hdA⟩, ⟨i, by change i < (P.arc d).points.length - 1; omega⟩⟩, ?_⟩
      simpa only [S, ite_eq_right hnot] using hyi
    have hvimage := (P.arc d).segmentAt_subset_image hi hvi
    have hends : P.pos v = (P.arc d).start ∨ P.pos v = (P.arc d).finish := by
      by_contra h
      exact P.interior_avoids_vertices d v ⟨hvimage, by
        simpa only [mem_insert_iff, mem_singleton_iff] using h⟩
    rcases hends with hstart | hfinish
    · have hi0 := (P.arc d).segmentAt_index_eq_zero_of_start_mem
        (P.arc_simple d) (P.arc_length d) hi (hstart ▸ hvi)
      refine ⟨d, P.pos_injective (hstart.trans (P.arc_start d)).symm, ?_⟩
      simpa only [hi0] using hyi
    · have hilast := (P.arc d).segmentAt_index_last_of_finish_mem
        (P.arc_simple d) (P.arc_length d) hi (hfinish ▸ hvi)
      refine ⟨flip d, P.pos_injective (hfinish.trans (P.arc_finish d)).symm, ?_⟩
      rw [P.arc_flip, Polyline.segmentAt_reverse_transfer _ (by
        have := P.arc_length d; omega)]
      have hind : (P.arc d).points.length - 2 - 0 = i := by omega
      simpa only [hind] using hyi
  · rintro ⟨d, _, hy⟩
    exact Or.inr ⟨d, (P.arc d).segmentAt_subset_image (by
      have := P.arc_length d; omega) hy⟩

/-- Helper toward Proposition 3.9: a sufficiently small complete angular
sector lies in a unique original face of a locally finite drawing. -/
theorem uibotPLDrawing_local_sector_face
    (hvert : Function.Surjective vert) (d : D) :
    ∃ r : ℝ, 0 < r ∧ ∃! F : P.Face, P.initialSector d r ⊆ F.val := by
  obtain ⟨r, hr, hlocal⟩ := uibotPLDrawing_local_initial_segments P hvert (vert d)
  have hsafe : P.initialSector d r ⊆ P.imageᶜ := by
    intro z hz hzimage
    obtain ⟨e, he, hze⟩ := (hlocal z (P.initialSector_subset_ball d r hz)).mp hzimage
    exact (Set.disjoint_left.mp (P.initialSector_disjoint_initial_segment d e r he)) hz hze
  have hc := P.isConnected_initialSector d hr
  obtain ⟨z, hz⟩ := hc.nonempty
  obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr (hsafe hz)
  have hsub : P.initialSector d r ⊆ F.val := by
    obtain ⟨w, _, hF⟩ := F.property
    rw [hF] at hzF ⊢
    rw [connectedComponentIn_eq hzF]
    exact hc.isPreconnected.subset_connectedComponentIn hz hsafe
  exact ⟨r, hr, F, hsub, fun G hG => P.faces_eq_of_mem (hG hz) (hsub hz)⟩

/-- Helper toward Proposition 3.9: the geometric left face is unchanged
across a vertex sector, without a finite total dart carrier. -/
theorem uibotPLDrawing_border_flip_rot (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) :
    P.dartBorders (flip (rot d)) F := by
  obtain ⟨r, hr, G, hsector, _⟩ := uibotPLDrawing_local_sector_face P hvert d
  have hdG := P.dartBorders_of_initialSector_subset hvert d hr G hsector
  have hGF : G = F := P.dartBorders_face_unique d G F hdG hF
  exact hGF ▸ P.dartBorders_flip_rot_of_initialSector_subset hvert d hr G hsector

end LocalStar

/-- Helper toward Proposition 3.9: whole-plane face succession preserves
an original complementary face for every drawing of the prescribed rotation. -/
theorem uibotWholePlane_faceSucc_border_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (d : WholePlaneDart W) (F : G.Face) :
    G.dartBorders (wholePlaneFaceSucc W H d) F ↔ G.dartBorders d F := by
  have hv := uibhbot_faceOrbit_dartVertex_surjective W H
  have hrev : wholePlaneDartFlip W
      (wholePlaneRotation W H (wholePlaneFaceSucc W H d)) = d := by
    change wholePlaneDartFlip W
      (wholePlaneRotation W H ((wholePlaneRotation W H).symm
        (wholePlaneDartFlip W d))) = d
    rw [Equiv.apply_symm_apply]
    exact G.flip_involutive d
  constructor
  · intro hd
    exact hrev ▸ uibotPLDrawing_border_flip_rot G hv _ F hd
  · intro hd
    obtain ⟨K, hK⟩ := G.dartBorders_exists_of_wedge_compl (wholePlaneFaceSucc W H d)
      (G.wedgeIn_compl_image hv _ _ (G.initial_nonzero _))
    have hdK := hrev ▸ uibotPLDrawing_border_flip_rot G hv _ K hK
    exact G.dartBorders_face_unique d K F hdK hd ▸ hK

/-- Helper toward Proposition 3.9: all darts in one whole-plane face orbit
border exactly the same original faces, for arbitrary drawings. -/
theorem uibotWholePlane_sameCycle_border_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (d e : WholePlaneDart W)
    (hde : (wholePlaneFaceSucc W H).SameCycle d e) (F : G.Face) :
    G.dartBorders d F ↔ G.dartBorders e F := by
  let f := wholePlaneFaceSucc W H
  have hf (a : WholePlaneDart W) : G.dartBorders (f a) F ↔ G.dartBorders a F :=
    uibotWholePlane_faceSucc_border_iff W H G a F
  have hi (a : WholePlaneDart W) : G.dartBorders (f.symm a) F ↔ G.dartBorders a F := by
    simpa only [Equiv.apply_symm_apply] using (hf (f.symm a)).symm
  obtain ⟨k, rfl⟩ := hde
  have hpow (k : ℤ) : G.dartBorders ((f ^ k) d) F ↔ G.dartBorders d F := by
    induction k using Int.induction_on with
    | zero => exact Iff.rfl
    | succ k ih =>
      rw [add_comm (k : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply, hf, ih]
    | pred k ih =>
      rw [show -(k : ℤ) - 1 = -1 + -(k : ℤ) by omega,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact (hi _).trans ih
  exact (hpow k).symm

/-- Helper toward Proposition 3.9: a created triangle's three darts
border the same original face in every whole-plane drawing. -/
theorem uibotWholePlane_triangle_border_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N : ℕ)
    (q : TriangleCreationTime (shiftedStream W N))
    (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList (shiftedStream W N) q)
    (F : G.Face) :
    G.dartBorders (wholePlaneDartι W N a) F ↔
      G.dartBorders (wholePlaneDartι W N
        (stageTriangleDartTriple (shiftedStream W N) q).1) F := by
  apply (uibotWholePlane_sameCycle_border_iff W H G _ _ ?_ F).symm
  exact (wholePlane_stageTriangle_sameCycle_iff W H N q _).mpr ⟨a, ha, rfl⟩

end DirectedDistances.PaperProofs.Section3
end
