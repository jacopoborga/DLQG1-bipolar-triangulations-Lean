/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents4
public import DirectedDistances.PlanarMap.CombinatorialMapEulerBound

/-! # Tree face orbits and complementary components

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
separate kernel validation remain the coordinator's responsibility. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

namespace CombinatorialMap

/-- Helper toward Proposition 5.16: equivalence-closure connectivity by
rotation and reversal implies the combinatorial map's path connectivity. -/
theorem isConnected_of_eqvGen {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D)
    (hconn : ∀ d e : D, Relation.EqvGen
      (fun x y => M.rot x = y ∨ M.edgeInv x = y) d e) : M.IsConnected := by
  let R : D → D → Prop := fun x y =>
    y = M.rot x ∨ y = M.rot.symm x ∨ y = M.edgeInv x ∨ y = M.edgeInv.symm x
  let : Std.Symm R := ⟨by
    intro x y h
    rcases h with h | h | h | h
    · subst y
      exact Or.inr (Or.inl (M.rot.symm_apply_apply x).symm)
    · subst y
      exact Or.inl (M.rot.apply_symm_apply x).symm
    · subst y
      exact Or.inr (Or.inr (Or.inr (M.edgeInv.symm_apply_apply x).symm))
    · subst y
      exact Or.inr (Or.inr (Or.inl (M.edgeInv.apply_symm_apply x).symm))⟩
  intro d e
  have h : Relation.EqvGen R d e := Relation.EqvGen.mono
    (fun _ _ h => h.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr (Or.inr (Or.inl h.symm)))) d e (hconn d e)
  rwa [Relation.EqvGen.eqvGen_eq_reflTransGen] at h

/-- Helper toward Proposition 5.16: a nonempty connected combinatorial
map with `E = V - 1` has exactly one face-successor orbit. This uses only
the combinatorial Euler bound and positive vertex and face counts. -/
theorem numFaces_eq_one_of_tree {D : Type*} [Fintype D] [DecidableEq D]
    [Nonempty D] (M : CombinatorialMap D) (hconn : M.IsConnected)
    (htree : M.numEdges = M.numVertices - 1) : M.numFaces = 1 := by
  classical
  obtain ⟨d⟩ := ‹Nonempty D›
  have hVpos : 0 < M.numVertices :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ d⟩
  have hFpos : 0 < M.numFaces :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ d⟩
  have hEuler := eulerChar_le_two_of_isConnected M hconn
  unfold eulerChar at hEuler
  omega

/-- Helper toward Proposition 5.16: any two darts of a nonempty connected
combinatorial tree belong to the same face-successor orbit. -/
theorem faceSucc_sameCycle_of_tree {D : Type*} [Fintype D] [DecidableEq D]
    [Nonempty D] (M : CombinatorialMap D) (hconn : M.IsConnected)
    (htree : M.numEdges = M.numVertices - 1) (d e : D) :
    M.faceSucc.SameCycle d e := by
  classical
  have hF : Fintype.card (FaceQuotient M) = 1 := M.numFaces_eq_one_of_tree hconn htree
  let : Subsingleton (FaceQuotient M) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact Quotient.exact (Subsingleton.elim
    (Quotient.mk (Equiv.Perm.SameCycle.setoid M.faceSucc) d)
    (Quotient.mk (Equiv.Perm.SameCycle.setoid M.faceSucc) e))

end CombinatorialMap

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the tree edge count forces exactly
one face-successor orbit for a finite ball under the original `hconn`. -/
theorem numFaces_eq_one_of_tree (B : D39FiniteBall)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) : B.map.numFaces = 1 := by
  let : Nonempty B.D := ⟨B.rootDart⟩
  exact B.map.numFaces_eq_one_of_tree (B.map.isConnected_of_eqvGen hconn) htree

/-- Helper toward Proposition 5.16: exactly one actual face-orbit set
exists in a finite ball tree, not merely one quotient equivalence class. -/
theorem existsUnique_faceCycleOrbit_of_tree (B : D39FiniteBall)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) :
    ∃! _O : D39BallFaceCycleOrbit B, True := by
  let : Nonempty B.D := ⟨B.rootDart⟩
  have hcycle := B.map.faceSucc_sameCycle_of_tree (B.map.isConnected_of_eqvGen hconn) htree
  let O : D39BallFaceCycleOrbit B :=
    ⟨{e | B.map.faceSucc.SameCycle B.rootDart e}, B.rootDart, rfl⟩
  refine ⟨O, trivial, ?_⟩
  intro Q _
  obtain ⟨d, hQ⟩ := Q.property
  apply Subtype.ext
  rw [hQ]
  ext e
  exact iff_of_true (hcycle d e) (hcycle B.rootDart e)

/-- Helper toward Proposition 5.16: the tree case of common-face orbit
uniqueness U1. In fact, the tree count puts all darts in a single orbit. -/
theorem plDartFace_sameCycle_of_eq_of_tree {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) (d e : B.D)
    (_hface : B.plDartFace vert P hvert d = B.plDartFace vert P hvert e) :
    B.map.faceSucc.SameCycle d e := by
  let : Nonempty B.D := ⟨B.rootDart⟩
  exact B.map.faceSucc_sameCycle_of_tree (B.map.isConnected_of_eqvGen hconn) htree d e

end D39FiniteBall

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: a combinatorial tree drawing has a
single geometric complementary face, by the proved dart-face surjection. -/
theorem subsingleton_plFace_of_tree {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) : Subsingleton P.Face := by
  let : Nonempty B.D := ⟨B.rootDart⟩
  constructor
  intro F G
  obtain ⟨d, rfl⟩ := B.plDartFace_surjective vert P hvert F
  obtain ⟨e, rfl⟩ := B.plDartFace_surjective vert P hvert G
  exact B.plDartFace_eq_of_sameCycle vert P hvert d e
    (B.map.faceSucc_sameCycle_of_tree (B.map.isConnected_of_eqvGen hconn) htree d e)

/-- Helper toward Proposition 5.16: in a tree drawing, the unique face
is the entire complement of the drawing image. -/
theorem plDartFace_eq_compl_image_of_tree {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) (d : B.D) :
    (B.plDartFace vert P hvert d).val = P.imageᶜ := by
  let : Subsingleton P.Face := B.subsingleton_plFace_of_tree vert P hvert hconn htree
  apply Subset.antisymm (P.face_subset_compl _)
  intro z hz
  obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr hz
  exact (Subsingleton.elim F (B.plDartFace vert P hvert d)) ▸ hzF

/-- Helper toward Proposition 5.16: the complement of a connected finite
ball tree drawing is connected, including its nonemptiness. -/
theorem isConnected_compl_plImage_of_tree {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) :
    IsConnected P.imageᶜ := by
  rw [← B.plDartFace_eq_compl_image_of_tree vert P hvert hconn htree B.rootDart]
  exact (P.face_isPathConnected hvert _).isConnected

/-- Helper toward Proposition 5.16: a connected finite ball tree drawing
has exactly one face, counted as actual complementary component sets. -/
theorem natCard_plFace_eq_one_of_tree {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (htree : B.map.numEdges = B.map.numVertices - 1) : Nat.card P.Face = 1 := by
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨B.subsingleton_plFace_of_tree vert P hvert hconn htree,
      ⟨B.plDartFace vert P hvert B.rootDart⟩⟩

end D39FiniteBall

namespace PLDrawing

/-- Helper toward Proposition 5.16: for any finite nonempty combinatorial
tree with a faithful PL drawing and surjective dart incidence, the plane
complement is connected and the drawing has exactly one geometric face. -/
theorem isConnected_compl_image_and_natCard_face_of_tree
    {D : Type} {V : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
    (M : CombinatorialMap D) (vert : D → V)
    (P : PLDrawing D V M.edgeInv M.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : D, Relation.EqvGen
      (fun x y => M.rot x = y ∨ M.edgeInv x = y) d e)
    (htree : M.numEdges = M.numVertices - 1) :
    IsConnected P.imageᶜ ∧ Nat.card P.Face = 1 := by
  let B : D39FiniteBall :=
    { D := D, map := M, missing := fun _ => False, tail := fun _ => False,
      rootDart := Classical.choice ‹Nonempty D›, original := Set.univ,
      original_closed := fun _ => Iff.rfl }
  exact ⟨B.isConnected_compl_plImage_of_tree vert P hvert hconn htree,
    B.natCard_plFace_eq_one_of_tree vert P hvert hconn htree⟩

end PLDrawing

/-- Helper toward Proposition 5.16: a point of the ambient set in the
closure of one of its components still belongs to that component. -/
theorem mem_connectedComponentIn_of_mem_closure {S : Set ℂ} {z q : ℂ}
    (hz : z ∈ S) (hq : q ∈ S)
    (hqcl : q ∈ closure (connectedComponentIn S z)) :
    q ∈ connectedComponentIn S z := by
  have hpre : IsPreconnected (insert q (connectedComponentIn S z)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hqcl subset_closure)
  exact hpre.subset_connectedComponentIn
    (mem_insert_of_mem _ (mem_connectedComponentIn hz))
    (insert_subset hq (connectedComponentIn_subset _ _)) (mem_insert _ _)

/-- Helper toward Proposition 5.16: removing a relatively present closed
set from a connected open planar region makes every remaining component
approach the removed set at a point inside the original region. -/
theorem exists_mem_closed_mem_closure_component_diff
    (U C : Set ℂ) (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hCclosed : IsClosed C) (hUC : (U ∩ C).Nonempty)
    (z : ℂ) (hz : z ∈ U \ C) :
    ∃ q ∈ U ∩ C, q ∈ closure (connectedComponentIn (U \ C) z) := by
  by_contra hnone
  have hKopen : IsOpen (connectedComponentIn (U \ C) z) :=
    (hUopen.inter hCclosed.isOpen_compl).connectedComponentIn
  have hUK : U ⊆ connectedComponentIn (U \ C) z := by
    apply hUconn.isPreconnected.subset_of_closure_inter_subset hKopen
      ⟨z, hz.1, mem_connectedComponentIn hz⟩
    rintro q ⟨hqcl, hqU⟩
    have hqC : q ∉ C := fun hqC => hnone ⟨q, ⟨hqU, hqC⟩, hqcl⟩
    exact mem_connectedComponentIn_of_mem_closure hz ⟨hqU, hqC⟩ hqcl
  obtain ⟨q, hqU, hqC⟩ := hUC
  exact (connectedComponentIn_subset (U \ C) z (hUK hqU)).2 hqC

namespace Polyline

/-- Helper toward Proposition 5.16: every simple polyline with at least
one segment has a nonempty arc interior. Two points of the first segment
suffice to avoid both endpoints without any endpoint-identification lemma. -/
theorem interior_nonempty_of_isSimple (c : Polyline) (hc : c.IsSimple)
    (hlen : 2 ≤ c.points.length) : c.interior.Nonempty := by
  let a := midpoint ℝ c.start (c.point 1)
  let b := midpoint ℝ c.start a
  have hne : c.start ≠ c.point 1 := by
    simpa only [point_zero_eq_start] using hc.1 0 (by omega)
  have ha : a ≠ c.start := fun he => hne ((midpoint_eq_left_iff ℝ).mp he)
  have hb : b ≠ c.start := fun he => ha ((midpoint_eq_left_iff ℝ).mp he).symm
  have hba : b ≠ a := fun he => ha ((midpoint_eq_right_iff ℝ).mp he).symm
  have ham : a ∈ segment ℝ c.start (c.point 1) := midpoint_mem_segment _ _
  have hbm : b ∈ segment ℝ c.start (c.point 1) :=
    (convex_segment c.start (c.point 1)).segment_subset
      (left_mem_segment ℝ c.start (c.point 1)) ham (midpoint_mem_segment c.start a)
  have himage {w : ℂ} (hw : w ∈ segment ℝ c.start (c.point 1)) : w ∈ c.image := by
    refine Or.inr ⟨0, by omega, ?_⟩
    simpa only [segmentAt, point_zero_eq_start] using hw
  by_cases haf : a = c.finish
  · refine ⟨b, himage hbm, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hb, fun he => hba (he.trans haf.symm)⟩
  · refine ⟨a, himage ham, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨ha, haf⟩

/-- Helper toward Proposition 5.16: around a regular point of an inserted
simple arc, both sufficiently small side half-discs lie in the original
open region with the arc removed. -/
theorem exists_halfDiscs_subset_diff (c : Polyline) (hc : c.IsSimple)
    (U : Set ℂ) (hU : IsOpen U) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxa : x ≠ c.point i)
    (hxb : x ≠ c.point (i + 1)) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∧
      leftHalfDisc x (c.point (i + 1) - c.point i) r ⊆ U \ c.image ∧
      rightHalfDisc x (c.point (i + 1) - c.point i) r ⊆ U \ c.image := by
  obtain ⟨s, hs, havoid⟩ := c.exists_pos_ball_avoiding_nonincident_segments
    hc i hi x hx hxa hxb
  obtain ⟨t, ht, hUball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  let r := min s t
  have hr : 0 < r := lt_min hs ht
  have hball : Metric.ball x r ⊆ U :=
    (Metric.ball_subset_ball (min_le_right s t)).trans hUball
  have hnot (y : ℂ) (hy : y ∈ Metric.ball x r)
      (hytrans : (star (c.point (i + 1) - c.point i) * (y - x)).im ≠ 0) :
      y ∉ c.image := by
    have hseg : ∀ j, j + 1 < c.points.length → y ∉ c.segmentAt j := by
      intro j hj hyj
      by_cases hji : j = i
      · subst j
        exact hytrans (segment_subset_edgeLine (c.point i) (c.point (i + 1)) x hx hyj)
      · exact havoid y (Metric.ball_subset_ball (min_le_left s t) hy) j hj hji hyj
    rintro (hystart | ⟨j, hj, hyj⟩)
    · apply hseg 0 (by omega)
      rw [mem_singleton_iff] at hystart
      rw [hystart, segmentAt, point_zero_eq_start]
      exact left_mem_segment ℝ _ _
    · exact hseg j hj hyj
  exact ⟨r, hr, hball,
    fun y hy => ⟨hball hy.1, hnot y hy.1 (ne_of_gt hy.2)⟩,
    fun y hy => ⟨hball hy.1, hnot y hy.1 (ne_of_lt hy.2)⟩⟩

/-- Helper toward Proposition 5.16: near a regular point of an inserted
arc, at most two components of the relative complement occur. Their
representatives lie in the actual left and right side germs, respectively,
and each whole half-disc lies in its representative's component. -/
theorem exists_two_components_near_segment_diff (c : Polyline) (hc : c.IsSimple)
    (U : Set ℂ) (hU : IsOpen U) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxa : x ≠ c.point i)
    (hxb : x ≠ c.point (i + 1)) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ u v : ℂ,
      u ∈ leftHalfDisc x (c.point (i + 1) - c.point i) r ∧
      v ∈ rightHalfDisc x (c.point (i + 1) - c.point i) r ∧
      u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      leftHalfDisc x (c.point (i + 1) - c.point i) r ⊆
        connectedComponentIn (U \ c.image) u ∧
      rightHalfDisc x (c.point (i + 1) - c.point i) r ⊆
        connectedComponentIn (U \ c.image) v ∧
      ∀ z ∈ Metric.ball x r, z ∈ U \ c.image →
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) u ∨
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) v := by
  obtain ⟨r, hr, _, hL, hR⟩ := c.exists_halfDiscs_subset_diff hc U hU i hi x hx hxa hxb hxU
  let d := c.point (i + 1) - c.point i
  have hd : d ≠ 0 := sub_ne_zero.mpr (hc.1 i hi).symm
  obtain ⟨u, hu⟩ := leftHalfDisc_nonempty x d r hd hr
  obtain ⟨v, hv⟩ := rightHalfDisc_nonempty x d r hd hr
  have hLC := (isConnected_leftHalfDisc x d r ⟨u, hu⟩).isPreconnected
    |>.subset_connectedComponentIn hu hL
  have hRC := (isConnected_rightHalfDisc x d r ⟨v, hv⟩).isPreconnected
    |>.subset_connectedComponentIn hv hR
  refine ⟨r, hr, u, v, hu, hv, hL hu, hR hv, hLC, hRC, ?_⟩
  intro z hz hzU
  let O := connectedComponentIn (U \ c.image) z ∩ Metric.ball x r
  have hO : IsOpen O :=
    (hU.inter c.isCompact_image.isClosed.isOpen_compl).connectedComponentIn.inter
      Metric.isOpen_ball
  obtain ⟨y, hy, hyline⟩ := (dense_compl_edgeLine x d hd).inter_open_nonempty
    O hO ⟨z, mem_connectedComponentIn hzU, hz⟩
  have hzy := connectedComponentIn_eq hy.1
  have htrans : (star d * (y - x)).im ≠ 0 := hyline
  rcases htrans.lt_or_gt with hn | hp
  · exact Or.inr (hzy.trans (connectedComponentIn_eq (hRC ⟨hy.2, hn⟩)).symm)
  · exact Or.inl (hzy.trans (connectedComponentIn_eq (hLC ⟨hy.2, hp⟩)).symm)

/-- Helper toward Proposition 5.16: every component accumulating at a
specified regular arc point contains a whole left or right side germ there.
Only two components can accumulate at that specified point. -/
theorem exists_side_germs_of_mem_closure_component_diff
    (c : Polyline) (hc : c.IsSimple) (U : Set ℂ) (hU : IsOpen U)
    (i : ℕ) (hi : i + 1 < c.points.length) (x : ℂ)
    (hx : x ∈ c.segmentAt i) (hxa : x ≠ c.point i)
    (hxb : x ≠ c.point (i + 1)) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ u v : ℂ, u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      ∀ z : ℂ, x ∈ closure (connectedComponentIn (U \ c.image) z) →
        (connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) u ∧
          leftHalfDisc x (c.point (i + 1) - c.point i) r ⊆
            connectedComponentIn (U \ c.image) z) ∨
        (connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) v ∧
          rightHalfDisc x (c.point (i + 1) - c.point i) r ⊆
            connectedComponentIn (U \ c.image) z) := by
  obtain ⟨r, hr, u, v, _, _, hu, hv, hL, hR, hcover⟩ :=
    c.exists_two_components_near_segment_diff hc U hU i hi x hx hxa hxb hxU
  refine ⟨r, hr, u, v, hu, hv, ?_⟩
  intro z hz
  obtain ⟨w, hwball, hwcomp⟩ := mem_closure_iff.mp hz (Metric.ball x r)
    Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hzw := connectedComponentIn_eq hwcomp
  rcases hcover w hwball (connectedComponentIn_subset _ _ hwcomp) with hwu | hwv
  · have heq := hzw.trans hwu
    exact Or.inl ⟨heq, heq ▸ hL⟩
  · have heq := hzw.trans hwv
    exact Or.inr ⟨heq, heq ▸ hR⟩

/-- Helper toward Proposition 5.16: every component left after inserting
an arc inside a connected open region approaches the interior of that arc.
The endpoints lie outside the region, so they cannot be the contact point. -/
theorem exists_interior_mem_closure_component_diff
    (c : Polyline) (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hinterior : c.interior ⊆ U) (hne : c.interior.Nonempty)
    (hstart : c.start ∉ U) (hfinish : c.finish ∉ U)
    (z : ℂ) (hz : z ∈ U \ c.image) :
    ∃ q ∈ c.interior, q ∈ U ∧ q ∈ closure (connectedComponentIn (U \ c.image) z) := by
  obtain ⟨q, hq⟩ := hne
  have hUC : (U ∩ c.image).Nonempty := ⟨q, hinterior hq, hq.1⟩
  obtain ⟨w, ⟨hwU, hwc⟩, hwcl⟩ := exists_mem_closed_mem_closure_component_diff
    U c.image hUopen hUconn c.isCompact_image.isClosed hUC z hz
  refine ⟨w, ⟨hwc, ?_⟩, hwU, hwcl⟩
  intro hwend
  rcases hwend with hwend | hwend
  · exact hstart (hwend ▸ hwU)
  · exact hfinish (hwend ▸ hwU)

/-- Helper toward Proposition 5.16: along one complete open segment of
an inserted arc, all accumulating components are represented by at most
two fixed components. Variable-radius connected strips make this uniform
along the segment; no continuity of the radii is assumed. -/
theorem exists_two_components_along_openSegment_diff
    (c : Polyline) (hc : c.IsSimple) (U : Set ℂ) (hU : IsOpen U)
    (i : ℕ) (hi : i + 1 < c.points.length)
    (hedge : openSegment ℝ (c.point i) (c.point (i + 1)) ⊆ U) :
    ∃ u v : ℂ, u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      ∀ z : ℂ,
        (∃ x ∈ openSegment ℝ (c.point i) (c.point (i + 1)),
          x ∈ closure (connectedComponentIn (U \ c.image) z)) →
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) u ∨
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) v := by
  classical
  let a := c.point i
  let b := c.point (i + 1)
  let d := b - a
  have hab : a ≠ b := hc.1 i hi
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  have hex (x : ↥(openSegment ℝ a b)) : ∃ r : ℝ, 0 < r ∧
      Metric.ball (x : ℂ) r ⊆ U ∧ leftHalfDisc x d r ⊆ U \ c.image ∧
        rightHalfDisc x d r ⊆ U \ c.image := by
    have hxa : (x : ℂ) ≠ a := fun he => hab (left_mem_openSegment_iff.mp (he ▸ x.property))
    have hxb : (x : ℂ) ≠ b := fun he => hab (right_mem_openSegment_iff.mp (he ▸ x.property))
    exact c.exists_halfDiscs_subset_diff hc U hU i hi x
      (openSegment_subset_segment ℝ a b x.property) hxa hxb (hedge x.property)
  choose r hr _ hL hR using hex
  let L := ⋃ x : ↥(openSegment ℝ a b), leftHalfDisc x d (r x)
  let R := ⋃ x : ↥(openSegment ℝ a b), rightHalfDisc x d (r x)
  have hline (x y : ↥(openSegment ℝ a b)) : (y : ℂ) ∈ edgeLine x d :=
    segment_subset_edgeLine a b x (openSegment_subset_segment ℝ a b x.property)
      (openSegment_subset_segment ℝ a b y.property)
  have hLc : IsConnected L :=
    isConnected_iUnion_leftHalfDisc_openSegment a b d hd hline r hr
  have hRc : IsConnected R := by
    dsimp only [R]
    simp_rw [rightHalfDisc_eq_leftHalfDisc_neg]
    apply isConnected_iUnion_leftHalfDisc_openSegment a b (-d) (neg_ne_zero.mpr hd) ?_ r hr
    intro x y
    have hxy := hline x y
    change (star d * ((y : ℂ) - x)).im = 0 at hxy
    change (star (-d) * ((y : ℂ) - x)).im = 0
    simpa only [star_neg, neg_mul, Complex.neg_im, neg_eq_zero] using hxy
  have hLsub : L ⊆ U \ c.image := iUnion_subset fun x => hL x
  have hRsub : R ⊆ U \ c.image := iUnion_subset fun x => hR x
  obtain ⟨u, hu⟩ := hLc.nonempty
  obtain ⟨v, hv⟩ := hRc.nonempty
  have hLC := hLc.isPreconnected.subset_connectedComponentIn hu hLsub
  have hRC := hRc.isPreconnected.subset_connectedComponentIn hv hRsub
  refine ⟨u, v, hLsub hu, hRsub hv, ?_⟩
  rintro z ⟨x, hx, hxcl⟩
  let x' : ↥(openSegment ℝ a b) := ⟨x, hx⟩
  let O := connectedComponentIn (U \ c.image) z ∩ Metric.ball x (r x')
  have hO : IsOpen O :=
    (hU.inter c.isCompact_image.isClosed.isOpen_compl).connectedComponentIn.inter
      Metric.isOpen_ball
  have hOne : O.Nonempty := by
    obtain ⟨w, hwb, hwK⟩ := mem_closure_iff.mp hxcl (Metric.ball x (r x'))
      Metric.isOpen_ball (Metric.mem_ball_self (hr x'))
    exact ⟨w, hwK, hwb⟩
  obtain ⟨w, hw, hwline⟩ := (dense_compl_edgeLine x d hd).inter_open_nonempty O hO hOne
  have hzw := connectedComponentIn_eq hw.1
  have htrans : (star d * (w - x)).im ≠ 0 := hwline
  rcases htrans.lt_or_gt with hn | hp
  · have hwR : w ∈ R := mem_iUnion.mpr ⟨x', hw.2, hn⟩
    exact Or.inr (hzw.trans (connectedComponentIn_eq (hRC hwR)).symm)
  · have hwL : w ∈ L := mem_iUnion.mpr ⟨x', hw.2, hp⟩
    exact Or.inl (hzw.trans (connectedComponentIn_eq (hLC hwL)).symm)

/-- Helper toward Proposition 5.16: a component of a region cut by an
inserted simple arc accumulates at a regular segment point, even when the
first contact supplied by connectedness is a bend of the arc. -/
theorem exists_openSegment_mem_closure_component_diff
    (c : Polyline) (hc : c.IsSimple)
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hinterior : c.interior ⊆ U) (hne : c.interior.Nonempty)
    (hstart : c.start ∉ U) (hfinish : c.finish ∉ U)
    (z : ℂ) (hz : z ∈ U \ c.image) :
    ∃ i : ℕ, i + 1 < c.points.length ∧ ∃ x : ℂ,
      x ∈ openSegment ℝ (c.point i) (c.point (i + 1)) ∧ x ∈ U ∧
      x ∈ closure (connectedComponentIn (U \ c.image) z) := by
  classical
  obtain ⟨q, hqint, hqU, hqcl⟩ := c.exists_interior_mem_closure_component_diff
    U hUopen hUconn hinterior hne hstart hfinish z hz
  have hqstart : q ≠ c.start := fun he => hqint.2 (Or.inl he)
  obtain ⟨i, hi, hqi⟩ : ∃ i, i + 1 < c.points.length ∧ q ∈ c.segmentAt i := by
    rcases hqint.1 with h | h
    · exact (hqstart h).elim
    · exact h
  by_cases hqend : q = c.point i ∨ q = c.point (i + 1)
  · let E : Set ℂ := (Set.range (fun j : Fin c.points.length => c.point j.val)) \ {q}
    have hEclosed : IsClosed E := ((finite_range _).sdiff).isClosed
    have hqE : q ∉ E := fun h => h.2 rfl
    obtain ⟨r₀, hr₀, hEball⟩ := Metric.mem_nhds_iff.mp (hEclosed.isOpen_compl.mem_nhds hqE)
    obtain ⟨s, hs, hUball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hqU)
    let r := min r₀ s
    have hr : 0 < r := lt_min hr₀ hs
    have hballU : Metric.ball q r ⊆ U :=
      (Metric.ball_subset_ball (min_le_right r₀ s)).trans hUball
    have hisolate (j : ℕ) (hj : j < c.points.length)
        (hjball : c.point j ∈ Metric.ball q r) : c.point j = q := by
      by_contra hjne
      exact hEball (Metric.ball_subset_ball (min_le_left r₀ s) hjball)
        ⟨⟨⟨j, hj⟩, rfl⟩, hjne⟩
    let K := connectedComponentIn (U \ c.image) z
    have hKopen : IsOpen K :=
      (hUopen.inter c.isCompact_image.isClosed.isOpen_compl).connectedComponentIn
    have hqnotK : q ∉ K := fun h => (connectedComponentIn_subset _ _ h).2 hqint.1
    obtain ⟨w, hwK, hwq⟩ := Metric.mem_closure_iff.mp hqcl r hr
    have hwball : w ∈ Metric.ball q r := by simpa only [Metric.mem_ball, dist_comm] using hwq
    have hwU : w ∈ Metric.ball q r \ {q} := ⟨hwball, fun he => hqnotK (he ▸ hwK)⟩
    obtain ⟨y, hyseg, hyball, hyne⟩ := PLDrawing.segment_endpoint_nearby
      (c.point i) (c.point (i + 1)) q (hc.1 i hi) hqend r hr
    have hyimage : y ∈ c.image := c.segmentAt_subset_image hi hyseg
    have hfront : ∃ x ∈ Metric.ball q r \ {q}, x ∈ frontier K := by
      by_contra hnone
      have hsubset : Metric.ball q r \ {q} ⊆ K := by
        apply (PLDrawing.punctured_ball_isPreconnected q r hr).subset_of_closure_inter_subset
          hKopen ⟨w, hwU, hwK⟩
        intro x hx
        by_contra hxK
        apply hnone
        refine ⟨x, hx.2, ?_⟩
        rw [frontier, hKopen.interior_eq]
        exact ⟨hx.1, hxK⟩
      exact (connectedComponentIn_subset _ _ (hsubset ⟨hyball, hyne⟩)).2 hyimage
    obtain ⟨x, hxball, hxfront⟩ := hfront
    have hxU := hballU hxball.1
    have hxcl : x ∈ closure K := frontier_subset_closure hxfront
    have hxnotK : x ∉ K := by
      have h := hxfront.2
      rwa [hKopen.interior_eq] at h
    have hximage : x ∈ c.image := by
      by_contra hximage
      exact hxnotK (mem_connectedComponentIn_of_mem_closure hz ⟨hxU, hximage⟩ hxcl)
    have hxnotvertex : ∀ j, j < c.points.length → x ≠ c.point j := by
      intro j hj he
      exact hxball.2 (he.trans (hisolate j hj (he ▸ hxball.1)))
    rcases hximage with hxroot | ⟨j, hj, hxj⟩
    · exact (hxnotvertex 0 (by have := c.nonempty; exact List.length_pos_iff.mpr this)
        (hxroot.trans c.point_zero_eq_start.symm)).elim
    · exact ⟨j, hj, x,
        mem_openSegment_of_ne_left_right (hxnotvertex j (by omega)).symm
          (hxnotvertex (j + 1) hj).symm hxj, hxU, hxcl⟩
  · exact ⟨i, hi, q,
      mem_openSegment_of_ne_left_right (fun he => hqend (Or.inl he.symm))
        (fun he => hqend (Or.inr he.symm)) hqi, hqU, hqcl⟩

/-- Helper toward Proposition 5.16: every component after inserting a
simple arc contains a full left or right germ at some regular arc point.
The positive radius and nondegenerate segment ensure a nonempty germ. -/
theorem exists_side_germ_subset_component_diff
    (c : Polyline) (hc : c.IsSimple) (hlen : 2 ≤ c.points.length)
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hinterior : c.interior ⊆ U)
    (hstart : c.start ∉ U) (hfinish : c.finish ∉ U)
    (z : ℂ) (hz : z ∈ U \ c.image) :
    ∃ i : ℕ, i + 1 < c.points.length ∧ ∃ x : ℂ,
      x ∈ openSegment ℝ (c.point i) (c.point (i + 1)) ∧ x ∈ U ∧
      ∃ r : ℝ, 0 < r ∧
        (leftHalfDisc x (c.point (i + 1) - c.point i) r ⊆
          connectedComponentIn (U \ c.image) z ∨
        rightHalfDisc x (c.point (i + 1) - c.point i) r ⊆
          connectedComponentIn (U \ c.image) z) := by
  obtain ⟨i, hi, x, hx, hxU, hxcl⟩ := c.exists_openSegment_mem_closure_component_diff
    hc U hUopen hUconn hinterior (c.interior_nonempty_of_isSimple hc hlen)
    hstart hfinish z hz
  have hxa : x ≠ c.point i := fun he =>
    hc.1 i hi (left_mem_openSegment_iff.mp (he ▸ hx))
  have hxb : x ≠ c.point (i + 1) := fun he =>
    hc.1 i hi (right_mem_openSegment_iff.mp (he ▸ hx))
  obtain ⟨r, hr, u, v, _, _, hside⟩ := c.exists_side_germs_of_mem_closure_component_diff
    hc U hUopen i hi x (openSegment_subset_segment ℝ _ _ hx) hxa hxb hxU
  refine ⟨i, hi, x, hx, hxU, r, hr, ?_⟩
  exact (hside z hxcl).imp And.right And.right

/-- Helper toward Proposition 5.16: inserting a single straight segment
in a connected open region creates at most two components. Representatives
may coincide, so this includes a nonseparating insertion. -/
theorem exists_two_components_diff_of_length_eq_two
    (c : Polyline) (hc : c.IsSimple) (hlen : c.points.length = 2)
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hinterior : c.interior ⊆ U)
    (hstart : c.start ∉ U) (hfinish : c.finish ∉ U) :
    ∃ u v : ℂ, u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      ∀ z ∈ U \ c.image,
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) u ∨
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) v := by
  have hi : 0 + 1 < c.points.length := by omega
  have hlast : c.point 1 = c.finish := by
    simpa only [hlen, Nat.reduceSub] using c.point_last_eq_finish
  have hedge : openSegment ℝ (c.point 0) (c.point 1) ⊆ U := by
    intro x hx
    apply hinterior
    refine ⟨c.segmentAt_subset_image hi (openSegment_subset_segment ℝ _ _ hx), ?_⟩
    rintro (hxs | hxf)
    · have he : x = c.point 0 := hxs.trans c.point_zero_eq_start.symm
      exact hc.1 0 hi (left_mem_openSegment_iff.mp (he ▸ hx))
    · have he : x = c.point 1 := hxf.trans hlast.symm
      exact hc.1 0 hi (right_mem_openSegment_iff.mp (he ▸ hx))
  obtain ⟨u, v, hu, hv, hcover⟩ := c.exists_two_components_along_openSegment_diff
    hc U hUopen 0 hi hedge
  refine ⟨u, v, hu, hv, ?_⟩
  intro z hz
  obtain ⟨i, hi, x, hx, _, hxcl⟩ := c.exists_openSegment_mem_closure_component_diff
    hc U hUopen hUconn hinterior (c.interior_nonempty_of_isSimple hc (by omega))
    hstart hfinish z hz
  have hi0 : i = 0 := by omega
  subst i
  exact hcover z ⟨x, hx, hxcl⟩

end Polyline

namespace PLDrawing

/-- Helper toward Proposition 5.16: if an extra simple PL arc has vertex
endpoints and its interior lies in one face, every component of that face
minus the arc contains a nonempty left or right side germ of the arc. -/
theorem exists_side_germ_in_face_diff_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (F : P.Face) (c : Polyline) (hc : c.IsSimple) (hlen : 2 ≤ c.points.length)
    (a b : V) (hstart : c.start = P.pos a) (hfinish : c.finish = P.pos b)
    (hinterior : c.interior ⊆ F.val) (z : ℂ) (hz : z ∈ F.val \ c.image) :
    ∃ i : ℕ, i + 1 < c.points.length ∧ ∃ x : ℂ,
      x ∈ openSegment ℝ (c.point i) (c.point (i + 1)) ∧ x ∈ F.val ∧
      ∃ r : ℝ, 0 < r ∧
        (Polyline.leftHalfDisc x (c.point (i + 1) - c.point i) r ⊆
          connectedComponentIn (F.val \ c.image) z ∨
        Polyline.rightHalfDisc x (c.point (i + 1) - c.point i) r ⊆
          connectedComponentIn (F.val \ c.image) z) := by
  apply c.exists_side_germ_subset_component_diff hc hlen F.val
    (P.face_open_frontier_subset_image hvert F).1
    (P.face_isPathConnected hvert F).isConnected hinterior ?_ ?_ z hz
  · intro hs
    exact P.face_subset_compl F hs (Or.inl ⟨a, hstart.symm⟩)
  · intro hf
    exact P.face_subset_compl F hf (Or.inl ⟨b, hfinish.symm⟩)

/-- Helper toward Proposition 5.16: the full at-most-two component bound
for insertion of a straight extra edge in a geometric face. -/
theorem exists_two_components_face_diff_arc_of_length_eq_two
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (F : P.Face) (c : Polyline) (hc : c.IsSimple) (hlen : c.points.length = 2)
    (a b : V) (hstart : c.start = P.pos a) (hfinish : c.finish = P.pos b)
    (hinterior : c.interior ⊆ F.val) :
    ∃ u v : ℂ, u ∈ F.val \ c.image ∧ v ∈ F.val \ c.image ∧
      ∀ z ∈ F.val \ c.image,
        connectedComponentIn (F.val \ c.image) z = connectedComponentIn (F.val \ c.image) u ∨
        connectedComponentIn (F.val \ c.image) z = connectedComponentIn (F.val \ c.image) v := by
  apply c.exists_two_components_diff_of_length_eq_two hc hlen F.val
    (P.face_open_frontier_subset_image hvert F).1
    (P.face_isPathConnected hvert F).isConnected hinterior
  · intro hs
    exact P.face_subset_compl F hs (Or.inl ⟨a, hstart.symm⟩)
  · intro hf
    exact P.face_subset_compl F hf (Or.inl ⟨b, hfinish.symm⟩)

end PLDrawing



















































































end DirectedDistances.PlanarMap

end
