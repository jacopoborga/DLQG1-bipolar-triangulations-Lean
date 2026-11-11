/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents3

/-! # Regular-neighborhood separation helpers

Helpers toward Proposition 5.16. A PL drawing is thickened using small vertex
neighborhoods and separated edge strips. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Metric Topology

namespace PLDrawing

/-- Helper toward Proposition 5.16: two darts have no shared endpoint when
all four endpoint positions are different. -/
def noSharedEndpoints {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (d e : D) : Prop :=
  P.pos (vert d) ≠ P.pos (vert e) ∧
  P.pos (vert d) ≠ P.pos (vert (flip e)) ∧
  P.pos (vert (flip d)) ≠ P.pos (vert e) ∧
  P.pos (vert (flip d)) ≠ P.pos (vert (flip e))

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: arcs with no shared endpoint have
disjoint images, by interior disjointness and vertex avoidance. -/
theorem arc_image_disjoint_of_noSharedEndpoints (d e : D)
    (h : P.noSharedEndpoints d e) :
    Disjoint (P.arc d).image (P.arc e).image := by
  apply Set.disjoint_left.mpr
  intro z hdz hez
  have hne : e ≠ d := by
    intro he
    subst e
    exact h.1 rfl
  have hflip : e ≠ flip d := by
    intro he
    subst e
    have hdouble : flip (flip d) = d := P.flip_involutive d
    exact h.2.1 (by rw [hdouble])
  have hdCases : z ∈ (P.arc d).interior ∨
      z = (P.arc d).start ∨ z = (P.arc d).finish := by
    by_cases hs : z = (P.arc d).start
    · exact Or.inr (Or.inl hs)
    · by_cases hf : z = (P.arc d).finish
      · exact Or.inr (Or.inr hf)
      · exact Or.inl ⟨hdz, by simp [Polyline.interior, hs, hf]⟩
  have heCases : z ∈ (P.arc e).interior ∨
      z = (P.arc e).start ∨ z = (P.arc e).finish := by
    by_cases hs : z = (P.arc e).start
    · exact Or.inr (Or.inl hs)
    · by_cases hf : z = (P.arc e).finish
      · exact Or.inr (Or.inr hf)
      · exact Or.inl ⟨hez, by simp [Polyline.interior, hs, hf]⟩
  rcases hdCases with hdInt | hdStart | hdFinish
  · rcases heCases with heInt | heStart | heFinish
    · exact (Set.disjoint_left.mp (P.interior_disjoint d e hne hflip)) hdInt heInt
    · have hz : z = P.pos (vert e) := by simpa only [P.arc_start] using heStart
      exact P.interior_avoids_vertices d (vert e) (hz.symm ▸ hdInt)
    · have hz : z = P.pos (vert (flip e)) := by
        simpa only [P.arc_finish] using heFinish
      exact P.interior_avoids_vertices d (vert (flip e)) (hz.symm ▸ hdInt)
  · rcases heCases with heInt | heStart | heFinish
    · have hz : z = P.pos (vert d) := by simpa only [P.arc_start] using hdStart
      exact P.interior_avoids_vertices e (vert d) (hz.symm ▸ heInt)
    · have hpos : P.pos (vert d) = P.pos (vert e) := by
        calc
          P.pos (vert d) = (P.arc d).start := (P.arc_start d).symm
          _ = z := hdStart.symm
          _ = (P.arc e).start := heStart
          _ = P.pos (vert e) := P.arc_start e
      exact h.1 hpos
    · have hpos : P.pos (vert d) = P.pos (vert (flip e)) := by
        calc
          P.pos (vert d) = (P.arc d).start := (P.arc_start d).symm
          _ = z := hdStart.symm
          _ = (P.arc e).finish := heFinish
          _ = P.pos (vert (flip e)) := P.arc_finish e
      exact h.2.1 hpos
  · rcases heCases with heInt | heStart | heFinish
    · have hz : z = P.pos (vert (flip d)) := by
        simpa only [P.arc_finish] using hdFinish
      exact P.interior_avoids_vertices e (vert (flip d)) (hz.symm ▸ heInt)
    · have hpos : P.pos (vert (flip d)) = P.pos (vert e) := by
        calc
          P.pos (vert (flip d)) = (P.arc d).finish := (P.arc_finish d).symm
          _ = z := hdFinish.symm
          _ = (P.arc e).start := heStart
          _ = P.pos (vert e) := P.arc_start e
      exact h.2.2.1 hpos
    · have hpos : P.pos (vert (flip d)) = P.pos (vert (flip e)) := by
        calc
          P.pos (vert (flip d)) = (P.arc d).finish := (P.arc_finish d).symm
          _ = z := hdFinish.symm
          _ = (P.arc e).finish := heFinish
          _ = P.pos (vert (flip e)) := P.arc_finish e
      exact h.2.2.2 hpos

/-- Helper toward Proposition 5.16: one positive distance bound works for
every pair of arcs in a finite drawing that share no endpoint. -/
theorem exists_uniform_arc_separation [Finite D] :
    ∃ δ : NNReal, 0 < δ ∧ ∀ d e : D, P.noSharedEndpoints d e →
      ∀ x ∈ (P.arc d).image, ∀ y ∈ (P.arc e).image,
        ENNReal.ofNNReal δ < edist x y := by
  classical
  let I := {p : D × D // P.noSharedEndpoints p.1 p.2}
  letI : Finite I := Finite.of_injective Subtype.val Subtype.val_injective
  let K : Set (ℂ × ℂ) := ⋃ p : I,
    (P.arc p.1.1).image ×ˢ (P.arc p.1.2).image
  have hcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_iUnion fun p =>
      (P.arc p.1.1).isCompact_image.prod (P.arc p.1.2).isCompact_image
  have hdisj : Disjoint K (Set.diagonal ℂ) := by
    apply Set.disjoint_left.mpr
    rintro ⟨x, y⟩ hxy hdiag
    rw [Set.mem_iUnion] at hxy
    obtain ⟨p, hp⟩ := hxy
    have hxy' : (x, y) ∈ (P.arc p.1.1).image ×ˢ (P.arc p.1.2).image := hp
    have hxyeq : x = y := by simpa only [Set.mem_diagonal_iff] using hdiag
    have hy' : x ∈ (P.arc p.1.2).image := hxyeq ▸ hxy'.2
    exact (Set.disjoint_left.mp
      (P.arc_image_disjoint_of_noSharedEndpoints p.1.1 p.1.2 p.2)) hxy'.1 hy'
  obtain ⟨δ, hδ, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hcompact isClosed_diagonal hdisj
  refine ⟨δ, hδ, ?_⟩
  intro d e hde x hx y hy
  have hmem : (x, y) ∈ K := by
    dsimp [K]
    rw [Set.mem_iUnion]
    exact ⟨⟨(d, e), hde⟩, ⟨hx, hy⟩⟩
  have hdiag : (x, x) ∈ Set.diagonal ℂ := by simp
  have h := hsep (x, y) hmem (x, x) hdiag
  simpa [Prod.edist_eq, edist_comm] using h

/-- Helper toward Proposition 5.16: a closed ball of positive radius has
exactly the outgoing initial segments in the drawing image. -/
theorem exists_closedBall_image_eq_initial_segments [Finite D]
    (hvert : Function.Surjective vert) (v : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.closedBall (P.pos v) r,
      (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0) := by
  obtain ⟨R, hR, hlocal⟩ := P.exists_ball_image_eq_initial_segments hvert v
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro y hy
  have hydist : dist y (P.pos v) ≤ R / 2 := by
    simpa only [Metric.mem_closedBall] using hy
  have hlt : dist y (P.pos v) < R := by linarith
  have hyball : y ∈ ball (P.pos v) R := by
    simpa only [Metric.mem_ball] using hlt
  exact hlocal y hyball

/-- Helper toward Proposition 5.16: one closed-ball radius works at every
vertex of a finite drawing. -/
theorem exists_uniform_closedBall_image_eq_initial_segments [Finite D]
    (hvert : Function.Surjective vert) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : V, ∀ y ∈ Metric.closedBall (P.pos v) r,
      (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0) := by
  classical
  letI : Finite V := Finite.of_surjective vert hvert
  letI : Fintype V := Fintype.ofFinite V
  let R : V → ℝ := fun v => Classical.choose (P.exists_closedBall_image_eq_initial_segments hvert v)
  have hR (v : V) : 0 < R v ∧
      ∀ y ∈ Metric.closedBall (P.pos v) (R v),
        (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0) :=
    Classical.choose_spec (P.exists_closedBall_image_eq_initial_segments hvert v)
  by_cases hV : Nonempty V
  · let S := Finset.univ.image R
    have hSne : S.Nonempty := by
      rcases hV with ⟨v⟩
      exact ⟨R v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
    let r := S.min' hSne
    have hrmem : r ∈ S := Finset.min'_mem S hSne
    have hrpos : 0 < r := by
      rcases Finset.mem_image.mp hrmem with ⟨v, _, hv⟩
      simpa only [← hv] using (hR v).1
    have hrle (v : V) : r ≤ R v :=
      Finset.min'_le S (R v) (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
    refine ⟨r, hrpos, ?_⟩
    intro v y hy
    exact (hR v).2 y (Metric.closedBall_subset_closedBall (hrle v) hy)
  · refine ⟨1, by norm_num, ?_⟩
    intro v
    exact (hV ⟨v⟩).elim

/-- Helper toward Proposition 5.16: two initial radial segments at one vertex
meet only at that vertex. -/
theorem initial_segments_intersection_eq_vertex (v : V) (d e : D)
    (hd : vert d = v) (he : vert e = v) (hne : d ≠ e)
    {z : ℂ} (hzd : z ∈ (P.arc d).segmentAt 0)
    (hze : z ∈ (P.arc e).segmentAt 0) : z = P.pos v := by
  by_contra hzv
  have hstartd : (P.arc d).point 0 = P.pos v := by
    rw [Polyline.point_zero_eq_start, P.arc_start, hd]
  have hstarte : (P.arc e).point 0 = P.pos v := by
    rw [Polyline.point_zero_eq_start, P.arc_start, he]
  have hsegd := hzd
  have hsege := hze
  rw [Polyline.segmentAt, hstartd, segment_eq_image'] at hsegd
  rw [Polyline.segmentAt, hstarte, segment_eq_image'] at hsege
  obtain ⟨s, hs, hsd⟩ := hsegd
  obtain ⟨t, ht, hte⟩ := hsege
  have hdirD : (P.arc d).point 1 - P.pos v = (P.arc d).initialDirection := by
    rw [Polyline.initialDirection, P.arc_start, hd]
  have hdirE : (P.arc e).point 1 - P.pos v = (P.arc e).initialDirection := by
    rw [Polyline.initialDirection, P.arc_start, he]
  have hsd' : P.pos v + (s : ℂ) • (P.arc d).initialDirection = z := by
    change P.pos v + (s : ℂ) • ((P.arc d).point 1 - P.pos v) = z at hsd
    simpa only [hdirD] using hsd
  have hte' : P.pos v + (t : ℂ) • (P.arc e).initialDirection = z := by
    change P.pos v + (t : ℂ) • ((P.arc e).point 1 - P.pos v) = z at hte
    simpa only [hdirE] using hte
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (by
    intro hs0
    apply hzv
    calc
      z = P.pos v + (s : ℂ) • (P.arc d).initialDirection := hsd'.symm
      _ = P.pos v := by simp [hs0])
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro ht0
    apply hzv
    calc
      z = P.pos v + (t : ℂ) • (P.arc e).initialDirection := hte'.symm
      _ = P.pos v := by simp [ht0])
  have hmul : (s : ℂ) * (P.arc d).initialDirection =
      (t : ℂ) * (P.arc e).initialDirection := by
    have heq := hsd'.trans hte'.symm
    have heq' : P.pos v + (s : ℂ) * (P.arc d).initialDirection =
        P.pos v + (t : ℂ) * (P.arc e).initialDirection := by
      change P.pos v + (s : ℂ) * (P.arc d).initialDirection =
        P.pos v + (t : ℂ) * (P.arc e).initialDirection at heq
      exact heq
    exact add_left_cancel heq'
  have harg := congrArg Complex.arg hmul
  rw [Complex.arg_real_mul _ hspos, Complex.arg_real_mul _ htpos] at harg
  exact hne (P.initial_arg_injective d e (hd.trans he.symm) harg)

/-- Helper toward Proposition 5.16: one positive radius isolates every
vertex star, and the incident initial radial pieces meet only at the vertex. -/
theorem exists_uniform_vertex_ball_data [Finite D]
    (hvert : Function.Surjective vert) :
    ∃ r : ℝ, 0 < r ∧
      (∀ v : V, ∀ y ∈ Metric.closedBall (P.pos v) r,
        (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0)) ∧
      (∀ v : V, ∀ d e : D, vert d = v → vert e = v → d ≠ e →
        ∀ z ∈ (P.arc d).segmentAt 0 ∩ Metric.closedBall (P.pos v) r,
          z ∈ (P.arc e).segmentAt 0 → z = P.pos v) := by
  obtain ⟨r, hr, hlocal⟩ := P.exists_uniform_closedBall_image_eq_initial_segments hvert
  refine ⟨r, hr, hlocal, ?_⟩
  intro v d e hd he hne z hz hze
  exact P.initial_segments_intersection_eq_vertex v d e hd he hne hz.1 hze

/-- Helper toward Proposition 5.16: data certifying isolated vertex stars
and pairwise separated edge strips for a finite PL drawing. -/
structure D39PLSeparationData [Finite D]
    (hvert : Function.Surjective vert) where
  /-- Helper toward Proposition 5.16: the uniform gap for arcs with no common endpoint. -/
  delta : NNReal
  /-- Helper toward Proposition 5.16: the uniform arc gap is positive. -/
  delta_pos : 0 < delta
  /-- Helper toward Proposition 5.16: every two nonincident arcs are at least
  `delta` apart in extended distance. -/
  arc_separation : ∀ d e : D, P.noSharedEndpoints d e →
    ∀ x ∈ (P.arc d).image, ∀ y ∈ (P.arc e).image,
      ENNReal.ofNNReal delta ≤ edist x y
  /-- Helper toward Proposition 5.16: the common vertex-ball radius. -/
  radius : ℝ
  /-- Helper toward Proposition 5.16: the vertex-ball radius is positive. -/
  radius_pos : 0 < radius
  /-- Helper toward Proposition 5.16: the drawing image in each closed vertex
  ball consists exactly of outgoing initial segments. -/
  vertex_local : ∀ v : V, ∀ y ∈ Metric.closedBall (P.pos v) radius,
    (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0)
  /-- Helper toward Proposition 5.16: distinct radial pieces at a vertex meet
  only at its position. -/
  radial_disjoint : ∀ v : V, ∀ d e : D, vert d = v → vert e = v → d ≠ e →
    ∀ z ∈ (P.arc d).segmentAt 0 ∩ Metric.closedBall (P.pos v) radius,
      z ∈ (P.arc e).segmentAt 0 → z = P.pos v
  /-- Helper toward Proposition 5.16: the common closed edge-strip radius. -/
  epsilon : ℝ
  /-- Helper toward Proposition 5.16: the edge-strip radius is positive. -/
  epsilon_pos : 0 < epsilon
  /-- Helper toward Proposition 5.16: after removing all vertex balls of
  radius `radius / 2`, distinct unoriented arcs have separated closed strips. -/
  edge_strip_separation : ∀ d e : D, d ≠ e → e ≠ flip d →
    ∀ x ∈ (P.arc d).image, (∀ v : V, radius / 2 < dist x (P.pos v)) →
    ∀ y ∈ (P.arc e).image, (∀ v : V, radius / 2 < dist y (P.pos v)) →
      2 * epsilon < dist x y





































end PLDrawing

end DirectedDistances.PlanarMap
