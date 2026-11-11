/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLRegularNeighborhoodPrelim
public import DirectedDistances.PlanarMap.D39BallOrbitComponents4

/-! # Trimmed arc separation toward Proposition 5.16

Helper toward Proposition 5.16: compact edge strips and the data packaging
their separation from the vertex neighborhoods. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Metric Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: the part of an arc image outside every
open vertex ball of radius `r / 2`. -/
def trimmedArc (r : ℝ) (d : D) : Set ℂ :=
  (P.arc d).image ∩ (⋃ v : V, Metric.ball (P.pos v) (r / 2))ᶜ

/-- Helper toward Proposition 5.16: a trimmed arc is compact. -/
theorem isCompact_trimmedArc (r : ℝ) (d : D) : IsCompact (P.trimmedArc r d) := by
  apply (P.arc d).isCompact_image.inter_right
  exact isClosed_compl_iff.mpr (isOpen_iUnion fun v => Metric.isOpen_ball)

/-- Helper toward Proposition 5.16: distinct unoriented arcs have disjoint
trimmed parts whenever the trimmed parts avoid a positive-radius vertex ball. -/
theorem disjoint_trimmedArc (r : ℝ) (hr : 0 < r) (d e : D)
    (hne : d ≠ e) (hflip : e ≠ flip d) :
    Disjoint (P.trimmedArc r d) (P.trimmedArc r e) := by
  apply Set.disjoint_left.mpr
  intro z hzD hzE
  obtain ⟨hdEndpoints, _⟩ := P.arc_intersection_endpoints d e hne.symm hflip hzD.1 hzE.1
  have hfar (v : V) : r / 2 ≤ dist z (P.pos v) := by
    have hnot : z ∉ Metric.ball (P.pos v) (r / 2) := by
      intro hz
      apply hzD.2
      exact Set.mem_iUnion.mpr ⟨v, hz⟩
    exact le_of_not_gt (by simpa only [Metric.mem_ball] using hnot)
  have hpos (hz : z = (P.arc d).start ∨ z = (P.arc d).finish) :
      z = P.pos (vert d) ∨ z = P.pos (vert (flip d)) := by
    rcases hz with hs | hf
    · exact Or.inl (hs.trans (P.arc_start d))
    · exact Or.inr (hf.trans (P.arc_finish d))
  rcases hpos hdEndpoints with hz | hz
  · have h := hfar (vert d)
    rw [hz] at h
    have hhalf : 0 < r / 2 := by linarith
    simp at h
    linarith
  · have h := hfar (vert (flip d))
    rw [hz] at h
    have hhalf : 0 < r / 2 := by linarith
    simp at h
    linarith

/-- Helper toward Proposition 5.16: a uniform vertex-ball radius can also
be chosen smaller than every distance between distinct vertex positions. -/
theorem exists_uniform_vertex_ball_data_and_vertex_gap [Finite D]
    (hvert : Function.Surjective vert) :
    ∃ r : ℝ, 0 < r ∧
      (∀ v : V, ∀ y ∈ Metric.closedBall (P.pos v) r,
        (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0)) ∧
      ∀ v w : V, v ≠ w → r < dist (P.pos v) (P.pos w) := by
  classical
  letI : Finite V := Finite.of_surjective vert hvert
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨r, hr, hlocal, _⟩ := P.exists_uniform_vertex_ball_data hvert
  let I := {p : V × V // p.1 ≠ p.2}
  letI : Finite I := Finite.of_injective Subtype.val Subtype.val_injective
  by_cases hI : Nonempty I
  · let S : Finset ℝ := Finset.univ.image fun p : I =>
      dist (P.pos p.1.1) (P.pos p.1.2)
    have hSne : S.Nonempty := by
      rcases hI with ⟨p⟩
      exact ⟨dist (P.pos p.1.1) (P.pos p.1.2),
        Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩
    let η : ℝ := S.min' hSne
    have hηmem : η ∈ S := Finset.min'_mem S hSne
    have hηpos : 0 < η := by
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hηmem
      rw [← hp]
      apply dist_pos.mpr
      intro hpos
      exact p.2 (P.pos_injective hpos)
    have hηle (v w : V) (hvw : v ≠ w) : η ≤ dist (P.pos v) (P.pos w) :=
      Finset.min'_le S (dist (P.pos v) (P.pos w)) <| Finset.mem_image.mpr
        ⟨⟨(v, w), hvw⟩, Finset.mem_univ _, rfl⟩
    let ρ : ℝ := min r (η / 2)
    have hρ : 0 < ρ := lt_min hr (half_pos hηpos)
    refine ⟨ρ, hρ, ?_, ?_⟩
    · intro v y hy
      exact hlocal v y (Metric.closedBall_subset_closedBall (min_le_left _ _) hy)
    · intro v w hvw
      calc
        ρ ≤ η / 2 := min_le_right _ _
        _ < η := half_lt_self hηpos
        _ ≤ dist (P.pos v) (P.pos w) := hηle v w hvw
  · refine ⟨r, hr, hlocal, ?_⟩
    intro v w hvw
    exact (hI ⟨⟨(v, w), hvw⟩⟩).elim

/-- Helper toward Proposition 5.16: in a sufficiently small uniform vertex
ball, every point of an arc belongs to the initial segment of a dart at that
vertex, and the dart is the same unoriented edge. -/
theorem exists_uniform_vertex_ball_arc_to_dart [Finite D]
    (hvert : Function.Surjective vert) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : V, ∀ e : D, ∀ y ∈ Metric.closedBall (P.pos v) r,
      y ∈ (P.arc e).image →
        ∃ d : D, vert d = v ∧ (e = d ∨ e = flip d) ∧
          y ∈ (P.arc d).segmentAt 0 := by
  obtain ⟨r, hr, hlocal, hgap⟩ := P.exists_uniform_vertex_ball_data_and_vertex_gap hvert
  refine ⟨r, hr, ?_⟩
  intro v e y hyball hyarc
  by_cases hyv : y = P.pos v
  · have hends : y = (P.arc e).start ∨ y = (P.arc e).finish := by
      by_contra h
      have hinterior : y ∈ (P.arc e).interior := by
        refine ⟨hyarc, ?_⟩
        simpa only [mem_insert_iff, mem_singleton_iff] using h
      exact P.interior_avoids_vertices e v (hyv ▸ hinterior)
    rcases hends with hs | hf
    · have hd : vert e = v := P.pos_injective <| by
        calc
          P.pos (vert e) = (P.arc e).start := (P.arc_start e).symm
          _ = y := hs.symm
          _ = P.pos v := hyv
      refine ⟨e, hd, Or.inl rfl, ?_⟩
      rw [Polyline.segmentAt, Polyline.point_zero_eq_start]
      rw [← hs]
      exact left_mem_segment ℝ _ _
    · have hd : vert (flip e) = v := P.pos_injective <| by
        calc
          P.pos (vert (flip e)) = (P.arc e).finish := (P.arc_finish e).symm
          _ = y := hf.symm
          _ = P.pos v := hyv
      refine ⟨flip e, hd, Or.inr (P.flip_involutive e).symm, ?_⟩
      rw [P.arc_flip, Polyline.segmentAt, Polyline.point_zero_eq_start,
        Polyline.start_reverse]
      rw [← hf]
      exact left_mem_segment ℝ _ _
  · have hyimage : y ∈ P.image := Or.inr ⟨e, hyarc⟩
    obtain ⟨d, hd, hyd⟩ := (hlocal v y hyball).mp hyimage
    by_cases hed : e = d
    · exact ⟨d, hd, Or.inl hed, hyd⟩
    by_cases hflip : e = flip d
    · exact ⟨d, hd, Or.inr hflip, hyd⟩
    have hends := P.arc_intersection_endpoints d e hed hflip
      ((P.arc d).segmentAt_subset_image (by have := P.arc_length d; omega) hyd) hyarc
    rcases hends.1 with hs | hf
    · have hypos : y = P.pos v := calc
        y = (P.arc d).start := hs
        _ = P.pos (vert d) := P.arc_start d
        _ = P.pos v := congrArg P.pos hd
      exact (hyv hypos).elim
    · have hdne : vert (flip d) ≠ v := by
        intro hv
        apply hyv
        calc
          y = (P.arc d).finish := hf
          _ = P.pos (vert (flip d)) := P.arc_finish d
          _ = P.pos v := congrArg P.pos hv
      have hball : dist (P.pos v) (P.pos (vert (flip d))) ≤ r := by
        have hball' : dist y (P.pos v) ≤ r := by
          simpa only [Metric.mem_closedBall] using hyball
        rw [hf, P.arc_finish d] at hball'
        simpa only [dist_comm] using hball'
      exact False.elim ((not_lt_of_ge hball) (hgap v (vert (flip d)) hdne.symm))

/-- Helper toward Proposition 5.16: one positive strip radius separates all
trimmed arc pairs in a finite drawing. -/
theorem exists_uniform_edge_strip_separation [Finite D] (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d e : D, d ≠ e → e ≠ flip d →
      ∀ x ∈ (P.arc d).image, (∀ v : V, r / 2 < dist x (P.pos v)) →
      ∀ y ∈ (P.arc e).image, (∀ v : V, r / 2 < dist y (P.pos v)) →
        2 * ε < dist x y := by
  classical
  let I := {p : D × D // p.1 ≠ p.2 ∧ p.2 ≠ flip p.1}
  letI : Finite I := Finite.of_injective Subtype.val Subtype.val_injective
  let Q : Set (ℂ × ℂ) := ⋃ p : I,
    P.trimmedArc r p.1.1 ×ˢ P.trimmedArc r p.1.2
  have hcompact : IsCompact Q := by
    dsimp [Q]
    exact isCompact_iUnion fun p =>
      (P.isCompact_trimmedArc r p.1.1).prod (P.isCompact_trimmedArc r p.1.2)
  have hdisj : Disjoint Q (Set.diagonal ℂ) := by
    apply Set.disjoint_left.mpr
    rintro ⟨x, y⟩ hxy hdiag
    rw [Set.mem_iUnion] at hxy
    obtain ⟨p, hp⟩ := hxy
    have hxy' : (x, y) ∈ P.trimmedArc r p.1.1 ×ˢ P.trimmedArc r p.1.2 := hp
    have hsame : x = y := by simpa only [Set.mem_diagonal_iff] using hdiag
    have hy : x ∈ P.trimmedArc r p.1.2 := hsame ▸ hxy'.2
    exact (Set.disjoint_left.mp
      (P.disjoint_trimmedArc r hr p.1.1 p.1.2 p.2.1 p.2.2)) hxy'.1 hy
  obtain ⟨δ, hδ, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hcompact isClosed_diagonal hdisj
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  refine ⟨(δ : ℝ) / 3, by positivity, ?_⟩
  intro d e hne hflip x hx hxfar y hy hyfar
  have hxtrim : x ∈ P.trimmedArc r d := by
    refine ⟨hx, ?_⟩
    intro hxball
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hxball
    exact (not_lt_of_ge (le_of_lt (hxfar v)))
      (by simpa only [Metric.mem_ball] using hv)
  have hytrim : y ∈ P.trimmedArc r e := by
    refine ⟨hy, ?_⟩
    intro hyball
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hyball
    exact (not_lt_of_ge (le_of_lt (hyfar v)))
      (by simpa only [Metric.mem_ball] using hv)
  have hprod : (x, y) ∈ Q := by
    dsimp [Q]
    rw [Set.mem_iUnion]
    exact ⟨⟨(d, e), ⟨hne, hflip⟩⟩, ⟨hxtrim, hytrim⟩⟩
  have hdiag : (x, x) ∈ Set.diagonal ℂ := by simp
  have hed := hsep (x, y) hprod (x, x) hdiag
  have hed' : (δ : ENNReal) < edist x y := by
    simpa [Prod.edist_eq, edist_comm] using hed
  have hdist : (δ : ℝ) < dist x y := by
    have hnnd : δ < nndist x y := by
      exact ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using hed')
    exact_mod_cast hnnd
  nlinarith

/-- Helper toward Proposition 5.16: the separated vertex balls and edge
strips can be packaged as `D39PLSeparationData`. -/
theorem exists_D39PLSeparationData [Finite D]
    (hvert : Function.Surjective vert) :
    ∃ S : P.D39PLSeparationData hvert, True := by
  obtain ⟨δ, hδ, hsep⟩ := P.exists_uniform_arc_separation
  obtain ⟨r, hr, hlocal, hradial⟩ := P.exists_uniform_vertex_ball_data hvert
  obtain ⟨ε, hε, hstrip⟩ := P.exists_uniform_edge_strip_separation r hr
  refine ⟨{
    delta := δ
    delta_pos := hδ
    arc_separation := ?_
    radius := r
    radius_pos := hr
    vertex_local := hlocal
    radial_disjoint := hradial
    epsilon := ε
    epsilon_pos := hε
    edge_strip_separation := hstrip
  }, trivial⟩
  intro d e hde x hx y hy
  exact le_of_lt (hsep d e hde x hx y hy)

end PLDrawing

end DirectedDistances.PlanarMap
