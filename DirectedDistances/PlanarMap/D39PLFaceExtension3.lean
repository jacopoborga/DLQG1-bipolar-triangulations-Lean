/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLFaceExtension2

/-! Helpers toward Proposition 5.16: boundary chains for the square annulus. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
namespace Polyline
open Set Topology

/-- Helper toward Proposition 5.16: the upper square boundary chain from
`(-R,a)` to `(R,b)`, through the two upper corners. -/
@[expose] def squareUpperChain (R a b : ℝ) : Polyline :=
  ofHead (⟨-R, a⟩ : ℂ) [⟨-R, R⟩, ⟨R, R⟩, ⟨R, b⟩]

/-- Helper toward Proposition 5.16: the lower square boundary chain from
`(-R,a)` to `(R,b)`, through the two lower corners. -/
@[expose] def squareLowerChain (R a b : ℝ) : Polyline :=
  ofHead (⟨-R, a⟩ : ℂ) [⟨-R, -R⟩, ⟨R, -R⟩, ⟨R, b⟩]

/-- Helper toward Proposition 5.16: exact endpoints and lengths of both
outer chains. -/
theorem square_chains_data (R a b : ℝ) :
    (squareUpperChain R a b).start = (⟨-R, a⟩ : ℂ) ∧
    (squareUpperChain R a b).finish = (⟨R, b⟩ : ℂ) ∧
    (squareUpperChain R a b).points.length = 4 ∧
    (squareLowerChain R a b).start = (⟨-R, a⟩ : ℂ) ∧
    (squareLowerChain R a b).finish = (⟨R, b⟩ : ℂ) ∧
    (squareLowerChain R a b).points.length = 4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Helper toward Proposition 5.16: coordinate descriptions of the three
upper boundary segments. -/
theorem squareUpperChain_segmentAt (R a b : ℝ) (hR : 0 < R)
    (ha : a < R) (hb : b < R) (z : ℂ) :
    (z ∈ (squareUpperChain R a b).segmentAt 0 ↔ a ≤ z.im ∧ z.im ≤ R ∧ z.re = -R) ∧
    (z ∈ (squareUpperChain R a b).segmentAt 1 ↔ -R ≤ z.re ∧ z.re ≤ R ∧ z.im = R) ∧
    (z ∈ (squareUpperChain R a b).segmentAt 2 ↔ b ≤ z.im ∧ z.im ≤ R ∧ z.re = R) := by
  refine ⟨mem_vertical_segment_iff a R (-R) ha z,
    mem_horizontal_segment_iff (-R) R R (by linarith only [hR]) z, ?_⟩
  change z ∈ segment ℝ (⟨R, R⟩ : ℂ) ⟨R, b⟩ ↔ _
  rw [segment_symm]
  exact mem_vertical_segment_iff b R R hb z

/-- Helper toward Proposition 5.16: coordinate descriptions of the three
lower boundary segments. -/
theorem squareLowerChain_segmentAt (R a b : ℝ) (hR : 0 < R)
    (ha : -R < a) (hb : -R < b) (z : ℂ) :
    (z ∈ (squareLowerChain R a b).segmentAt 0 ↔ -R ≤ z.im ∧ z.im ≤ a ∧ z.re = -R) ∧
    (z ∈ (squareLowerChain R a b).segmentAt 1 ↔ -R ≤ z.re ∧ z.re ≤ R ∧ z.im = -R) ∧
    (z ∈ (squareLowerChain R a b).segmentAt 2 ↔ -R ≤ z.im ∧ z.im ≤ b ∧ z.re = R) := by
  refine ⟨?_, mem_horizontal_segment_iff (-R) R (-R) (by linarith only [hR]) z,
    mem_vertical_segment_iff (-R) b R hb z⟩
  change z ∈ segment ℝ (⟨-R, a⟩ : ℂ) ⟨-R, -R⟩ ↔ _
  rw [segment_symm]
  exact mem_vertical_segment_iff (-R) a (-R) ha z

/-- Helper toward Proposition 5.16: the upper chain image consists exactly
of its three coordinate segments. -/
theorem mem_squareUpperChain_image_iff (R a b : ℝ) (hR : 0 < R)
    (ha : a < R) (hb : b < R) (z : ℂ) :
    z ∈ (squareUpperChain R a b).image ↔
      (a ≤ z.im ∧ z.im ≤ R ∧ z.re = -R) ∨
      (-R ≤ z.re ∧ z.re ≤ R ∧ z.im = R) ∨
      (b ≤ z.im ∧ z.im ≤ R ∧ z.re = R) := by
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · have hz' : z = (⟨-R, a⟩ : ℂ) := hz
      subst z
      exact Or.inl ⟨le_rfl, ha.le, rfl⟩
    · change i + 1 < 4 at hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl ((squareUpperChain_segmentAt R a b hR ha hb z).1.mp hz)
      · exact Or.inr (Or.inl ((squareUpperChain_segmentAt R a b hR ha hb z).2.1.mp hz))
      · exact Or.inr (Or.inr ((squareUpperChain_segmentAt R a b hR ha hb z).2.2.mp hz))
  · rintro (hz | hz | hz)
    · exact Or.inr ⟨0, by change 1 < 4; omega,
        (squareUpperChain_segmentAt R a b hR ha hb z).1.mpr hz⟩
    · exact Or.inr ⟨1, by change 2 < 4; omega,
        (squareUpperChain_segmentAt R a b hR ha hb z).2.1.mpr hz⟩
    · exact Or.inr ⟨2, by change 3 < 4; omega,
        (squareUpperChain_segmentAt R a b hR ha hb z).2.2.mpr hz⟩

/-- Helper toward Proposition 5.16: the lower chain image consists exactly
of its three coordinate segments. -/
theorem mem_squareLowerChain_image_iff (R a b : ℝ) (hR : 0 < R)
    (ha : -R < a) (hb : -R < b) (z : ℂ) :
    z ∈ (squareLowerChain R a b).image ↔
      (-R ≤ z.im ∧ z.im ≤ a ∧ z.re = -R) ∨
      (-R ≤ z.re ∧ z.re ≤ R ∧ z.im = -R) ∨
      (-R ≤ z.im ∧ z.im ≤ b ∧ z.re = R) := by
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · have hz' : z = (⟨-R, a⟩ : ℂ) := hz
      subst z
      exact Or.inl ⟨ha.le, le_rfl, rfl⟩
    · change i + 1 < 4 at hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl ((squareLowerChain_segmentAt R a b hR ha hb z).1.mp hz)
      · exact Or.inr (Or.inl ((squareLowerChain_segmentAt R a b hR ha hb z).2.1.mp hz))
      · exact Or.inr (Or.inr ((squareLowerChain_segmentAt R a b hR ha hb z).2.2.mp hz))
  · rintro (hz | hz | hz)
    · exact Or.inr ⟨0, by change 1 < 4; omega,
        (squareLowerChain_segmentAt R a b hR ha hb z).1.mpr hz⟩
    · exact Or.inr ⟨1, by change 2 < 4; omega,
        (squareLowerChain_segmentAt R a b hR ha hb z).2.1.mpr hz⟩
    · exact Or.inr ⟨2, by change 3 < 4; omega,
        (squareLowerChain_segmentAt R a b hR ha hb z).2.2.mpr hz⟩

/-- Helper toward Proposition 5.16: the upper outer chain is simple when
both slit endpoints lie strictly below the upper corners. -/
theorem squareUpperChain_isSimple (R a b : ℝ) (hR : 0 < R)
    (ha : a < R) (hb : b < R) : (squareUpperChain R a b).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    change i + 1 < 4 at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    all_goals
      norm_num [squareUpperChain, ofHead, point, start, Complex.ext_iff]
      ; linarith only [hR, ha, hb]
  · intro i hi
    change i + 2 < 4 at hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · ext z
      rw [mem_inter_iff, (squareUpperChain_segmentAt R a b hR ha hb z).1,
        (squareUpperChain_segmentAt R a b hR ha hb z).2.1, mem_singleton_iff]
      change (_ ∧ _) ↔ z = (⟨-R, R⟩ : ℂ)
      rw [Complex.ext_iff]
      constructor
      · intro hz; exact ⟨hz.1.2.2, hz.2.2.2⟩
      · rintro ⟨hre, him⟩
        rw [hre, him]
        exact ⟨⟨ha.le, le_rfl, rfl⟩, ⟨le_rfl, by linarith only [hR], rfl⟩⟩
    · ext z
      rw [mem_inter_iff, (squareUpperChain_segmentAt R a b hR ha hb z).2.1,
        (squareUpperChain_segmentAt R a b hR ha hb z).2.2, mem_singleton_iff]
      change (_ ∧ _) ↔ z = (⟨R, R⟩ : ℂ)
      rw [Complex.ext_iff]
      constructor
      · intro hz; exact ⟨hz.2.2.2, hz.1.2.2⟩
      · rintro ⟨hre, him⟩
        rw [hre, him]
        exact ⟨⟨by linarith only [hR], le_rfl, rfl⟩, ⟨hb.le, le_rfl, rfl⟩⟩
  · intro i j hi hj hij
    change i + 1 < 4 at hi
    change j + 1 < 4 at hj
    have hi0 : i = 0 := by omega
    have hj2 : j = 2 := by omega
    subst i; subst j
    apply Set.disjoint_left.mpr
    intro z hz hw
    have hz' := (squareUpperChain_segmentAt R a b hR ha hb z).1.mp hz
    have hw' := (squareUpperChain_segmentAt R a b hR ha hb z).2.2.mp hw
    linarith only [hz'.2.2, hw'.2.2, hR]

/-- Helper toward Proposition 5.16: the lower outer chain is simple when
both slit endpoints lie strictly above the lower corners. -/
theorem squareLowerChain_isSimple (R a b : ℝ) (hR : 0 < R)
    (ha : -R < a) (hb : -R < b) : (squareLowerChain R a b).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    change i + 1 < 4 at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    all_goals
      norm_num [squareLowerChain, ofHead, point, start, Complex.ext_iff]
      ; linarith only [hR, ha, hb]
  · intro i hi
    change i + 2 < 4 at hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · ext z
      rw [mem_inter_iff, (squareLowerChain_segmentAt R a b hR ha hb z).1,
        (squareLowerChain_segmentAt R a b hR ha hb z).2.1, mem_singleton_iff]
      change (_ ∧ _) ↔ z = (⟨-R, -R⟩ : ℂ)
      rw [Complex.ext_iff]
      constructor
      · intro hz; exact ⟨hz.1.2.2, hz.2.2.2⟩
      · rintro ⟨hre, him⟩
        rw [hre, him]
        exact ⟨⟨le_rfl, ha.le, rfl⟩, ⟨le_rfl, by linarith only [hR], rfl⟩⟩
    · ext z
      rw [mem_inter_iff, (squareLowerChain_segmentAt R a b hR ha hb z).2.1,
        (squareLowerChain_segmentAt R a b hR ha hb z).2.2, mem_singleton_iff]
      change (_ ∧ _) ↔ z = (⟨R, -R⟩ : ℂ)
      rw [Complex.ext_iff]
      constructor
      · intro hz; exact ⟨hz.2.2.2, hz.1.2.2⟩
      · rintro ⟨hre, him⟩
        rw [hre, him]
        exact ⟨⟨by linarith only [hR], le_rfl, rfl⟩, ⟨le_rfl, hb.le, rfl⟩⟩
  · intro i j hi hj hij
    change i + 1 < 4 at hi
    change j + 1 < 4 at hj
    have hi0 : i = 0 := by omega
    have hj2 : j = 2 := by omega
    subst i; subst j
    apply Set.disjoint_left.mpr
    intro z hz hw
    have hz' := (squareLowerChain_segmentAt R a b hR ha hb z).1.mp hz
    have hw' := (squareLowerChain_segmentAt R a b hR ha hb z).2.2.mp hw
    linarith only [hz'.2.2, hw'.2.2, hR]

/-- Helper toward Proposition 5.16: the two outer boundary chains cover
exactly the square boundary, including the subdivided vertical edges. -/
theorem square_chains_image_union (R a b : ℝ) (hR : 0 < R)
    (ha : -R < a ∧ a < R) (hb : -R < b ∧ b < R) :
    (squareUpperChain R a b).image ∪ (squareLowerChain R a b).image =
      (enclosingSquare R).image := by
  ext z
  rw [mem_union, mem_squareUpperChain_image_iff R a b hR ha.2 hb.2,
    mem_squareLowerChain_image_iff R a b hR ha.1 hb.1,
    mem_enclosingSquare_image_iff R hR]
  constructor
  · rintro ((hl | ht | hr) | (hl | hd | hr))
    · exact ⟨by rw [hl.2.2]; exact ⟨le_rfl, by linarith only [hR]⟩,
        ⟨ha.1.le.trans hl.1, hl.2.1⟩, Or.inl hl.2.2⟩
    · exact ⟨⟨ht.1, ht.2.1⟩, by rw [ht.2.2]; exact ⟨by linarith only [hR], le_rfl⟩,
        Or.inr (Or.inr (Or.inr ht.2.2))⟩
    · exact ⟨by rw [hr.2.2]; exact ⟨by linarith only [hR], le_rfl⟩,
        ⟨hb.1.le.trans hr.1, hr.2.1⟩, Or.inr (Or.inl hr.2.2)⟩
    · exact ⟨by rw [hl.2.2]; exact ⟨le_rfl, by linarith only [hR]⟩,
        ⟨hl.1, hl.2.1.trans ha.2.le⟩, Or.inl hl.2.2⟩
    · exact ⟨⟨hd.1, hd.2.1⟩, by rw [hd.2.2]; exact ⟨le_rfl, by linarith only [hR]⟩,
        Or.inr (Or.inr (Or.inl hd.2.2))⟩
    · exact ⟨by rw [hr.2.2]; exact ⟨by linarith only [hR], le_rfl⟩,
        ⟨hr.1, hr.2.1.trans hb.2.le⟩, Or.inr (Or.inl hr.2.2)⟩
  · rintro ⟨hre, him, hl | hr | hd | ht⟩
    · by_cases ha' : a ≤ z.im
      · exact Or.inl (Or.inl ⟨ha', him.2, hl⟩)
      · exact Or.inr (Or.inl ⟨him.1, (lt_of_not_ge ha').le, hl⟩)
    · by_cases hb' : b ≤ z.im
      · exact Or.inl (Or.inr (Or.inr ⟨hb', him.2, hr⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨him.1, (lt_of_not_ge hb').le, hr⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hre.1, hre.2, hd⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨hre.1, hre.2, ht⟩))

/-- Helper toward Proposition 5.16: the outer chains have exactly their
two common endpoints in common. -/
theorem square_chains_image_inter (R a b : ℝ) (hR : 0 < R)
    (ha : -R < a ∧ a < R) (hb : -R < b ∧ b < R) :
    (squareUpperChain R a b).image ∩ (squareLowerChain R a b).image =
      {(⟨-R, a⟩ : ℂ), (⟨R, b⟩ : ℂ)} := by
  ext z
  rw [mem_inter_iff, mem_squareUpperChain_image_iff R a b hR ha.2 hb.2,
    mem_squareLowerChain_image_iff R a b hR ha.1 hb.1]
  constructor
  · rintro ⟨hl | ht | hr, hl' | hd | hr'⟩
    · exact Or.inl (Complex.ext hl.2.2 (le_antisymm hl'.2.1 hl.1))
    · exact False.elim (by linarith only [hl.1, hd.2.2, ha.1])
    · exact False.elim (by linarith only [hl.2.2, hr'.2.2, hR])
    · exact False.elim (by linarith only [ht.2.2, hl'.2.1, ha.2])
    · exact False.elim (by linarith only [ht.2.2, hd.2.2, hR])
    · exact False.elim (by linarith only [ht.2.2, hr'.2.1, hb.2])
    · exact False.elim (by linarith only [hr.2.2, hl'.2.2, hR])
    · exact False.elim (by linarith only [hr.1, hd.2.2, hb.1])
    · exact Or.inr (Complex.ext hr.2.2 (le_antisymm hr'.2.1 hr.1))
  · rintro (rfl | rfl)
    · exact ⟨Or.inl ⟨le_rfl, ha.2.le, rfl⟩, Or.inl ⟨ha.1.le, le_rfl, rfl⟩⟩
    · exact ⟨Or.inr (Or.inr ⟨le_rfl, hb.2.le, rfl⟩),
        Or.inr (Or.inr ⟨hb.1.le, le_rfl, rfl⟩)⟩

/-- Helper toward Proposition 5.16: the indexed inner chains retain all
their endpoints, simplicity, exact image cover and intersection, and signed
angle additivity in a single construction. No interior diagonal is required. -/
theorem inner_boundary_chains_data (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) :
    let p := c.intervalPolyline i (j - i)
    let q := c.diagonalComplement i j
    p.IsSimple ∧ q.IsSimple ∧
      2 ≤ p.points.length ∧ 2 ≤ q.points.length ∧
      p.start = c.point i ∧ p.finish = c.point j ∧
      q.start = c.point j ∧ q.finish = c.point i ∧
      p.image ∪ q.image = c.image ∧
      p.image ∩ q.image = {c.point i, c.point j} ∧
      (∀ z : ℂ, p.angleSum z + q.angleSum z = c.angleSum z) := by
  dsimp only
  obtain ⟨hqstart, hqfinish, _⟩ := c.diagonalComplement_data hc i j hij hj
  refine ⟨c.isSimple_intervalPolyline_cyclic hc i (j - i) (by omega) (by omega),
    c.isSimple_diagonalComplement hc i j hij hj, ?_, ?_,
    start_intervalPolyline _ _ _, ?_, hqstart, hqfinish,
    c.diagonal_arcs_image_union hc i j hij hj,
    c.diagonal_arcs_image_inter hc i j hij hj, ?_⟩
  · rw [length_intervalPolyline]; omega
  · rw [length_diagonalComplement _ _ _ hj]; omega
  · rw [finish_intervalPolyline, show i + (j - i) = j by omega]
  · intro z
    exact (c.angleSum_diagonal_arcs hc i j hij hj z).symm

/-- Helper toward Proposition 5.16: any listed vertex of a cyclic polygon
has a representative before the repeated closing vertex. -/
theorem exists_vertex_index_before_closure (c : Polyline) (hc : c.IsCyclicSimple)
    (i : ℕ) (hi : i < c.points.length) :
    ∃ k : ℕ, k + 1 < c.points.length ∧ c.point k = c.point i := by
  by_cases hlast : i + 1 = c.points.length
  · refine ⟨0, by have hlen := hc.1; omega, ?_⟩
    rw [show i = c.points.length - 1 by omega]
    exact hc.2.1
  · exact ⟨i, by omega, rfl⟩

/-- Helper toward Proposition 5.16: two distinct polygon vertices split
the inner boundary into two oppositely joined simple arcs. The indices may
occur in either order and may include the repeated root. -/
theorem exists_inner_boundary_chains (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hi : i < c.points.length) (hj : j < c.points.length)
    (hne : c.point i ≠ c.point j) :
    ∃ p q : Polyline, p.IsSimple ∧ q.IsSimple ∧
      2 ≤ p.points.length ∧ 2 ≤ q.points.length ∧
      p.start = c.point i ∧ p.finish = c.point j ∧
      q.start = c.point j ∧ q.finish = c.point i ∧
      p.image ∪ q.image = c.image ∧
      p.image ∩ q.image = {c.point i, c.point j} ∧
      (∀ z : ℂ, p.angleSum z + q.angleSum z = c.angleSum z) := by
  obtain ⟨k, hk, hki⟩ := c.exists_vertex_index_before_closure hc i hi
  obtain ⟨l, hl, hlj⟩ := c.exists_vertex_index_before_closure hc j hj
  have hkl : k ≠ l := by
    intro heq
    exact hne (hki.symm.trans ((congrArg c.point heq).trans hlj))
  rcases lt_or_gt_of_ne hkl with hkl | hlk
  · obtain ⟨hp, hq, hplen, hqlen, hpstart, hpfinish, hqstart, hqfinish,
      hunion, hinter, hangle⟩ := c.inner_boundary_chains_data hc k l hkl hl
    exact ⟨_, _, hp, hq, hplen, hqlen, hpstart.trans hki, hpfinish.trans hlj,
      hqstart.trans hlj, hqfinish.trans hki, hunion,
      by simpa only [hki, hlj] using hinter, hangle⟩
  · obtain ⟨hp, hq, hplen, hqlen, hpstart, hpfinish, hqstart, hqfinish,
      hunion, hinter, hangle⟩ := c.inner_boundary_chains_data hc l k hlk hk
    refine ⟨_, _, hq, hp, hqlen, hplen, hqstart.trans hki, hqfinish.trans hlj,
      hpstart.trans hlj, hpfinish.trans hki, ?_, ?_, ?_⟩
    · rw [union_comm]; exact hunion
    · rw [inter_comm, hinter, hlj, hki, pair_comm]
    · intro z
      rw [add_comm]
      exact hangle z

/-- Helper toward Proposition 5.16: segments preceding a concatenation join
are unchanged. -/
theorem segmentAt_boundaryConcat_left (p q : Polyline) (i : ℕ)
    (hi : i + 1 < p.points.length) :
    (boundaryConcat p q).segmentAt i = p.segmentAt i := by
  simp only [segmentAt, point_boundaryConcat_left p q i (by omega),
    point_boundaryConcat_left p q (i + 1) hi]

/-- Helper toward Proposition 5.16: segments following a compatible
concatenation join are unchanged, including the segment at the join. -/
theorem segmentAt_boundaryConcat_right (p q : Polyline) (hjoin : p.finish = q.start)
    (i : ℕ) (hi : i + 1 < q.points.length) :
    (boundaryConcat p q).segmentAt (p.points.length - 1 + i) = q.segmentAt i := by
  simp only [segmentAt, Nat.add_assoc,
    point_boundaryConcat_right p q hjoin i (by omega),
    point_boundaryConcat_right p q hjoin (i + 1) hi]

/-- Helper toward Proposition 5.16: two simple chains meeting only at
their compatible join concatenate to a simple chain. -/
theorem isSimple_boundaryConcat (p q : Polyline) (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hjoin : p.finish = q.start) (hint : p.image ∩ q.image = {p.finish}) :
    (boundaryConcat p q).IsSimple := by
  have hcross (i j : ℕ) (hi : i + 1 < p.points.length)
      (hj : j + 1 < q.points.length) (z : ℂ)
      (hzi : z ∈ p.segmentAt i) (hzj : z ∈ q.segmentAt j) :
      z = p.finish ∧ i + 2 = p.points.length ∧ j = 0 := by
    have hz : z = p.finish := mem_singleton_iff.mp
      (hint ▸ (show z ∈ p.image ∩ q.image from
        ⟨Or.inr ⟨i, hi, hzi⟩, Or.inr ⟨j, hj, hzj⟩⟩))
    have hip := p.segmentAt_index_last_of_finish_mem hp hlenp hi (hz ▸ hzi)
    have hjq := q.segmentAt_index_eq_zero_of_start_mem hq hlenq hj
      (by rwa [hz, hjoin] at hzj)
    exact ⟨hz, hip, hjq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [length_boundaryConcat] at hi
    by_cases hleft : i + 1 < p.points.length
    · rw [point_boundaryConcat_left p q i (by omega),
        point_boundaryConcat_left p q (i + 1) hleft]
      exact hp.1 i hleft
    · have hidx : i = p.points.length - 1 + (i - (p.points.length - 1)) := by omega
      rw [hidx, show p.points.length - 1 + (i - (p.points.length - 1)) + 1 =
        p.points.length - 1 + (i - (p.points.length - 1) + 1) by omega,
        point_boundaryConcat_right p q hjoin _ (by omega),
        point_boundaryConcat_right p q hjoin _ (by omega)]
      exact hq.1 _ (by omega)
  · intro i hi
    rw [length_boundaryConcat] at hi
    by_cases hleft : i + 2 < p.points.length
    · rw [segmentAt_boundaryConcat_left p q i (by omega),
        segmentAt_boundaryConcat_left p q (i + 1) (by omega),
        point_boundaryConcat_left p q (i + 1) (by omega)]
      exact hp.2.1 i hleft
    · by_cases hright : p.points.length - 1 ≤ i
      · have hidx : i = p.points.length - 1 + (i - (p.points.length - 1)) := by omega
        rw [hidx, show p.points.length - 1 + (i - (p.points.length - 1)) + 1 =
          p.points.length - 1 + (i - (p.points.length - 1) + 1) by omega,
          segmentAt_boundaryConcat_right p q hjoin _ (by omega),
          segmentAt_boundaryConcat_right p q hjoin _ (by omega),
          point_boundaryConcat_right p q hjoin _ (by omega)]
        exact hq.2.1 _ (by omega)
      · have hnext : i + 1 = p.points.length - 1 + 0 := by omega
        rw [segmentAt_boundaryConcat_left p q i (by omega), hnext,
          segmentAt_boundaryConcat_right p q hjoin 0 (by omega),
          point_boundaryConcat_right p q hjoin 0 (by omega), point_zero_eq_start]
        ext z
        constructor
        · intro hz
          exact (hcross i 0 (by omega) (by omega) z hz.1 hz.2).1.trans hjoin
        · intro hz
          have hzeq : z = q.start := hz
          subst z
          constructor
          · rw [← hjoin, ← point_last_eq_finish,
              show p.points.length - 1 = i + 1 by omega]
            exact right_mem_segment ℝ _ _
          · rw [← point_zero_eq_start]
            exact left_mem_segment ℝ _ _
  · intro i j hi hj hij
    rw [length_boundaryConcat] at hi hj
    by_cases hleft : j + 1 < p.points.length
    · rw [segmentAt_boundaryConcat_left p q i (by omega),
        segmentAt_boundaryConcat_left p q j hleft]
      exact hp.2.2 i j (by omega) hleft hij
    · have hjidx : j = p.points.length - 1 + (j - (p.points.length - 1)) := by omega
      rw [hjidx, segmentAt_boundaryConcat_right p q hjoin _ (by omega)]
      by_cases hright : p.points.length - 1 ≤ i
      · have hiidx : i = p.points.length - 1 + (i - (p.points.length - 1)) := by omega
        rw [hiidx, segmentAt_boundaryConcat_right p q hjoin _ (by omega)]
        exact hq.2.2 _ _ (by omega) (by omega) (by omega)
      · rw [segmentAt_boundaryConcat_left p q i (by omega)]
        apply Set.disjoint_left.mpr
        intro z hzi hzj
        obtain ⟨_, hip, hjq⟩ := hcross i (j - (p.points.length - 1))
          (by omega) (by omega) z hzi hzj
        omega

/-- Helper toward Proposition 5.16: three simple chains concatenate simply
when successive pieces meet only at their joins and the end pieces are disjoint. -/
theorem isSimple_three_boundaryConcat (p q r : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple) (hr : r.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hlenr : 2 ≤ r.points.length)
    (hpq : p.finish = q.start) (hqr : q.finish = r.start)
    (hintpq : p.image ∩ q.image = {p.finish})
    (hintqr : q.image ∩ r.image = {q.finish})
    (hdisj : Disjoint p.image r.image) :
    (boundaryConcat (boundaryConcat p q) r).IsSimple := by
  apply isSimple_boundaryConcat _ _
    (isSimple_boundaryConcat p q hp hq hlenp hlenq hpq hintpq) hr
    (by rw [length_boundaryConcat]; omega) hlenr
    (by rw [finish_boundaryConcat_of_join _ _ hpq]; exact hqr)
  rw [image_boundaryConcat _ _ hpq, finish_boundaryConcat_of_join _ _ hpq,
    union_inter_distrib_right, hintqr]
  have hempty : p.image ∩ r.image = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  rw [hempty, empty_union]

/-- Helper toward Proposition 5.16: the two square chains, closed against
one another, already give a cyclically simple subdivided square boundary. -/
theorem square_chains_closedConcat_isCyclicSimple (R a b : ℝ) (hR : 0 < R)
    (ha : -R < a ∧ a < R) (hb : -R < b ∧ b < R) :
    (closedConcat (squareUpperChain R a b) (squareLowerChain R a b)).IsCyclicSimple := by
  apply closedConcat_isCyclicSimple _ _
    (squareUpperChain_isSimple R a b hR ha.2 hb.2)
    (squareLowerChain_isSimple R a b hR ha.1 hb.1)
    (by change 2 ≤ 4; omega) (by change 2 ≤ 4; omega) rfl rfl
  · intro heq
    have hre := congrArg Complex.re heq
    change -R = R at hre
    linarith only [hR, hre]
  · exact square_chains_image_inter R a b hR ha hb

/-- Helper toward Proposition 5.16: a square boundary arc, preceded by
the left horizontal slit and followed by the reversed right horizontal slit,
is a simple chain with the prescribed inner endpoints and exact image. -/
theorem square_bypass_data (R : ℝ) (hR : 0 < R) (a b : ℂ)
    (ha : a ∈ (enclosingSquare R).inside) (hb : b ∈ (enclosingSquare R).inside)
    (hab : a.re < b.re) (o : Polyline) (ho : o.IsSimple)
    (holen : 2 ≤ o.points.length)
    (hostart : o.start = (⟨-R, a.im⟩ : ℂ))
    (hofinish : o.finish = (⟨R, b.im⟩ : ℂ))
    (hoimage : o.image ⊆ (enclosingSquare R).image) :
    let s := diagonalArc a (⟨-R, a.im⟩ : ℂ)
    let t := diagonalArc (⟨R, b.im⟩ : ℂ) b
    let u := boundaryConcat (boundaryConcat s o) t
    u.IsSimple ∧ 2 ≤ u.points.length ∧ u.start = a ∧ u.finish = b ∧
      u.image = (segment ℝ a (⟨-R, a.im⟩ : ℂ) ∪ o.image) ∪
        segment ℝ b (⟨R, b.im⟩ : ℂ) := by
  dsimp only
  let l : ℂ := ⟨-R, a.im⟩
  let r : ℂ := ⟨R, b.im⟩
  let s := diagonalArc a l
  let t := diagonalArc r b
  have haj : (diagonalArc a l).finish = o.start := hostart.symm
  have hbj : o.finish = (diagonalArc r b).start := hofinish
  have hsdata := diagonalArc_data a l
  have htdata := diagonalArc_data r b
  have hal := ((enclosingSquare_inside R hR).subset ha).1.1
  have hbr := ((enclosingSquare_inside R hR).subset hb).1.2
  have hs : s.IsSimple := isSimple_diagonalArc a l (by
    intro heq
    have hre := congrArg Complex.re heq
    change a.re = -R at hre
    linarith only [hal, hre])
  have ht : t.IsSimple := isSimple_diagonalArc r b (by
    intro heq
    have hre := congrArg Complex.re heq
    change R = b.re at hre
    linarith only [hbr, hre])
  have hsouter := (left_slit_inter_enclosingSquare R hR a ha).1
  have htouter := (right_slit_inter_enclosingSquare R hR b hb).1
  have hso : s.image ∩ o.image = {s.finish} := by
    rw [hsdata.2.2.2, hsdata.2.1]
    ext z
    constructor
    · intro hz
      exact hsouter ▸ ⟨hz.1, hoimage hz.2⟩
    · rintro rfl
      refine ⟨right_mem_segment ℝ _ _, ?_⟩
      change (⟨-R, a.im⟩ : ℂ) ∈ o.image
      rw [← hostart]
      exact Or.inl rfl
  have hot : o.image ∩ t.image = {o.finish} := by
    rw [htdata.2.2.2, segment_symm, hofinish]
    ext z
    constructor
    · intro hz
      exact htouter ▸ ⟨hz.2, hoimage hz.1⟩
    · rintro rfl
      constructor
      · rw [← hofinish, ← point_last_eq_finish]
        exact o.point_mem_image (by omega)
      · exact right_mem_segment ℝ _ _
  have hst : Disjoint s.image t.image := by
    rw [hsdata.2.2.2, htdata.2.2.2, segment_symm ℝ r b]
    apply Set.disjoint_left.mpr
    intro z hzs hzt
    have hzsa : z.re ≤ a.re := by
      by_cases heq : z = a
      · exact heq ▸ le_rfl
      · exact (segment_re_lt_of_ne_left a l hal hzs heq).le
    have hztb : b.re ≤ z.re := by
      by_cases heq : z = b
      · exact heq ▸ le_rfl
      · exact (segment_re_gt_of_ne_left b r hbr hzt heq).le
    exact (not_le_of_gt hab) (hztb.trans hzsa)
  have hjoined : (boundaryConcat s o).finish = t.start := by
    rw [finish_boundaryConcat_of_join _ _ haj]
    exact hbj
  refine ⟨isSimple_three_boundaryConcat s o t hs ho ht (by change 2 ≤ 2; omega)
    holen (by change 2 ≤ 2; omega) haj hbj hso hot hst, ?_, ?_, ?_, ?_⟩
  · rw [length_boundaryConcat, length_boundaryConcat]
    change 2 ≤ 2 + o.points.length - 1 + 2 - 1
    omega
  · rw [start_boundaryConcat, start_boundaryConcat]; rfl
  · rw [finish_boundaryConcat_of_join _ _ hjoined]; rfl
  · rw [image_boundaryConcat _ _ hjoined, image_boundaryConcat _ _ haj,
      hsdata.2.2.2, htdata.2.2.2, segment_symm ℝ r b]

/-- Helper toward Proposition 5.16: the closed inside of the square is
exactly the closed coordinate square. -/
theorem enclosingSquare_closure_inside (R : ℝ) (hR : 0 < R) :
    closure (enclosingSquare R).inside =
      {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} := by
  rw [closure_inside_eq_union_image _ (enclosingSquare_isCyclicSimple R hR)]
  ext z
  rw [mem_union, enclosingSquare_inside R hR, mem_enclosingSquare_image_iff R hR]
  constructor
  · rintro (hz | hz)
    · exact ⟨abs_le.mpr ⟨hz.1.1.le, hz.1.2.le⟩,
        abs_le.mpr ⟨hz.2.1.le, hz.2.2.le⟩⟩
    · exact ⟨abs_le.mpr hz.1, abs_le.mpr hz.2.1⟩
  · intro hz
    have hre := abs_le.mp hz.1
    have him := abs_le.mp hz.2
    by_cases hs : z.re = -R ∨ z.re = R ∨ z.im = -R ∨ z.im = R
    · exact Or.inr ⟨hre, him, hs⟩
    · left
      push Not at hs
      exact ⟨⟨lt_of_le_of_ne hre.1 (Ne.symm hs.1), lt_of_le_of_ne hre.2 hs.2.1⟩,
        ⟨lt_of_le_of_ne him.1 (Ne.symm hs.2.2.1), lt_of_le_of_ne him.2 hs.2.2.2⟩⟩

/-- Helper toward Proposition 5.16: the two slits and the two pairs of
boundary arcs give cyclically simple cut polygons with the exact combined
boundary image. This does not yet identify their closed inside regions. -/
theorem exists_annulus_boundary_polygons (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ (R : ℝ) (s t p q : Polyline), 0 < R ∧
      (enclosingSquare R).IsCyclicSimple ∧
      closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ Disjoint s.image t.image ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      p.image ∪ q.image =
        (c.image ∪ (enclosingSquare R).image) ∪ (s.image ∪ t.image) ∧
      p.image ∩ q.image = s.image ∪ t.image ∧
      p.inside ⊆ (enclosingSquare R).inside ∧ q.inside ⊆ (enclosingSquare R).inside := by
  obtain ⟨R, i, j, hR, hi, hj, hbox, hdata⟩ :=
    c.exists_disjoint_horizontal_exterior_slits hc
  dsimp only at hdata
  obtain ⟨hab, haim, hbim, hs, ht, hsinter, htinter, hdisj, hcontain⟩ := hdata
  let a := c.point i
  let b := c.point j
  let l : ℂ := ⟨-R, a.im⟩
  let r : ℂ := ⟨R, b.im⟩
  let s := diagonalArc a l
  let t := diagonalArc b r
  have hnest : closure c.inside ⊆ (enclosingSquare R).inside := by
    intro z hz
    rw [enclosingSquare_inside R hR]
    exact ⟨abs_lt.mp (hbox z hz).1, abs_lt.mp (hbox z hz).2⟩
  have ha : a ∈ (enclosingSquare R).inside :=
    hnest (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hi))
  have hb : b ∈ (enclosingSquare R).inside :=
    hnest (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hj))
  have hne : a ≠ b := fun h => (ne_of_lt hab) (congrArg Complex.re h)
  let u := squareUpperChain R a.im b.im
  let v := squareLowerChain R a.im b.im
  have huq : u.image ⊆ (enclosingSquare R).image := by
    rw [← square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)]
    exact subset_union_left
  have hvq : v.image ⊆ (enclosingSquare R).image := by
    rw [← square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)]
    exact subset_union_right
  let U := boundaryConcat (boundaryConcat s u) (diagonalArc r b)
  let V := boundaryConcat (boundaryConcat s v) (diagonalArc r b)
  obtain ⟨hU, hUlen, hUstart, hUfinish, hUimage⟩ :=
    square_bypass_data R hR a b ha hb hab u
      (squareUpperChain_isSimple R a.im b.im hR (abs_lt.mp haim).2 (abs_lt.mp hbim).2)
      (by change 2 ≤ 4; omega) rfl rfl huq
  obtain ⟨hV, hVlen, hVstart, hVfinish, hVimage⟩ :=
    square_bypass_data R hR a b ha hb hab v
      (squareLowerChain_isSimple R a.im b.im hR (abs_lt.mp haim).1 (abs_lt.mp hbim).1)
      (by change 2 ≤ 4; omega) rfl rfl hvq
  obtain ⟨x, y, hx, hy, hxlen, hylen, hxstart, hxfinish, hystart, hyfinish,
    hxyunion, hxyinter, _⟩ := c.exists_inner_boundary_chains hc i j hi hj hne
  have havoid (o : Polyline) (hoq : o.image ⊆ (enclosingSquare R).image) :
      o.image ∩ c.image = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hzo, hzc⟩
    exact (hnest (c.image_subset_closure_inside_cyclic hc hzc)).1 (hoq hzo)
  have hcontact (o : Polyline) (hoq : o.image ⊆ (enclosingSquare R).image) :
      ((segment ℝ a l ∪ o.image) ∪ segment ℝ b r) ∩ c.image = {a, b} := by
    rw [union_inter_distrib_right, union_inter_distrib_right,
      ← (diagonalArc_data a l).2.2.2, ← (diagonalArc_data b r).2.2.2,
      hsinter, htinter, havoid o hoq, union_empty]
    rfl
  have hUc : U.image ∩ c.image = {a, b} := by
    rw [hUimage]
    exact hcontact u huq
  have hVc : V.image ∩ c.image = {a, b} := by
    rw [hVimage]
    exact hcontact v hvq
  have hxsub : x.image ⊆ c.image := by rw [← hxyunion]; exact subset_union_left
  have hysub : y.image ⊆ c.image := by rw [← hxyunion]; exact subset_union_right
  have hinter (w W : Polyline) (hwlen : 2 ≤ w.points.length)
      (hws : w.start = a) (hwf : w.finish = b) (hwsub : w.image ⊆ c.image)
      (hWlen : 2 ≤ W.points.length) (hWs : W.start = a) (hWf : W.finish = b)
      (hWc : W.image ∩ c.image = {a, b}) : w.image ∩ W.image = {w.start, w.finish} := by
    rw [hws, hwf]
    apply Set.Subset.antisymm
    · rintro z ⟨hzw, hzW⟩
      exact hWc ▸ ⟨hzW, hwsub hzw⟩
    · rintro z (rfl | rfl)
      · exact ⟨by rw [← hws]; exact Or.inl rfl, by rw [← hWs]; exact Or.inl rfl⟩
      · constructor
        · rw [← hwf, ← point_last_eq_finish]; exact w.point_mem_image (by omega)
        · rw [← hWf, ← point_last_eq_finish]; exact W.point_mem_image (by omega)
  have hyrevlen : 2 ≤ y.reverse.points.length := by simpa only [reverse, List.length_reverse] using hylen
  have hyrs : y.reverse.start = a := (start_reverse y).trans hyfinish
  have hyrf : y.reverse.finish = b := (finish_reverse y).trans hystart
  have hyrsub : y.reverse.image ⊆ c.image := by rw [image_reverse_transfer]; exact hysub
  have hp : (closedConcat x U).IsCyclicSimple := closedConcat_isCyclicSimple x U hx hU
    hxlen hUlen (hxstart.trans hUstart.symm) (hxfinish.trans hUfinish.symm)
    (by rw [hxstart, hxfinish]; exact hne)
    (hinter x U hxlen hxstart hxfinish hxsub hUlen hUstart hUfinish hUc)
  have hq : (closedConcat y.reverse V).IsCyclicSimple := closedConcat_isCyclicSimple
    y.reverse V (isSimple_reverse_transfer y hy) hV hyrevlen hVlen
    (hyrs.trans hVstart.symm) (hyrf.trans hVfinish.symm)
    (by rw [hyrs, hyrf]; exact hne)
    (hinter y.reverse V hyrevlen hyrs hyrf hyrsub hVlen hVstart hVfinish hVc)
  refine ⟨R, s, t, closedConcat x U, closedConcat y.reverse V, hR,
    enclosingSquare_isCyclicSimple R hR, hnest, hs, ht, hdisj,
    hsinter, htinter, ?_, ?_, hp, hq, ?_, ?_, ?_, ?_⟩
  · rw [(diagonalArc_data a l).2.2.2]
    exact (left_slit_inter_enclosingSquare R hR a ha).1
  · rw [(diagonalArc_data b r).2.2.2]
    exact (right_slit_inter_enclosingSquare R hR b hb).1
  · rw [image_closedConcat x U (hxfinish.trans hUfinish.symm),
      image_closedConcat y.reverse V (hyrf.trans hVfinish.symm), image_reverse_transfer,
      hUimage, hVimage, (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
    have huv : u.image ∪ v.image = (enclosingSquare R).image :=
      square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)
    rw [← hxyunion, ← huv]
    ext z
    simp only [mem_union]
    tauto
  · rw [image_closedConcat x U (hxfinish.trans hUfinish.symm),
      image_closedConcat y.reverse V (hyrf.trans hVfinish.symm), image_reverse_transfer,
      hUimage, hVimage, (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
    apply Set.Subset.antisymm
    · rintro z ⟨hzp, hzq⟩
      by_cases hzs : z ∈ segment ℝ a l
      · exact Or.inl hzs
      by_cases hzt : z ∈ segment ℝ b r
      · exact Or.inr hzt
      have hxp : z ∈ x.image ∨ z ∈ u.image := by
        rcases hzp with hz | (hz | hz) | hz
        · exact Or.inl hz
        · exact False.elim (hzs hz)
        · exact Or.inr hz
        · exact False.elim (hzt hz)
      have hyq : z ∈ y.image ∨ z ∈ v.image := by
        rcases hzq with hz | (hz | hz) | hz
        · exact Or.inl hz
        · exact False.elim (hzs hz)
        · exact Or.inr hz
        · exact False.elim (hzt hz)
      rcases hxp with hzx | hzu <;> rcases hyq with hzy | hzv
      · have hz : z ∈ ({a, b} : Set ℂ) := hxyinter ▸ ⟨hzx, hzy⟩
        rcases hz with rfl | rfl
        · exact Or.inl (left_mem_segment ℝ _ _)
        · exact Or.inr (left_mem_segment ℝ _ _)
      · exact False.elim (by
          have hz : z ∈ (∅ : Set ℂ) := havoid v hvq ▸ ⟨hzv, hxsub hzx⟩
          exact hz)
      · exact False.elim (by
          have hz : z ∈ (∅ : Set ℂ) := havoid u huq ▸ ⟨hzu, hysub hzy⟩
          exact hz)
      · have hz : z ∈ ({l, r} : Set ℂ) :=
          square_chains_image_inter R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim) ▸
            ⟨hzu, hzv⟩
        rcases hz with rfl | rfl
        · exact Or.inl (right_mem_segment ℝ _ _)
        · exact Or.inr (right_mem_segment ℝ _ _)
    · rintro z (hzs | hzt)
      · exact ⟨Or.inr (Or.inl (Or.inl hzs)), Or.inr (Or.inl (Or.inl hzs))⟩
      · exact ⟨Or.inr (Or.inr hzt), Or.inr (Or.inr hzt)⟩
  all_goals
    apply inside_subset_inside_of_image_subset_closure (enclosingSquare R)
      (enclosingSquare_isCyclicSimple R hR)
  · exact closed_closedConcat x U (hxstart.trans hUstart.symm) hUlen
  · rw [image_closedConcat x U (hxfinish.trans hUfinish.symm), hUimage]
    rintro z (hzx | (hzs | hzu) | hzt)
    · exact subset_closure (hnest (c.image_subset_closure_inside_cyclic hc (hxsub hzx)))
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inl ((diagonalArc_data a l).2.2.2.symm ▸ hzs))).2
    · exact (enclosingSquare R).image_subset_closure_inside_cyclic
        (enclosingSquare_isCyclicSimple R hR) (huq hzu)
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inr ((diagonalArc_data b r).2.2.2.symm ▸ hzt))).2
  · exact closed_closedConcat y.reverse V (hyrs.trans hVstart.symm) hVlen
  · rw [image_closedConcat y.reverse V (hyrf.trans hVfinish.symm),
      image_reverse_transfer, hVimage]
    rintro z (hzy | (hzs | hzv) | hzt)
    · exact subset_closure (hnest (c.image_subset_closure_inside_cyclic hc (hysub hzy)))
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inl ((diagonalArc_data a l).2.2.2.symm ▸ hzs))).2
    · exact (enclosingSquare R).image_subset_closure_inside_cyclic
        (enclosingSquare_isCyclicSimple R hR) (hvq hzv)
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inr ((diagonalArc_data b r).2.2.2.symm ▸ hzt))).2

/-- Helper toward Proposition 5.16: subtracting the two square bypass
angle sums cancels both slits exactly, without any simplicity or viewpoint
restriction. -/
theorem angleSum_square_bypass_sub (R : ℝ) (a b z : ℂ) :
    let s := diagonalArc a (⟨-R, a.im⟩ : ℂ)
    let t := diagonalArc (⟨R, b.im⟩ : ℂ) b
    (boundaryConcat (boundaryConcat s (squareUpperChain R a.im b.im)) t).angleSum z -
      (boundaryConcat (boundaryConcat s (squareLowerChain R a.im b.im)) t).angleSum z =
        (squareUpperChain R a.im b.im).angleSum z -
          (squareLowerChain R a.im b.im).angleSum z := by
  dsimp only
  have hupper :
      (boundaryConcat (diagonalArc a (⟨-R, a.im⟩ : ℂ))
        (squareUpperChain R a.im b.im)).finish = (⟨R, b.im⟩ : ℂ) := by
    rw [finish_boundaryConcat_of_join _ _ (by rfl)]
    rfl
  have hlower :
      (boundaryConcat (diagonalArc a (⟨-R, a.im⟩ : ℂ))
        (squareLowerChain R a.im b.im)).finish = (⟨R, b.im⟩ : ℂ) := by
    rw [finish_boundaryConcat_of_join _ _ (by rfl)]
    rfl
  rw [angleSum_boundaryConcat
      (boundaryConcat (diagonalArc a (⟨-R, a.im⟩ : ℂ)) (squareUpperChain R a.im b.im))
      (diagonalArc (⟨R, b.im⟩ : ℂ) b) hupper z,
    angleSum_boundaryConcat
      (boundaryConcat (diagonalArc a (⟨-R, a.im⟩ : ℂ)) (squareLowerChain R a.im b.im))
      (diagonalArc (⟨R, b.im⟩ : ℂ) b) hlower z,
    angleSum_boundaryConcat (diagonalArc a (⟨-R, a.im⟩ : ℂ))
      (squareUpperChain R a.im b.im) (by rfl) z,
    angleSum_boundaryConcat (diagonalArc a (⟨-R, a.im⟩ : ℂ))
      (squareLowerChain R a.im b.im) (by rfl) z]
  ring

/-- Helper toward Proposition 5.16: reversing a segment negates its
principal angle when the viewpoint avoids the chain. -/
theorem edgeAngle_reverse (p : Polyline) (z : ℂ) (hz : z ∉ p.image)
    (i : ℕ) (hi : i + 1 < p.points.length) :
    p.reverse.edgeAngle z i = -p.edgeAngle z (p.points.length - 2 - i) := by
  have hidx : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
  have hidx' : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
  rw [edgeAngle, point_reverse_transfer p hi,
    point_reverse_transfer p (by omega), hidx, hidx']
  rw [show (p.point (p.points.length - 2 - i) - z) /
      (p.point (p.points.length - 2 - i + 1) - z) =
      ((p.point (p.points.length - 2 - i + 1) - z) /
        (p.point (p.points.length - 2 - i) - z))⁻¹ by rw [inv_div]]
  rw [Complex.arg_inv, ite_eq_right]
  · rfl
  · exact ne_of_lt (p.edgeAngle_mem_Ioo z _ (by omega) hz).2

/-- Helper toward Proposition 5.16: reversing a whole chain negates its
normalized angle sum away from its image. -/
theorem angleSum_reverse (p : Polyline) (z : ℂ) (hz : z ∉ p.image) :
    p.reverse.angleSum z = -p.angleSum z := by
  have hlen : p.reverse.points.length = p.points.length := List.length_reverse
  have hsum : (∑ i ∈ Finset.range (p.points.length - 1), p.reverse.edgeAngle z i) =
      ∑ i ∈ Finset.range (p.points.length - 1),
        -p.edgeAngle z (p.points.length - 1 - 1 - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [edgeAngle_reverse p z hz i (by omega)]
    congr 2
  rw [Finset.sum_neg_distrib, Finset.sum_range_reflect] at hsum
  rw [angleSum, hlen, hsum, neg_div]
  rfl

/-- Helper toward Proposition 5.16: the winding of an endpoint-glued loop
is the first chain's angle sum minus the second chain's angle sum. -/
theorem angleSum_closedConcat (p q : Polyline) (hfinish : p.finish = q.finish)
    (z : ℂ) (hz : z ∉ q.image) :
    (closedConcat p q).angleSum z = p.angleSum z - q.angleSum z := by
  change (boundaryConcat p q.reverse).angleSum z = _
  rw [angleSum_boundaryConcat p q.reverse (by rw [start_reverse]; exact hfinish),
    angleSum_reverse q z hz, sub_eq_add_neg]

/-- Helper toward Proposition 5.16: exact winding cancellation for the
two inner arcs and square bypasses. The remaining outer-chain difference
has not been identified here with the oriented winding of the square. -/
theorem angleSum_annulus_chains (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) (R : ℝ) :
    let a := c.point i
    let b := c.point j
    let s := diagonalArc a (⟨-R, a.im⟩ : ℂ)
    let t := diagonalArc (⟨R, b.im⟩ : ℂ) b
    let U := boundaryConcat (boundaryConcat s (squareUpperChain R a.im b.im)) t
    let V := boundaryConcat (boundaryConcat s (squareLowerChain R a.im b.im)) t
    ∀ (z : ℂ), z ∉ c.image ∪ (U.image ∪ V.image) →
      (closedConcat V (c.intervalPolyline i (j - i))).angleSum z +
        (closedConcat (c.diagonalComplement i j).reverse U).angleSum z =
          (squareLowerChain R a.im b.im).angleSum z -
            (squareUpperChain R a.im b.im).angleSum z - c.angleSum z := by
  dsimp only
  intro z hz
  let a := c.point i
  let b := c.point j
  let s := diagonalArc a (⟨-R, a.im⟩ : ℂ)
  let t := diagonalArc (⟨R, b.im⟩ : ℂ) b
  let U := boundaryConcat (boundaryConcat s (squareUpperChain R a.im b.im)) t
  let V := boundaryConcat (boundaryConcat s (squareLowerChain R a.im b.im)) t
  have hUf : U.finish = b := by
    rw [finish_boundaryConcat _ _ (by change 2 ≤ 2; omega)]
    rfl
  have hVf : V.finish = b := by
    rw [finish_boundaryConcat _ _ (by change 2 ≤ 2; omega)]
    rfl
  have hxf : (c.intervalPolyline i (j - i)).finish = b := by
    rw [finish_intervalPolyline, show i + (j - i) = j by omega]
  have hyf : (c.diagonalComplement i j).reverse.finish = b := by
    rw [finish_reverse, (c.diagonalComplement_data hc i j hij hj).1]
  have hzx : z ∉ (c.intervalPolyline i (j - i)).image :=
    fun h => hz (Or.inl (c.image_intervalPolyline_subset i (j - i) (by omega) h))
  have hzy : z ∉ (c.diagonalComplement i j).image :=
    fun h => hz (Or.inl ((c.diagonalComplement_data hc i j hij hj).2.2 h))
  have hzU : z ∉ U.image := fun h => hz (Or.inr (Or.inl h))
  rw [angleSum_closedConcat V _ (hVf.trans hxf.symm) z hzx,
    angleSum_closedConcat _ U (hyf.trans hUf.symm) z hzU,
    angleSum_reverse _ z hzy]
  have harcs := c.angleSum_diagonal_arcs hc i j hij hj z
  have hcancel := angleSum_square_bypass_sub R a b z
  change U.angleSum z - V.angleSum z = _ at hcancel
  linarith only [harcs, hcancel]












































































end Polyline
end DirectedDistances.PlanarMap

