/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLRegularNeighborhood2

/-! # Segment level separation toward Proposition 5.16

Helper toward Proposition 5.16: bend isolation and trimmed straight segments
for a finite piecewise linear drawing. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Metric Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: the finite type of segment identities in
a finite dart drawing. -/
abbrev SegmentIndex := Σ d : D, Fin ((P.arc d).points.length - 1)

/-- Helper toward Proposition 5.16: the special points are all vertex positions
and all interior bends of all dart arcs. -/
def specialPoints : Set ℂ :=
  Set.range P.pos ∪ {z | ∃ d i, 0 < i ∧ i + 1 < (P.arc d).points.length ∧
    z = (P.arc d).point i}

/-- Helper toward Proposition 5.16: the union of open neighborhoods of the
special points, used to trim straight segments away from their endpoints. -/
def specialPointBalls (rho : ℝ) : Set ℂ :=
  ⋃ z : {z // z ∈ P.specialPoints}, Metric.ball z.1 (rho / 2)

/-- Helper toward Proposition 5.16: a straight drawing segment with the open
`rho / 2` neighborhoods of all special points removed. -/
def trimmedSegment (rho : ℝ) (d : D) (i : ℕ) : Set ℂ :=
  (P.arc d).segmentAt i ∩ (P.specialPointBalls rho)ᶜ

/-- Helper toward Proposition 5.16: the trimmed segment selected by a segment
identity. -/
def trimmedSegmentAt (rho : ℝ) (a : P.SegmentIndex) : Set ℂ :=
  P.trimmedSegment rho a.1 a.2.val

/-- Helper toward Proposition 5.16: two segment identities denote the same
geometric segment if they agree on a dart and index, or reverse a dart and its
corresponding segment index. -/
def same_geometric_segment (a b : P.SegmentIndex) : Prop :=
  (a.1 = b.1 ∧ a.2.val = b.2.val) ∨
    (b.1 = flip a.1 ∧
      b.2.val = (P.arc a.1).points.length - 2 - a.2.val)

/-- Helper toward Proposition 5.16: every segment identity has a valid arc
segment index. -/
theorem segmentIndex_valid (a : P.SegmentIndex) :
    a.2.val + 1 < (P.arc a.1).points.length := by
  have := P.arc_length a.1
  omega

/-- Helper toward Proposition 5.16: each straight segment of an arc is compact. -/
theorem isCompact_segmentAt (d : D) (i : ℕ) :
    IsCompact ((P.arc d).segmentAt i) := by
  rw [Polyline.segmentAt, ← convexHull_pair]
  exact ((finite_singleton ((P.arc d).point (i + 1))).insert
    ((P.arc d).point i)).isCompact_convexHull ℝ

/-- Helper toward Proposition 5.16: each trimmed straight segment is compact. -/
theorem isCompact_trimmedSegment (rho : ℝ) (d : D) (i : ℕ) :
    IsCompact (P.trimmedSegment rho d i) := by
  apply (P.isCompact_segmentAt d i).inter_right
  apply isClosed_compl_iff.mpr
  apply isOpen_iUnion
  intro z
  exact Metric.isOpen_ball

/-- Helper toward Proposition 5.16: no special point belongs to a trimmed
segment when the trimming radius is positive. -/
theorem specialPoint_not_mem_trimmedSegment (rho : ℝ) (hrho : 0 < rho)
    (d : D) (i : ℕ) {z : ℂ} (hz : z ∈ P.specialPoints) :
    z ∉ P.trimmedSegment rho d i := by
  intro hztrim
  have hzball : z ∈ Metric.ball z (rho / 2) := by
    simp only [Metric.mem_ball, dist_self]
    linarith
  have hzunion : z ∈ P.specialPointBalls rho := by
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hzball⟩
  exact hztrim.2 hzunion

/-- Helper toward Proposition 5.16: two disjoint compact subsets of the plane
have a positive uniform distance. -/
theorem exists_pos_separation_of_compact_disjoint {s t : Set ℂ}
    (hs : IsCompact s) (ht : IsCompact t) (hdisj : Disjoint s t) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ s, ∀ y ∈ t, 2 * eps < dist x y := by
  let Q : Set (ℂ × ℂ) := s ×ˢ t
  have hcompact : IsCompact Q := hs.prod ht
  have hdiag : Disjoint Q (Set.diagonal ℂ) := by
    apply Set.disjoint_left.mpr
    rintro ⟨x, y⟩ hxy hxy'
    have hsame : x = y := by simpa only [Set.mem_diagonal_iff] using hxy'
    have hx : x ∈ s := hxy.1
    have hy : x ∈ t := hsame ▸ hxy.2
    exact (Set.disjoint_left.mp hdisj) hx hy
  obtain ⟨δ, hδ, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hcompact isClosed_diagonal hdiag
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  refine ⟨(δ : ℝ) / 3, by positivity, ?_⟩
  intro x hx y hy
  have hprod : (x, y) ∈ Q := ⟨hx, hy⟩
  have hdiagx : (x, x) ∈ Set.diagonal ℂ := by simp
  have hed := hsep (x, y) hprod (x, x) hdiagx
  have hed' : (δ : ENNReal) < edist x y := by
    simpa [Prod.edist_eq, edist_comm] using hed
  have hdist : (δ : ℝ) < dist x y := by
    have hnnd : δ < nndist x y :=
      ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using hed')
    exact_mod_cast hnnd
  nlinarith

/-- Helper toward Proposition 5.16: every endpoint of a valid dart segment
is either a vertex position or an interior bend. -/
theorem point_special (d : D) (i : ℕ) (hi : i < (P.arc d).points.length) :
    (P.arc d).point i ∈ P.specialPoints := by
  by_cases hi0 : i = 0
  · left
    rw [hi0, Polyline.point_zero_eq_start, P.arc_start]
    exact ⟨vert d, rfl⟩
  by_cases hiLast : i + 1 = (P.arc d).points.length
  · left
    rw [show i = (P.arc d).points.length - 1 by omega,
      Polyline.point_last_eq_finish, P.arc_finish]
    exact ⟨vert (flip d), rfl⟩
  · right
    exact ⟨d, i, Nat.pos_of_ne_zero hi0, by omega, rfl⟩

/-- Helper toward Proposition 5.16: trimming at special points separates
distinct segments belonging to one simple dart arc. -/
theorem disjoint_trimmedSegments_same_arc (rho : ℝ) (hrho : 0 < rho)
    (d : D) (i j : ℕ) (hi : i + 1 < (P.arc d).points.length)
    (hj : j + 1 < (P.arc d).points.length) (hne : i ≠ j) :
    Disjoint (P.trimmedSegment rho d i) (P.trimmedSegment rho d j) := by
  apply Set.disjoint_left.mpr
  intro z hzI hzJ
  obtain ⟨hiend, hjend⟩ := (P.arc d).segmentAt_intersection_endpoints
    (P.arc_simple d) i j hi hj hne hzI.1 hzJ.1
  have hspecial : z ∈ P.specialPoints := by
    rcases hiend with h | h
    · rw [h]
      exact P.point_special d i (by omega)
    · rw [h]
      exact P.point_special d (i + 1) (by omega)
  exact (P.specialPoint_not_mem_trimmedSegment rho hrho d j hspecial) hzJ

/-- Helper toward Proposition 5.16: trimming at special points separates
segments belonging to different unoriented dart edges. -/
theorem disjoint_trimmedSegments_nonincident_darts (rho : ℝ) (hrho : 0 < rho)
    (d e : D) (hne : e ≠ d) (hflip : e ≠ flip d) (i j : ℕ)
    (hi : i + 1 < (P.arc d).points.length)
    (hj : j + 1 < (P.arc e).points.length) :
    Disjoint (P.trimmedSegment rho d i) (P.trimmedSegment rho e j) := by
  apply Set.disjoint_left.mpr
  intro z hzI hzJ
  obtain ⟨hiend, hend⟩ := P.arc_segment_intersection_endpoints d e hne hflip i j
    hi hj hzI.1 hzJ.1
  have hspecial : z ∈ P.specialPoints := by
    rcases hiend with h | h
    · rw [h]
      exact P.point_special d i (by omega)
    · rw [h]
      exact P.point_special d (i + 1) (by omega)
  exact (P.specialPoint_not_mem_trimmedSegment rho hrho e j hspecial) hzJ

/-- Helper toward Proposition 5.16: trimming separates distinct segments of
the same geometric edge when one is indexed on the reversed dart. -/
theorem disjoint_trimmedSegments_reverse_dart (rho : ℝ) (hrho : 0 < rho)
    (d : D) (i j : ℕ) (hi : i + 1 < (P.arc d).points.length)
    (hj : j + 1 < (P.arc (flip d)).points.length)
    (hne : i ≠ (P.arc d).points.length - 2 - j) :
    Disjoint (P.trimmedSegment rho d i) (P.trimmedSegment rho (flip d) j) := by
  have hjd : j + 1 < (P.arc d).points.length := by
    simpa only [P.arc_flip, Polyline.reverse, List.length_reverse] using hj
  let j' := (P.arc d).points.length - 2 - j
  apply Set.disjoint_left.mpr
  intro z hzI hzJ
  have hzseg : z ∈ (P.arc d).segmentAt j' := by
    have hzrev : z ∈ (P.arc d).reverse.segmentAt j := by
      simpa only [P.arc_flip] using hzJ.1
    rw [Polyline.segmentAt_reverse_transfer (P.arc d) hjd] at hzrev
    exact hzrev
  obtain ⟨hiend, _⟩ := (P.arc d).segmentAt_intersection_endpoints
    (P.arc_simple d) i j' hi (by dsimp [j']; omega) hne hzI.1 hzseg
  have hspecial : z ∈ P.specialPoints := by
    rcases hiend with h | h
    · rw [h]
      exact P.point_special d i (by omega)
    · rw [h]
      exact P.point_special d (i + 1) (by omega)
  exact (P.specialPoint_not_mem_trimmedSegment rho hrho (flip d) j hspecial) hzJ

/-- Helper toward Proposition 5.16: for positive trimming radius, any two
distinct geometric segments have disjoint trimmed parts. -/
theorem disjoint_trimmedSegmentAt_of_not_same (rho : ℝ) (hrho : 0 < rho)
    (a b : P.SegmentIndex) (hne : ¬ P.same_geometric_segment a b) :
    Disjoint (P.trimmedSegmentAt rho a) (P.trimmedSegmentAt rho b) := by
  obtain ⟨d, i⟩ := a
  obtain ⟨e, j⟩ := b
  let i' := i.val
  let j' := j.val
  have hi : i' + 1 < (P.arc d).points.length := by
    have hlen := P.arc_length d
    have h := i.isLt
    dsimp [i']
    omega
  have hj : j' + 1 < (P.arc e).points.length := by
    have hlen := P.arc_length e
    have h := j.isLt
    dsimp [j']
    omega
  change ¬ ((d = e ∧ i' = j') ∨
    (e = flip d ∧ j' = (P.arc d).points.length - 2 - i')) at hne
  by_cases hde : e = d
  · subst e
    by_cases hij : i' = j'
    · exact (hne (Or.inl ⟨rfl, hij⟩)).elim
    · exact P.disjoint_trimmedSegments_same_arc rho hrho d i' j' hi hj hij
  · by_cases hflip : e = flip d
    · subst e
      have hrev : j' ≠ (P.arc d).points.length - 2 - i' := by
        intro hji
        exact hne (Or.inr ⟨rfl, hji⟩)
      have hjrev : j' + 1 < (P.arc d).points.length := by
        simpa only [P.arc_flip, Polyline.reverse, List.length_reverse] using hj
      have hne' : i' ≠ (P.arc d).points.length - 2 - j' := by
        intro h
        apply hrev
        have hlen := P.arc_length d
        omega
      exact P.disjoint_trimmedSegments_reverse_dart rho hrho d i' j' hi hj hne'
    · exact P.disjoint_trimmedSegments_nonincident_darts rho hrho d e hde hflip
        i' j' hi hj

/-- Helper toward Proposition 5.16: compactness and disjointness give one
positive separation for all distinct geometric segments of a finite drawing. -/
theorem exists_uniform_trimmed_segment_separation [Finite D] (rho : ℝ)
    (hrho : 0 < rho) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ a b : P.SegmentIndex,
      ¬ P.same_geometric_segment a b →
      ∀ x ∈ P.trimmedSegmentAt rho a, ∀ y ∈ P.trimmedSegmentAt rho b,
        2 * eps < dist x y := by
  classical
  let I := {p : P.SegmentIndex × P.SegmentIndex //
    ¬ P.same_geometric_segment p.1 p.2}
  let Q : Set (ℂ × ℂ) := ⋃ p : I,
    P.trimmedSegmentAt rho p.1.1 ×ˢ P.trimmedSegmentAt rho p.1.2
  have hcompact : IsCompact Q := by
    dsimp [Q]
    exact isCompact_iUnion fun p =>
      (P.isCompact_trimmedSegment rho p.1.1.1 p.1.1.2.val).prod
        (P.isCompact_trimmedSegment rho p.1.2.1 p.1.2.2.val)
  have hdisj : Disjoint Q (Set.diagonal ℂ) := by
    apply Set.disjoint_left.mpr
    rintro ⟨x, y⟩ hxy hdiag
    rw [Set.mem_iUnion] at hxy
    obtain ⟨p, hp⟩ := hxy
    have hsame : x = y := by simpa only [Set.mem_diagonal_iff] using hdiag
    have hy : x ∈ P.trimmedSegmentAt rho p.1.2 := hsame ▸ hp.2
    exact (Set.disjoint_left.mp
      (P.disjoint_trimmedSegmentAt_of_not_same rho hrho p.1.1 p.1.2 p.2)) hp.1 hy
  obtain ⟨δ, hδ, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hcompact isClosed_diagonal hdisj
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  refine ⟨(δ : ℝ) / 3, by positivity, ?_⟩
  intro a b hab x hx y hy
  let p : I := ⟨(a, b), hab⟩
  have hprod : (x, y) ∈ Q := by
    dsimp [Q]
    exact mem_iUnion.mpr ⟨p, ⟨hx, hy⟩⟩
  have hdiagx : (x, x) ∈ Set.diagonal ℂ := by simp
  have hed := hsep (x, y) hprod (x, x) hdiagx
  have hed' : (δ : ENNReal) < edist x y := by
    simpa [Prod.edist_eq, edist_comm] using hed
  have hdist : (δ : ℝ) < dist x y := by
    have hnnd : δ < nndist x y :=
      ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using hed')
    exact_mod_cast hnnd
  nlinarith













































































/-- Helper toward Proposition 5.16: a simple polyline has no repeated points
at distinct indices in its vertex list. -/
theorem point_injective_of_isSimple (p : Polyline) (hp : p.IsSimple)
    {i j : ℕ} (hi : i < p.points.length) (hj : j < p.points.length)
    (hij : i ≠ j) : p.point i ≠ p.point j := by
  have hordered : ∀ a b, a < p.points.length → b < p.points.length → a < b →
      p.point a ≠ p.point b := by
    intro a b ha hb hab heq
    by_cases hsucc : b = a + 1
    · subst b
      exact hp.1 a (by omega) heq
    by_cases hadj : b = a + 2
    · subst b
      have hmem : p.point a ∈ p.segmentAt a ∩ p.segmentAt (a + 1) := by
        refine ⟨left_mem_segment ℝ _ _, ?_⟩
        rw [heq]
        exact right_mem_segment ℝ _ _
      rw [hp.2.1 a (by omega)] at hmem
      have hmid : p.point a = p.point (a + 1) := by simpa using hmem
      exact hp.1 a (by omega) hmid
    · have hdisj := hp.2.2 a (b - 1) (by omega) (by omega) (by omega)
      have hleft : p.point a ∈ p.segmentAt a := left_mem_segment ℝ _ _
      have hright : p.point a ∈ p.segmentAt (b - 1) := by
        rw [heq]
        rw [Polyline.segmentAt, show b - 1 + 1 = b by omega]
        exact right_mem_segment ℝ _ _
      exact (Set.disjoint_left.mp hdisj) hleft hright
  intro heq
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hordered i j hi hj hlt heq
  · exact hordered j i hj hi hgt heq.symm

/-- Helper toward Proposition 5.16: an interior bend of a simple dart arc
is not any vertex position of the drawing. -/
theorem bend_not_vertex (d : D) (i : ℕ)
    (hi0 : 0 < i) (hi : i + 1 < (P.arc d).points.length) (v : V) :
    (P.arc d).point i ≠ P.pos v := by
  intro h
  have hmem : (P.arc d).point i ∈ (P.arc d).interior := by
    change (P.arc d).point i ∈ Set.diff (P.arc d).image
      {(P.arc d).start, (P.arc d).finish}
    refine ⟨(P.arc d).point_mem_image (by omega), ?_⟩
    intro hend
    rcases hend with hstart | hfinish
    ·
      have heq : (P.arc d).point i = (P.arc d).point 0 := by
        simpa only [Set.mem_singleton_iff, Polyline.point_zero_eq_start] using hstart
      exact (point_injective_of_isSimple (P.arc d) (P.arc_simple d)
        (by have := P.arc_length d; omega) (by have := P.arc_length d; omega)
        (by omega)) heq
    ·
      have hfinish' : (P.arc d).point i = (P.arc d).finish := by
        simpa only [Set.mem_singleton_iff] using hfinish
      rw [← Polyline.point_last_eq_finish] at hfinish'
      have heq : (P.arc d).point i =
          (P.arc d).point ((P.arc d).points.length - 1) := by
        exact hfinish'
      exact (point_injective_of_isSimple (P.arc d) (P.arc_simple d)
        (by have := P.arc_length d; omega) (by have := P.arc_length d; omega)
        (by omega)) heq
  exact P.interior_avoids_vertices d v (h ▸ hmem)

end PLDrawing

end DirectedDistances.PlanarMap
