/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart4
public import DirectedDistances.PlanarMap.D39BallOrbitComponents4

/-! +# Cutting a polygon along an interior diagonal

These results do not assert completion of the proposition. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline
open Set Topology

/-- Helper toward Proposition 5.16: an interior diagonal meets the original
polygon precisely at its endpoints. -/
theorem diagonal_inter_image (c : Polyline) (i j : ℕ)
    (hi : i < c.points.length) (hj : j < c.points.length)
    (hin : openSegment ℝ (c.point i) (c.point j) ⊆ c.inside) :
    segment ℝ (c.point i) (c.point j) ∩ c.image = {c.point i, c.point j} := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzseg, hzimage⟩
    by_cases hi' : z = c.point i
    · exact Or.inl hi'
    by_cases hj' : z = c.point j
    · exact Or.inr hj'
    have hzo := mem_openSegment_of_ne_left_right (Ne.symm hi') (Ne.symm hj') hzseg
    exact False.elim ((hin hzo).1 hzimage)
  · rintro z (rfl | rfl)
    · exact ⟨left_mem_segment ℝ _ _, c.point_mem_image hi⟩
    · exact ⟨right_mem_segment ℝ _ _, c.point_mem_image hj⟩

/-- Helper toward Proposition 5.16: a proper contiguous arc of a cyclically
simple polygon is a simple linear chain. -/
theorem isSimple_intervalPolyline_cyclic (c : Polyline) (hc : c.IsCyclicSimple)
    (i n : ℕ) (hbound : i + n < c.points.length)
    (hproper : n + 1 < c.points.length) : (c.intervalPolyline i n).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [length_intervalPolyline] at hk
    rw [point_intervalPolyline _ _ _ _ (by omega),
      point_intervalPolyline _ _ _ _ (by omega)]
    exact hc.2.2.1 (i + k) (by omega)
  · intro k hk
    rw [length_intervalPolyline] at hk
    rw [segmentAt_intervalPolyline _ _ _ _ (by omega),
      segmentAt_intervalPolyline _ _ _ _ (by omega),
      point_intervalPolyline _ _ _ _ (by omega)]
    simpa only [Nat.add_assoc] using hc.2.2.2.1 (i + k) (by omega)
  · intro k l hk hl hkl
    rw [length_intervalPolyline] at hk hl
    rw [segmentAt_intervalPolyline _ _ _ _ (by omega),
      segmentAt_intervalPolyline _ _ _ _ (by omega)]
    exact hc.2.2.2.2.1 (i + k) (i + l) (by omega) (by omega) (by omega) (by omega)

/-- Helper toward Proposition 5.16: the straight chain from `a` to `b`. -/
@[expose] def diagonalArc (a b : ℂ) : Polyline := ofHead a [b]

/-- Helper toward Proposition 5.16: the straight chain has its prescribed
endpoints, two vertices, and exactly the closed segment as its image. -/
theorem diagonalArc_data (a b : ℂ) :
    (diagonalArc a b).start = a ∧ (diagonalArc a b).finish = b ∧
      (diagonalArc a b).points.length = 2 ∧
      (diagonalArc a b).image = segment ℝ a b := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [diagonalArc, image_ofHead_cons]
  have hs : (ofHead b []).image = {b} := by
    ext z
    simp [image, ofHead, start]
  rw [hs]
  exact Set.union_eq_left.mpr (by rintro z rfl; exact right_mem_segment ℝ _ _)

/-- Helper toward Proposition 5.16: a nondegenerate straight chain is simple. -/
theorem isSimple_diagonalArc (a b : ℂ) (hne : a ≠ b) :
    (diagonalArc a b).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hk0 : k = 0 := by change k + 1 < 2 at hk; omega
    subst k
    exact hne
  · intro k hk
    change k + 2 < 2 at hk
    omega
  · intro k l hk hl hkl
    change k + 1 < 2 at hk
    change l + 1 < 2 at hl
    omega

/-- Helper toward Proposition 5.16: the cyclic vertices before the repeated
root are pairwise distinct. -/
theorem point_injective_before_closure (c : Polyline) (hc : c.IsCyclicSimple)
    {a b : ℕ} (ha : a < c.points.length - 1) (hb : b < c.points.length - 1)
    (heq : c.point a = c.point b) : a = b := by
  have main (a b : ℕ) (ha : a < c.points.length - 1)
      (hb : b < c.points.length - 1) (hab : a < b)
      (heq : c.point a = c.point b) : False := by
    by_cases hw : a = 0 ∧ b + 2 = c.points.length
    · apply hc.2.2.1 b (by omega)
      calc
        c.point b = c.point 0 := by simpa only [hw.1] using heq.symm
        _ = c.point (b + 1) := by rw [hc.2.1]; congr 1; omega
    · apply not_mem_segmentAt_of_ne_vertex_cyclic c hc a b (by omega) (by omega)
        (by omega) (by omega) hw
      rw [heq]
      exact left_mem_segment ℝ _ _
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (main a b ha hb hab heq)
  · exact hab
  · exact False.elim (main b a hb ha hab heq.symm)

/-- Helper toward Proposition 5.16: the polygon consisting of the increasing
boundary arc and the diagonal traversed back to its first endpoint. -/
@[expose] def diagonalFirst (c : Polyline) (i j : ℕ) : Polyline :=
  closedConcat (c.intervalPolyline i (j - i)) (diagonalArc (c.point i) (c.point j))

/-- Helper toward Proposition 5.16: cutting off the increasing boundary arc
gives a cyclically simple polygon with fewer listed vertices. -/
theorem diagonalFirst_simple_shorter (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hi : i + 1 < j) (hj : j + 1 < c.points.length)
    (hwrap : ¬ (i = 0 ∧ j + 2 = c.points.length))
    (hin : openSegment ℝ (c.point i) (c.point j) ⊆ c.inside) :
    (c.diagonalFirst i j).IsCyclicSimple ∧
      (c.diagonalFirst i j).points.length < c.points.length := by
  have hij : i + (j - i) = j := by omega
  have hne : c.point i ≠ c.point j := by
    intro heq
    have := c.point_injective_before_closure hc (by omega) (by omega) heq
    omega
  obtain ⟨hdstart, hdfinish, hdlen, hdimage⟩ := diagonalArc_data (c.point i) (c.point j)
  have hint : (c.intervalPolyline i (j - i)).image ∩
      (diagonalArc (c.point i) (c.point j)).image =
      {(c.intervalPolyline i (j - i)).start,
        (c.intervalPolyline i (j - i)).finish} := by
    rw [hdimage, start_intervalPolyline, finish_intervalPolyline, hij]
    apply Set.Subset.antisymm
    · intro z hz
      have hz' := (c.diagonal_inter_image i j (by omega) (by omega) hin).le
        ⟨hz.2, c.image_intervalPolyline_subset i (j - i) (by omega) hz.1⟩
      exact hz'
    · rintro z (rfl | rfl)
      · exact ⟨by rw [← start_intervalPolyline c i (j - i)]; exact Or.inl rfl,
          left_mem_segment ℝ _ _⟩
      · refine ⟨?_, right_mem_segment ℝ _ _⟩
        have hv := (c.intervalPolyline i (j - i)).point_mem_image (i := j - i)
          (by rw [length_intervalPolyline]; omega)
        simpa only [point_intervalPolyline _ _ _ _ le_rfl, hij] using hv
  constructor
  · apply closedConcat_isCyclicSimple
    · exact c.isSimple_intervalPolyline_cyclic hc i (j - i) (by omega) (by omega)
    · exact isSimple_diagonalArc _ _ hne
    · rw [length_intervalPolyline]; omega
    · omega
    · simpa only [start_intervalPolyline] using hdstart.symm
    · simpa only [finish_intervalPolyline, hij] using hdfinish.symm
    · simpa only [start_intervalPolyline, finish_intervalPolyline, hij] using hne
    · exact hint
  · rw [diagonalFirst, points_length_closedConcat, length_intervalPolyline, hdlen]
    omega

/-- Helper toward Proposition 5.16: the complementary boundary arc runs from
vertex `j` through the repeated root to vertex `i`. -/
@[expose] def diagonalComplement (c : Polyline) (i j : ℕ) : Polyline :=
  boundaryConcat (c.intervalPolyline j (c.points.length - 1 - j))
    (c.intervalPolyline 0 i)

/-- Helper toward Proposition 5.16: the two pieces of the complementary arc
join at the same geometric root. -/
theorem diagonalComplement_join (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hj : j + 1 < c.points.length) :
    (c.intervalPolyline j (c.points.length - 1 - j)).finish =
      (c.intervalPolyline 0 i).start := by
  rw [finish_intervalPolyline, start_intervalPolyline]
  rw [show j + (c.points.length - 1 - j) = c.points.length - 1 by omega]
  exact hc.2.1.symm

/-- Helper toward Proposition 5.16: the complementary arc has the exact
length needed for the strict decrease in polygon size. -/
theorem length_diagonalComplement (c : Polyline) (i j : ℕ)
    (hj : j + 1 < c.points.length) :
    (c.diagonalComplement i j).points.length = c.points.length - j + i := by
  rw [diagonalComplement, length_boundaryConcat, length_intervalPolyline,
    length_intervalPolyline]
  omega

/-- Helper toward Proposition 5.16: complementary-arc vertices retain their
original cyclic indices, with the root represented by index zero. -/
theorem point_diagonalComplement (c : Polyline) (hc : c.IsCyclicSimple)
    (i j k : ℕ) (hj : j + 1 < c.points.length)
    (hk : k < (c.diagonalComplement i j).points.length) :
    (c.diagonalComplement i j).point k =
      c.point (if k < c.points.length - 1 - j then j + k
        else k - (c.points.length - 1 - j)) := by
  have hjoin := c.diagonalComplement_join hc i j hj
  rw [length_diagonalComplement _ _ _ hj] at hk
  by_cases hleft : k < c.points.length - 1 - j
  · rw [ite_eq_left hleft, diagonalComplement, point_boundaryConcat_left]
    · exact point_intervalPolyline _ _ _ _ (by omega)
    · rw [length_intervalPolyline]; omega
  · rw [ite_eq_right hleft, diagonalComplement]
    have hkidx : k = (c.intervalPolyline j (c.points.length - 1 - j)).points.length
        - 1 + (k - (c.points.length - 1 - j)) := by
      rw [length_intervalPolyline]; omega
    conv_lhs => rw [hkidx]
    rw [point_boundaryConcat_right _ _ hjoin]
    · rw [point_intervalPolyline _ _ _ _ (by omega), Nat.zero_add]
    · rw [length_intervalPolyline]; omega

/-- Helper toward Proposition 5.16: distinct original polygon segments meet
only at endpoints of both segments. -/
theorem segmentAt_intersection_endpoints_cyclic (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hi : i + 1 < c.points.length) (hj : j + 1 < c.points.length)
    (hij : i ≠ j) {z : ℂ} (hzi : z ∈ c.segmentAt i) (hzj : z ∈ c.segmentAt j) :
    (z = c.point i ∨ z = c.point (i + 1)) ∧
      (z = c.point j ∨ z = c.point (j + 1)) := by
  have main (i j : ℕ) (hi : i + 1 < c.points.length) (hj : j + 1 < c.points.length)
      (hij : i ≠ j) (hzi : z ∈ c.segmentAt i) (hzj : z ∈ c.segmentAt j) :
      z = c.point i ∨ z = c.point (i + 1) := by
    by_contra hn
    push Not at hn
    exact Set.disjoint_left.mp (c.disjoint_openSegment_segmentAt_cyclic hc i j hi hj hij)
      (mem_openSegment_of_ne_left_right (Ne.symm hn.1) (Ne.symm hn.2) hzi) hzj
  exact ⟨main i j hi hj hij hzi hzj, main j i hj hi hij.symm hzj hzi⟩

/-- Helper toward Proposition 5.16: a vertex-injective chain made of original
cyclic polygon segments is simple. -/
theorem isSimple_of_cyclic_segment_sources (c : Polyline) (hc : c.IsCyclicSimple)
    (p : Polyline)
    (hinj : ∀ a b, a < p.points.length → b < p.points.length →
      p.point a = p.point b → a = b)
    (hsource : ∀ k, k + 1 < p.points.length → ∃ a,
      a + 1 < c.points.length ∧ p.point k = c.point a ∧
        p.point (k + 1) = c.point (a + 1)) : p.IsSimple := by
  have hmeet (i j : ℕ) (hi : i + 1 < p.points.length)
      (hj : j + 1 < p.points.length) (hij : i ≠ j)
      (z : ℂ) (hzi : z ∈ p.segmentAt i) (hzj : z ∈ p.segmentAt j) :
      (z = p.point i ∨ z = p.point (i + 1)) ∧
        (z = p.point j ∨ z = p.point (j + 1)) := by
    obtain ⟨a, ha, hia, hia1⟩ := hsource i hi
    obtain ⟨b, hb, hjb, hjb1⟩ := hsource j hj
    have hab : a ≠ b := by
      intro heq
      exact hij (hinj i j (by omega) (by omega) (by rw [hia, hjb, heq]))
    rw [segmentAt, hia, hia1] at hzi
    rw [segmentAt, hjb, hjb1] at hzj
    rw [hia, hia1, hjb, hjb1]
    exact c.segmentAt_intersection_endpoints_cyclic hc a b ha hb hab hzi hzj
  refine ⟨?_, ?_, ?_⟩
  · intro i hi heq
    have := hinj i (i + 1) (by omega) hi heq
    omega
  · intro i hi
    apply Set.Subset.antisymm
    · rintro z ⟨hzi, hzj⟩
      obtain ⟨hzi', hzj'⟩ := hmeet i (i + 1) (by omega) (by omega) (by omega) z hzi hzj
      rcases hzi' with hzi' | hzi'
      · rcases hzj' with hzj' | hzj'
        all_goals
          have := hinj _ _ (by omega) (by omega) (hzi'.symm.trans hzj')
          omega
      · exact hzi'
    · rintro z rfl
      exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · intro i j hi hj hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨hzi', hzj'⟩ := hmeet i j hi hj (by omega) z hzi hzj
    rcases hzi' with hzi' | hzi' <;> rcases hzj' with hzj' | hzj'
    all_goals
      have := hinj _ _ (by omega) (by omega) (hzi'.symm.trans hzj')
      omega

/-- Helper toward Proposition 5.16: the complementary boundary chain is simple,
including when one of its pieces is a singleton at the root. -/
theorem isSimple_diagonalComplement (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) :
    (c.diagonalComplement i j).IsSimple := by
  apply c.isSimple_of_cyclic_segment_sources hc
  · intro a b ha hb heq
    rw [c.point_diagonalComplement hc i j a hj ha,
      c.point_diagonalComplement hc i j b hj hb] at heq
    rw [length_diagonalComplement _ _ _ hj] at ha hb
    have hidx := c.point_injective_before_closure hc
      (a := if a < c.points.length - 1 - j then j + a
        else a - (c.points.length - 1 - j))
      (b := if b < c.points.length - 1 - j then j + b
        else b - (c.points.length - 1 - j))
      (by split_ifs <;> omega) (by split_ifs <;> omega) heq
    split_ifs at hidx <;> omega
  · apply edges_boundaryConcat _ _ (c.diagonalComplement_join hc i j hj)
      (fun x y => ∃ a, a + 1 < c.points.length ∧ x = c.point a ∧ y = c.point (a + 1))
    · intro k hk
      rw [length_intervalPolyline] at hk
      refine ⟨j + k, by omega, point_intervalPolyline _ _ _ _ (by omega), ?_⟩
      simpa only [Nat.add_assoc] using
        point_intervalPolyline c j (c.points.length - 1 - j) (k + 1) (by omega)
    · intro k hk
      rw [length_intervalPolyline] at hk
      refine ⟨k, by omega, ?_, ?_⟩
      · simpa only [Nat.zero_add] using point_intervalPolyline c 0 i k (by omega)
      · simpa only [Nat.zero_add] using point_intervalPolyline c 0 i (k + 1) (by omega)

/-- Helper toward Proposition 5.16: the complementary chain has the prescribed
endpoints and stays on the original polygon. -/
theorem diagonalComplement_data (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) :
    (c.diagonalComplement i j).start = c.point j ∧
      (c.diagonalComplement i j).finish = c.point i ∧
      (c.diagonalComplement i j).image ⊆ c.image := by
  have hjoin := c.diagonalComplement_join hc i j hj
  refine ⟨?_, ?_, ?_⟩
  · rw [diagonalComplement, start_boundaryConcat, start_intervalPolyline]
  · rw [diagonalComplement, finish_boundaryConcat_of_join _ _ hjoin,
      finish_intervalPolyline, Nat.zero_add]
  · rw [diagonalComplement, image_boundaryConcat _ _ hjoin]
    exact Set.union_subset
      (c.image_intervalPolyline_subset j (c.points.length - 1 - j) (by omega))
      (c.image_intervalPolyline_subset 0 i (by omega))

/-- Helper toward Proposition 5.16: the second cut polygon closes the
complementary boundary arc by the opposite diagonal traversal. -/
@[expose] def diagonalSecond (c : Polyline) (i j : ℕ) : Polyline :=
  closedConcat (c.diagonalComplement i j) (diagonalArc (c.point j) (c.point i))

/-- Helper toward Proposition 5.16: the complementary cut polygon is cyclically
simple and has strictly fewer vertices than the original polygon. -/
theorem diagonalSecond_simple_shorter (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hi : i + 1 < j) (hj : j + 1 < c.points.length)
    (_hwrap : ¬ (i = 0 ∧ j + 2 = c.points.length))
    (hin : openSegment ℝ (c.point i) (c.point j) ⊆ c.inside) :
    (c.diagonalSecond i j).IsCyclicSimple ∧
      (c.diagonalSecond i j).points.length < c.points.length := by
  obtain ⟨hpstart, hpfinish, hpimage⟩ := c.diagonalComplement_data hc i j (by omega) hj
  obtain ⟨hdstart, hdfinish, hdlen, hdimage⟩ := diagonalArc_data (c.point j) (c.point i)
  have hne : c.point j ≠ c.point i := by
    intro heq
    have := c.point_injective_before_closure hc (by omega) (by omega) heq
    omega
  have hint : (c.diagonalComplement i j).image ∩
      (diagonalArc (c.point j) (c.point i)).image =
      {(c.diagonalComplement i j).start, (c.diagonalComplement i j).finish} := by
    rw [hdimage, hpstart, hpfinish]
    apply Set.Subset.antisymm
    · intro z hz
      have he := (c.diagonal_inter_image i j (by omega) (by omega) hin).le
        ⟨by simpa only [segment_symm] using hz.2, hpimage hz.1⟩
      exact he.elim Or.inr Or.inl
    · rintro z (rfl | rfl)
      · exact ⟨by rw [← hpstart]; exact Or.inl rfl, left_mem_segment ℝ _ _⟩
      · refine ⟨?_, right_mem_segment ℝ _ _⟩
        rw [← hpfinish, ← point_last_eq_finish]
        exact point_mem_image _ (by rw [length_diagonalComplement _ _ _ hj]; omega)
  constructor
  · apply closedConcat_isCyclicSimple
    · exact c.isSimple_diagonalComplement hc i j (by omega) hj
    · exact isSimple_diagonalArc _ _ hne
    · rw [length_diagonalComplement _ _ _ hj]; omega
    · omega
    · exact hpstart.trans hdstart.symm
    · exact hpfinish.trans hdfinish.symm
    · rwa [hpstart, hpfinish]
    · exact hint
  · rw [diagonalSecond, points_length_closedConcat, length_diagonalComplement _ _ _ hj,
      hdlen]
    omega

/-- Helper toward Proposition 5.16: the two complementary boundary arcs cover
exactly the original polygon image. -/
theorem diagonal_arcs_image_union (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) :
    (c.intervalPolyline i (j - i)).image ∪ (c.diagonalComplement i j).image =
      c.image := by
  have hjoin := c.diagonalComplement_join hc i j hj
  rw [diagonalComplement, image_boundaryConcat _ _ hjoin]
  apply Set.Subset.antisymm
  · exact Set.union_subset (c.image_intervalPolyline_subset i (j - i) (by omega))
      (Set.union_subset
        (c.image_intervalPolyline_subset j (c.points.length - 1 - j) (by omega))
        (c.image_intervalPolyline_subset 0 i (by omega)))
  · rintro z (hz | ⟨k, hk, hz⟩)
    · right; right
      rw [Set.mem_singleton_iff] at hz
      left
      simpa only [start_intervalPolyline, point_zero_eq_start, Set.mem_singleton_iff] using hz
    · by_cases hki : k < i
      · right; right; right
        refine ⟨k, by rw [length_intervalPolyline]; omega, ?_⟩
        simpa only [segmentAt_intervalPolyline c 0 i k hki, Nat.zero_add] using hz
      · by_cases hkj : k < j
        · left; right
          refine ⟨k - i, by rw [length_intervalPolyline]; omega, ?_⟩
          rw [segmentAt_intervalPolyline _ _ _ _ (by omega),
            show i + (k - i) = k by omega]
          exact hz
        · right; left; right
          refine ⟨k - j, by rw [length_intervalPolyline]; omega, ?_⟩
          rw [segmentAt_intervalPolyline _ _ _ _ (by omega),
            show j + (k - j) = k by omega]
          exact hz

/-- Helper toward Proposition 5.16: a polygon vertex on an interval arc is
one of that interval's listed vertices. -/
theorem point_mem_intervalPolyline_vertices (c : Polyline) (hc : c.IsCyclicSimple)
    (m i n : ℕ) (hm : m < c.points.length) (hbound : i + n < c.points.length)
    (hmem : c.point m ∈ (c.intervalPolyline i n).image) :
    ∃ k ≤ n, c.point m = c.point (i + k) := by
  rcases hmem with hmem | ⟨k, hk, hmem⟩
  · exact ⟨0, Nat.zero_le _, by simpa only [Set.mem_singleton_iff,
      start_intervalPolyline, Nat.add_zero] using hmem⟩
  · rw [length_intervalPolyline] at hk
    rw [segmentAt_intervalPolyline _ _ _ _ (by omega)] at hmem
    rcases c.point_eq_endpoint_of_mem_segmentAt_cyclic hc m (i + k) hm
      (by omega) hmem with heq | heq
    · exact ⟨k, by omega, heq⟩
    · exact ⟨k + 1, by omega, by simpa only [Nat.add_assoc] using heq⟩

/-- Helper toward Proposition 5.16: a vertex on the increasing boundary arc
can belong to the complementary arc only at their two common endpoints. -/
theorem point_mem_diagonalComplement_endpoints (c : Polyline) (hc : c.IsCyclicSimple)
    (i j m : ℕ) (hij : i < j) (hj : j + 1 < c.points.length)
    (him : i ≤ m) (hmj : m ≤ j)
    (hm : c.point m ∈ (c.diagonalComplement i j).image) : m = i ∨ m = j := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hc.2.1
  have heqiff := c.point_eq_iff_of_closed_vertex_injective (by have := hc.1; omega)
    hclosed (fun a b ha hb heq => c.point_injective_before_closure hc ha hb heq)
  rw [diagonalComplement, image_boundaryConcat _ _ (c.diagonalComplement_join hc i j hj)] at hm
  rcases hm with hm | hm
  · obtain ⟨k, hk, heq⟩ := c.point_mem_intervalPolyline_vertices hc m j
      (c.points.length - 1 - j) (by omega) (by omega) hm
    have hh := (heqiff m (j + k) (by omega) (by omega)).mp heq
    omega
  · obtain ⟨k, hk, heq⟩ := c.point_mem_intervalPolyline_vertices hc m 0 i
      (by omega) (by omega) hm
    have hh := (heqiff m (0 + k) (by omega) (by omega)).mp heq
    omega

/-- Helper toward Proposition 5.16: the two original boundary arcs intersect
exactly at the diagonal endpoints. -/
theorem diagonal_arcs_image_inter (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) :
    (c.intervalPolyline i (j - i)).image ∩ (c.diagonalComplement i j).image =
      {c.point i, c.point j} := by
  obtain ⟨hpstart, hpfinish, _⟩ := c.diagonalComplement_data hc i j hij hj
  have hqjoin := c.diagonalComplement_join hc i j hj
  have hvertex (m : ℕ) (him : i ≤ m) (hmj : m ≤ j)
      (hz : c.point m ∈ (c.diagonalComplement i j).image) :
      c.point m ∈ ({c.point i, c.point j} : Set ℂ) := by
    rcases c.point_mem_diagonalComplement_endpoints hc i j m hij hj him hmj hz with h | h
    · exact Or.inl (congrArg c.point h)
    · exact Or.inr (congrArg c.point h)
  apply Set.Subset.antisymm
  · rintro z ⟨hzp, hzq⟩
    rcases hzp with hzp | ⟨k, hk, hzp⟩
    · rw [Set.mem_singleton_iff, start_intervalPolyline] at hzp
      exact Or.inl hzp
    · rw [length_intervalPolyline] at hk
      rw [segmentAt_intervalPolyline _ _ _ _ (by omega)] at hzp
      have hmeet (a : ℕ) (ha : a + 1 < c.points.length)
          (houtside : a < i ∨ j ≤ a) (hz : z ∈ c.segmentAt a) :
          z ∈ ({c.point i, c.point j} : Set ℂ) := by
        have hne : i + k ≠ a := by omega
        obtain ⟨he, _⟩ := c.segmentAt_intersection_endpoints_cyclic hc (i + k) a
          (by omega) ha hne hzp hz
        rcases he with he | he
        · rw [he] at hzq ⊢
          exact hvertex (i + k) (by omega) (by omega) hzq
        · rw [he] at hzq ⊢
          exact hvertex (i + k + 1) (by omega) (by omega) hzq
      rw [diagonalComplement, image_boundaryConcat _ _ hqjoin] at hzq
      rcases hzq with hzq | hzq
      · rcases hzq with hzq | ⟨l, hl, hzq⟩
        · rw [Set.mem_singleton_iff, start_intervalPolyline] at hzq
          exact Or.inr hzq
        · rw [length_intervalPolyline] at hl
          rw [segmentAt_intervalPolyline _ _ _ _ (by omega)] at hzq
          exact hmeet (j + l) (by omega) (Or.inr (by omega)) hzq
      · rcases hzq with hzq | ⟨l, hl, hzq⟩
        · rw [Set.mem_singleton_iff, start_intervalPolyline, point_zero_eq_start] at hzq
          have hzq' : z ∈ c.segmentAt 0 := by
            rw [hzq, ← point_zero_eq_start]
            exact left_mem_segment ℝ _ _
          by_cases hi0 : i = 0
          · exact Or.inl (by simpa only [hi0, point_zero_eq_start] using hzq)
          · exact hmeet 0 (by omega) (Or.inl (by omega)) hzq'
        · rw [length_intervalPolyline] at hl
          rw [segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add] at hzq
          exact hmeet l (by omega) (Or.inl (by omega)) hzq
  · rintro z (rfl | rfl)
    · refine ⟨?_, ?_⟩
      · rw [← start_intervalPolyline c i (j - i)]; exact Or.inl rfl
      · rw [← hpfinish, ← point_last_eq_finish]
        exact point_mem_image _ (by rw [length_diagonalComplement _ _ _ hj]; omega)
    · refine ⟨?_, ?_⟩
      · have hv := (c.intervalPolyline i (j - i)).point_mem_image (i := j - i)
          (by rw [length_intervalPolyline]; omega)
        simpa only [point_intervalPolyline _ _ _ _ le_rfl,
          show i + (j - i) = j by omega] using hv
      · rw [← hpstart]; exact Or.inl rfl

/-- Helper toward Proposition 5.16: both cut images are the corresponding
boundary arcs together with the same closed diagonal. -/
theorem diagonal_images (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) :
    (c.diagonalFirst i j).image = (c.intervalPolyline i (j - i)).image ∪
      segment ℝ (c.point i) (c.point j) ∧
    (c.diagonalSecond i j).image = (c.diagonalComplement i j).image ∪
      segment ℝ (c.point i) (c.point j) := by
  obtain ⟨_, hf, _⟩ := c.diagonalComplement_data hc i j hij hj
  constructor
  · rw [diagonalFirst, image_closedConcat]
    · rw [(diagonalArc_data _ _).2.2.2]
    · rw [finish_intervalPolyline, (diagonalArc_data _ _).2.1]
      congr 1
      omega
  · rw [diagonalSecond, image_closedConcat]
    · rw [(diagonalArc_data _ _).2.2.2, segment_symm]
    · exact hf.trans (diagonalArc_data _ _).2.1.symm

/-- Helper toward Proposition 5.16: exact union and intersection of the two
cut polygon boundaries. -/
theorem diagonal_images_union_inter (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) :
    (c.diagonalFirst i j).image ∪ (c.diagonalSecond i j).image =
      c.image ∪ segment ℝ (c.point i) (c.point j) ∧
    (c.diagonalFirst i j).image ∩ (c.diagonalSecond i j).image =
      segment ℝ (c.point i) (c.point j) := by
  obtain ⟨hfirst, hsecond⟩ := c.diagonal_images hc i j hij hj
  rw [hfirst, hsecond]
  constructor
  · rw [show (c.intervalPolyline i (j - i)).image ∪ segment ℝ (c.point i) (c.point j) ∪
        ((c.diagonalComplement i j).image ∪ segment ℝ (c.point i) (c.point j)) =
        ((c.intervalPolyline i (j - i)).image ∪ (c.diagonalComplement i j).image) ∪
          segment ℝ (c.point i) (c.point j) by ext z; simp only [mem_union]; tauto,
      c.diagonal_arcs_image_union hc i j hij hj]
  · apply Set.Subset.antisymm
    · rintro z ⟨hz | hz, hw | hw⟩
      · have he := (c.diagonal_arcs_image_inter hc i j hij hj).le ⟨hz, hw⟩
        rcases he with he | he
        · rw [he]; exact left_mem_segment ℝ _ _
        · rw [he]; exact right_mem_segment ℝ _ _
      · exact hw
      · exact hz
      · exact hz
    · exact fun z hz => ⟨Or.inr hz, Or.inr hz⟩

/-- Helper toward Proposition 5.16: traversing a segment in both directions
has total signed angle zero away from that segment. -/
theorem angleSum_diagonalArc_cancel (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    (diagonalArc a b).angleSum z + (diagonalArc b a).angleSum z = 0 := by
  let p := diagonalArc a b
  let q := diagonalArc b a
  have hjoin : p.finish = q.start := rfl
  have hclosed : (boundaryConcat p q).start = (boundaryConcat p q).finish := by
    rw [start_boundaryConcat, finish_boundaryConcat_of_join _ _ hjoin]
    rfl
  have hlen : (boundaryConcat p q).points.length ≤ 3 := by
    rw [length_boundaryConcat]
    change 2 + 2 - 1 ≤ 3
    omega
  have him : (boundaryConcat p q).image = segment ℝ a b := by
    rw [image_boundaryConcat _ _ hjoin, (diagonalArc_data a b).2.2.2,
      (diagonalArc_data b a).2.2.2, segment_symm, Set.union_self]
  have hzero := (boundaryConcat p q).angleSum_eq_zero_of_length_le_three hlen
    hclosed z (by rwa [him])
  rwa [angleSum_boundaryConcat _ _ hjoin] at hzero

/-- Helper toward Proposition 5.16: the signed angle of the original boundary
is the sum of the angles of its two complementary arcs. -/
theorem angleSum_diagonal_arcs (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length) (z : ℂ) :
    c.angleSum z = (c.intervalPolyline i (j - i)).angleSum z +
      (c.diagonalComplement i j).angleSum z := by
  have h1 := c.angleSum_intervalPolyline_add z 0 i (c.points.length - 1 - i)
  have h2 := c.angleSum_intervalPolyline_add z i (j - i) (c.points.length - 1 - j)
  rw [show i + (c.points.length - 1 - i) = c.points.length - 1 by omega,
    angleSum_intervalPolyline_all, Nat.zero_add] at h1
  rw [show j - i + (c.points.length - 1 - j) = c.points.length - 1 - i by omega,
    show i + (j - i) = j by omega] at h2
  rw [diagonalComplement, angleSum_boundaryConcat _ _ (c.diagonalComplement_join hc i j hj)]
  linarith only [h1, h2]

/-- Helper toward Proposition 5.16: cutting along an interior diagonal preserves
the exact winding sum; the two diagonal traversals cancel. -/
theorem angleSum_diagonal_split (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length)
    (z : ℂ) (hz : z ∉ c.image ∪ segment ℝ (c.point i) (c.point j)) :
    c.angleSum z = (c.diagonalFirst i j).angleSum z +
      (c.diagonalSecond i j).angleSum z := by
  have hfirst : (c.diagonalFirst i j).angleSum z =
      (c.intervalPolyline i (j - i)).angleSum z +
        (diagonalArc (c.point j) (c.point i)).angleSum z := by
    change (boundaryConcat _ _).angleSum z = _
    apply angleSum_boundaryConcat
    rw [finish_intervalPolyline]
    change c.point (i + (j - i)) = c.point j
    congr 1
    omega
  have hsecond : (c.diagonalSecond i j).angleSum z =
      (c.diagonalComplement i j).angleSum z +
        (diagonalArc (c.point i) (c.point j)).angleSum z := by
    change (boundaryConcat _ _).angleSum z = _
    apply angleSum_boundaryConcat
    exact (c.diagonalComplement_data hc i j hij hj).2.1
  have hcancel := angleSum_diagonalArc_cancel (c.point i) (c.point j) z
    (fun h => hz (Or.inr h))
  rw [hfirst, hsecond]
  have harcs := c.angleSum_diagonal_arcs hc i j hij hj z
  linarith only [hcancel, harcs]

/-- Helper toward Proposition 5.16: closure of either winding side avoids the
other open side of a closed polygon. -/
theorem closure_sides_avoid (c : Polyline) (hclosed : c.start = c.finish) :
    closure c.inside ⊆ c.outsideᶜ ∧ closure c.outside ⊆ c.insideᶜ := by
  constructor
  · apply closure_minimal _ (c.isOpen_outside hclosed).isClosed_compl
    exact fun z hz hw => hz.2 hw.2
  · apply closure_minimal _ (c.isOpen_inside hclosed).isClosed_compl
    exact fun z hz hw => hw.2 hz.2

/-- Helper toward Proposition 5.16: a closed polygon whose boundary lies in
the closed inside of a simple polygon has its inside contained there. -/
theorem inside_subset_inside_of_image_subset_closure (c : Polyline)
    (hc : c.IsCyclicSimple) (p : Polyline) (hpclosed : p.start = p.finish)
    (himage : p.image ⊆ closure c.inside) : p.inside ⊆ c.inside := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hc.2.1
  have havoid : c.outside ⊆ p.imageᶜ := by
    intro z hz hzp
    exact (c.closure_sides_avoid hclosed).1 (himage hzp) hz
  have hout : c.outside ⊆ p.outside := by
    rcases p.subset_inside_or_outside_of_isPreconnected hpclosed c.outside
      (c.isConnected_inside_outside_cyclic hc).2.isPreconnected havoid with hin | hout
    · obtain ⟨R, hR⟩ := p.exists_radius_exterior_subset_outside hpclosed
      obtain ⟨z, hz, hzR⟩ := c.outside_unbounded hclosed R
      exact False.elim ((hin hz).2 (hR z hzR).2)
    · exact hout
  have hclout : closure c.outside ⊆ p.insideᶜ :=
    (closure_mono hout).trans (p.closure_sides_avoid hpclosed).2
  have hcimage : c.image ⊆ closure c.outside := by
    rw [← (c.frontier_inside_outside_eq_image_cyclic hc).2]
    exact frontier_subset_closure
  intro z hz
  have hznot : z ∉ c.image := fun h => hclout (hcimage h) hz
  exact ⟨hznot, fun hzero => hclout (subset_closure ⟨hznot, hzero⟩) hz⟩

/-- Helper toward Proposition 5.16: both cut interiors are contained in the
original interior, including all boundary-limit cases. -/
theorem diagonal_inside_subsets (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length)
    (hin : openSegment ℝ (c.point i) (c.point j) ⊆ c.inside) :
    (c.diagonalFirst i j).inside ⊆ c.inside ∧
      (c.diagonalSecond i j).inside ⊆ c.inside := by
  have hbound : c.image ∪ segment ℝ (c.point i) (c.point j) ⊆ closure c.inside := by
    apply Set.union_subset
    · rw [← (c.frontier_inside_outside_eq_image_cyclic hc).1]
      exact frontier_subset_closure
    · exact fun z hz => closure_mono hin (segment_subset_closure_openSegment hz)
  have him := (c.diagonal_images_union_inter hc i j hij hj).1
  have hfirstclosed : (c.diagonalFirst i j).start = (c.diagonalFirst i j).finish := by
    apply closed_closedConcat
    · exact (start_intervalPolyline _ _ _).trans (diagonalArc_data _ _).1.symm
    · exact le_rfl
  have hsecondclosed : (c.diagonalSecond i j).start = (c.diagonalSecond i j).finish := by
    apply closed_closedConcat
    · exact (c.diagonalComplement_data hc i j hij hj).1.trans (diagonalArc_data _ _).1.symm
    · exact le_rfl
  constructor
  · apply c.inside_subset_inside_of_image_subset_closure hc _ hfirstclosed
    exact fun z hz => hbound (him ▸ Or.inl hz)
  · apply c.inside_subset_inside_of_image_subset_closure hc _ hsecondclosed
    exact fun z hz => hbound (him ▸ Or.inr hz)

/-- Helper toward Proposition 5.16: the winding of a cyclically simple polygon
has absolute value one at every inside point. -/
theorem abs_angleSum_eq_one_of_mem_inside (c : Polyline) (hc : c.IsCyclicSimple)
    (z : ℂ) (hz : z ∈ c.inside) : |c.angleSum z| = 1 := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hc.2.1
  obtain ⟨L, R, _, _, hLc, hRc, hLavoid, hRavoid, _, _, a, b, hLa, hRb, hab⟩ :=
    c.exists_connected_constant_edge_strips_cyclic hc 0 (by have := hc.1; omega)
  obtain ⟨u, hu⟩ := hLc.nonempty
  obtain ⟨v, hv⟩ := hRc.nonempty
  have hdiff : |c.angleSum u - c.angleSum v| = 1 := by rw [hLa u hu, hRb v hv]; exact hab
  have hvalues (w : ℂ) (hw : w ∉ c.image) :
      c.angleSum w = 0 ∨ c.angleSum w = c.angleSum z := by
    by_cases hzero : c.angleSum w = 0
    · exact Or.inl hzero
    · right
      exact c.angleSum_eq_of_isPreconnected hclosed c.inside
        (c.isConnected_inside_outside_cyclic hc).1.isPreconnected
        (fun _ h => h.1) w z ⟨hw, hzero⟩ hz
  rcases hvalues u (hLavoid hu) with hu0 | huz <;>
    rcases hvalues v (hRavoid hv) with hv0 | hvz
  · simp only [hu0, hv0, sub_self, abs_zero] at hdiff
    norm_num at hdiff
  · simpa only [hu0, hvz, zero_sub, abs_neg] using hdiff
  · simpa only [huz, hv0, sub_zero] using hdiff
  · simp only [huz, hvz, sub_self, abs_zero] at hdiff
    norm_num at hdiff

/-- Helper toward Proposition 5.16: cutting removes only the open diagonal
from the original interior and gives two disjoint open interiors. -/
theorem diagonal_inside_disjoint_union (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hi : i + 1 < j) (hj : j + 1 < c.points.length)
    (hwrap : ¬ (i = 0 ∧ j + 2 = c.points.length))
    (hin : openSegment ℝ (c.point i) (c.point j) ⊆ c.inside) :
    Disjoint (c.diagonalFirst i j).inside (c.diagonalSecond i j).inside ∧
      c.inside \ openSegment ℝ (c.point i) (c.point j) =
        (c.diagonalFirst i j).inside ∪ (c.diagonalSecond i j).inside := by
  have hfirst := (c.diagonalFirst_simple_shorter hc i j hi hj hwrap hin).1
  have hsecond := (c.diagonalSecond_simple_shorter hc i j hi hj hwrap hin).1
  obtain ⟨hsub1, hsub2⟩ := c.diagonal_inside_subsets hc i j (by omega) hj hin
  obtain ⟨him1, him2⟩ := c.diagonal_images hc i j (by omega) hj
  have hoff (z : ℂ) (hz : z ∈ c.inside)
      (hdiag : z ∉ openSegment ℝ (c.point i) (c.point j)) :
      z ∉ c.image ∪ segment ℝ (c.point i) (c.point j) := by
    rintro (hzimage | hzseg)
    · exact hz.1 hzimage
    · apply hdiag
      apply mem_openSegment_of_ne_left_right _ _ hzseg
      · intro heq
        exact hz.1 (heq ▸ c.point_mem_image (by omega))
      · intro heq
        exact hz.1 (heq ▸ c.point_mem_image (by omega))
  have havoid1 (z : ℂ) (hz : z ∈ (c.diagonalFirst i j).inside) :
      z ∉ segment ℝ (c.point i) (c.point j) :=
    fun hd => hz.1 (him1 ▸ Or.inr hd)
  have havoid2 (z : ℂ) (hz : z ∈ (c.diagonalSecond i j).inside) :
      z ∉ segment ℝ (c.point i) (c.point j) :=
    fun hd => hz.1 (him2 ▸ Or.inr hd)
  constructor
  · apply Set.disjoint_left.mpr
    intro z hz1 hz2
    have hz := hsub1 hz1
    have hzoff : z ∉ c.image ∪ segment ℝ (c.point i) (c.point j) :=
      fun h => h.elim hz.1 (havoid1 z hz1)
    have hs := c.angleSum_diagonal_split hc i j (by omega) hj z hzoff
    have ha := eq_or_eq_neg_of_abs_eq (c.abs_angleSum_eq_one_of_mem_inside hc z hz)
    have hb := eq_or_eq_neg_of_abs_eq
      ((c.diagonalFirst i j).abs_angleSum_eq_one_of_mem_inside hfirst z hz1)
    have hd := eq_or_eq_neg_of_abs_eq
      ((c.diagonalSecond i j).abs_angleSum_eq_one_of_mem_inside hsecond z hz2)
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hd with hd | hd
    all_goals linarith only [hs, ha, hb, hd]
  · apply Set.Subset.antisymm
    · intro z hz
      have hzoff := hoff z hz.1 hz.2
      have hs := c.angleSum_diagonal_split hc i j (by omega) hj z hzoff
      have hz1 : z ∉ (c.diagonalFirst i j).image := by
        rw [him1]
        exact fun h => hzoff (h.elim
          (fun h => Or.inl (c.image_intervalPolyline_subset i (j - i) (by omega) h)) Or.inr)
      have hz2 : z ∉ (c.diagonalSecond i j).image := by
        rw [him2]
        exact fun h => hzoff (h.elim
          (fun h => Or.inl ((c.diagonalComplement_data hc i j (by omega) hj).2.2 h)) Or.inr)
      by_cases hzero : (c.diagonalFirst i j).angleSum z = 0
      · right
        refine ⟨hz2, ?_⟩
        intro hzero2
        exact hz.1.2 (by rw [hs, hzero, hzero2, add_zero])
      · exact Or.inl ⟨hz1, hzero⟩
    · rintro z (hz | hz)
      · exact ⟨hsub1 hz, fun hd => havoid1 z hz (openSegment_subset_segment ℝ _ _ hd)⟩
      · exact ⟨hsub2 hz, fun hd => havoid2 z hz (openSegment_subset_segment ℝ _ _ hd)⟩

/-- Helper toward Proposition 5.16: the closed inside of a simple polygon
consists precisely of its inside and its polygon image. -/
theorem closure_inside_eq_union_image (c : Polyline) (hc : c.IsCyclicSimple) :
    closure c.inside = c.inside ∪ c.image := by
  rw [closure_eq_self_union_frontier, (c.frontier_inside_outside_eq_image_cyclic hc).1]

/-- Helper toward Proposition 5.16: the two cut closed regions cover exactly
the original closed region and intersect exactly along the closed diagonal. -/
theorem diagonal_closure_union_inter (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hi : i + 1 < j) (hj : j + 1 < c.points.length)
    (hwrap : ¬ (i = 0 ∧ j + 2 = c.points.length))
    (hin : openSegment ℝ (c.point i) (c.point j) ⊆ c.inside) :
    closure c.inside = closure (c.diagonalFirst i j).inside ∪
      closure (c.diagonalSecond i j).inside ∧
    closure (c.diagonalFirst i j).inside ∩ closure (c.diagonalSecond i j).inside =
      segment ℝ (c.point i) (c.point j) := by
  have hfirst := (c.diagonalFirst_simple_shorter hc i j hi hj hwrap hin).1
  have hsecond := (c.diagonalSecond_simple_shorter hc i j hi hj hwrap hin).1
  obtain ⟨hsub1, hsub2⟩ := c.diagonal_inside_subsets hc i j (by omega) hj hin
  obtain ⟨hdisj, hregions⟩ := c.diagonal_inside_disjoint_union hc i j hi hj hwrap hin
  obtain ⟨hunion, hinter⟩ := c.diagonal_images_union_inter hc i j (by omega) hj
  obtain ⟨him1, him2⟩ := c.diagonal_images hc i j (by omega) hj
  have hcl := c.closure_inside_eq_union_image hc
  have hcl1 := (c.diagonalFirst i j).closure_inside_eq_union_image hfirst
  have hcl2 := (c.diagonalSecond i j).closure_inside_eq_union_image hsecond
  have hdiag1 : segment ℝ (c.point i) (c.point j) ⊆ (c.diagonalFirst i j).image :=
    fun _ hz => him1 ▸ Or.inr hz
  have hdiag2 : segment ℝ (c.point i) (c.point j) ⊆ (c.diagonalSecond i j).image :=
    fun _ hz => him2 ▸ Or.inr hz
  have hnot12 {z : ℂ} (hz : z ∈ (c.diagonalFirst i j).inside)
      (hw : z ∈ (c.diagonalSecond i j).image) : False := by
    rcases hunion.le (Or.inr hw) with h | h
    · exact (hsub1 hz).1 h
    · exact hz.1 (hdiag1 h)
  have hnot21 {z : ℂ} (hz : z ∈ (c.diagonalSecond i j).inside)
      (hw : z ∈ (c.diagonalFirst i j).image) : False := by
    rcases hunion.le (Or.inl hw) with h | h
    · exact (hsub2 hz).1 h
    · exact hz.1 (hdiag2 h)
  constructor
  · apply Set.Subset.antisymm
    · rw [hcl]
      rintro z (hz | hz)
      · by_cases hd : z ∈ openSegment ℝ (c.point i) (c.point j)
        · left
          rw [hcl1]
          exact Or.inr (hdiag1 (openSegment_subset_segment ℝ _ _ hd))
        · have hz' := hregions.le ⟨hz, hd⟩
          exact hz'.elim (fun h => Or.inl (subset_closure h))
            (fun h => Or.inr (subset_closure h))
      · have hz' := hunion.ge (Or.inl hz)
        rcases hz' with hz' | hz'
        · left; rw [hcl1]; exact Or.inr hz'
        · right; rw [hcl2]; exact Or.inr hz'
    · exact Set.union_subset (closure_mono hsub1) (closure_mono hsub2)
  · rw [hcl1, hcl2]
    apply Set.Subset.antisymm
    · rintro z ⟨hz | hz, hw | hw⟩
      · exact False.elim (Set.disjoint_left.mp hdisj hz hw)
      · exact False.elim (hnot12 hz hw)
      · exact False.elim (hnot21 hw hz)
      · exact hinter.le ⟨hz, hw⟩
    · exact fun _ hz => ⟨Or.inr (hdiag1 hz), Or.inr (hdiag2 hz)⟩

/-- Helper toward Proposition 5.16: every cyclically simple polygon with at
least four cyclic vertices admits the exact shorter-polygon closed-region
decomposition along an interior diagonal. -/
theorem exists_diagonal_closed_region_split (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : 5 ≤ c.points.length) :
    ∃ (a b : ℂ) (c₁ c₂ : Polyline),
      a ∈ c.image ∧ b ∈ c.image ∧ a ≠ b ∧
      c₁.IsCyclicSimple ∧ c₂.IsCyclicSimple ∧
      c₁.points.length < c.points.length ∧ c₂.points.length < c.points.length ∧
      openSegment ℝ a b ⊆ c.inside ∧
      c₁.image ∪ c₂.image = c.image ∪ segment ℝ a b ∧
      c₁.image ∩ c₂.image = segment ℝ a b ∧
      closure c.inside = closure c₁.inside ∪ closure c₂.inside ∧
      closure c₁.inside ∩ closure c₂.inside = segment ℝ a b := by
  obtain ⟨i, j, hi, hj, hij, hwrap, hin⟩ := c.exists_diagonal_cyclic hc hlen
  obtain ⟨hfirst, hfirstlen⟩ := c.diagonalFirst_simple_shorter hc i j hij hj hwrap hin
  obtain ⟨hsecond, hsecondlen⟩ := c.diagonalSecond_simple_shorter hc i j hij hj hwrap hin
  obtain ⟨hunion, hinter⟩ := c.diagonal_images_union_inter hc i j (by omega) hj
  obtain ⟨hclunion, hclinter⟩ := c.diagonal_closure_union_inter hc i j hij hj hwrap hin
  refine ⟨c.point i, c.point j, c.diagonalFirst i j, c.diagonalSecond i j,
    c.point_mem_image (by omega), c.point_mem_image (by omega), ?_,
    hfirst, hsecond, hfirstlen, hsecondlen, hin, hunion, hinter, hclunion, hclinter⟩
  intro heq
  have := c.point_injective_before_closure hc (by omega) (by omega) heq
  omega

end Polyline
end DirectedDistances.PlanarMap
