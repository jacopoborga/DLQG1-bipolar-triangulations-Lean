/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalSeparation5

/-! # Index bookkeeping for polygonal separation

Helpers toward Proposition 5.16. -/

public section

namespace DirectedDistances.PlanarMap
namespace Polyline

/-- Helper toward Proposition 5.16: the endpoint-glued vertex list has the
sum of the two edge counts plus one vertices. -/
theorem points_length_closedConcat (p q : Polyline) :
    (closedConcat p q).points.length = p.points.length + q.points.length - 1 := by
  have hq : 0 < q.points.length := List.length_pos_iff.mpr q.nonempty
  simp only [closedConcat, concat, Polyline.reverse, List.length_append,
    List.length_reverse, List.length_tail]
  omega

/-- Helper toward Proposition 5.16: endpoint separation rules out two
one-edge arcs, so the closed concatenation has at least three edges. -/
theorem points_length_closedConcat_ge_four (p q : Polyline)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hne : p.start ≠ p.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish}) :
    4 ≤ (closedConcat p q).points.length := by
  by_contra hnot
  have hlen : (closedConcat p q).points.length < 4 := by omega
  rw [points_length_closedConcat] at hlen
  have hpLen : p.points.length = 2 := by omega
  have hqLen : q.points.length = 2 := by omega
  let z : ℂ := p.start + (1 / 2 : ℝ) • (p.finish - p.start)
  have hp1 : p.point 1 = p.finish := by simpa [hpLen] using p.point_last_eq_finish
  have hq1 : q.point 1 = q.finish := by simpa [hqLen] using q.point_last_eq_finish
  have hsegp : z ∈ p.segmentAt 0 := by
    rw [Polyline.segmentAt, segment_eq_image']
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp only [point_zero_eq_start, hp1]
    simp [z]
  have hsegq : z ∈ q.segmentAt 0 := by
    rw [Polyline.segmentAt, segment_eq_image']
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp only [point_zero_eq_start, hq1]
    rw [← hstart, ← hfinish]
  have hpimage : z ∈ p.image := p.segmentAt_subset_image (by omega) hsegp
  have hqimage : z ∈ q.image := q.segmentAt_subset_image (by omega) hsegq
  have hpair : z = p.start ∨ z = p.finish := by
    have h := hint ▸ (show z ∈ p.image ∩ q.image from ⟨hpimage, hqimage⟩)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hzstart : z ≠ p.start := by
    intro heq
    have hmul : ((1 / 2 : ℝ) : ℂ) * (p.finish - p.start) = 0 := by
      have hh := congrArg (fun w : ℂ => w - p.start) heq
      simpa [z, RCLike.real_smul_eq_coe_mul] using hh
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · norm_num at hzero
    · exact hne (sub_eq_zero.mp hzero).symm
  have hzfinish : z ≠ p.finish := by
    intro heq
    have hmul : (((1 / 2 : ℝ) : ℂ) - 1) * (p.finish - p.start) = 0 := by
      have hh := congrArg (fun w : ℂ => w - p.start) heq
      dsimp [z] at hh ⊢
      linear_combination hh
    have hcoef : (((1 / 2 : ℝ) : ℂ) - 1) ≠ 0 := by norm_num
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact hcoef hzero
    · exact hne (sub_eq_zero.mp hzero).symm
  rcases hpair with heq | heq
  · exact hzstart heq
  · exact hzfinish heq

/-- Helper toward Proposition 5.16: before the join, the closed concatenation
has the same indexed vertices as its first arc. -/
theorem point_closedConcat_left (p q : Polyline) (i : ℕ)
    (hi : i < p.points.length) :
    (closedConcat p q).point i = p.point i := by
  change (p.points ++ q.reverse.points.tail).getD i (closedConcat p q).start =
    p.points.getD i p.start
  rw [List.getD_append _ _ _ _ hi]
  rw [show (closedConcat p q).start = p.start by
    simp [closedConcat]]

/-- Helper toward Proposition 5.16: the second arc's reversed vertex at a
positive index appears after the first arc's final vertex. -/
theorem point_closedConcat_right (p q : Polyline) (i : ℕ)
    (hi : i + 1 < q.points.length) :
    (closedConcat p q).point (p.points.length + i) =
      q.reverse.point (i + 1) := by
  change (p.points ++ q.reverse.points.tail).getD (p.points.length + i)
      (closedConcat p q).start = q.reverse.points.getD (i + 1) q.reverse.start
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  have hi' : i + 1 < q.reverse.points.length := by
    simpa [Polyline.reverse, List.length_reverse] using hi
  have hne : q.reverse.points ≠ [] := q.reverse.nonempty
  cases h : q.reverse.points with
  | nil => exact (hne h).elim
  | cons a l =>
      have hi'' : i < l.length := by simp only [h, List.length_cons] at hi'; omega
      change l.getD (p.points.length + i - p.points.length) (closedConcat p q).start =
        (a :: l).getD (i + 1) q.reverse.start
      rw [Nat.add_sub_cancel_left, List.getD_cons_succ]
      rw [List.getD_eq_getElem (l := l) (d := (closedConcat p q).start) hi'']
      rw [List.getD_eq_getElem (l := l) (d := q.reverse.start) hi'']

/-- Helper toward Proposition 5.16: edges wholly before the join are exactly
the corresponding edges of the first arc. -/
theorem segmentAt_closedConcat_left (p q : Polyline) (i : ℕ)
    (hi : i + 1 < p.points.length) :
    (closedConcat p q).segmentAt i = p.segmentAt i := by
  change segment ℝ ((closedConcat p q).point i)
      ((closedConcat p q).point (i + 1)) = segment ℝ (p.point i) (p.point (i + 1))
  rw [point_closedConcat_left p q i (by omega),
    point_closedConcat_left p q (i + 1) hi]

/-- Helper toward Proposition 5.16: edges in the reversed second arc agree
with the corresponding reversed-arc edges, including the join edge. -/
theorem segmentAt_closedConcat_right (p q : Polyline)
    (hfinish : p.finish = q.finish) (i : ℕ)
    (hi : i + 1 < q.points.length) :
    (closedConcat p q).segmentAt (p.points.length - 1 + i) =
      q.reverse.segmentAt i := by
  have hpLen : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
  by_cases hi0 : i = 0
  · subst i
    simp only [Nat.add_zero]
    have hmlast : p.points.length - 1 + 1 = p.points.length := by omega
    unfold Polyline.segmentAt
    rw [Nat.zero_add, hmlast]
    change segment ℝ ((closedConcat p q).point (p.points.length - 1))
        ((closedConcat p q).point p.points.length) =
      segment ℝ (q.reverse.point 0) (q.reverse.point 1)
    rw [point_closedConcat_left p q _ (by omega), ← Nat.add_zero p.points.length,
      point_closedConcat_right p q 0 hi]
    congr 1
    calc
      p.point (p.points.length - 1) = p.finish := p.point_last_eq_finish
      _ = q.finish := hfinish
      _ = q.reverse.point 0 := by
        rw [point_zero_eq_start, start_reverse]
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hidx : p.points.length - 1 + i = p.points.length + (i - 1) := by omega
    have hidx' : p.points.length - 1 + i + 1 = p.points.length + i := by omega
    change segment ℝ ((closedConcat p q).point (p.points.length - 1 + i))
        ((closedConcat p q).point (p.points.length - 1 + i + 1)) =
      segment ℝ (q.reverse.point i) (q.reverse.point (i + 1))
    rw [hidx', hidx, point_closedConcat_right p q (i - 1) (by omega),
      point_closedConcat_right p q i hi]
    have hsub : i - 1 + 1 = i := by omega
    rw [hsub]

/-- Helper toward Proposition 5.16: each vertex index along the reversed
second arc starts at the common endpoint and then follows that arc. -/
theorem point_closedConcat_right_edge (p q : Polyline)
    (hfinish : p.finish = q.finish) (j : ℕ)
    (hj : j + 1 < q.points.length) :
    (closedConcat p q).point (p.points.length - 1 + j) = q.reverse.point j := by
  have hpLen : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
  by_cases hj0 : j = 0
  · subst j
    calc
      (closedConcat p q).point (p.points.length - 1) = p.point (p.points.length - 1) :=
        point_closedConcat_left p q _ (by omega)
      _ = p.finish := p.point_last_eq_finish
      _ = q.finish := hfinish
      _ = q.reverse.point 0 := by rw [point_zero_eq_start, start_reverse]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hidx : p.points.length - 1 + j = p.points.length + (j - 1) := by omega
    rw [hidx, point_closedConcat_right p q (j - 1) (by omega)]
    have hsub : j - 1 + 1 = j := by omega
    rw [hsub]

/-- Helper toward Proposition 5.16: the closed concatenation's first and
last listed vertices agree when the two original arcs share their endpoints. -/
theorem point_zero_eq_last_closedConcat (p q : Polyline)
    (hstart : p.start = q.start) (hlenq : 2 ≤ q.points.length) :
    (closedConcat p q).point 0 =
      (closedConcat p q).point ((closedConcat p q).points.length - 1) := by
  let c := closedConcat p q
  have hc : c.start = c.finish := closed_closedConcat p q hstart hlenq
  calc
    c.point 0 = c.start := point_zero_eq_start c
    _ = c.finish := hc
    _ = c.point (c.points.length - 1) := point_last_eq_finish c |>.symm

/-- Helper toward Proposition 5.16: every edge in the endpoint-glued
concatenation is nondegenerate when each input arc is simple. -/
theorem closedConcat_edge_ne (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (_hlenq : 2 ≤ q.points.length)
    (hfinish : p.finish = q.finish) (i : ℕ)
    (hi : i + 1 < (closedConcat p q).points.length) :
    (closedConcat p q).point i ≠ (closedConcat p q).point (i + 1) := by
  have hlen := points_length_closedConcat p q
  by_cases hleft : i + 1 < p.points.length
  · rw [point_closedConcat_left p q i (by omega),
      point_closedConcat_left p q (i + 1) hleft]
    exact hp.1 i hleft
  · let j := i - (p.points.length - 1)
    have hidx : i = p.points.length - 1 + j := by
      dsimp [j]
      omega
    have hj : j + 1 < q.points.length := by
      dsimp [j]
      rw [hlen] at hi
      omega
    have hnext : p.points.length - 1 + j + 1 = p.points.length + j := by omega
    have hjrev : j + 1 < q.reverse.points.length := by
      simpa [Polyline.reverse, List.length_reverse] using hj
    rw [hidx, point_closedConcat_right_edge p q hfinish j hj, hnext,
      point_closedConcat_right p q j hj]
    exact (isSimple_reverse_transfer q hq).1 j hjrev




















































end Polyline
end DirectedDistances.PlanarMap

end
