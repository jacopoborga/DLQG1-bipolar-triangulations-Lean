/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents3

/-! # Closed subwalk extraction toward face-orbit identification

Helpers toward Proposition 5.16. The extraction below retains a possible
one-edge or two-edge return; a bridge traversal must not be called a Jordan -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

namespace Polyline

/-- Helper toward Proposition 5.16: the contiguous chain of `n` segments
starting at vertex `i`. Index bounds are imposed by the containment lemmas. -/
@[expose] def intervalPolyline (c : Polyline) (i n : ℕ) : Polyline :=
  ⟨List.ofFn (fun k : Fin (n + 1) => c.point (i + k.val)), by simp⟩

/-- Helper toward Proposition 5.16: an interval chain has `n + 1` vertices. -/
@[simp] theorem length_intervalPolyline (c : Polyline) (i n : ℕ) :
    (c.intervalPolyline i n).points.length = n + 1 := by
  simp only [intervalPolyline, List.length_ofFn]

/-- Helper toward Proposition 5.16: in-range vertices retain their original
indices after extracting a contiguous subwalk. -/
theorem point_intervalPolyline (c : Polyline) (i n k : ℕ) (hk : k ≤ n) :
    (c.intervalPolyline i n).point k = c.point (i + k) := by
  change (List.ofFn (fun t : Fin (n + 1) => c.point (i + t.val)))[k]?.getD _ = _
  have hk' : k < (List.ofFn (fun t : Fin (n + 1) => c.point (i + t.val))).length := by
    simpa only [List.length_ofFn] using Nat.lt_succ_of_le hk
  rw [List.getElem?_eq_getElem hk', Option.getD_some, List.getElem_ofFn]

/-- Helper toward Proposition 5.16: the extracted chain starts at vertex `i`. -/
@[simp] theorem start_intervalPolyline (c : Polyline) (i n : ℕ) :
    (c.intervalPolyline i n).start = c.point i := by
  rw [← point_zero_eq_start, point_intervalPolyline c i n 0 (Nat.zero_le n)]
  simp only [Nat.add_zero]

/-- Helper toward Proposition 5.16: the extracted chain ends at vertex `i+n`. -/
@[simp] theorem finish_intervalPolyline (c : Polyline) (i n : ℕ) :
    (c.intervalPolyline i n).finish = c.point (i + n) := by
  rw [← point_last_eq_finish, length_intervalPolyline, Nat.add_sub_cancel]
  exact c.point_intervalPolyline i n n le_rfl

/-- Helper toward Proposition 5.16: every segment in an extracted chain
is exactly the corresponding segment in the original chain. -/
theorem segmentAt_intervalPolyline (c : Polyline) (i n k : ℕ) (hk : k < n) :
    (c.intervalPolyline i n).segmentAt k = c.segmentAt (i + k) := by
  simp only [segmentAt, point_intervalPolyline c i n k (by omega),
    point_intervalPolyline c i n (k + 1) (by omega), Nat.add_assoc]

/-- Helper toward Proposition 5.16: an in-range contiguous subwalk has
image contained in the original closed walk, including both endpoints. -/
theorem image_intervalPolyline_subset (c : Polyline) (i n : ℕ)
    (hbound : i + n < c.points.length) :
    (c.intervalPolyline i n).image ⊆ c.image := by
  rintro z (hz | ⟨k, hk, hz⟩)
  · rw [mem_singleton_iff, start_intervalPolyline] at hz
    exact hz ▸ c.point_mem_image (by omega)
  · rw [length_intervalPolyline] at hk
    rw [segmentAt_intervalPolyline c i n k (by omega)] at hz
    exact c.segmentAt_subset_image (by omega) hz

/-- Helper toward Proposition 5.16: an interval chain retains each original
signed edge angle, with the same orientation. -/
theorem edgeAngle_intervalPolyline (c : Polyline) (z : ℂ) (i n k : ℕ)
    (hk : k < n) :
    (c.intervalPolyline i n).edgeAngle z k = c.edgeAngle z (i + k) := by
  simp only [edgeAngle, point_intervalPolyline c i n k (by omega),
    point_intervalPolyline c i n (k + 1) (by omega), Nat.add_assoc]

/-- Helper toward Proposition 5.16: winding sums add when a contiguous
chain is split at any vertex; this also allows either piece to be constant. -/
theorem angleSum_intervalPolyline_add (c : Polyline) (z : ℂ) (i m n : ℕ) :
    (c.intervalPolyline i (m + n)).angleSum z =
      (c.intervalPolyline i m).angleSum z +
        (c.intervalPolyline (i + m) n).angleSum z := by
  simp only [angleSum, length_intervalPolyline, Nat.add_sub_cancel]
  rw [Finset.sum_range_add]
  have hleft :
      (∑ k ∈ Finset.range m, (c.intervalPolyline i (m + n)).edgeAngle z k) =
        ∑ k ∈ Finset.range m, (c.intervalPolyline i m).edgeAngle z k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [edgeAngle_intervalPolyline c z i (m + n) k (by omega),
      edgeAngle_intervalPolyline c z i m k hk']
  have hright :
      (∑ k ∈ Finset.range n, (c.intervalPolyline i (m + n)).edgeAngle z (m + k)) =
        ∑ k ∈ Finset.range n, (c.intervalPolyline (i + m) n).edgeAngle z k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [edgeAngle_intervalPolyline c z i (m + n) (m + k) (by omega),
      edgeAngle_intervalPolyline c z (i + m) n k hk', Nat.add_assoc]
  rw [hleft, hright, add_div]

/-- Helper toward Proposition 5.16: taking the whole in-range vertex
interval leaves the signed winding sum unchanged. -/
theorem angleSum_intervalPolyline_all (c : Polyline) (z : ℂ) :
    (c.intervalPolyline 0 (c.points.length - 1)).angleSum z = c.angleSum z := by
  simp only [angleSum, length_intervalPolyline, Nat.add_sub_cancel]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [edgeAngle_intervalPolyline c z 0 (c.points.length - 1) k
    (Finset.mem_range.mp hk), Nat.zero_add]

/-- Helper toward Proposition 5.16: joining chains adds their edge counts,
including when either chain consists of a single vertex. -/
theorem length_boundaryConcat (p q : Polyline) :
    (boundaryConcat p q).points.length = p.points.length + q.points.length - 1 := by
  have hq : 0 < q.points.length := List.length_pos_iff.mpr q.nonempty
  simp only [boundaryConcat, List.length_append, List.length_tail]
  omega

/-- Helper toward Proposition 5.16: concatenation retains every vertex
of its first chain. -/
theorem point_boundaryConcat_left (p q : Polyline) (k : ℕ)
    (hk : k < p.points.length) : (boundaryConcat p q).point k = p.point k := by
  change (p.points ++ q.points.tail).getD k (boundaryConcat p q).start =
    p.points.getD k p.start
  rw [List.getD_append _ _ _ _ hk, start_boundaryConcat]

/-- Helper toward Proposition 5.16: vertices following the join retain
their indices in the second chain. -/
theorem point_boundaryConcat_right_succ (p q : Polyline) (k : ℕ)
    (hk : k + 1 < q.points.length) :
    (boundaryConcat p q).point (p.points.length + k) = q.point (k + 1) := by
  change (p.points ++ q.points.tail).getD (p.points.length + k)
      (boundaryConcat p q).start = q.points.getD (k + 1) q.start
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  cases h : q.points with
  | nil => exact (q.nonempty h).elim
  | cons a l =>
      have hk' : k < l.length := by simp only [h, List.length_cons] at hk; omega
      change l.getD (p.points.length + k - p.points.length) (boundaryConcat p q).start =
        (a :: l).getD (k + 1) q.start
      rw [Nat.add_sub_cancel_left, List.getD_cons_succ,
        List.getD_eq_getElem (l := l) (d := (boundaryConcat p q).start) hk',
        List.getD_eq_getElem (l := l) (d := q.start) hk']

/-- Helper toward Proposition 5.16: the common join vertex is also the
zeroth vertex of the second chain, so its entire index range is retained. -/
theorem point_boundaryConcat_right (p q : Polyline) (hjoin : p.finish = q.start)
    (k : ℕ) (hk : k < q.points.length) :
    (boundaryConcat p q).point (p.points.length - 1 + k) = q.point k := by
  have hp : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
  cases k with
  | zero =>
      rw [Nat.add_zero, point_boundaryConcat_left p q _ (by omega),
        point_last_eq_finish, hjoin, point_zero_eq_start]
  | succ k =>
      rw [show p.points.length - 1 + (k + 1) = p.points.length + k by omega]
      exact point_boundaryConcat_right_succ p q k hk

/-- Helper toward Proposition 5.16: a compatible concatenation ends at
the end of its second chain, also for a constant second chain. -/
theorem finish_boundaryConcat_of_join (p q : Polyline) (hjoin : p.finish = q.start) :
    (boundaryConcat p q).finish = q.finish := by
  have hp : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
  have hq : 0 < q.points.length := List.length_pos_iff.mpr q.nonempty
  rw [← point_last_eq_finish, length_boundaryConcat]
  rw [show p.points.length + q.points.length - 1 - 1 =
    p.points.length - 1 + (q.points.length - 1) by omega]
  rw [point_boundaryConcat_right p q hjoin _ (by omega), point_last_eq_finish]

/-- Helper toward Proposition 5.16: winding sums add across a compatible
join. Repeated vertices and reversed bridge traversals are allowed. -/
theorem angleSum_boundaryConcat (p q : Polyline) (hjoin : p.finish = q.start)
    (z : ℂ) : (boundaryConcat p q).angleSum z = p.angleSum z + q.angleSum z := by
  have hp : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
  have hq : 0 < q.points.length := List.length_pos_iff.mpr q.nonempty
  simp only [angleSum, length_boundaryConcat]
  rw [show p.points.length + q.points.length - 1 - 1 =
    (p.points.length - 1) + (q.points.length - 1) by omega, Finset.sum_range_add]
  have hleft : (∑ k ∈ Finset.range (p.points.length - 1),
      (boundaryConcat p q).edgeAngle z k) =
      ∑ k ∈ Finset.range (p.points.length - 1), p.edgeAngle z k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [edgeAngle, point_boundaryConcat_left p q k (by omega),
      point_boundaryConcat_left p q (k + 1) (by omega)]
  have hright : (∑ k ∈ Finset.range (q.points.length - 1),
      (boundaryConcat p q).edgeAngle z (p.points.length - 1 + k)) =
      ∑ k ∈ Finset.range (q.points.length - 1), q.edgeAngle z k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [edgeAngle,
      show p.points.length - 1 + k + 1 = p.points.length - 1 + (k + 1) by omega,
      point_boundaryConcat_right p q hjoin k (by omega),
      point_boundaryConcat_right p q hjoin (k + 1) (by omega)]
  rw [hleft, hright, add_div]

/-- Helper toward Proposition 5.16: a closed walk of at most two edges
has zero winding away from its image. In particular, traversing a bridge
and immediately returning cannot supply a separating polygon. -/
theorem angleSum_eq_zero_of_length_le_three (c : Polyline)
    (hlen : c.points.length ≤ 3) (hclosed : c.start = c.finish)
    (z : ℂ) (hz : z ∉ c.image) : c.angleSum z = 0 := by
  have hpos : 0 < c.points.length := List.length_pos_iff.mpr c.nonempty
  have hlen' : c.points.length = 1 ∨ c.points.length = 2 ∨ c.points.length = 3 := by omega
  rcases hlen' with h1 | h2 | h3
  · simp only [angleSum, h1, Nat.sub_self, Finset.range_zero, Finset.sum_empty,
      zero_div]
  · have hpt : c.point 1 = c.point 0 := by
      rw [point_zero_eq_start, hclosed, ← point_last_eq_finish, h2]
    have hne : c.point 0 - z ≠ 0 := sub_ne_zero.mpr fun h =>
      hz (h ▸ c.point_mem_image (by omega))
    simp only [angleSum, h2, Nat.add_one_sub_one, Finset.sum_range_one,
      edgeAngle, zero_add, hpt, div_self hne, Complex.arg_one, zero_div]
  · have hpt : c.point 2 = c.point 0 := by
      rw [point_zero_eq_start, hclosed, ← point_last_eq_finish, h3]
    have hang : c.edgeAngle z 0 ≠ Real.pi :=
      ne_of_lt (c.edgeAngle_mem_Ioo z 0 (by omega) hz).2
    have hinv : c.edgeAngle z 1 = -c.edgeAngle z 0 := by
      change Complex.arg ((c.point 2 - z) / (c.point 1 - z)) = _
      rw [hpt, ← inv_div, Complex.arg_inv]
      change (if c.edgeAngle z 0 = Real.pi then Real.pi else -c.edgeAngle z 0) = _
      rw [ite_eq_right hang]
    simp only [angleSum, h3, Nat.reduceSub, Finset.sum_range_succ,
      Finset.range_zero, Finset.sum_empty, zero_add, hinv, add_neg_cancel, zero_div]

/-- Helper toward Proposition 5.16: extraction of an interval preserves
any condition on the ordered endpoints of each segment. -/
theorem edges_intervalPolyline (c : Polyline) (R : ℂ → ℂ → Prop)
    (hR : ∀ k, k + 1 < c.points.length → R (c.point k) (c.point (k + 1)))
    (i n : ℕ) (hbound : i + n < c.points.length) :
    ∀ k, k + 1 < (c.intervalPolyline i n).points.length →
      R ((c.intervalPolyline i n).point k) ((c.intervalPolyline i n).point (k + 1)) := by
  intro k hk
  rw [length_intervalPolyline] at hk
  rw [point_intervalPolyline c i n k (by omega),
    point_intervalPolyline c i n (k + 1) (by omega), ← Nat.add_assoc]
  exact hR (i + k) (by omega)

/-- Helper toward Proposition 5.16: a compatible join introduces no -/
theorem edges_boundaryConcat (p q : Polyline) (hjoin : p.finish = q.start)
    (R : ℂ → ℂ → Prop)
    (hpR : ∀ k, k + 1 < p.points.length → R (p.point k) (p.point (k + 1)))
    (hqR : ∀ k, k + 1 < q.points.length → R (q.point k) (q.point (k + 1))) :
    ∀ k, k + 1 < (boundaryConcat p q).points.length →
      R ((boundaryConcat p q).point k) ((boundaryConcat p q).point (k + 1)) := by
  intro k hk
  by_cases hleft : k + 1 < p.points.length
  · rw [point_boundaryConcat_left p q k (by omega),
      point_boundaryConcat_left p q (k + 1) hleft]
    exact hpR k hleft
  · have hp : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    have hq : 0 < q.points.length := List.length_pos_iff.mpr q.nonempty
    rw [length_boundaryConcat] at hk
    let j := k - (p.points.length - 1)
    have hidx : k = p.points.length - 1 + j := by dsimp [j]; omega
    have hj : j + 1 < q.points.length := by dsimp [j]; omega
    rw [hidx, point_boundaryConcat_right p q hjoin j (by omega),
      show p.points.length - 1 + j + 1 = p.points.length - 1 + (j + 1) by omega,
      point_boundaryConcat_right p q hjoin (j + 1) hj]
    exact hqR j hj

/-- Helper toward Proposition 5.16: the first repeated vertex in a finite
nontrivial closed walk gives a return interval whose preceding vertices
are pairwise distinct. This does not yet exclude a reversed bridge. -/
theorem exists_first_return_interval (c : Polyline)
    (hlen : 2 ≤ c.points.length) (hclosed : c.start = c.finish) :
    ∃ i j : ℕ, i < j ∧ j < c.points.length ∧ c.point i = c.point j ∧
      ∀ a b : ℕ, a < j → b < j → c.point a = c.point b → a = b := by
  classical
  have hex : ∃ j : ℕ, j < c.points.length ∧ ∃ i < j, c.point i = c.point j := by
    refine ⟨c.points.length - 1, by omega, 0, by omega, ?_⟩
    rw [point_zero_eq_start, point_last_eq_finish]
    exact hclosed
  let j := Nat.find hex
  obtain ⟨hj, i, hij, heq⟩ := Nat.find_spec hex
  refine ⟨i, j, hij, hj, heq, ?_⟩
  intro a b ha hb hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hmin := Nat.find_min' hex (show b < c.points.length ∧
        ∃ i < b, c.point i = c.point b from ⟨by omega, a, hlt, hab⟩)
    omega
  · exact heq
  · have hmin := Nat.find_min' hex (show a < c.points.length ∧
        ∃ i < a, c.point i = c.point a from ⟨by omega, b, hgt, hab.symm⟩)
    omega

/-- Helper toward Proposition 5.16: extract an actual closed sub-polyline
with distinct vertices before its closing endpoint. Its image remains in
the original walk; no simplicity of its segment intersections is asserted. -/
theorem exists_closed_intervalPolyline (c : Polyline)
    (hlen : 2 ≤ c.points.length) (hclosed : c.start = c.finish) :
    ∃ i n : ℕ, 0 < n ∧ i + n < c.points.length ∧
      (c.intervalPolyline i n).start = (c.intervalPolyline i n).finish ∧
      (c.intervalPolyline i n).image ⊆ c.image ∧
      ∀ a b : ℕ, a < n → b < n →
        (c.intervalPolyline i n).point a = (c.intervalPolyline i n).point b → a = b := by
  obtain ⟨i, j, hij, hj, heq, hinj⟩ := c.exists_first_return_interval hlen hclosed
  have hsum : i + (j - i) = j := Nat.add_sub_of_le hij.le
  refine ⟨i, j - i, by omega, by omega, ?_,
    c.image_intervalPolyline_subset i (j - i) (by omega), ?_⟩
  · rw [start_intervalPolyline, finish_intervalPolyline, hsum]
    exact heq
  · intro a b ha hb hab
    rw [point_intervalPolyline c i (j - i) a (by omega),
      point_intervalPolyline c i (j - i) b (by omega)] at hab
    have := hinj (i + a) (i + b) (by omega) (by omega) hab
    omega

/-- Helper toward Proposition 5.16: a closed walk with nonzero winding
contains a closed polygonal walk with nonzero winding, at least three
edges, and no repeated vertex before its closing endpoint. Shortcuts remove
zero-winding returns; the resulting image stays in the original image.
Segment-intersection simplicity is a separate geometric obligation. -/
theorem exists_closed_vertex_injective_preserving_edges (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) (hz : z ∉ c.image)
    (hangle : c.angleSum z ≠ 0) (R : ℂ → ℂ → Prop)
    (hR : ∀ k, k + 1 < c.points.length → R (c.point k) (c.point (k + 1))) :
    ∃ q : Polyline, q.start = q.finish ∧ q.image ⊆ c.image ∧
      q.angleSum z ≠ 0 ∧ 4 ≤ q.points.length ∧
      (∀ a b : ℕ, a < q.points.length - 1 → b < q.points.length - 1 →
        q.point a = q.point b → a = b) ∧
      ∀ k, k + 1 < q.points.length → R (q.point k) (q.point (k + 1)) := by
  classical
  suffices h : ∀ n : ℕ, ∀ p : Polyline, p.points.length = n →
      p.start = p.finish → z ∉ p.image → p.angleSum z ≠ 0 →
      (∀ k, k + 1 < p.points.length → R (p.point k) (p.point (k + 1))) →
      ∃ q : Polyline, q.start = q.finish ∧ q.image ⊆ p.image ∧
        q.angleSum z ≠ 0 ∧ 4 ≤ q.points.length ∧
        (∀ a b : ℕ, a < q.points.length - 1 → b < q.points.length - 1 →
          q.point a = q.point b → a = b) ∧
        ∀ k, k + 1 < q.points.length → R (q.point k) (q.point (k + 1)) from
    h c.points.length c rfl hclosed hz hangle hR
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hlen hpclosed hzp hpangle hpR
    by_cases hinj : ∀ a b : ℕ, a < p.points.length - 1 → b < p.points.length - 1 →
        p.point a = p.point b → a = b
    · refine ⟨p, hpclosed, Subset.rfl, hpangle, ?_, hinj, hpR⟩
      by_contra hsmall
      exact hpangle (p.angleSum_eq_zero_of_length_le_three (by omega) hpclosed z hzp)
    · push Not at hinj
      obtain ⟨a, b, ha, hb, hab, hne⟩ := hinj
      have hrepeat : ∃ i j : ℕ, i < j ∧ j < p.points.length - 1 ∧ p.point i = p.point j := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨a, b, hlt, hb, hab⟩
        · exact ⟨b, a, hgt, ha, hab.symm⟩
      obtain ⟨i, j, hij, hj, heq⟩ := hrepeat
      let N := p.points.length - 1
      have hp : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
      have hsum : i + (j - i) = j := Nat.add_sub_of_le hij.le
      have hlast : j + (N - j) = N := Nat.add_sub_of_le (by dsimp [N]; omega)
      let l := p.intervalPolyline 0 i
      let r := p.intervalPolyline i (j - i)
      let t := p.intervalPolyline j (N - j)
      let s := boundaryConcat l t
      have hjoin : l.finish = t.start := by
        dsimp [l, t]
        rw [finish_intervalPolyline, start_intervalPolyline, Nat.zero_add]
        exact heq
      have hrclosed : r.start = r.finish := by
        dsimp [r]
        rw [start_intervalPolyline, finish_intervalPolyline, hsum]
        exact heq
      have hsclosed : s.start = s.finish := by
        dsimp [s]
        rw [start_boundaryConcat, finish_boundaryConcat_of_join l t hjoin]
        dsimp [l, t]
        rw [start_intervalPolyline, finish_intervalPolyline, hlast,
          point_zero_eq_start, point_last_eq_finish]
        exact hpclosed
      have hrimage : r.image ⊆ p.image :=
        p.image_intervalPolyline_subset i (j - i) (by omega)
      have hsimage : s.image ⊆ p.image := by
        dsimp [s]
        rw [image_boundaryConcat l t hjoin]
        exact union_subset
          (p.image_intervalPolyline_subset 0 i (by omega))
          (p.image_intervalPolyline_subset j (N - j) (by dsimp [N] at hlast ⊢; omega))
      have hrR : ∀ k, k + 1 < r.points.length → R (r.point k) (r.point (k + 1)) :=
        p.edges_intervalPolyline R hpR i (j - i) (by omega)
      have hsR : ∀ k, k + 1 < s.points.length → R (s.point k) (s.point (k + 1)) :=
        edges_boundaryConcat l t hjoin R
          (p.edges_intervalPolyline R hpR 0 i (by omega))
          (p.edges_intervalPolyline R hpR j (N - j) (by dsimp [N] at hlast ⊢; omega))
      have hrlen : r.points.length < n := by
        dsimp [r]
        rw [length_intervalPolyline]
        omega
      have hslen : s.points.length < n := by
        dsimp [s]
        rw [length_boundaryConcat]
        dsimp [l, t]
        rw [length_intervalPolyline, length_intervalPolyline]
        dsimp [N]
        omega
      have hdecomp : p.angleSum z = l.angleSum z + (r.angleSum z + t.angleSum z) := by
        calc
          p.angleSum z =
              (p.intervalPolyline 0 (i + ((j - i) + (N - j)))).angleSum z := by
            rw [show i + ((j - i) + (N - j)) = p.points.length - 1 by
              dsimp [N]; omega]
            exact (p.angleSum_intervalPolyline_all z).symm
          _ = l.angleSum z + (r.angleSum z + t.angleSum z) := by
            dsimp [l, r, t]
            rw [angleSum_intervalPolyline_add, Nat.zero_add,
              angleSum_intervalPolyline_add, hsum]
      have hsangle : s.angleSum z = l.angleSum z + t.angleSum z :=
        angleSum_boundaryConcat l t hjoin z
      by_cases hrangle : r.angleSum z = 0
      · have hsne : s.angleSum z ≠ 0 := by
          intro hzero
          apply hpangle
          linarith only [hdecomp, hsangle, hrangle, hzero]
        obtain ⟨q, hqc, hqi, hqa, hql, hqv, hqR⟩ :=
          ih s.points.length hslen s rfl hsclosed (fun h => hzp (hsimage h)) hsne hsR
        exact ⟨q, hqc, hqi.trans hsimage, hqa, hql, hqv, hqR⟩
      · obtain ⟨q, hqc, hqi, hqa, hql, hqv, hqR⟩ :=
          ih r.points.length hrlen r rfl hrclosed (fun h => hzp (hrimage h)) hrangle hrR
        exact ⟨q, hqc, hqi.trans hrimage, hqa, hql, hqv, hqR⟩

/-- Helper toward Proposition 5.16: nonzero winding yields a closed walk
with at least three edges and no repeated vertex before closure, contained
in the original image. This does not assert segment-intersection simplicity. -/
theorem exists_closed_vertex_injective_of_angleSum_ne_zero (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) (hz : z ∉ c.image)
    (hangle : c.angleSum z ≠ 0) :
    ∃ q : Polyline, q.start = q.finish ∧ q.image ⊆ c.image ∧
      q.angleSum z ≠ 0 ∧ 4 ≤ q.points.length ∧
      ∀ a b : ℕ, a < q.points.length - 1 → b < q.points.length - 1 →
        q.point a = q.point b → a = b := by
  obtain ⟨q, hqc, hqi, hqa, hql, hqv, _⟩ :=
    c.exists_closed_vertex_injective_preserving_edges hclosed z hz hangle
      (fun _ _ => True) (fun _ _ => trivial)
  exact ⟨q, hqc, hqi, hqa, hql, hqv⟩

/-- Helper toward Proposition 5.16: loop erasure can retain the exact
ordered endpoints of original segments, rather than only image containment. -/
theorem exists_closed_vertex_injective_with_segment_sources (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) (hz : z ∉ c.image)
    (hangle : c.angleSum z ≠ 0) :
    ∃ q : Polyline, q.start = q.finish ∧ q.image ⊆ c.image ∧
      q.angleSum z ≠ 0 ∧ 4 ≤ q.points.length ∧
      (∀ a b : ℕ, a < q.points.length - 1 → b < q.points.length - 1 →
        q.point a = q.point b → a = b) ∧
      ∀ k, k + 1 < q.points.length → ∃ i, i + 1 < c.points.length ∧
        q.point k = c.point i ∧ q.point (k + 1) = c.point (i + 1) := by
  exact c.exists_closed_vertex_injective_preserving_edges hclosed z hz hangle
    (fun a b => ∃ i, i + 1 < c.points.length ∧ a = c.point i ∧ b = c.point (i + 1))
    (fun k hk => ⟨k, hk, rfl, rfl⟩)

/-- Helper toward Proposition 5.16: different segments of a simple arc
can meet only at endpoints of both segments. -/
theorem segmentAt_intersection_endpoints (p : Polyline) (hp : p.IsSimple)
    (i j : ℕ) (hi : i + 1 < p.points.length) (hj : j + 1 < p.points.length)
    (hne : i ≠ j) {z : ℂ} (hzi : z ∈ p.segmentAt i) (hzj : z ∈ p.segmentAt j) :
    (z = p.point i ∨ z = p.point (i + 1)) ∧
      (z = p.point j ∨ z = p.point (j + 1)) := by
  have hforward : ∀ a b : ℕ, a + 1 < p.points.length → b + 1 < p.points.length →
      a < b → z ∈ p.segmentAt a → z ∈ p.segmentAt b → z = p.point (a + 1) ∧ b = a + 1 := by
    intro a b ha hb hab hza hzb
    by_cases hadj : b = a + 1
    · subst b
      have hz : z ∈ ({p.point (a + 1)} : Set ℂ) := by
        rw [← hp.2.1 a (by omega)]
        exact ⟨hza, hzb⟩
      exact ⟨hz, rfl⟩
    · exact ((Set.disjoint_left.mp (hp.2.2 a b ha hb (by omega))) hza hzb).elim
  rcases lt_or_gt_of_ne hne with hij | hji
  · obtain ⟨hz, hidx⟩ := hforward i j hi hj hij hzi hzj
    exact ⟨Or.inr hz, Or.inl (hidx ▸ hz)⟩
  · obtain ⟨hz, hidx⟩ := hforward j i hj hi hji hzj hzi
    exact ⟨Or.inl (hidx ▸ hz), Or.inr hz⟩

/-- Helper toward Proposition 5.16: if an endpoint of a simple arc lies
on an arc segment, it is an endpoint of that particular segment. -/
theorem segmentAt_endpoint_of_arc_endpoint (p : Polyline) (hp : p.IsSimple)
    (hlen : 2 ≤ p.points.length) (i : ℕ) (hi : i + 1 < p.points.length)
    {z : ℂ} (hz : z ∈ p.segmentAt i) (hend : z = p.start ∨ z = p.finish) :
    z = p.point i ∨ z = p.point (i + 1) := by
  rcases hend with rfl | rfl
  · have hidx := p.segmentAt_index_eq_zero_of_start_mem hp hlen hi hz
    exact Or.inl (by rw [hidx, point_zero_eq_start])
  · have hidx := p.segmentAt_index_last_of_finish_mem hp hlen hi hz
    exact Or.inr (by rw [show i + 1 = p.points.length - 1 by omega,
      point_last_eq_finish])

/-- Helper toward Proposition 5.16: vertex injectivity before closure
identifies exactly the two endpoint indices in a closed chain. -/
theorem point_eq_iff_of_closed_vertex_injective (c : Polyline)
    (hlen : 2 ≤ c.points.length) (hclosed : c.start = c.finish)
    (hinj : ∀ a b, a < c.points.length - 1 → b < c.points.length - 1 →
      c.point a = c.point b → a = b)
    (a b : ℕ) (ha : a < c.points.length) (hb : b < c.points.length) :
    c.point a = c.point b ↔ a = b ∨
      (a = 0 ∧ b = c.points.length - 1) ∨ (a = c.points.length - 1 ∧ b = 0) := by
  have hend : c.point 0 = c.point (c.points.length - 1) := by
    rw [point_zero_eq_start, point_last_eq_finish]
    exact hclosed
  constructor
  · intro hab
    by_cases ha' : a < c.points.length - 1
    · by_cases hb' : b < c.points.length - 1
      · exact Or.inl (hinj a b ha' hb' hab)
      · have hbidx : b = c.points.length - 1 := by omega
        have haidx : a = 0 := hinj a 0 ha' (by omega) (by rwa [hbidx, ← hend] at hab)
        exact Or.inr (Or.inl ⟨haidx, hbidx⟩)
    · have haidx : a = c.points.length - 1 := by omega
      by_cases hb' : b < c.points.length - 1
      · have hbidx : b = 0 := hinj b 0 hb' (by omega)
          (by rw [haidx, ← hend] at hab; exact hab.symm)
        exact Or.inr (Or.inr ⟨haidx, hbidx⟩)
      · exact Or.inl (by omega)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact hend
    · exact hend.symm

/-- Helper toward Proposition 5.16: a vertex-simple closed chain is a
simple polygon once distinct segments meet only at endpoints of both.
This explicitly isolates the geometric check needed after loop erasure. -/
theorem isCyclicSimple_of_vertex_injective_of_segment_endpoints (c : Polyline)
    (hlen : 4 ≤ c.points.length) (hclosed : c.start = c.finish)
    (hinj : ∀ a b, a < c.points.length - 1 → b < c.points.length - 1 →
      c.point a = c.point b → a = b)
    (hmeet : ∀ i j, i + 1 < c.points.length → j + 1 < c.points.length → i ≠ j →
      ∀ z, z ∈ c.segmentAt i → z ∈ c.segmentAt j →
        (z = c.point i ∨ z = c.point (i + 1)) ∧
        (z = c.point j ∨ z = c.point (j + 1))) : c.IsCyclicSimple := by
  have heq := c.point_eq_iff_of_closed_vertex_injective (by omega) hclosed hinj
  have hend : c.point 0 = c.point (c.points.length - 1) := by
    rw [point_zero_eq_start, point_last_eq_finish]
    exact hclosed
  refine ⟨hlen, hend, ?_, ?_, ?_, ?_⟩
  · intro i hi hab
    have := (heq i (i + 1) (by omega) hi).mp hab
    omega
  · intro i hi
    apply Set.Subset.antisymm
    · rintro z ⟨hzi, hzj⟩
      obtain ⟨hz, hw⟩ := hmeet i (i + 1) (by omega) hi (by omega) z hzi hzj
      rcases hz with hz | hz
      · rcases hw with hw | hw
        · have := (heq i (i + 1) (by omega) (by omega)).mp (hz.symm.trans hw)
          omega
        · have := (heq i (i + 1 + 1) (by omega) (by omega)).mp (hz.symm.trans hw)
          omega
      · exact hz
    · rintro z rfl
      exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · intro i j hi hj hij hwrap
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨hz, hw⟩ := hmeet i j hi hj (by omega) z hzi hzj
    rcases hz with hz | hz <;> rcases hw with hw | hw
    all_goals
      have h := hz.symm.trans hw
      have hh := (heq _ _ (by omega) (by omega)).mp h
      omega
  · apply Set.Subset.antisymm
    · rintro z ⟨hzi, hzj⟩
      obtain ⟨hz, hw⟩ := hmeet 0 (c.points.length - 2) (by omega) (by omega)
        (by omega) z hzi hzj
      rcases hz with hz | hz
      · exact hz
      · rcases hw with hw | hw
        · have := (heq 1 (c.points.length - 2) (by omega) (by omega)).mp (hz.symm.trans hw)
          omega
        · have := (heq 1 (c.points.length - 2 + 1) (by omega) (by omega)).mp (hz.symm.trans hw)
          omega
    · rintro z rfl
      refine ⟨left_mem_segment ℝ _ _, ?_⟩
      change c.point 0 ∈ segment ℝ _ _
      rw [show c.points.length - 2 + 1 = c.points.length - 1 by omega, ← hend]
      exact right_mem_segment ℝ _ _

end Polyline

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: different geometric edges of a PL
drawing intersect only at endpoints of both arcs. Multiedge identities are
retained by explicitly excluding both orientations of one edge. -/
theorem arc_intersection_endpoints (d e : D) (hne : e ≠ d) (hflip : e ≠ flip d)
    {z : ℂ} (hzd : z ∈ (P.arc d).image) (hze : z ∈ (P.arc e).image) :
    (z = (P.arc d).start ∨ z = (P.arc d).finish) ∧
      (z = (P.arc e).start ∨ z = (P.arc e).finish) := by
  have hnotint : ∀ a b : D, (z = (P.arc a).start ∨ z = (P.arc a).finish) →
      z ∉ (P.arc b).interior := by
    intro a b hend
    rcases hend with hz | hz
    · rw [P.arc_start] at hz
      exact hz ▸ P.interior_avoids_vertices b (vert a)
    · rw [P.arc_finish] at hz
      exact hz ▸ P.interior_avoids_vertices b (vert (flip a))
  have hd : z = (P.arc d).start ∨ z = (P.arc d).finish := by
    by_contra h
    have hdi : z ∈ (P.arc d).interior :=
      ⟨hzd, by simpa only [mem_insert_iff, mem_singleton_iff] using h⟩
    by_cases he : z = (P.arc e).start ∨ z = (P.arc e).finish
    · exact hnotint e d he hdi
    · have hei : z ∈ (P.arc e).interior :=
        ⟨hze, by simpa only [mem_insert_iff, mem_singleton_iff] using he⟩
      exact (Set.disjoint_left.mp (P.interior_disjoint d e hne hflip)) hdi hei
  refine ⟨hd, ?_⟩
  by_contra he
  exact hnotint d e hd ⟨hze, by simpa only [mem_insert_iff, mem_singleton_iff] using he⟩

/-- Helper toward Proposition 5.16: segments from distinct geometric
edges can meet only at endpoints of both segments, including at bends. -/
theorem arc_segment_intersection_endpoints (d e : D) (hne : e ≠ d)
    (hflip : e ≠ flip d) (i j : ℕ)
    (hi : i + 1 < (P.arc d).points.length) (hj : j + 1 < (P.arc e).points.length)
    {z : ℂ} (hzi : z ∈ (P.arc d).segmentAt i) (hzj : z ∈ (P.arc e).segmentAt j) :
    (z = (P.arc d).point i ∨ z = (P.arc d).point (i + 1)) ∧
      (z = (P.arc e).point j ∨ z = (P.arc e).point (j + 1)) := by
  obtain ⟨hd, he⟩ := P.arc_intersection_endpoints d e hne hflip
    ((P.arc d).segmentAt_subset_image hi hzi) ((P.arc e).segmentAt_subset_image hj hzj)
  exact ⟨(P.arc d).segmentAt_endpoint_of_arc_endpoint (P.arc_simple d)
    (P.arc_length d) i hi hzi hd,
    (P.arc e).segmentAt_endpoint_of_arc_endpoint (P.arc_simple e)
      (P.arc_length e) j hj hzj he⟩

/-- Helper toward Proposition 5.16: a vertex-simple closed chain assembled
from actual drawing segments is geometrically cyclically simple. This uses
the edge identity, reversal and disjoint-interior fields of the PL drawing. -/
theorem isCyclicSimple_of_arc_segment_sources (c : Polyline)
    (hlen : 4 ≤ c.points.length) (hclosed : c.start = c.finish)
    (hinj : ∀ a b, a < c.points.length - 1 → b < c.points.length - 1 →
      c.point a = c.point b → a = b)
    (hsource : ∀ k, k + 1 < c.points.length → ∃ d : D, ∃ a : ℕ,
      a + 1 < (P.arc d).points.length ∧ c.point k = (P.arc d).point a ∧
        c.point (k + 1) = (P.arc d).point (a + 1)) : c.IsCyclicSimple := by
  apply c.isCyclicSimple_of_vertex_injective_of_segment_endpoints hlen hclosed hinj
  intro i j hi hj hij z hzi hzj
  obtain ⟨d, a, ha, hia, hia1⟩ := hsource i hi
  obtain ⟨e, b, hb, hjb, hjb1⟩ := hsource j hj
  have hza : z ∈ (P.arc d).segmentAt a := by
    simpa only [Polyline.segmentAt, hia, hia1] using hzi
  have hzb : z ∈ (P.arc e).segmentAt b := by
    simpa only [Polyline.segmentAt, hjb, hjb1] using hzj
  by_cases hed : e = d
  · subst e
    have hab : a ≠ b := by
      intro hab
      have heq : c.point i = c.point j := by rw [hia, hjb, hab]
      exact hij (hinj i j (by omega) (by omega) heq)
    rw [hia, hia1, hjb, hjb1]
    exact (P.arc d).segmentAt_intersection_endpoints (P.arc_simple d) a b ha hb hab hza hzb
  by_cases hef : e = flip d
  · subst e
    rw [P.arc_flip] at hb hjb hjb1 hzb
    have hb' : b + 1 < (P.arc d).points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hb
    let b' := (P.arc d).points.length - 2 - b
    have hb'valid : b' + 1 < (P.arc d).points.length := by dsimp [b']; omega
    have hjrev : c.point j = (P.arc d).point (b' + 1) := by
      rw [hjb, Polyline.point_reverse_transfer _ (by omega)]
      congr 1
      dsimp [b']; omega
    have hjrev1 : c.point (j + 1) = (P.arc d).point b' := by
      rw [hjb1, Polyline.point_reverse_transfer _ hb']
      congr 1
      dsimp [b']; omega
    rw [Polyline.segmentAt_reverse_transfer _ hb'] at hzb
    have hab : a ≠ b' := by
      intro hab
      have heq1 : c.point i = c.point (j + 1) := by rw [hia, hjrev1, hab]
      have heq2 : c.point (i + 1) = c.point j := by rw [hia1, hjrev, hab]
      have h1 := (c.point_eq_iff_of_closed_vertex_injective (by omega) hclosed hinj
        i (j + 1) (by omega) hj).mp heq1
      have h2 := (c.point_eq_iff_of_closed_vertex_injective (by omega) hclosed hinj
        (i + 1) j hi (by omega)).mp heq2
      omega
    obtain ⟨hzae, hzbe⟩ := (P.arc d).segmentAt_intersection_endpoints
      (P.arc_simple d) a b' ha hb'valid hab hza hzb
    rw [hia, hia1, hjrev, hjrev1]
    exact ⟨hzae, hzbe.symm⟩
  · rw [hia, hia1, hjb, hjb1]
    exact P.arc_segment_intersection_endpoints d e hed hef a b ha hb hza hzb

/-- Helper toward Proposition 5.16: a closed drawing walk with nonzero
winding contains an actual simple closed polygon, still with nonzero
winding, using only its original drawing segments. Bridges are allowed in
the original walk and are eliminated by the proved loop-erasure argument. -/
theorem exists_cyclicSimple_of_angleSum_ne_zero (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) (hz : z ∉ c.image)
    (hangle : c.angleSum z ≠ 0)
    (hsource : ∀ k, k + 1 < c.points.length → ∃ d : D, ∃ a : ℕ,
      a + 1 < (P.arc d).points.length ∧ c.point k = (P.arc d).point a ∧
        c.point (k + 1) = (P.arc d).point (a + 1)) :
    ∃ q : Polyline, q.IsCyclicSimple ∧ q.image ⊆ c.image ∧ q.angleSum z ≠ 0 := by
  obtain ⟨q, hqc, hqi, hqa, hql, hqv, hqR⟩ :=
    c.exists_closed_vertex_injective_preserving_edges hclosed z hz hangle
      (fun x y => ∃ d : D, ∃ a : ℕ, a + 1 < (P.arc d).points.length ∧
        x = (P.arc d).point a ∧ y = (P.arc d).point (a + 1)) hsource
  exact ⟨q, P.isCyclicSimple_of_arc_segment_sources q hql hqc hqv hqR, hqi, hqa⟩

end PLDrawing

/-- Helper toward Proposition 5.16: every segment of a finite face walk
comes from an actual dart arc, with both endpoints in their original order. -/
theorem faceWalkPolyline_segment_sources {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (n : ℕ) :
    ∀ k, k + 1 < (faceWalkPolyline B vert P d n).points.length →
      ∃ e : B.D, ∃ a : ℕ, a + 1 < (P.arc e).points.length ∧
        (faceWalkPolyline B vert P d n).point k = (P.arc e).point a ∧
        (faceWalkPolyline B vert P d n).point (k + 1) = (P.arc e).point (a + 1) := by
  induction n with
  | zero =>
      intro k hk
      exact ⟨d, k, hk, rfl, rfl⟩
  | succ n ih =>
      exact Polyline.edges_boundaryConcat _ _
        (finish_faceWalkPolyline_eq_next_start B vert P d n)
        (fun x y => ∃ e : B.D, ∃ a : ℕ, a + 1 < (P.arc e).points.length ∧
          x = (P.arc e).point a ∧ y = (P.arc e).point (a + 1)) ih
        (fun k hk => ⟨(B.map.faceSucc : B.D → B.D)^[n + 1] d, k, hk, rfl, rfl⟩)

/-- Helper toward Proposition 5.16: a closed face-successor walk with
nonzero winding contains a simple closed polygon in its actual image.
No face-orbit correspondence, Euler formula or further Jordan input is used. -/
theorem exists_cyclicSimple_of_faceWalkPolyline_angleSum_ne_zero {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) (n : ℕ)
    (hclosed : (faceWalkPolyline B vert P d n).start =
      (faceWalkPolyline B vert P d n).finish)
    (z : ℂ) (hz : z ∉ (faceWalkPolyline B vert P d n).image)
    (hangle : (faceWalkPolyline B vert P d n).angleSum z ≠ 0) :
    ∃ q : Polyline, q.IsCyclicSimple ∧
      q.image ⊆ (faceWalkPolyline B vert P d n).image ∧ q.angleSum z ≠ 0 := by
  exact P.exists_cyclicSimple_of_angleSum_ne_zero _ hclosed z hz hangle
    (faceWalkPolyline_segment_sources B vert P d n)

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)

/-- Helper toward Proposition 5.16: a finite face walk starting in an
orbit stays in that orbit's actual geometric boundary, including bridges. -/
theorem image_faceWalkPolyline_subset_plOrbitBoundary (O : D39BallFaceCycleOrbit B)
    (d : B.D) (hd : d ∈ O.val) (n : ℕ) :
    (faceWalkPolyline B vert P d n).image ⊆ B.plOrbitBoundary vert P O := by
  have hiter : ∀ m : ℕ,
      B.map.faceSucc.SameCycle d ((B.map.faceSucc : B.D → B.D)^[m] d) := by
    intro m
    induction m with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact ih.apply_right
  obtain ⟨e, hO⟩ := O.property
  have hed : B.map.faceSucc.SameCycle e d := by
    simpa only [hO, Set.mem_ofPred_eq] using hd
  rw [image_faceWalkPolyline]
  rintro z ⟨i, _, hzi⟩
  apply mem_iUnion₂.mpr
  refine ⟨(B.map.faceSucc : B.D → B.D)^[i] d, ?_, hzi⟩
  simpa only [hO, Set.mem_ofPred_eq] using hed.trans (hiter i)




theorem exists_cyclicSimple_in_plOrbitBoundary_of_angleSum_ne_zero
    (hvert : Function.Surjective vert) (O : D39BallFaceCycleOrbit B)
    (d : B.D) (hd : d ∈ O.val) (n : ℕ)
    (hclosed : (faceWalkPolyline B vert P d n).start =
      (faceWalkPolyline B vert P d n).finish)
    (z : ℂ) (hz : z ∉ (faceWalkPolyline B vert P d n).image)
    (hangle : (faceWalkPolyline B vert P d n).angleSum z ≠ 0) :
    ∃ q : Polyline, q.IsCyclicSimple ∧ q.image ⊆ B.plOrbitBoundary vert P O ∧
      q.image ⊆ frontier (B.plOrbitFace vert P hvert O).val ∧ q.angleSum z ≠ 0 := by
  obtain ⟨q, hqc, hqi, hqa⟩ := exists_cyclicSimple_of_faceWalkPolyline_angleSum_ne_zero
    B vert P d n hclosed z hz hangle
  have hqO := hqi.trans (B.image_faceWalkPolyline_subset_plOrbitBoundary vert P O d hd n)
  exact ⟨q, hqc, hqO, hqO.trans (B.plOrbitBoundary_subset_frontier vert P hvert O), hqa⟩

/-- Helper toward Proposition 5.16: opposite darts can put the very same
geometric arc in two orbit boundaries. Distinct dart orbits alone therefore
do not imply disjoint geometric boundaries. -/
theorem arc_subset_inter_plOrbitBoundary_of_flip_mem
    (O₁ O₂ : D39BallFaceCycleOrbit B) (d : B.D)
    (hd : d ∈ O₁.val) (hflip : B.map.edgeInv d ∈ O₂.val) :
    (P.arc d).image ⊆ B.plOrbitBoundary vert P O₁ ∩ B.plOrbitBoundary vert P O₂ := by
  intro z hz
  refine ⟨mem_iUnion₂.mpr ⟨d, hd, hz⟩, ?_⟩
  apply mem_iUnion₂.mpr
  refine ⟨B.map.edgeInv d, hflip, ?_⟩
  rw [P.arc_image_flip]
  exact hz

end D39FiniteBall

































































end DirectedDistances.PlanarMap

end

