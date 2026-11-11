module

public import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Proposition 5.16: a two-vertex chain has the segment
between its vertices as its image. -/
private theorem image_twoPointPolyline (x y : ℂ) :
    (⟨[x, y], by simp⟩ : Polyline).image = segment ℝ x y := by
  ext z
  constructor
  · intro hz
    rcases hz with hz | ⟨i, hi, hz⟩
    · rw [mem_singleton_iff] at hz
      subst z
      exact left_mem_segment ℝ x y
    · have hi0 : i = 0 := by
        change i + 1 < 2 at hi
        omega
      subst i
      simpa [Polyline.segmentAt, Polyline.point, Polyline.start] using hz
  · intro hz
    refine Or.inr ⟨0, by simp, ?_⟩
    simpa [Polyline.segmentAt, Polyline.point, Polyline.start] using hz

/-- Helper toward Proposition 5.16: replacing a subchain between two
non-adjacent segments by the two segments through an intersection point
produces a strictly shorter vertex list. -/
theorem shortcut_points_length_lt (points : List ℂ) (z : ℂ) (i j : ℕ)
    (hij : i + 2 ≤ j) (hj : j + 1 < points.length) :
    (points.take (i + 1) ++ [z] ++ points.drop (j + 1)).length < points.length := by
  have hi : i + 1 ≤ points.length := by omega
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_take, List.length_drop]
  omega

/-- Helper toward Proposition 5.16: a self-intersection of two
non-adjacent segments yields a shorter polyline with the same endpoints and
image contained in the original image. -/
theorem exists_shorter_polyline_of_nonadjacent_segment_intersection
    (p : Polyline) (i j : ℕ) (hi : i + 1 < p.points.length)
    (hj : j + 1 < p.points.length) (hij : i + 1 < j) (z : ℂ)
    (hzi : z ∈ p.segmentAt i) (hzj : z ∈ p.segmentAt j) :
    ∃ q : Polyline, q.start = p.start ∧ q.finish = p.finish ∧
      q.image ⊆ p.image ∧ q.points.length < p.points.length := by
  let pre := p.intervalPolyline 0 i
  let first : Polyline := ⟨[p.point i, z], by simp⟩
  let second : Polyline := ⟨[z, p.point (j + 1)], by simp⟩
  let n := p.points.length - (j + 1) - 1
  let suf := p.intervalPolyline (j + 1) n
  let q := Polyline.boundaryConcat
    (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second) suf
  have hpre : pre.finish = first.start := by
    simp [pre, first, Polyline.finish_intervalPolyline, Polyline.start]
  have hfirst : first.finish = second.start := by
    simp [first, second, Polyline.finish, Polyline.start]
  have hsuf : second.finish = suf.start := by
    simp [second, suf, Polyline.finish, Polyline.start_intervalPolyline]
  have hpreFirst : (Polyline.boundaryConcat pre first).finish = second.start :=
    (Polyline.finish_boundaryConcat_of_join pre first hpre).trans hfirst
  have hmid : (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second).finish =
      suf.start :=
    (Polyline.finish_boundaryConcat_of_join
      (Polyline.boundaryConcat pre first) second hpreFirst).trans hsuf
  have hboundPre : 0 + i < p.points.length := by omega
  have hboundSuf : (j + 1) + n < p.points.length := by
    dsimp [n]
    omega
  have hstart : q.start = p.start := by
    simp [q, pre, Polyline.start_boundaryConcat,
      Polyline.start_intervalPolyline, Polyline.point_zero_eq_start]
  have hfinish : q.finish = p.finish := by
    change (Polyline.boundaryConcat
      (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second) suf).finish =
        p.finish
    rw [Polyline.finish_boundaryConcat_of_join
      (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second) suf hmid,
      Polyline.finish_intervalPolyline]
    have hn : (j + 1) + n = p.points.length - 1 := by
      dsimp [n]
      omega
    rw [hn, p.point_last_eq_finish]
  have hpreIm : pre.image ⊆ p.image :=
    p.image_intervalPolyline_subset 0 i hboundPre
  have hsufIm : suf.image ⊆ p.image :=
    p.image_intervalPolyline_subset (j + 1) n hboundSuf
  have hfirstIm : first.image ⊆ p.image := by
    change (⟨[p.point i, z], by simp⟩ : Polyline).image ⊆ p.image
    rw [image_twoPointPolyline]
    have hseg : segment ℝ (p.point i) z ⊆ p.segmentAt i := by
      exact (convex_segment (p.point i) (p.point (i + 1))).segment_subset
        (left_mem_segment ℝ _ _) hzi
    exact hseg.trans (p.segmentAt_subset_image hi)
  have hsecondIm : second.image ⊆ p.image := by
    change (⟨[z, p.point (j + 1)], by simp⟩ : Polyline).image ⊆ p.image
    rw [image_twoPointPolyline]
    have hseg : segment ℝ z (p.point (j + 1)) ⊆ p.segmentAt j := by
      exact (convex_segment (p.point j) (p.point (j + 1))).segment_subset
        hzj (right_mem_segment ℝ _ _)
    exact hseg.trans (p.segmentAt_subset_image hj)
  have hqIm : q.image ⊆ p.image := by
    change (Polyline.boundaryConcat
      (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second) suf).image ⊆
        p.image
    rw [Polyline.image_boundaryConcat
        (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second) suf hmid,
      Polyline.image_boundaryConcat (Polyline.boundaryConcat pre first) second hpreFirst,
      Polyline.image_boundaryConcat pre first hpre]
    exact union_subset (union_subset (union_subset hpreIm hfirstIm) hsecondIm)
      hsufIm
  have hqLen : q.points.length < p.points.length := by
    change (Polyline.boundaryConcat
      (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second) suf).points.length <
        p.points.length
    rw [Polyline.length_boundaryConcat
        (Polyline.boundaryConcat (Polyline.boundaryConcat pre first) second) suf,
      Polyline.length_boundaryConcat (Polyline.boundaryConcat pre first) second,
      Polyline.length_boundaryConcat pre first,
      Polyline.length_intervalPolyline p 0 i,
      Polyline.length_intervalPolyline p (j + 1) n]
    simp only [first, second, List.length_cons, List.length_nil]
    dsimp [n]
    omega
  exact ⟨q, hstart, hfinish, hqIm, hqLen⟩

/-- Helper toward Proposition 5.16: a polyline of least vertex count inside
an open connected set has disjoint non-adjacent segments. -/
theorem exists_polyline_without_nonadjacent_segment_intersections
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U) {x y : ℂ}
    (hx : x ∈ U) (hy : y ∈ U) :
    ∃ p : Polyline, p.start = x ∧ p.finish = y ∧ p.image ⊆ U ∧
      ∀ i j, i + 1 < p.points.length → j + 1 < p.points.length → i + 1 < j →
        Disjoint (p.segmentAt i) (p.segmentAt j) := by
  classical
  obtain ⟨p₀, hp₀s, hp₀f, hp₀im⟩ :=
    exists_polyline_in_open_connected hU hconn hx hy
  let P : ℕ → Prop := fun n => ∃ p : Polyline,
    p.start = x ∧ p.finish = y ∧ p.image ⊆ U ∧ p.points.length = n
  have hP : ∃ n, P n := by
    exact ⟨p₀.points.length, p₀, hp₀s, hp₀f, hp₀im, rfl⟩
  let n := Nat.find hP
  obtain ⟨p, hps, hpf, hpim, hlen⟩ := Nat.find_spec hP
  have hmin (q : Polyline) (hqs : q.start = x) (hqf : q.finish = y)
      (hqim : q.image ⊆ U) : n ≤ q.points.length := by
    apply Nat.find_min' hP
    exact ⟨q, hqs, hqf, hqim, rfl⟩
  refine ⟨p, hps, hpf, hpim, ?_⟩
  intro i j hi hj hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨q, hqs, hqf, hqim, hqlen⟩ :=
    exists_shorter_polyline_of_nonadjacent_segment_intersection
      p i j hi hj hij z hzi hzj
  have hleast := hmin q (hqs.trans hps) (hqf.trans hpf) (hqim.trans hpim)
  rw [hlen] at hqlen
  omega
















end DirectedDistances.PlanarMap
end
