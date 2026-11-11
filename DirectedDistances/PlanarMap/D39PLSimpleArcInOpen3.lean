module

public import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen2

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Proposition 5.16: if two segments meeting at `b` share a
second point, the segment joining their outer endpoints is contained in their
union. -/
theorem segment_subset_adjacent_union_of_mem_inter
    (a b c z : ℂ) (hzab : z ∈ segment ℝ a b)
    (hzbc : z ∈ segment ℝ b c) (hzb : z ≠ b) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  rw [segment_symm ℝ a b] at hzab
  rw [segment_eq_image'] at hzab hzbc
  rcases hzab with ⟨t, ht, hzt⟩
  rcases hzbc with ⟨u, hu, hzu⟩
  have htu : t • (a - b) = u • (c - b) := by
    apply add_left_cancel
    exact hzt.trans hzu.symm
  have ht0 : t ≠ 0 := by
    intro ht0
    subst t
    apply hzb
    simpa using hzt.symm
  have hu0 : u ≠ 0 := by
    intro hu0
    subst u
    apply hzb
    simpa using hzu.symm
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  by_cases htu' : t ≤ u
  · have hratio : c - b = (t / u) • (a - b) := by
      calc
        c - b = u⁻¹ • (u • (c - b)) := by
          rw [smul_smul]
          simp [hu0]
        _ = u⁻¹ • (t • (a - b)) := by rw [← htu]
        _ = (t / u) • (a - b) := by
          rw [div_eq_mul_inv, smul_smul]
          congr 1
          ring
    have hrange : t / u ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hu.1, (div_le_one hupos).2 htu'⟩
    have hcba : c ∈ segment ℝ b a := by
      rw [segment_eq_image']
      refine ⟨t / u, hrange, ?_⟩
      calc
        b + (t / u) • (a - b) = b + (c - b) := by rw [hratio]
        _ = c := by abel
    have hca : c ∈ segment ℝ a b := by
      rw [segment_symm ℝ a b]
      exact hcba
    intro w hw
    exact Or.inl ((convex_segment a b).segment_subset
      (left_mem_segment ℝ a b) hca hw)
  · have hut' : u ≤ t := le_of_not_ge htu'
    have hratio : a - b = (u / t) • (c - b) := by
      calc
        a - b = t⁻¹ • (t • (a - b)) := by
          rw [smul_smul]
          simp [ht0]
        _ = t⁻¹ • (u • (c - b)) := by rw [htu]
        _ = (u / t) • (c - b) := by
          rw [div_eq_mul_inv, smul_smul]
          congr 1
          ring
    have hrange : u / t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hu.1 ht.1, (div_le_one htpos).2 hut'⟩
    have habc : a ∈ segment ℝ b c := by
      rw [segment_eq_image']
      refine ⟨u / t, hrange, ?_⟩
      calc
        b + (u / t) • (c - b) = b + (a - b) := by rw [hratio]
        _ = a := by abel
    intro w hw
    exact Or.inr ((convex_segment b c).segment_subset habc
      (right_mem_segment ℝ b c) hw)

/-- Helper toward Proposition 5.16: the image of a two-point polyline is the
segment between its endpoints. -/
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

/-- Helper toward Proposition 5.16: deleting an interior vertex whose
replacement segment lies in the two old segments shortens the polyline while
preserving its endpoints and keeping its image inside the old image. -/
theorem exists_polyline_delete_interior_point
    (p : Polyline) (i : ℕ) (hi : i + 2 < p.points.length)
    (hreplacement : segment ℝ (p.point i) (p.point (i + 2)) ⊆
      p.segmentAt i ∪ p.segmentAt (i + 1)) :
    ∃ q : Polyline, q.start = p.start ∧ q.finish = p.finish ∧
      q.image ⊆ p.image ∧ q.points.length < p.points.length := by
  let pre := p.intervalPolyline 0 i
  let bridge : Polyline := ⟨[p.point i, p.point (i + 2)], by simp⟩
  let n := p.points.length - (i + 2) - 1
  let suf := p.intervalPolyline (i + 2) n
  let q := Polyline.boundaryConcat (Polyline.boundaryConcat pre bridge) suf
  have hpre : pre.finish = bridge.start := by
    simp [pre, bridge, Polyline.finish_intervalPolyline, Polyline.start]
  have hbridge : bridge.finish = suf.start := by
    simp [bridge, suf, Polyline.finish, Polyline.start_intervalPolyline]
  have hpreBridge : (Polyline.boundaryConcat pre bridge).finish = suf.start :=
    (Polyline.finish_boundaryConcat_of_join pre bridge hpre).trans hbridge
  have hboundPre : 0 + i < p.points.length := by omega
  have hboundSuf : (i + 2) + n < p.points.length := by
    dsimp [n]
    omega
  have hstart : q.start = p.start := by
    simp [q, pre, Polyline.start_boundaryConcat,
      Polyline.start_intervalPolyline, Polyline.point_zero_eq_start]
  have hfinish : q.finish = p.finish := by
    change (Polyline.boundaryConcat
      (Polyline.boundaryConcat pre bridge) suf).finish = p.finish
    rw [Polyline.finish_boundaryConcat_of_join
      (Polyline.boundaryConcat pre bridge) suf hpreBridge,
      Polyline.finish_intervalPolyline]
    have hn : (i + 2) + n = p.points.length - 1 := by
      dsimp [n]
      omega
    rw [hn, p.point_last_eq_finish]
  have hpreIm : pre.image ⊆ p.image :=
    p.image_intervalPolyline_subset 0 i hboundPre
  have hsufIm : suf.image ⊆ p.image :=
    p.image_intervalPolyline_subset (i + 2) n hboundSuf
  have hbridgeIm : bridge.image ⊆ p.image := by
    change (⟨[p.point i, p.point (i + 2)], by simp⟩ : Polyline).image ⊆ p.image
    rw [image_twoPointPolyline]
    exact hreplacement.trans (union_subset
      (p.segmentAt_subset_image (by omega))
      (p.segmentAt_subset_image (by omega)))
  have hqIm : q.image ⊆ p.image := by
    change (Polyline.boundaryConcat (Polyline.boundaryConcat pre bridge) suf).image ⊆
      p.image
    rw [Polyline.image_boundaryConcat
        (Polyline.boundaryConcat pre bridge) suf hpreBridge,
      Polyline.image_boundaryConcat pre bridge hpre]
    exact union_subset (union_subset hpreIm hbridgeIm) hsufIm
  have hqLen : q.points.length < p.points.length := by
    change (Polyline.boundaryConcat (Polyline.boundaryConcat pre bridge) suf).points.length <
      p.points.length
    rw [Polyline.length_boundaryConcat
        (Polyline.boundaryConcat pre bridge) suf,
      Polyline.length_boundaryConcat pre bridge,
      Polyline.length_intervalPolyline p 0 i,
      Polyline.length_intervalPolyline p (i + 2) n]
    simp only [bridge, List.length_cons, List.length_nil]
    dsimp [n]
    omega
  exact ⟨q, hstart, hfinish, hqIm, hqLen⟩

/-- Helper toward Proposition 5.16: every least-vertex-count polyline between
fixed endpoints has distinct vertices. -/
theorem minimal_polyline_vertices_injective
    {U : Set ℂ} {x y : ℂ} (p : Polyline) (n : ℕ)
    (hps : p.start = x) (hpf : p.finish = y) (hpim : p.image ⊆ U)
    (hlen : p.points.length = n)
    (hmin : ∀ q : Polyline, q.start = x → q.finish = y → q.image ⊆ U →
      n ≤ q.points.length) :
    ∀ i j, i < p.points.length → j < p.points.length →
      p.point i = p.point j → i = j := by
  intro i j hi hj hij
  by_contra hne
  have hnoRepeat : ∀ a b, a < b → a < p.points.length → b < p.points.length →
      p.point a = p.point b → False := by
    intro a b hab ha hb heq
    let pre := p.intervalPolyline 0 a
    let suf := p.intervalPolyline b (p.points.length - b - 1)
    have hpreBound : 0 + a < p.points.length := by omega
    have hsufBound : b + (p.points.length - b - 1) < p.points.length := by omega
    have hjoin : pre.finish = suf.start := by
      simp only [pre, Polyline.finish_intervalPolyline, Nat.zero_add,
        suf, Polyline.start_intervalPolyline]
      exact heq
    have hstart : (Polyline.boundaryConcat pre suf).start = x := by
      simp [pre, Polyline.start_boundaryConcat, Polyline.start_intervalPolyline,
        Polyline.point_zero_eq_start, hps]
    have hfinish : (Polyline.boundaryConcat pre suf).finish = y := by
      rw [Polyline.finish_boundaryConcat_of_join pre suf hjoin,
        Polyline.finish_intervalPolyline,
        show b + (p.points.length - b - 1) = p.points.length - 1 by omega,
        p.point_last_eq_finish, hpf]
    have himage : (Polyline.boundaryConcat pre suf).image ⊆ U := by
      rw [Polyline.image_boundaryConcat pre suf hjoin]
      exact union_subset
        ((p.image_intervalPolyline_subset 0 a hpreBound).trans hpim)
        ((p.image_intervalPolyline_subset b (p.points.length - b - 1)
          hsufBound).trans hpim)
    have hshort : (Polyline.boundaryConcat pre suf).points.length < p.points.length := by
      rw [Polyline.length_boundaryConcat, Polyline.length_intervalPolyline,
        Polyline.length_intervalPolyline]
      omega
    have hleast := hmin (Polyline.boundaryConcat pre suf) hstart hfinish himage
    rw [hlen] at hshort
    omega
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · exact (hnoRepeat i j hij' hi hj hij).elim
  · exact (hnoRepeat j i hji' hj hi hij.symm).elim

/-- Helper toward Proposition 5.16: every two points in an open connected
subset of the plane are joined by a simple polyline contained in that set. -/
theorem exists_simple_polyline_in_open_connected {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsConnected U) {x y : ℂ}
    (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    ∃ p : Polyline, p.IsSimple ∧ p.start = x ∧ p.finish = y ∧ p.image ⊆ U := by
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
  have _hlen2 : 2 ≤ p.points.length := by
    have hstartne : p.start ≠ p.finish := by
      intro heq
      exact hxy (hps.symm.trans (heq.trans hpf))
    have hstart : p.points.length = 1 → p.start = p.finish := by
      intro h
      rcases p with ⟨l, hn⟩
      cases l with
      | nil => simp at h
      | cons a l =>
        cases l with
        | nil => rfl
        | cons b l => simp at h
    by_contra hlt
    have hpos : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    exact hstartne (hstart (by omega))
  have hvertices := minimal_polyline_vertices_injective p n hps hpf hpim hlen hmin
  have hfirst : ∀ i, i + 1 < p.points.length →
      p.point i ≠ p.point (i + 1) := by
    intro i hi heq
    have hne : i ≠ i + 1 := by omega
    exact hne (hvertices i (i + 1) (by omega) (by omega) heq)
  have hadjacent : ∀ i, i + 2 < p.points.length →
      p.segmentAt i ∩ p.segmentAt (i + 1) = {p.point (i + 1)} := by
    intro i hi
    apply Set.Subset.antisymm
    · intro z hz
      simp only [Set.mem_singleton_iff]
      by_cases hzb : z = p.point (i + 1)
      · exact hzb
      · have hreplacement : segment ℝ (p.point i) (p.point (i + 2)) ⊆
          p.segmentAt i ∪ p.segmentAt (i + 1) := by
          apply segment_subset_adjacent_union_of_mem_inter
            (p.point i) (p.point (i + 1)) (p.point (i + 2)) z
          · simpa [Polyline.segmentAt] using hz.1
          · simpa [Polyline.segmentAt] using hz.2
          · exact hzb
        obtain ⟨q, hqs, hqf, hqim, hqlen⟩ :=
          exists_polyline_delete_interior_point p i hi hreplacement
        have hleast := hmin q (hqs.trans hps) (hqf.trans hpf) (hqim.trans hpim)
        rw [hlen] at hqlen
        omega
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      constructor
      · simpa [Polyline.segmentAt] using
          (right_mem_segment ℝ (p.point i) (p.point (i + 1)))
      · simpa [Polyline.segmentAt] using
          (left_mem_segment ℝ (p.point (i + 1)) (p.point (i + 2)))
  have hseparated : ∀ i j, i + 1 < p.points.length → j + 1 < p.points.length →
      i + 1 < j → Disjoint (p.segmentAt i) (p.segmentAt j) := by
    intro i j hi hj hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨q, hqs, hqf, hqim, hqlen⟩ :=
      exists_shorter_polyline_of_nonadjacent_segment_intersection
        p i j hi hj hij z hzi hzj
    have hleast := hmin q (hqs.trans hps) (hqf.trans hpf) (hqim.trans hpim)
    rw [hlen] at hqlen
    omega
  refine ⟨p, ?_, hps, hpf, hpim⟩
  exact ⟨hfirst, hadjacent, hseparated⟩

end DirectedDistances.PlanarMap
end
