module

public import DirectedDistances.PlanarMap.D39PolygonalSeparation6

/-! # Endpoint incidences for an endpoint-glued polygon

Helpers toward Proposition 5.16. -/

public section

namespace DirectedDistances.PlanarMap
namespace Polyline

open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: if the start of a simple polyline lies
on one of its segments, that segment is the first one. -/
private theorem start_mem_segmentAt_index (p : Polyline) (hp : p.IsSimple)
    (hlen : 2 ≤ p.points.length) (i : ℕ) (hi : i + 1 < p.points.length)
    (hmem : p.start ∈ p.segmentAt i) : i = 0 := by
  by_contra hi0
  have hseg0 : p.start ∈ p.segmentAt 0 := by
    rw [← point_zero_eq_start p]
    exact left_mem_segment ℝ _ _
  have hvalid0 : 0 + 1 < p.points.length := by omega
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hi0) with heq | hgt
  · subst i
    have hadj := hp.2.1 0 (by omega)
    have hpt : p.start = p.point 1 := by
      have : p.start ∈ ({p.point 1} : Set ℂ) := by
        rw [← hadj]
        exact ⟨hseg0, hmem⟩
      simpa [point_zero_eq_start p] using this
    exact (hp.1 0 hvalid0) (by simpa [point_zero_eq_start p] using hpt)
  · exact (Set.disjoint_left.mp (hp.2.2 0 i hvalid0 hi (by omega))) hseg0 hmem

/-- Helper toward Proposition 5.16: if the finish of a simple polyline lies
on one of its segments, that segment is the last one. -/
private theorem finish_mem_segmentAt_index (p : Polyline) (hp : p.IsSimple)
    (hlen : 2 ≤ p.points.length) (i : ℕ) (hi : i + 1 < p.points.length)
    (hmem : p.finish ∈ p.segmentAt i) : i + 2 = p.points.length := by
  let last := p.points.length - 2
  have hlast : last + 1 < p.points.length := by dsimp [last]; omega
  have hfinish : p.finish ∈ p.segmentAt last := by
    change p.finish ∈ segment ℝ (p.point last) (p.point (last + 1))
    rw [show last + 1 = p.points.length - 1 by dsimp [last]; omega,
      ← point_last_eq_finish p]
    exact right_mem_segment ℝ _ _
  by_contra hnot
  have hilt : i + 1 < last ∨ i + 1 = last := by
    have hle : i + 1 ≤ last := by dsimp [last]; omega
    exact lt_or_eq_of_le hle
  rcases hilt with hfar | hadjidx
  · exact (Set.disjoint_left.mp (hp.2.2 i last hi hlast hfar)) hmem hfinish
  · have hadj := hp.2.1 i (by dsimp [last] at hadjidx; omega)
    have hpt : p.finish = p.point (i + 1) := by
      have : p.finish ∈ ({p.point (i + 1)} : Set ℂ) := by
        rw [← hadj]
        exact ⟨hmem, by simpa [hadjidx] using hfinish⟩
      simpa using this
    have hne := hp.1 last hlast
    apply hne
    calc
      p.point last = p.finish := by simpa [hadjidx] using hpt.symm
      _ = p.point (last + 1) := by
        rw [show last + 1 = p.points.length - 1 by dsimp [last]; omega]
        exact point_last_eq_finish p |>.symm

/-- Helper toward Proposition 5.16: each segment of the closed concatenation
is the corresponding segment of one of its two arcs. -/
private theorem segmentAt_closedConcat_cases (p q : Polyline)
    (hfinish : p.finish = q.finish) (i : ℕ)
    (hi : i + 1 < (closedConcat p q).points.length) :
    (i + 1 < p.points.length ∧
      (closedConcat p q).segmentAt i = p.segmentAt i) ∨
    ∃ j, j + 1 < q.reverse.points.length ∧
      i = p.points.length - 1 + j ∧
      (closedConcat p q).segmentAt i = q.reverse.segmentAt j := by
  by_cases hleft : i + 1 < p.points.length
  · exact Or.inl ⟨hleft, segmentAt_closedConcat_left p q i hleft⟩
  · right
    let j := i - (p.points.length - 1)
    have hidx : i = p.points.length - 1 + j := by dsimp [j]; omega
    have hj : j + 1 < q.points.length := by
      dsimp [j]
      rw [points_length_closedConcat p q] at hi
      omega
    have hjrev : j + 1 < q.reverse.points.length := by
      simpa [Polyline.reverse, List.length_reverse] using hj
    exact ⟨j, hjrev, hidx, by
      simpa [hidx] using segmentAt_closedConcat_right p q hfinish j hj⟩

/-- Helper toward Proposition 5.16: a point shared by one segment from each
arc is one of the two common endpoints. -/
private theorem mixed_segment_mem_endpoints (p q : Polyline)
    (hfinish : p.finish = q.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish})
    (i j : ℕ) (hi : i + 1 < p.points.length)
    (hj : j + 1 < (closedConcat p q).points.length)
    (hjright : p.points.length - 1 ≤ j) (z : ℂ)
    (hzi : z ∈ p.segmentAt i)
    (hzj : z ∈ (closedConcat p q).segmentAt j) :
    z = p.start ∨ z = p.finish := by
  let k := j - (p.points.length - 1)
  have hidx : j = p.points.length - 1 + k := by dsimp [k]; omega
  have hk : k + 1 < q.reverse.points.length := by
    have hlen := points_length_closedConcat p q
    rw [hlen] at hj
    dsimp [k]
    have hqr : q.reverse.points.length = q.points.length := by
      simp [Polyline.reverse]
    rw [hqr]
    omega
  have hseg : (closedConcat p q).segmentAt j = q.reverse.segmentAt k := by
    rw [hidx]
    exact segmentAt_closedConcat_right p q hfinish k (by
      have hq : k + 1 < q.points.length := by simpa [Polyline.reverse] using hk
      exact hq)
  have hpim : z ∈ p.image := p.segmentAt_subset_image hi hzi
  have hqrev : z ∈ q.reverse.image := by
    have hzj' : z ∈ q.reverse.segmentAt k := by rw [← hseg]; exact hzj
    exact q.reverse.segmentAt_subset_image hk hzj'
  have hqim : z ∈ q.image := by
    simpa only [image_reverse_transfer] using hqrev
  have hend : z ∈ ({p.start, p.finish} : Set ℂ) := by
    rw [← hint]
    exact ⟨hpim, hqim⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hend

/-- Helper toward Proposition 5.16: nonadjacent segments from different arcs
are disjoint except for the first and last segments of the closed chain. -/
private theorem mixed_segments_disjoint (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish})
    (i j : ℕ) (hi : i + 1 < p.points.length)
    (hj : j + 1 < (closedConcat p q).points.length)
    (hjright : p.points.length - 1 ≤ j)
    (horder : i + 1 < j)
    (hwrap : ¬ (i = 0 ∧ j + 2 = (closedConcat p q).points.length)) :
    Disjoint ((closedConcat p q).segmentAt i)
      ((closedConcat p q).segmentAt j) := by
  have hlenqr : 2 ≤ q.reverse.points.length := by simpa [Polyline.reverse] using hlenq
  have hqrSimple : q.reverse.IsSimple := isSimple_reverse_transfer q hq
  have hidx : j = p.points.length - 1 + (j - (p.points.length - 1)) := by omega
  have hk : j - (p.points.length - 1) + 1 < q.reverse.points.length := by
    rw [points_length_closedConcat p q] at hj
    have hqrevlen : q.reverse.points.length = q.points.length := by simp [Polyline.reverse]
    rw [hqrevlen]
    omega
  have hsegL : (closedConcat p q).segmentAt i = p.segmentAt i :=
    segmentAt_closedConcat_left p q i hi
  have hsegR : (closedConcat p q).segmentAt j =
      q.reverse.segmentAt (j - (p.points.length - 1)) := by
    calc
      (closedConcat p q).segmentAt j =
          (closedConcat p q).segmentAt
            (p.points.length - 1 + (j - (p.points.length - 1))) :=
              congrArg (fun k => (closedConcat p q).segmentAt k) hidx
      _ = q.reverse.segmentAt (j - (p.points.length - 1)) :=
        segmentAt_closedConcat_right p q hfinish _ (by
          simpa [Polyline.reverse] using hk)
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hend := mixed_segment_mem_endpoints p q hfinish hint i j hi hj hjright z
    (by simpa [hsegL] using hzi) hzj
  rcases hend with hzstart | hzfinish
  · have hi0 : i = 0 := start_mem_segmentAt_index p hp hlenp i hi
      (by simpa [hsegL, hzstart] using hzi)
    have hlast : j + 2 = (closedConcat p q).points.length := by
      have hzfinishqr : z = q.reverse.finish := by
        calc
          z = p.start := hzstart
          _ = q.start := hstart
          _ = q.reverse.finish := by rw [finish_reverse]
      have hkfinish : j - (p.points.length - 1) + 2 = q.reverse.points.length :=
        finish_mem_segmentAt_index q.reverse hqrSimple hlenqr _ hk
          (by simpa [hsegR, hzfinishqr] using hzj)
      rw [points_length_closedConcat]
      have hqrlen : q.reverse.points.length = q.points.length := by simp [Polyline.reverse]
      rw [hqrlen] at hkfinish
      omega
    exact hwrap ⟨hi0, hlast⟩
  · have hilast : i + 2 = p.points.length :=
      finish_mem_segmentAt_index p hp hlenp i hi
        (by simpa [hsegL, hzfinish] using hzi)
    have hzstartqr : z = q.reverse.start := by
      calc
        z = p.finish := hzfinish
        _ = q.finish := hfinish
        _ = q.reverse.start := by rw [start_reverse]
    have hk0 : j - (p.points.length - 1) = 0 :=
      start_mem_segmentAt_index q.reverse hqrSimple hlenqr _ hk
        (by simpa [hsegR, hzstartqr] using hzj)
    omega

/-- Helper toward Proposition 5.16: adjacent edges at the join of two simple
arcs meet exactly at their common endpoint. -/
private theorem mixed_join_intersection (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hne : p.start ≠ p.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish})
    (i : ℕ) (hi : i + 2 < (closedConcat p q).points.length)
    (hleft : i + 2 = p.points.length) :
    (closedConcat p q).segmentAt i ∩
      (closedConcat p q).segmentAt (i + 1) =
        {(closedConcat p q).point (i + 1)} := by
  have hlenqr : 2 ≤ q.reverse.points.length := by simpa [Polyline.reverse] using hlenq
  have hqrSimple : q.reverse.IsSimple := isSimple_reverse_transfer q hq
  have hidxL : i + 1 < p.points.length := by omega
  have hidxR : i + 1 = p.points.length - 1 := by omega
  have hsegL : (closedConcat p q).segmentAt i = p.segmentAt i :=
    segmentAt_closedConcat_left p q i hidxL
  have hsegR : (closedConcat p q).segmentAt (i + 1) = q.reverse.segmentAt 0 := by
    rw [show i + 1 = p.points.length - 1 by omega]
    simpa using segmentAt_closedConcat_right p q hfinish 0 (by
      have : 0 + 1 < q.reverse.points.length := by omega
      simpa [Polyline.reverse] using this)
  have hincl : p.points.length + q.points.length - 1 ≥ 4 := by
    have hc := points_length_closedConcat_ge_four p q hlenp hlenq hstart hfinish hne hint
    rw [points_length_closedConcat] at hc
    exact hc
  apply Set.ext
  intro z
  constructor
  · intro hz
    have hend := mixed_segment_mem_endpoints p q hfinish hint i (i + 1)
      hidxL (by omega) (by omega) z (by simpa [hsegL] using hz.1) hz.2
    rcases hend with hzstart | hzfinish
    · have hi0 : i = 0 := start_mem_segmentAt_index p hp hlenp i hidxL
        (by simpa [hsegL, hzstart] using hz.1)
      have hzfinishqr : z = q.reverse.finish := by
        calc
          z = p.start := hzstart
          _ = q.start := hstart
          _ = q.reverse.finish := by rw [finish_reverse]
      have hkfinish : 0 + 2 = q.reverse.points.length :=
        finish_mem_segmentAt_index q.reverse hqrSimple hlenqr 0 (by omega)
          (by simpa [hsegR, hzfinishqr] using hz.2)
      have hqrevlen : q.reverse.points.length = q.points.length := by simp [Polyline.reverse]
      rw [hqrevlen] at hkfinish
      omega
    · have hzpoint : z = (closedConcat p q).point (i + 1) := by
        calc
          z = p.finish := hzfinish
          _ = p.point (i + 1) := by
            rw [show i + 1 = p.points.length - 1 by omega]
            exact point_last_eq_finish p |>.symm
          _ = (closedConcat p q).point (i + 1) := by
            symm
            exact point_closedConcat_left p q _ (by omega)
      simpa [hzpoint]
  · intro hz
    have hz' : z = (closedConcat p q).point (i + 1) := by simpa using hz
    subst z
    constructor
    · rw [hsegL]
      rw [point_closedConcat_left p q (i + 1) (by omega),
        show i + 1 = p.points.length - 1 by omega]
      have hiidx : i = p.points.length - 2 := by omega
      rw [hiidx]
      change p.point (p.points.length - 1) ∈ segment ℝ
        (p.point (p.points.length - 2)) (p.point (p.points.length - 2 + 1))
      convert right_mem_segment ℝ (p.point (p.points.length - 2))
        (p.point (p.points.length - 2 + 1)) using 1 <;> congr 1 <;> omega
    · rw [hsegR]
      have hpt : (closedConcat p q).point (i + 1) = q.reverse.point 0 := by
        calc
          (closedConcat p q).point (i + 1) = p.point (i + 1) :=
            point_closedConcat_left p q _ (by omega)
          _ = p.finish := by
            rw [show i + 1 = p.points.length - 1 by omega]
            exact point_last_eq_finish p
          _ = q.finish := hfinish
          _ = q.reverse.start := by rw [start_reverse]
          _ = q.reverse.point 0 := (point_zero_eq_start q.reverse).symm
      rw [hpt]
      exact left_mem_segment ℝ (q.reverse.point 0) (q.reverse.point 1)

/-- Helper toward Proposition 5.16: the endpoint-glued concatenation of two
simple arcs meeting only at their distinct common endpoints is cyclically
simple. -/
theorem closedConcat_isCyclicSimple (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hne : p.start ≠ p.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish}) :
    IsCyclicSimple (closedConcat p q) := by
  let c := closedConcat p q
  have hlen : 4 ≤ c.points.length := by
    dsimp [c]
    exact points_length_closedConcat_ge_four p q hlenp hlenq hstart hfinish hne hint
  have hroot : c.point 0 = c.point (c.points.length - 1) := by
    dsimp [c]
    exact point_zero_eq_last_closedConcat p q hstart hlenq
  have hqrSimple : q.reverse.IsSimple := isSimple_reverse_transfer q hq
  have hlenqr : 2 ≤ q.reverse.points.length := by simpa [Polyline.reverse] using hlenq
  refine ⟨hlen, hroot, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact closedConcat_edge_ne p q hp hq hlenp hlenq hfinish i hi
  · intro i hi
    have hlenp' : 2 ≤ p.points.length := hlenp
    by_cases hleft : i + 2 < p.points.length
    · rw [segmentAt_closedConcat_left p q i (by omega),
        segmentAt_closedConcat_left p q (i + 1) (by omega)]
      rw [point_closedConcat_left p q (i + 1) (by omega)]
      exact hp.2.1 i hleft
    · by_cases hright : p.points.length - 1 ≤ i
      · let j := i - (p.points.length - 1)
        have hidx : i = p.points.length - 1 + j := by dsimp [j]; omega
        have hj : j + 2 < q.reverse.points.length := by
          rw [points_length_closedConcat] at hi
          have hqrevlen : q.reverse.points.length = q.points.length := by simp [Polyline.reverse]
          rw [hqrevlen]
          dsimp [j]
          omega
        have hjq : j + 1 < q.points.length := by
          simpa [Polyline.reverse] using (show j + 1 < q.reverse.points.length by omega)
        have hj1q : j + 2 < q.points.length := by simpa [Polyline.reverse] using hj
        rw [hidx, segmentAt_closedConcat_right p q hfinish j hjq,
          show p.points.length - 1 + j + 1 = p.points.length - 1 + (j + 1) by omega,
          segmentAt_closedConcat_right p q hfinish (j + 1) hj1q]
        rw [point_closedConcat_right_edge p q hfinish (j + 1) (by omega)]
        exact hqrSimple.2.1 j hj
      · have hjoin : i + 2 = p.points.length := by omega
        exact mixed_join_intersection p q hp hq hlenp hlenq hstart hfinish hne
          hint i hi hjoin
  · intro i j hi hj hij hnotwrap
    by_cases hleftj : j + 1 < p.points.length
    · have hlefti : i + 1 < p.points.length := by omega
      rw [segmentAt_closedConcat_left p q i hlefti,
        segmentAt_closedConcat_left p q j hleftj]
      exact hp.2.2 i j hlefti hleftj hij
    · by_cases hlefti : i + 1 < p.points.length
      · have hjright : p.points.length - 1 ≤ j := by omega
        exact mixed_segments_disjoint p q hp hq hlenp hlenq hstart hfinish hint
          i j hlefti hj hjright hij hnotwrap
      · let a := i - (p.points.length - 1)
        let b := j - (p.points.length - 1)
        have hidxi : i = p.points.length - 1 + a := by dsimp [a]; omega
        have hidxj : j = p.points.length - 1 + b := by dsimp [b]; omega
        have hai : a + 1 < q.reverse.points.length := by
          rw [points_length_closedConcat] at hi
          have hqrevlen : q.reverse.points.length = q.points.length := by simp [Polyline.reverse]
          rw [hqrevlen]
          dsimp [a]
          omega
        have hbj : b + 1 < q.reverse.points.length := by
          rw [points_length_closedConcat] at hj
          have hqrevlen : q.reverse.points.length = q.points.length := by simp [Polyline.reverse]
          rw [hqrevlen]
          dsimp [b]
          omega
        have hab : a + 1 < b := by dsimp [a, b] at *; omega
        have haiq : a + 1 < q.points.length := by simpa [Polyline.reverse] using hai
        have hbjq : b + 1 < q.points.length := by simpa [Polyline.reverse] using hbj
        rw [hidxi, hidxj, segmentAt_closedConcat_right p q hfinish a haiq,
          segmentAt_closedConcat_right p q hfinish b hbjq]
        exact hqrSimple.2.2 a b hai hbj hab
  · have hlast : c.points.length - 2 + 1 < c.points.length := by omega
    have hfirstvalid : 0 + 1 < p.points.length := by omega
    have hlastidx : c.points.length - 2 =
        p.points.length - 1 + (q.reverse.points.length - 2) := by
      rw [points_length_closedConcat]
      simp only [Polyline.reverse, List.length_reverse]
      omega
    have hlastrev : q.reverse.points.length - 2 + 1 < q.reverse.points.length := by omega
    have hseg0 : c.segmentAt 0 = p.segmentAt 0 :=
      segmentAt_closedConcat_left p q 0 hfirstvalid
    have hsegLast : c.segmentAt (c.points.length - 2) =
        q.reverse.segmentAt (q.reverse.points.length - 2) := by
      rw [hlastidx]
      exact segmentAt_closedConcat_right p q hfinish _ (by
        simpa [Polyline.reverse] using hlastrev)
    have hc0 : c.point 0 = p.start := by
      calc
        c.point 0 = c.start := point_zero_eq_start c
        _ = p.start := by simp [c, closedConcat, start_concat]
    apply Set.ext
    intro z
    constructor
    · intro hz
      have hzleft : z ∈ p.segmentAt 0 := by rw [← hseg0]; exact hz.1
      have hend := mixed_segment_mem_endpoints p q hfinish hint 0 (c.points.length - 2)
        hfirstvalid hlast (by omega) z hzleft hz.2
      rcases hend with hzstart | hzfinish
      · rw [hc0]
        exact hzstart
      ·
        have hzleft : z ∈ p.segmentAt 0 := by rw [← hseg0]; exact hz.1
        have hfinishFirst : 0 + 2 = p.points.length :=
          finish_mem_segmentAt_index p hp hlenp 0 hfirstvalid
            (by simpa [hzfinish] using hzleft)
        have hzright : z ∈ q.reverse.segmentAt (q.reverse.points.length - 2) := by
          rw [← hsegLast]
          exact hz.2
        have hstartLast : q.reverse.points.length - 2 = 0 :=
          start_mem_segmentAt_index q.reverse hqrSimple hlenqr _ hlastrev
            (by
              have hzstartqr : z = q.reverse.start := by
                calc
                  z = p.finish := hzfinish
                  _ = q.finish := hfinish
                  _ = q.reverse.start := by rw [start_reverse]
              simpa [hzstartqr] using hzright)
        have hlenC : 4 ≤ c.points.length := hlen
        rw [points_length_closedConcat] at hlenC
        have hqrevlen : q.reverse.points.length = q.points.length := by simp [Polyline.reverse]
        rw [hqrevlen] at hstartLast
        omega
    · intro hz
      have hz' : z = c.point 0 := by simpa using hz
      subst z
      constructor
      · rw [hseg0, point_closedConcat_left p q 0 (by omega)]
        change p.point 0 ∈ segment ℝ (p.point 0) (p.point 1)
        exact left_mem_segment ℝ (p.point 0) (p.point 1)
      · rw [hsegLast]
        have hpoint : c.point 0 = q.reverse.point (q.reverse.points.length - 1) := by
          calc
            c.point 0 = c.start := point_zero_eq_start c
            _ = p.start := by simp [c, closedConcat, start_concat]
            _ = q.start := hstart
            _ = q.reverse.finish := by rw [finish_reverse]
            _ = q.reverse.point (q.reverse.points.length - 1) :=
              (point_last_eq_finish q.reverse).symm
        rw [hpoint, show q.reverse.points.length - 1 =
          (q.reverse.points.length - 2) + 1 by omega]
        exact right_mem_segment ℝ _ _
















end Polyline
end DirectedDistances.PlanarMap

end
