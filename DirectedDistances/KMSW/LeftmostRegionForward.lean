module

public import DirectedDistances.KMSW.InfinitePathGraphRay
public import DirectedDistances.KMSW.OutgoingOrderDrawing
public import DirectedDistances.KMSW.LeftmostGeodesicSubmap
public import DirectedDistances.PlanarMap.VariableRayStrip
import DirectedDistances.PlanarMap.SlopeAngularOrder
import Mathlib.Topology.Order.IntermediateValue

/-! # Forward containment between path traces -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set Filter

namespace Polyline

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
private theorem segmentAt_iff_heightFn {p : Polyline} (hp : p.XMonotone)
    {i : ℕ} (hi : i + 1 < p.points.length) {z : ℂ} :
    z ∈ p.segmentAt i ↔
      (p.point i).re ≤ z.re ∧ z.re ≤ (p.point (i + 1)).re ∧
        z.im = p.heightFn z.re := by
  have hab : (p.point i).re < (p.point (i + 1)).re :=
    p.point_re_lt hp (Nat.lt_succ_self i) hi
  rw [Polyline.segmentAt, mem_segment_iff_height hab]
  constructor
  · rintro ⟨hl, hr, hz⟩
    have hlinear := p.heightFn_linear_on_segment hp hi hl hr
    have hlinear' : p.heightFn z.re = segmentHeight (p.point i)
        (p.point (i + 1)) z.re := by
      simpa [segmentHeight] using hlinear
    exact ⟨hl, hr, hz.trans hlinear'.symm⟩
  · rintro ⟨hl, hr, hz⟩
    have hlinear := p.heightFn_linear_on_segment hp hi hl hr
    have hlinear' : p.heightFn z.re = segmentHeight (p.point i)
        (p.point (i + 1)) z.re := by
      simpa [segmentHeight] using hlinear
    exact ⟨hl, hr, hz.trans hlinear'⟩

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
private theorem exists_segment_covering {p : Polyline}
    (hlen : 2 ≤ p.points.length) {x : ℝ} (hlo : p.start.re < x)
    (hhi : x ≤ p.finish.re) :
    ∃ i, i + 1 < p.points.length ∧
      (p.point i).re ≤ x ∧ x ≤ (p.point (i + 1)).re := by
  let n := p.points.length - 1
  have hn : n < p.points.length := by dsimp [n]; omega
  have hlast : p.point n = p.finish := by
    dsimp [n]
    exact p.point_last_eq_finish
  have hex : ∃ j, x ≤ (p.point j).re := ⟨n, by rw [hlast]; exact hhi⟩
  let j := Nat.find hex
  have hj : x ≤ (p.point j).re := Nat.find_spec hex
  have hjle : j ≤ n := Nat.find_min' hex (by rw [hlast]; exact hhi)
  have hjlt : j < p.points.length := lt_of_le_of_lt hjle hn
  have hp0 : p.point 0 = p.start := p.point_zero_eq_start
  have hjpos : 0 < j := by
    by_contra hjnot
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos hjnot
    have hj' : x ≤ (p.point 0).re := by simpa [hjzero] using hj
    rw [hp0] at hj'
    exact (not_le_of_gt hlo) hj'
  let i := j - 1
  have hij : i + 1 = j := by dsimp [i]; omega
  have hilt : i + 1 < p.points.length := by rw [hij]; exact hjlt
  have hleft : (p.point i).re < x := by
    apply lt_of_not_ge
    intro hxi
    have hnot := Nat.find_min hex (show i < j by dsimp [i]; omega)
    exact hnot hxi
  exact ⟨i, hilt, hleft.le, by simpa [hij] using hj⟩

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
private theorem image_eq_heightFn_graph {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) :
    p.image = {z | p.start.re ≤ z.re ∧ z.re ≤ p.finish.re ∧
      z.im = p.heightFn z.re} := by
  have hp0 : p.point 0 = p.start := p.point_zero_eq_start
  have hn : p.points.length - 1 < p.points.length := by omega
  have hlast : p.point (p.points.length - 1) = p.finish :=
    p.point_last_eq_finish
  have hstartfinish : p.start.re < p.finish.re := by
    rw [← hp0, ← hlast]
    exact p.point_re_lt hp (by omega) hn
  ext z
  constructor
  · intro hz
    rcases hz with rfl | ⟨i, hi, hseg⟩
    · have hval : p.heightFn p.start.re = p.start.im := by
        rw [← hp0]
        exact p.heightFn_point hp (by omega)
      exact ⟨le_rfl, hstartfinish.le, hval.symm⟩
    · have hi0 : i < p.points.length := by omega
      have hleft : p.start.re ≤ (p.point i).re := by
        rw [← hp0]
        exact p.point_re_le_of_le hp (Nat.zero_le i) hi0
      have hiright : (p.point (i + 1)).re ≤ p.finish.re := by
        rw [← hlast]
        apply p.point_re_le_of_le hp
        · omega
        · exact hn
      obtain ⟨hl, hr, hh⟩ := (segmentAt_iff_heightFn hp hi).mp hseg
      exact ⟨hleft.trans hl, hr.trans hiright, hh⟩
  · rintro ⟨hl, hr, hh⟩
    by_cases hx : z.re = p.start.re
    · have hval : p.heightFn z.re = p.start.im := by
        rw [hx, ← hp0]
        exact p.heightFn_point hp (by omega)
      have hz' : z = p.start := by
        apply Complex.ext
        · exact hx
        · exact hh.trans hval
      subst z
      exact Or.inl rfl
    · have hlo : p.start.re < z.re := lt_of_le_of_ne hl (Ne.symm hx)
      obtain ⟨i, hi, hiL, hiR⟩ :=
        exists_segment_covering hlen hlo hr
      apply Or.inr
      refine ⟨i, hi, ?_⟩
      exact (segmentAt_iff_heightFn hp hi).mpr ⟨hiL, hiR, hh⟩

end Polyline

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P))

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Equal departure edges give equal heights until their common endpoint. -/
theorem infinitePresentPath_height_eq_of_edge_eq {v : ℕ}
    (U D : InfinitePresentPath w ⟨v⟩) (i j : ℕ) (he : U.edge i = D.edge j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ico
      ((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).start.re
      (((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).start.re + ε),
      infinitePresentPath_height hfin hfam D t =
        infinitePresentPath_height hfin hfam U t := by
  let p := (monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)
  have hp := infinitePresentPath_arc_start_re_lt_finish_re hfin hfam U i
  refine ⟨p.finish.re - p.start.re, sub_pos.mpr hp, ?_⟩
  intro t ht
  have ht' : t ∈ Icc p.start.re p.finish.re := ⟨ht.1, by linarith only [ht.2]⟩
  rw [infinitePresentPath_height_on_arc hfin hfam U i ht']
  have hd := infinitePresentPath_height_on_arc hfin hfam D j (x := t)
  rw [← he] at hd
  exact hd ht'

private theorem height_initial_segment {v : ℕ} (P : InfinitePresentPath w ⟨v⟩)
    (i : ℕ) {t : ℝ}
    (ht : t ∈ Icc
      ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).start.re
      (((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).point 1).re) :
    infinitePresentPath_height hfin hfam P t =
      ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).start.im +
      (((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).initialDirection.im /
        ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).initialDirection.re) *
      (t - ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).start.re) := by
  let p := (monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)
  have hm := infinitePresentPath_arc_xMonotone hfin hfam P i
  have hl := (monotoneLimitDrawing w hfin hfam).arc_length (P.edge i, false)
  change 2 ≤ p.points.length at hl
  have hlast : (p.point 1).re ≤ p.finish.re := by
    rw [← p.point_last_eq_finish]
    exact p.point_re_le_of_le hm (by omega) (by omega)
  rw [infinitePresentPath_height_on_arc hfin hfam P i ⟨ht.1, ht.2.trans hlast⟩]
  have hh := p.heightFn_linear_on_segment hm (i := 0) (by omega)
    (xval := t) (by simpa only [p.point_zero_eq_start] using ht.1) ht.2
  simpa only [Nat.zero_add, p.point_zero_eq_start, Polyline.initialDirection,
    Complex.sub_im, Complex.sub_re] using hh

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Strict angular order at a shared departure gives strict local height order. -/
theorem infinitePresentPath_height_lt_of_departure_arg_lt {v : ℕ}
    (U D : InfinitePresentPath w ⟨v⟩) (i j : ℕ)
    (hs : edgeWest w (U.edge i) = edgeWest w (D.edge j))
    (ha : Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (D.edge j, false)).initialDirection <
      Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).initialDirection) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo
      ((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).start.re
      (((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).start.re + ε),
      infinitePresentPath_height hfin hfam D t <
        infinitePresentPath_height hfin hfam U t := by
  let G := monotoneLimitDrawing w hfin hfam
  let p := G.arc (U.edge i, false)
  let q := G.arc (D.edge j, false)
  have hs' : p.start = q.start := by
    rw [G.arc_start, G.arc_start]
    exact congrArg G.pos hs
  have hp := outgoing_initialDirection_re_pos w hfin hfam _ (U.edge_outgoing i).1
  have hq := outgoing_initialDirection_re_pos w hfin hfam _ (D.edge_outgoing j).1
  have hp' : 0 < (p.point 1).re - p.start.re := hp
  have hq' : 0 < (q.point 1).re - q.start.re := hq
  let ε := min ((p.point 1).re - p.start.re) ((q.point 1).re - q.start.re)
  refine ⟨ε, lt_min hp' hq', ?_⟩
  intro t ht
  have htp : t ∈ Icc p.start.re (p.point 1).re := by
    refine ⟨ht.1.le, ?_⟩
    have hh := min_le_left ((p.point 1).re - p.start.re)
      ((q.point 1).re - q.start.re)
    have htt := ht.2
    change t < p.start.re + ε at htt
    linarith only [htt, hh]
  have htq : t ∈ Icc q.start.re (q.point 1).re := by
    have hh := min_le_right ((p.point 1).re - p.start.re)
      ((q.point 1).re - q.start.re)
    have hsr := congrArg Complex.re hs'
    refine ⟨by linarith only [ht.1, hsr], ?_⟩
    have htt := ht.2
    change t < p.start.re + ε at htt
    linarith only [htt, hh, hsr]
  rw [height_initial_segment w hfin hfam D j htq,
    height_initial_segment w hfin hfam U i htp]
  have hsl := (east_arg_lt_iff_slope_lt hq hp).mp ha
  change q.start.im + q.initialDirection.im / q.initialDirection.re *
      (t - q.start.re) < p.start.im + p.initialDirection.im /
      p.initialDirection.re * (t - p.start.re)
  rw [← hs']
  exact add_lt_add_right (mul_lt_mul_of_pos_right hsl (sub_pos.mpr ht.1)) _

private theorem arc_zero_start {v : ℕ} (P : InfinitePresentPath w ⟨v⟩) :
    ((monotoneLimitDrawing w hfin hfam).arc (P.edge 0, false)).start =
      (monotoneLimitDrawing w hfin hfam).pos v := by
  rw [(monotoneLimitDrawing w hfin hfam).arc_start]
  exact congrArg (monotoneLimitDrawing w hfin hfam).pos P.first_edge_outgoing.2

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Height domination forces reverse ordering of the right endpoints, by height escape. -/
theorem infinitePresentPath_rightEnd_le_of_height_le {v : ℕ}
    (Q R : InfinitePresentPath w ⟨v⟩)
    (hle : ∀ x ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
        (infinitePresentPath_rightEnd hfin hfam Q),
      x ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
        (infinitePresentPath_rightEnd hfin hfam R) →
      infinitePresentPath_height hfin hfam R x ≤
        infinitePresentPath_height hfin hfam Q x) :
    infinitePresentPath_rightEnd hfin hfam Q ≤ infinitePresentPath_rightEnd hfin hfam R := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  generalize hXR : infinitePresentPath_rightEnd hfin hfam R = XR at hlt
  induction XR using WithTop.recTopCoe with
  | top => exact (not_lt_of_ge le_top hlt)
  | coe b =>
    let x₀ := ((monotoneLimitDrawing w hfin hfam).pos v).re
    have hb : x₀ < b := by
      have hh := infinitePresentPath_start_lt_rightEnd hfin hfam R 0
      rw [arc_zero_start w hfin hfam R, hXR] at hh
      exact WithTop.coe_lt_coe.mp hh
    have hsub : Icc x₀ b ⊆ rayDomain x₀
        (infinitePresentPath_rightEnd hfin hfam Q) := by
      intro t ht
      exact ⟨ht.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht.2) hlt⟩
    have hc := infinitePresentPath_height_continuousOn hfin hfam Q
    rw [arc_zero_start w hfin hfam Q] at hc
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hc.mono hsub)
    obtain ⟨a, ha, hbig⟩ := infinitePresentPath_height_escape hfin hfam R (B + 1)
    rw [arc_zero_start w hfin hfam R] at ha hbig
    have hab : a < b := by
      have hh := ha.2
      rw [hXR] at hh
      exact WithTop.coe_lt_coe.mp hh
    have haQ := hsub ⟨ha.1, hab.le⟩
    have h1 := hbig a ha le_rfl
    have h2 := hle a haQ ha
    have h3 := hB (mem_image_of_mem _ (show a ∈ Icc x₀ b from ⟨ha.1, hab.le⟩))
    linarith only [h1, h2, h3]


private theorem exists_active_arc {v : ℕ} (P : InfinitePresentPath w ⟨v⟩) {x : ℝ}
    (hx : x ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
      (infinitePresentPath_rightEnd hfin hfam P)) :
    ∃ i, ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).start.re ≤ x ∧
      x < ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).finish.re := by
  let p := fun i => (monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)
  obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup hx.2
  have hk' : x < (p k).finish.re :=
    (WithTop.coe_lt_coe.mp hk).trans
      (infinitePresentPath_arc_start_re_lt_finish_re hfin hfam P k)
  let hex : ∃ i, x < (p i).finish.re := ⟨k, hk'⟩
  let i := Nat.find hex
  refine ⟨i, ?_, Nat.find_spec hex⟩
  by_cases hi : i = 0
  · simpa only [hi, p, arc_zero_start w hfin hfam P] using hx.1
  · have hn := Nat.find_min hex (show i - 1 < i by omega)
    have hs := congrArg Complex.re (infinitePresentPath_arc_seam hfin hfam P (i - 1))
    rw [Nat.sub_add_cancel (show 1 ≤ i by omega)] at hs
    exact hs ▸ le_of_not_gt hn

private theorem active_point_mem {v : ℕ} (P : InfinitePresentPath w ⟨v⟩)
    (i : ℕ) {x : ℝ}
    (hx : x ∈ Icc
      ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).start.re
      ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).finish.re) :
    (⟨x, infinitePresentPath_height hfin hfam P x⟩ : ℂ) ∈
      ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).image := by
  rw [Polyline.image_eq_heightFn_graph (infinitePresentPath_arc_xMonotone hfin hfam P i)
    ((monotoneLimitDrawing w hfin hfam).arc_length (P.edge i, false))]
  exact ⟨hx.1, hx.2, infinitePresentPath_height_on_arc hfin hfam P i hx⟩

private theorem contact_is_start {v : ℕ} (U D : InfinitePresentPath w ⟨v⟩)
    (i j : ℕ) {z : ℂ}
    (hu : z ∈ ((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).image)
    (hd : z ∈ ((monotoneLimitDrawing w hfin hfam).arc (D.edge j, false)).image)
    (hur : z.re < ((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).finish.re)
    (hdr : z.re < ((monotoneLimitDrawing w hfin hfam).arc (D.edge j, false)).finish.re)
    (hne : U.edge i ≠ D.edge j) :
    z = ((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).start := by
  let G := monotoneLimitDrawing w hfin hfam
  let p := G.arc (U.edge i, false)
  let q := G.arc (D.edge j, false)
  have hpfin : z ≠ p.finish := fun h => (ne_of_lt hur) (congrArg Complex.re h)
  have hqfin : z ≠ q.finish := fun h => (ne_of_lt hdr) (congrArg Complex.re h)
  by_contra hstart
  have hpi : z ∈ p.interior := ⟨hu, by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hstart, hpfin⟩⟩
  by_cases hqstart : z = q.start
  · have hv := G.interior_avoids_vertices (U.edge i, false) (edgeWest w (D.edge j))
    have he : q.start = G.pos (edgeWest w (D.edge j)) := G.arc_start _
    rw [hqstart, he] at hpi
    exact hv hpi
  · have hqi : z ∈ q.interior := ⟨hd, by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hqstart, hqfin⟩⟩
    have hdis := G.interior_disjoint (U.edge i, false) (D.edge j, false)
      (fun h => hne (congrArg Prod.fst h).symm) (by simp)
    exact Set.disjoint_left.mp hdis hpi hqi

private theorem continuous_le_of_local_right {f g : ℝ → ℝ} {x₀ b : ℝ}
    (hb : x₀ ≤ b) (hf : ContinuousOn f (Icc x₀ b)) (hg : ContinuousOn g (Icc x₀ b))
    (hstart : f x₀ = g x₀)
    (hloc : ∀ a ∈ Icc x₀ b, f a = g a →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo a (a + ε), f t ≤ g t) : f b ≤ g b := by
  by_contra hnot
  have hfb : g b < f b := lt_of_not_ge hnot
  let S := {x ∈ Icc x₀ b | f x ≤ g x}
  have hclosed : IsClosed S := isClosed_Icc.isClosed_le hf hg
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ h => h.1)
  have hS : x₀ ∈ S := ⟨⟨le_rfl, hb⟩, hstart.le⟩
  obtain ⟨a, ha, hmax⟩ := hcompact.exists_isMaxOn ⟨x₀, hS⟩ continuous_id.continuousOn
  have hab : a < b := lt_of_le_of_ne ha.1.2 (by
    intro he
    have hh := ha.2
    rw [he] at hh
    exact (not_le_of_gt hfb) hh)
  have heq : f a = g a := by
    apply le_antisymm ha.2
    by_contra hn
    have hneg : f a - g a < 0 := sub_neg.mpr (lt_of_not_ge hn)
    have hpos : 0 < f b - g b := sub_pos.mpr hfb
    have hsub : Icc a b ⊆ Icc x₀ b := Icc_subset_Icc_left ha.1.1
    obtain ⟨c, hc, hzero⟩ := intermediate_value_Icc hab.le
      ((hf.sub hg).mono hsub) (show (0 : ℝ) ∈ Icc (f a - g a) (f b - g b) from
        ⟨hneg.le, hpos.le⟩)
    change f c - g c = 0 at hzero
    have hca : a < c := lt_of_le_of_ne hc.1 (by
      intro he
      rw [← he] at hzero
      exact (ne_of_lt hneg) hzero)
    have hcS : c ∈ S := ⟨hsub hc, by linarith only [hzero]⟩
    exact (not_le_of_gt hca) (hmax hcS)
  obtain ⟨ε, hε, hlocal⟩ := hloc a ha.1 heq
  obtain ⟨t, hat, htr⟩ := exists_between (lt_min (lt_add_of_pos_right a hε) hab)
  have htlocal := hlocal t ⟨hat, htr.trans_le (min_le_left _ _)⟩
  have htS : t ∈ S := ⟨⟨ha.1.1.trans hat.le, (htr.trans_le (min_le_right _ _)).le⟩,
    htlocal⟩
  exact (not_le_of_gt hat) (hmax htS)


private theorem departure_arg_lt {v : ℕ} (U D : InfinitePresentPath w ⟨v⟩)
    (i j : ℕ) (h : SharedDepartureWeaklyRight w hfin hL htrans hR U D i j)
    (hne : U.edge i ≠ D.edge j) :
    Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (D.edge j, false)).initialDirection <
      Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (U.edge i, false)).initialDirection := by
  classical
  have hs : edgeWest w (U.edge i) = edgeWest w (D.edge j) := by
    rw [(InfinitePresentPath.edge_outgoing_at_initial w U i).2,
      (InfinitePresentPath.edge_outgoing_at_initial w D j).2, h.1]
  let u := edgeWest w (U.edge i)
  let hv := kmsw_vertex_allocated_of_finite_incidence w hfin u
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR u hv
  have hu : U.edge i ∈ es :=
    (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR u hv _).mpr
      ⟨(U.edge_outgoing i).1, rfl⟩
  have hd : D.edge j ∈ es :=
    (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR u hv _).mpr
      ⟨(D.edge_outgoing j).1, hs.symm⟩
  have hidx : es.idxOf (U.edge i) ≤ es.idxOf (D.edge j) := by
    have hh := h.2
    dsimp only [kmswPrefixOutgoingEdges] at hh
    simpa only [← (U.edge_outgoing i).2] using hh
  have hstrict : es.idxOf (U.edge i) < es.idxOf (D.edge j) :=
    lt_of_le_of_ne hidx (fun he => hne ((List.idxOf_inj hu).mp he))
  exact (kmswOutgoingEdgesLeftToRight_idxOf_lt_iff_arg_lt w hfin hfam hL htrans hR
    u hv _ _ hu hd).mp hstrict

private theorem contact_local_le {v : ℕ} (U D : InfinitePresentPath w ⟨v⟩)
    (h : GeodesicSharedDeparturesRightOf w hfin hL htrans hR v U D) {x : ℝ}
    (hxU : x ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
      (infinitePresentPath_rightEnd hfin hfam U))
    (hxD : x ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
      (infinitePresentPath_rightEnd hfin hfam D))
    (heq : infinitePresentPath_height hfin hfam D x =
      infinitePresentPath_height hfin hfam U x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo x (x + ε),
      infinitePresentPath_height hfin hfam D t ≤
        infinitePresentPath_height hfin hfam U t := by
  let G := monotoneLimitDrawing w hfin hfam
  obtain ⟨i, hiL, hiR⟩ := exists_active_arc w hfin hfam U hxU
  obtain ⟨j, hjL, hjR⟩ := exists_active_arc w hfin hfam D hxD
  by_cases he : U.edge i = D.edge j
  · let ε := (G.arc (U.edge i, false)).finish.re - x
    refine ⟨ε, sub_pos.mpr hiR, ?_⟩
    intro t ht
    have hti : t ∈ Icc (G.arc (U.edge i, false)).start.re
        (G.arc (U.edge i, false)).finish.re :=
      ⟨hiL.trans ht.1.le, by change t ≤ _; dsimp [ε] at ht; linarith only [ht.2]⟩
    rw [infinitePresentPath_height_on_arc hfin hfam U i hti]
    have htj : t ∈ Icc (G.arc (D.edge j, false)).start.re
        (G.arc (D.edge j, false)).finish.re := by simpa only [he] using hti
    rw [infinitePresentPath_height_on_arc hfin hfam D j htj, he]
  · let z : ℂ := ⟨x, infinitePresentPath_height hfin hfam U x⟩
    have hzi := active_point_mem w hfin hfam U i ⟨hiL, hiR.le⟩
    have hzj := active_point_mem w hfin hfam D j ⟨hjL, hjR.le⟩
    rw [heq] at hzj
    have hsi := contact_is_start w hfin hfam U D i j hzi hzj hiR hjR he
    have hsj := contact_is_start w hfin hfam D U j i hzj hzi hjR hiR (Ne.symm he)
    have hstarts : (G.arc (U.edge i, false)).start =
        (G.arc (D.edge j, false)).start := hsi.symm.trans hsj
    have hwest : edgeWest w (U.edge i) = edgeWest w (D.edge j) := by
      apply G.pos_injective
      have hu : (G.arc (U.edge i, false)).start = G.pos (edgeWest w (U.edge i)) :=
        G.arc_start _
      have hd : (G.arc (D.edge j, false)).start = G.pos (edgeWest w (D.edge j)) :=
        G.arc_start _
      exact hu.symm.trans (hstarts.trans hd)
    have hinit : (U.initial i).1 = (D.initial j).1 := by
      exact congrArg (fun n : ℕ => (⟨n⟩ : PresentVertex w))
        ((InfinitePresentPath.edge_outgoing_at_initial w U i).2.symm.trans
          (hwest.trans (InfinitePresentPath.edge_outgoing_at_initial w D j).2))
    have harg := departure_arg_lt w hfin hL htrans hR hfam U D i j (h i j hinit) he
    obtain ⟨ε, hε, hlocal⟩ := infinitePresentPath_height_lt_of_departure_arg_lt
      w hfin hfam U D i j hwest harg
    have hx : x = (G.arc (U.edge i, false)).start.re := congrArg Complex.re hsi
    refine ⟨ε, hε, fun t ht => ?_⟩
    have ht' : t ∈ Ioo (G.arc (U.edge i, false)).start.re
        ((G.arc (U.edge i, false)).start.re + ε) := by
      rw [← hx]
      exact ht
    exact (hlocal t ht').le

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Weakly right shared departures imply a global weak height inequality. -/
theorem infinitePresentPath_height_le_of_sharedDeparturesRightOf (v : ℕ)
    (U D : InfinitePresentPath w ⟨v⟩)
    (h : GeodesicSharedDeparturesRightOf w hfin hL htrans hR v U D) (x : ℝ)
    (hxU : x ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
      (infinitePresentPath_rightEnd hfin hfam U))
    (hxD : x ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
      (infinitePresentPath_rightEnd hfin hfam D)) :
    infinitePresentPath_height hfin hfam D x ≤
      infinitePresentPath_height hfin hfam U x := by
  let x₀ := ((monotoneLimitDrawing w hfin hfam).pos v).re
  have hsubU : Icc x₀ x ⊆ rayDomain x₀
      (infinitePresentPath_rightEnd hfin hfam U) := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht.2) hxU.2⟩
  have hsubD : Icc x₀ x ⊆ rayDomain x₀
      (infinitePresentPath_rightEnd hfin hfam D) := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht.2) hxD.2⟩
  have hcU := infinitePresentPath_height_continuousOn hfin hfam U
  have hcD := infinitePresentPath_height_continuousOn hfin hfam D
  rw [arc_zero_start w hfin hfam U] at hcU
  rw [arc_zero_start w hfin hfam D] at hcD
  have hs (P : InfinitePresentPath w ⟨v⟩) :
      infinitePresentPath_height hfin hfam P x₀ =
        ((monotoneLimitDrawing w hfin hfam).pos v).im := by
    have hh := height_initial_segment w hfin hfam P 0 (t := x₀)
    rw [arc_zero_start w hfin hfam P] at hh
    have hpos := outgoing_initialDirection_re_pos w hfin hfam _ P.first_edge_outgoing.1
    have hbound : x₀ ≤
        (((monotoneLimitDrawing w hfin hfam).arc (P.edge 0, false)).point 1).re := by
      change 0 < _ - _ at hpos
      rw [arc_zero_start w hfin hfam P] at hpos
      exact (sub_pos.mp hpos).le
    dsimp only [x₀] at hh
    simpa only [sub_self, mul_zero, add_zero] using hh ⟨le_rfl, hbound⟩
  apply continuous_le_of_local_right hxU.1 (hcD.mono hsubD) (hcU.mono hsubU)
    ((hs D).trans (hs U).symm)
  intro a ha heq
  exact contact_local_le w hfin hL htrans hR hfam U D h (hsubU ha) (hsubD ha) heq


/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Shared-departure containment implies containment in the closed region between traces. -/
theorem trace_subset_closedBetween_of_inBetween (v : ℕ)
    (P R Q : InfinitePresentPath w ⟨v⟩)
    (h : InBetweenLeftmostRightmost w hfin hL htrans hR v P R Q) :
    pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)) ⊆
      closedBetween
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P.edge i, false)))
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false))) := by
  have hQR : GeodesicSharedDeparturesRightOf w hfin hL htrans hR v Q R := by
    intro i j hs
    exact h.2 j i hs.symm
  have hlo := infinitePresentPath_height_le_of_sharedDeparturesRightOf
    w hfin hL htrans hR hfam v Q R hQR
  have hend : infinitePresentPath_rightEnd hfin hfam Q ≤
      infinitePresentPath_rightEnd hfin hfam R :=
    infinitePresentPath_rightEnd_le_of_height_le w hfin hfam Q R (fun x hxQ hxR =>
      hlo x hxQ hxR)
  have eP := infinitePresentPath_trace_eq_graph hfin hfam P
  have eR := infinitePresentPath_trace_eq_graph hfin hfam R
  have eQ := infinitePresentPath_trace_eq_graph hfin hfam Q
  rw [arc_zero_start w hfin hfam P] at eP
  rw [arc_zero_start w hfin hfam R] at eR
  rw [arc_zero_start w hfin hfam Q] at eQ
  intro z hz
  obtain ⟨hzQ, hzi⟩ := (Set.ext_iff.mp eQ z).mp hz
  have hzR : z.re ∈ rayDomain ((monotoneLimitDrawing w hfin hfam).pos v).re
      (infinitePresentPath_rightEnd hfin hfam R) := ⟨hzQ.1, hzQ.2.trans_le hend⟩
  rw [mem_closedBetween_iff eP eR]
  refine ⟨hzR, ?_, fun hzP => ?_⟩
  · rw [hzi]
    exact hlo z.re hzQ hzR
  · rw [hzi]
    exact infinitePresentPath_height_le_of_sharedDeparturesRightOf
      w hfin hL htrans hR hfam v P Q h.1 z.re hzP hzQ

end DirectedDistances.KMSW
