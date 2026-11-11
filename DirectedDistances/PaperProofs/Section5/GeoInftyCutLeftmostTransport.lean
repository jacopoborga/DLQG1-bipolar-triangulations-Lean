/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmostExist
import DirectedDistances.RandomWalk.PastCodeLaw
import DirectedDistances.KMSW.InftyCutSequence

/-! Supporting lemmas for paper labels `lem-geo-infty` (see CORRESPONDENCE.md). -/

/-! # Drawing comparisons for the run-zero leftmost-geodesic transport

Deterministic helpers toward Lemma 5.4 (`lem-geo-infty`),
The angular characterization below applies to raw codes, without global
nonnegativity or transience hypotheses. Finite eligible extensions construct
the raw leftmost path directly. The cut comparison transfers by literal arc
restriction; common finite-avoidance vertices give pairwise coalescence.
No identification between the hatted and raw drawings is needed. -/

public section
namespace DirectedDistances.PaperProofs.Section5.LeftmostTransport

open Filter Set Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap

namespace Polyline

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result. -/
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

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result. -/
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

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result. -/
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


variable (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P))




@[expose] def SharedDepartureArgRightOf {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) : Prop :=
  ∀ i j, (P.initial i).1 = (Q.initial j).1 →
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (Q.edge j, false)).initialDirection ≤
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (P.edge i, false)).initialDirection

private theorem arc_start_at_initial {v : ℕ} (U : InfinitePresentPath w ⟨v⟩) (m : ℕ) :
    ((monotoneLimitDrawing w hfin hfam).arc (U.edge m, false)).start =
      (monotoneLimitDrawing w hfin hfam).pos (U.initial m).1.id := by
  rw [(monotoneLimitDrawing w hfin hfam).arc_start]
  change (monotoneLimitDrawing w hfin hfam).pos (edgeWest w (U.edge m)) = _
  rw [(U.edge_outgoing_at_initial w m).2]


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

private theorem arc_zero_start {v : ℕ} (P : InfinitePresentPath w ⟨v⟩) :
    ((monotoneLimitDrawing w hfin hfam).arc (P.edge 0, false)).start =
      (monotoneLimitDrawing w hfin hfam).pos v := by
  rw [(monotoneLimitDrawing w hfin hfam).arc_start]
  exact congrArg (monotoneLimitDrawing w hfin hfam).pos P.first_edge_outgoing.2

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


private theorem contact_local_le {v : ℕ} (U D : InfinitePresentPath w ⟨v⟩)
    (h : SharedDepartureArgRightOf w hfin hfam U D) {x : ℝ}
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
    have harg : Complex.arg (G.arc (D.edge j, false)).initialDirection <
        Complex.arg (G.arc (U.edge i, false)).initialDirection := by
      apply lt_of_le_of_ne (h i j hinit)
      intro ha
      apply he
      exact congrArg Prod.fst (G.initial_arg_injective (U.edge i, false) (D.edge j, false) hwest ha.symm)
    obtain ⟨ε, hε, hlocal⟩ := infinitePresentPath_height_lt_of_departure_arg_lt
      w hfin hfam U D i j hwest harg
    have hx : x = (G.arc (U.edge i, false)).start.re := congrArg Complex.re hsi
    refine ⟨ε, hε, fun t ht => ?_⟩
    have ht' : t ∈ Ioo (G.arc (U.edge i, false)).start.re
        ((G.arc (U.edge i, false)).start.re + ε) := by
      rw [← hx]
      exact ht
    exact (hlocal t ht').le



theorem height_le_of_sharedDepartureArgRightOf (v : ℕ)
    (U D : InfinitePresentPath w ⟨v⟩)
    (h : SharedDepartureArgRightOf w hfin hfam U D) (x : ℝ)
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
  exact contact_local_le w hfin hfam U D h (hsubU ha) (hsubD ha) heq





theorem trace_subset_closedBetween_of_departureArgs (v : ℕ)
    (P R Q : InfinitePresentPath w ⟨v⟩)
    (h : SharedDepartureArgRightOf w hfin hfam P Q ∧
      SharedDepartureArgRightOf w hfin hfam Q R) :
    pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)) ⊆
      closedBetween
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P.edge i, false)))
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false))) := by
  have hlo := height_le_of_sharedDepartureArgRightOf
    w hfin hfam v Q R h.2
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
    exact height_le_of_sharedDepartureArgRightOf
      w hfin hfam v P Q h.1 z.re hzP hzQ

private theorem arc_abscissa_mem_domain {v : ℕ} (U : InfinitePresentPath w ⟨v⟩)
    (m : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc
      ((monotoneLimitDrawing w hfin hfam).arc (U.edge m, false)).start.re
      ((monotoneLimitDrawing w hfin hfam).arc (U.edge m, false)).finish.re) :
    t ∈ rayDomain
      ((monotoneLimitDrawing w hfin hfam).arc (U.edge 0, false)).start.re
      (infinitePresentPath_rightEnd hfin hfam U) := by
  refine ⟨((infinitePresentPath_start_re_strictMono hfin hfam U).monotone
    (Nat.zero_le m)).trans ht.1, ?_⟩
  have hr := ht.2
  rw [infinitePresentPath_arc_seam hfin hfam U m] at hr
  exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hr)
    (infinitePresentPath_start_lt_rightEnd hfin hfam U (m + 1))

private theorem strict_height_graph_points {v : ℕ}
    (U D : InfinitePresentPath w ⟨v⟩) (m n : ℕ)
    (hs : (U.initial m).1 = (D.initial n).1)
    (harg : Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (D.edge n, false)).initialDirection <
      Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (U.edge m, false)).initialDirection) :
    ∃ t : ℝ,
      (⟨t, infinitePresentPath_height hfin hfam U t⟩ : ℂ) ∈
        pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (U.edge i, false)) ∧
      (⟨t, infinitePresentPath_height hfin hfam D t⟩ : ℂ) ∈
        pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (D.edge i, false)) ∧
      infinitePresentPath_height hfin hfam D t <
        infinitePresentPath_height hfin hfam U t := by
  obtain ⟨ε, hε, hlt⟩ :=
    infinitePresentPath_height_lt_after_shared_departure w hfin hfam U D m n hs harg
  let G := monotoneLimitDrawing w hfin hfam
  let s := (G.pos (U.initial m).1.id).re
  let a := (G.arc (U.edge m, false)).finish.re - s
  let b := (G.arc (D.edge n, false)).finish.re - s
  have hUs : (G.arc (U.edge m, false)).start.re = s :=
    congrArg Complex.re (arc_start_at_initial w hfin hfam U m)
  have hDs : (G.arc (D.edge n, false)).start.re = s := by
    rw [arc_start_at_initial w hfin hfam D n, ← hs]
  have ha : 0 < a := by
    have h := infinitePresentPath_arc_start_re_lt_finish_re hfin hfam U m
    change 0 < (G.arc (U.edge m, false)).finish.re - s
    rw [hUs] at h
    exact sub_pos.mpr h
  have hb : 0 < b := by
    have h := infinitePresentPath_arc_start_re_lt_finish_re hfin hfam D n
    change 0 < (G.arc (D.edge n, false)).finish.re - s
    rw [hDs] at h
    exact sub_pos.mpr h
  let d := min ε (min a b)
  have hd : 0 < d := lt_min hε (lt_min ha hb)
  have hdε : d ≤ ε := min_le_left _ _
  have hda : d ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hdb : d ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  let t := s + d / 2
  have hst : s < t := by dsimp [t]; linarith only [hd]
  have htε : t < s + ε := by dsimp [t]; linarith only [hd, hdε]
  have htU : t ≤ (G.arc (U.edge m, false)).finish.re := by
    dsimp [t, a] at *
    linarith only [hd, hda]
  have htD : t ≤ (G.arc (D.edge n, false)).finish.re := by
    dsimp [t, b] at *
    linarith only [hd, hdb]
  refine ⟨t, infinitePresentPath_height_point_mem_trace w hfin hfam U
    (arc_abscissa_mem_domain w hfin hfam U m ⟨?_, htU⟩),
    infinitePresentPath_height_point_mem_trace w hfin hfam D
    (arc_abscissa_mem_domain w hfin hfam D n ⟨?_, htD⟩), hlt t ⟨hst, htε⟩⟩
  · rw [hUs]
    exact hst.le
  · rw [hDs]
    exact hst.le




theorem trace_subset_closedBetween_iff_departureArgs (v : ℕ)
    (P R Q : InfinitePresentPath w ⟨v⟩) :
    pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)) ⊆
      closedBetween
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P.edge i, false)))
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false))) ↔
    SharedDepartureArgRightOf w hfin hfam P Q ∧
      SharedDepartureArgRightOf w hfin hfam Q R := by
  constructor
  · intro hsub
    constructor
    · intro m n hs
      by_contra h
      have ha := lt_of_not_ge h
      obtain ⟨t, hQ, hP, hlt⟩ :=
        strict_height_graph_points w hfin hfam Q P n m hs.symm ha
      have hbound := (hsub hQ).2 _ hP rfl
      exact (not_le_of_gt hlt) hbound
    · intro n m hs
      by_contra h
      have ha := lt_of_not_ge h
      obtain ⟨t, _, hQ, hlt⟩ :=
        strict_height_graph_points w hfin hfam R Q m n hs.symm ha
      obtain ⟨r, hr, hre, him⟩ := (hsub hQ).1
      rw [infinitePresentPath_trace_eq_graph hfin hfam R] at hr
      have hri := hr.2
      rw [hre] at hri
      rw [hri] at him
      exact (not_le_of_gt hlt) him
  · exact trace_subset_closedBetween_of_departureArgs w hfin hfam v P R Q



theorem SharedDepartureArgRightOf.antisymm {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩)
    (hPQ : SharedDepartureArgRightOf w hfin hfam P Q)
    (hQP : SharedDepartureArgRightOf w hfin hfam Q P) : P.edge = Q.edge := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hpfx : List.ofFn (fun i : Fin n => P.edge i.val) =
        List.ofFn (fun i : Fin n => Q.edge i.val) := by
      apply congrArg List.ofFn
      funext i
      exact ih i.val i.isLt
    have hs := P.initial_vertex_eq_of_prefix_eq Q n hpfx
    have ha := le_antisymm (hQP n n hs.symm) (hPQ n n hs)
    have hv : kmswLimitDartVertex w (P.edge n, false) =
        kmswLimitDartVertex w (Q.edge n, false) := by
      change edgeWest w (P.edge n) = edgeWest w (Q.edge n)
      rw [(P.edge_outgoing_at_initial w n).2,
        (Q.edge_outgoing_at_initial w n).2, hs]
    exact congrArg Prod.fst ((monotoneLimitDrawing w hfin hfam).initial_arg_injective
      (P.edge n, false) (Q.edge n, false) hv ha)





theorem planar_leftmost_ldp_edge_unique {v : ℕ}
    (P Q R : InfinitePresentPath w ⟨v⟩)
    (hP : P.HasLongestSegments) (hQ : Q.HasLongestSegments)
    (hleftP : ∀ S : InfinitePresentPath w ⟨v⟩, S.HasLongestSegments →
      pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (S.edge i, false)) ⊆
        closedBetween
          (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P.edge i, false)))
          (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false))))
    (hleftQ : ∀ S : InfinitePresentPath w ⟨v⟩, S.HasLongestSegments →
      pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (S.edge i, false)) ⊆
        closedBetween
          (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)))
          (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false)))) :
    P.edge = Q.edge := by
  exact SharedDepartureArgRightOf.antisymm w hfin hfam P Q
    ((trace_subset_closedBetween_iff_departureArgs w hfin hfam v P R Q).mp
      (hleftP Q hQ)).1
    ((trace_subset_closedBetween_iff_departureArgs w hfin hfam v Q R P).mp
      (hleftQ P hP)).1




private theorem exists_arg_max_extension (v : ℕ) (pfx : List ℕ)
    (hp : StartsInfiniteLdpGeodesicWithPrefix w v pfx) :
    ∃ e, StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [e]) ∧
      ∀ f, StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [f]) →
        Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection ≤
          Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection := by
  classical
  have hfinite := startsInfiniteLdpGeodesicWithPrefix_extensions_finite w hfin v pfx
  let S := hfinite.toFinset
  obtain ⟨a, ha⟩ := hp.exists_extension
  have hS : S.Nonempty := ⟨a, hfinite.mem_toFinset.mpr ha⟩
  obtain ⟨e, he, hmax⟩ := S.exists_max_image
    (fun f => Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection) hS
  exact ⟨e, hfinite.mem_toFinset.mp he,
    fun f hf => hmax f (hfinite.mem_toFinset.mpr hf)⟩

private noncomputable def argPrefixes (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    ℕ → {pfx : List ℕ // StartsInfiniteLdpGeodesicWithPrefix w v pfx}
  | 0 => ⟨[], by obtain ⟨P, hP⟩ := hg; exact ⟨P, hP, rfl⟩⟩
  | n + 1 =>
    let p := argPrefixes v hg n
    let he := exists_arg_max_extension w hfin hfam v p.val p.property
    ⟨p.val ++ [he.choose], he.choose_spec.1⟩

private noncomputable def argEdge (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) : ℕ :=
  (exists_arg_max_extension w hfin hfam v
    (argPrefixes w hfin hfam v hg n).val (argPrefixes w hfin hfam v hg n).property).choose

private theorem argPrefixes_succ (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (argPrefixes w hfin hfam v hg (n + 1)).val =
      (argPrefixes w hfin hfam v hg n).val ++ [argEdge w hfin hfam v hg n] := rfl

private theorem argPrefixes_eq_ofFn (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (argPrefixes w hfin hfam v hg n).val =
      List.ofFn (fun i : Fin n => argEdge w hfin hfam v hg i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [argPrefixes_succ, ih, List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

private theorem argPrefixes_length (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (argPrefixes w hfin hfam v hg n).val.length = n := by
  rw [argPrefixes_eq_ofFn, List.length_ofFn]

private noncomputable def argPrefixWitness (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    InfinitePresentPath w ⟨v⟩ :=
  (argPrefixes w hfin hfam v hg n).property.choose

private theorem argPrefixWitness_longest (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (argPrefixWitness w hfin hfam v hg n).HasLongestSegments :=
  (argPrefixes w hfin hfam v hg n).property.choose_spec.1

private theorem argPrefixWitness_edges (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    List.ofFn (fun i : Fin n => (argPrefixWitness w hfin hfam v hg n).edge i.val) =
      List.ofFn (fun i : Fin n => argEdge w hfin hfam v hg i.val) := by
  have he := (argPrefixes w hfin hfam v hg n).property.choose_spec.2
  change List.ofFn (fun i : Fin (argPrefixes w hfin hfam v hg n).val.length =>
    (argPrefixWitness w hfin hfam v hg n).edge i.val) =
      (argPrefixes w hfin hfam v hg n).val at he
  have he' : List.ofFn (fun i : Fin n =>
      (argPrefixWitness w hfin hfam v hg n).edge i.val) =
        (argPrefixes w hfin hfam v hg n).val := by
    simpa only [argPrefixes_length, Fin.val_cast] using he
  exact he'.trans (argPrefixes_eq_ofFn w hfin hfam v hg n)

private noncomputable def argPath (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    InfinitePresentPath w ⟨v⟩ where
  edge := argEdge w hfin hfam v hg
  initial n := (argPrefixWitness w hfin hfam v hg n).initial n
  prefix_length n := (argPrefixWitness w hfin hfam v hg n).prefix_length n
  prefix_edges n := ((argPrefixWitness w hfin hfam v hg n).prefix_edges n).trans
    (argPrefixWitness_edges w hfin hfam v hg n)

private theorem argPath_longest (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    (argPath w hfin hfam v hg).HasLongestSegments := by
  intro a b ha hab
  obtain ⟨z, q, hlen, he, hq⟩ :=
    argPrefixWitness_longest w hfin hfam v hg b a b ha hab
  exact ⟨z, q, hlen, he.trans (congrArg (fun es : List ℕ => es.drop (a - 1))
    (argPrefixWitness_edges w hfin hfam v hg b)), hq⟩

private theorem argPath_firstDivergence (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments)
    (Q : InfinitePresentPath w ⟨v⟩) (hQ : Q.HasLongestSegments)
    (n : ℕ) (hn : ∀ i, i < n → (argPath w hfin hfam v hg).edge i = Q.edge i) :
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (Q.edge n, false)).initialDirection ≤
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc
        ((argPath w hfin hfam v hg).edge n, false)).initialDirection := by
  have hs : List.ofFn (fun i : Fin n => Q.edge i.val) =
      (argPrefixes w hfin hfam v hg n).val := by
    rw [argPrefixes_eq_ofFn]
    apply congrArg List.ofFn
    funext i
    exact (hn i.val i.isLt).symm
  have hc : StartsInfiniteLdpGeodesicWithPrefix w v
      ((argPrefixes w hfin hfam v hg n).val ++ [Q.edge n]) := by
    refine ⟨Q, hQ, ?_⟩
    simpa only [List.length_append, List.length_singleton, argPrefixes_length,
      List.ofFn_succ', List.concat_eq_append, Fin.val_cast, Fin.val_castSucc, Fin.val_last]
      using congrArg (fun es : List ℕ => es ++ [Q.edge n]) hs
  exact (exists_arg_max_extension w hfin hfam v
    (argPrefixes w hfin hfam v hg n).val
    (argPrefixes w hfin hfam v hg n).property).choose_spec.2 (Q.edge n) hc






theorem exists_sharedDepartureArg_leftmost_ldp (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments ∧
      ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
        SharedDepartureArgRightOf w hfin hfam P Q := by
  let P := argPath w hfin hfam v hg
  have hP := argPath_longest w hfin hfam v hg
  refine ⟨P, hP, fun Q hQ m n hs => ?_⟩
  have hmn := P.index_eq_of_initial_eq w Q hP hQ m n hs
  subst n
  obtain ⟨S, hS, he⟩ := P.exists_geodesic_splice w Q hP hQ m hs
  have hmax := argPath_firstDivergence w hfin hfam v hg S hS m (by
    intro i hi
    rw [he i, ite_eq_left hi])
  rw [he m, ite_eq_right (Nat.lt_irrefl m)] at hmax
  exact hmax


private theorem incoming_geometric_initialDirection_re_neg (e : ℕ) :
    ((monotoneLimitDrawing w hfin hfam).arc (e, true)).initialDirection.re < 0 := by
  have hn := kmsw_edge_allocated_by_self w e
  have ha := monotoneLimitDrawing_arc_layout w hfin hfam e e hn false
  simp only [Bool.false_eq_true, ↓reduceIte] at ha
  rw [monotoneLimitDrawing_arc_layout w hfin hfam e e hn true]
  apply Polyline.reverse_initialDirection_re_neg
  · exact layoutArc_points_pairwise w e e hn
  · rw [← ha]
    exact (monotoneLimitDrawing w hfin hfam).arc_length (e, false)

private theorem backward_east_turn_after_west {a b c : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : c.re < 0)
    (hba : Complex.arg b < Complex.arg a) : ccwTurn a c < ccwTurn a b := by
  have hab := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hbb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
  have hnot : ¬Complex.arg a < Complex.arg b := not_lt.mpr hba.le
  by_cases him : c.im < 0
  · have hcb := (west_arg_lt_lower hc him).trans hbb.1
    have hca : ¬Complex.arg a < Complex.arg c := not_lt.mpr (hcb.trans hba).le
    simp only [ccwTurn, hnot, hca, ↓reduceIte]
    linarith only [hcb]
  · have hac := hab.2.trans (west_arg_gt_upper hc (le_of_not_gt him))
    simp only [ccwTurn, hnot, hac, ↓reduceIte]
    have hcp := Complex.arg_le_pi c
    linarith only [hcp, hbb.1, Real.pi_pos]

private theorem outgoing_rotation_arg_lt_of_incoming (v : ℕ)
    (hin : ∃ i, edgeEast w i = v)
    (e f : ℕ) (he : EdgePresent w e) (hf : EdgePresent w f)
    (hev : edgeWest w e = v) (hfv : edgeWest w f = v) (hne : e ≠ f)
    (hrot : kmswInfRot w hfin (e, false) = (f, false)) :
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection <
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection := by
  let G := monotoneLimitDrawing w hfin hfam
  obtain ⟨i, hiv⟩ := hin
  have hr := G.rotation_agreement (e, false)
  rw [hrot] at hr
  have hargne : Complex.arg (G.arc (e, false)).initialDirection ≠
      Complex.arg (G.arc (f, false)).initialDirection := by
    intro h
    exact hne (congrArg Prod.fst (G.initial_arg_injective _ _
      (show kmswLimitDartVertex w (e, false) = kmswLimitDartVertex w (f, false)
        from hev.trans hfv.symm) h))
  rcases hr.2.2.2 with hs | hs
  · exact (hne (congrArg Prod.fst hs.1).symm).elim
  · by_contra hn
    have hback : Complex.arg (G.arc (f, false)).initialDirection <
        Complex.arg (G.arc (e, false)).initialDirection :=
      lt_of_le_of_ne (le_of_not_gt hn) hargne.symm
    have hmin := hs.2 (i, true)
      (show kmswLimitDartVertex w (i, true) = kmswLimitDartVertex w (e, false)
        from hiv.trans hev.symm) (by simp)
    exact (not_lt_of_ge hmin) (backward_east_turn_after_west
      (outgoing_initialDirection_re_pos w hfin hfam e he)
      (outgoing_initialDirection_re_pos w hfin hfam f hf)
      (incoming_geometric_initialDirection_re_neg w hfin hfam i) hback)





theorem outgoingArc_arg_le (v e f : ℕ) (hin : ∃ i, edgeEast w i = v)
    (hev : edgeWest w e = v)
    (harc : RotationArc (kmswInfRot w hfin) (futureMapTail w) (e, false) (f, false)) :
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection ≤
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection := by
  obtain ⟨n, hn, hout⟩ := harc
  let σ := kmswInfRot w hfin
  have hv (k : ℕ) : kmswLimitDartVertex w ((σ ^ k) (e, false)) = v := by
    induction k with
    | zero => exact hev
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (kmswLimitDartVertex_rot w hfin _).trans ih
  have hb (k : ℕ) (hk : k ≤ n) :
      (σ ^ k) (e, false) = (((σ ^ k) (e, false)).1, false) :=
    Prod.ext rfl (hout k hk).1
  have hbound : ∀ k, k ≤ n →
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection ≤
        Complex.arg ((monotoneLimitDrawing w hfin hfam).arc
          (((σ ^ k) (e, false)).1, false)).initialDirection := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      apply (ih (by omega)).trans
      let a := ((σ ^ k) (e, false)).1
      let b := ((σ ^ (k + 1)) (e, false)).1
      have hav : edgeWest w a = v := by
        have hh := hv k
        rw [hb k (by omega)] at hh
        exact hh
      have hbv : edgeWest w b = v := by
        have hh := hv (k + 1)
        rw [hb (k + 1) hk] at hh
        exact hh
      by_cases hab : a = b
      · change Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (a, false)).initialDirection ≤
          Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (b, false)).initialDirection
        rw [hab]
      · apply (outgoing_rotation_arg_lt_of_incoming w hfin hfam v hin a b
          (hout k (by omega)).2 (hout (k + 1) hk).2 hav hbv hab ?_).le
        change σ (a, false) = (b, false)
        rw [← hb k (by omega), ← hb (k + 1) hk, pow_succ', Equiv.Perm.mul_apply]
  have h := hbound n le_rfl
  rw [hn] at h
  exact h

include hfin in



theorem exists_incoming_geometric (h : BoundaryHitWitnesses w) (v : ℕ) :
    ∃ i, edgeEast w i = v := by
  classical
  by_cases hin : ∃ i, EdgePresent w i ∧ edgeEast w i = v
  · obtain ⟨i, _, hi⟩ := hin
    exact ⟨i, hi⟩
  · obtain ⟨k, _, hk⟩ := (kmswRunBoundaryDegree w h v
      (kmsw_vertex_allocated_of_finite_incidence w hfin v)).2.mp hin
    refine ⟨boundaryOuterEdge w h (k - 1), ?_⟩
    have he := (boundaryOuterEdge_endpoints w h (k - 1)).2.1
    rw [show k - 1 + 1 = k by omega] at he
    exact he.trans hk.symm

private theorem outgoing_arc_to_rightmost_eq {w : ℕ → Fin 3}
    {hf : KMSWFiniteIncidence w} {v e f : ℕ}
    (hfmost : kmswRunRightmostOutAt w hf v f)
    (harc : RotationArc (kmswInfRot w hf) (futureMapTail w)
      (e, false) (f, false)) : e = f := by
  have hprev : ¬ futureMapTail w ((kmswInfRot w hf).symm (f, false)) := by
    obtain ⟨_, _, k, hk, hstop, hgap⟩ := hfmost
    by_cases hk1 : k = 1
    · simpa only [hk1, pow_one] using hstop
    · intro hp
      have hnot := hgap 1 (by omega) (by omega)
      rw [pow_one] at hnot
      exact hnot hp.2
  obtain ⟨n, hn, hout⟩ := harc
  cases n with
  | zero => exact congrArg Prod.fst hn
  | succ n =>
    have hpred : (kmswInfRot w hf ^ n) (e, false) =
        (kmswInfRot w hf).symm (f, false) := by
      apply (kmswInfRot w hf).injective
      rw [Equiv.apply_symm_apply]
      exact (congrArg (fun σ : Equiv.Perm (ℕ × Bool) => σ (e, false))
        (pow_succ' (kmswInfRot w hf) n)).symm.trans hn
    exact (hprev (hpred ▸ hout n (Nat.le_succ n))).elim





theorem rightmost_arg_le (h : BoundaryHitWitnesses w) (v e f : ℕ)
    (he : kmswRunRightmostOutAt w hfin v e)
    (hf : EdgePresent w f) (hfv : edgeWest w f = v) :
    Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (e, false)).initialDirection ≤
      Complex.arg ((monotoneLimitDrawing w hfin hfam).arc (f, false)).initialDirection := by
  rcases kmswInfRot_outgoing_interval_all w hfin e f
      (he.2.1.trans hfv.symm) he.1 hf with harc | harc
  · exact outgoingArc_arg_le w hfin hfam v e f
      (exists_incoming_geometric w hfin h v) he.2.1 harc
  · have hfe : f = e := outgoing_arc_to_rightmost_eq he harc
    rw [hfe]




theorem sharedDepartureArgRightOf_rightmost (h : BoundaryHitWitnesses w) {v : ℕ}
    (Q R : InfinitePresentPath w ⟨v⟩)
    (hR : ∀ n, kmswRunRightmostOutAt w hfin (R.initial n).1.id (R.edge n)) :
    SharedDepartureArgRightOf w hfin hfam Q R := by
  intro i j hs
  exact rightmost_arg_le w hfin hfam h _ _ _ (hR j)
    (Q.edge_outgoing_at_initial w i).1
    ((Q.edge_outgoing_at_initial w i).2.trans (congrArg PresentVertex.id hs))





theorem exists_planar_leftmost_ldp (h : BoundaryHitWitnesses w) (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments)
    (R : InfinitePresentPath w ⟨v⟩)
    (hR : ∀ n, kmswRunRightmostOutAt w hfin (R.initial n).1.id (R.edge n)) :
    ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments ∧
      ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
        pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)) ⊆
          closedBetween
            (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P.edge i, false)))
            (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false))) := by
  obtain ⟨P, hP, hleft⟩ := exists_sharedDepartureArg_leftmost_ldp w hfin hfam v hg
  exact ⟨P, hP, fun Q hQ => trace_subset_closedBetween_of_departureArgs w hfin hfam v P R Q
    ⟨hleft Q hQ, sharedDepartureArgRightOf_rightmost w hfin hfam h Q R hR⟩⟩


private theorem pathEdgeList_injective {u v : PresentVertex w} :
    Function.Injective (pathEdgeList (u := u) (v := v)) := by
  intro p
  induction p with
  | nil =>
    intro q hq
    cases q with
    | nil => rfl
    | cons q f =>
      have hr := congrArg List.reverse hq
      simp only [pathEdgeList, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.reverse_nil, reduceCtorEq] at hr
  | @cons a b p e ih =>
    intro q hq
    cases q with
    | nil =>
      have hr := congrArg List.reverse hq
      simp only [pathEdgeList, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.reverse_nil, List.cons_ne_nil] at hr
    | @cons c d q f =>
      have hr := congrArg List.reverse hq
      simp only [pathEdgeList, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.cons.injEq] at hr
      have hac : a = c := by
        cases a with | mk a =>
          cases c with | mk c =>
            congr 1
            exact e.property.2.1.symm.trans
              ((congrArg (edgeWest w) hr.1).trans f.property.2.1)
      subst c
      have hef : e = f := Subtype.ext hr.1
      subst f
      exact congrArg (fun r => r.cons e) (ih (List.reverse_injective hr.2))



theorem infinitePresentPath_eq_of_edge_eq {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (he : Q.edge = P.edge) : Q = P := by
  have hi : Q.initial = P.initial := by
    funext n
    have hp : pathEdgeList (Q.initial n).2 = pathEdgeList (P.initial n).2 := by
      rw [Q.prefix_edges, P.prefix_edges, he]
    have hv : (Q.initial n).1 = (P.initial n).1 := by
      have hid := (pathEdgeList_endpoint (Q.initial n).2).symm.trans
        ((congrArg (geodesicPrefixEnd w v) hp).trans
          (pathEdgeList_endpoint (P.initial n).2))
      cases hq : (Q.initial n).1 with | mk q =>
        cases hpv : (P.initial n).1 with | mk p =>
          congr 1
          simpa only [hq, hpv] using hid
    generalize Q.initial n = q at hp hv ⊢
    generalize P.initial n = p at hp hv ⊢
    obtain ⟨q, qp⟩ := q
    obtain ⟨p, pp⟩ := p
    change q = p at hv
    subst p
    exact congrArg (Sigma.mk q) (pathEdgeList_injective w hp)
  cases Q
  cases P
  cases he
  cases hi
  rfl




theorem existsUnique_planar_leftmost_ldp (h : BoundaryHitWitnesses w) (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments)
    (R : InfinitePresentPath w ⟨v⟩)
    (hR : ∀ n, kmswRunRightmostOutAt w hfin (R.initial n).1.id (R.edge n)) :
    ∃! P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments ∧
      ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
        pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)) ⊆
          closedBetween
            (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P.edge i, false)))
            (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false))) := by
  obtain ⟨P, hP, hleft⟩ := exists_planar_leftmost_ldp w hfin hfam h v hg R hR
  refine ⟨P, ⟨hP, hleft⟩, fun Q hQ => ?_⟩
  exact infinitePresentPath_eq_of_edge_eq w P Q
    (planar_leftmost_ldp_edge_unique w hfin hfam Q P R hQ.1 hP hQ.2 hleft)

end DirectedDistances.PaperProofs.Section5.LeftmostTransport

namespace DirectedDistances.PaperProofs.Section5

open Filter MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk





theorem m0Cut_ae_existsUnique_runZero_leftmost_ldp :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ _hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let G := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
      ∀ k : ℤ,
        ∃ R : KMSWRunRightmostRay w (H.1 0),
          R.vertex 0 = boundaryVertex w h k ∧
          ∃ T : InfinitePresentPath w (boundaryPresentVertex w h k),
            T.edge = R.edge ∧
            (∀ n, kmswRunRightmostOutAt w (H.1 0) (T.initial n).1.id (T.edge n)) ∧
            ∃! P : InfinitePresentPath w (boundaryPresentVertex w h k),
              P.HasLongestSegments ∧
              ∀ Q : InfinitePresentPath w (boundaryPresentVertex w h k),
                Q.HasLongestSegments →
                  pathTrace G (fun i => (Q.edge i, false)) ⊆
                    closedBetween (pathTrace G (fun i => (P.edge i, false)))
                      (pathTrace G (fun i => (T.edge i, false))) := by
  filter_upwards [m0Cut_ae_ldp_geodesic_and_rightmost_exists] with W hW
  obtain ⟨H, h, hLL, hall⟩ := hW
  refine ⟨H, h, hLL, fun k => ?_⟩
  obtain ⟨⟨A⟩, R, hstart, T, he, hT⟩ := hall k
  refine ⟨R, hstart, T, he, hT, ?_⟩
  exact LeftmostTransport.existsUnique_planar_leftmost_ldp (shiftedStream W 0)
    (H.1 0) _ h (boundaryVertex (shiftedStream W 0) h k)
    ⟨A.codePath, A.segments⟩ T hT


section Cut

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

local notation "w" => shiftedStream W 0
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hp H
local notation "P0" => monotoneFamilyDrawing w ((And.left H) 0) (monotone_family_all w)
local notation "D" => m0CutData W H h hLL






@[expose] def CutLeftmost (k : ℤ) (P : M0CutInfiniteGeodesic W H h hLL k true)
    (R : InfinitePresentPath w (boundaryPresentVertex w h k)) : Prop :=
  ∀ Q : M0CutInfinitePath W H D ((D).x k), Q.HasLongestSegments →
    pathTrace G (fun n => (Q.edge n, false)) ⊆
      closedBetween
        (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
        (pathTrace G (fun n => wholePlaneDartι W 0 (R.edge n, false)))




theorem cutLeftmost_iff_runZero (k : ℤ)
    (P : M0CutInfiniteGeodesic W H h hLL k true)
    (R : InfinitePresentPath w (boundaryPresentVertex w h k)) :
    CutLeftmost W H h hp hLL k P R ↔
      ∀ Q : InfinitePresentPath w (boundaryPresentVertex w h k), Q.HasLongestSegments →
        pathTrace P0 (fun n => (Q.edge n, false)) ⊆
          closedBetween (pathTrace P0 (fun n => (P.codePath.edge n, false)))
            (pathTrace P0 (fun n => (R.edge n, false))) :=
  m0Cut_ldp_containment_iff W H h hp hLL k P.codePath.edge R.edge



theorem existsUnique_cutLeftmost_of_runZero (k : ℤ)
    (R : InfinitePresentPath w (boundaryPresentVertex w h k))
    (hex : ∃! P : InfinitePresentPath w (boundaryPresentVertex w h k),
      P.HasLongestSegments ∧
        ∀ Q : InfinitePresentPath w (boundaryPresentVertex w h k), Q.HasLongestSegments →
          pathTrace P0 (fun n => (Q.edge n, false)) ⊆
            closedBetween (pathTrace P0 (fun n => (P.edge n, false)))
              (pathTrace P0 (fun n => (R.edge n, false)))) :
    ∃! P : M0CutInfiniteGeodesic W H h hLL k true, CutLeftmost W H h hp hLL k P R := by
  obtain ⟨A, hA, huniq⟩ := hex
  have hstart : (A.initial 0).1.id = boundaryVertex w h k :=
    congrArg PresentVertex.id ((A.initial 0).2.eq_of_length_zero (A.prefix_length 0)).symm
  let P : M0CutInfiniteGeodesic W H h hLL k true := {
    codePath := A
    segments := hA.1
    startsAtCutBoundary := ((D).x_eq h hLL k).trans
      (congrArg (wholePlaneVertexι W 0) hstart.symm)
    cutStep := fun n => by
      apply (m0Cut_identification_directedStep W H h hLL
        ((A.initial n).1.id) ((A.initial (n + 1)).1.id)).2
      obtain ⟨he, hw⟩ := A.edge_outgoing_at_initial w n
      obtain ⟨_, ht⟩ := A.edge_incoming_at_succ w n
      exact ⟨A.edge n, he, congrArg (wholePlaneVertexι W 0) hw,
        congrArg (wholePlaneVertexι W 0) ht⟩ }
  have hP : CutLeftmost W H h hp hLL k P R :=
    (cutLeftmost_iff_runZero W H h hp hLL k P R).2 hA.2
  refine ⟨P, hP, fun Q hQ => ?_⟩
  have hcode : Q.codePath = A := huniq Q.codePath
    ⟨Q.segments, (cutLeftmost_iff_runZero W H h hp hLL k Q R).1 hQ⟩
  have hext : ∀ B C : M0CutInfiniteGeodesic W H h hLL k true,
      B.codePath = C.codePath → B = C := by
    intro B C he
    cases B
    cases C
    dsimp only at he
    cases he
    rfl
  exact hext Q P hcode

end Cut






theorem m0Cut_ae_existsUnique_cutLeftmost_ldp :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
        ∀ k : ℤ,
          ∃ R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
            R.vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
            ∃ T : InfinitePresentPath (shiftedStream W 0)
                (boundaryPresentVertex (shiftedStream W 0) h k),
              T.edge = R.edge ∧
              (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
                (T.initial n).1.id (T.edge n)) ∧
              ∃! P : M0CutInfiniteGeodesic W H h hLL k true,
                CutLeftmost W H h hp hLL k P T := by
  filter_upwards [m0Cut_ae_existsUnique_runZero_leftmost_ldp,
    wholePlaneIID_ae_pastCode_boundaryHitWitnesses] with W hW hp
  change BoundaryHitWitnesses (kmswPastCode W) at hp
  obtain ⟨H, h, hLL, hall⟩ := hW
  refine ⟨H, h, hLL, hp, fun k => ?_⟩
  obtain ⟨R, hstart, T, he, hT, hex⟩ := hall k
  exact ⟨R, hstart, T, he, hT,
    existsUnique_cutLeftmost_of_runZero W H h hp hLL k T hex⟩


namespace LeftmostTransport

open Quiver Set

variable (w : ℕ → Fin 3) (hf : KMSWFiniteIncidence w)
    (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P))

include hf hfam in
private theorem initial_injective {x : PresentVertex w} (P : InfinitePresentPath w x) :
    Function.Injective (fun n => (P.initial n).1) := by
  intro i j hij
  apply infinitePresentPath_west_injective hf hfam P
  change edgeWest w (P.edge i) = edgeWest w (P.edge j)
  rw [(P.edge_outgoing_at_initial w i).2, (P.edge_outgoing_at_initial w j).2]
  exact congrArg PresentVertex.id hij

private theorem exists_initial_of_mem_vertices {x : ℕ} (P : InfinitePresentPath w ⟨x⟩)
    (N : ℕ) {z : PresentVertex w} (hz : z ∈ (P.initial N).2.vertices) :
    ∃ i, (P.initial i).1 = z := by
  obtain ⟨p, q, hpq⟩ := (P.initial N).2.exists_eq_comp_of_mem_vertices hz
  let i := p.length
  have hi : i ≤ N := by
    have hl := P.prefix_length N
    rw [hpq, Path.length_comp] at hl
    dsimp [i]
    omega
  let full := List.ofFn (fun k : Fin N => P.edge k.val)
  have hlist : pathEdgeList p ++ pathEdgeList q = full := by
    rw [← pathEdgeList_comp, ← hpq, P.prefix_edges]
  have htake : pathEdgeList p = full.take i := by
    change pathEdgeList p = full.take p.length
    rw [← hlist, ← pathEdgeList_length p]
    simp
  have hpfx : List.ofFn (fun k : Fin i => P.edge k.val) = full.take i := by
    apply List.ext_get
    · simp [full, Nat.min_eq_left hi]
    · intro k hk₁ hk₂
      simp [full, List.get_eq_getElem]
  refine ⟨i, ?_⟩
  have hp := pathEdgeList_endpoint p
  have hP := pathEdgeList_endpoint (P.initial i).2
  rw [P.prefix_edges, hpfx, ← htake] at hP
  exact congrArg PresentVertex.mk (hP.symm.trans hp)

include hf hfam in



theorem finiteAvoidance_separates_reachable
    (hall : ∀ v : ℕ, Nonempty (InfinitePresentPath w ⟨v⟩))
    {a z : PresentVertex w} (havoid : FiniteAvoidance a z)
    (b : PresentVertex w) (hzb : Quiver.Reachable z b) (r : Path a b) :
    z ∈ r.vertices := by
  classical
  by_contra hmiss
  have hbn : b ≠ z := by
    intro he
    exact hmiss (he ▸ r.end_mem_vertices)
  obtain ⟨p⟩ := hzb
  have hforward {c : PresentVertex w} (q : Path b c) : z ∉ q.vertices := by
    intro hz
    obtain ⟨q₁, q₂, _⟩ := q.exists_eq_comp_of_mem_vertices hz
    have hcycle := presentVertex_acyclic w z (p.comp q₁)
    rw [Path.length_comp] at hcycle
    have hlen : p.length = 0 := by omega
    exact hbn (p.eq_of_length_zero hlen).symm
  obtain ⟨T⟩ := hall b.id
  let y : ℕ → PresentVertex w := fun n => (T.initial n).1
  have hy : Function.Injective y := initial_injective w hf hfam T
  have hfinite : {n : ℕ | y n ∈ {c | ∃ q : Path a c, z ∉ q.vertices}}.Finite :=
    havoid.preimage hy.injOn
  apply Set.infinite_univ (hfinite.subset ?_)
  intro n _
  refine ⟨r.comp (T.initial n).2, ?_⟩
  rw [Path.vertices_comp]
  intro hz
  rcases List.mem_append.mp hz with hr | ht
  · exact hmiss (List.mem_of_mem_dropLast hr)
  · exact hforward (T.initial n).2 ht





theorem shift_sharedDepartureArg_leftmost {x : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (hP : P.HasLongestSegments)
    (hleft : ∀ T : InfinitePresentPath w ⟨x⟩, T.HasLongestSegments →
      SharedDepartureArgRightOf w hf hfam P T) (i : ℕ)
    (hsep : ∀ z : PresentVertex w, Quiver.Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices)
    (Q : InfinitePresentPath w (P.initial i).1) (hQ : Q.HasLongestSegments) :
    SharedDepartureArgRightOf w hf hfam (P.shift i) Q := by
  obtain ⟨S, hS, he⟩ := P.exists_ldp_splice_at_separator hP i Q hQ hsep
  have hedge (n : ℕ) : S.edge (i + n) = Q.edge n := by
    rw [he, ite_eq_right (by omega : ¬i + n < i), Nat.add_sub_cancel_left]
  intro m n hmn
  have hSvertex : (S.initial (i + n)).1 = (Q.initial n).1 := by
    apply congrArg PresentVertex.mk
    exact (S.edge_outgoing_at_initial w (i + n)).2.symm.trans
      ((congrArg (edgeWest w) (hedge n)).trans (Q.edge_outgoing_at_initial w n).2)
  have hshared : (P.initial (i + m)).1 = (S.initial (i + n)).1 :=
    hmn.trans hSvertex.symm
  have hh := hleft S hS (i + m) (i + n) hshared
  rw [hedge] at hh
  exact hh

private theorem common_start_edge_eq {x y : PresentVertex w}
    (P : InfinitePresentPath w x) (Q : InfinitePresentPath w y) (hxy : x = y)
    (hP : P.HasLongestSegments) (hQ : Q.HasLongestSegments)
    (hleftP : ∀ T : InfinitePresentPath w x, T.HasLongestSegments →
      SharedDepartureArgRightOf w hf hfam P T)
    (hleftQ : ∀ T : InfinitePresentPath w y, T.HasLongestSegments →
      SharedDepartureArgRightOf w hf hfam Q T) : P.edge = Q.edge := by
  subst y
  exact SharedDepartureArgRightOf.antisymm w hf hfam P Q (hleftP Q hQ) (hleftQ P hP)




theorem leftmost_ldp_tails_eq_at_separator {x y : ℕ}
    (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    (hP : P.HasLongestSegments) (hQ : Q.HasLongestSegments)
    (hleftP : ∀ T : InfinitePresentPath w ⟨x⟩, T.HasLongestSegments →
      SharedDepartureArgRightOf w hf hfam P T)
    (hleftQ : ∀ T : InfinitePresentPath w ⟨y⟩, T.HasLongestSegments →
      SharedDepartureArgRightOf w hf hfam Q T)
    (i j : ℕ) (hij : (P.initial i).1 = (Q.initial j).1)
    (hsepP : ∀ z : PresentVertex w, Quiver.Reachable (P.initial i).1 z →
      ∀ r : Path (⟨x⟩ : PresentVertex w) z, (P.initial i).1 ∈ r.vertices)
    (hsepQ : ∀ z : PresentVertex w, Quiver.Reachable (Q.initial j).1 z →
      ∀ r : Path (⟨y⟩ : PresentVertex w) z, (Q.initial j).1 ∈ r.vertices) :
    (P.shift i).edge = (Q.shift j).edge :=
  common_start_edge_eq w hf hfam (P.shift i) (Q.shift j) hij
    (P.shift_hasLongestSegments hP i) (Q.shift_hasLongestSegments hQ j)
    (shift_sharedDepartureArg_leftmost w hf hfam P hP hleftP i hsepP)
    (shift_sharedDepartureArg_leftmost w hf hfam Q hQ hleftQ j hsepQ)




theorem leftmost_ldp_coalesce_of_common_finiteAvoidance
    (hall : ∀ v : ℕ, Nonempty (InfinitePresentPath w ⟨v⟩))
    {x y : ℕ} (P : InfinitePresentPath w ⟨x⟩) (Q : InfinitePresentPath w ⟨y⟩)
    (hP : P.HasLongestSegments) (hQ : Q.HasLongestSegments)
    (hleftP : ∀ T : InfinitePresentPath w ⟨x⟩, T.HasLongestSegments →
      SharedDepartureArgRightOf w hf hfam P T)
    (hleftQ : ∀ T : InfinitePresentPath w ⟨y⟩, T.HasLongestSegments →
      SharedDepartureArgRightOf w hf hfam Q T)
    (z : PresentVertex w) (hzP : FiniteAvoidance (⟨x⟩ : PresentVertex w) z)
    (hzQ : FiniteAvoidance (⟨y⟩ : PresentVertex w) z) :
    ∃ i j, (P.shift i).edge = (Q.shift j).edge := by
  obtain ⟨N, hN⟩ := finiteAvoidance_eventually_forces_path_through hzP
    (fun n => (P.initial n).1) (initial_injective w hf hfam P)
    (fun n => ⟨(P.initial n).2⟩)
  obtain ⟨i, hi⟩ := exists_initial_of_mem_vertices w P N (hN N le_rfl (P.initial N).2)
  obtain ⟨M, hM⟩ := finiteAvoidance_eventually_forces_path_through hzQ
    (fun n => (Q.initial n).1) (initial_injective w hf hfam Q)
    (fun n => ⟨(Q.initial n).2⟩)
  obtain ⟨j, hj⟩ := exists_initial_of_mem_vertices w Q M (hM M le_rfl (Q.initial M).2)
  refine ⟨i, j, leftmost_ldp_tails_eq_at_separator w hf hfam P Q hP hQ
    hleftP hleftQ i j (hi.trans hj.symm) ?_ ?_⟩
  · rw [hi]
    exact finiteAvoidance_separates_reachable w hf hfam hall hzP
  · rw [hj]
    exact finiteAvoidance_separates_reachable w hf hfam hall hzQ

end LeftmostTransport








theorem m0Cut_ae_leftmost_ldp_and_pairwise_coalescence :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k true,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, CutLeftmost W H h hp hLL k (P k) (T k)) ∧
        (∀ k Q, CutLeftmost W H h hp hLL k Q (T k) → Q = P k) ∧
        ∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n)) := by
  have havoid := ae_cutWindow_finiteAvoidance_infinite
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at havoid
  have hpull := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable havoid
  filter_upwards [m0Cut_ae_existsUnique_cutLeftmost_ldp, hpull] with W hW havoidW
  have hs (i : ℕ) : shiftedCodePath W 0 (i + 1) = shiftedStream W 0 i := by
    simp only [shiftedCodePath, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel]
  simp only [hs] at havoidW
  obtain ⟨H, h, hLL, hp, hall⟩ := hW
  choose R hstart T he hT P hleft huniq using hall
  refine ⟨H, h, hLL, hp, R, T, P,
    fun k => ⟨hstart k, he k, hT k⟩, hleft, huniq, ?_⟩
  let w := shiftedStream W 0
  let hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  have hforward (v : ℕ) : Nonempty (InfinitePresentPath w ⟨v⟩) := by
    obtain ⟨A, hA⟩ := kmswRunRightmostRay_exists' W H h hLL
      (m0CutData W H h hLL).betaL v
    have hpresent := runRightmostRay_exists_presentPath A
    rw [hA] at hpresent
    obtain ⟨S, _⟩ := hpresent
    exact ⟨S⟩
  have hang (k : ℤ) (S : InfinitePresentPath w (boundaryPresentVertex w h k))
      (hS : S.HasLongestSegments) :
      LeftmostTransport.SharedDepartureArgRightOf w (H.1 0) hfam (P k).codePath S := by
    have hcontain := (cutLeftmost_iff_runZero W H h hp hLL k (P k) (T k)).1
      (hleft k) S hS
    exact ((LeftmostTransport.trace_subset_closedBetween_iff_departureArgs
      w (H.1 0) hfam (boundaryVertex w h k) (P k).codePath (T k) S).1 hcontain).1
  intro k k'
  let K := max k.natAbs k'.natAbs
  have hbounds (a : ℤ) (ha : a.natAbs ≤ K) : -(K : ℤ) ≤ a ∧ a ≤ K := by
    have hlo : -(a.natAbs : ℤ) ≤ a := by cases a <;> simp <;> omega
    have hhi : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
    have hab : (a.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast ha
    constructor <;> omega
  have hk := hbounds k (Nat.le_max_left _ _)
  have hk' := hbounds k' (Nat.le_max_right _ _)
  obtain ⟨z, hz⟩ := (havoidW h K).nonempty
  obtain ⟨i, j, htail⟩ := LeftmostTransport.leftmost_ldp_coalesce_of_common_finiteAvoidance
    w (H.1 0) hfam hforward (P k).codePath (P k').codePath
    (P k).segments (P k').segments (hang k) (hang k') z
    (hz k hk.1 hk.2) (hz k' hk'.1 hk'.2)
  exact ⟨i, j, fun n => congrArg (wholePlaneEdgeι W 0) (congrFun htail n)⟩

end DirectedDistances.PaperProofs.Section5
