module

public import DirectedDistances.KMSW.InfinitePathDrawing
public import DirectedDistances.PlanarMap.ProperGraphRay

/-! # Height escape for infinite present paths -/

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

variable {w : ℕ → Fin 3}
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P))
  {start : PresentVertex w} (Q : InfinitePresentPath w start)

include hfin hfam in
/-- Starting vertices along the path are distinct.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_west_injective :
    Function.Injective (fun i => edgeWest w (Q.edge i)) := by
  intro i j hij
  apply (infinitePresentPath_start_re_strictMono hfin hfam Q).injective
  have hs (k : ℕ) :
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge k, false)).start =
        (monotoneLimitDrawing w hfin hfam).pos (edgeWest w (Q.edge k)) := by
    rw [(monotoneLimitDrawing w hfin hfam).arc_start]
    rfl
  dsimp only at hij ⊢
  rw [hs i, hs j, hij]

include hfin in
private theorem vertex_allocated (v : ℕ) : ∃ n, v < (kmswStage w n).nextVertex := by
  classical
  by_contra h
  have hb (n : ℕ) : (kmswStage w n).nextVertex ≤ v := by
    by_contra hn
    exact h ⟨n, by omega⟩
  have hf := (Set.finite_Iio v).biUnion (fun u _ => hfin u)
  have hu : (Set.univ : Set ℕ).Finite := hf.subset (by
    intro e _
    have he := kmsw_edge_allocated_by_self w e
    have hw := (kmswStage_endpoints_lt_nextVertex w e e he).1
    exact Set.mem_iUnion₂.mpr
      ⟨(kmswStage w e).west e, hw.trans_le (hb e), e, he, Or.inl rfl⟩)
  exact Set.infinite_univ hu

private theorem nextVertex_step_bound (n : ℕ) :
    (kmswStage w (n + 1)).nextVertex ≤ (kmswStage w n).nextVertex + 1 := by
  rw [kmswStage, kmswStep]
  cases kmswCodeStep (w n) with
  | down =>
    cases hs : (kmswStage w n).UR <;> simp [kmswStepOfStep, hs, State.addEdge]
  | left =>
    cases hs : (kmswStage w n).UL.dropLast.reverse <;>
      simp [kmswStepOfStep, hs, State.addEdge]
  | up => simp [kmswStepOfStep, State.addEdge]

private theorem height_controls_allocation (v n : ℕ)
    (hv : ((monotoneLimitDrawing w hfin hfam).pos v).im ≤ n) :
    v < (kmswStage w n).nextVertex := by
  let k := Nat.find (vertex_allocated hfin v)
  have hk : v < (kmswStage w k).nextVertex := Nat.find_spec (vertex_allocated hfin v)
  suffices hkn : k ≤ n from hk.trans_le (CutConverse.nextVertex_mono w hkn)
  cases hkval : k with
  | zero => exact Nat.zero_le n
  | succ m =>
    have hold : ¬v < (kmswStage w m).nextVertex := by
      exact Nat.find_min (vertex_allocated hfin v) (by omega)
    have hb := nextVertex_step_bound (w := w) m
    have hvbirth : v = (kmswStage w m).nextVertex := by rw [hkval] at hk; omega
    have hgrow : (kmswStage w (m + 1)).nextVertex =
        (kmswStage w m).nextVertex + 1 := by rw [hkval] at hk; omega
    have hheight : ((monotoneLimitDrawing w hfin hfam).pos v).im = (m + 1 : ℕ) := by
      rw [monotoneLimitDrawing_pos_layout w hfin hfam k v hk, hkval, hvbirth]
      exact layoutHeight_created_vertex w m hgrow
    rw [hheight] at hv
    have hmn : m + 1 ≤ n := by exact_mod_cast hv
    omega

/-- The limit drawing has finitely many vertices below every fixed height.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem monotoneLimitDrawing_finite_height_sublevel (R : ℝ) :
    {v | ((monotoneLimitDrawing w hfin hfam).pos v).im ≤ R}.Finite := by
  obtain ⟨n, hn⟩ := exists_nat_ge R
  apply (Set.finite_Iio (kmswStage w n).nextVertex).subset
  intro v hv
  exact height_controls_allocation hfin hfam v n (hv.trans hn)

/-- The starting heights tend to positive infinity.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_start_im_tendsto :
    Tendsto (fun i =>
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.im)
      atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro M
  have hf : {i | ((monotoneLimitDrawing w hfin hfam).pos
      (edgeWest w (Q.edge i))).im ≤ M}.Finite :=
    (monotoneLimitDrawing_finite_height_sublevel hfin hfam M).preimage
      (infinitePresentPath_west_injective hfin hfam Q).injOn
  obtain ⟨B, hB⟩ := hf.bddAbove
  refine ⟨B + 1, fun i hi => ?_⟩
  have hgt : M < ((monotoneLimitDrawing w hfin hfam).pos
      (edgeWest w (Q.edge i))).im := by
    apply lt_of_not_ge
    intro h
    have := hB h
    omega
  have hs := (monotoneLimitDrawing w hfin hfam).arc_start (Q.edge i, false)
  rw [hs]
  exact hgt.le

/-- Every point of an arc is above the smaller of its two endpoint heights.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_arc_height_lower (i : ℕ) (z : ℂ)
    (hz : z ∈ ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).image) :
    min ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.im
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.im ≤ z.im := by
  have he := kmsw_edge_allocated_by_self w (Q.edge i)
  rw [monotoneLimitDrawing_arc_layout w hfin hfam (Q.edge i) (Q.edge i) he false] at *
  simp only [Bool.false_eq_true, ↓reduceIte] at *
  obtain ⟨hs, ht⟩ := layoutArc_endpoints w (Q.edge i) (Q.edge i) he
  rw [hs, ht]
  exact layoutArc_height_lower w (Q.edge i) (Q.edge i) he z hz

/-- All points of sufficiently late arcs are uniformly above any prescribed height.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_trace_tail_height (M : ℝ) :
    ∃ N : ℕ, ∀ i, N ≤ i → ∀ z ∈
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).image, M ≤ z.im := by
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp
    (infinitePresentPath_start_im_tendsto hfin hfam Q) M
  refine ⟨N, fun i hi z hz => ?_⟩
  apply le_trans (le_min (hN i hi) ?_)
    (infinitePresentPath_arc_height_lower hfin hfam Q i z hz)
  rw [infinitePresentPath_arc_seam hfin hfam Q i]
  exact hN (i + 1) (by omega)

/-- The supremum of all starting abscissas, allowing a finite right endpoint.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] noncomputable def infinitePresentPath_rightEnd : WithTop ℝ :=
  ⨆ i, (((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.re : WithTop ℝ)

/-- Every starting abscissa is strictly below the right endpoint.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_start_lt_rightEnd (i : ℕ) :
    (((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.re : WithTop ℝ) <
      infinitePresentPath_rightEnd hfin hfam Q := by
  have hlt := infinitePresentPath_start_re_strictMono hfin hfam Q (Nat.lt_succ_self i)
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt)
    (le_ciSup (show BddAbove (Set.range (fun j =>
      (((monotoneLimitDrawing w hfin hfam).arc (Q.edge j, false)).start.re :
        WithTop ℝ))) from ⟨⊤, fun _ _ => le_top⟩) (i + 1))

/-- Every trace point has abscissa in the half-open domain of the ray.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_trace_re_mem_domain {z : ℂ}
    (hz : z ∈ pathTrace (monotoneLimitDrawing w hfin hfam)
      (fun i => (Q.edge i, false))) :
    z.re ∈ rayDomain
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge 0, false)).start.re
      (infinitePresentPath_rightEnd hfin hfam Q) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  have hmono := infinitePresentPath_arc_xMonotone hfin hfam Q i
  rw [Polyline.image_eq_heightFn_graph hmono
    ((monotoneLimitDrawing w hfin hfam).arc_length (Q.edge i, false))] at hi
  refine ⟨?_, ?_⟩
  · exact ((infinitePresentPath_start_re_strictMono hfin hfam Q).monotone
      (Nat.zero_le i)).trans hi.1
  · have hr := hi.2.1
    rw [infinitePresentPath_arc_seam hfin hfam Q i] at hr
    exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hr)
      (infinitePresentPath_start_lt_rightEnd hfin hfam Q (i + 1))

private theorem exists_arc_reaching {x : ℝ}
    (hx : (x : WithTop ℝ) < infinitePresentPath_rightEnd hfin hfam Q) :
    ∃ i, x ≤ ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re := by
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hx
  have hi' := WithTop.coe_lt_coe.mp hi
  exact ⟨i, (hi'.trans
    (infinitePresentPath_arc_start_re_lt_finish_re hfin hfam Q i)).le⟩

/-- The first arc whose finish reaches the abscissa, extended by zero if none does.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] noncomputable def infinitePresentPath_rayIndex (x : ℝ) : ℕ := by
  classical
  exact if h : ∃ i, x ≤ ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re
  then Nat.find h else 0

private theorem rayIndex_spec {x : ℝ}
    (hx : (x : WithTop ℝ) < infinitePresentPath_rightEnd hfin hfam Q) :
    x ≤ ((monotoneLimitDrawing w hfin hfam).arc
      (Q.edge (infinitePresentPath_rayIndex hfin hfam Q x), false)).finish.re := by
  have h := exists_arc_reaching hfin hfam Q hx
  rw [infinitePresentPath_rayIndex, dite_eq_left h]
  exact Nat.find_spec h

private theorem rayIndex_le {x : ℝ} (i : ℕ)
    (hi : x ≤ ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re) :
    infinitePresentPath_rayIndex hfin hfam Q x ≤ i := by
  have h : ∃ i, x ≤
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re := ⟨i, hi⟩
  rw [infinitePresentPath_rayIndex, dite_eq_left h]
  exact Nat.find_min' h hi

private theorem rayIndex_min {x : ℝ}
    (hx : (x : WithTop ℝ) < infinitePresentPath_rightEnd hfin hfam Q) (i : ℕ)
    (hi : i < infinitePresentPath_rayIndex hfin hfam Q x) :
    ¬x ≤ ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re := by
  have h := exists_arc_reaching hfin hfam Q hx
  rw [infinitePresentPath_rayIndex, dite_eq_left h] at hi
  exact Nat.find_min h hi

private theorem rayIndex_start {x : ℝ}
    (hx : x ∈ rayDomain
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge 0, false)).start.re
      (infinitePresentPath_rightEnd hfin hfam Q)) :
    ((monotoneLimitDrawing w hfin hfam).arc
      (Q.edge (infinitePresentPath_rayIndex hfin hfam Q x), false)).start.re ≤ x := by
  let k := infinitePresentPath_rayIndex hfin hfam Q x
  by_cases hk : k = 0
  · simpa [k, hk] using hx.1
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hprev := lt_of_not_ge (rayIndex_min hfin hfam Q hx.2 (k - 1) (by omega))
    have hs := congrArg Complex.re (infinitePresentPath_arc_seam hfin hfam Q (k - 1))
    rw [Nat.sub_add_cancel hkpos] at hs
    exact (hs ▸ hprev).le

/-- The height of the first arc reaching the abscissa; outside the ray's domain this
is extended by the height function of arc zero whenever no arc reaches the abscissa.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] noncomputable def infinitePresentPath_height (x : ℝ) : ℝ :=
  ((monotoneLimitDrawing w hfin hfam).arc
    (Q.edge (infinitePresentPath_rayIndex hfin hfam Q x), false)).heightFn x

private theorem height_agreement (k i : ℕ) (x : ℝ)
    (hki : k ≤ i)
    (hxk : x ≤ ((monotoneLimitDrawing w hfin hfam).arc (Q.edge k, false)).finish.re)
    (hxi : ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.re ≤ x) :
    ((monotoneLimitDrawing w hfin hfam).arc (Q.edge k, false)).heightFn x =
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).heightFn x := by
  let p := fun j => (monotoneLimitDrawing w hfin hfam).arc (Q.edge j, false)
  have hsm := infinitePresentPath_start_re_strictMono hfin hfam Q
  rcases eq_or_lt_of_le hki with rfl | hki
  · rfl
  · have hfs : (p k).finish.re = (p (k + 1)).start.re :=
      congrArg Complex.re (infinitePresentPath_arc_seam hfin hfam Q k)
    have hsk : (p (k + 1)).start.re ≤ x :=
      (hsm.monotone (Nat.succ_le_of_lt hki)).trans hxi
    have hEqX : x = (p k).finish.re := le_antisymm hxk (hfs ▸ hsk)
    have hEqI : i = k + 1 := by
      apply hsm.injective
      exact le_antisymm (hxi.trans (hEqX.le.trans hfs.le))
        (hsm.monotone (Nat.succ_le_of_lt hki))
    subst i
    have hmk := infinitePresentPath_arc_xMonotone hfin hfam Q k
    have hmn := infinitePresentPath_arc_xMonotone hfin hfam Q (k + 1)
    have hlk := (monotoneLimitDrawing w hfin hfam).arc_length (Q.edge k, false)
    have hln := (monotoneLimitDrawing w hfin hfam).arc_length (Q.edge (k + 1), false)
    change 2 ≤ (p k).points.length at hlk
    change 2 ≤ (p (k + 1)).points.length at hln
    have hlast : (p k).point ((p k).points.length - 1) = (p k).finish :=
      (p k).point_last_eq_finish
    have hfirst : (p (k + 1)).point 0 = (p (k + 1)).start :=
      (p (k + 1)).point_zero_eq_start
    rw [hEqX]
    calc
      (p k).heightFn (p k).finish.re = (p k).finish.im := by
        rw [← hlast]
        exact (p k).heightFn_point hmk (by omega)
      _ = (p (k + 1)).start.im :=
        congrArg Complex.im (infinitePresentPath_arc_seam hfin hfam Q k)
      _ = (p (k + 1)).heightFn (p (k + 1)).start.re := by
        rw [← hfirst]
        exact ((p (k + 1)).heightFn_point hmn (by omega)).symm
      _ = (p (k + 1)).heightFn (p k).finish.re :=
        congrArg (p (k + 1)).heightFn hfs.symm

/-- The ray height agrees with each individual arc, including both seams.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_height_on_arc (i : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.re
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re) :
    infinitePresentPath_height hfin hfam Q x =
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).heightFn x := by
  have hxX : (x : WithTop ℝ) < infinitePresentPath_rightEnd hfin hfam Q := by
    have hr := hx.2
    rw [infinitePresentPath_arc_seam hfin hfam Q i] at hr
    exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hr)
      (infinitePresentPath_start_lt_rightEnd hfin hfam Q (i + 1))
  exact height_agreement hfin hfam Q _ i x (rayIndex_le hfin hfam Q i hx.2)
    (rayIndex_spec hfin hfam Q hxX) hx.1

/-- The trace is exactly the graph of the constructed height on the half-open domain.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_trace_eq_graph :
    pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)) =
      {z | z.re ∈ rayDomain
        ((monotoneLimitDrawing w hfin hfam).arc (Q.edge 0, false)).start.re
        (infinitePresentPath_rightEnd hfin hfam Q) ∧
        z.im = infinitePresentPath_height hfin hfam Q z.re} := by
  ext z
  constructor
  · intro hz
    have hx := infinitePresentPath_trace_re_mem_domain hfin hfam Q hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    rw [Polyline.image_eq_heightFn_graph (infinitePresentPath_arc_xMonotone hfin hfam Q i)
      ((monotoneLimitDrawing w hfin hfam).arc_length (Q.edge i, false))] at hi
    exact ⟨hx, hi.2.2.trans (infinitePresentPath_height_on_arc hfin hfam Q i
      ⟨hi.1, hi.2.1⟩).symm⟩
  · rintro ⟨hx, hh⟩
    let k := infinitePresentPath_rayIndex hfin hfam Q z.re
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [Polyline.image_eq_heightFn_graph (infinitePresentPath_arc_xMonotone hfin hfam Q k)
      ((monotoneLimitDrawing w hfin hfam).arc_length (Q.edge k, false))]
    exact ⟨rayIndex_start hfin hfam Q hx, rayIndex_spec hfin hfam Q hx.2, hh⟩

/-- The ray height is continuous throughout its half-open abscissa domain.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_height_continuousOn :
    ContinuousOn (infinitePresentPath_height hfin hfam Q)
      (rayDomain ((monotoneLimitDrawing w hfin hfam).arc (Q.edge 0, false)).start.re
        (infinitePresentPath_rightEnd hfin hfam Q)) := by
  let p := fun i => (monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)
  let h := infinitePresentPath_height hfin hfam Q
  have hsm := infinitePresentPath_start_re_strictMono hfin hfam Q
  have harc (i : ℕ) : ContinuousOn h (Set.Icc (p i).start.re (p i).finish.re) := by
    apply (p i).continuous_heightFn.continuousOn.congr
    intro x hx
    exact infinitePresentPath_height_on_arc hfin hfam Q i hx
  have hprefix (n : ℕ) : ContinuousOn h (Set.Icc (p 0).start.re (p n).start.re) := by
    induction n with
    | zero =>
      rw [Set.Icc_self]
      exact continuousOn_singleton h _
    | succ n ih =>
      have hn := harc n
      have hs := congrArg Complex.re (infinitePresentPath_arc_seam hfin hfam Q n)
      change (p n).finish.re = (p (n + 1)).start.re at hs
      rw [hs] at hn
      have hu := ih.union_of_isClosed hn isClosed_Icc isClosed_Icc
      rwa [Set.Icc_union_Icc_eq_Icc (hsm.monotone (Nat.zero_le n))
        (hsm (Nat.lt_succ_self n)).le] at hu
  intro x hx
  obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hx.2
  have hxn : x < (p n).start.re := WithTop.coe_lt_coe.mp hn
  apply (hprefix n x ⟨hx.1, hxn.le⟩).mono_of_mem_nhdsWithin
  apply Filter.mem_of_superset
    (inter_mem_nhdsWithin _ (Iio_mem_nhds hxn))
  intro t ht
  exact ⟨ht.1.1, ht.2.le⟩

/-- The height eventually exceeds every bound near the right endpoint.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_height_escape (M : ℝ) :
    ∃ a ∈ rayDomain
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge 0, false)).start.re
      (infinitePresentPath_rightEnd hfin hfam Q),
      ∀ t ∈ rayDomain
        ((monotoneLimitDrawing w hfin hfam).arc (Q.edge 0, false)).start.re
        (infinitePresentPath_rightEnd hfin hfam Q),
        a ≤ t → M ≤ infinitePresentPath_height hfin hfam Q t := by
  let p := fun i => (monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)
  have hsm := infinitePresentPath_start_re_strictMono hfin hfam Q
  obtain ⟨N, hN⟩ := infinitePresentPath_trace_tail_height hfin hfam Q M
  refine ⟨(p (N + 1)).start.re,
    ⟨hsm.monotone (Nat.zero_le _), infinitePresentPath_start_lt_rightEnd hfin hfam Q _⟩,
    ?_⟩
  intro t ht hat
  let k := infinitePresentPath_rayIndex hfin hfam Q t
  have hk : N ≤ k := by
    by_contra hnk
    have hkn : k + 1 ≤ N := by omega
    have hupper := rayIndex_spec hfin hfam Q ht.2
    have hs := congrArg Complex.re (infinitePresentPath_arc_seam hfin hfam Q k)
    change t ≤ (p k).finish.re at hupper
    change (p k).finish.re = (p (k + 1)).start.re at hs
    have hlt := hsm (show k + 1 < N + 1 by omega)
    exact (not_le_of_gt hlt) (hat.trans (hupper.trans hs.le))
  let z : ℂ := ⟨t, infinitePresentPath_height hfin hfam Q t⟩
  have hz : z ∈ (p k).image := by
    rw [Polyline.image_eq_heightFn_graph (infinitePresentPath_arc_xMonotone hfin hfam Q k)
      ((monotoneLimitDrawing w hfin hfam).arc_length (Q.edge k, false))]
    exact ⟨rayIndex_start hfin hfam Q ht, rayIndex_spec hfin hfam Q ht.2, rfl⟩
  exact hN k hk z hz

/-- Every infinite present path traces a proper continuous graph ray.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem infinitePresentPath_properGraphRay :
    ProperGraphRay
      (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)))
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge 0, false)).start.re := by
  exact ⟨infinitePresentPath_rightEnd hfin hfam Q, infinitePresentPath_height hfin hfam Q,
    infinitePresentPath_start_lt_rightEnd hfin hfam Q 0,
    infinitePresentPath_height_continuousOn hfin hfam Q,
    infinitePresentPath_trace_eq_graph hfin hfam Q,
    infinitePresentPath_height_escape hfin hfam Q⟩

end DirectedDistances.KMSW
