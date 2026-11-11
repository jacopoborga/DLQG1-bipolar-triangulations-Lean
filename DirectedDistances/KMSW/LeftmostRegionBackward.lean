module

public import DirectedDistances.KMSW.InfinitePathGraphRay
public import DirectedDistances.KMSW.OutgoingOrderDrawing
public import DirectedDistances.KMSW.LeftmostGeodesicSubmap
public import DirectedDistances.PlanarMap.VariableRayStrip
import DirectedDistances.PlanarMap.SlopeAngularOrder

/-! # Containment implies shared-departure order -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set Filter

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P))

private theorem arc_start_at_initial {v : ℕ} (U : InfinitePresentPath w ⟨v⟩) (m : ℕ) :
    ((monotoneLimitDrawing w hfin hfam).arc (U.edge m, false)).start =
      (monotoneLimitDrawing w hfin hfam).pos (U.initial m).1.id := by
  rw [(monotoneLimitDrawing w hfin hfam).arc_start]
  change (monotoneLimitDrawing w hfin hfam).pos (edgeWest w (U.edge m)) = _
  rw [(U.edge_outgoing_at_initial w m).2]

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Every departure abscissa is in the ray domain. -/
theorem infinitePresentPath_initial_re_mem_domain {v : ℕ}
    (U : InfinitePresentPath w ⟨v⟩) (m : ℕ) :
    ((monotoneLimitDrawing w hfin hfam).pos (U.initial m).1.id).re ∈
      rayDomain ((monotoneLimitDrawing w hfin hfam).arc (U.edge 0, false)).start.re
        (infinitePresentPath_rightEnd hfin hfam U) := by
  rw [← arc_start_at_initial w hfin hfam U m]
  exact ⟨(infinitePresentPath_start_re_strictMono hfin hfam U).monotone
    (Nat.zero_le m), infinitePresentPath_start_lt_rightEnd hfin hfam U m⟩

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Every graph point in the ray domain lies on the path trace. -/
theorem infinitePresentPath_height_point_mem_trace {v : ℕ}
    (U : InfinitePresentPath w ⟨v⟩) {t : ℝ}
    (ht : t ∈ rayDomain
      ((monotoneLimitDrawing w hfin hfam).arc (U.edge 0, false)).start.re
      (infinitePresentPath_rightEnd hfin hfam U)) :
    (⟨t, infinitePresentPath_height hfin hfam U t⟩ : ℂ) ∈
      pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (U.edge i, false)) := by
  rw [infinitePresentPath_trace_eq_graph hfin hfam U]
  exact ⟨ht, rfl⟩

private theorem heightFn_initial {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) {t : ℝ}
    (hl : p.start.re ≤ t) (hr : t ≤ (p.point 1).re) :
    p.heightFn t = p.start.im +
      (p.initialDirection.im / p.initialDirection.re) * (t - p.start.re) := by
  have h := p.heightFn_linear_on_segment hp (i := 0) (by omega)
    (show (p.point 0).re ≤ t by rw [p.point_zero_eq_start]; exact hl) hr
  simpa only [Nat.zero_add, p.point_zero_eq_start, Polyline.initialDirection,
    Complex.sub_im, Complex.sub_re] using h

private theorem point_one_re_le_finish {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : (p.point 1).re ≤ p.finish.re := by
  rw [← p.point_last_eq_finish]
  exact p.point_re_le_of_le hp (by omega) (by omega)

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Strictly smaller outgoing argument gives strictly smaller height just after a shared vertex. -/
theorem infinitePresentPath_height_lt_after_shared_departure {v : ℕ}
    (U D : InfinitePresentPath w ⟨v⟩) (m n : ℕ)
    (hs : (U.initial m).1 = (D.initial n).1)
    (harg : Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (D.edge n, false)).initialDirection <
      Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (U.edge m, false)).initialDirection) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo
      ((monotoneLimitDrawing w hfin hfam).pos (U.initial m).1.id).re
      (((monotoneLimitDrawing w hfin hfam).pos (U.initial m).1.id).re + ε),
      infinitePresentPath_height hfin hfam D t <
        infinitePresentPath_height hfin hfam U t := by
  let G := monotoneLimitDrawing w hfin hfam
  let p := G.arc (U.edge m, false)
  let q := G.arc (D.edge n, false)
  have hp := infinitePresentPath_arc_xMonotone hfin hfam U m
  have hq := infinitePresentPath_arc_xMonotone hfin hfam D n
  have hplen := G.arc_length (U.edge m, false)
  have hqlen := G.arc_length (D.edge n, false)
  have hps : p.start = G.pos (U.initial m).1.id :=
    arc_start_at_initial w hfin hfam U m
  have hqs : q.start = p.start := by
    rw [arc_start_at_initial w hfin hfam D n, hps, hs]
  have hpdx : 0 < (p.point 1).re - p.start.re := by
    have h := Polyline.initialDirection_re_pos hp hplen
    exact h
  have hqdx : 0 < (q.point 1).re - p.start.re := by
    have h := Polyline.initialDirection_re_pos hq hqlen
    change 0 < (q.point 1).re - q.start.re at h
    rwa [hqs] at h
  refine ⟨min ((p.point 1).re - p.start.re) ((q.point 1).re - p.start.re),
    lt_min hpdx hqdx, ?_⟩
  intro t ht
  change (G.pos (U.initial m).1.id).re < t ∧
    t < (G.pos (U.initial m).1.id).re +
      min ((p.point 1).re - p.start.re) ((q.point 1).re - p.start.re) at ht
  rw [← hps] at ht
  have hpt : t ≤ (p.point 1).re := by
    have hb := min_le_left ((p.point 1).re - p.start.re)
      ((q.point 1).re - p.start.re)
    linarith only [ht.2, hb]
  have hqt : t ≤ (q.point 1).re := by
    have hb := min_le_right ((p.point 1).re - p.start.re)
      ((q.point 1).re - p.start.re)
    linarith only [ht.2, hb]
  rw [infinitePresentPath_height_on_arc hfin hfam U m
    ⟨ht.1.le, hpt.trans (point_one_re_le_finish hp hplen)⟩,
    infinitePresentPath_height_on_arc hfin hfam D n
    ⟨by rw [hqs]; exact ht.1.le, hqt.trans (point_one_re_le_finish hq hqlen)⟩]
  rw [heightFn_initial hp hplen ht.1.le hpt,
    heightFn_initial hq hqlen (by rw [hqs]; exact ht.1.le) hqt, hqs]
  have hslope := (east_arg_lt_iff_slope_lt
    (Polyline.initialDirection_re_pos hq hqlen)
    (Polyline.initialDirection_re_pos hp hplen)).mp harg
  have hmul := mul_lt_mul_of_pos_right hslope (sub_pos.mpr ht.1)
  linarith only [hmul]

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

private theorem arg_lt_of_prefix_idx_lt {v : ℕ}
    (U D : InfinitePresentPath w ⟨v⟩) (m n : ℕ)
    (hs : (U.initial m).1 = (D.initial n).1)
    (hidx : (kmswPrefixOutgoingEdges w hfin hL htrans hR v
        (List.ofFn (fun i : Fin m => U.edge i.val))).idxOf (D.edge n) <
      (kmswPrefixOutgoingEdges w hfin hL htrans hR v
        (List.ofFn (fun i : Fin m => U.edge i.val))).idxOf (U.edge m)) :
    Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (U.edge m, false)).initialDirection <
      Complex.arg
        ((monotoneLimitDrawing w hfin hfam).arc (D.edge n, false)).initialDirection := by
  have hend : geodesicPrefixEnd w v (List.ofFn (fun i : Fin m => U.edge i.val)) =
      (U.initial m).1.id := by
    rw [← U.prefix_edges, pathEdgeList_endpoint]
  have heU := U.edge_outgoing_at_initial w m
  have heD := D.edge_outgoing_at_initial w n
  rw [← hs] at heD
  rw [← hend] at heU heD
  unfold kmswPrefixOutgoingEdges at hidx
  exact (kmswOutgoingEdgesLeftToRight_idxOf_lt_iff_arg_lt w hfin hfam hL htrans hR
    (geodesicPrefixEnd w v (List.ofFn (fun i : Fin m => U.edge i.val)))
    (kmsw_vertex_allocated_of_finite_incidence w hfin _)
    (D.edge n) (U.edge m)
    ((mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR _ _ _).2 heD)
    ((mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR _ _ _).2 heU)).mp hidx

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result.
Containment between graph traces forces the shared-departure rotation inequalities. -/
theorem inBetween_of_trace_subset_closedBetween (v : ℕ)
    (P R Q : InfinitePresentPath w ⟨v⟩)
    (hsub : pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (Q.edge i, false)) ⊆
      closedBetween
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P.edge i, false)))
        (pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (R.edge i, false)))) :
    InBetweenLeftmostRightmost w hfin hL htrans hR v P R Q := by
  constructor
  · intro m n hs
    refine ⟨hs, ?_⟩
    by_contra h
    have ha := arg_lt_of_prefix_idx_lt w hfin hL htrans hR hfam
      P Q m n hs (lt_of_not_ge h)
    obtain ⟨t, hQ, hP, hlt⟩ :=
      strict_height_graph_points w hfin hfam Q P n m hs.symm ha
    have hbound := (hsub hQ).2 _ hP rfl
    exact (not_le_of_gt hlt) hbound
  · intro m n hs
    refine ⟨hs.symm, ?_⟩
    by_contra h
    have ha := arg_lt_of_prefix_idx_lt w hfin hL htrans hR hfam
      Q R n m hs.symm (lt_of_not_ge h)
    obtain ⟨t, _, hQ, hlt⟩ :=
      strict_height_graph_points w hfin hfam R Q m n hs ha
    obtain ⟨r, hr, hre, him⟩ := (hsub hQ).1
    rw [infinitePresentPath_trace_eq_graph hfin hfam R] at hr
    have hri := hr.2
    rw [hre] at hri
    rw [hri] at him
    exact (not_le_of_gt hlt) him

end DirectedDistances.KMSW
