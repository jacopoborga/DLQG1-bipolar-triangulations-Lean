module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing
import DirectedDistances.KMSW.MonotoneStepCommon
import DirectedDistances.PlanarMap.GraphRegionWedge
import Mathlib.Topology.Piecewise




public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_counts (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 ∧
      (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR, State.addEdge]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_stage_lists (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) :
    (kmswStage w (n + 1)).active = (kmswStage w n).nextEdge ∧
      (kmswStage w (n + 1)).triangles = (kmswStage w n).triangles ∧
      (kmswStage w (n + 1)).UL = (kmswStage w n).UL ++ [(kmswStage w n).nextEdge] ∧
      (kmswStage w (n + 1)).UR = [] ∧
      (kmswStage w (n + 1)).LL = (kmswStage w n).LL ∧
      (kmswStage w (n + 1)).LR = (kmswStage w n).LR ++ [(kmswStage w n).nextEdge] := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR, State.addEdge]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_endpoints (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) :
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    t.west s.nextEdge = s.east s.active ∧ t.east s.nextEdge = s.nextVertex ∧
      t.present s.nextEdge = true := by
  simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR, State.addEdge]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_fresh_edge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) :
    (kmswStage w n).nextEdge ∈ freshEdges w n := by
  rw [freshEdges, (invariant_succ_pen_counts w n hc hUR).1]
  exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self _⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_new_vertex_position (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    layoutPos w (n + 1) (kmswStage w n).nextVertex =
      ⟨(layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re + 1,
        (n + 1 : ℝ)⟩ := by
  apply Complex.ext <;>
    simp [layoutPos, layoutHeight_created_vertex,
      invariant_succ_pen_counts w n hc hUR, kmswStageRank, hc, hUR]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_active_arc (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    layoutArc w (n + 1) (kmswStage w n).nextEdge =
      roofArc (layoutPos w (n + 1) ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge))
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge))
        (n + 1) (rampSlope w n) := by
  have hm : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    simp [isFreshLeftMissing, hc]
  rw [layoutArc_fresh w n _ (invariant_succ_pen_fresh_edge w n hc hUR)]
  simp [hm]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_old_arc (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    layoutArc w (n + 1) e = layoutArc w n e := layoutArc_old w n e he

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_old_dart (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    layoutDart w (n + 1) (stageDartIncl w n d) = layoutDart w n d := by
  rcases d with ⟨e, b⟩
  cases b
  · simpa [layoutDart, stageDartIncl] using layoutArc_old w n e.val e.isLt
  · simpa [layoutDart, stageDartIncl] using
      congrArg Polyline.reverse (layoutArc_old w n e.val e.isLt)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_pos_layout (w : ℕ → Fin 3) (n : ℕ)
    (h : LayoutGood w (n + 1)) :
    ∀ v : Fin (kmswStage w (n + 1)).nextVertex,
      (monotoneLayoutDrawing w (n + 1) h).pos v = layoutPos w (n + 1) v.val := by
  intro v
  rfl

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_arc_layout (w : ℕ → Fin 3) (n : ℕ)
    (h : LayoutGood w (n + 1)) :
    ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
      (monotoneLayoutDrawing w (n + 1) h).arc d = layoutDart w (n + 1) d := by
  intro d
  rfl

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_new_edge_points (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    layoutPos w (n + 1) (t.west s.nextEdge) =
        layoutPos w n (s.east s.active) ∧
      layoutPos w (n + 1) (t.east s.nextEdge) =
        layoutPos w (n + 1) s.nextVertex := by
  dsimp only
  obtain ⟨hw, he, _⟩ := invariant_succ_pen_endpoints w n hc hUR
  have hwestOld : (kmswStage w n).east (kmswStage w n).active <
      (kmswStage w n).nextVertex :=
    (kmswStage_endpoints_lt_nextVertex w n _
      (kmswStage_boundary_ids_lt_nextEdge w n).1).2
  rw [hw, layoutPos_old_vertex w n _ hwestOld, he]
  constructor <;> rfl

private theorem heightFn_of_mem_image {p : Polyline} (hp : p.XMonotone)
    {z : ℂ} (hz : z ∈ p.image) : p.heightFn z.re = z.im := by
  rcases hz with hz | ⟨i, hi, hz⟩
  · rw [hz]
    simpa only [Polyline.point_zero_eq_start] using
      (Polyline.heightFn_point hp (List.length_pos_iff.mpr p.nonempty))
  · have hstrict := Polyline.point_re_lt hp (Nat.lt_succ_self i) hi
    have hz' := (mem_segment_iff_height hstrict).mp hz
    rw [Polyline.heightFn_linear_on_segment hp hi hz'.1 hz'.2.1]
    exact hz'.2.2.symm

private theorem heightFn_finish {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : p.heightFn p.finish.re = p.finish.im := by
  rw [← p.point_last_eq_finish]
  exact p.heightFn_point hp (k := p.points.length - 1) (by omega)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_boundary_values (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let a := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
    G.xmax = a.re ∧ G.lower a.re = a.im ∧ G.upper a.re = a.im := by
  dsimp only
  let a : ℂ := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  change G.xmax = a.re ∧ G.lower a.re = a.im ∧ G.upper a.re = a.im
  have hxmax := G.xmax_eq_active_east_of_UR_nil hUR
  obtain ⟨us, hus⟩ := kmswStage_UL_last w n
  have hactiveU : (kmswStage w n).active ∈
      (kmswStage w n).UL ++ (kmswStage w n).UR := by
    rw [hus, hUR]
    simp
  have hnonempty := kmswStage_boundary_nonempty w n
  let es := ((kmswStage w n).LL ++ (kmswStage w n).LR).getLast hnonempty.2
  have hes : es ∈ (kmswStage w n).LL ++ (kmswStage w n).LR :=
    List.getLast_mem _
  have hids := kmswStage_boundary_ids_lt_nextEdge w n
  have hactiveBound : (kmswStage w n).active < (kmswStage w n).nextEdge := hids.1
  have hesBound : es < (kmswStage w n).nextEdge := by
    apply hids.2
    simp only [List.mem_append] at hes ⊢
    tauto
  have heqEnd := (kmswStage_boundary_endpoints w n).2
  have hupperLast :
      ((kmswStage w n).UL ++ (kmswStage w n).UR).getLast hnonempty.1 =
        (kmswStage w n).active := by
    simp [hus, hUR]
  have hvertex : (kmswStage w n).east es =
      (kmswStage w n).east (kmswStage w n).active := by
    calc
      (kmswStage w n).east es =
          (kmswStage w n).east
            (((kmswStage w n).UL ++ (kmswStage w n).UR).getLast hnonempty.1) :=
        heqEnd.symm
      _ = (kmswStage w n).east (kmswStage w n).active := by rw [hupperLast]
  have hpos : layoutPos w n ((kmswStage w n).east es) =
      layoutPos w n ((kmswStage w n).east (kmswStage w n).active) :=
    congrArg (layoutPos w n) hvertex
  have heUpper : (G.upper a.re) =
      (layoutArc w n (kmswStage w n).active).heightFn a.re := by
    apply G.upper_eq_heightFn hactiveU
    have hrank := kmswStageRank_strict w n _ hactiveBound
    constructor
    · change (kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) : ℝ) ≤
        (kmswStageRank w n ((kmswStage w n).east (kmswStage w n).active) : ℝ)
      exact_mod_cast hrank.le
    · change (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re ≤ _
      rfl
  have hactiveFinish := heightFn_finish
      (layoutArc_points_pairwise w n _ hactiveBound)
      (layoutArc_length_two_le w n _)
  rw [layoutArc_finish w n _ hactiveBound] at hactiveFinish
  have hUpperValue : G.upper a.re = a.im := by
    rw [heUpper]
    change (layoutArc w n (kmswStage w n).active).heightFn
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re = _
    exact hactiveFinish
  have heLower : G.lower a.re = (layoutArc w n es).heightFn a.re := by
    apply G.lower_eq_heightFn hes
    have hrank := kmswStageRank_strict w n es hesBound
    constructor
    · change (layoutPos w n ((kmswStage w n).west es)).re ≤
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re
      rw [← hvertex]
      change (kmswStageRank w n ((kmswStage w n).west es) : ℝ) ≤
        (kmswStageRank w n ((kmswStage w n).east es) : ℝ)
      exact_mod_cast hrank.le
    · change (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re ≤
        (layoutPos w n ((kmswStage w n).east es)).re
      rw [← hvertex]
  have hlastFinish := heightFn_finish (layoutArc_points_pairwise w n es hesBound)
      (layoutArc_length_two_le w n es)
  rw [layoutArc_finish w n es hesBound] at hlastFinish
  have hLowerValue : G.lower a.re = a.im := by
    rw [heLower]
    change (layoutArc w n es).heightFn
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re =
        (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).im
    rw [← hpos]
    exact hlastFinish
  exact ⟨hxmax, hLowerValue, hUpperValue⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_heightFn_roof (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    let a := layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge)
    let b := layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge)
    ∀ x ∈ Set.Icc a.re b.re,
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x =
        roofHeight a b (n + 1) (rampSlope w n) x := by
  dsimp only
  intro x hx
  have he := invariant_succ_pen_fresh_edge w n hc hUR
  have hm : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    simp [isFreshLeftMissing, hc]
  have hz :
      (⟨x, roofHeight
        (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge))
        (layoutPos w (n + 1)
          ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge))
        (n + 1) (rampSlope w n) x⟩ : ℂ) ∈
        (layoutArc w (n + 1) (kmswStage w n).nextEdge).image := by
    rw [layoutArc_image_fresh w n _ he]
    simp only [hm]
    exact ⟨hx.1, hx.2, rfl⟩
  exact heightFn_of_mem_image
    (layoutArc_points_pairwise w (n + 1) _
      (Finset.mem_Ico.mp he).2) hz

private theorem continuousOn_if_le {a b c : ℝ} {f g : ℝ → ℝ}
    (_hab : a ≤ b) (_hbc : b ≤ c)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc b c))
    (hjoin : f b = g b) :
    ContinuousOn (fun x => if x ≤ b then f x else g x) (Set.Icc a c) := by
  have hleft : ContinuousOn f (Set.Icc a c ∩ closure (Set.Iic b)) := by
    apply hf.mono
    intro x hx
    have hxb : x ≤ b := by
      simpa only [closure_Iic, Set.mem_Iic] using hx.2
    exact ⟨hx.1.1, hxb⟩
  have hcomp : (Set.Iic b)ᶜ = Set.Ioi b := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Iic, Set.mem_Ioi]
    exact not_le
  have hrightClosure : closure (Set.Ioi b) ⊆ Set.Ici b := by
    apply closure_minimal
    · intro x hx
      change b < x at hx
      exact hx.le
    · exact isClosed_Ici
  have hright : ContinuousOn g (Set.Icc a c ∩ closure (Set.Iic b)ᶜ) := by
    apply hg.mono
    intro x hx
    have hx' : x ∈ closure (Set.Ioi b) := by simpa only [hcomp] using hx.2
    exact ⟨hrightClosure hx', hx.1.2⟩
  have hboundary : ∀ x ∈ Set.Icc a c ∩ frontier (Set.Iic b), f x = g x := by
    intro x hx
    have hxb : x = b := Set.mem_singleton_iff.mp (frontier_Iic_subset b hx.2)
    subst x
    exact hjoin
  have heq : (fun x => if x ≤ b then f x else g x) =
      (Set.Iic b).piecewise f g := by
    funext x
    by_cases hx : x ≤ b <;> simp [Set.piecewise, hx]
  rw [heq]
  exact hleft.piecewise hboundary hright

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_chart_continuous (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
    let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
    ContinuousOn (fun x => if x ≤ G.xmax then G.lower x else p.heightFn x)
        (Set.Icc G.xmin q.re) ∧
      ContinuousOn (fun x => if x ≤ G.xmax then G.upper x else p.heightFn x)
        (Set.Icc G.xmin q.re) := by
  dsimp only
  let a : ℂ := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let q : ℂ := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let e : ℕ := (kmswStage w n).nextEdge
  let p : Polyline := layoutArc w (n + 1) e
  have hvalues := invariant_succ_pen_boundary_values w n hc hUR G
  change G.xmax = a.re ∧ G.lower a.re = a.im ∧ G.upper a.re = a.im at hvalues
  have hxmax : G.xmax = a.re := hvalues.1
  have hstart : p.start = a := by
    dsimp [p, e, a]
    rw [layoutArc_start w (n + 1) _ (by
      rw [(invariant_succ_pen_counts w n hc hUR).1]
      omega)]
    exact (invariant_succ_pen_new_edge_points w n hc hUR).1
  have hqpos := invariant_succ_pen_new_vertex_position w n hc hUR
  have hqre : q.re = G.xmax + 1 := by
    rw [hxmax]
    exact congrArg Complex.re hqpos
  have hmaxq : G.xmax ≤ q.re := by rw [hqre]; linarith
  have hpPair := layoutArc_points_pairwise w (n + 1) e (by
    dsimp [e]
    rw [(invariant_succ_pen_counts w n hc hUR).1]
    omega)
  have hstartHeightA : p.heightFn a.re = a.im := by
    have hh := p.heightFn_point hpPair (k := 0) (by
      have := p.nonempty
      simp only [List.length_pos_iff.mpr this])
    rw [Polyline.point_zero_eq_start, hstart] at hh
    exact hh
  have hjoinLower : G.lower G.xmax = p.heightFn G.xmax := by
    rw [hxmax]
    exact hvalues.2.1.trans hstartHeightA.symm
  have hjoinUpper : G.upper G.xmax = p.heightFn G.xmax := by
    rw [hxmax]
    exact hvalues.2.2.trans hstartHeightA.symm
  constructor
  · exact continuousOn_if_le G.hx hmaxq G.lower_continuous
      (Polyline.continuous_heightFn p).continuousOn hjoinLower
  · exact continuousOn_if_le G.hx hmaxq G.upper_continuous
      (Polyline.continuous_heightFn p).continuousOn hjoinUpper

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem graphOver_if_le_union {a b c : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hjoin : f b = g b) :
    graphOver a c (fun x => if x ≤ b then f x else g x) =
      graphOver a b f ∪ graphOver b c g := by
  ext z
  constructor
  · rintro ⟨ha, hc, hz⟩
    by_cases hxb : z.re ≤ b
    · left
      exact ⟨ha, hxb, by simpa [hxb] using hz⟩
    · right
      have hbx : b ≤ z.re := le_of_lt (lt_of_not_ge hxb)
      exact ⟨hbx, hc, by simpa [hxb] using hz⟩
  · rintro (⟨ha, hb, hz⟩ | ⟨hb, hc, hz⟩)
    · exact ⟨ha, hb.trans hbc, by simpa [hb] using hz⟩
    · refine ⟨hab.trans hb, hc, ?_⟩
      by_cases hxb : z.re ≤ b
      · have heq : z.re = b := le_antisymm hxb hb
        have hzi : z.im = g b := by simpa [heq] using hz
        simpa [heq, hjoin] using hzi
      · simpa [hxb] using hz

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_chart_order (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 2) (_hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
    ∀ x ∈ Set.Icc G.xmin q.re,
      (if x ≤ G.xmax then G.lower x
        else (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x) ≤
      (if x ≤ G.xmax then G.upper x
        else (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x) := by
  dsimp only
  intro x hx
  by_cases hbranch : x ≤ G.xmax
  · simpa [hbranch] using G.lower_le_upper x ⟨hx.1, hbranch⟩
  · simp [hbranch]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem closedGraphRegion_if_le_split {a b c : ℝ} {f g h : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hjoinF : f b = h b) (hjoinG : g b = h b) :
    closedGraphRegion a c (fun x => if x ≤ b then f x else h x)
        (fun x => if x ≤ b then g x else h x) =
      closedGraphRegion a b f g ∪ graphOver b c h := by
  ext z
  constructor
  · rintro ⟨ha, hc, hlow, hhigh⟩
    by_cases hxb : z.re ≤ b
    · left
      exact ⟨ha, hxb, by simpa [hxb] using hlow,
        by simpa [hxb] using hhigh⟩
    · right
      have hbx : b ≤ z.re := le_of_lt (lt_of_not_ge hxb)
      have hz : z.im = h z.re := by
        apply le_antisymm
        · simpa [hxb] using hhigh
        · simpa [hxb] using hlow
      exact ⟨hbx, hc, hz⟩
  · rintro (⟨ha, hb, hlow, hhigh⟩ | ⟨hb, hc, hz⟩)
    · refine ⟨ha, hb.trans hbc, ?_, ?_⟩
      · simpa [hb] using hlow
      · simpa [hb] using hhigh
    · refine ⟨hab.trans hb, hc, ?_, ?_⟩
      · by_cases hxb : z.re ≤ b
        · have heq : z.re = b := le_antisymm hxb hb
          have hzi : z.im = h b := by simpa only [heq] using hz
          simpa [heq, hjoinF] using hzi.symm.le
        · simpa [hxb] using hz.symm.le
      · by_cases hxb : z.re ≤ b
        · have heq : z.re = b := le_antisymm hxb hb
          have hzi : z.im = h b := by simpa only [heq] using hz
          simpa [heq, hjoinG] using hzi.le
        · simpa [hxb] using hz.le

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_arc_image_graph (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    let a := layoutPos w (n + 1)
      ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge)
    let b := layoutPos w (n + 1)
      ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge)
    (layoutArc w (n + 1) (kmswStage w n).nextEdge).image =
      graphOver a.re b.re
        (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn := by
  dsimp only
  let a : ℂ := layoutPos w (n + 1)
    ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge)
  let b : ℂ := layoutPos w (n + 1)
    ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge)
  have he := invariant_succ_pen_fresh_edge w n hc hUR
  have hm : ¬ isFreshLeftMissing w n (kmswStage w n).nextEdge := by
    simp [isFreshLeftMissing, hc]
  have hheight := invariant_succ_pen_heightFn_roof w n hc hUR
  ext z
  constructor
  · intro hz
    rw [layoutArc_image_fresh w n _ he] at hz
    simp only [hm] at hz
    rcases hz with ⟨ha, hb, hz⟩
    refine ⟨ha, hb, ?_⟩
    exact hz.trans (hheight z.re ⟨ha, hb⟩).symm
  · rintro ⟨ha, hb, hz⟩
    rw [layoutArc_image_fresh w n _ he]
    simp only [hm]
    refine ⟨ha, hb, ?_⟩
    exact hz.trans (hheight z.re ⟨ha, hb⟩)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_chart_trace_splits (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
    let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
    graphOver G.xmin q.re (fun x => if x ≤ G.xmax then G.lower x else p.heightFn x) =
        graphOver G.xmin G.xmax G.lower ∪ p.image ∧
      graphOver G.xmin q.re (fun x => if x ≤ G.xmax then G.upper x else p.heightFn x) =
        graphOver G.xmin G.xmax G.upper ∪ p.image := by
  dsimp only
  let a : ℂ := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let q : ℂ := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let e : ℕ := (kmswStage w n).nextEdge
  let p : Polyline := layoutArc w (n + 1) e
  have hvalues := invariant_succ_pen_boundary_values w n hc hUR G
  change G.xmax = a.re ∧ G.lower a.re = a.im ∧ G.upper a.re = a.im at hvalues
  have hxmax : G.xmax = a.re := hvalues.1
  have hqpos := invariant_succ_pen_new_vertex_position w n hc hUR
  have hqre : q.re = G.xmax + 1 := by
    rw [hxmax]
    exact congrArg Complex.re hqpos
  have hmaxq : G.xmax ≤ q.re := by rw [hqre]; linarith
  have hpoints := invariant_succ_pen_new_edge_points w n hc hUR
  change layoutPos w (n + 1) ((kmswStage w (n + 1)).west e) = a ∧
      layoutPos w (n + 1) ((kmswStage w (n + 1)).east e) = q at hpoints
  have hstart : p.start = a := by
    dsimp [p, e]
    rw [layoutArc_start w (n + 1) _ (by
      rw [(invariant_succ_pen_counts w n hc hUR).1]
      omega)]
    exact hpoints.1
  have hpPair := layoutArc_points_pairwise w (n + 1) e (by
    dsimp [e]
    rw [(invariant_succ_pen_counts w n hc hUR).1]
    omega)
  have hstartHeight : p.heightFn a.re = a.im := by
    have hh := p.heightFn_point hpPair (k := 0) (by
      have := p.nonempty
      simp only [List.length_pos_iff.mpr this])
    rw [Polyline.point_zero_eq_start, hstart] at hh
    exact hh
  have hjoinLower : G.lower G.xmax = p.heightFn G.xmax := by
    rw [hxmax]
    exact hvalues.2.1.trans hstartHeight.symm
  have hjoinUpper : G.upper G.xmax = p.heightFn G.xmax := by
    rw [hxmax]
    exact hvalues.2.2.trans hstartHeight.symm
  have hArcGraph := invariant_succ_pen_arc_image_graph w n hc hUR
  change p.image = graphOver
    (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)).re
    (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)).re p.heightFn at hArcGraph
  rw [hpoints.1, hpoints.2] at hArcGraph
  rw [← hxmax] at hArcGraph
  have hArcGraph' : p.image = graphOver G.xmax q.re p.heightFn := by
    exact hArcGraph
  constructor
  · rw [graphOver_if_le_union G.hx hmaxq hjoinLower, ← hArcGraph']
  · rw [graphOver_if_le_union G.hx hmaxq hjoinUpper, ← hArcGraph']

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_drawing_arc_old (w : ℕ → Fin 3) (n : ℕ)
    (_hc : w n = 2) (_hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (d : StageDart (kmswStage w n).nextEdge) :
    (monotoneLayoutDrawing w (n + 1) h).arc (stageDartIncl w n d) = P.arc d := by
  calc
    (monotoneLayoutDrawing w (n + 1) h).arc (stageDartIncl w n d) =
        layoutDart w (n + 1) (stageDartIncl w n d) :=
      invariant_succ_pen_arc_layout w n h (stageDartIncl w n d)
    _ = layoutDart w n d := invariant_succ_pen_old_dart w n d
    _ = P.arc d := (G.arc_layout d).symm

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_old_edge_trace (w : ℕ → Fin 3) (n i : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (hi : i < (kmswStage w n).nextEdge) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) i = stageEdgeTrace P i := by
  have hcount := (invariant_succ_pen_counts w n hc hUR).1
  have hinew : i < (kmswStage w (n + 1)).nextEdge := by omega
  have hd : ((⟨i, hinew⟩, false) : StageDart (kmswStage w (n + 1)).nextEdge) =
      stageDartIncl w n ((⟨i, hi⟩, false)) := by
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  unfold stageEdgeTrace
  rw [dite_eq_left hinew, dite_eq_left hi, hd]
  exact congrArg Polyline.image
    (invariant_succ_pen_drawing_arc_old w n hc hUR G h ((⟨i, hi⟩, false)))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_new_edge_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    (h : LayoutGood w (n + 1)) :
    stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) (kmswStage w n).nextEdge =
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).image := by
  have hcount := (invariant_succ_pen_counts w n hc hUR).1
  have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by omega
  unfold stageEdgeTrace
  rw [dite_eq_left he]
  rw [invariant_succ_pen_arc_layout w n h]
  rfl

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_lower_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
    let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
    graphOver G.xmin q.re (fun x =>
      if x ≤ G.xmax then G.lower x else p.heightFn x) =
        ⋃ e ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR,
          stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  dsimp only
  let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hLists := invariant_succ_pen_stage_lists w n hc hUR
  rcases hLists with ⟨_, _, _, _, hLL, hLR⟩
  have hcount := (invariant_succ_pen_counts w n hc hUR).1
  have hOldBound : ∀ e ∈ s.LL ++ s.LR, e < s.nextEdge := by
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append] at he ⊢
    tauto
  have hTraceSets :
      (⋃ e ∈ t.LL ++ t.LR, stageEdgeTrace
        (monotoneLayoutDrawing w (n + 1) h) e) =
        (⋃ e ∈ s.LL ++ s.LR, stageEdgeTrace P e) ∪ p.image := by
    rw [hLL, hLR]
    ext z
    simp only [Set.mem_iUnion, List.mem_append, List.mem_singleton, Set.mem_union]
    constructor
    · rintro ⟨e, he, hz⟩
      rcases he with he | he
      · have heOld : e ∈ s.LL ++ s.LR := by
          simpa [s] using (List.mem_append.mpr (Or.inl he) :
            e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR)
        have htr := invariant_succ_pen_old_edge_trace w n e hc hUR G h
          (hOldBound e heOld)
        rw [htr] at hz
        exact Or.inl ⟨e, Or.inl he, hz⟩
      · rcases he with he | he
        · have heOld : e ∈ s.LL ++ s.LR := by
            simpa [s] using (List.mem_append.mpr (Or.inr he) :
              e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR)
          have htr := invariant_succ_pen_old_edge_trace w n e hc hUR G h
            (hOldBound e heOld)
          rw [htr] at hz
          exact Or.inl ⟨e, Or.inr he, hz⟩
        · subst e
          exact Or.inr (by
            rw [invariant_succ_pen_new_edge_trace w n hc hUR h] at hz
            exact hz)
    · rintro (⟨e, he, hz⟩ | hz)
      · rcases he with he | he
        · have heNew : e ∈ s.LL ++ (s.LR ++ [s.nextEdge]) :=
            List.mem_append.mpr (Or.inl he)
          have htr := invariant_succ_pen_old_edge_trace w n e hc hUR G h
            (hOldBound e (by simpa [s] using
              (List.mem_append.mpr (Or.inl he) :
                e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR)))
          exact ⟨e, by simpa [s] using heNew, htr.symm ▸ hz⟩
        · have heNew : e ∈ s.LL ++ (s.LR ++ [s.nextEdge]) :=
            List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl he)))
          have htr := invariant_succ_pen_old_edge_trace w n e hc hUR G h
            (hOldBound e (by simpa [s] using
              (List.mem_append.mpr (Or.inr he) :
                e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR)))
          exact ⟨e, by simpa [s] using heNew, htr.symm ▸ hz⟩
      · have heNew : s.nextEdge ∈ s.LL ++ (s.LR ++ [s.nextEdge]) := by simp
        exact ⟨s.nextEdge, by simp [s], by
          rw [invariant_succ_pen_new_edge_trace w n hc hUR h]
          exact hz⟩
  have hsplit := invariant_succ_pen_chart_trace_splits w n hc hUR G
  rw [hsplit.1, G.lower_trace, ← hTraceSets]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_upper_trace (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
    let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
    graphOver G.xmin q.re (fun x =>
      if x ≤ G.xmax then G.upper x else p.heightFn x) =
        ⋃ e ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR,
          stageEdgeTrace (monotoneLayoutDrawing w (n + 1) h) e := by
  dsimp only
  let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hLists := invariant_succ_pen_stage_lists w n hc hUR
  rcases hLists with ⟨_, _, hUL, hUR', _, _⟩
  have hOldBound : ∀ e ∈ s.UL ++ s.UR, e < s.nextEdge := by
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2
    simp only [List.mem_append] at he ⊢
    tauto
  have hTraceSets :
      (⋃ e ∈ t.UL ++ t.UR, stageEdgeTrace
        (monotoneLayoutDrawing w (n + 1) h) e) =
        (⋃ e ∈ s.UL ++ s.UR, stageEdgeTrace P e) ∪ p.image := by
    rw [hUL, hUR']
    simp only [List.append_nil]
    ext z
    simp only [Set.mem_iUnion, List.mem_append, List.mem_singleton, Set.mem_union]
    constructor
    · rintro ⟨e, he, hz⟩
      rcases he with he | he
      · have heOld : e ∈ s.UL ++ s.UR := by
          simpa [s] using (List.mem_append.mpr (Or.inl he) :
            e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)
        have htr := invariant_succ_pen_old_edge_trace w n e hc hUR G h
          (hOldBound e heOld)
        rw [htr] at hz
        exact Or.inl ⟨e, Or.inl he, hz⟩
      · exact Or.inr (by
          subst e
          rw [invariant_succ_pen_new_edge_trace w n hc hUR h] at hz
          exact hz)
    · rintro (⟨e, he, hz⟩ | hz)
      · rcases he with he | he
        · have heNew : e ∈ s.UL ++ [s.nextEdge] := by
            exact List.mem_append.mpr (Or.inl he)
          have htr := invariant_succ_pen_old_edge_trace w n e hc hUR G h
            (hOldBound e (by simpa [s] using
              (List.mem_append.mpr (Or.inl he) :
                e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR)))
          have heNew : e ∈ s.UL ++ [s.nextEdge] := List.mem_append.mpr (Or.inl he)
          exact ⟨e, by simpa [s] using heNew, htr.symm ▸ hz⟩
        · have hfalse : False := by
            simp [s, hUR] at he
          exact False.elim hfalse
      · have heNew : s.nextEdge ∈ s.UL ++ [s.nextEdge] := by simp
        exact ⟨s.nextEdge, by simp [s], by
          rw [invariant_succ_pen_new_edge_trace w n hc hUR h]
          exact hz⟩
  have hsplit := invariant_succ_pen_chart_trace_splits w n hc hUR G
  rw [hsplit.2, G.upper_trace, ← hTraceSets]

private theorem abs_roofHeight_sub_le {a b : ℂ} {H M x y : ℝ} (hM : 0 ≤ M) :
    |roofHeight a b H M x - roofHeight a b H M y| ≤ M * |x - y| := by
  have hleft :
      |(a.im + M * (x - a.re)) - (a.im + M * (y - a.re))| ≤ M * |x - y| := by
    rw [show (a.im + M * (x - a.re)) - (a.im + M * (y - a.re)) =
      M * (x - y) by ring, abs_mul, abs_of_nonneg hM]
  have hright :
      |(b.im + M * (b.re - x)) - (b.im + M * (b.re - y))| ≤ M * |x - y| := by
    rw [show (b.im + M * (b.re - x)) - (b.im + M * (b.re - y)) =
      -M * (x - y) by ring, abs_mul, abs_neg, abs_of_nonneg hM]
  have hinner :
      |min (a.im + M * (x - a.re)) (b.im + M * (b.re - x)) -
        min (a.im + M * (y - a.re)) (b.im + M * (b.re - y))| ≤ M * |x - y| :=
    (abs_min_sub_min_le_max _ _ _ _).trans (max_le hleft hright)
  calc
    |roofHeight a b H M x - roofHeight a b H M y| ≤
        max |H - H| _ := abs_min_sub_min_le_max _ _ _ _
    _ ≤ M * |x - y| := max_le (by simp [mul_nonneg hM (abs_nonneg (x - y))]) hinner

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_upper_lipschitz_margin (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∃ L : ℝ, 0 ≤ L ∧ L < rampSlope w (n + 1) ∧
      ∀ x ∈ Set.Icc G.xmin
          (layoutPos w (n + 1) (kmswStage w n).nextVertex).re,
        ∀ y ∈ Set.Icc G.xmin
            (layoutPos w (n + 1) (kmswStage w n).nextVertex).re,
          |(if x ≤ G.xmax then G.upper x else
              (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x) -
            (if y ≤ G.xmax then G.upper y else
              (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn y)| ≤
            L * |x - y| := by
  obtain ⟨L, hL, hLM, hLip⟩ := G.upper_lipschitz_margin
  let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
  let a := layoutPos w (n + 1)
    ((kmswStage w (n + 1)).west (kmswStage w n).nextEdge)
  let b := layoutPos w (n + 1)
    ((kmswStage w (n + 1)).east (kmswStage w n).nextEdge)
  let M := rampSlope w n
  have hM : 0 < M := rampSlope_pos w n
  have hLM' : L ≤ M := le_of_lt hLM
  have hvalues := invariant_succ_pen_boundary_values w n hc hUR G
  change G.xmax = (layoutPos w n
    ((kmswStage w n).east (kmswStage w n).active)).re ∧ _ at hvalues
  have hpoints := invariant_succ_pen_new_edge_points w n hc hUR
  have hleft : a.re = G.xmax := by
    dsimp [a]
    rw [hpoints.1, hvalues.1]
  have hright : b.re = q.re := by
    dsimp [a, b, q]
    exact congrArg Complex.re hpoints.2
  have hstart : p.start = layoutPos w n
      ((kmswStage w n).east (kmswStage w n).active) := by
    dsimp [p]
    rw [layoutArc_start w (n + 1) _ (by
      rw [(invariant_succ_pen_counts w n hc hUR).1]
      omega)]
    exact hpoints.1
  have hpair := layoutArc_points_pairwise w (n + 1) (kmswStage w n).nextEdge
    (by rw [(invariant_succ_pen_counts w n hc hUR).1]; omega)
  have hjoin : p.heightFn G.xmax = G.upper G.xmax := by
    rw [hvalues.1]
    have hh := p.heightFn_point hpair (k := 0) (by
      have := p.nonempty
      simp only [List.length_pos_iff.mpr this])
    rw [Polyline.point_zero_eq_start, hstart] at hh
    exact hh.trans hvalues.2.2.symm
  have hqbound : G.xmax ≤ q.re := by
    have hq := invariant_succ_pen_new_vertex_position w n hc hUR
    rw [hvalues.1]
    have := congrArg Complex.re hq
    change _ ≤ _
    rw [this]
    simp
  have hroof : ∀ x ∈ Set.Icc G.xmax q.re,
      p.heightFn x = roofHeight a b (n + 1) M x := by
    intro x hx
    have hraw := invariant_succ_pen_heightFn_roof w n hc hUR x
    have harg : x ∈ Set.Icc a.re b.re := by
      rw [hleft, hright]
      exact hx
    simpa [p, a, b, M] using hraw harg
  have hroofLip : ∀ x ∈ Set.Icc G.xmax q.re, ∀ y ∈ Set.Icc G.xmax q.re,
      |p.heightFn x - p.heightFn y| ≤ M * |x - y| := by
    intro x hx y hy
    rw [hroof x hx, hroof y hy]
    exact abs_roofHeight_sub_le hM.le
  have hLipOrdered : ∀ x ∈ Set.Icc G.xmin q.re,
      ∀ y ∈ Set.Icc G.xmin q.re, x ≤ y →
        |(if x ≤ G.xmax then G.upper x else p.heightFn x) -
          (if y ≤ G.xmax then G.upper y else p.heightFn y)| ≤ M * |x - y| := by
    intro x hx y hy hxy
    by_cases hyOld : y ≤ G.xmax
    · have hxOld : x ≤ G.xmax := hxy.trans hyOld
      simp only [hxOld, hyOld, ↓reduceIte]
      calc
        |G.upper x - G.upper y| ≤ L * |x - y| :=
          hLip x ⟨hx.1, hxOld⟩ y ⟨hy.1, hyOld⟩
        _ ≤ M * |x - y| := mul_le_mul_of_nonneg_right hLM' (abs_nonneg _)
    · by_cases hxOld : x ≤ G.xmax
      · simp only [hxOld, hyOld, ↓reduceIte]
        have hyNew : G.xmax < y := lt_of_not_ge hyOld
        calc
          |G.upper x - p.heightFn y| ≤
              |G.upper x - G.upper G.xmax| +
                |G.upper G.xmax - p.heightFn y| := abs_sub_le _ _ _
          _ ≤ L * |x - G.xmax| + M * |G.xmax - y| := by
            apply add_le_add
            · exact hLip x ⟨hx.1, hxOld⟩ G.xmax ⟨G.hx, le_rfl⟩
            · rw [← hjoin]
              exact hroofLip G.xmax ⟨le_rfl, hqbound⟩ y
                ⟨hyNew.le, hy.2⟩
          _ ≤ M * |x - y| := by
            have hleftle : L * |x - G.xmax| ≤ M * |x - G.xmax| :=
              mul_le_mul_of_nonneg_right hLM' (abs_nonneg _)
            rw [abs_of_nonpos (sub_nonpos.mpr hxOld)] at hleftle
            rw [abs_of_nonpos (sub_nonpos.mpr hxOld),
              abs_of_nonpos (sub_nonpos.mpr hyNew.le),
              abs_of_nonpos (sub_nonpos.mpr hxy)]
            nlinarith
      · simp only [hxOld, hyOld, ↓reduceIte]
        exact hroofLip x ⟨le_of_not_ge hxOld, hx.2⟩ y
          ⟨le_of_not_ge hyOld, hy.2⟩
  have hLipNew : ∀ x ∈ Set.Icc G.xmin q.re, ∀ y ∈ Set.Icc G.xmin q.re,
      |(if x ≤ G.xmax then G.upper x else p.heightFn x) -
        (if y ≤ G.xmax then G.upper y else p.heightFn y)| ≤ M * |x - y| := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · exact hLipOrdered x hx y hy hxy
    · simpa only [abs_sub_comm] using hLipOrdered y hy x hx hyx
  refine ⟨M, hM.le, ?_, hLipNew⟩
  dsimp [M]
  exact rampSlope_lt w (Nat.lt_succ_self n)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_cover_lower (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ e : Fin (kmswStage w (n + 1)).nextEdge,
      e.val ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR ∨
        ∃ i : Fin (kmswStage w n).triangles.length, e.val ∈ G.capLower i := by
  intro e
  have hLists := invariant_succ_pen_stage_lists w n hc hUR
  rcases hLists with ⟨_, _, hUL, hUR', _, _⟩
  have hcount := (invariant_succ_pen_counts w n hc hUR).1
  by_cases hold : e.val < (kmswStage w n).nextEdge
  · let old : Fin (kmswStage w n).nextEdge := ⟨e.val, hold⟩
    rcases G.cover_lower old with hb | ⟨i, hi⟩
    · left
      rcases List.mem_append.mp hb with hb | hb
      · rw [hUL, hUR']
        apply List.mem_append_left
        exact List.mem_append.mpr (Or.inl (by simpa [old] using hb))
      · simp [hUR] at hb
    · exact Or.inr ⟨i, hi⟩
  · left
    have heq : e.val = (kmswStage w n).nextEdge := by
      have he : e.val < (kmswStage w n).nextEdge + 1 := by
        simpa only [hcount] using e.isLt
      omega
    simp only [hUL, hUR', List.append_nil]
    exact List.mem_append.mpr (Or.inr (by simp [heq]))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_cover_upper (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∀ e : Fin (kmswStage w (n + 1)).nextEdge,
      e.val ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR ∨
        ∃ i : Fin (kmswStage w n).triangles.length, e.val ∈ G.capUpper i := by
  intro e
  have hLists := invariant_succ_pen_stage_lists w n hc hUR
  rcases hLists with ⟨_, _, _, _, hLL, hLR⟩
  have hcount := (invariant_succ_pen_counts w n hc hUR).1
  by_cases hold : e.val < (kmswStage w n).nextEdge
  · let old : Fin (kmswStage w n).nextEdge := ⟨e.val, hold⟩
    rcases G.cover_upper old with hb | ⟨i, hi⟩
    · left
      rcases List.mem_append.mp hb with hb | hb
      · rw [hLL, hLR]
        exact List.mem_append.mpr (Or.inl (by simpa [old] using hb))
      · rw [hLL, hLR]
        exact List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl (by simpa [old] using hb))))
    · exact Or.inr ⟨i, hi⟩
  · left
    have heq : e.val = (kmswStage w n).nextEdge := by
      have he : e.val < (kmswStage w n).nextEdge + 1 := by
        simpa only [hcount] using e.isLt
      omega
    simp only [hLL, hLR]
    exact List.mem_append.mpr
      (Or.inr (List.mem_append.mpr (Or.inr (by simp [heq]))))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_cap_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    let hLen := congrArg List.length
      (invariant_succ_pen_stage_lists w n hc hUR).2.1
    ∀ i j : Fin (kmswStage w (n + 1)).triangles.length, i ≠ j →
      Disjoint (G.cap (i.cast hLen)).region (G.cap (j.cast hLen)).region := by
  intro hLen i j hij
  apply G.cap_disjoint
  intro hEq
  apply hij
  apply Fin.ext
  simpa using congrArg Fin.val hEq

private theorem cap_region_real_lt_xmax {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) {z : ℂ}
    (hz : z ∈ (G.cap i).region) : z.re < G.xmax := by
  have hsub : (G.cap i).region ⊆
      closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    intro y hy
    rw [← G.cover]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, subset_closure hy⟩)
  have hzK := hsub hz
  by_contra hnot
  have heq : z.re = G.xmax := le_antisymm hzK.2.1 (le_of_not_gt hnot)
  have hopen := isOpen_graphRegion (G.cap i).low_continuous
    (G.cap i).high_continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z hz
  let z' := z + ((ε / 2 : ℝ) : ℂ)
  have hdist : dist z' z < ε := by
    dsimp [z']
    rw [dist_eq_norm]
    have hsubz : z + ((ε / 2 : ℝ) : ℂ) - z = ((ε / 2 : ℝ) : ℂ) := by
      abel
    rw [hsubz]
    have hpos : 0 < ε / 2 := by linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    linarith
  have hz' : z' ∈ (G.cap i).region := hball (Metric.mem_ball.mpr hdist)
  have hz'K := hsub hz'
  have hre : z'.re = z.re + ε / 2 := by
    simp [z', Complex.add_re]
  rw [heq] at hre
  have : G.xmax < z'.re := by rw [hre]; linarith
  exact (not_le_of_gt this) hz'K.2.1

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_cap_pendant_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (G.cap i).region
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).image := by
  apply Set.disjoint_left.mpr
  intro z hzcap hzedge
  have hvalues := invariant_succ_pen_boundary_values w n hc hUR G
  have hpoints := invariant_succ_pen_new_edge_points w n hc hUR
  have hp := invariant_succ_pen_arc_image_graph w n hc hUR
  dsimp only at hp
  rw [hpoints.1, hpoints.2] at hp
  rw [hp] at hzedge
  have hstrict := cap_region_real_lt_xmax G i hzcap
  exact (not_le_of_gt hstrict) (hvalues.1.symm ▸ hzedge.1)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem invariant_succ_pen_cap_avoid_union (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    Disjoint (G.cap i).region
      (P.image ∪ (layoutArc w (n + 1) (kmswStage w n).nextEdge).image) := by
  apply Set.disjoint_left.mpr
  intro z hzcap hz
  rcases hz with hzOld | hzNew
  · exact Set.disjoint_left.mp (G.cap_avoid i) hzcap hzOld
  · exact Set.disjoint_left.mp
      (invariant_succ_pen_cap_pendant_disjoint w n hc hUR G i) hzcap hzNew

open Set

private theorem reverse_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · have hz' : z = p.finish := by
      simpa only [Polyline.start_reverse, Set.mem_singleton_iff] using hz
    rw [hz', ← p.point_last_eq_finish]
    by_cases hlen : 2 ≤ p.points.length
    · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
      have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
      rw [Polyline.segmentAt, hidx]
      exact right_mem_segment ℝ _ _
    · have hlen1 : p.points.length = 1 := by
        have := List.length_pos_iff.mpr p.nonempty
        omega
      simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
      exact Or.inl rfl
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    have hrev : ∀ j, j < p.points.length →
        p.reverse.point j = p.point (p.points.length - 1 - j) := by
      intro j hj
      have hj' : p.points.length - 1 - j < p.points.length := by omega
      change p.points.reverse.getD j p.reverse.start =
        p.points.getD (p.points.length - 1 - j) p.start
      rw [List.getD_reverse j hj]
      rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj']
      rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj']
    have hidx : p.points.length - 1 - (i + 1) + 1 = p.points.length - 1 - i := by
      omega
    refine Or.inr ⟨p.points.length - 1 - (i + 1), by omega, ?_⟩
    simp only [Polyline.segmentAt, hrev i (by omega), hrev (i + 1) hi'] at hz
    simpa only [Polyline.segmentAt, hidx, segment_symm] using hz

private theorem finish_mem_image (p : Polyline) : p.finish ∈ p.image := by
  apply reverse_image_subset
  exact Or.inl (Polyline.start_reverse p).symm

private theorem pen_old_arc (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (he' : e < (kmswStage w (n + 1)).nextEdge) (b : Bool) :
    (monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he'⟩, b) =
      P.arc (⟨e, he⟩, b) := by
  rw [G.arc_layout]
  change (if b then (layoutArc w (n + 1) e).reverse else layoutArc w (n + 1) e) = _
  rw [layoutArc_old w n e he]

private theorem upper_edge_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) :
    e < (kmswStage w n).nextEdge := by
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
  simp only [List.mem_append] at he ⊢
  tauto

private theorem step_triangle_ids (s : State) (c : Step)
    (ha : s.active < s.nextEdge) (hb : ∀ e ∈ s.UL, e < s.nextEdge)
    (htri : ∀ t ∈ s.triangles,
      t.1 < s.nextEdge ∧ t.2.1 < s.nextEdge ∧ t.2.2 < s.nextEdge) :
    ∀ t ∈ (kmswStepOfStep s c).triangles,
      t.1 < (kmswStepOfStep s c).nextEdge ∧
        t.2.1 < (kmswStepOfStep s c).nextEdge ∧
        t.2.2 < (kmswStepOfStep s c).nextEdge := by
  intro t ht
  cases c with
  | down =>
    cases hs : s.UR with
    | nil =>
      simp only [kmswStepOfStep, hs, State.addEdge] at ht ⊢
      obtain ⟨h0, h1, h2⟩ := htri t ht
      omega
    | cons e es =>
      simpa only [kmswStepOfStep, hs] using htri t (by simpa [kmswStepOfStep, hs] using ht)
  | left =>
    cases hs : s.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
        List.mem_singleton] at ht ⊢
      rcases ht with ht | rfl
      · obtain ⟨h0, h1, h2⟩ := htri t ht
        omega
      · dsimp only
        omega
    | cons e es =>
      have he : e < s.nextEdge := by
        apply hb e
        apply List.mem_of_mem_dropLast
        apply List.mem_reverse.mp
        rw [hs]
        exact List.mem_cons_self
      simp only [kmswStepOfStep, hs, State.addEdge, List.mem_append,
        List.mem_singleton] at ht ⊢
      rcases ht with ht | rfl
      · obtain ⟨h0, h1, h2⟩ := htri t ht
        omega
      · dsimp only
        omega
  | up =>
    simp only [kmswStepOfStep, State.addEdge, List.mem_append, List.mem_singleton] at ht ⊢
    rcases ht with ht | rfl
    · obtain ⟨h0, h1, h2⟩ := htri t ht
      omega
    · dsimp only
      omega

private theorem triangle_ids_lt (w : ℕ → Fin 3) (n : ℕ) :
    ∀ t ∈ (kmswStage w n).triangles,
      t.1 < (kmswStage w n).nextEdge ∧ t.2.1 < (kmswStage w n).nextEdge ∧
        t.2.2 < (kmswStage w n).nextEdge := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    apply step_triangle_ids (kmswStage w n) (kmswCodeStep (w n))
      (kmswStage_boundary_ids_lt_nextEdge w n).1 ?_ ih
    intro e he
    exact upper_edge_lt w n e (List.mem_append.mpr (Or.inl he))

private theorem cap_edge_lt (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (i : Fin (kmswStage w n).triangles.length)
    (e : ℕ) (he : e ∈ G.capLower i ++ G.capUpper i) :
    e < (kmswStage w n).nextEdge := by
  have ht := triangle_ids_lt w n _ (List.get_mem _ i)
  rcases (G.cap_edges i e).mp he with he | he | he
  · exact he ▸ ht.1
  · exact he ▸ ht.2.1
  · exact he ▸ ht.2.2

private theorem initial_ray_mem_image (p : Polyline) (hlen : 2 ≤ p.points.length)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p.start + t • p.initialDirection ∈ p.image := by
  refine Or.inr ⟨0, by omega, ?_⟩
  change p.start + t • p.initialDirection ∈ segment ℝ (p.point 0) (p.point 1)
  rw [Polyline.point_zero_eq_start]
  have heq : p.start + t • p.initialDirection =
      (1 - t) • p.start + t • p.point 1 := by
    rw [Polyline.initialDirection, smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, rfl⟩

private theorem initial_line_at (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : p.initialDirection.re ≠ 0)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) (x : ℝ)
    (ht : (x - p.start.re) / p.initialDirection.re ∈ Icc (0 : ℝ) 1) :
    f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  have hx : (p.start + ((x - p.start.re) / p.initialDirection.re) •
      p.initialDirection).re = x := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, div_mul_cancel₀ _ hd]
    ring
  have hh := hgraph _ (initial_ray_mem_image p hlen ht)
  rw [hx] at hh
  rw [hh]
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  ring

private theorem initial_line_east (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : 0 < p.initialDirection.re)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∃ η > 0, ∀ x ∈ Icc p.start.re (p.start.re + η),
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  refine ⟨p.initialDirection.re, hd, ?_⟩
  intro x hx
  apply initial_line_at p f hlen hd.ne' hgraph x
  exact ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,
    (div_le_one hd).mpr (by linarith only [hx.2])⟩

private theorem initial_line_west (p : Polyline) (f : ℝ → ℝ)
    (hlen : 2 ≤ p.points.length) (hd : p.initialDirection.re < 0)
    (hgraph : ∀ z ∈ p.image, f z.re = z.im) :
    ∃ η > 0, ∀ x ∈ Icc (p.start.re - η) p.start.re,
      f x = p.start.im + (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) :=
    by
  refine ⟨-p.initialDirection.re, neg_pos.mpr hd, ?_⟩
  intro x hx
  apply initial_line_at p f hlen hd.ne hgraph x
  exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hx.2) hd.le,
    (div_le_one_of_neg hd).mpr (by linarith only [hx.1])⟩

private theorem pen_drawing_image (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) :
    (monotoneLayoutDrawing w (n + 1) h).image =
      P.image ∪ (layoutArc w (n + 1) (kmswStage w n).nextEdge).image := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  obtain ⟨hcount, hvertices⟩ := invariant_succ_pen_counts w n hc hUR
  have h0 : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by omega
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨⟨e, b⟩, hz⟩)
    · by_cases hv : v.val < (kmswStage w n).nextVertex
      · left
        refine Or.inl ⟨⟨v.val, hv⟩, ?_⟩
        rw [G.pos_layout]
        exact (layoutPos_old_vertex w n v.val hv).symm
      · right
        have hv' : v.val = (kmswStage w n).nextVertex := by have := v.isLt; omega
        have hz : Q.pos v =
            (layoutArc w (n + 1) (kmswStage w n).nextEdge).finish := by
          rw [layoutArc_finish w (n + 1) _ h0,
            (invariant_succ_pen_endpoints w n hc hUR).2.1]
          change layoutPos w (n + 1) v.val = _
          rw [hv']
        exact hz ▸ finish_mem_image _
    · by_cases he : e.val < (kmswStage w n).nextEdge
      · left
        rw [pen_old_arc w n G h e.val he e.isLt b] at hz
        exact Or.inr ⟨(⟨e.val, he⟩, b), hz⟩
      · have heq : e.val = (kmswStage w n).nextEdge := by have := e.isLt; omega
        have hz' : z ∈ (layoutArc w (n + 1) e.val).image := by
          cases b
          · exact hz
          · exact reverse_image_subset _ hz
        exact Or.inr (heq ▸ hz')
  · rintro (hz | hz)
    · rcases hz with ⟨v, rfl⟩ | ⟨d, hz⟩
      · refine Or.inl ⟨stageVertexIncl w n v, ?_⟩
        rw [G.pos_layout]
        exact layoutPos_old_vertex w n v.val v.isLt
      · refine Or.inr ⟨stageDartIncl w n d, ?_⟩
        rw [invariant_succ_pen_drawing_arc_old w n hc hUR G h d]
        exact hz
    · exact Or.inr ⟨(⟨_, h0⟩, false), hz⟩

private theorem pen_image_height_le (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) (h : LayoutGood w (n + 1)) :
    ∀ z ∈ (monotoneLayoutDrawing w (n + 1) h).image, z.im ≤ (n + 1 : ℝ) := by
  intro z hz
  rw [pen_drawing_image w n hc hUR G h] at hz
  rcases hz with hz | hz
  · exact (G.image_height_le z hz).trans (by exact_mod_cast Nat.le_succ n)
  · have hi := layoutArc_image_fresh w n _ (invariant_succ_pen_fresh_edge w n hc hUR)
    dsimp only at hi
    simp only [isFreshLeftMissing, hc] at hi
    rw [hi] at hz
    rw [hz.2.2]
    exact roofHeight_le_top _ _ _ _ _


private theorem pen_ext_lower_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hmem : e ∈ (kmswStage w (n + 1)).LL ++ (kmswStage w (n + 1)).LR) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, true)).initialDirection
      (closedGraphRegion G.xmin
        (layoutPos w (n + 1) (kmswStage w n).nextVertex).re
        (fun x => if x ≤ G.xmax then G.lower x else
          (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x)
        (fun x => if x ≤ G.xmax then G.upper x else
          (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x))ᶜ := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  let p := Q.arc (⟨e, he⟩, true)
  have hd : p.initialDirection.re < 0 :=
    Polyline.reverse_initialDirection_re_neg (layoutArc_points_pairwise w (n + 1) e he)
      (layoutArc_length_two_le w (n + 1) e)
  have hgraph : ∀ z ∈ p.image, (fun x => if x ≤ G.xmax then G.lower x else
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x) z.re = z.im := by
    intro z hz
    have hzG : z ∈ graphOver G.xmin
        (layoutPos w (n + 1) (kmswStage w n).nextVertex).re
        (fun x => if x ≤ G.xmax then G.lower x else
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x) := by
      rw [invariant_succ_pen_lower_trace w n hc hUR G h]
      refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hmem, ?_⟩⟩
      simp only [stageEdgeTrace, he, ↓reduceDIte]
      exact reverse_image_subset _ hz
    exact hzG.2.2.symm
  obtain ⟨η, hη, hline⟩ := initial_line_west p (fun x => if x ≤ G.xmax then G.lower x else
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x)
    (Q.arc_length (⟨e, he⟩, true)) hd hgraph
  exact wedgeIn_compl_closedGraphRegion_west_lower p.start p.initialDirection η hd hη hline


private theorem pen_ext_upper_wedge (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) (e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hmem : e ∈ (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR) :
    WedgeIn ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).start
      ((monotoneLayoutDrawing w (n + 1) h).arc (⟨e, he⟩, false)).initialDirection
      (closedGraphRegion G.xmin
        (layoutPos w (n + 1) (kmswStage w n).nextVertex).re
        (fun x => if x ≤ G.xmax then G.lower x else
          (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x)
        (fun x => if x ≤ G.xmax then G.upper x else
          (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x))ᶜ := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  let p := Q.arc (⟨e, he⟩, false)
  have hd : 0 < p.initialDirection.re :=
    Polyline.initialDirection_re_pos (layoutArc_points_pairwise w (n + 1) e he)
      (layoutArc_length_two_le w (n + 1) e)
  have hgraph : ∀ z ∈ p.image, (fun x => if x ≤ G.xmax then G.upper x else
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x) z.re = z.im := by
    intro z hz
    have hzG : z ∈ graphOver G.xmin
        (layoutPos w (n + 1) (kmswStage w n).nextVertex).re
        (fun x => if x ≤ G.xmax then G.upper x else
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x) := by
      rw [invariant_succ_pen_upper_trace w n hc hUR G h]
      refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hmem, ?_⟩⟩
      simpa only [stageEdgeTrace, he, ↓reduceDIte] using hz
    exact hzG.2.2.symm
  obtain ⟨η, hη, hline⟩ := initial_line_east p (fun x => if x ≤ G.xmax then G.upper x else
      (layoutArc w (n + 1) (kmswStage w n).nextEdge).heightFn x)
    (Q.arc_length (⟨e, he⟩, false)) hd hgraph
  exact wedgeIn_compl_closedGraphRegion_east_upper p.start p.initialDirection η hd hη hline


private theorem pen_chart_data (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) :
    let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
    let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
    G.xmax ≤ q.re ∧ G.lower G.xmax = p.heightFn G.xmax ∧
      G.upper G.xmax = p.heightFn G.xmax ∧
      p.image = graphOver G.xmax q.re p.heightFn := by
  dsimp only
  let a : ℂ := layoutPos w n ((kmswStage w n).east (kmswStage w n).active)
  let q : ℂ := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let e : ℕ := (kmswStage w n).nextEdge
  let p : Polyline := layoutArc w (n + 1) e
  have hvalues := invariant_succ_pen_boundary_values w n hc hUR G
  change G.xmax = a.re ∧ G.lower a.re = a.im ∧ G.upper a.re = a.im at hvalues
  have hxmax : G.xmax = a.re := hvalues.1
  have hqpos := invariant_succ_pen_new_vertex_position w n hc hUR
  have hqre : q.re = G.xmax + 1 := by
    rw [hxmax]
    exact congrArg Complex.re hqpos
  have hmaxq : G.xmax ≤ q.re := by rw [hqre]; linarith
  have hpoints := invariant_succ_pen_new_edge_points w n hc hUR
  change layoutPos w (n + 1) ((kmswStage w (n + 1)).west e) = a ∧
      layoutPos w (n + 1) ((kmswStage w (n + 1)).east e) = q at hpoints
  have hstart : p.start = a := by
    dsimp [p, e]
    rw [layoutArc_start w (n + 1) _ (by
      rw [(invariant_succ_pen_counts w n hc hUR).1]
      omega)]
    exact hpoints.1
  have hpPair := layoutArc_points_pairwise w (n + 1) e (by
    dsimp [e]
    rw [(invariant_succ_pen_counts w n hc hUR).1]
    omega)
  have hstartHeight : p.heightFn a.re = a.im := by
    have hh := p.heightFn_point hpPair (k := 0) (by
      have := p.nonempty
      simp only [List.length_pos_iff.mpr this])
    rw [Polyline.point_zero_eq_start, hstart] at hh
    exact hh
  have hjoinLower : G.lower G.xmax = p.heightFn G.xmax := by
    rw [hxmax]
    exact hvalues.2.1.trans hstartHeight.symm
  have hjoinUpper : G.upper G.xmax = p.heightFn G.xmax := by
    rw [hxmax]
    exact hvalues.2.2.trans hstartHeight.symm
  have hArcGraph := invariant_succ_pen_arc_image_graph w n hc hUR
  change p.image = graphOver
    (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)).re
    (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)).re p.heightFn at hArcGraph
  rw [hpoints.1, hpoints.2] at hArcGraph
  rw [← hxmax] at hArcGraph
  have hArcGraph' : p.image = graphOver G.xmax q.re p.heightFn := by
    exact hArcGraph
  exact ⟨hmaxq, hjoinLower, hjoinUpper, hArcGraph'⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
noncomputable def invariant_succ_pen (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P)
    (h : LayoutGood w (n + 1)) :
    MonotoneStageInvariant w (n + 1) (monotoneLayoutDrawing w (n + 1) h) := by
  let Q := monotoneLayoutDrawing w (n + 1) h
  let q := layoutPos w (n + 1) (kmswStage w n).nextVertex
  let p := layoutArc w (n + 1) (kmswStage w n).nextEdge
  have htri := (invariant_succ_pen_stage_lists w n hc hUR).2.1
  let hLen := congrArg List.length htri
  let idx : Fin (kmswStage w (n + 1)).triangles.length →
      Fin (kmswStage w n).triangles.length := fun i => i.cast hLen
  have hidx : Function.Bijective idx := by
    constructor
    · intro i j hij
      exact Fin.ext (congrArg
        (fun k : Fin (kmswStage w n).triangles.length => k.val) hij)
    · intro i
      refine ⟨i.cast hLen.symm, ?_⟩
      exact Fin.ext rfl
  have ht : ∀ i, (kmswStage w (n + 1)).triangles.get i =
      (kmswStage w n).triangles.get (idx i) := by
    intro i
    simp only [List.get_eq_getElem, htri]
    rfl
  obtain ⟨hmaxq, hjoinL, hjoinU, hpgraph⟩ := pen_chart_data w n hc hUR G
  have hcaps : (⋃ i, closure (G.cap (idx i)).region) =
      ⋃ i, closure (G.cap i).region := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨idx i, hi⟩
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      obtain ⟨j, rfl⟩ := hidx.2 i
      exact mem_iUnion.mpr ⟨j, hi⟩
  refine
    { toMonotoneStageCertificate :=
        { xmin := G.xmin
          xmax := q.re
          hx := G.hx.trans hmaxq
          lower := fun x => if x ≤ G.xmax then G.lower x else p.heightFn x
          upper := fun x => if x ≤ G.xmax then G.upper x else p.heightFn x
          lower_continuous := (invariant_succ_pen_chart_continuous w n hc hUR G).1
          upper_continuous := (invariant_succ_pen_chart_continuous w n hc hUR G).2
          lower_le_upper := invariant_succ_pen_chart_order w n hc hUR G
          lower_trace := invariant_succ_pen_lower_trace w n hc hUR G h
          upper_trace := invariant_succ_pen_upper_trace w n hc hUR G h
          cap := fun i => G.cap (idx i)
          capLower := fun i => G.capLower (idx i)
          capUpper := fun i => G.capUpper (idx i)
          cap_lower_trace := ?_
          cap_upper_trace := ?_
          cap_edges := ?_
          cap_avoid := ?_
          cap_disjoint := ?_
          cover := ?_
          cap_lower_wedge := ?_
          cap_upper_wedge := ?_
          ext_upper_wedge := pen_ext_upper_wedge w n hc hUR G h
          ext_lower_wedge := pen_ext_lower_wedge w n hc hUR G h }
      cover_lower := ?_
      cover_upper := ?_
      upper_lipschitz_margin := invariant_succ_pen_upper_lipschitz_margin w n hc hUR G
      image_height_le := ?_
      pos_layout := invariant_succ_pen_pos_layout w n h
      arc_layout := invariant_succ_pen_arc_layout w n h }
  · intro i
    rw [G.cap_lower_trace]
    apply iUnion_congr
    intro e
    apply iUnion_congr
    intro he
    exact (invariant_succ_pen_old_edge_trace w n e hc hUR G h
      (cap_edge_lt w n G (idx i) e (List.mem_append.mpr (Or.inl he)))).symm
  · intro i
    rw [G.cap_upper_trace]
    apply iUnion_congr
    intro e
    apply iUnion_congr
    intro he
    exact (invariant_succ_pen_old_edge_trace w n e hc hUR G h
      (cap_edge_lt w n G (idx i) e (List.mem_append.mpr (Or.inr he)))).symm
  · intro i e
    rw [ht i]
    exact G.cap_edges (idx i) e
  · intro i
    rw [pen_drawing_image w n hc hUR G h]
    exact invariant_succ_pen_cap_avoid_union w n hc hUR G (idx i)
  · intro i j hij
    exact G.cap_disjoint (idx i) (idx j) (fun heq => hij (hidx.1 heq))
  · change Q.image ∪ (⋃ i, closure (G.cap (idx i)).region) =
      closedGraphRegion G.xmin q.re
        (fun x => if x ≤ G.xmax then G.lower x else p.heightFn x)
        (fun x => if x ≤ G.xmax then G.upper x else p.heightFn x)
    rw [closedGraphRegion_if_le_split G.hx hmaxq hjoinL hjoinU,
      ← hpgraph, hcaps, ← G.cover, pen_drawing_image w n hc hUR G h]
    ext z
    simp only [Set.mem_union]
    tauto
  · intro i e he hmem
    have heOld := cap_edge_lt w n G (idx i) e (List.mem_append.mpr (Or.inl hmem))
    rw [pen_old_arc w n G h e heOld he false]
    exact G.cap_lower_wedge (idx i) e heOld hmem
  · intro i e he hmem
    have heOld := cap_edge_lt w n G (idx i) e (List.mem_append.mpr (Or.inr hmem))
    rw [pen_old_arc w n G h e heOld he true]
    exact G.cap_upper_wedge (idx i) e heOld hmem
  · intro e
    rcases invariant_succ_pen_cover_lower w n hc hUR G e with he | ⟨i, hi⟩
    · exact Or.inl he
    · obtain ⟨j, rfl⟩ := hidx.2 i
      exact Or.inr ⟨j, hi⟩
  · intro e
    rcases invariant_succ_pen_cover_upper w n hc hUR G e with he | ⟨i, hi⟩
    · exact Or.inl he
    · obtain ⟨j, rfl⟩ := hidx.2 i
      exact Or.inr ⟨j, hi⟩
  · simpa only [Nat.cast_add, Nat.cast_one] using pen_image_height_le w n hc hUR G h

end DirectedDistances.KMSW
