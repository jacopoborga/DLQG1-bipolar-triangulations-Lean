module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.GraphRegion
public import DirectedDistances.PlanarMap.MonotonePolyline
import DirectedDistances.PlanarMap.RoofPolyline

/-! # Infinite ray strips

Helpers toward Lemma 4.6 (lem-geo-exist); not a paper result. Source context: -/

public section
namespace DirectedDistances.PlanarMap

open Set
open Filter
open scoped Topology

/-- Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] def pathTrace {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (G : PLDrawing D V flip rot vert) (es : ℕ → D) : Set ℂ :=
  ⋃ i, (G.arc (es i)).image

/-- Finite initial portion of a path trace, indexed by `i < n`.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] def pathTracePrefix {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (G : PLDrawing D V flip rot vert) (es : ℕ → D) (n : ℕ) : Set ℂ :=
  {z | ∃ i, i < n ∧ z ∈ (G.arc (es i)).image}

/-- Prefix traces increase with the prefix length.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem pathTracePrefix_mono {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (G : PLDrawing D V flip rot vert) (es : ℕ → D)
    {m n : ℕ} (hmn : m ≤ n) : pathTracePrefix G es m ⊆ pathTracePrefix G es n := by
  rintro z ⟨i, hi, hz⟩
  exact ⟨i, lt_of_lt_of_le hi hmn, hz⟩

/-- Every finite prefix is contained in the full trace.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem pathTracePrefix_subset {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (G : PLDrawing D V flip rot vert) (es : ℕ → D) (n : ℕ) :
    pathTracePrefix G es n ⊆ pathTrace G es := by
  rintro z ⟨i, _, hz⟩
  exact mem_iUnion.mpr ⟨i, hz⟩

/-- Closed region above the starting abscissa and between two ray heights.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] def closedRayStrip (x₀ : ℝ) (lo hi : ℝ → ℝ) : Set ℂ :=
  {z | x₀ ≤ z.re ∧ lo z.re ≤ z.im ∧ z.im ≤ hi z.re}

/-- A set is the graph of `h` on the closed half-line from `x₀`.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] def IsGraphRay (S : Set ℂ) (x₀ : ℝ) (h : ℝ → ℝ) : Prop :=
  S = {z | x₀ ≤ z.re ∧ z.im = h z.re}

/-- The graph of a continuous function on `[x₀, ∞)` is closed.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem isClosed_graphRay {x₀ : ℝ} {h : ℝ → ℝ} (hh : Continuous h) :
    IsClosed {z : ℂ | x₀ ≤ z.re ∧ z.im = h z.re} := by
  have hx : IsClosed {z : ℂ | x₀ ≤ z.re} := isClosed_Ici.preimage Complex.continuous_re
  let f : ℂ → ℝ := fun z => z.im - h z.re
  have hf : Continuous f := Complex.continuous_im.sub (hh.comp Complex.continuous_re)
  have he : IsClosed {z : ℂ | z.im = h z.re} := by
    have hpre : IsClosed (f ⁻¹' ({0} : Set ℝ)) :=
      isClosed_singleton.preimage hf
    convert hpre using 1
    ext z
    simp [f, sub_eq_zero]
  change IsClosed ({z : ℂ | x₀ ≤ z.re} ∩ {z | z.im = h z.re})
  exact hx.inter he

/-- The region between two ordered graph rays contains both boundary rays.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem graphRays_subset_closedRayStrip {S T : Set ℂ} {x₀ : ℝ} {lo hi : ℝ → ℝ}
    (hlo : IsGraphRay S x₀ lo) (hhi : IsGraphRay T x₀ hi)
    (hle : ∀ x, lo x ≤ hi x) : S ∪ T ⊆ closedRayStrip x₀ lo hi := by
  rw [hlo, hhi]
  rintro z (⟨hx, hz⟩ | ⟨hx, hz⟩)
  · exact ⟨hx, le_of_eq hz.symm, (le_of_eq hz).trans (hle z.re)⟩
  · exact ⟨hx, (hle z.re).trans (le_of_eq hz.symm), le_of_eq hz⟩

/-- Closedness of a strip with continuous boundary heights.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem isClosed_closedRayStrip {x₀ : ℝ} {lo hi : ℝ → ℝ}
    (hlo : Continuous lo) (hhi : Continuous hi) :
    IsClosed (closedRayStrip x₀ lo hi) := by
  have hx : IsClosed {z : ℂ | x₀ ≤ z.re} := isClosed_Ici.preimage Complex.continuous_re
  have hl : IsClosed {z : ℂ | lo z.re ≤ z.im} := by
    have hc : Continuous (fun z : ℂ => z.im - lo z.re) :=
      Complex.continuous_im.sub (hlo.comp Complex.continuous_re)
    have hpre : IsClosed ((fun z : ℂ => z.im - lo z.re) ⁻¹' Set.Ici 0) :=
      isClosed_Ici.preimage hc
    convert hpre using 1
    ext z
    simp [sub_nonneg]
  have hh : IsClosed {z : ℂ | z.im ≤ hi z.re} := by
    have hc : Continuous (fun z : ℂ => z.im - hi z.re) :=
      Complex.continuous_im.sub (hhi.comp Complex.continuous_re)
    have hpre : IsClosed ((fun z : ℂ => z.im - hi z.re) ⁻¹' Set.Iic 0) :=
      isClosed_Iic.preimage hc
    convert hpre using 1
    ext z
    simp
  change IsClosed ({z : ℂ | x₀ ≤ z.re} ∩
    ({z | lo z.re ≤ z.im} ∩ {z | z.im ≤ hi z.re}))
  exact hx.inter (hl.inter hh)

/-- On a third graph ray, strip membership is exactly the pair of height bounds.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem mem_closedRayStrip_iff_graphHeight_bounds {S : Set ℂ} {x₀ : ℝ}
    {lo hi h' : ℝ → ℝ} {z : ℂ} (hray : IsGraphRay S x₀ h') (hz : z ∈ S) :
    z ∈ closedRayStrip x₀ lo hi ↔ lo z.re ≤ h' z.re ∧ h' z.re ≤ hi z.re := by
  rw [hray] at hz
  rcases hz with ⟨hx, hgraph⟩
  constructor
  · rintro ⟨_, hlo, hhi⟩
    exact ⟨by simpa [hgraph] using hlo, by simpa [hgraph] using hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨hx, by simpa [hgraph] using hlo, by simpa [hgraph] using hhi⟩

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
      obtain ⟨hl, hr, hh⟩ := (p.segmentAt_iff_heightFn hp hi).mp hseg
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
        p.exists_segment_covering hlen hlo hr
      apply Or.inr
      refine ⟨i, hi, ?_⟩
      exact (p.segmentAt_iff_heightFn hp hi).mpr ⟨hiL, hiR, hh⟩

end Polyline

/-- The first arc whose finish is at or to the right of `x`.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] noncomputable def pathTraceRayIndex {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) (es : ℕ → D)
    (hstep : ∀ i, (G.arc (es i)).start.re < (G.arc (es i)).finish.re)
    (htend : Tendsto (fun i => (G.arc (es i)).start.re) atTop atTop)
    (x : ℝ) : ℕ :=
  Nat.find (show ∃ i, x ≤ (G.arc (es i)).finish.re from by
    have hevent : ∀ᶠ i : ℕ in atTop, x < (G.arc (es i)).start.re :=
      htend.eventually (eventually_gt_atTop x)
    obtain ⟨i, hi⟩ := hevent.exists
    exact ⟨i, (lt_trans hi (hstep i)).le⟩)

/-- The height on the first arc reaching `x`.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] noncomputable def pathTraceRayHeight {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) (es : ℕ → D)
    (hstep : ∀ i, (G.arc (es i)).start.re < (G.arc (es i)).finish.re)
    (htend : Tendsto (fun i => (G.arc (es i)).start.re) atTop atTop)
    (x : ℝ) : ℝ :=
  (G.arc (es (pathTraceRayIndex G es hstep htend x))).heightFn x

/-- Consecutive x-monotone arcs with matching endpoints form the graph of their
first-finish height function.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem isGraphRay_pathTrace_of_xMonotone {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V}
    (G : PLDrawing D V flip rot vert) (es : ℕ → D)
    (hmono : ∀ i, (G.arc (es i)).XMonotone)
    (hseam : ∀ i, (G.arc (es i)).finish = (G.arc (es (i + 1))).start)
    (hstep : ∀ i, (G.arc (es i)).start.re < (G.arc (es i)).finish.re)
    (htend : Tendsto (fun i => (G.arc (es i)).start.re) atTop atTop) :
    IsGraphRay (pathTrace G es) (G.arc (es 0)).start.re
      (pathTraceRayHeight G es hstep htend) := by
  let p : ℕ → Polyline := fun i => G.arc (es i)
  have hstartStep (i : ℕ) : (p i).start.re < (p (i + 1)).start.re := by
    rw [← hseam i]
    exact hstep i
  have hstartMono : Monotone (fun i : ℕ => (p i).start.re) := by
    intro i j hij
    induction j with
    | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact le_rfl
    | succ j ih =>
      by_cases hij' : i ≤ j
      · exact (ih hij').trans (hstartStep j).le
      · have hEq : i = j + 1 := by omega
        rw [hEq]
  have hfinishExists (x : ℝ) :
      ∃ i, x ≤ (p i).finish.re := by
    have hevent : ∀ᶠ i : ℕ in atTop, x < (p i).start.re :=
      htend.eventually (eventually_gt_atTop x)
    obtain ⟨i, hi⟩ := hevent.exists
    exact ⟨i, (lt_trans hi (hstep i)).le⟩
  have hIndexSpec (x : ℝ) :
      x ≤ (p (pathTraceRayIndex G es hstep htend x)).finish.re := by
    exact Nat.find_spec (hfinishExists x)
  have hIndexMin (x : ℝ) (i : ℕ)
      (hi : i < pathTraceRayIndex G es hstep htend x) :
      ¬ x ≤ (p i).finish.re := by
    exact Nat.find_min (hfinishExists x) hi
  have hHeightAgreement (k i : ℕ) (x : ℝ)
      (hki : k ≤ i) (hxk : x ≤ (p k).finish.re)
      (hxi : (p i).start.re ≤ x) :
      (p k).heightFn x = (p i).heightFn x := by
    rcases eq_or_lt_of_le hki with rfl | hki
    · rfl
    · have hk1 : k + 1 ≤ i := Nat.succ_le_of_lt hki
      have hsk1 : (p (k + 1)).start.re ≤ x :=
        (hstartMono hk1).trans hxi
      have hfinishStart : (p k).finish.re = (p (k + 1)).start.re :=
        congrArg Complex.re (hseam k)
      have hEqX : x = (p k).finish.re := le_antisymm hxk
        (hfinishStart ▸ hsk1)
      have hEqI : i = k + 1 := by
        by_contra hne
        have hlt : k + 1 < i := by omega
        have hslt := hstartStep (k + 1)
        have hsklt : (p (k + 1)).start.re < (p i).start.re := by
          exact lt_of_lt_of_le hslt (hstartMono (Nat.succ_le_of_lt hlt))
        have : (p i).start.re ≤ (p (k + 1)).start.re := by
          rw [← hfinishStart, ← hEqX]
          exact hxi
        exact (not_le_of_gt hsklt) this
      subst i
      have hlenK : 2 ≤ (p k).points.length := G.arc_length (es k)
      have hlenNext : 2 ≤ (p (k + 1)).points.length := G.arc_length (es (k + 1))
      have hlastK : (p k).point ((p k).points.length - 1) = (p k).finish :=
        (p k).point_last_eq_finish
      have hp0Next : (p (k + 1)).point 0 = (p (k + 1)).start :=
        (p (k + 1)).point_zero_eq_start
      rw [hEqX]
      calc
        (p k).heightFn (p k).finish.re = (p k).finish.im := by
          rw [← hlastK]
          exact (p k).heightFn_point (hmono k) (by omega)
        _ = (p (k + 1)).start.im := congrArg Complex.im (hseam k)
        _ = (p (k + 1)).heightFn (p (k + 1)).start.re := by
          rw [← hp0Next]
          exact ((p (k + 1)).heightFn_point (hmono (k + 1)) (by omega)).symm
        _ = (p (k + 1)).heightFn (p k).finish.re :=
          congrArg (p (k + 1)).heightFn hfinishStart.symm
  unfold IsGraphRay
  apply Set.ext
  intro z
  constructor
  · intro hz
    simp only [pathTrace, mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    rw [Polyline.image_eq_heightFn_graph (hmono i) (G.arc_length (es i))] at hzi
    obtain ⟨hl, hr, him⟩ := hzi
    let k := pathTraceRayIndex G es hstep htend z.re
    have hkSpec : z.re ≤ (p k).finish.re := hIndexSpec z.re
    have hki : k ≤ i := by
      dsimp [k]
      exact Nat.find_min' (hfinishExists z.re) hr
    have hstart : (p 0).start.re ≤ z.re :=
      (hstartMono (Nat.zero_le i)).trans hl
    have hheight : (p k).heightFn z.re = (p i).heightFn z.re :=
      hHeightAgreement k i z.re hki hkSpec hl
    exact ⟨hstart, him.trans hheight.symm⟩
  · rintro ⟨hx, him⟩
    let k := pathTraceRayIndex G es hstep htend z.re
    have hkSpec : z.re ≤ (p k).finish.re := hIndexSpec z.re
    have hkStart : (p k).start.re ≤ z.re := by
      by_cases hk0 : k = 0
      · simpa [hk0] using hx
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hprevNot : ¬ z.re ≤ (p (k - 1)).finish.re := by
          apply hIndexMin z.re (k - 1)
          omega
        have hprev : (p (k - 1)).finish.re < z.re := lt_of_not_ge hprevNot
        have hseamPrev : (p (k - 1)).finish.re = (p k).start.re := by
          have hseam' := congrArg Complex.re (hseam (k - 1))
          rwa [Nat.sub_add_cancel hkpos] at hseam'
        rw [← hseamPrev]
        exact hprev.le
    have hmem : z ∈ (p k).image := by
      rw [Polyline.image_eq_heightFn_graph (hmono k) (G.arc_length (es k))]
      exact ⟨hkStart, hkSpec, him⟩
    simp only [pathTrace, mem_iUnion]
    exact ⟨k, hmem⟩

end DirectedDistances.PlanarMap
