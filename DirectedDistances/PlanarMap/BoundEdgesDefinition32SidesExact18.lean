/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact17
public import DirectedDistances.PlanarMap.LeftAtOnPolygonalReturn
import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen3
import DirectedDistances.PlanarMap.D39PLOrientedPlaneHomeomorph
import Mathlib.Topology.TietzeExtension

/-! # Local loop erasure toward Definition 3.2

These geometric helpers address simplification of a polygonal return. They
do not identify a continuous return with an arbitrary simple replacement. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

namespace Polyline

/-- Helper toward Definition 3.2: a polyline with distinct endpoints contains
a simple polyline with the same endpoints and no more vertices. No openness
or connectedness premise is needed for this finite loop erasure. -/
theorem exists_simple_subimage32 (p₀ : Polyline) (hne : p₀.start ≠ p₀.finish) :
    ∃ p : Polyline, p.IsSimple ∧ p.start = p₀.start ∧ p.finish = p₀.finish ∧
      p.image ⊆ p₀.image ∧ 2 ≤ p.points.length ∧
      p.points.length ≤ p₀.points.length := by
  classical
  let P : ℕ → Prop := fun n => ∃ p : Polyline,
    p.start = p₀.start ∧ p.finish = p₀.finish ∧ p.image ⊆ p₀.image ∧
      p.points.length = n
  have hP : ∃ n, P n := ⟨p₀.points.length, p₀, rfl, rfl, Subset.rfl, rfl⟩
  let n := Nat.find hP
  obtain ⟨p, hps, hpf, hpim, hlen⟩ := Nat.find_spec hP
  have hmin (q : Polyline) (hqs : q.start = p₀.start)
      (hqf : q.finish = p₀.finish) (hqim : q.image ⊆ p₀.image) :
      n ≤ q.points.length := Nat.find_min' hP ⟨q, hqs, hqf, hqim, rfl⟩
  have hlen2 : 2 ≤ p.points.length := by
    have hstartne : p.start ≠ p.finish := fun heq => hne (hps.symm.trans (heq.trans hpf))
    have hsingle : p.points.length = 1 → p.start = p.finish := by
      intro h
      rcases p with ⟨l, hn⟩
      cases l with
      | nil => simp at h
      | cons a l =>
        cases l with
        | nil => rfl
        | cons b l => simp at h
    have hpos : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    by_contra hlt
    exact hstartne (hsingle (by omega))
  have hvertices := minimal_polyline_vertices_injective p n hps hpf hpim hlen hmin
  have hfirst : ∀ i, i + 1 < p.points.length → p.point i ≠ p.point (i + 1) := by
    intro i hi heq
    have := hvertices i (i + 1) (by omega) (by omega) heq
    omega
  have hadjacent : ∀ i, i + 2 < p.points.length →
      p.segmentAt i ∩ p.segmentAt (i + 1) = {p.point (i + 1)} := by
    intro i hi
    apply Subset.antisymm
    · intro z hz
      simp only [mem_singleton_iff]
      by_contra hzb
      have hreplacement : segment ℝ (p.point i) (p.point (i + 2)) ⊆
          p.segmentAt i ∪ p.segmentAt (i + 1) := by
        apply segment_subset_adjacent_union_of_mem_inter
          (p.point i) (p.point (i + 1)) (p.point (i + 2)) z
        · exact hz.1
        · exact hz.2
        · exact hzb
      obtain ⟨q, hqs, hqf, hqim, hqlen⟩ :=
        exists_polyline_delete_interior_point p i hi hreplacement
      have hleast := hmin q (hqs.trans hps) (hqf.trans hpf) (hqim.trans hpim)
      rw [hlen] at hqlen
      omega
    · intro z hz
      rw [mem_singleton_iff] at hz
      subst z
      exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  have hseparated : ∀ i j, i + 1 < p.points.length → j + 1 < p.points.length →
      i + 1 < j → Disjoint (p.segmentAt i) (p.segmentAt j) := by
    intro i j hi hj hij
    apply disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨q, hqs, hqf, hqim, hqlen⟩ :=
      exists_shorter_polyline_of_nonadjacent_segment_intersection
        p i j hi hj hij z hzi hzj
    have hleast := hmin q (hqs.trans hps) (hqf.trans hpf) (hqim.trans hpim)
    rw [hlen] at hqlen
    omega
  refine ⟨p, ⟨hfirst, hadjacent, hseparated⟩, hps, hpf, hpim, hlen2, ?_⟩
  rw [hlen]
  exact hmin p₀ rfl rfl Subset.rfl

end Polyline

/-- Helper toward Definition 3.2: a path in an open disk has a canonical
logarithmic increment about every point outside that disk. The formula
depends only on its endpoints, including when the viewpoint is on the
boundary circle. -/
theorem hasLiftIncrement_of_range_subset_ball32 {x y : ℂ}
    (q : Path x y) (c w : ℂ) (r : ℝ)
    (hq : Set.range q ⊆ ball c r) (hw : r ≤ dist c w) :
    HasLiftIncrement q w
      (Complex.log ((y - w) / (c - w)) - Complex.log ((x - w) / (c - w))) := by
  have hbound (t : I) : ‖q t - c‖ < ‖c - w‖ := by
    have hqt : ‖q t - c‖ < r := by
      simpa only [mem_ball, dist_eq_norm] using hq (mem_range_self t)
    exact hqt.trans_le (by simpa only [dist_eq_norm] using hw)
  have hden : c - w ≠ 0 := by
    apply norm_pos_iff.mp
    exact (norm_nonneg _).trans_lt (hbound 0)
  have hratio (t : I) : (q t - w) / (c - w) - 1 = (q t - c) / (c - w) := by
    field_simp [hden]
    ring
  have hslit (t : I) : (q t - w) / (c - w) ∈ Complex.slitPlane := by
    apply Complex.ball_one_subset_slitPlane
    rw [mem_ball, dist_eq_norm, hratio, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hden)).mpr (hbound t)
  let φ : C(I, ℂ) :=
    ⟨fun t => Complex.log (c - w) + Complex.log ((q t - w) / (c - w)),
      continuous_const.add
        (((q.continuous.sub continuous_const).div_const _).clog hslit)⟩
  refine ⟨φ, ?_, ?_⟩
  · intro t
    change Complex.exp (Complex.log (c - w) + Complex.log ((q t - w) / (c - w))) = _
    rw [Complex.exp_add, Complex.exp_log hden,
      Complex.exp_log (Complex.slitPlane_ne_zero (hslit t))]
    field_simp [hden]
  · change (Complex.log (c - w) + Complex.log ((q 1 - w) / (c - w))) -
      (Complex.log (c - w) + Complex.log ((q 0 - w) / (c - w))) = _
    rw [q.source, q.target]
    ring

/-- Helper toward Definition 3.2: any two paths in the same disk with the
same endpoints have exactly the same logarithmic lift increments about
every point outside that disk. -/
theorem hasLiftIncrement_iff_of_range_subset_ball32 {x y : ℂ}
    (q q' : Path x y) (c w : ℂ) (r : ℝ)
    (hq : Set.range q ⊆ ball c r) (hq' : Set.range q' ⊆ ball c r)
    (hw : r ≤ dist c w) (v : ℂ) :
    HasLiftIncrement q w v ↔ HasLiftIncrement q' w v := by
  have h := hasLiftIncrement_of_range_subset_ball32 q c w r hq hw
  have h' := hasLiftIncrement_of_range_subset_ball32 q' c w r hq' hw
  constructor
  · intro hv
    exact (hasLiftIncrement_unique32 h hv) ▸ h'
  · intro hv
    exact (hasLiftIncrement_unique32 h' hv) ▸ h

/-- Helper toward Definition 3.2: a continuous logarithm on a set determines
the lift increment of every path in that set solely from its endpoints. -/
theorem hasLiftIncrement_of_log_on_set32 {U : Set ℂ} (f : C(U, ℂ)) (w : ℂ)
    (hf : ∀ z : U, Complex.exp (f z) = z.val - w)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) (q : Path x y)
    (hq : Set.range q ⊆ U) :
    HasLiftIncrement q w (f ⟨y, hy⟩ - f ⟨x, hx⟩) := by
  let qU : C(I, U) := ⟨fun t => ⟨q t, hq (mem_range_self t)⟩,
    q.continuous.subtype_mk _⟩
  refine ⟨f.comp qU, fun t => hf (qU t), ?_⟩
  change f (qU 1) - f (qU 0) = _
  have h0 : qU 0 = ⟨x, hx⟩ := Subtype.ext q.source
  have h1 : qU 1 = ⟨y, hy⟩ := Subtype.ext q.target
  rw [h0, h1]

/-- Helper toward Definition 3.2: an injective continuous arc avoiding a
point has an open neighborhood carrying a continuous logarithm about that
point. Tietze extension is applied separately to the real and imaginary
parts of its lift; the slit-plane correction makes the extension exact. -/
theorem exists_log_neighborhood_of_injective_path32 {x y : ℂ}
    (q : Path x y) (hqi : Function.Injective q) (w : ℂ)
    (hw : w ∉ Set.range q) :
    ∃ U : Set ℂ, IsOpen U ∧ Set.range q ⊆ U ∧
      ∃ f : C(U, ℂ), ∀ z : U, Complex.exp (f z) = z.val - w := by
  obtain ⟨v, φ, hφ, _⟩ := exists_hasLiftIncrement32 q w hw
  have hclosed := q.continuous.isClosedEmbedding hqi
  let φre : C(I, ℝ) := ⟨fun t => (φ t).re, by fun_prop⟩
  let φim : C(I, ℝ) := ⟨fun t => (φ t).im, by fun_prop⟩
  obtain ⟨fre, hfre⟩ := φre.exists_extension' hclosed
  obtain ⟨fim, hfim⟩ := φim.exists_extension' hclosed
  let ψ : C(ℂ, ℂ) := ⟨fun z => (fre z : ℂ) + (fim z : ℂ) * Complex.I, by fun_prop⟩
  have hψ (t : I) : ψ (q t) = φ t := by
    apply Complex.ext
    · simpa only [ψ, ContinuousMap.coe_mk, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_self, add_zero, Function.comp_apply, φre,
        ContinuousMap.coe_mk] using congrFun hfre t
    · simpa only [ψ, ContinuousMap.coe_mk, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, zero_mul, add_zero, zero_add, Function.comp_apply, φim,
        ContinuousMap.coe_mk] using congrFun hfim t
  let R : ℂ → ℂ := fun z => (z - w) / Complex.exp (ψ z)
  have hRc : Continuous R := by
    exact (continuous_id.sub continuous_const).div
      (Complex.continuous_exp.comp ψ.continuous) (fun z => Complex.exp_ne_zero _)
  let U : Set ℂ := R ⁻¹' Complex.slitPlane
  have hU : IsOpen U := Complex.isOpen_slitPlane.preimage hRc
  have hqU : Set.range q ⊆ U := by
    rintro z ⟨t, rfl⟩
    change (q t - w) / Complex.exp (ψ (q t)) ∈ Complex.slitPlane
    rw [hψ, hφ, div_self (by rw [← hφ]; exact Complex.exp_ne_zero _)]
    exact Complex.one_mem_slitPlane
  let f : C(U, ℂ) := ⟨fun z => ψ z + Complex.log (R z),
    (ψ.continuous.comp continuous_subtype_val).add
      ((hRc.comp continuous_subtype_val).clog (fun z => z.2))⟩
  refine ⟨U, hU, hqU, f, ?_⟩
  intro z
  change Complex.exp (ψ z + Complex.log (R z)) = z.val - w
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero z.2)]
  dsimp [R]
  exact mul_div_cancel₀ _ (Complex.exp_ne_zero _)

/-- Helper toward Definition 3.2: an injective continuous path has a simple
polygonal replacement preserving every lift increment about a prescribed
point off the path. The replacement lies in the same logarithm neighborhood;
this asserts neither face containment nor intersection control with a
separate closing arc. -/
theorem exists_simple_polyline_same_liftIncrement_in_open32 {x y : ℂ}
    (q : Path x y) (hqi : Function.Injective q) (w : ℂ)
    (hw : w ∉ Set.range q) (O : Set ℂ) (hO : IsOpen O)
    (hqO : Set.range q ⊆ O) :
    ∃ p : Polyline, p.IsSimple ∧ ∃ (hs : x = p.start) (ht : y = p.finish),
      2 ≤ p.points.length ∧ p.image ⊆ O ∧ ∀ v : ℂ,
        (HasLiftIncrement q w v ↔ HasLiftIncrement (p.toPath.cast hs ht) w v) := by
  have hxy : x ≠ y := by
    intro h
    have h01 : (0 : I) = 1 := hqi (q.source.trans (h.trans q.target.symm))
    exact zero_ne_one h01
  obtain ⟨U, hU, hqU, f, hf⟩ := exists_log_neighborhood_of_injective_path32 q hqi w hw
  let W := U ∩ O
  have hW : IsOpen W := hU.inter hO
  have hqW : Set.range q ⊆ W := fun z hz => ⟨hqU hz, hqO hz⟩
  obtain ⟨n, p₀, hps, hpt, _, hpU, _⟩ :=
    exists_polygonal_approx_homotopy_in_open32 q hW hqW (show (0 : ℝ) < 1 by norm_num)
  have hpne : p₀.start ≠ p₀.finish := fun h => hxy (hps.symm.trans (h.trans hpt))
  obtain ⟨p, hsimple, hs, ht, hpim, hlen, _⟩ := p₀.exists_simple_subimage32 hpne
  have hxU : x ∈ U := hqU ⟨0, q.source⟩
  have hyU : y ∈ U := hqU ⟨1, q.target⟩
  let hs' : x = p.start := (hs.trans hps).symm
  let ht' : y = p.finish := (ht.trans hpt).symm
  have hpU' : Set.range (p.toPath.cast hs' ht') ⊆ U := by
    rintro z ⟨t, rfl⟩
    apply inter_subset_left.trans' hpU
    apply hpim
    rw [← p.range_toPath]
    exact mem_range_self t
  have hqlog := hasLiftIncrement_of_log_on_set32 f w hf hxU hyU q hqU
  have hplog := hasLiftIncrement_of_log_on_set32 f w hf hxU hyU
    (p.toPath.cast hs' ht') hpU'
  have hpO : p.image ⊆ O := hpim.trans (hpU.trans inter_subset_right)
  refine ⟨p, hsimple, hs', ht', hlen, hpO, fun v => ?_⟩
  constructor
  · intro hv
    exact (hasLiftIncrement_unique32 hqlog hv) ▸ hplog
  · intro hv
    exact (hasLiftIncrement_unique32 hplog hv) ▸ hqlog

/-- Helper toward Definition 3.2: a simple polygonal return in any prescribed
open neighborhood of an injective continuous return can preserve exactly
the winding of the whole closed traversal about a prescribed viewpoint.
The same replacement works for every winding integer at that viewpoint. -/
theorem exists_simple_polyline_return_same_winding_in_open32 {x y : ℂ}
    (α : Path x y) (q : Path y x) (hqi : Function.Injective q) (w : ℂ)
    (hw : w ∉ Set.range q) (O : Set ℂ) (hO : IsOpen O)
    (hqO : Set.range q ⊆ O) :
    ∃ p : Polyline, p.IsSimple ∧ ∃ (hs : y = p.start) (ht : x = p.finish),
      2 ≤ p.points.length ∧ p.image ⊆ O ∧ ∀ n : ℤ,
        (HasWinding (α.trans q) w n ↔
          HasWinding (α.trans (p.toPath.cast hs ht)) w n) := by
  obtain ⟨p, hp, hs, ht, hlen, hpO, hlift⟩ :=
    exists_simple_polyline_same_liftIncrement_in_open32 q hqi w hw O hO hqO
  refine ⟨p, hp, hs, ht, hlen, hpO, fun n => ?_⟩
  change HasLiftIncrement (α.trans q) w (2 * Real.pi * Complex.I * (n : ℤ)) ↔
    HasLiftIncrement (α.trans (p.toPath.cast hs ht)) w
      (2 * Real.pi * Complex.I * (n : ℤ))
  rw [hasLiftIncrement_trans_iff, hasLiftIncrement_trans_iff]
  simp only [hlift]

/-- Helper toward Definition 3.2: one simple polygonal replacement preserves
the winding about every viewpoint in a whole disk separated from the return.
Its image remains in any prescribed open neighborhood of the entire return.
In particular the replacement need not depend on the accumulating viewpoint. -/
theorem exists_simple_polyline_return_same_winding_near_in_open32 {x y z : ℂ}
    (α : Path x y) (q : Path y x) (hqi : Function.Injective q)
    (hz : z ∉ Set.range q) (O : Set ℂ) (hO : IsOpen O)
    (hqO : Set.range q ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ ∃ p : Polyline, p.IsSimple ∧
      ∃ (hs : y = p.start) (ht : x = p.finish),
        2 ≤ p.points.length ∧ p.image ⊆ O ∧
        ∀ w : ℂ, w ∈ ball z r → ∀ n : ℤ,
          (HasWinding (α.trans q) w n ↔
            HasWinding (α.trans (p.toPath.cast hs ht)) w n) := by
  obtain ⟨U, hU, hqU, f, hf⟩ := exists_log_neighborhood_of_injective_path32 q hqi z hz
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp
    (isCompact_range q.continuous).isClosed.isOpen_compl z hz
  let W := (U ∩ O) ∩ (closedBall z (R / 2))ᶜ
  have hW : IsOpen W := (hU.inter hO).inter isClosed_closedBall.isOpen_compl
  have hqW : Set.range q ⊆ W := by
    intro v hv
    refine ⟨⟨hqU hv, hqO hv⟩, ?_⟩
    intro hvball
    have hvR : v ∈ ball z R :=
      (mem_closedBall.mp hvball).trans_lt (half_lt_self hR)
    exact hball hvR hv
  obtain ⟨p, hp, hs, ht, hlen, hpW, _⟩ :=
    exists_simple_polyline_same_liftIncrement_in_open32 q hqi z hz W hW hqW
  have hpO : p.image ⊆ O := fun v hv => (hpW hv).1.2
  have hyW : y ∈ W := hqW ⟨0, q.source⟩
  have hxW : x ∈ W := hqW ⟨1, q.target⟩
  have hpW' : Set.range (p.toPath.cast hs ht) ⊆ W := by
    rintro v ⟨t, rfl⟩
    apply hpW
    rw [← p.range_toPath]
    exact mem_range_self t
  refine ⟨R / 2, half_pos hR, p, hp, hs, ht, hlen, hpO, ?_⟩
  intro w hw n
  have hden (v : W) : v.val - z ≠ 0 := by
    have hdist : R / 2 < dist v.val z := lt_of_not_ge v.2.2
    exact norm_pos_iff.mp ((half_pos hR).trans
      (by simpa only [dist_eq_norm] using hdist))
  have hratio (v : W) :
      (v.val - w) / (v.val - z) - 1 = (z - w) / (v.val - z) := by
    field_simp [hden v]
    ring
  have hslit (v : W) : (v.val - w) / (v.val - z) ∈ Complex.slitPlane := by
    apply Complex.ball_one_subset_slitPlane
    rw [mem_ball, dist_eq_norm, hratio, norm_div]
    apply (div_lt_one (norm_pos_iff.mpr (hden v))).mpr
    have hw' : ‖z - w‖ < R / 2 := by
      simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
    have hv' : R / 2 < ‖v.val - z‖ := by
      simpa only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] using v.2.2
    exact hw'.trans hv'
  let fW : C(W, ℂ) := f.comp ⟨fun v => ⟨v.val, v.2.1.1⟩, by fun_prop⟩
  let fw : C(W, ℂ) := ⟨fun v => fW v + Complex.log ((v.val - w) / (v.val - z)),
    fW.continuous.add (((continuous_subtype_val.sub continuous_const).div
      (continuous_subtype_val.sub continuous_const) hden).clog hslit)⟩
  have hfw (v : W) : Complex.exp (fw v) = v.val - w := by
    change Complex.exp (fW v + Complex.log ((v.val - w) / (v.val - z))) = _
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hslit v))]
    have hfW : Complex.exp (fW v) = v.val - z := hf ⟨v.val, v.2.1.1⟩
    rw [hfW]
    exact mul_div_cancel₀ _ (hden v)
  have hqlog := hasLiftIncrement_of_log_on_set32 fw w hfw hyW hxW q hqW
  have hplog := hasLiftIncrement_of_log_on_set32 fw w hfw hyW hxW
    (p.toPath.cast hs ht) hpW'
  have hlift (v : ℂ) :
      HasLiftIncrement q w v ↔ HasLiftIncrement (p.toPath.cast hs ht) w v := by
    constructor
    · intro hv
      exact (hasLiftIncrement_unique32 hqlog hv) ▸ hplog
    · intro hv
      exact (hasLiftIncrement_unique32 hplog hv) ▸ hqlog
  change HasLiftIncrement (α.trans q) w (2 * Real.pi * Complex.I * (n : ℤ)) ↔
    HasLiftIncrement (α.trans (p.toPath.cast hs ht)) w
      (2 * Real.pi * Complex.I * (n : ℤ))
  rw [hasLiftIncrement_trans_iff, hasLiftIncrement_trans_iff]
  simp only [hlift]

/-- Helper toward Definition 3.2: one simple polygonal return preserves all
signed winding accumulation tests at a point off the original injective
return, in every observation set. The replacement stays in the prescribed
open neighborhood, including its two endpoints. -/
theorem exists_simple_polyline_return_preserves_winding_accumulation_in_open32
    {x y z : ℂ} (α : Path x y) (q : Path y x) (hqi : Function.Injective q)
    (hz : z ∉ Set.range q) (O : Set ℂ) (hO : IsOpen O)
    (hqO : Set.range q ⊆ O) :
    ∃ p : Polyline, p.IsSimple ∧ ∃ (hs : y = p.start) (ht : x = p.finish),
      2 ≤ p.points.length ∧ p.image ⊆ O ∧ ∀ A : Set ℂ, ∀ n : ℤ,
        (z ∈ closure {w : ℂ | w ∈ A ∧ HasWinding (α.trans q) w n} ↔
          z ∈ closure {w : ℂ | w ∈ A ∧
            HasWinding (α.trans (p.toPath.cast hs ht)) w n}) := by
  obtain ⟨r, hr, p, hp, hs, ht, hlen, hpO, heq⟩ :=
    exists_simple_polyline_return_same_winding_near_in_open32 α q hqi hz O hO hqO
  refine ⟨p, hp, hs, ht, hlen, hpO, fun A n => ?_⟩
  constructor
  · intro hcl
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.mp hcl (min ε r) (lt_min hε hr)
    have hwball : w ∈ ball z r := by
      rw [mem_ball, dist_comm]
      exact hd.trans_le (min_le_right _ _)
    exact ⟨w, ⟨hw.1, (heq w hwball n).mp hw.2⟩, hd.trans_le (min_le_left _ _)⟩
  · intro hcl
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.mp hcl (min ε r) (lt_min hε hr)
    have hwball : w ∈ ball z r := by
      rw [mem_ball, dist_comm]
      exact hd.trans_le (min_le_right _ _)
    exact ⟨w, ⟨hw.1, (heq w hwball n).mpr hw.2⟩, hd.trans_le (min_le_left _ _)⟩

/-- Helper toward Definition 3.2: a drawn-face `LeftAtOn` return has a simple
polygonal replacement preserving winding-one accumulation, with image in
the face together with arbitrarily small endpoint neighborhoods. Exact face
containment near those endpoints and endpoint-only arc intersection remain
separate obligations. -/
theorem exists_leftAtOn_simple_polyline_return_endpoint_neighborhoods32
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hF : IsOpen F.val) (s : {t : I // t ∈ openParams})
    (hleft : LeftAtOn F.val (P.arc d).toPath s)
    {η : ℝ} (hη : 0 < η) :
    ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b)
      (_hb : b < 1), ∃ p : Polyline, p.IsSimple ∧
      ∃ (hs : (P.arc d).toPath b = p.start)
        (ht : (P.arc d).toPath a = p.finish),
        2 ≤ p.points.length ∧
        p.image ⊆ F.val ∪ ball ((P.arc d).toPath b) η ∪ ball ((P.arc d).toPath a) η ∧
        (P.arc d).toPath s.1 ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding
          ((edgeSubarc (P.arc d).toPath a b (le_of_lt (lt_trans _has _hsb))).trans
            (p.toPath.cast hs ht)) w 1} := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩ := hleft
  obtain ⟨r, hr, hdisj⟩ := P.exists_ball_disjoint_returnPath32 d F a b s has hsb q hqF
  have hz : (P.arc d).toPath s.1 ∉ Set.range q :=
    fun hmem => disjoint_left.mp hdisj (mem_ball_self hr) hmem
  let O := F.val ∪ ball ((P.arc d).toPath b) η ∪ ball ((P.arc d).toPath a) η
  have hO : IsOpen O := (hF.union isOpen_ball).union isOpen_ball
  have hqO : Set.range q ⊆ O := by
    rintro z ⟨t, rfl⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (Or.inr (by simpa only [Path.source] using mem_ball_self hη))
    by_cases ht1 : t = 1
    · subst t
      exact Or.inr (by simpa only [Path.target] using mem_ball_self hη)
    exact Or.inl (Or.inl (hqF t
      ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩))
  obtain ⟨p, hp, hs, ht, hlen, hpO, hacc⟩ :=
    exists_simple_polyline_return_preserves_winding_accumulation_in_open32
      (edgeSubarc (P.arc d).toPath a b (le_of_lt (lt_trans has hsb)))
      q hqi hz O hO hqO
  exact ⟨a, b, ha, has, hsb, hb, p, hp, hs, ht, hlen, hpO,
    (hacc F.val 1).mp hcl⟩




























































































































end DirectedDistances.PlanarMap

end
