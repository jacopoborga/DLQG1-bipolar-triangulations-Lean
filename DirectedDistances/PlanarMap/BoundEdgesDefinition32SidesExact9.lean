/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact8
public import DirectedDistances.PlanarMap.D39PolygonWindingBridge
import DirectedDistances.PlanarMap.D39PolygonalSeparation5
import DirectedDistances.PlanarMap.D39PolygonalConnected
import DirectedDistances.PlanarMap.D39WindingExistence
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-! # Local logarithmic winding across an isolated segment -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric Filter
open scoped Topology ComplexConjugate

/-- Helper toward Definition 3.2: the increment of a logarithmic lift of an
arbitrary path is unique, including paths whose endpoints differ. -/
theorem hasLiftIncrement_unique32 {a b w c d : ℂ} {γ : Path a b}
    (hc : HasLiftIncrement γ w c) (hd : HasLiftIncrement γ w d) : c = d := by
  obtain ⟨φ, hφ, hφinc⟩ := hc
  obtain ⟨ψ, hψ, hψinc⟩ := hd
  let f : I → ℂ := fun t => φ t - ψ t
  let T := AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
  let : DiscreteTopology T := NormedSpace.discreteTopology_zmultiples _
  have hfmem (t : I) : f t ∈ T := by
    have hexp : Complex.exp (f t) = Complex.exp (0 : ℂ) := by
      change Complex.exp (φ t - ψ t) = _
      rw [Complex.exp_sub, hφ, hψ]
      have hne : γ t - w ≠ 0 := by rw [← hψ t]; exact Complex.exp_ne_zero _
      simp only [div_self hne, Complex.exp_zero]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    change f t ∈ AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨k, by simpa [zsmul_eq_mul, mul_comm] using hk.symm⟩
  let fT : I → T := fun t => ⟨f t, hfmem t⟩
  have hcont : Continuous fT :=
    Continuous.subtype_mk (φ.continuous.sub ψ.continuous) hfmem
  have h10 : f 1 = f 0 := congrArg Subtype.val
    (PreconnectedSpace.constant inferInstance hcont : fT 1 = fT 0)
  dsimp [f] at h10
  rw [← hφinc, ← hψinc]
  linear_combination h10

/-- Helper toward Definition 3.2: every continuous path avoiding the
viewpoint has a logarithmic lift with some complex endpoint increment. -/
theorem exists_hasLiftIncrement32 {a b : ℂ} (γ : Path a b) (w : ℂ)
    (havoid : w ∉ Set.range γ) : ∃ c : ℂ, HasLiftIncrement γ w c := by
  let f : C(I, ℂ) := ⟨fun t => γ t - w, γ.continuous.sub continuous_const⟩
  have hzero (t : I) : f t ≠ 0 := by
    intro ht
    exact havoid ⟨t, sub_eq_zero.mp ht⟩
  let δ : Path (⟨f 0, hzero 0⟩ : {x : ℂ // x ≠ 0})
      (⟨f 1, hzero 1⟩ : {x : ℂ // x ≠ 0}) :=
    { toFun := fun t => ⟨f t, hzero t⟩
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  have hbase : Complex.exp (Complex.log (f 0)) = f 0 := Complex.exp_log (hzero 0)
  let φ := Complex.isCoveringMap_exp.liftPath δ (Complex.log (f 0)) (by
    apply Subtype.ext
    exact hbase.symm)
  refine ⟨φ 1 - φ 0, φ, ?_, rfl⟩
  intro t
  have ht := congrFun
    (Complex.isCoveringMap_exp.liftPath_lifts δ (Complex.log (f 0)) (by
      apply Subtype.ext
      exact hbase.symm)) t
  exact congrArg Subtype.val ht

/-- Helper toward Definition 3.2: near a viewpoint avoided by a path, its
logarithmic lift increment varies by the explicit endpoint logarithms. -/
theorem hasLiftIncrement_stable_nearby32 {a b x c : ℂ} (γ : Path a b)
    (hc : HasLiftIncrement γ x c) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, dist w x < r →
      HasLiftIncrement γ w
        (c + Complex.log ((b - w) / (b - x)) -
          Complex.log ((a - w) / (a - x))) := by
  obtain ⟨φ, hφ, hinc⟩ := hc
  have hden (t : I) : γ t - x ≠ 0 := by
    rw [← hφ t]
    exact Complex.exp_ne_zero _
  have hclosed : IsClosed (Set.range γ) := (isCompact_range γ.continuous).isClosed
  have havoid : x ∉ Set.range γ := by
    rintro ⟨t, ht⟩
    exact hden t (sub_eq_zero.mpr ht)
  have hr : 0 < infDist x (Set.range γ) :=
    hclosed.notMem_iff_infDist_pos (Set.range_nonempty γ) |>.mp havoid
  refine ⟨infDist x (Set.range γ), hr, ?_⟩
  intro w hw
  let R : I → ℂ := fun t => (γ t - w) / (γ t - x)
  have hR (t : I) : R t ∈ Complex.slitPlane := by
    apply Complex.ball_one_subset_slitPlane
    change dist (R t) 1 < 1
    rw [dist_eq_norm]
    have heq : R t - 1 = (x - w) / (γ t - x) := by
      dsimp [R]
      field_simp [hden t]
      ring
    rw [heq, norm_div]
    apply (div_lt_one (norm_pos_iff.mpr (hden t))).2
    have hdist := infDist_le_dist_of_mem (x := x) (Set.mem_range_self (f := γ) t)
    calc
      ‖x - w‖ = dist w x := by rw [dist_eq_norm, norm_sub_rev]
      _ < infDist x (Set.range γ) := hw
      _ ≤ ‖γ t - x‖ := by simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hRcont : Continuous R :=
    (γ.continuous.sub continuous_const).div (γ.continuous.sub continuous_const) hden
  let ψ : C(I, ℂ) := ⟨fun t => φ t + Complex.log (R t),
    φ.continuous.add (hRcont.clog hR)⟩
  refine ⟨ψ, ?_, ?_⟩
  · intro t
    change Complex.exp (φ t + Complex.log (R t)) = γ t - w
    rw [Complex.exp_add, hφ, Complex.exp_log (Complex.slitPlane_ne_zero (hR t))]
    exact mul_div_cancel₀ _ (hden t)
  · change (φ 1 + Complex.log (R 1)) - (φ 0 + Complex.log (R 0)) = _
    have hR0 : R 0 = (a - w) / (a - x) := by simp only [R, Path.source]
    have hR1 : R 1 = (b - w) / (b - x) := by simp only [R, Path.target]
    rw [hR0, hR1, ← hinc]
    ring

/-- Helper toward Definition 3.2: the endpoint correction for moving the
viewpoint tends to zero at every point distinct from that endpoint. -/
theorem tendsto_endpoint_log_correction32 {a x : ℂ} (hax : a ≠ x) :
    Tendsto (fun w : ℂ => (Complex.log ((a - w) / (a - x))).im)
      (𝓝 x) (𝓝 0) := by
  have hden : a - x ≠ 0 := sub_ne_zero.mpr hax
  have hratio : ContinuousAt (fun w : ℂ => (a - w) / (a - x)) x := by fun_prop
  have hlog : ContinuousAt (fun w : ℂ => Complex.log ((a - w) / (a - x))) x := by
    apply ContinuousAt.clog hratio
    simpa only [div_self hden] using (show (1 : ℂ) ∈ Complex.slitPlane by
      rw [Complex.mem_slitPlane_iff]; exact Or.inl (by norm_num))
  convert (Complex.continuous_im.continuousAt.comp hlog).tendsto using 1 <;>
    simp [Function.comp_def, hden]

/-- Helper toward Definition 3.2: for an isolated straight traversal closed
by any continuous return path, the winding integer is its principal segment
angle plus a continuous endpoint correction and a fixed return increment. -/
theorem exists_segment_return_winding_formula32 {a b x : ℂ}
    (q : Path b a) (havoid : x ∉ Set.range q) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, dist w x < r →
      (b - w) / (a - w) ∈ Complex.slitPlane → ∀ n : ℤ,
      HasWinding ((Path.segment a b).trans q) w n →
      2 * Real.pi * (n : ℝ) = Complex.arg ((b - w) / (a - w)) +
        (c + Complex.log ((a - w) / (a - x)) -
          Complex.log ((b - w) / (b - x))).im := by
  obtain ⟨c, hc⟩ := exists_hasLiftIncrement32 q x havoid
  obtain ⟨r, hr, hnear⟩ := hasLiftIncrement_stable_nearby32 q hc
  refine ⟨c, r, hr, ?_⟩
  intro w hw hquot n hn
  have ha : a - w ≠ 0 := by
    intro hz
    have hnonzero := Complex.slitPlane_ne_zero hquot
    rw [hz, div_zero] at hnonzero
    exact hnonzero rfl
  have hs := hasLiftIncrement_segment (Complex.exp_log ha) hquot
  have hsum := hasLiftIncrement_trans hs (hnear w hw)
  have heq := hasLiftIncrement_unique32 hsum hn
  have him := congrArg Complex.im heq
  have htwo : (2 : ℂ).re = (2 : ℝ) := by norm_num
  simpa only [Complex.add_im, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.intCast_re, Complex.intCast_im, Complex.log_im,
    htwo, mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one] using him.symm

/-- Helper toward Definition 3.2: the argument of the endpoint quotient
has the signed limits `pi` and `-pi` on the two sides of a straight segment. -/
theorem tendsto_segment_arg_sides32 {a b x : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) :
    Tendsto (fun w : ℂ => Complex.arg ((b - w) / (a - w)))
      (𝓝[{w : ℂ | 0 < (star (b - a) * (w - x)).im}] x) (𝓝 Real.pi) ∧
    Tendsto (fun w : ℂ => Complex.arg ((b - w) / (a - w)))
      (𝓝[{w : ℂ | (star (b - a) * (w - x)).im < 0}] x) (𝓝 (-Real.pi)) := by
  let p : Polyline := ⟨[a, b], by simp⟩
  have hp0 : p.point 0 = a := by simp [p, Polyline.point]
  have hp1 : p.point 1 = b := by simp [p, Polyline.point]
  have hi : 0 + 1 < p.points.length := by simp [p]
  have hseg : x ∈ p.segmentAt 0 := by
    simpa only [Polyline.segmentAt, hp0, hp1] using
      openSegment_subset_segment ℝ a b hx
  have hxa : x ≠ a := by
    intro heq
    subst x
    exact hab ((left_mem_openSegment_iff).mp hx)
  have hxb : x ≠ b := by
    intro heq
    subst x
    exact hab ((right_mem_openSegment_iff).mp hx)
  have hpne : p.point 0 ≠ p.point (0 + 1) := by simpa only [hp0, hp1] using hab
  have hpos := Polyline.tendsto_edgeAngle_nhdsWithin_pos_cyclic p 0 hi x hseg
    (by simpa only [hp0] using hxa) (by simpa only [hp1] using hxb) hpne
  have hneg := Polyline.tendsto_edgeAngle_nhdsWithin_neg_cyclic p 0 hi x hseg
    (by simpa only [hp0] using hxa) (by simpa only [hp1] using hxb) hpne
  exact ⟨by simpa only [Polyline.edgeAngle, hp0, hp1, Complex.star_def] using hpos,
    by simpa only [Polyline.edgeAngle, hp0, hp1, Complex.star_def] using hneg⟩

/-- Helper toward Definition 3.2: an off-line viewpoint gives a segment
endpoint quotient in the slit plane, on either strict transverse side. -/
theorem segment_quotient_mem_slitPlane32 {a b x w : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b)
    (hw : (star (b - a) * (w - x)).im ≠ 0) :
    (b - w) / (a - w) ∈ Complex.slitPlane := by
  let p : Polyline := ⟨[a, b], by simp⟩
  have hp0 : p.point 0 = a := by simp [p, Polyline.point]
  have hp1 : p.point 1 = b := by simp [p, Polyline.point]
  have hxa : x ≠ a := by
    intro heq
    subst x
    exact hab (left_mem_openSegment_iff.mp hx)
  have hxb : x ≠ b := by
    intro heq
    subst x
    exact hab (right_mem_openSegment_iff.mp hx)
  have hseg : x ∈ p.segmentAt 0 := by
    simpa only [Polyline.segmentAt, hp0, hp1] using
      openSegment_subset_segment ℝ a b hx
  have hid := Polyline.edgeQuotient_im_mul_normSq_eq_side p 0 x hseg
    (by simpa only [hp0] using hxa) (by simpa only [hp1] using hxb) w
  have hid' : (((b - w) / (a - w)).im) * ‖a - w‖ ^ 2 =
      (star (b - a) * (w - x)).im := by
    simpa only [hp0, hp1, Complex.star_def] using hid
  rw [Complex.mem_slitPlane_iff]
  right
  intro hz
  rw [hz, zero_mul] at hid'
  exact hw hid'.symm

/-- Helper toward Definition 3.2: a logarithmic lift on a loop determines
an integer winding, since the two endpoint exponentials coincide. -/
theorem exists_hasWinding_of_hasLiftIncrement32 {z w c : ℂ} (L : Path z z)
    (hc : HasLiftIncrement L w c) : ∃ n : ℤ, HasWinding L w n := by
  obtain ⟨φ, hφ, _⟩ := hc
  have heq : Complex.exp (φ 1) = Complex.exp (φ 0) := by
    rw [hφ, hφ, Path.source, Path.target]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  refine ⟨n, φ, hφ, ?_⟩
  rw [hn]
  ring

/-- Helper toward Definition 3.2: across an isolated straight traversal,
any two nearby winding integers differ by positive one in left-minus-right
order. The return path is arbitrary and need not be polygonal or simple. -/
theorem exists_segment_return_winding_jump32 {a b x : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) (q : Path b a) (havoid : x ∉ Set.range q) :
    ∃ r : ℝ, 0 < r ∧ ∀ u v : ℂ, dist u x < r → dist v x < r →
      0 < (star (b - a) * (u - x)).im →
      (star (b - a) * (v - x)).im < 0 → ∀ m n : ℤ,
      HasWinding ((Path.segment a b).trans q) u m →
      HasWinding ((Path.segment a b).trans q) v n → m = n + 1 := by
  have hxa : a ≠ x := by
    intro heq
    subst x
    exact hab (left_mem_openSegment_iff.mp hx)
  have hxb : b ≠ x := by
    intro heq
    subst x
    exact hab (right_mem_openSegment_iff.mp hx)
  obtain ⟨c, r, hr, hformula⟩ := exists_segment_return_winding_formula32 q havoid
  let f : ℂ → ℝ := fun w => Complex.arg ((b - w) / (a - w)) +
    (c + Complex.log ((a - w) / (a - x)) -
      Complex.log ((b - w) / (b - x))).im
  have hcorrection : Tendsto
      (fun w : ℂ => (c + Complex.log ((a - w) / (a - x)) -
        Complex.log ((b - w) / (b - x))).im) (𝓝 x) (𝓝 c.im) := by
    have hc : Tendsto (fun _ : ℂ => c.im) (𝓝 x) (𝓝 c.im) := tendsto_const_nhds
    have h := (hc.add (tendsto_endpoint_log_correction32 hxa)).sub
      (tendsto_endpoint_log_correction32 hxb)
    simpa only [Complex.sub_im, Complex.add_im, add_zero, sub_zero] using h
  obtain ⟨hpos, hneg⟩ := tendsto_segment_arg_sides32 hab hx
  have hfpos : Tendsto f
      (𝓝[{w : ℂ | 0 < (star (b - a) * (w - x)).im}] x)
      (𝓝 (Real.pi + c.im)) :=
    hpos.add (hcorrection.mono_left nhdsWithin_le_nhds)
  have hfneg : Tendsto f
      (𝓝[{w : ℂ | (star (b - a) * (w - x)).im < 0}] x)
      (𝓝 (-Real.pi + c.im)) :=
    hneg.add (hcorrection.mono_left nhdsWithin_le_nhds)
  have hpp : ∀ᶠ w : ℂ in 𝓝 x,
      0 < (star (b - a) * (w - x)).im →
        dist (f w) (Real.pi + c.im) < Real.pi / 4 := by
    exact eventually_nhdsWithin_iff.mp
      (hfpos.eventually (Metric.ball_mem_nhds _ (by positivity)))
  have hnn : ∀ᶠ w : ℂ in 𝓝 x,
      (star (b - a) * (w - x)).im < 0 →
        dist (f w) (-Real.pi + c.im) < Real.pi / 4 := by
    exact eventually_nhdsWithin_iff.mp
      (hfneg.eventually (Metric.ball_mem_nhds _ (by positivity)))
  obtain ⟨s, hs, hsp⟩ := Metric.eventually_nhds_iff.mp hpp
  obtain ⟨t, ht, htn⟩ := Metric.eventually_nhds_iff.mp hnn
  refine ⟨min r (min s t), lt_min hr (lt_min hs ht), ?_⟩
  intro u v hu hv hup hvn m n hm hn
  have huR := hu.trans_le (min_le_left r (min s t))
  have hvR := hv.trans_le (min_le_left r (min s t))
  have huS := hu.trans_le ((min_le_right r (min s t)).trans (min_le_left s t))
  have hvT := hv.trans_le ((min_le_right r (min s t)).trans (min_le_right s t))
  have hmformula : 2 * Real.pi * (m : ℝ) = f u :=
    hformula u huR (segment_quotient_mem_slitPlane32 hab hx (ne_of_gt hup)) m hm
  have hnformula : 2 * Real.pi * (n : ℝ) = f v :=
    hformula v hvR (segment_quotient_mem_slitPlane32 hab hx (ne_of_lt hvn)) n hn
  have hmclose := abs_lt.mp (show |f u - (Real.pi + c.im)| < Real.pi / 4 by
    simpa only [Real.dist_eq] using hsp huS hup)
  have hnclose := abs_lt.mp (show |f v - (-Real.pi + c.im)| < Real.pi / 4 by
    simpa only [Real.dist_eq] using htn hvT hvn)
  have hpin : |((m - n : ℤ) : ℝ) - 1| < 1 / 2 := by
    rw [Int.cast_sub, abs_lt]
    constructor <;> nlinarith only [hmclose.1, hmclose.2, hnclose.1,
      hnclose.2, hmformula, hnformula, Real.pi_pos]
  have heq := Polyline.int_sub_eq_one_of_abs_lt_half_cyclic m n hpin
  omega

/-- Helper toward Definition 3.2: near a point of an isolated straight
traversal, winding exists on both strict sides for an arbitrary continuous
return path. No winding hypothesis is required at the tested point. -/
theorem exists_segment_return_winding_nearby32 {a b x : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) (q : Path b a) (havoid : x ∉ Set.range q) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, dist w x < r →
      (star (b - a) * (w - x)).im ≠ 0 →
      ∃ n : ℤ, HasWinding ((Path.segment a b).trans q) w n := by
  obtain ⟨c, hc⟩ := exists_hasLiftIncrement32 q x havoid
  obtain ⟨r, hr, hnear⟩ := hasLiftIncrement_stable_nearby32 q hc
  refine ⟨r, hr, ?_⟩
  intro w hw hside
  have hquot := segment_quotient_mem_slitPlane32 hab hx hside
  have ha : a - w ≠ 0 := by
    intro hz
    have hne := Complex.slitPlane_ne_zero hquot
    rw [hz, div_zero] at hne
    exact hne rfl
  exact exists_hasWinding_of_hasLiftIncrement32 _
    (hasLiftIncrement_trans
      (hasLiftIncrement_segment (Complex.exp_log ha) hquot) (hnear w hw))

/-- Helper toward Definition 3.2: crossing an isolated straight segment
once from its right to its left increases winding by exactly one. The return
path is any continuous path avoiding the segment's tested interior point;
the radius is chosen uniformly for all viewpoints and all winding integers. -/
theorem exists_segment_return_hasWinding_iff32 {a b x : ℂ} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) (q : Path b a) (havoid : x ∉ Set.range q) :
    ∃ r : ℝ, 0 < r ∧ ∀ u v : ℂ, dist u x < r → dist v x < r →
      0 < (star (b - a) * (u - x)).im →
      (star (b - a) * (v - x)).im < 0 → ∀ n : ℤ,
      (HasWinding ((Path.segment a b).trans q) u (n + 1) ↔
        HasWinding ((Path.segment a b).trans q) v n) := by
  obtain ⟨r, hr, hjump⟩ := exists_segment_return_winding_jump32 hab hx q havoid
  obtain ⟨s, hs, hexists⟩ := exists_segment_return_winding_nearby32 hab hx q havoid
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro u v hu hv hup hvn n
  have hur := hu.trans_le (min_le_left r s)
  have hvr := hv.trans_le (min_le_left r s)
  have hus := hu.trans_le (min_le_right r s)
  have hvs := hv.trans_le (min_le_right r s)
  constructor
  · intro hn
    obtain ⟨k, hk⟩ := hexists v hvs (ne_of_lt hvn)
    have heq := hjump u v hur hvr hup hvn (n + 1) k hn hk
    have hkn : k = n := by omega
    exact hkn ▸ hk
  · intro hn
    obtain ⟨k, hk⟩ := hexists u hus (ne_of_gt hup)
    have heq := hjump u v hur hvr hup hvn k n hk hn
    exact heq ▸ hk

/-- Helper toward Definition 3.2: a straight segment and a return path
outside a prescribed disk have constant winding on each open half-disk,
with the left integer exactly one greater than the right integer. -/
theorem exists_segment_return_halfDisk_winding32 {a b x : ℂ} {r : ℝ}
    (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) (hr : 0 < r)
    (q : Path b a) (havoid : Disjoint (ball x r) (Set.range q)) :
    ∃ n : ℤ,
      (∀ u ∈ ball x r, 0 < (star (b - a) * (u - x)).im →
        HasWinding ((Path.segment a b).trans q) u (n + 1)) ∧
      (∀ v ∈ ball x r, (star (b - a) * (v - x)).im < 0 →
        HasWinding ((Path.segment a b).trans q) v n) := by
  let L := (Path.segment a b).trans q
  have hconstant (U : Set ℂ) (hconn : IsPreconnected U)
      (hball : U ⊆ ball x r)
      (hside : ∀ w ∈ U, (star (b - a) * (w - x)).im ≠ 0) :
      ∃ n : ℤ, ∀ w ∈ U, HasWinding L w n := by
    apply hasWinding_value_constant_on_preconnected L U _ hconn
    intro w hw hL
    have hquot := segment_quotient_mem_slitPlane32 hab hx (hside w hw)
    have ha : a - w ≠ 0 := by
      intro hz
      have hne := Complex.slitPlane_ne_zero hquot
      rw [hz, div_zero] at hne
      exact hne rfl
    obtain ⟨φ, hφ, _⟩ := hasLiftIncrement_segment (Complex.exp_log ha) hquot
    rw [Path.trans_range] at hL
    rcases hL with hseg | hq
    · obtain ⟨t, ht⟩ := hseg
      have he := hφ t
      rw [ht, sub_self] at he
      exact Complex.exp_ne_zero _ he
    · exact Set.disjoint_left.mp havoid (hball hw) hq
  obtain ⟨m, hm⟩ := hconstant (Polyline.leftHalfDisc x (b - a) r)
    (Polyline.convex_leftHalfDisc x (b - a) r).isPreconnected
    (fun _ hw => hw.1) (fun _ hw => ne_of_gt hw.2)
  obtain ⟨n, hn⟩ := hconstant (Polyline.rightHalfDisc x (b - a) r)
    (Polyline.convex_rightHalfDisc x (b - a) r).isPreconnected
    (fun _ hw => hw.1) (fun _ hw => ne_of_lt hw.2)
  have hxq : x ∉ Set.range q := Set.disjoint_left.mp havoid (mem_ball_self hr)
  obtain ⟨s, hs, hjump⟩ := exists_segment_return_winding_jump32 hab hx q hxq
  have hdir : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨u, hu⟩ := Polyline.leftHalfDisc_nonempty x (b - a) (min r s) hdir
    (lt_min hr hs)
  obtain ⟨v, hv⟩ := Polyline.rightHalfDisc_nonempty x (b - a) (min r s) hdir
    (lt_min hr hs)
  have huR : u ∈ ball x r := ball_subset_ball (min_le_left r s) hu.1
  have hvR : v ∈ ball x r := ball_subset_ball (min_le_left r s) hv.1
  have huS : dist u x < s := (mem_ball.mp hu.1).trans_le (min_le_right r s)
  have hvS : dist v x < s := (mem_ball.mp hv.1).trans_le (min_le_right r s)
  have hmn : m = n + 1 := hjump u v huS hvS hu.2 hv.2 m n
    (hm u ⟨huR, hu.2⟩) (hn v ⟨hvR, hv.2⟩)
  refine ⟨n, ?_, ?_⟩
  · intro u hu hup
    exact hmn ▸ hm u ⟨hu, hup⟩
  · intro v hv hvn
    exact hn v ⟨hv, hvn⟩

/-- Helper toward Definition 3.2: in any prescribed disk disjoint from
the return path, moving across the straight traversal from right to left
adds exactly one to winding, for every integer and every pair of viewpoints. -/
theorem segment_return_hasWinding_iff32 {a b x : ℂ} {r : ℝ}
    (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) (hr : 0 < r)
    (q : Path b a) (havoid : Disjoint (ball x r) (Set.range q))
    (u v : ℂ) (hu : u ∈ ball x r) (hv : v ∈ ball x r)
    (hup : 0 < (star (b - a) * (u - x)).im)
    (hvn : (star (b - a) * (v - x)).im < 0) (n : ℤ) :
    HasWinding ((Path.segment a b).trans q) u (n + 1) ↔
      HasWinding ((Path.segment a b).trans q) v n := by
  obtain ⟨k, hkleft, hkright⟩ :=
    exists_segment_return_halfDisk_winding32 hab hx hr q havoid
  have hleft := hkleft u hu hup
  have hright := hkright v hv hvn
  constructor
  · intro hn
    have heq := hasWinding_unique hn hleft
    have hnk : n = k := by omega
    exact hnk.symm ▸ hright
  · intro hn
    have heq := hasWinding_unique hn hright
    exact heq.symm ▸ hleft

/-- Helper toward Definition 3.2: signed winding accumulation transfers
across an isolated segment with exactly the same unit increment as pointwise
winding. In particular, right-side winding one forces left-side winding two. -/
theorem mem_closure_segment_return_winding_iff32 {a b x : ℂ} {r : ℝ}
    (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) (hr : 0 < r)
    (q : Path b a) (havoid : Disjoint (ball x r) (Set.range q)) (n : ℤ) :
    (x ∈ closure {w : ℂ | HasWinding ((Path.segment a b).trans q) w (n + 1) ∧
      0 < (star (b - a) * (w - x)).im}) ↔
    (x ∈ closure {w : ℂ | HasWinding ((Path.segment a b).trans q) w n ∧
      (star (b - a) * (w - x)).im < 0}) := by
  obtain ⟨k, hkleft, hkright⟩ :=
    exists_segment_return_halfDisk_winding32 hab hx hr q havoid
  have hdir : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  constructor
  · intro hcl
    obtain ⟨u, hu, hux⟩ := Metric.mem_closure_iff.mp hcl r hr
    have huR : u ∈ ball x r := by simpa only [mem_ball, dist_comm] using hux
    have heq := hasWinding_unique hu.1 (hkleft u huR hu.2)
    have hnk : n = k := by omega
    apply closure_mono _ (Polyline.mem_closure_rightHalfDisc x (b - a) r hdir hr)
    intro v hv
    exact ⟨hnk.symm ▸ hkright v hv.1 hv.2, hv.2⟩
  · intro hcl
    obtain ⟨v, hv, hvx⟩ := Metric.mem_closure_iff.mp hcl r hr
    have hvR : v ∈ ball x r := by simpa only [mem_ball, dist_comm] using hvx
    have hnk := hasWinding_unique hv.1 (hkright v hvR hv.2)
    apply closure_mono _ (Polyline.mem_closure_leftHalfDisc x (b - a) r hdir hr)
    intro u hu
    exact ⟨hnk.symm ▸ hkleft u hu.1 hu.2, hu.2⟩















































































































end DirectedDistances.PlanarMap

end
