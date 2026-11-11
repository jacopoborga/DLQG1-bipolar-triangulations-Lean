/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.LeftAtOnPolygonalReturn
import DirectedDistances.PlanarMap.D39PLOrientedPlaneHomeomorph

/-! # Polygonal return winding obstruction toward Definition 3.2

The polygonal winding bound is transferred from the canonical closed vertex
list to concatenated paths. The boundary-to-boundary simple polygonal return
belong to the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

namespace Polyline

/-- Helper toward Definition 3.2: two simple polygonal arcs meeting only
at their opposite endpoints have winding between minus one and one under
ordinary path concatenation, including its endpoint casts. -/
theorem trans_hasWinding_bounds32 (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hjoin : p.finish = q.start) (hclose : p.start = q.finish)
    (hne : p.start ≠ p.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish})
    (w : ℂ) (n : ℤ)
    (hw : HasWinding (p.toPath.trans (q.toPath.cast hjoin hclose)) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  have hqrev : q.reverse.IsSimple := isSimple_reverse_transfer q hq
  have hlenrev : 2 ≤ q.reverse.points.length := by
    simpa only [reverse, List.length_reverse] using hlenq
  have hs : p.start = q.reverse.start := by
    simpa only [start_reverse] using hclose
  have hf : p.finish = q.reverse.finish := by
    simpa only [finish_reverse] using hjoin
  have hintrev : p.image ∩ q.reverse.image = {p.start, p.finish} := by
    simpa only [image_reverse_transfer] using hint
  have havoid : w ∉ p.image ∪ q.reverse.image := by
    rw [image_reverse_transfer, ← range_toPath p, ← range_toPath q]
    intro hwim
    apply hw.not_mem_range
    rw [Path.trans_range]
    rcases hwim with hpw | hqw
    · exact Or.inl hpw
    · exact Or.inr hqw
  have hsplit := (hasLiftIncrement_trans_iff p.toPath
    (q.toPath.cast hjoin hclose)).mp hw
  obtain ⟨v₁, v₂, hv₁, hv₂, hv⟩ := hsplit
  have hqcast : HasLiftIncrement q.toPath w v₂ :=
    (hasLiftIncrement_congr_fun _ q.toPath (fun _ => rfl)).mp hv₂
  have hcat := (hasLiftIncrement_boundaryConcat_iff (ContinuousMap.id ℂ)
    p q hlenp hlenq hjoin w (2 * Real.pi * Complex.I * (n : ℤ))).mpr
      ⟨v₁, v₂, by simpa only [ContinuousMap.coe_id, Path.map_id] using hv₁,
        by simpa only [ContinuousMap.coe_id, Path.map_id] using hqcast, hv⟩
  simp only [ContinuousMap.coe_id, Path.map_id] at hcat
  have hclosed : HasWinding
      ((closedConcat p q.reverse).toPath.cast rfl
        (closedConcat_closed p q.reverse hlenrev hs)) w n := by
    change HasLiftIncrement _ w (2 * Real.pi * Complex.I * (n : ℤ))
    apply (hasLiftIncrement_congr_fun _ (p.boundaryConcat q).toPath ?_).mpr hcat
    intro t
    change (p.concat q.reverse.reverse).toPath t = (p.boundaryConcat q).toPath t
    rw [reverse_reverse]
    rfl
  exact closedConcat_hasWinding_bounds32 p q.reverse hp hqrev hlenp hlenrev
    hs hf hne hintrev w n havoid hclosed

end Polyline

/-- Helper toward Definition 3.2: a straight chord closed by a simple
polygonal return meeting it only at the endpoints has absolute winding at
most one, in the path representation used by the signed crossing lemma. -/
theorem segment_polyline_return_hasWinding_bounds32 {a b : ℂ}
    (hab : a ≠ b) (q : Polyline) (hq : q.IsSimple)
    (hlenq : 2 ≤ q.points.length)
    (hstart : b = q.start) (hfinish : a = q.finish)
    (hint : segment ℝ a b ∩ q.image = {a, b})
    (w : ℂ) (n : ℤ)
    (hw : HasWinding ((Path.segment a b).trans
      (q.toPath.cast hstart hfinish)) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  let p : Polyline := ⟨[a, b], by simp⟩
  have hp : p.IsSimple := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
      subst i
      exact hab
    · intro i hi
      change i + 2 < 2 at hi
      omega
    · intro i j hi hj hij
      change i + 1 < 2 at hi
      change j + 1 < 2 at hj
      omega
  have hpimage : p.image = segment ℝ a b := by
    rw [← p.range_toPath]
    exact Path.range_segment a b
  exact Polyline.trans_hasWinding_bounds32 p q hp hq (by simp [p]) hlenq
    hstart hfinish hab (by simpa only [hpimage, p, Polyline.start, Polyline.finish,
      List.head_cons, List.getLast_cons_cons, List.getLast_singleton] using hint) w n hw

/-- Helper toward Definition 3.2: for a straight chord with a simple
polygonal return, winding one cannot accumulate from its right and winding
minus one cannot accumulate from its left. The signed unit jump would give
winding two or minus two, contradicting the polygonal winding bound. -/
theorem not_mem_closure_wrong_side_segment_polyline_return32 {a b x : ℂ}
    (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b)
    (q : Polyline) (hq : q.IsSimple) (hlenq : 2 ≤ q.points.length)
    (hstart : b = q.start) (hfinish : a = q.finish)
    (hint : segment ℝ a b ∩ q.image = {a, b}) :
    x ∉ closure {w : ℂ | HasWinding ((Path.segment a b).trans
      (q.toPath.cast hstart hfinish)) w 1 ∧
        (star (b - a) * (w - x)).im < 0} ∧
    x ∉ closure {w : ℂ | HasWinding ((Path.segment a b).trans
      (q.toPath.cast hstart hfinish)) w (-1) ∧
        0 < (star (b - a) * (w - x)).im} := by
  have hxa : x ≠ a := fun h => hab (left_mem_openSegment_iff.mp (h ▸ hx))
  have hxb : x ≠ b := fun h => hab (right_mem_openSegment_iff.mp (h ▸ hx))
  have hxq : x ∉ q.image := by
    intro hxq
    have hmem : x ∈ ({a, b} : Set ℂ) :=
      hint ▸ ⟨openSegment_subset_segment ℝ a b hx, hxq⟩
    rcases hmem with h | h
    · exact hxa h
    · exact hxb h
  have hxrange : x ∉ Set.range (q.toPath.cast hstart hfinish) := by
    intro hxrange
    obtain ⟨t, ht⟩ := hxrange
    exact hxq (q.range_toPath ▸ ⟨t, ht⟩)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (isCompact_range (q.toPath.cast hstart hfinish).continuous).isClosed.isOpen_compl
      x hxrange
  have hdisj : Disjoint (ball x r) (Set.range (q.toPath.cast hstart hfinish)) :=
    Set.disjoint_left.mpr (fun _ hw => hball hw)
  constructor
  · intro hcl
    have htwo := (mem_closure_segment_return_winding_iff32 hab hx hr
      (q.toPath.cast hstart hfinish) hdisj 1).mpr hcl
    obtain ⟨w, hw, _⟩ := Metric.mem_closure_iff.mp htwo 1 zero_lt_one
    have hbound := segment_polyline_return_hasWinding_bounds32 hab q hq hlenq
      hstart hfinish hint w 2 hw.1
    omega
  · intro hcl
    have hcl' : x ∈ closure {w : ℂ | HasWinding ((Path.segment a b).trans
        (q.toPath.cast hstart hfinish)) w ((-2 : ℤ) + 1) ∧
          0 < (star (b - a) * (w - x)).im} := by
      norm_num only
      exact hcl
    have hminus := (mem_closure_segment_return_winding_iff32 hab hx hr
      (q.toPath.cast hstart hfinish) hdisj (-2)).mp hcl'
    obtain ⟨w, hw, _⟩ := Metric.mem_closure_iff.mp hminus 1 zero_lt_one
    have hbound := segment_polyline_return_hasWinding_bounds32 hab q hq hlenq
      hstart hfinish hint w (-2) hw.1
    omega

/-- Helper toward Definition 3.2: every continuous endpoint-preserving
change of the first traversal preserves winding in both directions, even
when that parameter map has constant intervals. -/
theorem hasWinding_trans_reparam_left_continuous_iff32 {x y : ℂ}
    (α : Path x y) (β : Path y x)
    (f : I → I) (hc : Continuous f) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (w : ℂ) (n : ℤ) :
    HasWinding ((α.reparam f hc h0 h1).trans β) w n ↔
      HasWinding (α.trans β) w n := by
  constructor
  · intro hw
    have havoid : w ∉ Set.range (α.trans β) := by
      have hno := hw.not_mem_range
      rw [Path.trans_range, Path.range_reparam α hc h0 h1] at hno
      rwa [Path.trans_range]
    obtain ⟨k, hk⟩ := hasWinding_exists (α.trans β) w havoid
    have hkn : k = n := hasWinding_unique (hk.trans_reparam_left f hc h0 h1) hw
    exact hkn ▸ hk
  · intro hw
    exact hw.trans_reparam_left f hc h0 h1

/-- Helper toward Definition 3.2: removing the constant pauses from a
straight edge subarc preserves every winding integer of its concatenation
with a fixed return path. The affine hypothesis is purely geometric. -/
theorem edgeSubarc_affine_trans_hasWinding_iff32 {x y : ℂ}
    (γ : Path x y) (a b : I) (hab : a < b)
    (hline : ∀ u : I, a ≤ u → u ≤ b →
      γ u = γ a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (γ b - γ a)))
    (q : Path (γ b) (γ a)) (w : ℂ) (n : ℤ) :
    HasWinding ((edgeSubarc γ a b hab.le).trans q) w n ↔
      HasWinding ((Path.segment (γ a) (γ b)).trans q) w n := by
  have habR : (a : ℝ) < (b : ℝ) := hab
  let g : I → I := fun t => ⟨
      (((min (max t a) b : I) : ℝ) - a) / ((b : ℝ) - a), by
    have hca : a ≤ min (max t a) b := le_min (le_max_right _ _) hab.le
    have hcb : min (max t a) b ≤ b := min_le_right _ _
    constructor
    · exact div_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ _ from hca))
        (sub_pos.mpr habR).le
    · exact (div_le_one (sub_pos.mpr habR)).mpr
        (sub_le_sub_right (show (_ : ℝ) ≤ b from hcb) _)⟩
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg0 : g 0 = 0 := by
    apply Subtype.ext
    simp only [g, max_eq_right (show (0 : I) ≤ a from a.2.1),
      min_eq_left hab.le, sub_self, zero_div, Set.Icc.coe_zero]
  have hg1 : g 1 = 1 := by
    apply Subtype.ext
    simp only [g, max_eq_left (show a ≤ (1 : I) from a.2.2),
      min_eq_right (show b ≤ (1 : I) from b.2.2),
      div_self (sub_ne_zero.mpr habR.ne'), Set.Icc.coe_one]
  have hpaused : edgeSubarc γ a b hab.le =
      (Path.segment (γ a) (γ b)).reparam g hgc hg0 hg1 := by
    apply Path.ext
    funext t
    rw [edgeSubarc_affine_apply γ hab hline]
    change _ = Path.segment (γ a) (γ b) (g t)
    rw [Path.segment_apply, AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    exact add_comm _ _
  rw [hpaused]
  exact hasWinding_trans_reparam_left_continuous_iff32 _ q g hgc hg0 hg1 w n

/-- Helper toward Definition 3.2: the absolute winding bound also holds
for a paused affine subarc closed by a simple polygonal return. -/
theorem edgeSubarc_affine_polyline_return_hasWinding_bounds32 {x y : ℂ}
    (γ : Path x y) (a b : I) (hab : a < b)
    (hline : ∀ u : I, a ≤ u → u ≤ b →
      γ u = γ a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (γ b - γ a)))
    (hne : γ a ≠ γ b)
    (q : Polyline) (hq : q.IsSimple) (hlenq : 2 ≤ q.points.length)
    (hstart : γ b = q.start) (hfinish : γ a = q.finish)
    (hint : segment ℝ (γ a) (γ b) ∩ q.image = {γ a, γ b})
    (w : ℂ) (n : ℤ)
    (hw : HasWinding ((edgeSubarc γ a b hab.le).trans
      (q.toPath.cast hstart hfinish)) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  exact segment_polyline_return_hasWinding_bounds32 hne q hq hlenq hstart hfinish
    hint w n ((edgeSubarc_affine_trans_hasWinding_iff32 γ a b hab hline _ w n).mp hw)

/-- Helper toward Definition 3.2: the wrong-side winding accumulation
obstruction survives the pauses in an affine subarc's traversal. -/
theorem not_mem_closure_wrong_side_edgeSubarc_affine_polyline_return32
    {x y z : ℂ} (γ : Path x y) (a b : I) (hab : a < b)
    (hline : ∀ u : I, a ≤ u → u ≤ b →
      γ u = γ a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (γ b - γ a)))
    (hne : γ a ≠ γ b) (hz : z ∈ openSegment ℝ (γ a) (γ b))
    (q : Polyline) (hq : q.IsSimple) (hlenq : 2 ≤ q.points.length)
    (hstart : γ b = q.start) (hfinish : γ a = q.finish)
    (hint : segment ℝ (γ a) (γ b) ∩ q.image = {γ a, γ b}) :
    z ∉ closure {w : ℂ | HasWinding ((edgeSubarc γ a b hab.le).trans
      (q.toPath.cast hstart hfinish)) w 1 ∧
        (star (γ b - γ a) * (w - z)).im < 0} ∧
    z ∉ closure {w : ℂ | HasWinding ((edgeSubarc γ a b hab.le).trans
      (q.toPath.cast hstart hfinish)) w (-1) ∧
        0 < (star (γ b - γ a) * (w - z)).im} := by
  simpa only [edgeSubarc_affine_trans_hasWinding_iff32 γ a b hab hline] using
    not_mem_closure_wrong_side_segment_polyline_return32 hne hz q hq hlenq
      hstart hfinish hint













































































































































end DirectedDistances.PlanarMap

end
