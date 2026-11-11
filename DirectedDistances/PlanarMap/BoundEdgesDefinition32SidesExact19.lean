/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact18
import DirectedDistances.PlanarMap.LeftAtOnPolygonalReturn
import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen3
import DirectedDistances.PlanarMap.D39PLOrientedPlaneHomeomorph

/-! # Endpoint connectors toward Definition 3.2 -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

private theorem image_twoPoint19 (x y : ℂ) :
    (⟨[x, y], by simp⟩ : Polyline).image = segment ℝ x y := by
  rw [← Polyline.range_toPath]
  exact Path.range_segment x y

/-- Helper toward Definition 3.2: two segments sharing an endpoint and a
second point have one outer endpoint on the other segment. -/
theorem mem_segment_or_mem_segment_of_common_point32 (a b c z : ℂ)
    (hzab : z ∈ segment ℝ a b) (hzbc : z ∈ segment ℝ b c) (hzb : z ≠ b) :
    c ∈ segment ℝ a b ∨ a ∈ segment ℝ b c := by
  rw [segment_symm ℝ a b, segment_eq_image'] at hzab
  rw [segment_eq_image'] at hzbc
  obtain ⟨t, ht, hzt⟩ := hzab
  obtain ⟨u, hu, hzu⟩ := hzbc
  have heq : t • (a - b) = u • (c - b) := add_left_cancel (hzt.trans hzu.symm)
  have ht0 : t ≠ 0 := by
    intro h; subst t; exact hzb (by simpa using hzt.symm)
  have hu0 : u ≠ 0 := by
    intro h; subst u; exact hzb (by simpa using hzu.symm)
  by_cases htu : t ≤ u
  · left
    rw [segment_symm ℝ a b, segment_eq_image']
    refine ⟨t / u, ⟨div_nonneg ht.1 hu.1,
      (div_le_one (lt_of_le_of_ne hu.1 (Ne.symm hu0))).mpr htu⟩, ?_⟩
    have hr : (t / u) • (a - b) = c - b := by
      rw [div_eq_inv_mul, mul_smul, heq, smul_smul, inv_mul_cancel₀ hu0, one_smul]
    change b + (t / u) • (a - b) = c
    rw [hr]; abel
  · right
    rw [segment_eq_image']
    refine ⟨u / t, ⟨div_nonneg hu.1 ht.1,
      (div_le_one (lt_of_le_of_ne ht.1 (Ne.symm ht0))).mpr (le_of_not_ge htu)⟩, ?_⟩
    have hr : (u / t) • (c - b) = a - b := by
      rw [div_eq_inv_mul, mul_smul, ← heq, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    change b + (u / t) • (c - b) = a
    rw [hr]; abel

/-- Helper toward Definition 3.2: a short connector from a chord endpoint
to a point outside the chord has exactly that endpoint in common with it. -/
theorem segment_inter_short_connector32 (a b c : ℂ) {r : ℝ}
    (hr : 0 < r) (hrab : r ≤ dist a b)
    (hc : c ∈ ball b r) (hcout : c ∉ segment ℝ a b) :
    segment ℝ a b ∩ segment ℝ b c = {b} := by
  have hseg : segment ℝ b c ⊆ ball b r :=
    (convex_ball b r).segment_subset (mem_ball_self hr) hc
  apply Subset.antisymm
  · intro z hz
    apply mem_singleton_iff.mpr
    by_contra hzb
    rcases mem_segment_or_mem_segment_of_common_point32 a b c z hz.1 hz.2 hzb with h | h
    · exact hcout h
    · exact (not_lt_of_ge hrab) (mem_ball.mp (hseg h))
  · intro z hz
    rw [mem_singleton_iff] at hz
    subst z
    exact ⟨right_mem_segment ℝ a b, left_mem_segment ℝ b c⟩

/-- Helper toward Definition 3.2: a return meeting a straight chord only at
its endpoints has a simple polygonal replacement with the same intersection
property in every open neighborhood of its entire image. -/
theorem exists_simple_polyline_return_disjoint_in_open32
    {a b : ℂ} (hab : a ≠ b) (q : Path b a)
    (hqi : Function.Injective q)
    (hint : segment ℝ a b ∩ Set.range q = ({a, b} : Set ℂ))
    (U : Set ℂ) (hU : IsOpen U) (hqU : Set.range q ⊆ U) :
    ∃ p : Polyline, p.IsSimple ∧ p.start = b ∧ p.finish = a ∧
      2 ≤ p.points.length ∧ p.image ⊆ U ∧
      segment ℝ a b ∩ p.image = ({a, b} : Set ℂ) := by
  have haU : a ∈ U := hqU ⟨1, q.target⟩
  have hbU : b ∈ U := hqU ⟨0, q.source⟩
  obtain ⟨ra, hra, hballa⟩ := Metric.isOpen_iff.mp hU a haU
  obtain ⟨rb, hrb, hballb⟩ := Metric.isOpen_iff.mp hU b hbU
  let r := min ra (min rb (dist a b))
  have hr : 0 < r := lt_min hra (lt_min hrb (dist_pos.mpr hab))
  have hrab : r ≤ dist a b := (min_le_right _ _).trans (min_le_right _ _)
  have hba : ball a r ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hballa
  have hbb : ball b r ⊆ U :=
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))).trans hballb
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous q.continuous) r hr
  let τ : ℝ := min δ (1 / 2) / 2
  have hτ : 0 < τ := half_pos (lt_min hδ (by norm_num))
  have hτδ : τ < δ := (half_lt_self (lt_min hδ (by norm_num))).trans_le
    (min_le_left _ _)
  have hτhalf : τ < 1 / 2 :=
    (half_lt_self (lt_min hδ (by norm_num))).trans_le (min_le_right _ _)
  let t₀ : I := ⟨τ, ⟨hτ.le, by linarith⟩⟩
  let t₁ : I := σ t₀
  have ht₀ : 0 < t₀ := hτ
  have ht₁ : t₁ < 1 := by change 1 - τ < 1; linarith
  have ht : t₀ < t₁ := by change τ < 1 - τ; linarith
  have hdist₀ : dist t₀ (0 : I) < δ := by
    change |τ - 0| < δ
    simpa only [sub_zero, abs_of_pos hτ] using hτδ
  have hdist₁ : dist t₁ (1 : I) < δ := by
    change |(1 - τ) - 1| < δ
    rw [show (1 - τ) - 1 = -τ by ring, abs_neg, abs_of_pos hτ]
    exact hτδ
  have hqb : q t₀ ∈ ball b r := by
    simpa only [mem_ball, q.source] using hosc hdist₀
  have hqa : q t₁ ∈ ball a r := by
    simpa only [mem_ball, q.target] using hosc hdist₁
  have havoid (t : I) (ht : t ∈ openParams) : q t ∉ segment ℝ a b := by
    intro hmem
    have hx : q t ∈ ({a, b} : Set ℂ) := hint ▸ ⟨hmem, mem_range_self t⟩
    rcases hx with hx | hx
    · have heq : t = 1 := hqi (hx.trans q.target.symm)
      exact (ne_of_lt ht.2) (congrArg Subtype.val heq)
    · have heq : t = 0 := hqi (hx.trans q.source.symm)
      exact (ne_of_gt ht.1) (congrArg Subtype.val heq)
  let O := U ∩ (segment ℝ a b)ᶜ
  have hchord : IsClosed (segment ℝ a b) := by
    rw [← Path.range_segment a b]
    exact (isCompact_range (Path.segment a b).continuous).isClosed
  have hO : IsOpen O := hU.inter hchord.isOpen_compl
  have hmid : Set.range (edgeSubarc q t₀ t₁ ht.le) ⊆ O :=
    range_edgeSubarc_subset_of_open_traversal32 (U := O) q
      (fun t h => ⟨hqU (mem_range_self t), havoid t h⟩) t₀ t₁ ht₀ ht₁ ht.le
  obtain ⟨_, m, hms, hmf, _, hmO, _⟩ :=
    exists_polygonal_approx_homotopy_in_open32 (edgeSubarc q t₀ t₁ ht.le)
      hO hmid (show (0 : ℝ) < 1 by norm_num)
  let l : Polyline := ⟨[b, q t₀], by simp⟩
  let k : Polyline := ⟨[q t₁, a], by simp⟩
  have hlm : l.finish = m.start := hms.symm
  have hmk : (l.boundaryConcat m).finish = k.start :=
    (Polyline.finish_boundaryConcat_of_join l m hlm).trans hmf
  let p₀ := (l.boundaryConcat m).boundaryConcat k
  have hp₀s : p₀.start = b := by
    simp only [p₀, Polyline.start_boundaryConcat]; rfl
  have hp₀f : p₀.finish = a :=
    Polyline.finish_boundaryConcat_of_join _ _ hmk
  have hp₀im : p₀.image = segment ℝ b (q t₀) ∪ m.image ∪ segment ℝ (q t₁) a := by
    rw [Polyline.image_boundaryConcat _ _ hmk,
      Polyline.image_boundaryConcat _ _ hlm, image_twoPoint19,
      image_twoPoint19]
  have hlU : segment ℝ b (q t₀) ⊆ U :=
    ((convex_ball b r).segment_subset (mem_ball_self hr) hqb).trans hbb
  have hkU : segment ℝ (q t₁) a ⊆ U :=
    ((convex_ball a r).segment_subset hqa (mem_ball_self hr)).trans hba
  have hp₀U : p₀.image ⊆ U := by
    rw [hp₀im]
    exact union_subset (union_subset hlU (hmO.trans inter_subset_left)) hkU
  have hlint := segment_inter_short_connector32 a b (q t₀) hr hrab hqb
    (havoid t₀ ⟨ht₀, ht.trans ht₁⟩)
  have hkint : segment ℝ a b ∩ segment ℝ (q t₁) a = {a} := by
    rw [segment_symm ℝ a b, segment_symm ℝ (q t₁) a]
    apply segment_inter_short_connector32 b a (q t₁) hr
      (by simpa only [dist_comm] using hrab) hqa
    simpa only [segment_symm ℝ b a] using havoid t₁ ⟨ht₀.trans ht, ht₁⟩
  have hp₀inter : segment ℝ a b ∩ p₀.image ⊆ ({a, b} : Set ℂ) := by
    intro z hz
    rw [hp₀im] at hz
    rcases hz.2 with (hl | hm) | hk
    · exact Or.inr (mem_singleton_iff.mp (hlint ▸ ⟨hz.1, hl⟩))
    · exact False.elim ((hmO hm).2 hz.1)
    · exact Or.inl (mem_singleton_iff.mp (hkint ▸ ⟨hz.1, hk⟩))
  obtain ⟨p, hp, hps, hpf, hpim, hlen, _⟩ :=
    p₀.exists_simple_subimage32 (by rw [hp₀s, hp₀f]; exact hab.symm)
  have hs : p.start = b := hps.trans hp₀s
  have hf : p.finish = a := hpf.trans hp₀f
  refine ⟨p, hp, hs, hf, hlen, hpim.trans hp₀U, Subset.antisymm ?_ ?_⟩
  · exact fun z hz => hp₀inter ⟨hz.1, hpim hz.2⟩
  · intro z hz
    rcases hz with hz | hz
    · rw [hz]
      refine ⟨left_mem_segment ℝ a b, ?_⟩
      rw [← hf, ← p.range_toPath]
      exact ⟨1, p.toPath.target⟩
    · rw [mem_singleton_iff] at hz
      rw [hz]
      refine ⟨right_mem_segment ℝ a b, ?_⟩
      rw [← hs, ← p.range_toPath]
      exact ⟨0, p.toPath.source⟩

/-- Helper toward Definition 3.2: a simple continuous return to a straight
chord admits a simple polygonal replacement meeting the chord only at its
endpoints and preserving every winding integer at a prescribed viewpoint. -/
theorem exists_simple_polyline_return_same_winding_disjoint32
    {a b : ℂ} (hab : a ≠ b) (q : Path b a)
    (hqi : Function.Injective q)
    (hint : segment ℝ a b ∩ Set.range q = ({a, b} : Set ℂ))
    (w : ℂ) (hw : w ∉ segment ℝ a b ∪ Set.range q) :
    ∃ p : Polyline, p.IsSimple ∧ ∃ (hs : b = p.start) (ht : a = p.finish),
      2 ≤ p.points.length ∧
      segment ℝ a b ∩ p.image = ({a, b} : Set ℂ) ∧
      ∀ n : ℤ, HasWinding ((Path.segment a b).trans q) w n ↔
        HasWinding ((Path.segment a b).trans (p.toPath.cast hs ht)) w n := by
  obtain ⟨U, hU, hqU, f, hf⟩ := exists_log_neighborhood_of_injective_path32
    q hqi w (fun h => hw (Or.inr h))
  obtain ⟨p, hp, hps, hpf, hlen, hpU, hpint⟩ :=
    exists_simple_polyline_return_disjoint_in_open32 hab q hqi hint U hU hqU
  have hbU : b ∈ U := hqU ⟨0, q.source⟩
  have haU : a ∈ U := hqU ⟨1, q.target⟩
  have hpU' : Set.range (p.toPath.cast hps.symm hpf.symm) ⊆ U := by
    rintro z ⟨t, rfl⟩
    apply hpU
    rw [← p.range_toPath]
    exact mem_range_self t
  have hqlog := hasLiftIncrement_of_log_on_set32 f w hf hbU haU q hqU
  have hplog := hasLiftIncrement_of_log_on_set32 f w hf hbU haU
    (p.toPath.cast hps.symm hpf.symm) hpU'
  have hlift (v : ℂ) : HasLiftIncrement q w v ↔
      HasLiftIncrement (p.toPath.cast hps.symm hpf.symm) w v := by
    constructor
    · intro hv
      exact (hasLiftIncrement_unique32 hqlog hv) ▸ hplog
    · intro hv
      exact (hasLiftIncrement_unique32 hplog hv) ▸ hqlog
  refine ⟨p, hp, hps.symm, hpf.symm, hlen, hpint, fun n => ?_⟩
  change HasLiftIncrement _ w (2 * Real.pi * Complex.I * (n : ℤ)) ↔
    HasLiftIncrement _ w (2 * Real.pi * Complex.I * (n : ℤ))
  rw [hasLiftIncrement_trans_iff, hasLiftIncrement_trans_iff]
  simp only [hlift]

/-- Helper toward Definition 3.2: a straight chord with an injective
continuous return meeting it only at the endpoints has winding between
minus one and one. The replacement may depend on the viewpoint. -/
theorem segment_injective_return_hasWinding_bounds32 {a b : ℂ}
    (hab : a ≠ b) (q : Path b a) (hqi : Function.Injective q)
    (hint : segment ℝ a b ∩ Set.range q = ({a, b} : Set ℂ))
    (w : ℂ) (n : ℤ) (hw : HasWinding ((Path.segment a b).trans q) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  have havoid : w ∉ segment ℝ a b ∪ Set.range q := by
    rw [← Path.range_segment a b, ← Path.trans_range]
    exact hw.not_mem_range
  obtain ⟨p, hp, hs, ht, hlen, hpint, heq⟩ :=
    exists_simple_polyline_return_same_winding_disjoint32 hab q hqi hint w havoid
  exact segment_polyline_return_hasWinding_bounds32 hab p hp hlen hs ht hpint w n
    ((heq n).mp hw)

/-- Helper toward Definition 3.2: winding one cannot accumulate from the
right of a straight chord with an injective continuous return, and winding
minus one cannot accumulate from the left. -/
theorem not_mem_closure_wrong_side_segment_injective_return32 {a b x : ℂ}
    (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b)
    (q : Path b a) (hqi : Function.Injective q)
    (hint : segment ℝ a b ∩ Set.range q = ({a, b} : Set ℂ)) :
    x ∉ closure {w : ℂ | HasWinding ((Path.segment a b).trans q) w 1 ∧
        (star (b - a) * (w - x)).im < 0} ∧
    x ∉ closure {w : ℂ | HasWinding ((Path.segment a b).trans q) w (-1) ∧
        0 < (star (b - a) * (w - x)).im} := by
  have hxa : x ≠ a := fun h => hab (left_mem_openSegment_iff.mp (h ▸ hx))
  have hxb : x ≠ b := fun h => hab (right_mem_openSegment_iff.mp (h ▸ hx))
  have hxq : x ∉ Set.range q := by
    intro hxq
    have hmem : x ∈ ({a, b} : Set ℂ) := hint ▸ ⟨openSegment_subset_segment ℝ a b hx, hxq⟩
    rcases hmem with h | h
    · exact hxa h
    · exact hxb h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (isCompact_range q.continuous).isClosed.isOpen_compl x hxq
  have hdisj : Disjoint (ball x r) (Set.range q) :=
    disjoint_left.mpr (fun _ hw => hball hw)
  constructor
  · intro hcl
    have htwo := (mem_closure_segment_return_winding_iff32 hab hx hr q hdisj 1).mpr hcl
    obtain ⟨w, hw, _⟩ := Metric.mem_closure_iff.mp htwo 1 zero_lt_one
    have hbound := segment_injective_return_hasWinding_bounds32 hab q hqi hint w 2 hw.1
    omega
  · intro hcl
    have hcl' : x ∈ closure {w : ℂ | HasWinding ((Path.segment a b).trans q)
        w ((-2 : ℤ) + 1) ∧ 0 < (star (b - a) * (w - x)).im} := by
      norm_num only
      exact hcl
    have hminus := (mem_closure_segment_return_winding_iff32 hab hx hr q hdisj (-2)).mp hcl'
    obtain ⟨w, hw, _⟩ := Metric.mem_closure_iff.mp hminus 1 zero_lt_one
    have hbound := segment_injective_return_hasWinding_bounds32 hab q hqi hint w (-2) hw.1
    omega

/-- Helper toward Definition 3.2: the winding bound for continuous simple
returns also holds after the constant pauses of an affine subarc. -/
theorem edgeSubarc_affine_injective_return_hasWinding_bounds32 {x y : ℂ}
    (γ : Path x y) (a b : I) (hab : a < b)
    (hline : ∀ u : I, a ≤ u → u ≤ b →
      γ u = γ a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (γ b - γ a)))
    (hne : γ a ≠ γ b)
    (q : Path (γ b) (γ a)) (hqi : Function.Injective q)
    (hint : segment ℝ (γ a) (γ b) ∩ Set.range q = ({γ a, γ b} : Set ℂ))
    (w : ℂ) (n : ℤ)
    (hw : HasWinding ((edgeSubarc γ a b hab.le).trans q) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  exact segment_injective_return_hasWinding_bounds32 hne q hqi hint w n
    ((edgeSubarc_affine_trans_hasWinding_iff32 γ a b hab hline q w n).mp hw)

/-- Helper toward Definition 3.2: the wrong-side accumulation obstruction
for continuous simple returns survives an affine subarc's pauses. -/
theorem not_mem_closure_wrong_side_edgeSubarc_affine_injective_return32
    {x y z : ℂ} (γ : Path x y) (a b : I) (hab : a < b)
    (hline : ∀ u : I, a ≤ u → u ≤ b →
      γ u = γ a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (γ b - γ a)))
    (hne : γ a ≠ γ b) (hz : z ∈ openSegment ℝ (γ a) (γ b))
    (q : Path (γ b) (γ a)) (hqi : Function.Injective q)
    (hint : segment ℝ (γ a) (γ b) ∩ Set.range q = ({γ a, γ b} : Set ℂ)) :
    z ∉ closure {w : ℂ | HasWinding ((edgeSubarc γ a b hab.le).trans q) w 1 ∧
        (star (γ b - γ a) * (w - z)).im < 0} ∧
    z ∉ closure {w : ℂ | HasWinding ((edgeSubarc γ a b hab.le).trans q) w (-1) ∧
        0 < (star (γ b - γ a) * (w - z)).im} := by
  simpa only [edgeSubarc_affine_trans_hasWinding_iff32 γ a b hab hline] using
    not_mem_closure_wrong_side_segment_injective_return32 hne hz q hqi hint



























































































































end DirectedDistances.PlanarMap

end
