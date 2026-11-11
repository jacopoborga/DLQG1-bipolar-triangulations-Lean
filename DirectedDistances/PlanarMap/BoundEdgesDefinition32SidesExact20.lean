/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact19
import DirectedDistances.PlanarMap.D39PLCornerAccessArc
import DirectedDistances.PlanarMap.D39PLOrientedPlaneHomeomorph

/-! # Unpaused polygonal subarcs toward Definition 3.2 -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

/-- Helper toward Definition 3.2: the increasing affine parameter map
onto a selected closed interval. -/
@[expose] def intervalParam20 (a b : I) (hab : a ≤ b) (t : I) : I :=
  ⟨(a : ℝ) + (t : ℝ) * ((b : ℝ) - a), by
    constructor
    · exact a.2.1.trans (le_add_of_nonneg_right
        (mul_nonneg t.2.1 (sub_nonneg.mpr hab)))
    · calc
        (a : ℝ) + (t : ℝ) * ((b : ℝ) - a) ≤ a + 1 * ((b : ℝ) - a) :=
          add_le_add_right (mul_le_mul_of_nonneg_right t.2.2 (sub_nonneg.mpr hab)) _
        _ = (b : ℝ) := by ring
        _ ≤ 1 := b.2.2⟩

private theorem intervalParam20_zero (a b : I) (hab : a ≤ b) :
    intervalParam20 a b hab 0 = a := by
  apply Subtype.ext
  simp [intervalParam20]

private theorem intervalParam20_one (a b : I) (hab : a ≤ b) :
    intervalParam20 a b hab 1 = b := by
  apply Subtype.ext
  simp [intervalParam20]

/-- Helper toward Definition 3.2: traverse a selected parameter interval
without the constant pauses of `edgeSubarc`, retaining every bend. -/
@[expose] def linearSubarc32 {x y : ℂ} (γ : Path x y)
    (a b : I) (hab : a ≤ b) : Path (γ a) (γ b) where
  toFun t := γ (intervalParam20 a b hab t)
  continuous_toFun := γ.continuous.comp (by unfold intervalParam20; fun_prop)
  source' := by rw [intervalParam20_zero]
  target' := by rw [intervalParam20_one]

/-- Helper toward Definition 3.2: removing pauses preserves injectivity
on every nondegenerate interval of an injective path. -/
theorem linearSubarc32_injective {x y : ℂ} (γ : Path x y)
    (hγ : Function.Injective γ) (a b : I) (hab : a < b) :
    Function.Injective (linearSubarc32 γ a b hab.le) := by
  intro s t hst
  have h := congrArg Subtype.val (hγ hst)
  change (a : ℝ) + (s : ℝ) * ((b : ℝ) - a) =
    a + (t : ℝ) * ((b : ℝ) - a) at h
  apply Subtype.ext
  exact mul_right_cancel₀ (sub_ne_zero.mpr
    (ne_of_gt (show (a : ℝ) < b from hab)))
    (add_left_cancel h)

/-- Helper toward Definition 3.2: the exact image of a paused subarc is
the original path's image of the selected closed parameter interval. -/
theorem range_edgeSubarc_eq_image_Icc32 {x y : ℂ} (γ : Path x y)
    (a b : I) (hab : a ≤ b) :
    Set.range (edgeSubarc γ a b hab) = γ '' Set.Icc a b := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [edgeSubarc_apply_clamp]
    exact ⟨min (max t a) b,
      ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_⟩
    rw [edgeSubarc_apply_clamp, max_eq_left ht.1, min_eq_left ht.2]

/-- Helper toward Definition 3.2: an arbitrary subarc, including one
crossing several polygonal segments, has unchanged winding after its
constant pauses are removed. The original return is retained. -/
theorem edgeSubarc_linearSubarc_trans_hasWinding_iff32 {x y : ℂ}
    (γ : Path x y) (a b : I) (hab : a < b)
    (q : Path (γ b) (γ a)) (w : ℂ) (n : ℤ) :
    HasWinding ((edgeSubarc γ a b hab.le).trans q) w n ↔
      HasWinding ((linearSubarc32 γ a b hab.le).trans q) w n := by
  have habR : (a : ℝ) < b := hab
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
  have heq : edgeSubarc γ a b hab.le =
      (linearSubarc32 γ a b hab.le).reparam g hgc hg0 hg1 := by
    apply Path.ext
    funext t
    rw [edgeSubarc_apply_clamp]
    change γ (min (max t a) b) = γ (intervalParam20 a b hab.le (g t))
    congr 1
    apply Subtype.ext
    dsimp [intervalParam20, g]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr habR.ne')]
    ring
  rw [heq]
  exact hasWinding_trans_reparam_left_continuous_iff32 _ q g hgc hg0 hg1 w n

/-- Helper toward Definition 3.2: every injective path contained in an
injective arc traverses exactly the interval between its endpoint parameters.
No polygonal, side, or winding premise is required. -/
theorem range_injective_path_subset_arc_eq_image_Icc32 {x y : ℂ}
    (γ : Path x y) (hγ : Function.Injective γ) (a b : I) (hab : a ≤ b)
    (δ : Path (γ a) (γ b)) (hδ : Function.Injective δ)
    (hsub : Set.range δ ⊆ Set.range γ) :
    Set.range δ = γ '' Set.Icc a b := by
  let e : I ≃ₜ Set.range γ :=
    (γ.continuous.isClosedEmbedding hγ).isEmbedding.toHomeomorph
  let f : I → I := fun t => e.symm ⟨δ t, hsub (mem_range_self t)⟩
  have hfc : Continuous f :=
    e.symm.continuous.comp (δ.continuous.subtype_mk _)
  have hmatch (t : I) : γ (f t) = δ t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨δ t, hsub (mem_range_self t)⟩)
  have hf0 : f 0 = a := hγ ((hmatch 0).trans δ.source)
  have hf1 : f 1 = b := hγ ((hmatch 1).trans δ.target)
  have hfi : Function.Injective f := by
    intro s t hst
    apply hδ
    rw [← hmatch s, ← hmatch t, hst]
  have hmono : StrictMono f :=
    hfc.strictMono_of_inj_boundedOrder
      (by change f 0 ≤ f 1; rw [hf0, hf1]; exact hab) hfi
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨f t, ⟨?_, ?_⟩, hmatch t⟩
    · rw [← hf0]; exact hmono.monotone t.2.1
    · rw [← hf1]; exact hmono.monotone t.2.2
  · rintro ⟨t, ht, rfl⟩
    have ht' : t ∈ Set.Icc (f 0) (f 1) := by rwa [hf0, hf1]
    obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) 1 hfc ht'
    exact ⟨u, (hmatch u).symm.trans (congrArg γ hu)⟩

/-- Helper toward Definition 3.2: cutting a simple polyline at arbitrary
ordered parameters yields a simple polyline with exactly the selected
subarc image, including both endpoints and every intervening bend. -/
theorem exists_simple_polyline_image_edgeSubarc32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (a b : I) (hab : a < b) :
    ∃ r : Polyline, r.IsSimple ∧ r.start = p.toPath a ∧
      r.finish = p.toPath b ∧ 2 ≤ r.points.length ∧
      r.image = Set.range (edgeSubarc p.toPath a b hab.le) := by
  have hpi := p.toPath_injective hlen hp
  have hb0 : b ≠ 0 := ne_of_gt ((show (0 : I) ≤ a from a.2.1).trans_lt hab)
  have hbs : p.toPath b ≠ p.start := by
    intro heq
    exact hb0 (hpi (heq.trans p.toPath.source.symm))
  obtain ⟨r, hr, hrs, hrf, hrsub, _⟩ :=
    p.exists_simple_prefix_preserving_arg hp
      (p.range_toPath ▸ mem_range_self b) hbs
  have hrlen : 2 ≤ r.points.length :=
    Polyline.length_two_of_start_ne_finish r (by rw [hrs, hrf]; exact hbs.symm)
  let δ : Path (p.toPath 0) (p.toPath b) :=
    r.toPath.cast (p.toPath.source.trans hrs.symm) hrf.symm
  have hδsub : Set.range δ ⊆ Set.range p.toPath := by
    simpa only [δ, Path.cast_coe, Polyline.range_toPath] using hrsub
  have hrim : r.image = p.toPath '' Set.Icc (0 : I) b := by
    have hh := range_injective_path_subset_arc_eq_image_Icc32 p.toPath hpi 0 b
      b.2.1 δ (r.toPath_injective hrlen hr) hδsub
    simpa only [δ, Path.cast_coe, Polyline.range_toPath] using hh
  have har : p.toPath a ∈ r.image := by
    rw [hrim]
    exact ⟨a, ⟨a.2.1, hab.le⟩, rfl⟩
  obtain ⟨s, hs, hss, hsf, hsr⟩ := r.exists_simple_suffix hr har
  have hsf' : s.finish = p.toPath b := hsf.trans hrf
  have hslen : 2 ≤ s.points.length :=
    Polyline.length_two_of_start_ne_finish s (by
      rw [hss, hsf']; exact fun heq => hab.ne (hpi heq))
  let ε : Path (p.toPath a) (p.toPath b) := s.toPath.cast hss.symm hsf'.symm
  have hεsub : Set.range ε ⊆ Set.range p.toPath := by
    simpa only [ε, Path.cast_coe, Polyline.range_toPath] using hsr.trans hrsub
  have hsim := range_injective_path_subset_arc_eq_image_Icc32 p.toPath hpi a b
    hab.le ε (s.toPath_injective hslen hs) hεsub
  refine ⟨s, hs, hss, hsf', hslen, ?_⟩
  rw [range_edgeSubarc_eq_image_Icc32]
  simpa only [ε, Path.cast_coe, Polyline.range_toPath] using hsim

/-- Helper toward Definition 3.2: any path in the image of an injective
arc with the same endpoints has exactly that arc's logarithmic increments
at every viewpoint off the arc. -/
theorem hasLiftIncrement_iff_of_range_subset_injective_path32 {x y : ℂ}
    (α : Path x y) (hα : Function.Injective α) (δ : Path x y)
    (hsub : Set.range δ ⊆ Set.range α)
    (w : ℂ) (hw : w ∉ Set.range α) (v : ℂ) :
    HasLiftIncrement α w v ↔ HasLiftIncrement δ w v := by
  obtain ⟨U, _, hαU, f, hf⟩ :=
    exists_log_neighborhood_of_injective_path32 α hα w hw
  have hxU : x ∈ U := hαU ⟨0, α.source⟩
  have hyU : y ∈ U := hαU ⟨1, α.target⟩
  have hαlog := hasLiftIncrement_of_log_on_set32 f w hf hxU hyU α hαU
  have hδlog := hasLiftIncrement_of_log_on_set32 f w hf hxU hyU δ (hsub.trans hαU)
  constructor
  · intro hv
    exact (hasLiftIncrement_unique32 hαlog hv) ▸ hδlog
  · intro hv
    exact (hasLiftIncrement_unique32 hδlog hv) ▸ hαlog

/-- Helper toward Definition 3.2: replacing an injective arc by a path
with the same endpoints and image preserves every winding of its loop
with an unchanged return. -/
theorem hasWinding_trans_iff_of_same_injective_arc_image32 {x y : ℂ}
    (α : Path x y) (hα : Function.Injective α) (δ : Path x y)
    (him : Set.range δ = Set.range α) (q : Path y x) (w : ℂ) (n : ℤ) :
    HasWinding (α.trans q) w n ↔ HasWinding (δ.trans q) w n := by
  by_cases hw : w ∈ Set.range α
  · have hαno : ¬ HasWinding (α.trans q) w n := fun h =>
      h.not_mem_range (by rw [Path.trans_range]; exact Or.inl hw)
    have hδno : ¬ HasWinding (δ.trans q) w n := fun h =>
      h.not_mem_range (by rw [Path.trans_range, him]; exact Or.inl hw)
    exact iff_of_false hαno hδno
  · change HasLiftIncrement _ w (2 * Real.pi * Complex.I * (n : ℤ)) ↔
      HasLiftIncrement _ w (2 * Real.pi * Complex.I * (n : ℤ))
    rw [hasLiftIncrement_trans_iff, hasLiftIncrement_trans_iff]
    simp only [hasLiftIncrement_iff_of_range_subset_injective_path32
      α hα δ him.subset w hw]

/-- Helper toward Definition 3.2: sufficiently short straight connectors
from either endpoint of a simple polyline to a point off its image meet
that entire image only at the endpoint. -/
theorem exists_ball_connector_inter_simple_polyline32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (b : ℂ) (hb : b = p.start ∨ b = p.finish) :
    ∃ r : ℝ, 0 < r ∧ ∀ c ∈ ball b r, c ∉ p.image →
      p.image ∩ segment ℝ b c = {b} := by
  classical
  let K : ℕ → Set ℂ := fun i =>
    if b = p.point i then {p.point (i + 1)}
    else if b = p.point (i + 1) then {p.point i} else p.segmentAt i
  let T : Set ℂ := ⋃ i ∈ Finset.range (p.points.length - 1), K i
  have hKclosed (i : ℕ) : IsClosed (K i) := by
    dsimp [K]
    split_ifs
    · exact isClosed_singleton
    · exact isClosed_singleton
    · rw [Polyline.segmentAt, ← Path.range_segment]
      exact (isCompact_range (Path.segment _ _).continuous).isClosed
  have hTclosed : IsClosed T := isClosed_biUnion_finset (fun i _ => hKclosed i)
  have hbK (i : ℕ) (hi : i + 1 < p.points.length) : b ∉ K i := by
    dsimp [K]
    split_ifs with h0 h1
    · intro heq
      exact hp.1 i hi (h0.symm.trans heq)
    · intro heq
      exact hp.1 i hi (heq.symm.trans h1)
    · intro hmem
      exact (p.segmentAt_endpoint_of_arc_endpoint hp hlen i hi hmem hb).elim h0 h1
  have hbT : b ∉ T := by
    intro h
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.mp h
    exact hbK i (by have := Finset.mem_range.mp hi; omega) hbi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hTclosed.isOpen_compl b hbT
  refine ⟨r, hr, fun c hc hcout => Subset.antisymm ?_ ?_⟩
  · intro z hz
    apply mem_singleton_iff.mpr
    by_contra hzb
    have hzball : z ∈ ball b r :=
      (convex_ball b r).segment_subset (mem_ball_self hr) hc hz.2
    obtain ⟨i, hi, hzi⟩ : ∃ i, i + 1 < p.points.length ∧ z ∈ p.segmentAt i := by
      rcases hz.1 with hzs | hzs
      · refine ⟨0, by omega, ?_⟩
        have hzstart : z = p.start := hzs
        rw [hzstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact hzs
    have hiT : i ∈ Finset.range (p.points.length - 1) := Finset.mem_range.mpr (by omega)
    have hnotK (v : ℂ) (hv : v ∈ ball b r) : v ∉ K i := by
      intro hvi
      exact hball hv (mem_iUnion₂.mpr ⟨i, hiT, hvi⟩)
    by_cases h0 : b = p.point i
    · have hseg : z ∈ segment ℝ (p.point (i + 1)) b := by
        simpa only [Polyline.segmentAt, ← h0, segment_symm ℝ b] using hzi
      rcases mem_segment_or_mem_segment_of_common_point32 _ b c z hseg hz.2 hzb with h | h
      · apply hcout
        apply p.segmentAt_subset_image hi
        simpa only [Polyline.segmentAt, ← h0, segment_symm ℝ b] using h
      · apply hnotK _ ((convex_ball b r).segment_subset (mem_ball_self hr) hc h)
        simp only [K, ite_eq_left h0, mem_singleton_iff]
    · by_cases h1 : b = p.point (i + 1)
      · have hseg : z ∈ segment ℝ (p.point i) b := by
          simpa only [Polyline.segmentAt, ← h1] using hzi
        rcases mem_segment_or_mem_segment_of_common_point32 _ b c z hseg hz.2 hzb with h | h
        · apply hcout
          apply p.segmentAt_subset_image hi
          simpa only [Polyline.segmentAt, ← h1] using h
        · apply hnotK _ ((convex_ball b r).segment_subset (mem_ball_self hr) hc h)
          simp only [K, ite_eq_right h0, ite_eq_left h1, mem_singleton_iff]
      · exact hnotK z hzball (by simpa only [K, ite_eq_right h0, ite_eq_right h1] using hzi)
  · intro z hz
    rw [mem_singleton_iff] at hz
    subst z
    refine ⟨?_, left_mem_segment ℝ _ _⟩
    rcases hb with rfl | rfl
    · exact Or.inl rfl
    · rw [← p.range_toPath]
      exact ⟨1, p.toPath.target⟩

private theorem image_twoPoint20 (x y : ℂ) :
    (⟨[x, y], by simp⟩ : Polyline).image = segment ℝ x y := by
  rw [← Polyline.range_toPath]
  exact Path.range_segment x y

/-- Helper toward Definition 3.2: a continuous simple return to a simple
polyline admits a simple polygonal replacement in every open neighborhood
of the return, with exactly the original endpoint contacts. -/
theorem exists_simple_polyline_return_disjoint_polyline_in_open32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (q : Path p.finish p.start) (hqi : Function.Injective q)
    (hint : p.image ∩ Set.range q = ({p.start, p.finish} : Set ℂ))
    (U : Set ℂ) (hU : IsOpen U) (hqU : Set.range q ⊆ U) :
    ∃ r : Polyline, r.IsSimple ∧ r.start = p.finish ∧ r.finish = p.start ∧
      2 ≤ r.points.length ∧ r.image ⊆ U ∧
      p.image ∩ r.image = ({p.start, p.finish} : Set ℂ) := by
  have hne : p.start ≠ p.finish := by
    intro h
    have h01 := p.toPath_injective hlen hp (p.toPath.source.trans (h.trans p.toPath.target.symm))
    exact zero_ne_one h01
  obtain ⟨ra, hra, hballa⟩ := Metric.isOpen_iff.mp hU p.start (hqU ⟨1, q.target⟩)
  obtain ⟨rb, hrb, hballb⟩ := Metric.isOpen_iff.mp hU p.finish (hqU ⟨0, q.source⟩)
  obtain ⟨sa, hsa, hcona⟩ :=
    exists_ball_connector_inter_simple_polyline32 p hp hlen p.start (Or.inl rfl)
  obtain ⟨sb, hsb, hconb⟩ :=
    exists_ball_connector_inter_simple_polyline32 p hp hlen p.finish (Or.inr rfl)
  let ρ := min (min ra rb) (min sa sb)
  have hρ : 0 < ρ := lt_min (lt_min hra hrb) (lt_min hsa hsb)
  have hρra : ρ ≤ ra := (min_le_left _ _).trans (min_le_left _ _)
  have hρrb : ρ ≤ rb := (min_le_left _ _).trans (min_le_right _ _)
  have hρsa : ρ ≤ sa := (min_le_right _ _).trans (min_le_left _ _)
  have hρsb : ρ ≤ sb := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous q.continuous) ρ hρ
  let τ : ℝ := min δ (1 / 2) / 2
  have hτ : 0 < τ := half_pos (lt_min hδ (by norm_num))
  have hτδ : τ < δ := (half_lt_self (lt_min hδ (by norm_num))).trans_le (min_le_left _ _)
  have hτhalf : τ < 1 / 2 :=
    (half_lt_self (lt_min hδ (by norm_num))).trans_le (min_le_right _ _)
  let t₀ : I := ⟨τ, ⟨hτ.le, by linarith⟩⟩
  let t₁ : I := σ t₀
  have ht₀ : 0 < t₀ := hτ
  have ht₁ : t₁ < 1 := by change 1 - τ < 1; linarith
  have ht : t₀ < t₁ := by change τ < 1 - τ; linarith
  have hd₀ : dist t₀ (0 : I) < δ := by
    change |τ - 0| < δ
    simpa only [sub_zero, abs_of_pos hτ] using hτδ
  have hd₁ : dist t₁ (1 : I) < δ := by
    change |(1 - τ) - 1| < δ
    rw [show (1 - τ) - 1 = -τ by ring, abs_neg, abs_of_pos hτ]
    exact hτδ
  have hqb : q t₀ ∈ ball p.finish ρ := by
    simpa only [mem_ball, q.source] using hosc hd₀
  have hqa : q t₁ ∈ ball p.start ρ := by
    simpa only [mem_ball, q.target] using hosc hd₁
  have havoid (t : I) (ht : t ∈ openParams) : q t ∉ p.image := by
    intro hmem
    have hx : q t ∈ ({p.start, p.finish} : Set ℂ) := hint ▸ ⟨hmem, mem_range_self t⟩
    rcases hx with hx | hx
    · have heq : t = 1 := hqi (hx.trans q.target.symm)
      exact (ne_of_lt ht.2) (congrArg Subtype.val heq)
    · have heq : t = 0 := hqi (hx.trans q.source.symm)
      exact (ne_of_gt ht.1) (congrArg Subtype.val heq)
  let O := U ∩ p.imageᶜ
  have hO : IsOpen O := hU.inter p.isCompact_image.isClosed.isOpen_compl
  have hmid : Set.range (edgeSubarc q t₀ t₁ ht.le) ⊆ O :=
    range_edgeSubarc_subset_of_open_traversal32 (U := O) q
      (fun t h => ⟨hqU (mem_range_self t), havoid t h⟩) t₀ t₁ ht₀ ht₁ ht.le
  obtain ⟨_, m, hms, hmf, _, hmO, _⟩ :=
    exists_polygonal_approx_homotopy_in_open32 (edgeSubarc q t₀ t₁ ht.le)
      hO hmid (show (0 : ℝ) < 1 by norm_num)
  let l : Polyline := ⟨[p.finish, q t₀], by simp⟩
  let k : Polyline := ⟨[q t₁, p.start], by simp⟩
  have hlm : l.finish = m.start := hms.symm
  have hmk : (l.boundaryConcat m).finish = k.start :=
    (Polyline.finish_boundaryConcat_of_join l m hlm).trans hmf
  let r₀ := (l.boundaryConcat m).boundaryConcat k
  have hr₀s : r₀.start = p.finish := by
    simp only [r₀, Polyline.start_boundaryConcat]; rfl
  have hr₀f : r₀.finish = p.start := Polyline.finish_boundaryConcat_of_join _ _ hmk
  have hr₀im : r₀.image = segment ℝ p.finish (q t₀) ∪ m.image ∪ segment ℝ (q t₁) p.start := by
    rw [Polyline.image_boundaryConcat _ _ hmk,
      Polyline.image_boundaryConcat _ _ hlm, image_twoPoint20, image_twoPoint20]
  have hlU : segment ℝ p.finish (q t₀) ⊆ U :=
    ((convex_ball p.finish ρ).segment_subset (mem_ball_self hρ) hqb).trans
      ((ball_subset_ball hρrb).trans hballb)
  have hkU : segment ℝ (q t₁) p.start ⊆ U :=
    ((convex_ball p.start ρ).segment_subset hqa (mem_ball_self hρ)).trans
      ((ball_subset_ball hρra).trans hballa)
  have hr₀U : r₀.image ⊆ U := by
    rw [hr₀im]
    exact union_subset (union_subset hlU (hmO.trans inter_subset_left)) hkU
  have hlint := hconb (q t₀) (ball_subset_ball hρsb hqb) (havoid t₀ ⟨ht₀, ht.trans ht₁⟩)
  have hkint : p.image ∩ segment ℝ (q t₁) p.start = {p.start} := by
    rw [segment_symm]
    exact hcona (q t₁) (ball_subset_ball hρsa hqa) (havoid t₁ ⟨ht₀.trans ht, ht₁⟩)
  have hr₀inter : p.image ∩ r₀.image ⊆ ({p.start, p.finish} : Set ℂ) := by
    intro z hz
    rw [hr₀im] at hz
    rcases hz.2 with (hl | hm) | hk
    · exact Or.inr (mem_singleton_iff.mp (hlint ▸ ⟨hz.1, hl⟩))
    · exact False.elim ((hmO hm).2 hz.1)
    · exact Or.inl (mem_singleton_iff.mp (hkint ▸ ⟨hz.1, hk⟩))
  obtain ⟨r, hr, hrs, hrf, hrim, hrlen, _⟩ :=
    r₀.exists_simple_subimage32 (by rw [hr₀s, hr₀f]; exact hne.symm)
  have hs : r.start = p.finish := hrs.trans hr₀s
  have hf : r.finish = p.start := hrf.trans hr₀f
  refine ⟨r, hr, hs, hf, hrlen, hrim.trans hr₀U, Subset.antisymm ?_ ?_⟩
  · exact fun z hz => hr₀inter ⟨hz.1, hrim hz.2⟩
  · intro z hz
    rcases hz with hz | hz
    · rw [hz]
      refine ⟨Or.inl rfl, ?_⟩
      rw [← hf, ← r.range_toPath]
      exact ⟨1, r.toPath.target⟩
    · rw [mem_singleton_iff] at hz
      rw [hz]
      constructor
      · rw [← p.range_toPath]; exact ⟨1, p.toPath.target⟩
      · rw [← hs, ← r.range_toPath]; exact ⟨0, r.toPath.source⟩

/-- Helper toward Definition 3.2: a simple polygonal arc closed by an
injective continuous return meeting it only at the endpoints has winding
between minus one and one. -/
theorem simple_polyline_injective_return_hasWinding_bounds32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (q : Path p.finish p.start) (hqi : Function.Injective q)
    (hint : p.image ∩ Set.range q = ({p.start, p.finish} : Set ℂ))
    (w : ℂ) (n : ℤ) (hw : HasWinding (p.toPath.trans q) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  have havoidq : w ∉ Set.range q := by
    intro h
    exact hw.not_mem_range (by rw [Path.trans_range]; exact Or.inr h)
  obtain ⟨U, hU, hqU, f, hf⟩ :=
    exists_log_neighborhood_of_injective_path32 q hqi w havoidq
  obtain ⟨r, hr, hrs, hrf, hrlen, hrU, hrint⟩ :=
    exists_simple_polyline_return_disjoint_polyline_in_open32 p hp hlen q hqi hint U hU hqU
  have hbU : p.finish ∈ U := hqU ⟨0, q.source⟩
  have haU : p.start ∈ U := hqU ⟨1, q.target⟩
  let δ : Path p.finish p.start := r.toPath.cast hrs.symm hrf.symm
  have hδU : Set.range δ ⊆ U := by
    simpa only [δ, Path.cast_coe, Polyline.range_toPath] using hrU
  have hqlog := hasLiftIncrement_of_log_on_set32 f w hf hbU haU q hqU
  have hδlog := hasLiftIncrement_of_log_on_set32 f w hf hbU haU δ hδU
  have hlift (v : ℂ) : HasLiftIncrement q w v ↔ HasLiftIncrement δ w v := by
    constructor
    · intro hv; exact (hasLiftIncrement_unique32 hqlog hv) ▸ hδlog
    · intro hv; exact (hasLiftIncrement_unique32 hδlog hv) ▸ hqlog
  have hw' : HasWinding (p.toPath.trans δ) w n := by
    change HasLiftIncrement _ w (2 * Real.pi * Complex.I * (n : ℤ))
    rw [hasLiftIncrement_trans_iff]
    have h := (hasLiftIncrement_trans_iff p.toPath q).mp hw
    simpa only [hlift] using h
  have hne : p.start ≠ p.finish := by
    intro h
    have h01 := p.toPath_injective hlen hp (p.toPath.source.trans (h.trans p.toPath.target.symm))
    exact zero_ne_one h01
  exact Polyline.trans_hasWinding_bounds32 p r hp hr hlen hrlen hrs.symm hrf.symm
    hne hrint w n hw'

/-- Helper toward Definition 3.2: the winding bound holds for every
selected subarc of a simple polyline, with its original injective continuous
return and its original paused traversal. -/
theorem edgeSubarc_simple_polyline_injective_return_hasWinding_bounds32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (a b : I) (hab : a < b)
    (q : Path (p.toPath b) (p.toPath a)) (hqi : Function.Injective q)
    (hint : Set.range (edgeSubarc p.toPath a b hab.le) ∩ Set.range q =
      ({p.toPath a, p.toPath b} : Set ℂ))
    (w : ℂ) (n : ℤ)
    (hw : HasWinding ((edgeSubarc p.toPath a b hab.le).trans q) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  obtain ⟨r, hr, hrs, hrf, hrlen, hrim⟩ :=
    exists_simple_polyline_image_edgeSubarc32 p hp hlen a b hab
  let α := linearSubarc32 p.toPath a b hab.le
  have hα : Function.Injective α := linearSubarc32_injective _ (p.toPath_injective hlen hp) a b hab
  have hαsub : Set.range α ⊆ Set.range p.toPath := by
    rintro z ⟨t, rfl⟩
    exact mem_range_self (intervalParam20 a b hab.le t)
  have hαim := range_injective_path_subset_arc_eq_image_Icc32 p.toPath
    (p.toPath_injective hlen hp) a b hab.le α hα hαsub
  let δ : Path (p.toPath a) (p.toPath b) := r.toPath.cast hrs.symm hrf.symm
  have hδim : Set.range δ = Set.range α := by
    simp only [δ, Path.cast_coe, Polyline.range_toPath]
    rw [hrim, range_edgeSubarc_eq_image_Icc32, hαim]
  have hwα := (edgeSubarc_linearSubarc_trans_hasWinding_iff32 p.toPath a b hab q w n).mp hw
  have hwδ := (hasWinding_trans_iff_of_same_injective_arc_image32 α hα δ hδim q w n).mp hwα
  let q' : Path r.finish r.start := q.cast hrf hrs
  have hrint : r.image ∩ Set.range q' = ({r.start, r.finish} : Set ℂ) := by
    simpa only [q', Path.cast_coe, hrs, hrf, hrim] using hint
  have hw' : HasWinding (r.toPath.trans q') w n := by
    apply (hasLiftIncrement_congr_fun (δ.trans q) (r.toPath.trans q') (fun _ => rfl)).mp
    exact hwδ
  exact simple_polyline_injective_return_hasWinding_bounds32 r hr hrlen q'
    hqi hrint w n hw'




theorem exists_ball_hasLiftIncrement_iff_of_common_increment32 {a b x c : ℂ}
    (q r : Path a b) (hq : HasLiftIncrement q x c) (hr : HasLiftIncrement r x c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, dist w x < ε →
      ∀ v : ℂ, HasLiftIncrement q w v ↔ HasLiftIncrement r w v := by
  obtain ⟨εq, hεq, hqnear⟩ := hasLiftIncrement_stable_nearby32 q hq
  obtain ⟨εr, hεr, hrnear⟩ := hasLiftIncrement_stable_nearby32 r hr
  refine ⟨min εq εr, lt_min hεq hεr, fun w hw v => ?_⟩
  have hqw := hqnear w (hw.trans_le (min_le_left _ _))
  have hrw := hrnear w (hw.trans_le (min_le_right _ _))
  constructor
  · intro hv; exact (hasLiftIncrement_unique32 hqw hv) ▸ hrw
  · intro hv; exact (hasLiftIncrement_unique32 hrw hv) ▸ hqw

/-- Helper toward Definition 3.2: a return to a simple polyline has a
single simple polygonal replacement preserving all winding integers in a
whole neighborhood of any chosen point off the return. The replacement
also preserves the exact endpoint-only intersection. -/
theorem exists_simple_polyline_return_same_winding_near32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (q : Path p.finish p.start) (hqi : Function.Injective q)
    (hint : p.image ∩ Set.range q = ({p.start, p.finish} : Set ℂ))
    (x : ℂ) (hx : x ∉ Set.range q) :
    ∃ r : Polyline, r.IsSimple ∧ ∃ (hs : p.finish = r.start) (ht : p.start = r.finish),
      2 ≤ r.points.length ∧ p.image ∩ r.image = ({p.start, p.finish} : Set ℂ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, dist w x < ε → ∀ n : ℤ,
        HasWinding (p.toPath.trans q) w n ↔
          HasWinding (p.toPath.trans (r.toPath.cast hs ht)) w n := by
  obtain ⟨U, hU, hqU, f, hf⟩ :=
    exists_log_neighborhood_of_injective_path32 q hqi x hx
  obtain ⟨r, hr, hrs, hrf, hrlen, hrU, hrint⟩ :=
    exists_simple_polyline_return_disjoint_polyline_in_open32 p hp hlen q hqi hint U hU hqU
  have hbU : p.finish ∈ U := hqU ⟨0, q.source⟩
  have haU : p.start ∈ U := hqU ⟨1, q.target⟩
  let δ : Path p.finish p.start := r.toPath.cast hrs.symm hrf.symm
  have hδU : Set.range δ ⊆ U := by
    simpa only [δ, Path.cast_coe, Polyline.range_toPath] using hrU
  have hqlog := hasLiftIncrement_of_log_on_set32 f x hf hbU haU q hqU
  have hδlog := hasLiftIncrement_of_log_on_set32 f x hf hbU haU δ hδU
  obtain ⟨ε, hε, heq⟩ := exists_ball_hasLiftIncrement_iff_of_common_increment32 q δ hqlog hδlog
  refine ⟨r, hr, hrs.symm, hrf.symm, hrlen, hrint, ε, hε, fun w hw n => ?_⟩
  change HasLiftIncrement (p.toPath.trans q) w (2 * Real.pi * Complex.I * (n : ℤ)) ↔
    HasLiftIncrement (p.toPath.trans δ) w (2 * Real.pi * Complex.I * (n : ℤ))
  rw [hasLiftIncrement_trans_iff, hasLiftIncrement_trans_iff]
  simp only [heq w hw]

/-- Helper toward Definition 3.2: the local jump across an oriented
polygon edge has positive sign from right to left. This retains the sign
discarded by the absolute-value polygonal edge-jump theorem. -/
theorem Polyline.exists_signed_angleSum_edge_jump_cyclic32
    (p : Polyline) (hp : p.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u v : ℂ,
      u ∉ p.image → v ∉ p.image → dist u x < ε → dist v x < ε →
      0 < (star (p.point (i + 1) - p.point i) * (u - x)).im →
      (star (p.point (i + 1) - p.point i) * (v - x)).im < 0 →
      p.angleSum u - p.angleSum v = 1 := by
  have hclosed : p.start = p.finish := by
    rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
    exact hp.2.1
  let Lpos := (∑ j ∈ Finset.range (p.points.length - 1),
    if j = i then Real.pi else p.edgeAngle x j) / (2 * Real.pi)
  let Lneg := (∑ j ∈ Finset.range (p.points.length - 1),
    if j = i then -Real.pi else p.edgeAngle x j) / (2 * Real.pi)
  have hLdiff : Lpos - Lneg = 1 := by
    have hiMem : i ∈ Finset.range (p.points.length - 1) := Finset.mem_range.mpr (by omega)
    have hsum :
        (∑ j ∈ Finset.range (p.points.length - 1), if j = i then Real.pi else p.edgeAngle x j) -
        (∑ j ∈ Finset.range (p.points.length - 1), if j = i then -Real.pi else p.edgeAngle x j) =
        2 * Real.pi := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ = (if i = i then Real.pi else p.edgeAngle x i) -
            (if i = i then -Real.pi else p.edgeAngle x i) := by
          apply Finset.sum_eq_single_of_mem i hiMem
          intro j _ hji
          simp only [ite_eq_right hji, sub_self]
        _ = 2 * Real.pi := by simp only [ite_true]; ring
    dsimp [Lpos, Lneg]
    rw [← sub_div, hsum]
    exact div_self (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hpos := p.tendsto_angleSum_nhdsWithin_pos_cyclic hp i hi x hx hxi hxi1
  have hneg := p.tendsto_angleSum_nhdsWithin_neg_cyclic hp i hi x hx hxi hxi1
  have hevpos : ∀ᶠ z : ℂ in 𝓝 x,
      0 < (star (p.point (i + 1) - p.point i) * (z - x)).im →
        dist (p.angleSum z) Lpos < 1 / 4 := by
    have h := hpos.eventually (Metric.ball_mem_nhds Lpos (by norm_num : 0 < (1 / 4 : ℝ)))
    exact eventually_nhdsWithin_iff.mp (by simpa only [mem_ball, Complex.star_def] using h)
  have hevneg : ∀ᶠ z : ℂ in 𝓝 x,
      (star (p.point (i + 1) - p.point i) * (z - x)).im < 0 →
        dist (p.angleSum z) Lneg < 1 / 4 := by
    have h := hneg.eventually (Metric.ball_mem_nhds Lneg (by norm_num : 0 < (1 / 4 : ℝ)))
    exact eventually_nhdsWithin_iff.mp (by simpa only [mem_ball, Complex.star_def] using h)
  obtain ⟨εp, hεp, hnearpos⟩ := Metric.eventually_nhds_iff.mp hevpos
  obtain ⟨εn, hεn, hnearneg⟩ := Metric.eventually_nhds_iff.mp hevneg
  refine ⟨min εp εn, lt_min hεp hεn, fun u v hu hv hux hvx hup hvn => ?_⟩
  have huNear := hnearpos (hux.trans_le (min_le_left _ _)) hup
  have hvNear := hnearneg (hvx.trans_le (min_le_right _ _)) hvn
  have huClose : |p.angleSum u - Lpos| < 1 / 4 := by simpa only [Real.dist_eq] using huNear
  have hvClose : |p.angleSum v - Lneg| < 1 / 4 := by simpa only [Real.dist_eq] using hvNear
  have hclose : |(p.angleSum u - p.angleSum v) - 1| < 1 / 2 := by
    calc
      _ = |(p.angleSum u - Lpos) + -(p.angleSum v - Lneg)| := by congr 1; linarith only [hLdiff]
      _ ≤ |p.angleSum u - Lpos| + |-(p.angleSum v - Lneg)| := abs_add_le _ _
      _ < 1 / 2 := by rw [abs_neg]; linarith only [huClose, hvClose]
  obtain ⟨m, hm⟩ := p.angleSum_isInt hclosed u hu
  obtain ⟨n, hn⟩ := p.angleSum_isInt hclosed v hv
  have hmn := Polyline.int_sub_eq_one_of_abs_lt_half_cyclic m n
    (by simpa only [hm, hn, Int.cast_sub] using hclose)
  rw [hm, hn, ← Int.cast_sub, hmn]
  norm_num

/-- Helper toward Definition 3.2: for a cyclically simple polygon,
angle sum one cannot accumulate from the right of an oriented segment,
and angle sum minus one cannot accumulate from its left. -/
theorem Polyline.not_mem_closure_wrong_side_angleSum_cyclic32
    (p : Polyline) (hp : p.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    x ∉ closure {w : ℂ | w ∉ p.image ∧ p.angleSum w = 1 ∧
      (star (p.point (i + 1) - p.point i) * (w - x)).im < 0} ∧
    x ∉ closure {w : ℂ | w ∉ p.image ∧ p.angleSum w = -1 ∧
      0 < (star (p.point (i + 1) - p.point i) * (w - x)).im} := by
  have hbound (w : ℂ) (hw : w ∉ p.image) :
      -1 ≤ p.angleSum w ∧ p.angleSum w ≤ 1 := by
    by_cases hz : p.angleSum w = 0
    · rw [hz]; constructor <;> norm_num
    · exact abs_le.mp (le_of_eq (p.abs_angleSum_eq_one_of_mem_inside hp w ⟨hw, hz⟩))
  obtain ⟨ε, hε, hjump⟩ := p.exists_signed_angleSum_edge_jump_cyclic32 hp i hi x hx hxi hxi1
  obtain ⟨r, hr, _, _, _, _, _, _, hdisl, hdisr⟩ :=
    p.exists_connected_edge_sides_cyclic hp i hi x hx hxi hxi1
  have hd : p.point (i + 1) - p.point i ≠ 0 := sub_ne_zero.mpr (hp.2.2.1 i hi).symm
  constructor
  · intro hcl
    obtain ⟨v, hv, hvx⟩ := Metric.mem_closure_iff.mp hcl ε hε
    obtain ⟨u, hu⟩ := Polyline.leftHalfDisc_nonempty x _ (min r ε) hd (lt_min hr hε)
    have hu' : u ∈ Polyline.leftHalfDisc x _ r :=
      ⟨ball_subset_ball (min_le_left _ _) hu.1, hu.2⟩
    have huout : u ∉ p.image := fun h => disjoint_left.mp hdisl hu' h
    have huε : dist u x < ε := (mem_ball.mp hu.1).trans_le (min_le_right _ _)
    have hvε : dist v x < ε := by simpa only [dist_comm] using hvx
    have hj := hjump u v huout hv.1 huε hvε hu.2 hv.2.2
    have hb := (hbound u huout).2
    linarith only [hj, hv.2.1, hb]
  · intro hcl
    obtain ⟨u, hu, hux⟩ := Metric.mem_closure_iff.mp hcl ε hε
    obtain ⟨v, hv⟩ := Polyline.rightHalfDisc_nonempty x _ (min r ε) hd (lt_min hr hε)
    have hv' : v ∈ Polyline.rightHalfDisc x _ r :=
      ⟨ball_subset_ball (min_le_left _ _) hv.1, hv.2⟩
    have hvout : v ∉ p.image := fun h => disjoint_left.mp hdisr hv' h
    have hvε : dist v x < ε := (mem_ball.mp hv.1).trans_le (min_le_right _ _)
    have huε : dist u x < ε := by simpa only [dist_comm] using hux
    have hj := hjump u v hu.1 hvout huε hvε hu.2.2 hv.2
    have hb := (hbound v hvout).1
    linarith only [hj, hu.2.1, hb]

/-- Helper toward Definition 3.2: one polygonal replacement of a simple
return preserves winding accumulation at a prescribed point off the return,
simultaneously for every test set and winding integer. It retains exactly
the same endpoint contacts with the original simple polyline. -/
theorem exists_simple_polyline_return_same_winding_accumulation32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (q : Path p.finish p.start) (hqi : Function.Injective q)
    (hint : p.image ∩ Set.range q = ({p.start, p.finish} : Set ℂ))
    (x : ℂ) (hx : x ∉ Set.range q) :
    ∃ r : Polyline, r.IsSimple ∧ ∃ (hs : p.finish = r.start) (ht : p.start = r.finish),
      2 ≤ r.points.length ∧ p.image ∩ r.image = ({p.start, p.finish} : Set ℂ) ∧
      ∀ (F : Set ℂ) (n : ℤ),
        (x ∈ closure {w : ℂ | w ∈ F ∧ HasWinding (p.toPath.trans q) w n}) ↔
        x ∈ closure {w : ℂ | w ∈ F ∧
          HasWinding (p.toPath.trans (r.toPath.cast hs ht)) w n} := by
  obtain ⟨r, hr, hs, ht, hrlen, hrint, ε, hε, heq⟩ :=
    exists_simple_polyline_return_same_winding_near32 p hp hlen q hqi hint x hx
  refine ⟨r, hr, hs, ht, hrlen, hrint, fun F n => ?_⟩
  constructor
  · intro hcl
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp hcl (min δ ε) (lt_min hδ hε)
    have hwε : dist w x < ε := by
      exact (show dist w x < min δ ε by simpa only [dist_comm] using hdist).trans_le
        (min_le_right _ _)
    refine ⟨w, ⟨hw.1, (heq w hwε n).mp hw.2⟩, ?_⟩
    exact hdist.trans_le (min_le_left _ _)
  · intro hcl
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp hcl (min δ ε) (lt_min hδ hε)
    have hwε : dist w x < ε := by
      exact (show dist w x < min δ ε by simpa only [dist_comm] using hdist).trans_le
        (min_le_right _ _)
    refine ⟨w, ⟨hw.1, (heq w hwε n).mpr hw.2⟩, ?_⟩
    exact hdist.trans_le (min_le_left _ _)









































































































end DirectedDistances.PlanarMap

end
