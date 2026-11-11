module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Module






public section
namespace DirectedDistances.PlanarMap

open Set

private theorem complex_finrank : Module.finrank ℝ ℂ = 2 := by
  exact Module.finrank_eq_card_basis Complex.basisOneI



theorem triangle_interior_nonempty (a b c : ℂ)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    (interior (convexHull ℝ ({a, b, c} : Set ℂ))).Nonempty := by
  let : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  have hi : AffineIndependent ℝ ![a, b, c] :=
    affineIndependent_iff_not_collinear_set.mpr hnc
  have ht := hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    (by simp only [Fintype.card_fin, complex_finrank])
  simpa only [Matrix.range_cons, Matrix.range_empty, singleton_union, insert_empty_eq] using ht



theorem isOpen_triangle_interior (a b c : ℂ) :
    IsOpen (interior (convexHull ℝ ({a, b, c} : Set ℂ))) := isOpen_interior



theorem isCompact_triangle (a b c : ℂ) :
    IsCompact (convexHull ℝ ({a, b, c} : Set ℂ)) := by
  exact ((finite_singleton c).insert b |>.insert a).isCompact_convexHull ℝ



theorem isBounded_triangle (a b c : ℂ) :
    Bornology.IsBounded (convexHull ℝ ({a, b, c} : Set ℂ)) :=
  (isCompact_triangle a b c).isBounded



theorem closure_triangle_interior (a b c : ℂ)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    closure (interior (convexHull ℝ ({a, b, c} : Set ℂ))) =
      convexHull ℝ ({a, b, c} : Set ℂ) := by
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    (triangle_interior_nonempty a b c hnc), (isCompact_triangle a b c).isClosed.closure_eq]



theorem openSegment_triangle_interior (a b c : ℂ) {x y : ℂ}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set ℂ))
    (hy : y ∈ interior (convexHull ℝ ({a, b, c} : Set ℂ))) :
    openSegment ℝ x y ⊆ interior (convexHull ℝ ({a, b, c} : Set ℂ)) :=
  (convex_convexHull ℝ _).openSegment_self_interior_subset_interior hx hy



theorem segment_subset_triangle (a b c : ℂ) {x y : ℂ}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set ℂ))
    (hy : y ∈ interior (convexHull ℝ ({a, b, c} : Set ℂ))) :
    segment ℝ x y ⊆ convexHull ℝ ({a, b, c} : Set ℂ) :=
  (convex_convexHull ℝ _).segment_subset hx (interior_subset hy)

private noncomputable def triangleBasis (a b c : ℂ)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : AffineBasis (Fin 3) ℝ ℂ where
  toFun := ![a, b, c]
  ind' := affineIndependent_iff_not_collinear_set.mpr hnc
  tot' := by
    let : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
    have hi := affineIndependent_iff_not_collinear_set.mpr hnc
    exact hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp only [Fintype.card_fin, complex_finrank])

private theorem coord_zero_on_segment (B : AffineBasis (Fin 3) ℝ ℂ)
    {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) {x : ℂ}
    (hx : x ∈ segment ℝ (B i) (B j)) : B.coord k x = 0 := by
  obtain ⟨u, v, _, _, huv, rfl⟩ := hx
  rw [Convex.combo_affine_apply huv, B.coord_apply_ne hki, B.coord_apply_ne hkj]
  simp only [smul_zero, add_zero]



theorem frontier_triangle_interior (a b c : ℂ)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    frontier (interior (convexHull ℝ ({a, b, c} : Set ℂ))) =
      segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  let B := triangleBasis a b c hnc
  have hrange : range B = ({a, b, c} : Set ℂ) := by
    change range ![a, b, c] = _
    simp only [Matrix.range_cons, Matrix.range_empty, singleton_union, insert_empty_eq]
  have hinter : interior (convexHull ℝ ({a, b, c} : Set ℂ)) =
      {x | ∀ i, 0 < B.coord i x} := hrange ▸ B.interior_convexHull
  have hclosed : convexHull ℝ ({a, b, c} : Set ℂ) =
      {x | ∀ i, 0 ≤ B.coord i x} := hrange ▸ B.convexHull_eq_nonneg_coord
  rw [frontier, interior_interior, closure_triangle_interior a b c hnc, hinter, hclosed]
  ext x
  have hsum : B.coord 0 x + B.coord 1 x + B.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using B.sum_coord_apply_eq_one x
  have hrep : B.coord 0 x • a + B.coord 1 x • b + B.coord 2 x • c = x := by
    have hr := B.linear_combination_coord_eq_self x
    rw [Fin.sum_univ_three] at hr
    exact hr
  change ((∀ i, 0 ≤ B.coord i x) ∧ ¬ ∀ i, 0 < B.coord i x) ↔ _
  constructor
  · rintro ⟨hx, hn⟩
    by_cases h0 : 0 < B.coord 0 x
    · by_cases h1 : 0 < B.coord 1 x
      · have h2 : B.coord 2 x = 0 := by
          have hn2 : ¬ 0 < B.coord 2 x := by
            intro h2
            apply hn
            intro i
            fin_cases i <;> assumption
          exact le_antisymm (not_lt.mp hn2) (hx 2)
        left; left
        refine ⟨B.coord 0 x, B.coord 1 x, hx 0, hx 1, ?_, ?_⟩
        · linarith only [hsum, h2]
        · simpa only [h2, zero_smul, add_zero] using hrep
      · have hz : B.coord 1 x = 0 := le_antisymm (not_lt.mp h1) (hx 1)
        right
        refine ⟨B.coord 2 x, B.coord 0 x, hx 2, hx 0, ?_, ?_⟩
        · linarith only [hsum, hz]
        · simpa only [hz, zero_smul, add_zero, zero_add, add_comm] using hrep
    · have hz : B.coord 0 x = 0 := le_antisymm (not_lt.mp h0) (hx 0)
      left; right
      refine ⟨B.coord 1 x, B.coord 2 x, hx 1, hx 2, ?_, ?_⟩
      · linarith only [hsum, hz]
      · simpa only [hz, zero_smul, zero_add] using hrep
  · intro hx
    have hT : x ∈ convexHull ℝ ({a, b, c} : Set ℂ) := by
      rcases hx with (hx | hx) | hx
      · exact segment_subset_convexHull (by simp) (by simp) hx
      · exact segment_subset_convexHull (by simp) (by simp) hx
      · exact segment_subset_convexHull (by simp) (by simp) hx
    refine ⟨by rwa [hclosed] at hT, ?_⟩
    intro hp
    rcases hx with (hx | hx) | hx
    · have hz := coord_zero_on_segment B (i := 0) (j := 1) (k := 2)
        (by decide) (by decide) hx
      linarith only [hp 2, hz]
    · have hz := coord_zero_on_segment B (i := 1) (j := 2) (k := 0)
        (by decide) (by decide) hx
      linarith only [hp 0, hz]
    · have hz := coord_zero_on_segment B (i := 2) (j := 0) (k := 1)
        (by decide) (by decide) hx
      linarith only [hp 1, hz]



theorem triangle_inter_side_line (a b c : ℂ)
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    convexHull ℝ ({a, b, c} : Set ℂ) ∩ (line[ℝ, a, b] : Set ℂ) =
      segment ℝ a b := by
  let B := triangleBasis a b c hnc
  have hrange : range B = ({a, b, c} : Set ℂ) := by
    change range ![a, b, c] = _
    simp only [Matrix.range_cons, Matrix.range_empty, singleton_union, insert_empty_eq]
  ext x
  constructor
  · rintro ⟨hx, hl⟩
    have hp : ∀ i, 0 ≤ B.coord i x := by
      rwa [← hrange, B.convexHull_eq_nonneg_coord] at hx
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hl
    have hz : B.coord 2 (AffineMap.lineMap a b t) = 0 := by
      change B.coord 2 (AffineMap.lineMap (B 0) (B 1) t) = 0
      rw [AffineMap.apply_lineMap, B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0),
        B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 1)]
      simp only [AffineMap.lineMap_same, AffineMap.const_apply]
    have hsum : B.coord 0 (AffineMap.lineMap a b t) +
        B.coord 1 (AffineMap.lineMap a b t) = 1 := by
      have hs := B.sum_coord_apply_eq_one (AffineMap.lineMap a b t)
      simpa only [Fin.sum_univ_three, hz, add_zero] using hs
    refine ⟨B.coord 0 _, B.coord 1 _, hp 0, hp 1, hsum, ?_⟩
    have hr := B.linear_combination_coord_eq_self (AffineMap.lineMap a b t)
    rw [Fin.sum_univ_three] at hr
    change B.coord 0 _ • a + B.coord 1 _ • b + B.coord 2 _ • c = _ at hr
    simpa only [hz, zero_smul, add_zero] using hr
  · intro hx
    refine ⟨segment_subset_convexHull (by simp) (by simp) hx, ?_⟩
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨t, _, rfl⟩ := hx
    exact AffineMap.lineMap_mem_affineSpan_pair t a b



theorem isConnected_union_of_preconnected_attachment {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsConnected A)
    (hB : ∀ b ∈ B, ∃ C ⊆ A ∪ B, IsPreconnected C ∧ b ∈ C ∧ (C ∩ A).Nonempty) :
    IsConnected (A ∪ B) := by
  obtain ⟨a, ha⟩ := hA.nonempty
  refine ⟨⟨a, Or.inl ha⟩, ?_⟩
  apply isPreconnected_of_forall a
  intro b hb
  rcases hb with hb | hb
  · exact ⟨A, subset_union_left, ha, hb, hA.isPreconnected⟩
  · obtain ⟨C, hC, hc, hbC, x, hxC, hxA⟩ := hB b hb
    refine ⟨A ∪ C, union_subset subset_union_left hC, Or.inl ha, Or.inr hbC, ?_⟩
    exact hA.isPreconnected.union x hxA hxC hc

private theorem isPathConnected_compl_closedBall_complex (p : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected (Metric.closedBall p R)ᶜ := by
  let f : ℝ × ℝ → ℂ := fun x => p + (x.1 : ℂ) * Complex.exp (x.2 * Complex.I)
  have hf : Continuous f := by fun_prop
  have heq : f '' (Ioi R ×ˢ (univ : Set ℝ)) = (Metric.closedBall p R)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨r, t⟩, ⟨hr, _⟩, rfl⟩
      change R < r at hr
      simp only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le]
      simpa only [f, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hR.trans hr.le), Complex.norm_exp_ofReal_mul_I, mul_one] using hr
    · intro hz
      have hzR : R < ‖z - p‖ := by
        simpa only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] using hz
      refine ⟨(‖z - p‖, Complex.arg (z - p)), ⟨hzR, mem_univ _⟩, ?_⟩
      dsimp only [f]
      rw [Complex.norm_mul_exp_arg_mul_I]
      exact add_sub_cancel p z
  rw [← heq]
  have hI : IsPathConnected (Ioi R) :=
    (convex_Ioi R).isPathConnected ⟨R + 1, by simp only [mem_Ioi]; linarith⟩
  have hU : IsPathConnected (univ : Set ℝ) :=
    convex_univ.isPathConnected ⟨0, mem_univ _⟩
  exact (hI.prod hU).image hf

private theorem ray_avoids_starConvex {K : Set ℂ} {p z : ℂ}
    (hstar : StarConvex ℝ p K) (hz : z ∉ K) {t : ℝ} (ht : 1 ≤ t) :
    p + t • (z - p) ∉ K := by
  intro hq
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hm := hstar.add_smul_sub_mem hq (inv_nonneg.mpr htpos.le)
    (inv_le_one_of_one_le₀ ht)
  apply hz
  simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul,
    add_sub_cancel] using hm



theorem isPathConnected_compl_of_isCompact_starConvex {K : Set ℂ} {p : ℂ}
    (hK : IsCompact K) (hstar : StarConvex ℝ p K) : IsPathConnected Kᶜ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · rw [compl_empty]
    exact convex_univ.isPathConnected ⟨0, mem_univ _⟩
  have hpK : p ∈ K := hstar.mem hne
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 p
  have hsub : (Metric.closedBall p R)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hKR
  have hE := isPathConnected_compl_closedBall_complex p R hR.le
  have hreach : ∀ z ∈ Kᶜ, ∃ w ∈ (Metric.closedBall p R)ᶜ, JoinedIn Kᶜ z w := by
    intro z hz
    have hzp : z ≠ p := by rintro rfl; exact hz hpK
    have hd : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
    let t : ℝ := (R + ‖z - p‖ + 1) / ‖z - p‖
    have htd : t * ‖z - p‖ = R + ‖z - p‖ + 1 :=
      div_mul_cancel₀ _ hd.ne'
    have ht : 1 ≤ t := by
      apply (le_div_iff₀ hd).mpr
      linarith only [hR]
    let w := p + t • (z - p)
    refine ⟨w, ?_, JoinedIn.of_segment_subset ?_⟩
    · change ¬ dist w p ≤ R
      rw [dist_eq_norm]
      dsimp only [w]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (zero_le_one.trans ht), htd]
      linarith only [hd]
    · rintro q ⟨u, v, hu, hv, huv, rfl⟩
      have huv' : 1 ≤ u + v * t := by nlinarith only [huv, hv, ht]
      have heq : u • z + v • w = p + (u + v * t) • (z - p) := by
        calc
          u • z + v • w = (u + v) • p + (u + v * t) • (z - p) := by
            dsimp only [w]
            module
          _ = p + (u + v * t) • (z - p) := by rw [huv, one_smul]
      rw [heq]
      exact ray_avoids_starConvex hstar hz huv'
  obtain ⟨e, he⟩ := hE.nonempty
  refine ⟨e, hsub he, ?_⟩
  intro z hz
  obtain ⟨w, hw, hzw⟩ := hreach z hz
  exact ((hE.joinedIn e he w hw).mono hsub).trans hzw.symm



theorem exists_norm_gt_compl_of_isCompact {K : Set ℂ} (hK : IsCompact K) (R : ℝ) :
    ∃ z ∈ Kᶜ, R < ‖z‖ := by
  obtain ⟨S, hS⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨z, hz⟩ := NormedField.exists_lt_norm ℂ (max R S)
  refine ⟨z, ?_, lt_of_le_of_lt (le_max_left _ _) hz⟩
  intro hzK
  have hle : ‖z‖ ≤ S := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hS hzK
  exact (not_lt_of_ge hle) (lt_of_le_of_lt (le_max_right _ _) hz)

private theorem compact_complex_segment (x y : ℂ) : IsCompact (segment ℝ x y) := by
  rw [← convexHull_pair]
  exact ((finite_singleton y).insert x).isCompact_convexHull ℝ



theorem isPathConnected_triangle_compl (a b c : ℂ) :
    IsPathConnected (convexHull ℝ ({a, b, c} : Set ℂ))ᶜ := by
  apply isPathConnected_compl_of_isCompact_starConvex (p := a) (isCompact_triangle a b c)
  exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ (by simp))



theorem exists_norm_gt_triangle_compl (a b c : ℂ) (R : ℝ) :
    ∃ z ∈ (convexHull ℝ ({a, b, c} : Set ℂ))ᶜ, R < ‖z‖ :=
  exists_norm_gt_compl_of_isCompact (isCompact_triangle a b c) R



theorem isPathConnected_segment_compl (x y : ℂ) :
    IsPathConnected (segment ℝ x y)ᶜ := by
  apply isPathConnected_compl_of_isCompact_starConvex (p := x) (compact_complex_segment x y)
  exact (convex_segment (𝕜 := ℝ) x y) (left_mem_segment ℝ x y)



theorem exists_norm_gt_segment_compl (x y : ℂ) (R : ℝ) :
    ∃ z ∈ (segment ℝ x y)ᶜ, R < ‖z‖ :=
  exists_norm_gt_compl_of_isCompact (compact_complex_segment x y) R



theorem isPathConnected_union_segments_compl (x y z : ℂ) :
    IsPathConnected (segment ℝ x y ∪ segment ℝ x z)ᶜ := by
  apply isPathConnected_compl_of_isCompact_starConvex (p := x)
    ((compact_complex_segment x y).union (compact_complex_segment x z))
  exact ((convex_segment (𝕜 := ℝ) x y) (left_mem_segment ℝ x y)).union
    ((convex_segment (𝕜 := ℝ) x z) (left_mem_segment ℝ x z))



theorem exists_norm_gt_union_segments_compl (x y z : ℂ) (R : ℝ) :
    ∃ w ∈ (segment ℝ x y ∪ segment ℝ x z)ᶜ, R < ‖w‖ :=
  exists_norm_gt_compl_of_isCompact
    ((compact_complex_segment x y).union (compact_complex_segment x z)) R

end DirectedDistances.PlanarMap
