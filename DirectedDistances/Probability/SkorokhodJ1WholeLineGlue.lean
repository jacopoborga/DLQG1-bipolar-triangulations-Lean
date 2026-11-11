/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.Cadlag

@[expose] public section
namespace DirectedDistances.Probability

open Filter TopologicalSpace
open scoped Topology

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. Real càdlàg paths on the nonnegative half-line. -/
abbrev CadlagNonnegative :=
  {f : Set.Ici (0 : ℝ) → ℝ // IsCadlag f}

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. Reverse a nonnegative càdlàg path using its left limits. -/
noncomputable def leftLimitReversal (y : CadlagNonnegative) :
    Set.Ici (0 : ℝ) → ℝ := fun s => y.1.leftLim s

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The left-limit reversal retains the initial value. -/
theorem leftLimitReversal_zero (y : CadlagNonnegative) :
    leftLimitReversal y ⟨0, le_rfl⟩ = y.1 ⟨0, le_rfl⟩ := by
  apply leftLim_eq_of_isBot
  change ∀ z : Set.Ici (0 : ℝ), (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ)) ≤ z
  intro z
  exact z.property

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. Glue two nonnegative paths at zero with their common value zero. -/
noncomputable def wholeLineGlue (x y : CadlagNonnegative)
    (_hx0 : x.1 ⟨0, le_rfl⟩ = 0) (_hy0 : y.1 ⟨0, le_rfl⟩ = 0) : ℝ → ℝ :=
  fun t => if ht : t ∈ Set.Ici (0 : ℝ) then x.1 ⟨t, ht⟩ else
    leftLimitReversal y ⟨-t, neg_nonneg.mpr
      (le_of_lt (lt_of_not_ge (by simpa using ht)))⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The glued path has the prescribed value at zero. -/
theorem wholeLineGlue_zero (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0) :
    wholeLineGlue x y hx0 hy0 0 = 0 := by
  simp [wholeLineGlue, hx0]

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The glued path restricts to its given nonnegative path. -/
theorem wholeLineGlue_nonnegative (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0)
    (t : Set.Ici (0 : ℝ)) :
    wholeLineGlue x y hx0 hy0 t = x.1 t := by
  simp [wholeLineGlue, t.property]

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. Negative values are given by the left-limit reversal. -/
theorem wholeLineGlue_negative (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0)
    {t : ℝ} (ht : t < 0) :
    wholeLineGlue x y hx0 hy0 t = y.1.leftLim ⟨-t, neg_nonneg.mpr ht.le⟩ := by
  have hnot : ¬ t ∈ Set.Ici (0 : ℝ) := by
    simp [Set.mem_Ici, not_le.mpr ht]
  simp [wholeLineGlue, hnot, leftLimitReversal]

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The reversal has the source value at each positive time. -/
theorem leftLimitReversal_value (y : CadlagNonnegative) {s : ℝ} (hs : 0 < s) :
    leftLimitReversal y ⟨s, hs.le⟩ = y.1.leftLim ⟨s, hs.le⟩ := rfl

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The right limit of the left-limit reversal is the source value. -/
theorem leftLimitReversal_rightLim (y : CadlagNonnegative) {s : ℝ} (hs : 0 < s) :
    (leftLimitReversal y).rightLim ⟨s, hs.le⟩ = y.1 ⟨s, hs.le⟩ := by
  let p : Set.Ici (0 : ℝ) := ⟨s, hs.le⟩
  have hy : Tendsto y.1 (nhdsWithin p (Set.Ioi p)) (nhds (y.1 p)) :=
    (y.2.isRightContinuous p).tendsto
  have hright : y.1.rightLim p = y.1 p := rightLim_eq_of_tendsto hy
  have hy' : Tendsto y.1 (nhdsWithin p (Set.Ioi p)) (nhds (y.1.rightLim p)) := by
    rw [hright]
    exact hy
  calc
    (leftLimitReversal y).rightLim p = y.1.rightLim p := rightLim_leftLim hy'
    _ = y.1 p := hright

private theorem leftLimitReversal_mem_of_eventually
    (y : CadlagNonnegative) (c : Set.Ici (0 : ℝ)) (t : Set ℝ)
    (hclosed : IsClosed t) (hval : ∀ᶠ d in 𝓝[<] c, y.1 d ∈ t)
    [NeBot (𝓝[<] c)] :
    y.1.leftLim c ∈ t :=
  hclosed.mem_of_tendsto (y.2.tendsto_nhdsLT_leftLim c) hval

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The left-limit reversal converges from the right to the source value. -/
theorem leftLimitReversal_tendsto_right (y : CadlagNonnegative) {s : ℝ} (hs : 0 < s) :
    Tendsto (leftLimitReversal y) (𝓝[>] (⟨s, hs.le⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (y.1 ⟨s, hs.le⟩)) := by
  let p : Set.Ici (0 : ℝ) := ⟨s, hs.le⟩
  have hy : Tendsto y.1 (𝓝[>] p) (𝓝 (y.1 p)) :=
    (y.2.isRightContinuous p).tendsto
  obtain ⟨b, hb⟩ : (Set.Ioi p).Nonempty :=
    ⟨⟨s + 1, le_of_lt (lt_trans hs (by norm_num))⟩, by
      change s < s + 1
      linarith⟩
  apply (closed_nhds_basis (y.1 p)).tendsto_right_iff.2
  rintro t ⟨ht, hclosed⟩
  obtain ⟨u, pu, hu⟩ : ∃ u, p < u ∧ Set.Ioo p u ⊆ {z | y.1 z ∈ t} := by
    have hmem := (closed_nhds_basis (y.1 p)).tendsto_right_iff.1 hy t ⟨ht, hclosed⟩
    have hset : {z : Set.Ici (0 : ℝ) | y.1 z ∈ t} ∈ 𝓝[>] p := hmem
    exact (nhdsGT_basis_of_exists_gt (α := Set.Ici (0 : ℝ)) ⟨b, hb⟩).mem_iff.mp hset
  filter_upwards [Ioo_mem_nhdsGT pu] with c hc
  have hne : NeBot (𝓝[<] c) := nhdsLT_neBot_of_exists_lt ⟨p, hc.1⟩
  have hval : ∀ᶠ d in 𝓝[<] c, y.1 d ∈ t := by
    filter_upwards [Ioo_mem_nhdsLT hc.1] with d hd
    exact hu ⟨hd.1, hd.2.trans hc.2⟩
  exact @leftLimitReversal_mem_of_eventually y c t hclosed hval hne

private theorem wholeLineGlue_tendsto_left_negative (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (wholeLineGlue x y hx0 hy0) (𝓝[<] (-s)) (𝓝 (y.1 ⟨s, hs.le⟩)) := by
  let p : Set.Ici (0 : ℝ) := ⟨s, hs.le⟩
  let φ : ℝ → Set.Ici (0 : ℝ) := fun t => ⟨max 0 (-t), le_max_left _ _⟩
  have hφc : Continuous φ := by
    apply continuous_induced_rng.2
    change Continuous (fun t : ℝ => max 0 (-t))
    exact continuous_const.max continuous_neg
  have hpoint : φ (-s) = p := by
    apply Subtype.ext
    dsimp [φ, p]
    simp only [neg_neg]
    exact max_eq_right hs.le
  have hφ' : Tendsto φ (𝓝[Set.Iio (-s)] (-s))
      (𝓝[Set.Ioi (φ (-s))] (φ (-s))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hφc.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    apply eventually_nhdsWithin_of_forall
    intro t ht
    change t < -s at ht
    apply Set.mem_Ioi.mpr
    change (φ (-s)).val < (φ t).val
    dsimp [φ]
    simp only [neg_neg]
    rw [max_eq_right (show (0 : ℝ) ≤ -t by linarith),
      max_eq_right hs.le]
    linarith
  have hφ : Tendsto φ (𝓝[<] (-s)) (𝓝[>] p) := by
    simpa only [hpoint] using hφ'
  have hcomp := (leftLimitReversal_tendsto_right y hs).comp hφ
  have heq : (fun t : ℝ => wholeLineGlue x y hx0 hy0 t) =ᶠ[𝓝[<] (-s)]
      (leftLimitReversal y ∘ φ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htneg : t < 0 := by
      change t < -s at ht
      linarith
    rw [wholeLineGlue_negative x y hx0 hy0 htneg]
    change y.1.leftLim ⟨-t, _⟩ = y.1.leftLim (φ t)
    congr 1
    apply Subtype.ext
    simp [φ, max_eq_right (show (0 : ℝ) ≤ -t by linarith)]
  have hglue : Tendsto (wholeLineGlue x y hx0 hy0) (𝓝[<] (-s))
      (𝓝 (y.1 p)) := hcomp.congr' heq.symm
  exact hglue

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The glued path has the prescribed left limit at negative times. -/
theorem wholeLineGlue_leftLim_negative (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0)
    {s : ℝ} (hs : 0 < s) :
    (wholeLineGlue x y hx0 hy0).leftLim (-s) = y.1 ⟨s, hs.le⟩ :=
  leftLim_eq_of_tendsto (wholeLineGlue_tendsto_left_negative x y hx0 hy0 hs)

private theorem leftLimitReversal_tendsto_left (y : CadlagNonnegative)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (leftLimitReversal y) (𝓝[<] (⟨s, hs.le⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (leftLimitReversal y ⟨s, hs.le⟩)) := by
  let p : Set.Ici (0 : ℝ) := ⟨s, hs.le⟩
  have hy := y.2.tendsto_nhdsLT_leftLim p
  have hc : ContinuousWithinAt (leftLimitReversal y) (Set.Iic p) p := by
    change ContinuousWithinAt y.1.leftLim (Set.Iic p) p
    exact continuousWithinAt_leftLim_Iic hy
  exact hc.tendsto.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self)

private theorem leftLimitReversal_tendsto_right_zero (y : CadlagNonnegative) :
    Tendsto (leftLimitReversal y) (𝓝[>] (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (y.1 ⟨0, le_rfl⟩)) := by
  let p : Set.Ici (0 : ℝ) := ⟨0, le_rfl⟩
  have hy : Tendsto y.1 (𝓝[>] p) (𝓝 (y.1 p)) :=
    (y.2.isRightContinuous p).tendsto
  obtain ⟨b, hb⟩ : (Set.Ioi p).Nonempty :=
    ⟨⟨1, by norm_num⟩, by change (0 : ℝ) < 1; norm_num⟩
  apply (closed_nhds_basis (y.1 p)).tendsto_right_iff.2
  rintro t ⟨ht, hclosed⟩
  obtain ⟨u, pu, hu⟩ : ∃ u, p < u ∧ Set.Ioo p u ⊆ {z | y.1 z ∈ t} := by
    have hmem := (closed_nhds_basis (y.1 p)).tendsto_right_iff.1 hy t ⟨ht, hclosed⟩
    have hset : {z : Set.Ici (0 : ℝ) | y.1 z ∈ t} ∈ 𝓝[>] p := hmem
    exact (nhdsGT_basis_of_exists_gt (α := Set.Ici (0 : ℝ)) ⟨b, hb⟩).mem_iff.mp hset
  filter_upwards [Ioo_mem_nhdsGT pu] with c hc
  have hne : NeBot (𝓝[<] c) := nhdsLT_neBot_of_exists_lt ⟨p, hc.1⟩
  have hval : ∀ᶠ d in 𝓝[<] c, y.1 d ∈ t := by
    filter_upwards [Ioo_mem_nhdsLT hc.1] with d hd
    exact hu ⟨hd.1, hd.2.trans hc.2⟩
  exact @leftLimitReversal_mem_of_eventually y c t hclosed hval hne

private theorem wholeLineGlue_tendsto_left_zero (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0) :
    Tendsto (wholeLineGlue x y hx0 hy0) (𝓝[<] 0) (𝓝 0) := by
  let p : Set.Ici (0 : ℝ) := ⟨0, le_rfl⟩
  let φ : ℝ → Set.Ici (0 : ℝ) := fun t => ⟨max 0 (-t), le_max_left _ _⟩
  have hφc : Continuous φ := by
    apply continuous_induced_rng.2
    change Continuous (fun t : ℝ => max 0 (-t))
    exact continuous_const.max continuous_neg
  have hφ' : Tendsto φ (𝓝[<] 0) (𝓝[>] (φ 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hφc.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    apply eventually_nhdsWithin_of_forall
    intro t ht
    change t < 0 at ht
    change (φ 0).val < (φ t).val
    dsimp [φ]
    simp only [neg_zero, max_self]
    rw [max_eq_right (show (0 : ℝ) ≤ -t by linarith)]
    exact neg_pos.mpr ht
  have hφ : Tendsto φ (𝓝[<] 0) (𝓝[>] p) := by
    simpa only [show φ 0 = p by ext; simp [φ, p]] using hφ'
  have hcomp := (leftLimitReversal_tendsto_right_zero y).comp hφ
  have heq : (fun t : ℝ => wholeLineGlue x y hx0 hy0 t) =ᶠ[𝓝[<] 0]
      (leftLimitReversal y ∘ φ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htneg : t < 0 := by simpa using ht
    rw [wholeLineGlue_negative x y hx0 hy0 htneg]
    change y.1.leftLim ⟨-t, _⟩ = y.1.leftLim (φ t)
    congr 1
    apply Subtype.ext
    simp [φ, max_eq_right (show (0 : ℝ) ≤ -t by linarith)]
  have hglue := hcomp.congr' heq.symm
  simpa [hy0] using hglue

private def nonnegativeCoordinate (t : ℝ) : Set.Ici (0 : ℝ) :=
  ⟨max t 0, le_max_right _ _⟩

private def reversedCoordinate (t : ℝ) : Set.Ici (0 : ℝ) :=
  ⟨max 0 (-t), le_max_left _ _⟩

private theorem nonnegativeCoordinate_tendsto_gt {t : ℝ} (ht : 0 ≤ t) :
    Tendsto nonnegativeCoordinate (𝓝[>] t)
      (𝓝[>] (⟨t, ht⟩ : Set.Ici (0 : ℝ))) := by
  have hc : Continuous nonnegativeCoordinate := by
    apply continuous_induced_rng.2
    change Continuous (fun u : ℝ => max u 0)
    exact continuous_id.max continuous_const
  have hpoint : nonnegativeCoordinate t = ⟨t, ht⟩ := by
    apply Subtype.ext
    exact max_eq_left ht
  have h : Tendsto nonnegativeCoordinate (𝓝[>] t)
      (𝓝[>] (nonnegativeCoordinate t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hc.continuousAt (x := t)).mono_left nhdsWithin_le_nhds, ?_⟩
    apply eventually_nhdsWithin_of_forall
    intro u hu
    change t < u at hu
    change max t 0 < max u 0
    rw [max_eq_left ht, max_eq_left (show (0 : ℝ) ≤ u by linarith)]
    exact hu
  simpa [hpoint] using h

private theorem nonnegativeCoordinate_tendsto_lt {t : ℝ} (ht : 0 < t) :
    Tendsto nonnegativeCoordinate (𝓝[<] t)
      (𝓝[<] (⟨t, ht.le⟩ : Set.Ici (0 : ℝ))) := by
  have hc : Continuous nonnegativeCoordinate := by
    apply continuous_induced_rng.2
    change Continuous (fun u : ℝ => max u 0)
    exact continuous_id.max continuous_const
  have hpoint : nonnegativeCoordinate t = ⟨t, ht.le⟩ := by
    apply Subtype.ext
    exact max_eq_left ht.le
  have h : Tendsto nonnegativeCoordinate (𝓝[<] t)
      (𝓝[<] (nonnegativeCoordinate t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hc.continuousAt (x := t)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with u hu
    change nonnegativeCoordinate u < nonnegativeCoordinate t
    change max u 0 < max t 0
    rw [max_eq_left hu.1.le, max_eq_left ht.le]
    exact hu.2
  simpa [hpoint] using h

private theorem reversedCoordinate_tendsto_gt {t : ℝ} (ht : t < 0) :
    Tendsto reversedCoordinate (𝓝[>] t)
      (𝓝[<] (⟨-t, neg_nonneg.mpr ht.le⟩ : Set.Ici (0 : ℝ))) := by
  have hc : Continuous reversedCoordinate := by
    apply continuous_induced_rng.2
    change Continuous (fun u : ℝ => max 0 (-u))
    exact continuous_const.max continuous_neg
  have hpoint : reversedCoordinate t = ⟨-t, neg_nonneg.mpr ht.le⟩ := by
    apply Subtype.ext
    simp [reversedCoordinate, max_eq_right (neg_nonneg.mpr ht.le)]
  have h : Tendsto reversedCoordinate (𝓝[>] t)
      (𝓝[<] (reversedCoordinate t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hc.continuousAt (x := t)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT ht] with u hu
    change reversedCoordinate u < reversedCoordinate t
    change max 0 (-u) < max 0 (-t)
    rw [max_eq_right (neg_nonneg.mpr hu.2.le),
      max_eq_right (neg_nonneg.mpr ht.le)]
    exact neg_lt_neg hu.1
  simpa [hpoint] using h

private theorem reversedCoordinate_tendsto_left_zero :
    Tendsto reversedCoordinate (𝓝[<] 0)
      (𝓝[>] (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ))) := by
  have hc : Continuous reversedCoordinate := by
    apply continuous_induced_rng.2
    change Continuous (fun u : ℝ => max 0 (-u))
    exact continuous_const.max continuous_neg
  have hpoint : reversedCoordinate 0 = (⟨0, le_rfl⟩ : Set.Ici (0 : ℝ)) := by
    apply Subtype.ext
    simp [reversedCoordinate]
  have h : Tendsto reversedCoordinate (𝓝[<] 0)
      (𝓝[>] (reversedCoordinate 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hc.continuousAt (x := (0 : ℝ))).mono_left nhdsWithin_le_nhds, ?_⟩
    apply eventually_nhdsWithin_of_forall
    intro u hu
    change u < 0 at hu
    change max 0 (-(0 : ℝ)) < max 0 (-u)
    rw [neg_zero, max_self, max_eq_right (neg_nonneg.mpr hu.le)]
    exact neg_pos.mpr hu
  simpa [hpoint] using h

/-- Helper toward Theorem 1.6 (thm-busemann-conv, left-limit negative-time ruling);
not a paper result. The glued whole-line path is càdlàg. -/
theorem wholeLineGlue_isCadlag (x y : CadlagNonnegative)
    (hx0 : x.1 ⟨0, le_rfl⟩ = 0) (hy0 : y.1 ⟨0, le_rfl⟩ = 0) :
    IsCadlag (wholeLineGlue x y hx0 hy0) := by
  constructor
  · intro t
    by_cases ht : 0 ≤ t
    · let p : Set.Ici (0 : ℝ) := ⟨t, ht⟩
      have hcomp := (x.2.isRightContinuous p).tendsto.comp
        (nonnegativeCoordinate_tendsto_gt ht)
      have heq : (fun u : ℝ => wholeLineGlue x y hx0 hy0 u) =ᶠ[𝓝[>] t]
          (fun u => x.1 (nonnegativeCoordinate u)) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hut : t < u := by simpa using hu
        have hu0 : 0 ≤ u := le_trans ht hut.le
        simp [wholeLineGlue, nonnegativeCoordinate, hu0]
      have hglue := hcomp.congr' heq.symm
      have hval : wholeLineGlue x y hx0 hy0 t = x.1 p := by
        simpa [p] using wholeLineGlue_nonnegative x y hx0 hy0 p
      change Tendsto (wholeLineGlue x y hx0 hy0) (𝓝[>] t)
        (𝓝 (wholeLineGlue x y hx0 hy0 t))
      rw [hval]
      exact hglue
    · have ht' : t < 0 := lt_of_not_ge ht
      have hs : 0 < -t := neg_pos.mpr ht'
      let p : Set.Ici (0 : ℝ) := ⟨-t, hs.le⟩
      have hcomp := (leftLimitReversal_tendsto_left y hs).comp
        (reversedCoordinate_tendsto_gt ht')
      have heq : (fun u : ℝ => wholeLineGlue x y hx0 hy0 u) =ᶠ[𝓝[>] t]
          (leftLimitReversal y ∘ reversedCoordinate) := by
        filter_upwards [Ioo_mem_nhdsGT ht'] with u hu
        rw [wholeLineGlue_negative x y hx0 hy0 hu.2]
        have hu2 : (0 : ℝ) ≤ -u := neg_nonneg.mpr hu.2.le
        show y.1.leftLim _ = y.1.leftLim (reversedCoordinate u)
        apply congrArg y.1.leftLim
        apply Subtype.ext
        exact (max_eq_right hu2).symm
      have hglue := hcomp.congr' heq.symm
      have hval : wholeLineGlue x y hx0 hy0 t = leftLimitReversal y p := by
        rw [wholeLineGlue_negative x y hx0 hy0 ht']
        apply congrArg y.1.leftLim
        apply Subtype.ext
        rfl
      change Tendsto (wholeLineGlue x y hx0 hy0) (𝓝[>] t)
        (𝓝 (wholeLineGlue x y hx0 hy0 t))
      rw [hval]
      exact hglue
  · intro t
    by_cases ht : 0 < t
    · let p : Set.Ici (0 : ℝ) := ⟨t, ht.le⟩
      have hcomp := (x.2.tendsto_nhdsLT_leftLim p).comp
        (nonnegativeCoordinate_tendsto_lt ht)
      have heq : (fun u : ℝ => wholeLineGlue x y hx0 hy0 u) =ᶠ[𝓝[<] t]
          (fun u => x.1 (nonnegativeCoordinate u)) := by
        filter_upwards [Ioo_mem_nhdsLT ht] with u hu
        have hu0 : 0 ≤ u := hu.1.le
        simp [wholeLineGlue, nonnegativeCoordinate, hu0]
      have hglue := hcomp.congr' heq.symm
      have hval : wholeLineGlue x y hx0 hy0 t = x.1 p := by
        simpa [p] using wholeLineGlue_nonnegative x y hx0 hy0 p
      exact ⟨x.1.leftLim p, by simpa [hval] using hglue⟩
    · by_cases ht0 : t = 0
      · subst t
        exact ⟨0, wholeLineGlue_tendsto_left_zero x y hx0 hy0⟩
      · have ht' : t < 0 := by
          rcases lt_or_eq_of_le (le_of_not_gt ht) with h | h
          · exact h
          · exact (ht0 h).elim
        have hs : 0 < -t := neg_pos.mpr ht'
        exact ⟨y.1 ⟨-t, hs.le⟩,
          by simpa using wholeLineGlue_tendsto_left_negative x y hx0 hy0 hs⟩

end DirectedDistances.Probability
