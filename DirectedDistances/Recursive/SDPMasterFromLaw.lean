/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic









public section
namespace DirectedDistances.Recursive.SDPMasterFromLaw

open MeasureTheory ProbabilityTheory
open Function
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (Y : Ω → ℤ → ℤ)
variable (hY : ∀ k, Measurable (fun ω => Y ω k))
variable (h0 : ∀ ω, Y ω 0 = 0)

/-- The integer increment at time `k`. -/
@[expose] def increment (k : ℤ) (ω : Ω) : ℤ := Y ω k - Y ω (k - 1)

/-- The law of the increment at time zero, `eq:den-dist-f-g`, -/
@[expose] noncomputable def sdpF (x : ℤ) : ℝ :=
  μ.real {ω | increment Y 0 ω = x}

/-- The law of the increment at time one, `eq:den-dist-f-g`, -/
@[expose] noncomputable def sdpG (y : ℤ) : ℝ :=
  μ.real {ω | increment Y 1 ω = y}

private theorem measurable_increment (hY : ∀ k, Measurable (fun ω => Y ω k)) (k : ℤ) :
    Measurable (fun ω => increment Y k ω) := by
  exact (hY k).sub (hY (k - 1))

private theorem left_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    {k x : ℤ} (hk : k ≤ 0) :
    μ.real {ω | increment Y k ω = x} = sdpF μ Y x := by
  have hm := congrArg (fun ν : Measure ℤ => ν.real {x}) (hstatL k hk)
  rw [MeasureTheory.map_measureReal_apply (measurable_increment (Y := Y) hY k)
        (measurableSet_singleton x),
      MeasureTheory.map_measureReal_apply (measurable_increment (Y := Y) hY 0)
        (measurableSet_singleton x)] at hm
  simpa [sdpF, Set.preimage, Set.mem_singleton_iff] using hm

private theorem right_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hstatR : ∀ k ≥ 1, μ.map (increment Y k) = μ.map (increment Y 1))
    {k y : ℤ} (hk : k ≥ 1) :
    μ.real {ω | increment Y k ω = y} = sdpG μ Y y := by
  have hm := congrArg (fun ν : Measure ℤ => ν.real {y}) (hstatR k hk)
  rw [MeasureTheory.map_measureReal_apply (measurable_increment (Y := Y) hY k)
        (measurableSet_singleton y),
      MeasureTheory.map_measureReal_apply (measurable_increment (Y := Y) hY 1)
        (measurableSet_singleton y)] at hm
  simpa [sdpG, Set.preimage, Set.mem_singleton_iff] using hm

/-- Every atom of either increment law is nonnegative. -/
theorem sdpF_nonneg (x : ℤ) : 0 ≤ sdpF μ Y x :=
  MeasureTheory.measureReal_nonneg

/-- Every atom of either increment law is nonnegative. -/
theorem sdpG_nonneg (y : ℤ) : 0 ≤ sdpG μ Y y :=
  MeasureTheory.measureReal_nonneg

/-- Reflection symmetry of the time-zero increment law. -/
theorem sdpF_symm
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hsym : μ.map (increment Y 0) = μ.map (fun ω => -increment Y 0 ω))
    (x : ℤ) : sdpF μ Y (-x) = sdpF μ Y x := by
  calc
    sdpF μ Y (-x) = μ.real {ω | increment Y 0 ω = -x} := rfl
    _ = μ.real {ω | -increment Y 0 ω = x} :=
      congrArg (fun s : Set Ω => μ.real s) (by
        ext ω
        simp only [Set.mem_setOf_eq]
        unfold increment
        omega)
    _ = (μ.map (fun ω => -increment Y 0 ω)).real {x} := by
      symm
      exact MeasureTheory.map_measureReal_apply
        (measurable_neg.comp (measurable_increment (Y := Y) hY 0))
        (measurableSet_singleton x)
    _ = (μ.map (increment Y 0)).real {x} := by rw [hsym]
    _ = μ.real {ω | increment Y 0 ω = x} :=
      MeasureTheory.map_measureReal_apply
        (measurable_increment (Y := Y) hY 0) (measurableSet_singleton x)
    _ = sdpF μ Y x := rfl

/-- The positive increment exclusion forces the time-one law to vanish below -/
theorem sdpG_zero_below
    (hge : ∀ᵐ ω ∂μ, ∀ k ≥ 1, -1 ≤ increment Y k ω)
    {y : ℤ} (hy : y < -1) : sdpG μ Y y = 0 := by
  have hAE : {ω | increment Y 1 ω = y} =ᵐ[μ] (∅ : Set Ω) := by
    filter_upwards [hge] with ω hω
    apply propext
    constructor
    · intro heq
      have hbound := hω 1 le_rfl
      rw [heq] at hbound
      exact (not_le_of_gt hy) hbound
    · intro hfalse
      exact False.elim hfalse
  rw [sdpG, MeasureTheory.measureReal_congr hAE]
  simp

/-- The time-zero increment law has total mass one. -/
theorem sdpF_hasSum_one (hY : ∀ k, Measurable (fun ω => Y ω k)) :
    HasSum (sdpF μ Y) 1 := by
  let ν : Measure ℤ := μ.map (increment Y 0)
  have hfib : (∑' z : ℤ, ν {z}) = ν Set.univ := by
    have hd : Pairwise (fun a b => Disjoint ({a} : Set ℤ) ({b} : Set ℤ)) := by
      intro a b hab
      exact Set.disjoint_singleton.mpr hab
    have hm : ∀ z : ℤ, MeasurableSet ({z} : Set ℤ) := fun z => measurableSet_singleton z
    have hU : (⋃ z : ℤ, ({z} : Set ℤ)) = Set.univ := by ext z; simp
    calc
      (∑' z : ℤ, ν {z}) = ν (⋃ z : ℤ, ({z} : Set ℤ)) :=
        (MeasureTheory.measure_iUnion hd hm).symm
      _ = ν Set.univ := congrArg ν hU
  have htotal : (∑' z : ℤ, ν {z}) = 1 := by
    rw [hfib]
    simp [ν]
  have hfinite : (∑' z : ℤ, ν {z}) ≠ ∞ := by rw [htotal]; simp
  have hs := ENNReal.hasSum_toReal hfinite
  have hreal : (∑' z : ℤ, (ν {z}).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun z => measure_ne_top _ _), htotal]
    simp
  rw [hreal] at hs
  have hterm (z : ℤ) : (ν {z}).toReal = sdpF μ Y z := by
    change (μ.map (increment Y 0)).real {z} = _
    rw [MeasureTheory.map_measureReal_apply
      (measurable_increment (Y := Y) hY 0) (measurableSet_singleton z)]
    rfl
  simpa only [hterm] using hs

private theorem pair_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (fun k ω => increment Y k ω) μ)
    {i j a b : ℤ} (hij : i ≠ j) :
    μ.real {ω | increment Y i ω = a ∧ increment Y j ω = b} =
      μ.real {ω | increment Y i ω = a} *
        μ.real {ω | increment Y j ω = b} := by
  have hi := measurable_increment (Y := Y) hY i
  have hj := measurable_increment (Y := Y) hY j
  have he := (hind.indepFun hij).measure_inter_preimage_eq_mul
    ({a} : Set ℤ) ({b} : Set ℤ) (measurableSet_singleton a) (measurableSet_singleton b)
  have he' : μ {ω | increment Y i ω = a ∧ increment Y j ω = b} =
      μ {ω | increment Y i ω = a} * μ {ω | increment Y j ω = b} := by
    simpa [Set.preimage, Set.mem_singleton_iff, Set.inter_def] using he
  simp only [Measure.real]
  rw [he', ENNReal.toReal_mul]

private theorem real_iUnion_tsum {ι : Type*} [Countable ι] {s : ι → Set Ω}
    (hd : Pairwise (Disjoint on s)) (hm : ∀ i, MeasurableSet (s i)) :
    μ.real (⋃ i, s i) = ∑' i, μ.real (s i) := by
  change (μ (⋃ i, s i)).toReal = ∑' i, (μ (s i)).toReal
  rw [MeasureTheory.measure_iUnion hd hm]
  exact ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _)

private theorem triple_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (fun k ω => increment Y k ω) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (hstatR : ∀ k ≥ 1, μ.map (increment Y k) = μ.map (increment Y 1))
    (a b c : ℤ) :
    μ.real {ω | increment Y 0 ω = a ∧ increment Y 1 ω = b ∧
        increment Y 2 ω = c} = sdpF μ Y a * sdpG μ Y b * sdpG μ Y c := by
  have hm : ∀ k : ℤ, Measurable (fun ω => increment Y k ω) :=
    fun k => measurable_increment (Y := Y) hY k
  have hInd := hind.indepFun_prodMk hm 0 1 2 (by omega) (by omega)
  have hp := hInd.measure_inter_preimage_eq_mul
    ({(a, b)} : Set (ℤ × ℤ)) ({c} : Set ℤ)
    (measurableSet_singleton (a, b)) (measurableSet_singleton c)
  have hp' : μ {ω | increment Y 0 ω = a ∧ increment Y 1 ω = b ∧
      increment Y 2 ω = c} =
      μ {ω | increment Y 0 ω = a ∧ increment Y 1 ω = b} *
        μ {ω | increment Y 2 ω = c} := by
    simpa [Set.preimage, Set.mem_singleton_iff, Set.inter_def, Prod.mk.injEq,
      and_assoc] using hp
  calc
    μ.real {ω | increment Y 0 ω = a ∧ increment Y 1 ω = b ∧
        increment Y 2 ω = c} =
      μ.real {ω | increment Y 0 ω = a ∧ increment Y 1 ω = b} *
        μ.real {ω | increment Y 2 ω = c} := by
          simp only [Measure.real]
          rw [hp', ENNReal.toReal_mul]
    _ = sdpF μ Y a * sdpG μ Y b * sdpG μ Y c := by
      rw [pair_atom (μ := μ) (Y := Y) hY hind (by omega),
        left_atom (μ := μ) (Y := Y) hY hstatL (k := 0) (x := a) le_rfl,
        right_atom (μ := μ) (Y := Y) hY hstatR (k := 1) (y := b) le_rfl,
        right_atom (μ := μ) (Y := Y) hY hstatR (k := 2) (y := c) (by omega)]

/-! The next lemmas are event probabilities in `eq:splitting-proba-in-3` -/

/-- The first minimum event in the SDP splitting identity. Splitting according
to `Y(-1) ≤ 0` or `Y(-1) ≥ 1` gives the extra countable sum at `y = -1`, -/
theorem sdp_min_left_term
    (hY : ∀ k, Measurable (fun ω => Y ω k)) (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (fun k ω => increment Y k ω) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (x y : ℤ) (hy : -1 ≤ y) :
    μ.real {ω | (Y ω (-2) - min (Y ω (-1)) 1,
        -min (Y ω (-1)) 1) = (-x, y)} =
      sdpF μ Y x * sdpF μ Y y +
        if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, sdpF μ Y (j : ℤ) *
            sdpF μ Y (x - (j : ℤ) - 1)) else 0 := by
  classical
  let H : Set Ω := {ω | increment Y 0 ω = y ∧ increment Y (-1) ω = x}
  let T : {j : ℤ // j ≤ -2} → Set Ω := fun j =>
    {ω | increment Y 0 ω = (j : ℤ) ∧
      increment Y (-1) ω = x - (j : ℤ) - 1}
  let L : Set Ω := ⋃ j, T j
  let A : Set Ω := {ω | (Y ω (-2) - min (Y ω (-1)) 1,
      -min (Y ω (-1)) 1) = (-x, y)}
  have h0id (ω : Ω) : increment Y 0 ω = -Y ω (-1) := by
    dsimp [increment]
    rw [h0 ω]
    omega
  have hminusid (ω : Ω) : Y ω (-2) = Y ω (-1) - increment Y (-1) ω := by
    dsimp [increment]
    omega
  have hset : A = H ∪ (if y = -1 then L else ∅) := by
    ext ω
    simp only [A, H, L, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
      Set.mem_empty_iff_false, Set.mem_ite_empty_right]
    constructor
    · intro hA
      have hc : Y ω (-2) - min (Y ω (-1)) 1 = -x := by
        exact congrArg Prod.fst hA
      have hd : -min (Y ω (-1)) 1 = y := by
        exact congrArg Prod.snd hA
      by_cases hlow : Y ω (-1) ≤ 0
      · left
        have hmin : min (Y ω (-1)) 1 = Y ω (-1) := min_eq_left (by omega)
        have hD0 : increment Y 0 ω = y := by rw [h0id ω]; omega
        have hDm : increment Y (-1) ω = x := by
          rw [hmin] at hc
          rw [hminusid ω] at hc
          omega
        exact ⟨hD0, hDm⟩
      ·
        have hhigh : 1 ≤ Y ω (-1) := by omega
        have hmin : min (Y ω (-1)) 1 = 1 := min_eq_right (by omega)
        have hy' : y = -1 := by rw [hmin] at hd; omega
        have hD0 : increment Y 0 ω ≤ -1 := by rw [h0id ω]; omega
        by_cases heq : increment Y 0 ω = -1
        · left
          have hDm : increment Y (-1) ω = x := by
            rw [hmin] at hc
            rw [hminusid ω] at hc
            have hYminus : Y ω (-1) = 1 := by
              have hh := heq
              rw [h0id ω] at hh
              omega
            rw [hYminus] at hc
            omega
          have hD0eq : increment Y 0 ω = y := by rw [hy']; exact heq
          exact ⟨hD0eq, hDm⟩
        · have hD0le : increment Y 0 ω ≤ -2 := by omega
          right
          refine ⟨hy', ⟨⟨increment Y 0 ω, hD0le⟩, ?_⟩⟩
          simp only [T, Set.mem_setOf_eq]
          constructor
          · trivial
          · rw [hminusid ω, hmin] at hc
            have hD0eq := h0id ω
            omega
    · rintro (hH | ⟨hy', hL⟩)
      · rcases hH with ⟨hD0, hDm⟩
        by_cases hy0 : 0 ≤ y
        · have hYminus : Y ω (-1) = -y := by rw [h0id ω] at hD0; omega
          have hmin : min (Y ω (-1)) 1 = Y ω (-1) :=
            min_eq_left (by rw [hYminus]; omega)
          simp only [Prod.mk.injEq]
          constructor
          · rw [hminusid ω, hmin, hYminus]
            omega
          · rw [hmin, hYminus]
            omega
        · have hy' : y = -1 := by omega
          have hYminus : Y ω (-1) = 1 := by rw [h0id ω] at hD0; omega
          have hmin : min (Y ω (-1)) 1 = 1 := min_eq_right (by omega)
          simp only [Prod.mk.injEq]
          constructor
          · rw [hminusid ω, hmin, hYminus]
            omega
          · rw [hmin]
            exact hy'.symm
      · subst y
        rcases hL with ⟨j, hj⟩
        simp only [T, Set.mem_setOf_eq] at hj
        rcases hj with ⟨hD0, hDm⟩
        have hYminus : Y ω (-1) = -(j : ℤ) := by rw [h0id ω] at hD0; omega
        have hmin : min (Y ω (-1)) 1 = 1 := min_eq_right (by rw [hYminus]; omega)
        simp only [Prod.mk.injEq]
        constructor
        · rw [hminusid ω, hmin, hYminus, hDm]
          omega
        · rw [hmin]
  have hHmass : μ.real H = sdpF μ Y y * sdpF μ Y x := by
    simpa [H] using pair_atom (μ := μ) (Y := Y) hY hind (i := 0) (j := -1)
      (a := y) (b := x) (by omega) |>.trans (by
        rw [left_atom (μ := μ) (Y := Y) hY hstatL (k := 0) (x := y) le_rfl,
          left_atom (μ := μ) (Y := Y) hY hstatL (k := -1) (x := x) (by omega)])
  have hTmeas : ∀ j, MeasurableSet (T j) := by
    intro j
    simp only [T, Set.setOf_and]
    exact (measurableSet_eq_fun (measurable_increment (Y := Y) hY 0) measurable_const).inter
      (measurableSet_eq_fun (measurable_increment (Y := Y) hY (-1)) measurable_const)
  have hTdisj : Pairwise (Disjoint on T) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro ω hj hk
    simp only [T, Set.mem_setOf_eq] at hj hk
    exact hjk (Subtype.ext (by omega))
  have hLmass : μ.real L =
      ∑' j : {j : ℤ // j ≤ -2},
        sdpF μ Y (j : ℤ) * sdpF μ Y (x - (j : ℤ) - 1) := by
    rw [show L = ⋃ j, T j by rfl, real_iUnion_tsum (μ := μ) hTdisj hTmeas]
    apply tsum_congr
    intro j
    have hpair := pair_atom (μ := μ) (Y := Y) hY hind (i := 0) (j := -1)
      (a := (j : ℤ)) (b := x - (j : ℤ) - 1) (by omega)
    rw [hpair,
      left_atom (μ := μ) (Y := Y) hY hstatL (k := 0) (x := (j : ℤ)) le_rfl,
      left_atom (μ := μ) (Y := Y) hY hstatL (k := -1)
        (x := x - (j : ℤ) - 1) (by omega)]
  have hdisj : Disjoint H (if y = -1 then L else ∅) := by
    by_cases hy' : y = -1
    · subst y
      apply Set.disjoint_left.mpr
      intro ω hH hL
      rcases Set.mem_iUnion.mp hL with ⟨j, hj⟩
      simp only [H, T, Set.mem_setOf_eq] at hH hj
      have : (j : ℤ) ≤ -2 := j.property
      omega
    · simp [hy']
  have hLmeas : MeasurableSet L := MeasurableSet.iUnion hTmeas
  have hcondmeas : MeasurableSet (if y = -1 then L else ∅) := by
    by_cases h : y = -1 <;> simp [h, hLmeas]
  calc
    μ.real A = μ.real (H ∪ (if y = -1 then L else ∅)) :=
      congrArg (fun s : Set Ω => μ.real s) hset
    _ = μ.real H + μ.real (if y = -1 then L else ∅) :=
      MeasureTheory.measureReal_union hdisj hcondmeas
    _ = sdpF μ Y x * sdpF μ Y y +
        if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2},
            sdpF μ Y (j : ℤ) * sdpF μ Y (x - (j : ℤ) - 1)) else 0 := by
      rw [hHmass]
      by_cases hy' : y = -1 <;> simp [hy', hLmass] <;> ring


/-- The middle term in the splitting law contributes only at `y = -1`, -/
theorem sdp_shift_term (h0 : ∀ ω, Y ω 0 = 0) (x y : ℤ) :
    μ.real {ω | (-Y ω 1 - 1, -1) = (x, y)} =
      if y = -1 then sdpG μ Y (-x - 1) else 0 := by
  by_cases hy : y = -1
  · subst y
    have hset : {ω | (-Y ω 1 - 1, -1) = (x, -1)} =
        {ω | increment Y 1 ω = -x - 1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Prod.mk.injEq]
      simp only [increment, sub_self, h0 ω, sub_zero, and_true]
      omega
    rw [if_pos rfl, show μ.real {ω | (-Y ω 1 - 1, -1) = (x, -1)} =
      μ.real {ω | increment Y 1 ω = -x - 1} from congrArg (fun s : Set Ω => μ.real s) hset]
    rfl
  · have hset : {ω | (-Y ω 1 - 1, -1) = (x, y)} = ∅ := by
      ext ω
      simp [hy, eq_comm]
    rw [if_neg hy, show μ.real {ω | (-Y ω 1 - 1, -1) = (x, y)} =
      μ.real ∅ from congrArg (fun s : Set Ω => μ.real s) hset]
    simp

/-- The time-one increment law has total mass one. -/
theorem sdpG_hasSum_one (hY : ∀ k, Measurable (fun ω => Y ω k)) :
    HasSum (sdpG μ Y) 1 := by
  let ν : Measure ℤ := μ.map (increment Y 1)
  have hfib : (∑' z : ℤ, ν {z}) = ν Set.univ := by
    have hd : Pairwise (fun a b => Disjoint ({a} : Set ℤ) ({b} : Set ℤ)) := by
      intro a b hab
      exact Set.disjoint_singleton.mpr hab
    have hm : ∀ z : ℤ, MeasurableSet ({z} : Set ℤ) := fun z => measurableSet_singleton z
    have hU : (⋃ z : ℤ, ({z} : Set ℤ)) = Set.univ := by ext z; simp
    calc
      (∑' z : ℤ, ν {z}) = ν (⋃ z : ℤ, ({z} : Set ℤ)) :=
        (MeasureTheory.measure_iUnion hd hm).symm
      _ = ν Set.univ := congrArg ν hU
  have htotal : (∑' z : ℤ, ν {z}) = 1 := by
    rw [hfib]
    simp [ν]
  have hfinite : (∑' z : ℤ, ν {z}) ≠ ∞ := by rw [htotal]; simp
  have hs := ENNReal.hasSum_toReal hfinite
  have hreal : (∑' z : ℤ, (ν {z}).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun z => measure_ne_top _ _), htotal]
    simp
  rw [hreal] at hs
  have hterm (z : ℤ) : (ν {z}).toReal = sdpG μ Y z := by
    change (μ.map (increment Y 1)).real {z} = _
    rw [MeasureTheory.map_measureReal_apply
      (measurable_increment (Y := Y) hY 1) (measurableSet_singleton z)]
    rfl
  simpa only [hterm] using hs

/-- The third minimum event in the SDP splitting identity. The positive-time
increment bound gives the finite convolution, with the exceptional case -/
theorem sdp_min_right_term
    (hY : ∀ k, Measurable (fun ω => Y ω k)) (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (fun k ω => increment Y k ω) μ)
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (hstatR : ∀ k ≥ 1, μ.map (increment Y k) = μ.map (increment Y 1))
    (hge : ∀ᵐ ω ∂μ, ∀ k ≥ 1, -1 ≤ increment Y k ω)
    (x y : ℤ) (hy : -1 ≤ y) :
    μ.real {ω | (Y ω (-1) - min 0 (Y ω 2 + 1),
        Y ω 2 - min 0 (Y ω 2 + 1)) = (-x, y)} =
      sdpF μ Y x * ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
        sdpG μ Y j * sdpG μ Y (y - j) +
          if y = -1 then sdpG μ Y (-1) ^ 2 * sdpF μ Y (x + 1) else 0 := by
  classical
  let J := Finset.Icc (-1 : ℤ) (y + 1)
  let T : ℤ → Set Ω := fun j =>
    {ω | increment Y 0 ω = x ∧ increment Y 1 ω = j ∧
      increment Y 2 ω = y - j}
  let L : Set Ω := ⋃ j ∈ J, T j
  let E : Set Ω :=
    {ω | increment Y 0 ω = x + 1 ∧ increment Y 1 ω = -1 ∧
      increment Y 2 ω = -1}
  let A : Set Ω := {ω | (Y ω (-1) - min 0 (Y ω 2 + 1),
      Y ω 2 - min 0 (Y ω 2 + 1)) = (-x, y)}
  have h0id (ω : Ω) : increment Y 0 ω = -Y ω (-1) := by
    dsimp [increment]
    rw [h0 ω]
    omega
  have h2id (ω : Ω) : Y ω 2 = increment Y 1 ω + increment Y 2 ω := by
    dsimp [increment]
    rw [h0 ω]
    omega
  have hbound : ∀ᵐ ω ∂μ,
      -1 ≤ increment Y 1 ω ∧ -1 ≤ increment Y 2 ω := by
    filter_upwards [hge] with ω hω
    exact ⟨hω 1 le_rfl, hω 2 (by omega)⟩
  have hAE : A =ᵐ[μ] (L ∪ (if y = -1 then E else ∅)) := by
    filter_upwards [hbound] with ω hb
    apply propext
    simp only [A, L, T, E, Set.mem_setOf_eq, Set.mem_union,
      Set.mem_iUnion₂, Set.mem_ite_empty_right, Set.mem_empty_iff_false]
    constructor
    · intro hA
      have hx : Y ω (-1) - min 0 (Y ω 2 + 1) = -x := congrArg Prod.fst hA
      have hy' : Y ω 2 - min 0 (Y ω 2 + 1) = y := congrArg Prod.snd hA
      by_cases hbig : -1 ≤ Y ω 2
      · left
        have hmin : min 0 (Y ω 2 + 1) = 0 := min_eq_left (by omega)
        have hy2 : Y ω 2 = y := by rw [hmin] at hy'; omega
        have hD0 : increment Y 0 ω = x := by
          rw [h0id ω]
          rw [hmin] at hx
          omega
        have hsum : y = increment Y 1 ω + increment Y 2 ω := by
          rw [← hy2]
          exact h2id ω
        have hj1 : increment Y 1 ω ∈ J := by
          simp only [J, Finset.mem_Icc]
          rcases hb with ⟨hb1, hb2⟩
          omega
        have hD2 : increment Y 2 ω = y - increment Y 1 ω := by omega
        exact ⟨increment Y 1 ω, hj1, hD0, rfl, hD2⟩
      · right
        have hsmall : Y ω 2 = -2 := by
          have hsum := h2id ω
          rcases hb with ⟨hb1, hb2⟩
          omega
        have hmin : min 0 (Y ω 2 + 1) = -1 := by rw [hsmall]; decide
        have hy' : y = -1 := by rw [hmin] at hy'; omega
        refine ⟨hy', ?_⟩
        have hD0 : increment Y 0 ω = x + 1 := by
          rw [h0id ω]
          rw [hmin] at hx
          omega
        have hD1 : increment Y 1 ω = -1 := by
          have hsum := h2id ω
          rcases hb with ⟨hb1, hb2⟩
          omega
        have hD2 : increment Y 2 ω = -1 := by
          have hsum := h2id ω
          rcases hb with ⟨hb1, hb2⟩
          omega
        exact ⟨hD0, hD1, hD2⟩
    · rintro (hL | ⟨hy', hE⟩)
      · rcases hL with ⟨j, hj, hT⟩
        rcases hT with ⟨hD0, hD1, hD2⟩
        have hY2 : Y ω 2 = y := by rw [h2id ω, hD1, hD2]; omega
        have hmin : min 0 (Y ω 2 + 1) = 0 := min_eq_left (by rw [hY2]; omega)
        have hYminus : Y ω (-1) = -x := by rw [h0id ω] at hD0; omega
        simp only [Prod.mk.injEq]
        constructor
        · rw [hYminus, hmin]
          omega
        · rw [hmin, hY2]
          omega
      · subst y
        rcases hE with ⟨hD0, hD1, hD2⟩
        have hY2 : Y ω 2 = -2 := by rw [h2id ω, hD1, hD2]; norm_num
        have hmin : min 0 (Y ω 2 + 1) = -1 := by rw [hY2]; decide
        have hYminus : Y ω (-1) = -(x + 1) := by rw [h0id ω] at hD0; omega
        simp only [Prod.mk.injEq]
        constructor
        · rw [hYminus, hmin]
          omega
        · rw [hmin, hY2]
          omega
  have hTmeas : ∀ j, MeasurableSet (T j) := by
    intro j
    simp only [T, Set.setOf_and]
    exact (measurableSet_eq_fun (measurable_increment (Y := Y) hY 0) measurable_const).inter
      ((measurableSet_eq_fun (measurable_increment (Y := Y) hY 1) measurable_const).inter
        (measurableSet_eq_fun (measurable_increment (Y := Y) hY 2) measurable_const))
  have hTdisj : Set.PairwiseDisjoint (↑J) T := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro ω hTa hTb
    simp only [T, Set.mem_setOf_eq] at hTa hTb
    have : a = b := by omega
    exact hab this
  have hm : ∀ j ∈ J, MeasurableSet (T j) := fun j _ => hTmeas j
  have hLmass : μ.real L =
      sdpF μ Y x * ∑ j ∈ J, sdpG μ Y j * sdpG μ Y (y - j) := by
    rw [show L = ⋃ j ∈ J, T j by rfl,
      MeasureTheory.measureReal_biUnion_finset hTdisj hm]
    simp_rw [T, triple_atom (μ := μ) (Y := Y) hY hind hstatL hstatR]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hEmass : μ.real E =
      sdpF μ Y (x + 1) * sdpG μ Y (-1) * sdpG μ Y (-1) := by
    simpa [E] using triple_atom (μ := μ) (Y := Y) hY hind hstatL hstatR
      (x + 1) (-1) (-1)
  have hdisj : Disjoint L (if y = -1 then E else ∅) := by
    by_cases hy' : y = -1
    · subst y
      apply Set.disjoint_left.mpr
      intro ω hL hE
      rcases Set.mem_iUnion₂.mp hL with ⟨j, hj, hT⟩
      simp only [T, E, Set.mem_setOf_eq] at hT hE
      rcases hT with ⟨_, hD1, hD2⟩
      rcases hE with ⟨_, hE1, hE2⟩
      omega
    · simp [hy']
  have hLmeas : MeasurableSet L := Finset.measurableSet_biUnion J hm
  have hEmeas : MeasurableSet E := by
    simp only [E, Set.setOf_and]
    exact (measurableSet_eq_fun (measurable_increment (Y := Y) hY 0) measurable_const).inter
      ((measurableSet_eq_fun (measurable_increment (Y := Y) hY 1) measurable_const).inter
        (measurableSet_eq_fun (measurable_increment (Y := Y) hY 2) measurable_const))
  have hcondmeas : MeasurableSet (if y = -1 then E else ∅) := by
    by_cases h : y = -1 <;> simp [h, hEmeas]
  have huniv : μ Set.univ ≠ ∞ := by simp
  have hLfinite : μ L ≠ ∞ := measure_ne_top_of_subset (Set.subset_univ L) huniv
  have hcondfinite : μ (if y = -1 then E else ∅) ≠ ∞ :=
    measure_ne_top_of_subset (Set.subset_univ _) huniv
  calc
    μ.real A = μ.real (L ∪ (if y = -1 then E else ∅)) :=
      MeasureTheory.measureReal_congr hAE
    _ = μ.real L + μ.real (if y = -1 then E else ∅) :=
      MeasureTheory.measureReal_union hdisj hcondmeas hLfinite hcondfinite
    _ = sdpF μ Y x * ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
          sdpG μ Y j * sdpG μ Y (y - j) +
        if y = -1 then sdpG μ Y (-1) ^ 2 * sdpF μ Y (x + 1) else 0 := by
      rw [hLmass]
      by_cases hy' : y = -1
      · subst y
        simp
        rw [hEmass]
        simp [J]
        ring
      · simp [hy', J]

/-- The generic law hypotheses imply the SDP master equation in the exact
law-level helpers, not properties proved here for the Busemann function. -/
theorem sdp_master_equation_from_law
    (hY : ∀ k, Measurable (fun ω => Y ω k)) (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (fun k ω => increment Y k ω) μ)
    (hstatR : ∀ k ≥ 1, μ.map (increment Y k) = μ.map (increment Y 1))
    (hstatL : ∀ k ≤ 0, μ.map (increment Y k) = μ.map (increment Y 0))
    (hsym : μ.map (increment Y 0) = μ.map (fun ω => -increment Y 0 ω))
    (hge : ∀ᵐ ω ∂μ, ∀ k ≥ 1, -1 ≤ increment Y k ω)
    (hsplit : ∀ x y, μ.real {ω | (Y ω (-1), Y ω 1) = (x, y)} =
      (1 / 3 : ℝ) * μ.real {ω | (Y ω (-2) - min (Y ω (-1)) 1,
          -min (Y ω (-1)) 1) = (x, y)} +
        (1 / 3 : ℝ) * μ.real {ω | (-Y ω 1 - 1, -1) = (x, y)} +
        (1 / 3 : ℝ) * μ.real {ω | (Y ω (-1) - min 0 (Y ω 2 + 1),
          Y ω 2 - min 0 (Y ω 2 + 1)) = (x, y)}) :
    ∀ x y : ℤ, -1 ≤ y →
      3 * sdpF μ Y x * sdpG μ Y y =
        sdpF μ Y x *
          (sdpF μ Y y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1),
            sdpG μ Y j * sdpG μ Y (y - j)) +
          (if y = -1 then
            (∑' j : {j : ℤ // j ≤ -2},
              sdpF μ Y (j : ℤ) * sdpF μ Y (x - (j : ℤ) - 1)) +
              sdpG μ Y (-1) ^ 2 * sdpF μ Y (x + 1) + sdpG μ Y (x - 1)
          else 0) := by
  intro x y hy
  have h0id (ω : Ω) : increment Y 0 ω = -Y ω (-1) := by
    dsimp [increment]
    rw [h0 ω]
    omega
  have h1id (ω : Ω) : Y ω 1 = increment Y 1 ω := by
    dsimp [increment]
    rw [h0 ω]
    omega
  have hAE : {ω | (Y ω (-1), Y ω 1) = (-x, y)} =ᵐ[μ]
      {ω | increment Y 0 ω = x ∧ increment Y 1 ω = y} := by
    filter_upwards [] with ω
    apply propext
    simp only [Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨hx, hy'⟩
      constructor
      · rw [h0id ω]
        omega
      · rw [← h1id ω]
        exact hy'
    · rintro ⟨hx, hy'⟩
      constructor
      · rw [h0id ω] at hx
        omega
      · rw [h1id ω]
        exact hy'
  have hleft : μ.real {ω | (Y ω (-1), Y ω 1) = (-x, y)} =
      sdpF μ Y x * sdpG μ Y y := by
    calc
      μ.real {ω | (Y ω (-1), Y ω 1) = (-x, y)} =
          μ.real {ω | increment Y 0 ω = x ∧ increment Y 1 ω = y} :=
            MeasureTheory.measureReal_congr hAE
      _ = μ.real {ω | increment Y 0 ω = x} *
            μ.real {ω | increment Y 1 ω = y} :=
          pair_atom (μ := μ) (Y := Y) hY hind (by omega)
      _ = sdpF μ Y x * sdpG μ Y y := rfl
  have hrec := hsplit (-x) y
  rw [hleft,
    sdp_min_left_term (μ := μ) (Y := Y) hY h0 hind hstatL x y hy,
    sdp_shift_term (μ := μ) (Y := Y) h0 (-x) y,
    sdp_min_right_term (μ := μ) (Y := Y) hY h0 hind hstatL hstatR hge x y hy] at hrec
  by_cases hy' : y = -1
  · simp [hy'] at hrec ⊢
    nlinarith [hrec]
  · simp [hy'] at hrec ⊢
    nlinarith [hrec]

end DirectedDistances.Recursive.SDPMasterFromLaw
