module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic








public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open Function
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (Y : Ω → ℤ → ℤ)
variable (hY : ∀ k, Measurable (fun ω => Y ω k))
variable (h0 : ∀ ω, Y ω 0 = 0)

/-- The integer increment at time `k`. -/
@[expose] def ldpIncrement (k : ℤ) (ω : Ω) : ℤ := Y ω k - Y ω (k - 1)

/-- The law of the increment at time zero. -/
@[expose] def ldpF (x : ℤ) : ℝ := μ.real {ω | ldpIncrement Y 0 ω = x}

/-- The law of the increment at time one. -/
@[expose] def ldpG (y : ℤ) : ℝ := μ.real {ω | ldpIncrement Y 1 ω = y}

private theorem measurable_ldpIncrement (hY : ∀ k, Measurable (fun ω => Y ω k)) (k : ℤ) :
    Measurable (fun ω => ldpIncrement Y k ω) := by
  exact (hY k).sub (hY (k - 1))

private theorem ldp_left_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hstatL : ∀ k ≤ 0, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 0))
    {k x : ℤ} (hk : k ≤ 0) :
    μ.real {ω | ldpIncrement Y k ω = x} = ldpF μ Y x := by
  have hm := congrArg (fun ν : Measure ℤ => ν.real {x}) (hstatL k hk)
  rw [MeasureTheory.map_measureReal_apply (measurable_ldpIncrement (Y := Y) hY k)
        (measurableSet_singleton x),
      MeasureTheory.map_measureReal_apply (measurable_ldpIncrement (Y := Y) hY 0)
        (measurableSet_singleton x)] at hm
  simpa [ldpF, Set.preimage, Set.mem_singleton_iff] using hm

private theorem ldp_right_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hstatR : ∀ k ≥ 1, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 1))
    {k y : ℤ} (hk : k ≥ 1) :
    μ.real {ω | ldpIncrement Y k ω = y} = ldpG μ Y y := by
  have hm := congrArg (fun ν : Measure ℤ => ν.real {y}) (hstatR k hk)
  rw [MeasureTheory.map_measureReal_apply (measurable_ldpIncrement (Y := Y) hY k)
        (measurableSet_singleton y),
      MeasureTheory.map_measureReal_apply (measurable_ldpIncrement (Y := Y) hY 1)
        (measurableSet_singleton y)] at hm
  simpa [ldpG, Set.preimage, Set.mem_singleton_iff] using hm

/-- Every atom of either increment law is nonnegative. -/
theorem ldpF_nonneg (x : ℤ) : 0 ≤ ldpF μ Y x :=
  MeasureTheory.measureReal_nonneg

/-- Every atom of either increment law is nonnegative. -/
theorem ldpG_nonneg (y : ℤ) : 0 ≤ ldpG μ Y y :=
  MeasureTheory.measureReal_nonneg

/-- Reflection symmetry of the time-zero increment law. -/
theorem ldpF_symm
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hsym : μ.map (ldpIncrement Y 0) = μ.map (fun ω => -ldpIncrement Y 0 ω))
    (x : ℤ) : ldpF μ Y (-x) = ldpF μ Y x := by
  have hm := congrArg (fun ν : Measure ℤ => ν.real {x}) hsym
  have hNmap : (μ.map (fun ω => -ldpIncrement Y 0 ω)).real {x} =
      μ.real {ω | -ldpIncrement Y 0 ω = x} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (MeasureTheory.map_measureReal_apply (f := fun ω => -ldpIncrement Y 0 ω)
        (measurable_neg.comp (measurable_ldpIncrement (Y := Y) hY 0))
        (measurableSet_singleton x))
  have hNset : {ω | -ldpIncrement Y 0 ω = x} =
      {ω | ldpIncrement Y 0 ω = -x} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    omega
  have hN : (μ.map (fun ω => -ldpIncrement Y 0 ω)).real {x} = ldpF μ Y (-x) := by
    rw [hNmap, hNset]
    rfl
  have hD : (μ.map (ldpIncrement Y 0)).real {x} = ldpF μ Y x := by
    have hDmap : (μ.map (ldpIncrement Y 0)).real {x} =
        μ.real {ω | ldpIncrement Y 0 ω = x} := by
      simpa [Set.preimage, Set.mem_singleton_iff] using
        (MeasureTheory.map_measureReal_apply (f := ldpIncrement Y 0)
          (measurable_ldpIncrement (Y := Y) hY 0) (measurableSet_singleton x))
    rw [hDmap]
    rfl
  calc
    ldpF μ Y (-x) = (μ.map (fun ω => -ldpIncrement Y 0 ω)).real {x} := hN.symm
    _ = (μ.map (ldpIncrement Y 0)).real {x} := hm.symm
    _ = ldpF μ Y x := hD

/-- The positive-increment exclusion forces the time-one law to vanish on
nonnegative integers. -/
theorem ldpG_zero_of_nonneg
    (hneg : ∀ᵐ ω ∂μ, ∀ k ≥ 1, ldpIncrement Y k ω ≤ -1)
    {y : ℤ} (hy : 0 ≤ y) : ldpG μ Y y = 0 := by
  have hAE : {ω | ldpIncrement Y 1 ω = y} =ᵐ[μ] (∅ : Set Ω) := by
    filter_upwards [hneg] with ω hω
    apply propext
    constructor
    · intro heq
      have hbound := hω 1 le_rfl
      omega
    · intro hfalse
      cases hfalse
  rw [ldpG, MeasureTheory.measureReal_congr hAE]
  simp

/-- The generic pair-atom factorization supplied by independent increments. -/
theorem ldp_pair_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    {i j a b : ℤ} (hij : i ≠ j) :
    μ.real {ω | ldpIncrement Y i ω = a ∧ ldpIncrement Y j ω = b} =
      μ.real {ω | ldpIncrement Y i ω = a} *
        μ.real {ω | ldpIncrement Y j ω = b} := by
  have hi := measurable_ldpIncrement (Y := Y) hY i
  have hj := measurable_ldpIncrement (Y := Y) hY j
  have he := (hind.indepFun hij).measure_inter_preimage_eq_mul
    ({a} : Set ℤ) ({b} : Set ℤ) (measurableSet_singleton a) (measurableSet_singleton b)
  have he' : μ {ω | ldpIncrement Y i ω = a ∧ ldpIncrement Y j ω = b} =
      μ {ω | ldpIncrement Y i ω = a} * μ {ω | ldpIncrement Y j ω = b} := by
    simpa [Set.preimage, Set.mem_singleton_iff, Set.inter_def] using he
  simp only [Measure.real]
  rw [he', ENNReal.toReal_mul]

/-- The time-zero increment law has total mass one. -/
theorem ldpF_hasSum_one (hY : ∀ k, Measurable (fun ω => Y ω k)) :
    HasSum (ldpF μ Y) 1 := by
  let ν : Measure ℤ := μ.map (ldpIncrement Y 0)
  have hfib : (∑' z : ℤ, ν {z}) = ν Set.univ := by
    have hd : Pairwise (fun a b => Disjoint ({a} : Set ℤ) ({b} : Set ℤ)) := by
      intro a b hab
      exact Set.disjoint_singleton.mpr hab
    have hm : ∀ z : ℤ, MeasurableSet ({z} : Set ℤ) := fun z => measurableSet_singleton z
    have hU : (⋃ z : ℤ, ({z} : Set ℤ)) = Set.univ := by ext z; simp
    calc
      (∑' z : ℤ, ν {z}) = ν (⋃ z : ℤ, ({z} : Set ℤ)) := (MeasureTheory.measure_iUnion hd hm).symm
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
  have hterm (z : ℤ) : (ν {z}).toReal = ldpF μ Y z := by
    change (μ.map (ldpIncrement Y 0)).real {z} = _
    rw [MeasureTheory.map_measureReal_apply
      (measurable_ldpIncrement (Y := Y) hY 0) (measurableSet_singleton z)]
    rfl
  simpa only [hterm] using hs

/-- The time-one increment law has total mass one. -/
theorem ldpG_hasSum_one (hY : ∀ k, Measurable (fun ω => Y ω k)) :
    HasSum (ldpG μ Y) 1 := by
  let ν : Measure ℤ := μ.map (ldpIncrement Y 1)
  have hfib : (∑' z : ℤ, ν {z}) = ν Set.univ := by
    have hd : Pairwise (fun a b => Disjoint ({a} : Set ℤ) ({b} : Set ℤ)) := by
      intro a b hab
      exact Set.disjoint_singleton.mpr hab
    have hm : ∀ z : ℤ, MeasurableSet ({z} : Set ℤ) := fun z => measurableSet_singleton z
    have hU : (⋃ z : ℤ, ({z} : Set ℤ)) = Set.univ := by ext z; simp
    calc
      (∑' z : ℤ, ν {z}) = ν (⋃ z : ℤ, ({z} : Set ℤ)) := (MeasureTheory.measure_iUnion hd hm).symm
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
  have hterm (z : ℤ) : (ν {z}).toReal = ldpG μ Y z := by
    change (μ.map (ldpIncrement Y 1)).real {z} = _
    rw [MeasureTheory.map_measureReal_apply
      (measurable_ldpIncrement (Y := Y) hY 1) (measurableSet_singleton z)]
    rfl
  simpa only [hterm] using hs

private theorem ldp_real_iUnion_tsum {s : ℕ → Set Ω}
    (hd : Pairwise (Disjoint on s)) (hm : ∀ n, MeasurableSet (s n)) :
    μ.real (⋃ n, s n) = ∑' n, μ.real (s n) := by
  change (μ (⋃ n, s n)).toReal = ∑' n, (μ (s n)).toReal
  rw [MeasureTheory.measure_iUnion hd hm]
  exact ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)

private theorem ldp_triple_atom
    (hY : ∀ k, Measurable (fun ω => Y ω k))
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hstatL : ∀ k ≤ 0, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 0))
    (hstatR : ∀ k ≥ 1, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 1))
    (hsym : μ.map (ldpIncrement Y 0) = μ.map (fun ω => -ldpIncrement Y 0 ω))
    (a b c : ℤ) :
    μ.real {ω | ldpIncrement Y 0 ω = a ∧ ldpIncrement Y 1 ω = b ∧
        ldpIncrement Y 2 ω = c} = ldpF μ Y a * ldpG μ Y b * ldpG μ Y c := by
  have hm : ∀ k : ℤ, Measurable (fun ω => ldpIncrement Y k ω) :=
    fun k => measurable_ldpIncrement (Y := Y) hY k
  have hInd := hind.indepFun_prodMk hm 0 1 2 (by omega) (by omega)
  have hp := hInd.measure_inter_preimage_eq_mul
    ({(a, b)} : Set (ℤ × ℤ)) ({c} : Set ℤ)
    (measurableSet_singleton (a, b)) (measurableSet_singleton c)
  have hp' : μ {ω | ldpIncrement Y 0 ω = a ∧ ldpIncrement Y 1 ω = b ∧
      ldpIncrement Y 2 ω = c} =
      μ {ω | ldpIncrement Y 0 ω = a ∧ ldpIncrement Y 1 ω = b} *
        μ {ω | ldpIncrement Y 2 ω = c} := by
    simpa [Set.preimage, Set.mem_singleton_iff, Set.inter_def, Prod.mk.injEq,
      and_assoc] using hp
  calc
    μ.real {ω | ldpIncrement Y 0 ω = a ∧ ldpIncrement Y 1 ω = b ∧
        ldpIncrement Y 2 ω = c} =
      μ.real {ω | ldpIncrement Y 0 ω = a ∧ ldpIncrement Y 1 ω = b} *
        μ.real {ω | ldpIncrement Y 2 ω = c} := by
          simp only [Measure.real]
          rw [hp', ENNReal.toReal_mul]
    _ = ldpF μ Y a * ldpG μ Y b * ldpG μ Y c := by
      rw [ldp_pair_atom (μ := μ) (Y := Y) hY hind (by omega),
        ldp_left_atom (μ := μ) (Y := Y) hY hstatL (k := 0) (x := a) le_rfl,
        ldp_right_atom (μ := μ) (Y := Y) hY hstatR (k := 1) (y := b) le_rfl,
        ldp_right_atom (μ := μ) (Y := Y) hY hstatR (k := 2) (y := c) (by omega)]

/-- The probability of the first, maximum-containing event in the splitting law.
The first branch is divided into `Y(-1) ≤ 0` and `Y(-1) ≥ 1`, yielding the
countable sum when `y = -1`. -/
theorem ldp_max_term
    (hY : ∀ k, Measurable (fun ω => Y ω k)) (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hstatL : ∀ k ≤ 0, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 0))
    (hsym : μ.map (ldpIncrement Y 0) = μ.map (fun ω => -ldpIncrement Y 0 ω))
    (x y : ℤ) (hy : y ≤ -1) :
    μ.real {ω | (Y ω (-2) - max (Y ω (-1)) 1, -max (Y ω (-1)) 1) = (x, y)} =
      ldpF μ Y x * ldpF μ Y y +
        if y = -1 then
          (∑' j : ℕ, ldpF μ Y ((j : ℤ) + x + 1) * ldpF μ Y (-(j : ℤ))) else 0 := by
  classical
  let H : Set Ω := {ω | ldpIncrement Y 0 ω = y ∧ ldpIncrement Y (-1) ω = -x}
  let T : ℕ → Set Ω := fun j =>
    {ω | ldpIncrement Y 0 ω = (j : ℤ) ∧
      ldpIncrement Y (-1) ω = -((j : ℤ) + x + 1)}
  let L : Set Ω := ⋃ j, T j
  let A : Set Ω := {ω | (Y ω (-2) - max (Y ω (-1)) 1,
      -max (Y ω (-1)) 1) = (x, y)}
  have h0id (ω : Ω) : ldpIncrement Y 0 ω = -Y ω (-1) := by
    dsimp [ldpIncrement]
    rw [h0 ω]
    omega
  have hminusid (ω : Ω) : Y ω (-2) = Y ω (-1) - ldpIncrement Y (-1) ω := by
    dsimp [ldpIncrement]
    omega
  have hset : A = H ∪ (if y = -1 then L else ∅) := by
    ext ω
    simp only [A, H, L, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
      Set.mem_empty_iff_false, Set.mem_ite_empty_right]
    constructor
    · intro hA
      have hcoords :
          Y ω (-2) - max (Y ω (-1)) 1 = x ∧ -max (Y ω (-1)) 1 = y := by
        simpa only [Prod.mk.injEq] using hA
      by_cases hz : Y ω (-1) ≤ 0
      · right
        have hmax : max (Y ω (-1)) 1 = 1 := max_eq_right (by omega)
        have hy' : y = -1 := by
          rw [hmax] at hcoords
          exact hcoords.2.symm
        refine ⟨hy', ?_⟩
        subst y
        refine ⟨Int.toNat (-Y ω (-1)), ?_⟩
        have hj : 0 ≤ -Y ω (-1) := by omega
        have hjcast : ((Int.toNat (-Y ω (-1)) : ℕ) : ℤ) = -Y ω (-1) :=
          Int.toNat_of_nonneg hj
        have hD0 := h0id ω
        have hDminus := hminusid ω
        have hx : Y ω (-2) - 1 = x := by
          rw [hmax] at hcoords
          exact hcoords.1
        simp only [T, Set.mem_setOf_eq]
        constructor
        · rw [hD0, hjcast]
        · dsimp [ldpIncrement]
          have hx' := hx
          rw [hminusid ω] at hx'
          rw [hminusid ω]
          omega
      · left
        have hz' : 1 ≤ Y ω (-1) := by omega
        have hmax : max (Y ω (-1)) 1 = Y ω (-1) := max_eq_left (by omega)
        have hD0 := h0id ω
        have hDminus := hminusid ω
        rw [hmax] at hcoords
        constructor
        · rw [hD0]
          exact hcoords.2
        · rw [hDminus] at hcoords
          omega
    · rintro (hH | ⟨hy', hL⟩)
      · rcases hH with ⟨hD0, hDm⟩
        have hZ : Y ω (-1) = -y := by rw [h0id ω] at hD0; omega
        have hmax : max (Y ω (-1)) 1 = Y ω (-1) :=
          max_eq_left (by rw [hZ]; omega)
        have hDminus := hminusid ω
        simp only [A, Set.mem_setOf_eq, Prod.mk.injEq]
        constructor
        · rw [hDminus, hmax, hZ]
          omega
        · rw [hmax, hZ]
          omega
      · have hyneg : y = -1 := hy'
        subst y
        rcases hL with ⟨j, hj⟩
        simp only [T, Set.mem_setOf_eq] at hj
        rcases hj with ⟨hD0, hDm⟩
        have hz : Y ω (-1) = -(j : ℤ) := by rw [h0id ω] at hD0; omega
        have hmax : max (Y ω (-1)) 1 = 1 := max_eq_right (by rw [hz]; omega)
        have hDminus := hminusid ω
        simp only [A, Set.mem_setOf_eq, Prod.mk.injEq]
        constructor
        · rw [hz]
          rw [show max (-(j : ℤ)) 1 = 1 by omega]
          rw [hDminus]
          omega
        · rw [hz]
          rw [show max (-(j : ℤ)) 1 = 1 by omega]
  have hHmass : μ.real H = ldpF μ Y y * ldpF μ Y (-x) := by
    simpa [H] using ldp_pair_atom (μ := μ) (Y := Y) hY hind (i := 0) (j := -1)
      (a := y) (b := -x) (by omega) |>.trans (by
        rw [ldp_left_atom (μ := μ) (Y := Y) hY hstatL (k := 0) (x := y) le_rfl,
          ldp_left_atom (μ := μ) (Y := Y) hY hstatL (k := -1) (x := -x) (by omega)])
  have hTmeas : ∀ j, MeasurableSet (T j) := by
    intro j
    simp only [T, Set.setOf_and]
    exact (measurableSet_eq_fun (measurable_ldpIncrement (Y := Y) hY 0) measurable_const).inter
      (measurableSet_eq_fun (measurable_ldpIncrement (Y := Y) hY (-1)) measurable_const)
  have hTdisj : Pairwise (Disjoint on T) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro ω hj hk
    simp only [T, Set.mem_setOf_eq] at hj hk
    omega
  have hLmass : μ.real L = ∑' j : ℕ, ldpF μ Y ((j : ℤ) + x + 1) * ldpF μ Y (-(j : ℤ)) := by
    rw [show L = ⋃ j, T j by rfl, ldp_real_iUnion_tsum (μ := μ) hTdisj hTmeas]
    apply tsum_congr
    intro j
    have hpair := ldp_pair_atom (μ := μ) (Y := Y) hY hind (i := 0) (j := -1)
      (a := (j : ℤ)) (b := -((j : ℤ) + x + 1)) (by omega)
    rw [hpair,
      ldp_left_atom (μ := μ) (Y := Y) hY hstatL (k := 0) (x := (j : ℤ)) le_rfl,
      ldp_left_atom (μ := μ) (Y := Y) hY hstatL (k := -1)
        (x := -((j : ℤ) + x + 1)) (by omega),
      ldpF_symm (μ := μ) (Y := Y) hY hsym ((j : ℤ)),
      ldpF_symm (μ := μ) (Y := Y) hY hsym ((j : ℤ) + x + 1)]
    ring
  have hdisj : Disjoint H (if y = -1 then L else ∅) := by
    by_cases hy' : y = -1
    · subst y
      apply Set.disjoint_left.mpr
      intro ω hH hL
      rcases Set.mem_iUnion.mp hL with ⟨j, hj⟩
      simp only [H, T, Set.mem_setOf_eq] at hH hj
      have hz := h0id ω
      omega
    · simp [hy']
  have hLmeas : MeasurableSet L := MeasurableSet.iUnion hTmeas
  have hcondmeas : MeasurableSet (if y = -1 then L else ∅) := by
    by_cases h : y = -1 <;> simp [h, hLmeas]
  calc
    μ.real A = μ.real (H ∪ (if y = -1 then L else ∅)) := congrArg (fun s : Set Ω => μ.real s) hset
    _ = μ.real H + μ.real (if y = -1 then L else ∅) :=
      MeasureTheory.measureReal_union hdisj hcondmeas
    _ = ldpF μ Y x * ldpF μ Y y +
        if y = -1 then
          (∑' j : ℕ, ldpF μ Y ((j : ℤ) + x + 1) * ldpF μ Y (-(j : ℤ))) else 0 := by
      rw [hHmass, ldpF_symm (μ := μ) (Y := Y) hY hsym x]
      by_cases hy' : y = -1 <;> simp [hy', hLmass] <;> ring

/-- The second event in the splitting law contributes only at `y = -1`. -/
theorem ldp_shift_term
    (h0 : ∀ ω, Y ω 0 = 0)
    (x y : ℤ) :
    μ.real {ω | (-Y ω 1 - 1, -1) = (x, y)} =
      if y = -1 then ldpG μ Y (-x - 1) else 0 := by
  by_cases hy : y = -1
  · subst y
    have hset : {ω | (-Y ω 1 - 1, -1) = (x, -1)} =
        {ω | ldpIncrement Y 1 ω = -x - 1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Prod.mk.injEq]
      constructor
      · intro h
        rcases h with ⟨hx, _⟩
        dsimp [ldpIncrement]
        rw [h0 ω]
        omega
      · intro h
        dsimp [ldpIncrement] at h
        rw [h0 ω] at h
        constructor
        · omega
        · trivial
    rw [if_pos rfl, hset]
    rfl
  · have hset : {ω | (-Y ω 1 - 1, -1) = (x, y)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, Prod.mk.injEq]
      constructor
      · rintro ⟨hx, hy'⟩
        exact hy hy'.symm
      · intro hfalse
        cases hfalse
    rw [if_neg hy, hset]
    simp

/-- The last event in the splitting law is the finite convolution of the
positive-time increment laws. -/
theorem ldp_sum_term
    (hY : ∀ k, Measurable (fun ω => Y ω k)) (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hstatL : ∀ k ≤ 0, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 0))
    (hstatR : ∀ k ≥ 1, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 1))
    (hsym : μ.map (ldpIncrement Y 0) = μ.map (fun ω => -ldpIncrement Y 0 ω))
    (hneg : ∀ᵐ ω ∂μ, ∀ k ≥ 1, ldpIncrement Y k ω ≤ -1)
    (x y : ℤ) (hy : y ≤ -1) :
    μ.real {ω | (Y ω (-1), Y ω 2) = (x, y)} =
      ldpF μ Y x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1),
        ldpG μ Y (y + j) * ldpG μ Y (-j) := by
  classical
  let J := Finset.Icc (1 : ℤ) (-y - 1)
  let T : ℤ → Set Ω := fun j =>
    {ω | ldpIncrement Y 0 ω = -x ∧ ldpIncrement Y 1 ω = y + j ∧
      ldpIncrement Y 2 ω = -j}
  have hbound : ∀ᵐ ω ∂μ,
      ldpIncrement Y 1 ω ≤ -1 ∧ ldpIncrement Y 2 ω ≤ -1 := by
    filter_upwards [hneg] with ω hω
    exact ⟨hω 1 le_rfl, hω 2 (by omega)⟩
  have h0id (ω : Ω) : ldpIncrement Y 0 ω = -Y ω (-1) := by
    dsimp [ldpIncrement]
    rw [h0 ω]
    omega
  have h2id (ω : Ω) : Y ω 2 = ldpIncrement Y 1 ω + ldpIncrement Y 2 ω := by
    dsimp [ldpIncrement]
    rw [h0 ω]
    omega
  have hAE : {ω | (Y ω (-1), Y ω 2) = (x, y)} =ᵐ[μ]
      (⋃ j ∈ J, T j) := by
    filter_upwards [hbound] with ω hb
    apply propext
    simp only [Set.mem_iUnion₂]
    constructor
    · intro h
      rcases Prod.mk.inj h with ⟨hx, hy'⟩
      have hD1 : ldpIncrement Y 1 ω = y + -ldpIncrement Y 2 ω := by
        have hsum := h2id ω
        rw [hy'] at hsum
        omega
      refine ⟨-ldpIncrement Y 2 ω, ?_, ?_⟩
      · simp [J, Finset.mem_Icc]
        omega
      · simp only [T, Set.mem_setOf_eq]
        have hD0 : ldpIncrement Y 0 ω = -x := by rw [h0id ω, hx]
        exact ⟨hD0, hD1, by omega⟩
    · rintro ⟨j, hj, hT⟩
      simp only [T, Set.mem_setOf_eq] at hT
      rcases hT with ⟨hD0, hD1, hD2⟩
      have hx : Y ω (-1) = x := by rw [h0id ω] at hD0; omega
      have hy' : Y ω 2 = y := by rw [h2id ω, hD1, hD2]; omega
      exact Prod.ext hx hy'
  have hd : Set.PairwiseDisjoint (↑J) T := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro ω hTa hTb
    simp only [T, Set.mem_setOf_eq] at hTa hTb
    have hEq : a = b := by omega
    exact hab hEq
  have hm : ∀ j ∈ J, MeasurableSet (T j) := by
    intro j hj
    simp only [T, Set.setOf_and]
    exact (measurableSet_eq_fun (measurable_ldpIncrement (Y := Y) hY 0) measurable_const).inter
      ((measurableSet_eq_fun (measurable_ldpIncrement (Y := Y) hY 1) measurable_const).inter
        (measurableSet_eq_fun (measurable_ldpIncrement (Y := Y) hY 2) measurable_const))
  have hmass : μ.real (⋃ j ∈ J, T j) = ∑ j ∈ J, μ.real (T j) :=
    MeasureTheory.measureReal_biUnion_finset hd hm
  rw [MeasureTheory.measureReal_congr hAE, hmass]
  simp_rw [T, ldp_triple_atom (μ := μ) (Y := Y) hY hind hstatL hstatR hsym]
  rw [Finset.mul_sum]
  rw [ldpF_symm (μ := μ) (Y := Y) hY hsym x]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The generic law hypotheses imply the LDP master equation. The factors
`ldpF μ Y (-x)` arising directly from the left increment have been replaced by
`ldpF μ Y x` using the explicitly assumed reflection symmetry. -/
theorem ldp_master_equation_from_law
    (hY : ∀ k, Measurable (fun ω => Y ω k)) (h0 : ∀ ω, Y ω 0 = 0)
    (hind : iIndepFun (fun k ω => ldpIncrement Y k ω) μ)
    (hstatR : ∀ k ≥ 1, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 1))
    (hstatL : ∀ k ≤ 0, μ.map (ldpIncrement Y k) = μ.map (ldpIncrement Y 0))
    (hsym : μ.map (ldpIncrement Y 0) = μ.map (fun ω => -ldpIncrement Y 0 ω))
    (hneg : ∀ᵐ ω ∂μ, ∀ k ≥ 1, ldpIncrement Y k ω ≤ -1)
    (hsplit : ∀ x y, μ.real {ω | (Y ω (-1), Y ω 1) = (x, y)} =
      (1 / 3 : ℝ) * μ.real {ω | (Y ω (-2) - max (Y ω (-1)) 1,
          -max (Y ω (-1)) 1) = (x, y)} +
        (1 / 3 : ℝ) * μ.real {ω | (-Y ω 1 - 1, -1) = (x, y)} +
        (1 / 3 : ℝ) * μ.real {ω | (Y ω (-1), Y ω 2) = (x, y)}) :
    ∀ x y : ℤ, y ≤ -1 →
      3 * ldpF μ Y x * ldpG μ Y y =
        ldpF μ Y x * ldpF μ Y y +
          ldpF μ Y x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1),
            ldpG μ Y (y + j) * ldpG μ Y (-j) +
          (if y = -1 then
            (∑' j : ℕ, ldpF μ Y ((j : ℤ) + x + 1) * ldpF μ Y (-(j : ℤ))) +
              ldpG μ Y (-x - 1) else 0) := by
  intro x y hy
  have h0id (ω : Ω) : ldpIncrement Y 0 ω = -Y ω (-1) := by
    dsimp [ldpIncrement]
    rw [h0 ω]
    omega
  have h1id (ω : Ω) : Y ω 1 = ldpIncrement Y 1 ω := by
    dsimp [ldpIncrement]
    rw [h0 ω]
    omega
  have hAE : {ω | (Y ω (-1), Y ω 1) = (x, y)} =ᵐ[μ]
      {ω | ldpIncrement Y 0 ω = -x ∧ ldpIncrement Y 1 ω = y} := by
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
  have hleft : μ.real {ω | (Y ω (-1), Y ω 1) = (x, y)} =
      ldpF μ Y x * ldpG μ Y y := by
    calc
      μ.real {ω | (Y ω (-1), Y ω 1) = (x, y)} =
          μ.real {ω | ldpIncrement Y 0 ω = -x ∧ ldpIncrement Y 1 ω = y} :=
            MeasureTheory.measureReal_congr hAE
      _ = μ.real {ω | ldpIncrement Y 0 ω = -x} *
            μ.real {ω | ldpIncrement Y 1 ω = y} :=
          ldp_pair_atom (μ := μ) (Y := Y) hY hind (by omega)
      _ = ldpF μ Y x * ldpG μ Y y := by
          change ldpF μ Y (-x) * ldpG μ Y y = ldpF μ Y x * ldpG μ Y y
          rw [ldpF_symm (μ := μ) (Y := Y) hY hsym x]
  have hrec := hsplit x y
  rw [hleft,
    ldp_max_term (μ := μ) (Y := Y) hY h0 hind hstatL hsym x y hy,
    ldp_shift_term (μ := μ) (Y := Y) h0 x y,
    ldp_sum_term (μ := μ) (Y := Y) hY h0 hind hstatL hstatR hsym hneg x y hy] at hrec
  by_cases hy' : y = -1
  · simp [hy'] at hrec ⊢
    nlinarith [hrec]
  · simp [hy'] at hrec ⊢
    nlinarith [hrec]

end DirectedDistances.Recursive
