module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-! # Hewitt–Savage zero–one law helper

generic Hewitt–Savage zero–one law; not the paper result. -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal symmDiff Topology

/-- The coordinate map that exchanges `[0,n)` with `[n,2n)` and fixes all later indices.
generic Hewitt–Savage zero–one law; not the paper result. -/
@[expose] def blockSwapIndex (n i : ℕ) : ℕ :=
  if i < n then i + n else if i < 2 * n then i - n else i

/-- The block exchange is an involution.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem blockSwapIndex_involutive (n : ℕ) : Function.Involutive (blockSwapIndex n) := by
  intro i
  unfold blockSwapIndex
  by_cases h₁ : i < n
  · have h₂ : ¬ i + n < n := by omega
    have h₃ : i + n < 2 * n := by omega
    simp [h₁, h₂, h₃]
  · by_cases h₂ : i < 2 * n
    · have hni : n ≤ i := by omega
      have h₃ : i - n < n := by omega
      have h₄ : i - n < 2 * n := by omega
      simp [h₁, h₂, h₃, Nat.sub_add_cancel hni]
    · simp [h₁, h₂]

/-- The induced permutation of coordinates exchanging two adjacent blocks of length `n`.
generic Hewitt–Savage zero–one law; not the paper result. -/
@[expose] def blockSwapPerm (n : ℕ) : Equiv.Perm ℕ :=
  (blockSwapIndex_involutive n).toPerm (blockSwapIndex n)

/-- The coordinate permutation agrees pointwise with the block exchange.
generic Hewitt–Savage zero–one law; not the paper result. -/
@[simp] theorem blockSwapPerm_apply (n i : ℕ) :
    blockSwapPerm n i = blockSwapIndex n i := rfl

private theorem blockSwap_range_disjoint (n : ℕ) :
    Disjoint (Finset.range n) ((Finset.range n).map (blockSwapPerm n).toEmbedding) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rcases Finset.mem_map.mp hj with ⟨j, hj, hji⟩
  have hi_lt : i < n := Finset.mem_range.mp hi
  have hj_lt : j < n := Finset.mem_range.mp hj
  have hval : i = j + n := by
    calc
      i = blockSwapPerm n j := hji.symm
      _ = blockSwapIndex n j := rfl
      _ = j + n := by simp [blockSwapIndex, hj_lt]
  omega

/-- The block exchange has finite support.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem blockSwapPerm_support_finite (n : ℕ) :
    {i | blockSwapPerm n i ≠ i}.Finite := by
  apply (Finset.Iio (2 * n)).finite_toSet.subset
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi
  by_contra h
  have hbound : 2 * n ≤ i := by
    exact Nat.le_of_not_gt (by simpa [Finset.mem_Iio] using h)
  have hi₁ : ¬ i < n := by omega
  have hi₂ : ¬ i < 2 * n := by omega
  have hfixed : blockSwapPerm n i = i := by
    simp [blockSwapPerm, blockSwapIndex, hi₁, hi₂]
  exact hi hfixed

/-- Below `n`, the block exchange adds `n`.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem blockSwapIndex_of_lt (n i : ℕ) (hi : i < n) :
    blockSwapIndex n i = i + n := by
  simp [blockSwapIndex, hi]

/-- On the second block, the coordinate exchange subtracts `n`.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem blockSwapIndex_of_middle (n i : ℕ) (h₁ : n ≤ i) (h₂ : i < 2 * n) :
    blockSwapIndex n i = i - n := by
  simp [blockSwapIndex, not_lt.mpr h₁, h₂]

/-- At and after `2n`, the coordinate exchange fixes the index.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem blockSwapIndex_of_ge (n i : ℕ) (hi : 2 * n ≤ i) :
    blockSwapIndex n i = i := by
  have h₁ : n ≤ i := by omega
  simp [blockSwapIndex, not_lt.mpr h₁, not_lt.mpr hi]


private theorem exists_measure_symmDiff_lt_of_generateFrom_isSetAlgebra
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetAlgebra C)
    (hgen : ‹MeasurableSpace α› = MeasurableSpace.generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ C, μ (t ∆ s) < ε := by
  have hpi : IsPiSystem C := fun t ht u hu _ => hC.inter_mem ht hu
  apply MeasurableSpace.induction_on_inter
    (C := fun s hs => ∀ ε : ℝ≥0∞, 0 < ε → ∃ t ∈ C, μ (t ∆ s) < ε)
    hgen hpi ?_ ?_ ?_ ?_ s hs ε hε
  · intro ε hε
    exact ⟨∅, hC.empty_mem, by simp [hε]⟩
  · intro t ht ε hε
    exact ⟨t, ht, by simp [hε]⟩
  · intro t ht ih ε hε
    obtain ⟨u, hu, htu⟩ := ih ε hε
    exact ⟨uᶜ, hC.compl_mem hu, by simpa only [compl_symmDiff_compl] using htu⟩
  · intro f hdisj hf_meas ih ε hε
    obtain ⟨δ, hδpos, hδsum⟩ :=
      ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos hε.ne').ne' ℕ
    have hex i : ∃ t ∈ C, μ (t ∆ f i) < δ i := ih i (δ i) (hδpos i)
    choose t ht hdiff using hex
    have htail : Tendsto (fun n => μ (⋃ i ∈ Ici n, f i)) atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i => (hf_meas i).nullMeasurableSet) hdisj
    obtain ⟨n, hn⟩ : ∃ n, μ (⋃ i ∈ Ici n, f i) < ε / 2 :=
      ((tendsto_order.1 htail).2 _ (ENNReal.half_pos hε.ne')).exists
    refine ⟨⋃ i ∈ Finset.range n, t i, hC.biUnion_mem _ (fun i hi => ht i), ?_⟩
    calc μ ((⋃ i ∈ Finset.range n, t i) ∆ (⋃ i, f i))
        ≤ μ ((⋃ i ∈ Finset.range n, (t i) ∆ (f i)) ∪ ⋃ i ∈ Ici n, f i) := by
          apply measure_mono
          intro x hx
          simp only [Finset.mem_range, mem_symmDiff, mem_iUnion, exists_prop, not_exists,
            not_and, mem_Ici, mem_union] at hx ⊢
          grind
      _ ≤ ∑ i ∈ Finset.range n, μ (t i ∆ f i) + μ (⋃ i ∈ Ici n, f i) := by
          apply (measure_union_le _ _).trans
          gcongr
          exact measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ Finset.range n, δ i + μ (⋃ i ∈ Ici n, f i) := by
          gcongr with i
          exact (hdiff i).le
      _ ≤ ∑' i, δ i + μ (⋃ i ∈ Ici n, f i) := by
          gcongr
          exact sum_le_tsum (Finset.range n)
      _ < ε / 2 + ε / 2 := by
          gcongr
      _ = ε := ENNReal.add_halves ε

private theorem measureReal_mem_Icc_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : Set Ω) : μ.real A ∈ Set.Icc 0 1 := by
  constructor
  · exact measureReal_nonneg
  · rw [measureReal_def]
    calc
      (μ A).toReal ≤ (μ Set.univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ A))
      _ = 1 := by simp

private theorem blockSwap_initial_support (n : ℕ) :
    Finset.Iic n = Finset.range (n + 1) := by
  ext i
  simp only [Finset.mem_Iic, Finset.mem_range]
  omega

/-- Reindexing coordinates by a permutation preserves an identical infinite product law.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem infinitePi_map_coordinatePerm {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (σ : Equiv.Perm ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun x i => x (σ i)) =
      Measure.infinitePi (fun _ : ℕ => ν) := by
  have hfun :
      (Equiv.piCongrLeft (fun _ : ℕ => α) σ.symm : (ℕ → α) → (ℕ → α)) =
        (fun x i => x (σ i)) := by
    funext x i
    simp [Equiv.piCongrLeft_apply]
  rw [← hfun]
  exact Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : ℕ => ν) (X := fun _ : ℕ => α) σ.symm

/-- Disjoint finite coordinate blocks are independent under the identical infinite product law.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem infinitePi_indepFun_restrict {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (s t : Finset ℕ) (hst : Disjoint s t) :
    IndepFun (fun x (i : s) => x i) (fun x (i : t) => x i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := by
  have hcoords : iIndepFun (fun i (x : ℕ → α) => x i)
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
    ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ => ν) (X := fun _ (x : α) => x) (by fun_prop)
  exact hcoords.indepFun_finset s t hst (fun i => by fun_prop)

private def permuteFinsetEquiv (σ : Equiv.Perm ℕ) (I : Finset ℕ) :
    I ≃ I.map σ.toEmbedding where
  toFun i := ⟨σ i, Finset.mem_map.mpr ⟨i, i.2, rfl⟩⟩
  invFun j := ⟨σ.symm j, by
    rcases Finset.mem_map.mp j.2 with ⟨i, hi, hji⟩
    have hs : σ.symm (j : ℕ) = i := by rw [← hji]; simp
    exact hs ▸ hi⟩
  left_inv _ := by simp
  right_inv _ := by apply Subtype.ext; simp

private def permuteCylinderBase {α : Type*} (σ : Equiv.Perm ℕ) (I : Finset ℕ)
    (S : Set (∀ _i : I, α)) : Set (∀ _j : I.map σ.toEmbedding, α) :=
  {y | (fun i : I => y (permuteFinsetEquiv σ I i)) ∈ S}

private theorem measurableSet_permuteCylinderBase {α : Type*} [MeasurableSpace α]
    (σ : Equiv.Perm ℕ) (I : Finset ℕ) (S : Set (∀ _i : I, α))
    (hS : MeasurableSet S) : MeasurableSet (permuteCylinderBase σ I S) :=
  hS.preimage (by fun_prop)

private theorem reindex_preimage_cylinder {α : Type*} [MeasurableSpace α]
    (σ : Equiv.Perm ℕ) (I : Finset ℕ) (S : Set (∀ _i : I, α)) :
    (fun x (i : ℕ) => x (σ i)) ⁻¹'
      cylinder (α := fun _ : ℕ => α) I S =
      cylinder (α := fun _ : ℕ => α) (I.map σ.toEmbedding)
        (permuteCylinderBase σ I S) := by
  ext x
  simp only [Set.mem_preimage, mem_cylinder, permuteCylinderBase]
  have hre : I.restrict (fun i : ℕ => x (σ i)) = (fun i : I => x (σ i)) := by
    funext i
    rfl
  rw [hre]
  simp [permuteFinsetEquiv]

/-- Disjoint coordinate cylinders are independent under the identical infinite product law.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem infinitePi_cylinder_indep {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (s t : Finset ℕ) (hst : Disjoint s t)
    (S : Set (∀ _i : s, α)) (T : Set (∀ _i : t, α))
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (Measure.infinitePi (fun _ : ℕ => ν))
      (cylinder (α := fun _ : ℕ => α) s S ∩ cylinder (α := fun _ : ℕ => α) t T) =
      (Measure.infinitePi (fun _ : ℕ => ν)) (cylinder (α := fun _ : ℕ => α) s S) *
        (Measure.infinitePi (fun _ : ℕ => ν)) (cylinder (α := fun _ : ℕ => α) t T) := by
  have h := (infinitePi_indepFun_restrict ν s t hst).measure_inter_preimage_eq_mul
    S T hS hT
  simpa [cylinder, Finset.restrict_def] using h

/-- Approximate a measurable event in an infinite product by a cylinder on a finite initial block.
generic Hewitt–Savage zero–one law; not the paper result. -/
theorem exists_initialCylinder_approx {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (A : Set (ℕ → α))
    (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∃ S : Set ((i : Finset.Iic n) → α),
      MeasurableSet S ∧
      (Measure.infinitePi (fun _ : ℕ => ν)) (cylinder (Finset.Iic n) S ∆ A) < ε := by
  let C := measurableCylinders (fun _ : ℕ => α)
  have hC : IsSetAlgebra C := isSetAlgebra_measurableCylinders
  have hgen : (inferInstance : MeasurableSpace (ℕ → α)) = MeasurableSpace.generateFrom C := by
    dsimp [C]
    exact generateFrom_measurableCylinders.symm
  obtain ⟨t, ht, hdiff⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetAlgebra
      (μ := Measure.infinitePi (fun _ : ℕ => ν)) hC hgen hA hε
  have htC : t ∈ measurableCylinders (fun _ : ℕ => α) := by
    simpa [C] using ht
  have ht' : t ∈ ⋃ (n) (S : Set (∀ i : Finset.Iic n, α))
      (_ : MeasurableSet S), {cylinder (Finset.Iic n) S} := by
    rw [measurableCylinders_nat] at htC
    exact htC
  simp only [mem_iUnion, mem_singleton_iff] at ht'
  obtain ⟨n, S, hS, rfl⟩ := ht'
  exact ⟨n, S, hS, hdiff⟩

/-- A measurable event invariant under every finitely supported coordinate permutation has
probability zero or one under an identical infinite product law. This is the generic
Hewitt–Savage zero–one law, a helper toward `lem-filtration-mono` -/
theorem infinitePi_hs_zero_one {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (A : Set (ℕ → α))
    (hA : MeasurableSet A)
    (hInv : ∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite →
      (fun x (i : ℕ) => x (σ i)) ⁻¹' A = A) :
    (Measure.infinitePi (fun _ : ℕ => ν)) A = 0 ∨
      (Measure.infinitePi (fun _ : ℕ => ν)) A = 1 := by
  let μ := Measure.infinitePi (fun _ : ℕ => ν)
  let p := μ.real A
  have hpIcc : p ∈ Set.Icc 0 1 := by
    change (Measure.infinitePi (fun _ : ℕ => ν)).real A ∈ Set.Icc 0 1
    exact measureReal_mem_Icc_one A
  have hsq : p * p = p := by
    by_contra hneq
    let d := |p - p * p|
    have hdpos : 0 < d := by
      dsimp [d]
      apply abs_pos.mpr
      intro hz
      apply hneq
      nlinarith
    let δ := d / 8
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨n, S, hS, happrox⟩ :=
      exists_initialCylinder_approx ν A hA (ENNReal.ofReal_pos.mpr hδ)
    let I : Finset ℕ := Finset.Iic n
    let σ : Equiv.Perm ℕ := blockSwapPerm (n + 1)
    let J : Finset ℕ := I.map σ.toEmbedding
    let Sσ := permuteCylinderBase σ I S
    let B := cylinder (α := fun _ : ℕ => α) I S
    let C := (fun (x : ℕ → α) (i : ℕ) => x (σ i)) ⁻¹' B
    have hSσ : MeasurableSet Sσ := by
      exact measurableSet_permuteCylinderBase σ I S hS
    have hCeq : C = cylinder (α := fun _ : ℕ => α) J Sσ := by
      dsimp [C, B, J, Sσ, I, σ]
      exact reindex_preimage_cylinder (blockSwapPerm (n + 1)) (Finset.Iic n) S
    have hBmeas : MeasurableSet B := hS.cylinder I
    have hCmeas : MeasurableSet C := by
      rw [hCeq]
      exact hSσ.cylinder J
    have hdisj : Disjoint I J := by
      dsimp [I, J, σ]
      rw [blockSwap_initial_support]
      exact blockSwap_range_disjoint (n + 1)
    have hInvσ := hInv σ (by simpa [σ] using blockSwapPerm_support_finite (n + 1))
    have hmeasure_preimage (E : Set (ℕ → α)) (hE : MeasurableSet E) :
        μ ((fun x (i : ℕ) => x (σ i)) ⁻¹' E) = μ E := by
      calc
        μ ((fun x (i : ℕ) => x (σ i)) ⁻¹' E) = μ.map (fun x (i : ℕ) => x (σ i)) E := by
          symm
          exact Measure.map_apply (by fun_prop) hE
        _ = μ E := by simp [μ, infinitePi_map_coordinatePerm]
    have hsym : A ∆ C = (fun x (i : ℕ) => x (σ i)) ⁻¹' (A ∆ B) := by
      dsimp [C]
      calc
        A ∆ ((fun x (i : ℕ) => x (σ i)) ⁻¹' B) =
            ((fun x (i : ℕ) => x (σ i)) ⁻¹' A) ∆
              ((fun x (i : ℕ) => x (σ i)) ⁻¹' B) := by rw [hInvσ]
        _ = (fun x (i : ℕ) => x (σ i)) ⁻¹' (A ∆ B) :=
          (preimage_symmDiff A B).symm
    have happroxAB : μ (A ∆ B) < ENNReal.ofReal δ := by
      simpa [μ, B, I, symmDiff_comm] using happrox
    have happroxAC : μ (A ∆ C) < ENNReal.ofReal δ := by
      calc
        μ (A ∆ C) = μ ((fun x (i : ℕ) => x (σ i)) ⁻¹' (A ∆ B)) := by rw [hsym]
        _ = μ (A ∆ B) := hmeasure_preimage _ (hA.symmDiff hBmeas)
        _ < ENNReal.ofReal δ := happroxAB
    have hIndep : μ (B ∩ C) = μ B * μ C := by
      rw [hCeq]
      simpa [μ, B, I, J] using
        infinitePi_cylinder_indep ν I J hdisj S Sσ hS hSσ
    have hrealAB : μ.real (A ∆ B) < δ := by
      rw [measureReal_def]
      have hh := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 happroxAB
      simpa [ENNReal.toReal_ofReal hδ.le] using hh
    have hrealAC : μ.real (A ∆ C) < δ := by
      rw [measureReal_def]
      have hh := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 happroxAC
      simpa [ENNReal.toReal_ofReal hδ.le] using hh
    have hcloseB : |p - μ.real B| < δ := by
      apply lt_of_le_of_lt
        (abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hBmeas.nullMeasurableSet)
      simpa [p] using hrealAB
    have hcloseC : |p - μ.real C| < δ := by
      apply lt_of_le_of_lt
        (abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hCmeas.nullMeasurableSet)
      simpa [p] using hrealAC
    have hsubset : A ∆ (B ∩ C) ⊆ (A ∆ B) ∪ (A ∆ C) := by
      intro x hx
      simp only [mem_symmDiff, mem_inter_iff, mem_union] at hx ⊢
      grind
    have hinterDiff : μ.real (A ∆ (B ∩ C)) ≤ μ.real (A ∆ B) + μ.real (A ∆ C) := by
      calc
        μ.real (A ∆ (B ∩ C)) ≤ μ.real ((A ∆ B) ∪ (A ∆ C)) := measureReal_mono hsubset
        _ ≤ μ.real (A ∆ B) + μ.real (A ∆ C) := measureReal_union_le _ _
    have hcloseInter : |p - μ.real (B ∩ C)| < 2 * δ := by
      calc
        |p - μ.real (B ∩ C)| ≤ μ.real (A ∆ (B ∩ C)) := by
          simpa [p] using abs_measureReal_sub_le_measureReal_symmDiff
            hA.nullMeasurableSet (hBmeas.inter hCmeas).nullMeasurableSet
        _ ≤ μ.real (A ∆ B) + μ.real (A ∆ C) := hinterDiff
        _ < δ + δ := add_lt_add hrealAB hrealAC
        _ = 2 * δ := by ring
    have hmulReal : μ.real (B ∩ C) = μ.real B * μ.real C := by
      change (μ (B ∩ C)).toReal = (μ B).toReal * (μ C).toReal
      rw [hIndep, ENNReal.toReal_mul]
    let q := μ.real B
    let r := μ.real C
    have hcloseB' : |q - p| < δ := by simpa [q, abs_sub_comm] using hcloseB
    have hcloseC' : |r - p| < δ := by simpa [r, abs_sub_comm] using hcloseC
    have hpabs : |p| ≤ 1 := by
      rw [abs_of_nonneg hpIcc.1]
      exact hpIcc.2
    have hrIcc : r ∈ Set.Icc 0 1 := by
      change μ.real C ∈ Set.Icc 0 1
      exact measureReal_mem_Icc_one C
    have hrabs : |r| ≤ 1 := by
      rw [abs_of_nonneg hrIcc.1]
      exact hrIcc.2
    have hclosePQr : |p - q * r| < 2 * δ := by
      simpa [hmulReal, q, r] using hcloseInter
    have hprod : |q * r - p * p| ≤ 2 * δ := by
      calc
        |q * r - p * p| = |(q - p) * r + p * (r - p)| := by congr 1; ring
        _ ≤ |q - p| * |r| + |p| * |r - p| := by
          calc
            |(q - p) * r + p * (r - p)| ≤ |(q - p) * r| + |p * (r - p)| := abs_add_le _ _
            _ = |q - p| * |r| + |p| * |r - p| := by rw [abs_mul, abs_mul]
        _ ≤ δ * 1 + 1 * δ := by
          gcongr
        _ = 2 * δ := by ring
    have htriangle : d ≤ |p - q * r| + |q * r - p * p| := by
      dsimp [d]
      calc
        |p - p * p| = |(p - q * r) + (q * r - p * p)| := by congr 1; ring
        _ ≤ |p - q * r| + |q * r - p * p| := abs_add_le _ _
    have hcontr : d < 4 * δ := by
      calc
        d ≤ |p - q * r| + |q * r - p * p| := htriangle
        _ < 2 * δ + 2 * δ := add_lt_add_of_lt_of_le hclosePQr hprod
        _ = 4 * δ := by ring
    dsimp [δ, d] at hcontr
    nlinarith [hdpos]
  have hroot : p = 0 ∨ p = 1 := by
    have hfactor : p * (p - 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hfactor with hp | hp
    · left
      exact hp
    · right
      linarith
  rcases hroot with hp | hp
  · left
    have htoReal : (μ A).toReal = 0 := by simpa [p, measureReal_def] using hp
    rcases (ENNReal.toReal_eq_zero_iff (μ A)).mp htoReal with hzero | htop
    · exact hzero
    · exact (measure_ne_top _ _ htop).elim
  · right
    have htoReal : (μ A).toReal = 1 := by simpa [p, measureReal_def] using hp
    exact ENNReal.toReal_eq_one_iff (μ A) |>.mp htoReal

end DirectedDistances.Probability
