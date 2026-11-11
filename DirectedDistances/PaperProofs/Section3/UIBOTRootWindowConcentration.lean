/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteRootWindow
public import DirectedDistances.PaperProofs.Section3.UIBOTQuadrantBridgeCarrier
public import Mathlib.Probability.Moments.SubGaussian

/-! # Root-window concentration helpers toward Proposition 3.9

These are auxiliary probability estimates for `prop-kmsw-uibot`
carrier, including unavailable windows. No geometric local-limit assertion
or admissibility-probability lower bound is asserted here. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW
open scoped ENNReal NNReal BigOperators

/-- Helper toward Proposition 3.9: conditioning on a measurable event loses
at most its reciprocal probability. This ENNReal inequality also holds for
zero-measure conditioning events, under Mathlib's conditioning convention. -/
theorem cond_apply_le_div_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) (hB : MeasurableSet B) :
    μ[|B] A ≤ μ A / μ B := by
  rw [cond_apply hB, div_eq_mul_inv, mul_comm (μ A)]
  exact mul_le_mul_right (measure_mono Set.inter_subset_right) _

/-- Helper toward Proposition 3.9: the real-valued conditioning loss for a
finite measure, with the denominator kept as the actual event probability. -/
theorem cond_real_apply_le_div_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω) (hB : MeasurableSet B)
    (hpos : 0 < μ B) :
    (μ[|B]).real A ≤ μ.real A / μ.real B := by
  have ht : μ A / μ B ≠ ∞ :=
    ENNReal.div_ne_top (measure_ne_top μ A) hpos.ne'
  simpa only [measureReal_def, ENNReal.toReal_div] using
    ENNReal.toReal_mono ht (cond_apply_le_div_measure μ A B hB)

private theorem subgaussian_mono {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) (sq_nonneg t)) (by norm_num)

/-- Helper toward Proposition 3.9: two-sided Chernoff bound for a
sub-Gaussian variable, used for residue-class pattern counts. -/
theorem measureReal_abs_ge_le_of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-t^2 / (2*c)) := by
  have hs : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    rcases le_total 0 (X ω) with hx | hx
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq, abs_of_nonneg hx] using hω)
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq, abs_of_nonpos hx] using hω)
  calc
    μ.real {ω | t ≤ |X ω|} ≤
        μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := measureReal_mono hs
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-t^2 / (2*c)) + Real.exp (-t^2 / (2*c)) :=
      add_le_add (h.measure_ge_le ht) (h.neg.measure_ge_le ht)
    _ = 2 * Real.exp (-t^2 / (2*c)) := by ring

section WordLaw

local instance : MeasurableSpace (Fin 3) := ⊤
local instance (m : ℕ) : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤

private instance letter_isProbabilityMeasure :
    IsProbabilityMeasure (DirectedDistances.PlanarMap.uniformCountingMeasure (Fin 3)) := by
  constructor
  simp [DirectedDistances.PlanarMap.uniformCountingMeasure, Measure.smul_apply,
    smul_eq_mul, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    ENNReal.inv_mul_cancel]

private instance iid_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (uibotFiniteIIDWordLaw n) := by
  rw [uibotFiniteIIDWordLaw_eq_uniform]
  constructor
  simp [DirectedDistances.PlanarMap.uniformCountingMeasure, Measure.smul_apply,
    smul_eq_mul, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    ENNReal.inv_mul_cancel]

/-- Helper toward Proposition 3.9: conditioning on the exact KMSW
endpoint-and-cone event costs at most its reciprocal iid probability. -/
theorem uibotFiniteIIDWordLaw_cond_apply_le (ℓ ρ n : ℕ)
    (A : Set (Fin (n - 1) → Fin 3)) :
    ((uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]) A ≤
      uibotFiniteIIDWordLaw n A /
        uibotFiniteIIDWordLaw n {w | KMSWWalkAdmissible ℓ ρ n w} := by
  exact cond_apply_le_div_measure _ _ _ (Set.to_countable _).measurableSet

/-- Helper toward Proposition 3.9: real-valued conditioning transfer for
the actual finite iid word law and admissibility event. -/
theorem uibotFiniteIIDWordLaw_cond_real_apply_le (ℓ ρ n : ℕ)
    (A : Set (Fin (n - 1) → Fin 3))
    (hpos : 0 < uibotFiniteIIDWordLaw n {w | KMSWWalkAdmissible ℓ ρ n w}) :
    ((uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]).real A ≤
      (uibotFiniteIIDWordLaw n).real A /
        (uibotFiniteIIDWordLaw n).real {w | KMSWWalkAdmissible ℓ ρ n w} := by
  exact cond_real_apply_le_div_measure _ _ _ (Set.to_countable _).measurableSet hpos

private theorem iid_projection {ι : Type*} [Fintype ι] (n : ℕ)
    (f : ι → Fin (n - 1)) (hf : Function.Injective f) :
    (uibotFiniteIIDWordLaw n).map (fun w i => w (f i)) =
      Measure.pi (fun _ : ι => DirectedDistances.PlanarMap.uniformCountingMeasure (Fin 3)) := by
  have hi : iIndepFun (fun i (w : Fin (n - 1) → Fin 3) => w i)
      (uibotFiniteIIDWordLaw n) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp := (hi.precomp hf).map_fun_eq_pi_map (fun _ =>
    (measurable_pi_apply _).aemeasurable)
  simpa only [uibotFiniteIIDWordLaw, (measurePreserving_eval
    (fun _ : Fin (n - 1) => DirectedDistances.PlanarMap.uniformCountingMeasure (Fin 3)) _).map_eq]
    using hp

private theorem iid_block_law {ι : Type*} [Fintype ι] (n L : ℕ)
    (f : (ι × Fin L) → Fin (n - 1)) (hf : Function.Injective f) :
    (uibotFiniteIIDWordLaw n).map (fun w a i => w (f (a, i))) =
      Measure.pi (fun _ : ι => Measure.pi
        (fun _ : Fin L => DirectedDistances.PlanarMap.uniformCountingMeasure (Fin 3))) := by
  classical
  apply Measure.ext_of_singleton
  intro y
  have he : (fun (w : Fin (n - 1) → Fin 3) a i => w (f (a, i))) ⁻¹' {y} =
      (fun (w : Fin (n - 1) → Fin 3) p => w (f p)) ⁻¹'
        {fun p : ι × Fin L => y p.1 p.2} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Prod.forall]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), he,
    ← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    iid_projection n f hf]
  simp only [Measure.pi_singleton, Fintype.prod_prod_type]

/-- Helper toward Proposition 3.9: an arbitrary injective selection of
disjoint equal-length blocks from the iid word consists of independent blocks. -/
theorem uibotFiniteIIDWordLaw_iIndepFun_blocks {ι : Type*} [Fintype ι]
    (n L : ℕ) (f : (ι × Fin L) → Fin (n - 1)) (hf : Function.Injective f) :
    iIndepFun (fun a (w : Fin (n - 1) → Fin 3) i => w (f (a, i)))
      (uibotFiniteIIDWordLaw n) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun _ => (measurable_of_countable _).aemeasurable)).mpr
  rw [iid_block_law n L f hf]
  congr 1
  funext a
  exact (iid_projection n (fun i => f (a, i))
    (fun i j h => (Prod.mk.inj (hf h)).2)).symm

private abbrev ColorRoots (n m : ℕ) (r : Fin (2*m+1)) :=
  {j : Fin n // UIBOTRootWindowValid m j ∧ j.val % (2*m+1) = r.val}

private def colorIndex {n m : ℕ} {r : Fin (2*m+1)}
    (p : ColorRoots n m r × Fin (2*m)) : Fin (n-1) :=
  ⟨p.1.val.val - m + p.2.val,
    (uibotFiniteRootWindow_index p.1.val p.1.property.1 p.2).1⟩

private theorem colorIndex_injective {n m : ℕ} (r : Fin (2*m+1)) :
    Function.Injective (colorIndex (n := n) (m := m) (r := r)) := by
  intro ⟨j, i⟩ ⟨k, t⟩ h
  have he := congrArg Fin.val h
  change j.val.val - m + i.val = k.val.val - m + t.val at he
  have hj := j.property.1.1
  have hk := k.property.1.1
  have hi := i.isLt
  have ht := t.isLt
  have hmod : j.val.val ≡ k.val.val [MOD (2*m+1)] :=
    j.property.2.trans k.property.2.symm
  have hjk : j.val.val = k.val.val := by
    apply le_antisymm
    · exact hmod.le_of_lt_add (by omega)
    · exact hmod.symm.le_of_lt_add (by omega)
  have hroot : j = k := Subtype.ext (Fin.ext hjk)
  apply Prod.ext hroot
  apply Fin.ext
  change i.val = t.val
  omega

/-- Helper toward Proposition 3.9: valid centered windows whose roots
have the same residue modulo `2m+1` are mutually independent under the iid law. -/
theorem uibotFiniteIIDWordLaw_iIndepFun_rootWindows (n m : ℕ) (r : Fin (2*m+1)) :
    iIndepFun (fun (j : {j : Fin n // UIBOTRootWindowValid m j ∧
        j.val % (2*m+1) = r.val}) (w : Fin (n-1) → Fin 3) =>
      uibotFiniteRootWindow m w j.val) (uibotFiniteIIDWordLaw n) := by
  classical
  have h := uibotFiniteIIDWordLaw_iIndepFun_blocks n (2*m)
    (colorIndex (r := r)) (colorIndex_injective r)
  have hh := h.comp (fun _ => some) (fun _ => measurable_of_countable _)
  convert hh using 1
  funext j w
  simp only [uibotFiniteRootWindow, dite_eq_left j.property.1, Function.comp_apply, colorIndex]

/-- Helper toward Proposition 3.9: a valid root window has exactly the
uniform three-letter pattern probability, without a boundary approximation. -/
theorem uibotFiniteIIDWordLaw_rootWindow_pattern_real {n m : ℕ}
    (j : Fin n) (hj : UIBOTRootWindowValid m j) (v : Fin (2*m) → Fin 3) :
    (uibotFiniteIIDWordLaw n).real {w | uibotFiniteRootWindow m w j = some v} =
      (3 : ℝ)⁻¹ ^ (2*m) := by
  let f : Fin (2*m) → Fin (n-1) := fun i =>
    ⟨j.val - m + i.val, (uibotFiniteRootWindow_index j hj i).1⟩
  have hf : Function.Injective f := by
    intro i t h
    have he := congrArg Fin.val h
    change j.val - m + i.val = j.val - m + t.val at he
    exact Fin.ext (by omega)
  have hp := congrArg (fun μ : Measure (Fin (2*m) → Fin 3) => μ {v})
    (iid_projection n f hf)
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.pi_singleton] at hp
  have he : {w | uibotFiniteRootWindow m w j = some v} =
      (fun w i => w (f i)) ⁻¹' {v} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      uibotFiniteRootWindow, dite_eq_left hj, Option.some.injEq, f]
  rw [measureReal_def, he, hp]
  simp [DirectedDistances.PlanarMap.uniformCountingMeasure, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_pow]

private noncomputable def patternIndicator {n : ℕ} (m : ℕ)
    (v : Fin (2*m) → Fin 3) (j : Fin n) (w : Fin (n-1) → Fin 3) : ℝ :=
  if uibotFiniteRootWindow m w j = some v then 1 else 0

private theorem patternIndicator_bounds {n m : ℕ} (v : Fin (2*m) → Fin 3)
    (j : Fin n) (w : Fin (n-1) → Fin 3) :
    patternIndicator m v j w ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold patternIndicator
  split_ifs <;> constructor <;> norm_num

private theorem patternProbability_bounds (m : ℕ) :
    (3 : ℝ)⁻¹ ^ (2*m) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem patternIndicator_integral {n m : ℕ} (v : Fin (2*m) → Fin 3)
    (j : Fin n) (hj : UIBOTRootWindowValid m j) :
    ∫ w, patternIndicator m v j w ∂uibotFiniteIIDWordLaw n =
      (3 : ℝ)⁻¹ ^ (2*m) := by
  have he : patternIndicator m v j =
      {w | uibotFiniteRootWindow m w j = some v}.indicator (fun _ => (1 : ℝ)) := by
    classical
    funext w
    simp [patternIndicator, Set.indicator]
  rw [he, integral_indicator_const (1 : ℝ) (Set.to_countable _).measurableSet,
    smul_eq_mul, mul_one]
  exact uibotFiniteIIDWordLaw_rootWindow_pattern_real j hj v

private theorem patternIndicator_subgaussian {n m : ℕ} (v : Fin (2*m) → Fin 3)
    (j : Fin n) (hj : UIBOTRootWindowValid m j) :
    HasSubgaussianMGF (fun w => patternIndicator m v j w - (3 : ℝ)⁻¹ ^ (2*m))
      1 (uibotFiniteIIDWordLaw n) := by
  have hi : Integrable (patternIndicator m v j) (uibotFiniteIIDWordLaw n) :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ (patternIndicator_bounds v j))
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := uibotFiniteIIDWordLaw n)
    (X := fun w => patternIndicator m v j w - (3 : ℝ)⁻¹ ^ (2*m))
    (a := -1) (b := 1) (measurable_of_countable _).aemeasurable
    (ae_of_all _ (fun w => by
      have hb := patternIndicator_bounds v j w
      have hp := patternProbability_bounds m
      constructor <;> linarith only [hb.1, hb.2, hp.1, hp.2])) (by
      rw [integral_sub hi (integrable_const _), patternIndicator_integral v j hj]
      simp)
  convert h using 1
  norm_num

private noncomputable def colorSum {n : ℕ} (m : ℕ) (v : Fin (2*m) → Fin 3)
    (r : Fin (2*m+1)) (w : Fin (n-1) → Fin 3) : ℝ :=
  ∑ j : ColorRoots n m r, (patternIndicator m v j.val w - (3 : ℝ)⁻¹ ^ (2*m))

private theorem colorSum_subgaussian (n m : ℕ) (v : Fin (2*m) → Fin 3)
    (r : Fin (2*m+1)) :
    HasSubgaussianMGF (colorSum m v r) n (uibotFiniteIIDWordLaw n) := by
  classical
  have hi := (uibotFiniteIIDWordLaw_iIndepFun_rootWindows n m r).comp
    (fun _ x => (if x = some v then (1 : ℝ) else 0) - (3 : ℝ)⁻¹ ^ (2*m))
    (fun _ => measurable_of_countable _)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi (c := fun _ => 1)
    (s := Finset.univ) (fun j _ => patternIndicator_subgaussian v j.val j.property.1)
  apply subgaussian_mono h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hc := Fintype.card_subtype_le
    (fun j : Fin n => UIBOTRootWindowValid m j ∧ j.val % (2*m+1) = r.val)
  simp only [Fintype.card_fin] at hc
  exact_mod_cast hc

private theorem sum_subtype_eq_sum_ite {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    (∑ x : {x // p x}, f x.val) = ∑ x : α, if p x then f x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) _).symm

private theorem sum_patternIndicator {n m : ℕ} (v : Fin (2*m) → Fin 3)
    (w : Fin (n-1) → Fin 3) :
    (∑ j : Fin n, patternIndicator m v j w) =
      (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) := by
  classical
  simp only [patternIndicator, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_boole]

private theorem sum_colorSum (n m : ℕ) (v : Fin (2*m) → Fin 3)
    (w : Fin (n-1) → Fin 3) :
    (∑ r : Fin (2*m+1), colorSum m v r w) =
      (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) -
        (Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) *
          (3 : ℝ)⁻¹ ^ (2*m) := by
  classical
  have hcolor (r : Fin (2*m+1)) : colorSum m v r w =
      ∑ j : Fin n, if UIBOTRootWindowValid m j ∧ j.val % (2*m+1) = r.val then
        patternIndicator m v j w - (3 : ℝ)⁻¹ ^ (2*m) else 0 := by
    unfold colorSum
    exact sum_subtype_eq_sum_ite
      (fun j : Fin n => UIBOTRootWindowValid m j ∧ j.val % (2*m+1) = r.val)
      (fun j => patternIndicator m v j w - (3 : ℝ)⁻¹ ^ (2*m))
  simp_rw [hcolor]
  rw [Finset.sum_comm]
  have hj (j : Fin n) :
      (∑ r : Fin (2*m+1), if UIBOTRootWindowValid m j ∧
          j.val % (2*m+1) = r.val then
        patternIndicator m v j w - (3 : ℝ)⁻¹ ^ (2*m) else 0) =
      patternIndicator m v j w -
        (if UIBOTRootWindowValid m j then (1 : ℝ) else 0) * (3 : ℝ)⁻¹ ^ (2*m) := by
    by_cases hv : UIBOTRootWindowValid m j
    · have he (r : Fin (2*m+1)) : j.val % (2*m+1) = r.val ↔
          r = ⟨j.val % (2*m+1), Nat.mod_lt _ (by omega)⟩ := by
        exact ⟨fun h => Fin.ext h.symm, fun h => (congrArg Fin.val h).symm⟩
      simp only [hv, true_and, ite_true, one_mul]
      simp_rw [he]
      simp
    · have hz : patternIndicator m v j w = 0 := by
        simp [patternIndicator, uibotFiniteRootWindow, hv]
      simp [hv, hz]
  simp_rw [hj]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_patternIndicator]
  congr 1
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_boole]

private theorem boundary_bias (n m : ℕ) :
    |((Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) - n) *
      (3 : ℝ)⁻¹ ^ (2*m)| ≤ 2*m := by
  classical
  have hc := uibotFiniteRootWindow_invalid_card n m
  have hcard : Nat.card {j : Fin n // UIBOTRootWindowValid m j} +
      Nat.card {j : Fin n // ¬UIBOTRootWindowValid m j} = n := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]
    have hc := Fintype.card_subtype_le (UIBOTRootWindowValid m : Fin n → Prop)
    simp only [Fintype.card_fin] at hc
    omega
  have hcast : (Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) +
      (Nat.card {j : Fin n // ¬UIBOTRootWindowValid m j} : ℝ) = n := by
    exact_mod_cast hcard
  have hbound : (Nat.card {j : Fin n // ¬UIBOTRootWindowValid m j} : ℝ) ≤ 2*m := by
    exact_mod_cast hc
  have hp := patternProbability_bounds m
  have hnneg : (0 : ℝ) ≤ Nat.card {j : Fin n // ¬UIBOTRootWindowValid m j} :=
    Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hp.1, abs_of_nonpos (by linarith only [hcast, hnneg])]
  calc
    _ ≤ -((Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) - n) * 1 :=
      mul_le_mul_of_nonneg_left hp.2 (by linarith only [hcast, hnneg])
    _ ≤ 2*m := by linarith

/-- Helper toward Proposition 3.9: exponential concentration of a fixed
pattern once the deterministic `2m` boundary error is at most half the
deviation threshold. All `n` roots remain in the denominator. -/
theorem uibotFiniteIIDWordLaw_rootWindow_concentration_of_large
    (n m : ℕ) (hn : 0 < n) (v : Fin (2*m) → Fin 3)
    (δ : ℝ) (hδ : 0 < δ) (hlarge : (4 : ℝ)*m ≤ n*δ) :
    (uibotFiniteIIDWordLaw n).real
      {w | δ ≤ |(Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
        n - (3 : ℝ)⁻¹ ^ (2*m)|} ≤
      (2 * (2*m+1) : ℝ) * Real.exp (-(δ^2 / (8*(2*m+1)^2)) * n) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : (0 : ℝ) < 2*m+1 := by positivity
  let t : ℝ := n*δ / (2*(2*m+1))
  have ht : 0 ≤ t := le_of_lt (div_pos (mul_pos hnR hδ) (by positivity))
  have hsub : {w | δ ≤ |(Nat.card
        {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) / n -
          (3 : ℝ)⁻¹ ^ (2*m)|} ⊆
      ⋃ r : Fin (2*m+1), {w | t ≤ |colorSum m v r w|} := by
    intro w hw
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot
    have hsum : (∑ r : Fin (2*m+1), |colorSum m v r w|) < n*δ/2 := by
      calc
        _ < ∑ _r : Fin (2*m+1), t := by
          apply Finset.sum_lt_sum (fun r _ => (hnot r).le)
          exact ⟨0, Finset.mem_univ _, hnot 0⟩
        _ = n*δ/2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          dsimp [t]
          field_simp
    have htri := Finset.abs_sum_le_sum_abs
      (fun r : Fin (2*m+1) => colorSum m v r w) Finset.univ
    rw [sum_colorSum] at htri
    have hb := boundary_bias n m
    have hab := abs_add_le
      ((Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) -
        (Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) * (3 : ℝ)⁻¹ ^ (2*m))
      (((Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) - n) *
        (3 : ℝ)⁻¹ ^ (2*m))
    have he : ((Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) -
        (Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) * (3 : ℝ)⁻¹ ^ (2*m)) +
        (((Nat.card {j : Fin n // UIBOTRootWindowValid m j} : ℝ) - n) *
          (3 : ℝ)⁻¹ ^ (2*m)) =
      (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) -
        n * (3 : ℝ)⁻¹ ^ (2*m) := by ring
    rw [he] at hab
    have hmul := mul_le_mul_of_nonneg_right hw hnR.le
    have he' : ((Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
        n - (3 : ℝ)⁻¹ ^ (2*m)) * n =
        (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) -
          n * (3 : ℝ)⁻¹ ^ (2*m) := by field_simp
    have heabs := congrArg abs he'
    rw [abs_mul, abs_of_pos hnR] at heabs
    rw [heabs] at hmul
    linarith only [hmul, htri, hab, hb, hsum, hlarge]
  have htail (r : Fin (2*m+1)) :
      (uibotFiniteIIDWordLaw n).real {w | t ≤ |colorSum m v r w|} ≤
        2 * Real.exp (-(δ^2 / (8*(2*m+1)^2)) * n) := by
    have hh := measureReal_abs_ge_le_of_hasSubgaussianMGF
      (colorSum_subgaussian n m v r) ht
    convert hh using 1
    congr 2
    simp only [NNReal.coe_natCast]
    dsimp [t]
    field_simp
    ring
  calc
    _ ≤ (uibotFiniteIIDWordLaw n).real
        (⋃ r : Fin (2*m+1), {w | t ≤ |colorSum m v r w|}) := measureReal_mono hsub
    _ ≤ ∑ r : Fin (2*m+1),
        (uibotFiniteIIDWordLaw n).real {w | t ≤ |colorSum m v r w|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _r : Fin (2*m+1),
        2 * Real.exp (-(δ^2 / (8*(2*m+1)^2)) * n) :=
      Finset.sum_le_sum (fun r _ => htail r)
    _ = _ := by simp [mul_assoc, mul_left_comm, mul_comm]

/-- Helper toward Proposition 3.9: every fixed centered pattern has an
exponentially concentrated empirical frequency under the unconditioned iid
word law, uniformly over all sizes, including zero and boundary-only sizes. -/
theorem uibotFiniteIIDWordLaw_rootWindow_exponential_concentration
    (m : ℕ) (v : Fin (2*m) → Fin 3) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (uibotFiniteIIDWordLaw n).real
        {w | δ ≤ |(Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
          n - (3 : ℝ)^(-((2*m : ℕ) : ℤ))|} ≤ C * Real.exp (-c*n) := by
  let c : ℝ := δ^2 / (8*(2*m+1)^2)
  let T : ℝ := 4*m/δ
  let C : ℝ := (2*(2*m+1)) * Real.exp (c*T)
  have hc : 0 < c := div_pos (sq_pos_of_pos hδ) (by positivity)
  have hT : 0 ≤ T := div_nonneg (by positivity) hδ.le
  have hpre : (1 : ℝ) ≤ 2*(2*m+1) := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hC : 0 < C := mul_pos (lt_of_lt_of_le zero_lt_one hpre) (Real.exp_pos _)
  have hexp : 1 ≤ Real.exp (c*T) := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (mul_nonneg hc.le hT)
  have hCpre : 2*(2*m+1) ≤ C :=
    le_mul_of_one_le_right (by positivity) hexp
  refine ⟨c, hc, C, hC, fun n => ?_⟩
  have hmain : (uibotFiniteIIDWordLaw n).real
      {w | δ ≤ |(Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
        n - (3 : ℝ)⁻¹^(2*m)|} ≤ C * Real.exp (-c*n) := by
    by_cases hlarge : (4 : ℝ)*m ≤ n*δ
    · by_cases hn : 0 < n
      · exact (uibotFiniteIIDWordLaw_rootWindow_concentration_of_large n m hn v δ hδ
          hlarge).trans (mul_le_mul_of_nonneg_right hCpre (Real.exp_nonneg _))
      · have hn0 : n = 0 := by omega
        subst n
        simpa only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] using
          (measureReal_le_one (μ := uibotFiniteIIDWordLaw 0)).trans (hpre.trans hCpre)
    · have hnle : (n : ℝ) ≤ T := (le_div_iff₀ hδ).mpr (le_of_not_ge hlarge)
      have he : 1 ≤ Real.exp (c*T - c*n) := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
          (show (0 : ℝ) ≤ c*T - c*n by nlinarith only [hc, hnle])
      calc
        _ ≤ 1 := measureReal_le_one
        _ ≤ 2*(2*m+1) := hpre
        _ ≤ (2*(2*m+1)) * Real.exp (c*T - c*n) :=
          le_mul_of_one_le_right (by positivity) he
        _ = C * Real.exp (-c*n) := by
          dsimp [C]
          rw [show c*T-c*n = c*T+(-c*n) by ring, Real.exp_add]
          ring
  simpa only [zpow_neg, zpow_natCast, inv_pow] using hmain

/-- Helper toward Proposition 3.9: a subexponential lower bound for the
actual admissibility probability transfers the proved iid pattern estimate
to eventual exponential decay after conditioning. The sole additional
hypothesis is the denominator bound, along the necessary admissible sizes;
this is a conditional helper, not a paper-facing local-limit statement. -/
theorem uibotFiniteIIDWordLaw_cond_rootWindow_exponential_of_subexponential
    (ℓ ρ m : ℕ) (v : Fin (2*m) → Fin 3) (δ : ℝ) (hδ : 0 < δ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      n + ℓ + ρ ≡ 0 [MOD 3] →
        Real.exp (-ε * (n : ℝ)) ≤
          (uibotFiniteIIDWordLaw n).real {w | KMSWWalkAdmissible ℓ ρ n w}) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ((uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]).real
        {w | δ ≤ |(Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
          n - (3 : ℝ)^(-((2*m : ℕ) : ℤ))|} ≤ C * Real.exp (-c*n) := by
  obtain ⟨c, hc, C, hC, htail⟩ :=
    uibotFiniteIIDWordLaw_rootWindow_exponential_concentration m v δ hδ
  refine ⟨c/2, half_pos hc, C, hC, ?_⟩
  filter_upwards [hsub (c/2) (half_pos hc), Filter.eventually_ge_atTop 1] with n hden hn
  by_cases hmod : n + ℓ + ρ ≡ 0 [MOD 3]
  · have hden' := hden hmod
    have hposReal : 0 < (uibotFiniteIIDWordLaw n).real
        {w | KMSWWalkAdmissible ℓ ρ n w} := (Real.exp_pos _).trans_le hden'
    have hpos : 0 < uibotFiniteIIDWordLaw n {w | KMSWWalkAdmissible ℓ ρ n w} := by
      exact (ENNReal.toReal_pos_iff.mp hposReal).1
    calc
      _ ≤ (uibotFiniteIIDWordLaw n).real
          {w | δ ≤ |(Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
            n - (3 : ℝ)^(-((2*m : ℕ) : ℤ))|} /
          (uibotFiniteIIDWordLaw n).real {w | KMSWWalkAdmissible ℓ ρ n w} :=
        uibotFiniteIIDWordLaw_cond_real_apply_le ℓ ρ n _ hpos
      _ ≤ (C * Real.exp (-c*n)) / Real.exp (-(c/2)*n) :=
        div_le_div₀ (mul_nonneg hC.le (Real.exp_nonneg _)) (htail n)
          (Real.exp_pos _) hden'
      _ = C * Real.exp (-(c/2)*n) := by
        rw [mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring
  · have he : {w : Fin (n-1) → Fin 3 | KMSWWalkAdmissible ℓ ρ n w} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hw
      exact hmod (kmswWalkAdmissible_size_modEq ℓ ρ n hn w hw)
    rw [he, cond_empty, measureReal_zero_apply]
    exact mul_nonneg hC.le (Real.exp_nonneg _)

/-- Helper toward Proposition 3.9: conditioned pattern deviations tend to
zero if the actual admissibility probability satisfies every positive
subexponential lower bound along the necessary size congruence. The
denominator hypothesis remains explicit and must be proved by assembly. -/
theorem uibotFiniteIIDWordLaw_cond_rootWindow_tendsto_zero_of_subexponential
    (ℓ ρ m : ℕ) (v : Fin (2*m) → Fin 3) (δ : ℝ) (hδ : 0 < δ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      n + ℓ + ρ ≡ 0 [MOD 3] →
        Real.exp (-ε * (n : ℝ)) ≤
          (uibotFiniteIIDWordLaw n).real {w | KMSWWalkAdmissible ℓ ρ n w}) :
    Filter.Tendsto (fun n : ℕ =>
      ((uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]).real
        {w | δ ≤ |(Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ) /
          n - (3 : ℝ)^(-((2*m : ℕ) : ℤ))|}) Filter.atTop (nhds 0) := by
  obtain ⟨c, hc, C, _hC, hbound⟩ :=
    uibotFiniteIIDWordLaw_cond_rootWindow_exponential_of_subexponential ℓ ρ m v δ hδ hsub
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Filter.Tendsto (fun n : ℕ => C * Real.exp (-c*(n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (Real.tendsto_exp_atBot.comp
        (hnat.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))).const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) hbound hlim

end WordLaw

end DirectedDistances.PaperProofs.Section3
