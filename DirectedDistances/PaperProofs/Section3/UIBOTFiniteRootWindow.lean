/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteRadiusLawBridge
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Supporting lemmas for paper labels `prop-kmsw-uibot` (see CORRESPONDENCE.md). -/












public section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open scoped ENNReal BigOperators

private theorem uniform_mass {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Set α) :
    uniformCountingMeasure α s =
      (Fintype.card α : ℝ≥0∞)⁻¹ * (Nat.card s : ℝ≥0∞) := by
  rw [uniformCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply (Set.to_countable s).measurableSet, Set.encard,
    ENat.card_eq_coe_natCard]
  rfl

/-- The actual finite map marginal transported through the inverse procedure
equivalence is uniform on the actual admissible walk class. Procedure-reading -/
theorem uibotFiniteUniformSampleLaw_inverse_uniform
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    letI : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
    letI : MeasurableSpace (Fin n) := ⊤
    letI : MeasurableSpace (KMSWWalkClass ℓ ρ n) := ⊤
    (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map
      (fun p => (kmswProcedureEquiv ℓ ρ n hn).symm p.1) =
        uniformCountingMeasure (KMSWWalkClass ℓ ρ n) := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
  let : MeasurableSpace (Fin n) := ⊤
  let : MeasurableSpace (KMSWWalkClass ℓ ρ n) := ⊤
  change ((uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map
    ((kmswProcedureEquiv ℓ ρ n hn).symm ∘ Prod.fst)) = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    uibotFiniteUniformSampleLaw_map_fst]
  exact uniformCountingMeasure_map_of_bijective _ (kmswProcedureEquiv ℓ ρ n hn).symm.bijective

section WordLaw

local instance : MeasurableSpace (Fin 3) := ⊤
local instance : IsFiniteMeasure (uniformCountingMeasure (Fin 3)) := by
  constructor
  simp [uniformCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_univ, ENat.card_eq_coe_fintype_card]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by norm_num)) (by finiteness)



@[expose] noncomputable def uibotFiniteIIDWordLaw (n : ℕ) :
    Measure (Fin (n - 1) → Fin 3) :=
  Measure.pi (fun _ => uniformCountingMeasure (Fin 3))

/-- Product sampling and uniform counting on the full word carrier agree.
This is an identity proved from the singleton product formula, not a premise. -/
theorem uibotFiniteIIDWordLaw_eq_uniform (n : ℕ) :
    uibotFiniteIIDWordLaw n = uniformCountingMeasure (Fin (n - 1) → Fin 3) := by
  apply Measure.ext_of_singleton
  intro w
  rw [uibotFiniteIIDWordLaw, Measure.pi_singleton]
  simp [uniformCountingMeasure, ENNReal.inv_pow]

/-- Admissibility has positive probability whenever the actual finite map
carrier is nonempty. No assumed conditioning identity is used. Procedure -/
theorem uibotFiniteIIDWordLaw_admissible_pos
    (ℓ ρ n : ℕ) (hn : 1 ≤ n) (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    0 < uibotFiniteIIDWordLaw n {w | KMSWWalkAdmissible ℓ ρ n w} := by
  classical
  obtain ⟨q⟩ := hne
  let w := (kmswProcedureEquiv ℓ ρ n hn).symm q
  rw [uibotFiniteIIDWordLaw_eq_uniform]
  have hsub : {w.val} ⊆ {c | KMSWWalkAdmissible ℓ ρ n c} :=
    Set.singleton_subset_iff.mpr w.property
  apply lt_of_lt_of_le ?_ (measure_mono hsub)
  simp only [uniformCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_singleton, mul_one]
  exact ENNReal.inv_pos.mpr (by finiteness)

private theorem uniform_subtype_cond {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : α → Prop) [Fintype {x // p x}] :
    letI : MeasurableSpace {x // p x} := ⊤
    (uniformCountingMeasure {x // p x}).map (fun x => x.val) =
      (uniformCountingMeasure α)[|{x | p x}] := by
  classical
  let : MeasurableSpace {x // p x} := ⊤
  have hmass : uniformCountingMeasure α {x | p x} =
      (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card {x // p x} : ℝ≥0∞) := by
    have hc : Nat.card ↑{x | p x} = Fintype.card {x // p x} := by
      change Nat.card {x // p x} = _
      exact Nat.card_eq_fintype_card
    rw [uniform_mass, hc]
  apply Measure.ext_of_singleton
  intro x
  let : Nonempty α := ⟨x⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    cond_apply (Set.to_countable _).measurableSet, hmass]
  by_cases hx : p x
  · have hpre : (fun y : {x // p x} => y.val) ⁻¹' {x} = {⟨x, hx⟩} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    have hinter : {x | p x} ∩ {x} = {x} := by ext y; simp [hx]
    rw [hpre, hinter]
    simp only [uniformCountingMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.count_singleton, mul_one]
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (by finiteness)))
      (Or.inl (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero))), inv_inv]
    rw [mul_comm (Fintype.card α : ℝ≥0∞), mul_assoc,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by finiteness), mul_one]
  · have hpre : (fun y : {x // p x} => y.val) ⁻¹' {x} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hy
      exact hx (hy ▸ y.property)
    have hinter : {x | p x} ∩ {x} = ∅ := by ext y; simp [hx]
    rw [hpre, hinter, measure_empty, measure_empty, mul_zero]

/-- Uniform admissible words are exactly uniform iid words conditioned on
the actual endpoint-and-cone event. Procedure-reading finite-law helper for -/
theorem uibotFiniteWalk_uniform_eq_cond (ℓ ρ n : ℕ) :
    letI : MeasurableSpace (KMSWWalkClass ℓ ρ n) := ⊤
    (uniformCountingMeasure (KMSWWalkClass ℓ ρ n)).map
      (fun w : KMSWWalkClass ℓ ρ n => w.val) =
      (uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}] := by
  let : MeasurableSpace (KMSWWalkClass ℓ ρ n) := ⊤
  rw [uibotFiniteIIDWordLaw_eq_uniform]
  exact uniform_subtype_cond (KMSWWalkAdmissible ℓ ρ n)

end WordLaw

/-- A root `j : Fin n` supports the full radius-`m` increment window exactly
when its walk times `[j-m,j+m]` lie in `[0,n-1]`. -/
@[expose] def UIBOTRootWindowValid {n : ℕ} (m : ℕ) (j : Fin n) : Prop :=
  m ≤ j.val ∧ j.val + m ≤ n - 1

/-- Decidability of `UIBOTRootWindowValid`, used to define the finite root-window law. -/
instance instDecidableUIBOTRootWindowValid {n m : ℕ} (j : Fin n) :
    Decidable (UIBOTRootWindowValid m j) :=
  inferInstanceAs (Decidable (_ ∧ _))




@[expose] def uibotFiniteRootWindow {n : ℕ} (m : ℕ)
    (w : Fin (n - 1) → Fin 3) (j : Fin n) : Option (Fin (2*m) → Fin 3) :=
  if h : UIBOTRootWindowValid m j then
    some (fun i => w ⟨j.val - m + i.val, by
      have := i.isLt
      have := h.1
      have := h.2
      omega⟩)
  else none

/-- Exact validity characterization, including empty words and small sizes. -/
theorem uibotFiniteRootWindow_ne_none_iff {n m : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) :
    uibotFiniteRootWindow m w j ≠ none ↔ UIBOTRootWindowValid m j := by
  unfold uibotFiniteRootWindow
  split <;> simp_all

/-- Each window letter has global index `j-m+i`, with the integer centered
offset `i-m`; no code index is used as the root carrier. -/
theorem uibotFiniteRootWindow_index {n m : ℕ} (j : Fin n)
    (h : UIBOTRootWindowValid m j) (i : Fin (2*m)) :
    (j.val - m + i.val : ℕ) < n - 1 ∧
      ((j.val - m + i.val : ℕ) : ℤ) - (j.val : ℤ) = (i.val : ℤ) - (m : ℤ) := by
  have := h.1
  have := h.2
  have := i.isLt
  constructor <;> omega

/-- At most `2*m` of ALL `n` edge roots have an unavailable window.
This bound includes sizes for which no window is valid. -/
theorem uibotFiniteRootWindow_invalid_card (n m : ℕ) :
    Nat.card {j : Fin n // ¬ UIBOTRootWindowValid m j} ≤ 2*m := by
  classical
  let f : {j : Fin n // ¬ UIBOTRootWindowValid m j} → Fin (2*m) := fun j =>
    ⟨if j.val.val < m then j.val.val else m + (n-1-j.val.val), by
      have hj := j.val.isLt
      have hb := j.property
      simp only [UIBOTRootWindowValid, not_and, not_le] at hb
      split_ifs with h
      · omega
      · have := hb (by omega)
        omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he := congrArg Fin.val hab
    change (if a.val.val < m then a.val.val else m + (n-1-a.val.val)) =
      (if b.val.val < m then b.val.val else m + (n-1-b.val.val)) at he
    have ha := a.val.isLt
    have hb := b.val.isLt
    apply Subtype.ext
    apply Fin.ext
    split_ifs at he <;> omega
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

/-- Cemetery probability for an independently uniform all-edge index, with
the exact finite `n` normalization. No lower bound on `n` relative to `m`. -/
theorem uibotFiniteRootWindow_none_bound {n : ℕ} (_hn : 1 ≤ n) (m : ℕ)
    (w : Fin (n-1) → Fin 3) :
    letI : MeasurableSpace (Fin n) := ⊤
    uniformCountingMeasure (Fin n) {j | uibotFiniteRootWindow m w j = none} ≤
      (2*m : ℕ) / (n : ℝ≥0∞) := by
  let : MeasurableSpace (Fin n) := ⊤
  have he : {j | uibotFiniteRootWindow m w j = none} =
      {j | ¬ UIBOTRootWindowValid m j} := by
    ext j
    have h := uibotFiniteRootWindow_ne_none_iff (m := m) w j
    simp only [Set.mem_ofPred_eq]
    simpa only [not_not] using not_congr h
  rw [he, uniform_mass, Fintype.card_fin, div_eq_mul_inv, mul_comm]
  have hc : (Nat.card {j : Fin n // ¬ UIBOTRootWindowValid m j} : ℝ≥0∞) ≤ (2*m : ℕ) := by
    exact_mod_cast uibotFiniteRootWindow_invalid_card n m
  exact mul_le_mul_of_nonneg_right hc zero_le

/-- Real normalization of the same boundary estimate, including `n=1`. -/
theorem uibotFiniteRootWindow_none_bound_real {n : ℕ} (hn : 1 ≤ n) (m : ℕ)
    (w : Fin (n-1) → Fin 3) :
    letI : MeasurableSpace (Fin n) := ⊤
    (uniformCountingMeasure (Fin n) {j | uibotFiniteRootWindow m w j = none}).toReal ≤
      (2*m : ℕ) / (n : ℝ) := by
  let : MeasurableSpace (Fin n) := ⊤
  have h := uibotFiniteRootWindow_none_bound hn m w
  have ht : ((2*m : ℕ) / (n : ℝ≥0∞)) ≠ ∞ := by
    apply ENNReal.div_ne_top (by finiteness)
    exact_mod_cast (show n ≠ 0 by omega)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast] using ENNReal.toReal_mono ht h

section ActualRootLaw

local instance : MeasurableSpace (Fin 3) := ⊤
local instance (n : ℕ) : MeasurableSpace (Fin n) := ⊤
local instance (ℓ ρ n : ℕ) : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
local instance (ℓ ρ n : ℕ) : MeasurableSpace (KMSWWalkClass ℓ ρ n) := ⊤
local instance (n : ℕ) : SFinite (uniformCountingMeasure (Fin n)) := by
  unfold uniformCountingMeasure
  infer_instance

/-- The actual joint encoded-word and all-edge-root law is conditioned iid
words times an independent uniform `Fin n` root. Procedure reading toward -/
theorem uibotFiniteUniformSampleLaw_word_root
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map
      (fun p => (((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val, p.2)) =
      ((uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]).prod
        (uniformCountingMeasure (Fin n)) := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  have hw : (uniformCountingMeasure (KMSWMapIsoClass ℓ ρ n)).map
      (fun q => ((kmswProcedureEquiv ℓ ρ n hn).symm q).val) =
      (uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}] := by
    change (uniformCountingMeasure (KMSWMapIsoClass ℓ ρ n)).map
      ((fun w : KMSWWalkClass ℓ ρ n => w.val) ∘ (kmswProcedureEquiv ℓ ρ n hn).symm) = _
    rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      uniformCountingMeasure_map_of_bijective _ (kmswProcedureEquiv ℓ ρ n hn).symm.bijective,
      uibotFiniteWalk_uniform_eq_cond]
  rw [uibotFiniteUniformSampleLaw_eq, ← hw]
  have hp := Measure.map_prod_map (f := fun q : KMSWMapIsoClass ℓ ρ n =>
    ((kmswProcedureEquiv ℓ ρ n hn).symm q).val) (g := id)
    (uniformCountingMeasure (KMSWMapIsoClass ℓ ρ n))
    (uniformCountingMeasure (Fin n)) (measurable_of_countable _) measurable_id
  have hf : Prod.map (fun q : KMSWMapIsoClass ℓ ρ n =>
      ((kmswProcedureEquiv ℓ ρ n hn).symm q).val) (id : Fin n → Fin n) =
      (fun p => (((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val, p.2)) := by
    funext p
    rcases p with ⟨q, j⟩
    rfl
  rw [hf, Measure.map_id] at hp
  exact hp.symm

/-- Actual optional rooted increment-window law; the root remains one of all
`n` edges. No geometric convergence premise is used. -/
@[expose] noncomputable def uibotFiniteRootWindowLaw
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ) :
    letI : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
    Measure (Option (Fin (2*m) → Fin 3)) :=
  letI : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
  (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map
    (fun p => uibotFiniteRootWindow m ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2)

/-- Finite pattern probability is the conditioned-iid expectation of the
empirical frequency of matching valid starts, normalized by ALL `n` roots.
Unavailable starts contribute cemetery mass, not a zero-valued word. -/
theorem uibotFiniteRootWindowLaw_pattern_mass
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ) (v : Fin (2*m) → Fin 3) :
    letI : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
    uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m {some v} =
      ∫⁻ w, (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ≥0∞) /
        (n : ℝ≥0∞) ∂(uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}] := by
  let : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
  let := uibotFiniteMapFintype ℓ ρ n hn
  have he : uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m =
      (((uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]).prod
        (uniformCountingMeasure (Fin n))).map
          (fun p => uibotFiniteRootWindow m p.1 p.2) := by
    rw [← uibotFiniteUniformSampleLaw_word_root ℓ ρ n hℓ hρ hn hne,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  rw [he, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.prod_apply (Set.to_countable _).measurableSet]
  apply lintegral_congr
  intro w
  rw [uniform_mass, Fintype.card_fin, div_eq_mul_inv, mul_comm]
  rfl

/-- The actual finite uniform-map sample has cemetery probability at most
`2m/n`, without a conditioning-probability loss. This uses the independent
all-edge root marginal and holds even when every window is unavailable. -/
theorem uibotFiniteRootWindowLaw_none_bound
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ) :
    letI : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
    uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m {none} ≤
      (2*m : ℕ) / (n : ℝ≥0∞) := by
  let : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
  let := uibotFiniteMapFintype ℓ ρ n hn
  have he : (fun p : KMSWMapIsoClass ℓ ρ n × Fin n =>
      uibotFiniteRootWindow m ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2) ⁻¹'
        {none} = Prod.snd ⁻¹' {j : Fin n | ¬UIBOTRootWindowValid m j} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    simpa only [not_not] using
      not_congr (uibotFiniteRootWindow_ne_none_iff (m := m)
        ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2)
  rw [uibotFiniteRootWindowLaw, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _), he,
    ← Measure.map_apply measurable_snd (Set.to_countable _).measurableSet,
    uibotFiniteUniformSampleLaw_map_snd, uniform_mass, Fintype.card_fin,
    div_eq_mul_inv, mul_comm]
  have hc : (Nat.card {j : Fin n // ¬UIBOTRootWindowValid m j} : ℝ≥0∞) ≤ (2*m : ℕ) := by
    exact_mod_cast uibotFiniteRootWindow_invalid_card n m
  exact mul_le_mul_of_nonneg_right hc zero_le

end ActualRootLaw

/-- The inverse equivalence used by the finite law is the source inverse
Peano-height walk's code, not an arbitrary bijection. Procedure reading, -/
theorem uibotProcedureInverse_eq (ℓ ρ n : ℕ) (hn : 1 ≤ n)
    (q : KMSWMapIsoClass ℓ ρ n) :
    (kmswProcedureEquiv ℓ ρ n hn).symm q = kmswClassInverseWalkClass q := by
  apply (kmswProcedureEquiv ℓ ρ n hn).injective
  rw [Equiv.apply_symm_apply]
  exact (kmswToMapIsoClass_comp_inverse_of_prefix
    (kmswPeanoPrefixExistsFinal_holds ℓ ρ n) hn q).symm

/-- The root is the source edge `λ_{j+1}` in its finite one-based notation,
and position `j` of its inverse walk is the same Peano index. -/
theorem uibotFiniteRootWindow_peano_alignment {ℓ ρ n : ℕ}
    (R : KMSWMapRep ℓ ρ n) (j : Fin n) :
    (uibotPeanoRootedAt R j).root =
      (firstVisitOrder R.B).get ⟨j.val, by
        rw [firstVisitOrder_length, R.edges]
        exact j.isLt⟩ := rfl

/-- All centered positions use exact source times `j+i`, `-m ≤ i ≤ m`.
The subtraction is between finite inverse-walk positions and uses the same -/
theorem uibotFiniteRootWindow_source_positions {ℓ ρ n m : ℕ} (hn : 1 ≤ n)
    (q : KMSWMapIsoClass ℓ ρ n) (j : Fin n) (h : UIBOTRootWindowValid m j)
    (k : Fin (2*m+1)) :
    integrateCodes (finiteCodeExtend ((kmswProcedureEquiv ℓ ρ n hn).symm q).val)
        (j.val-m+k.val) -
      integrateCodes (finiteCodeExtend ((kmswProcedureEquiv ℓ ρ n hn).symm q).val) j.val =
      kmswClassInverseWalk q ⟨j.val-m+k.val, by
        have := h.1; have := h.2; have := k.isLt; omega⟩ -
        kmswClassInverseWalk q j := by
  rw [uibotProcedureInverse_eq]
  exact congrArg₂ (· - ·)
    (integrateCodes_kmswClassInverseWalkClass q _ (by
      have := h.1; have := h.2; have := k.isLt; omega))
    (integrateCodes_kmswClassInverseWalkClass q _ j.isLt)

/-- Recover every window letter from a successful optional observation. -/
theorem uibotFiniteRootWindow_letter {n m : ℕ} (w : Fin (n-1) → Fin 3)
    (j : Fin n) (h : UIBOTRootWindowValid m j) (v : Fin (2*m) → Fin 3)
    (hv : uibotFiniteRootWindow m w j = some v) (i : Fin (2*m)) :
    v i = w ⟨j.val-m+i.val, (uibotFiniteRootWindow_index j h i).1⟩ := by
  unfold uibotFiniteRootWindow at hv
  rw [dite_eq_left h] at hv
  exact (congrFun (Option.some.inj hv) i).symm

/-- Integrating a successful increment window and centering at time `m`
gives the exact finite source displacement `Z(j+i)-Z(j)` at every offset,
including both endpoints. Outside this valid event no source path is defined. -/
theorem uibotFiniteRootWindow_integrate {n m : ℕ} (w : Fin (n-1) → Fin 3)
    (j : Fin n) (h : UIBOTRootWindowValid m j) (v : Fin (2*m) → Fin 3)
    (hv : uibotFiniteRootWindow m w j = some v) (k : Fin (2*m+1)) :
    let c : ℕ → Fin 3 := fun t => if ht : t < 2*m then v ⟨t, ht⟩ else 0
    integrateCodes c k.val - integrateCodes c m =
      integrateCodes (finiteCodeExtend w) (j.val-m+k.val) -
        integrateCodes (finiteCodeExtend w) j.val := by
  dsimp only
  let c : ℕ → Fin 3 := fun t => if ht : t < 2*m then v ⟨t, ht⟩ else 0
  have hs (t : ℕ) (ht : t ≤ 2*m) :
      integrateCodes c t = integrateCodes (finiteCodeExtend w) (j.val-m+t) -
        integrateCodes (finiteCodeExtend w) (j.val-m) := by
    have he : integrateCodes (finiteCodeExtend w) (j.val-m+t) =
        integrateCodes (finiteCodeExtend w) (j.val-m) + integrateCodes c t := by
      rw [integrateCodes, Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < 2*m := lt_of_lt_of_le (Finset.mem_range.mp hi) ht
      have hb := (uibotFiniteRootWindow_index j h ⟨i, hi'⟩).1
      simp only [c, dite_eq_left hi', finiteCodeExtend, dite_eq_left hb]
      rw [uibotFiniteRootWindow_letter w j h v hv ⟨i, hi'⟩]
    rw [he]
    abel
  rw [hs k.val (by have := k.isLt; omega), hs m (by omega)]
  have hj : j.val-m+m = j.val := Nat.sub_add_cancel h.1
  rw [hj]
  abel

/-- A successful actual finite window integrates to the centered source
inverse walk. In the zero-based convention its root is `λ_{j+1}` and its -/
theorem uibotFiniteRootWindow_source_integrate {ℓ ρ n m : ℕ} (hn : 1 ≤ n)
    (q : KMSWMapIsoClass ℓ ρ n) (j : Fin n) (h : UIBOTRootWindowValid m j)
    (v : Fin (2*m) → Fin 3)
    (hv : uibotFiniteRootWindow m ((kmswProcedureEquiv ℓ ρ n hn).symm q).val j = some v)
    (k : Fin (2*m+1)) :
    let c : ℕ → Fin 3 := fun t => if ht : t < 2*m then v ⟨t, ht⟩ else 0
    integrateCodes c k.val - integrateCodes c m =
      kmswClassInverseWalk q ⟨j.val-m+k.val, by
        have := h.1; have := h.2; have := k.isLt; omega⟩ -
        kmswClassInverseWalk q j :=
  (uibotFiniteRootWindow_integrate _ j h v hv k).trans
    (uibotFiniteRootWindow_source_positions hn q j h k)

/-- Exact empirical frequency of a pattern among valid starts, divided by
the number of ALL edge roots. This is zero if there are no valid starts. -/
theorem uibotFiniteRootWindow_pattern_frequency {n m : ℕ}
    (w : Fin (n-1) → Fin 3) (v : Fin (2*m) → Fin 3) :
    letI : MeasurableSpace (Fin n) := ⊤
    uniformCountingMeasure (Fin n) {j | uibotFiniteRootWindow m w j = some v} =
      (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ≥0∞) /
        (n : ℝ≥0∞) := by
  let : MeasurableSpace (Fin n) := ⊤
  rw [uniform_mass, Fintype.card_fin, div_eq_mul_inv, mul_comm]
  rfl

/-- Every total word-valued extension agreeing on valid windows has pattern
mass between the exact valid-start frequency and that frequency plus `2m/n`.
The agreement premise describes extensions only; it assumes no probability
or convergence conclusion. All small-size and empty-valid-set cases remain. -/
theorem uibotFiniteRootWindow_pattern_boundary {n m : ℕ} (hn : 1 ≤ n)
    (w : Fin (n-1) → Fin 3) (W : Fin n → (Fin (2*m) → Fin 3))
    (hW : ∀ j, UIBOTRootWindowValid m j → uibotFiniteRootWindow m w j = some (W j))
    (v : Fin (2*m) → Fin 3) :
    letI : MeasurableSpace (Fin n) := ⊤
    let p := (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ≥0∞) /
      (n : ℝ≥0∞)
    p ≤ uniformCountingMeasure (Fin n) {j | W j = v} ∧
      uniformCountingMeasure (Fin n) {j | W j = v} ≤ p + (2*m : ℕ)/(n : ℝ≥0∞) := by
  let : MeasurableSpace (Fin n) := ⊤
  dsimp only
  rw [← uibotFiniteRootWindow_pattern_frequency w v]
  constructor
  · apply measure_mono
    intro j hj
    have hj' : uibotFiniteRootWindow m w j = some v := hj
    have hh : UIBOTRootWindowValid m j :=
      (uibotFiniteRootWindow_ne_none_iff w j).mp (by rw [hj']; exact Option.some_ne_none v)
    exact Option.some.inj ((hW j hh).symm.trans hj')
  · calc
      _ ≤ uniformCountingMeasure (Fin n)
          ({j | uibotFiniteRootWindow m w j = some v} ∪
            {j | uibotFiniteRootWindow m w j = none}) := by
        apply measure_mono
        intro j hj
        by_cases hh : UIBOTRootWindowValid m j
        · exact Or.inl ((hW j hh).trans (congrArg some hj))
        · apply Or.inr
          simpa only [Set.mem_ofPred_eq, not_not] using
            (not_congr (uibotFiniteRootWindow_ne_none_iff (m := m) w j)).mpr hh
      _ ≤ _ + _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl (uibotFiniteRootWindow_none_bound hn m w)

/-- If the finite walk is too short, every root has a cemetery window.
In particular, a positive-radius window at the single-edge map is unavailable. -/
theorem uibotFiniteRootWindow_of_small {n m : ℕ} (hsmall : n ≤ 2*m)
    (w : Fin (n-1) → Fin 3) (j : Fin n) :
    uibotFiniteRootWindow m w j = none := by
  have hh : ¬UIBOTRootWindowValid m j := by
    intro h
    have := h.1
    have := h.2
    have := j.isLt
    omega
  simpa only [not_not] using
    (not_congr (uibotFiniteRootWindow_ne_none_iff (m := m) w j)).mpr hh

/-- The actual finite sample has cemetery mass ONE, rather than zero, when
no centered window fits. This remains compatible with the bound `2m/n`. -/
theorem uibotFiniteRootWindowLaw_none_of_small
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ) (hsmall : n ≤ 2*m) :
    letI : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
    uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m {none} = 1 := by
  let : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
  let : MeasurableSpace (Fin n) := ⊤
  let : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
  let := uibotFiniteMapFintype ℓ ρ n hn
  let := uibotFiniteUniformSampleLaw_probability ℓ ρ n hℓ hρ hn hne
  rw [uibotFiniteRootWindowLaw, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have he : (fun p : KMSWMapIsoClass ℓ ρ n × Fin n =>
      uibotFiniteRootWindow m ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2) ⁻¹'
        {none} = Set.univ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact uibotFiniteRootWindow_of_small hsmall _ _
  rw [he, measure_univ]

/-- Real normalization of the actual independent-root cemetery bound. -/
theorem uibotFiniteRootWindowLaw_none_bound_real
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ) :
    letI : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
    (uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m {none}).toReal ≤
      (2*m : ℕ) / (n : ℝ) := by
  let : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
  have ht : ((2*m : ℕ)/(n : ℝ≥0∞)) ≠ ∞ := by
    apply ENNReal.div_ne_top (by finiteness)
    exact_mod_cast (show n ≠ 0 by omega)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast] using
    ENNReal.toReal_mono ht (uibotFiniteRootWindowLaw_none_bound ℓ ρ n hℓ hρ hn hne m)

section ActualPatternBoundary

local instance : MeasurableSpace (Fin 3) := ⊤
local instance (n : ℕ) : MeasurableSpace (Fin n) := ⊤
local instance (ℓ ρ n : ℕ) : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤

/-- Under the actual finite uniform-map sample, every total extension of the
valid increment window has pattern mass within `2m/n` of the exact conditional
empirical frequency. The root and word keep the actual joint law proved above;
the sole extension premise says that its values agree on valid windows. -/
theorem uibotFiniteRootWindowLaw_pattern_boundary
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) (m : ℕ)
    (W : KMSWMapIsoClass ℓ ρ n × Fin n → (Fin (2*m) → Fin 3))
    (hW : ∀ p, UIBOTRootWindowValid m p.2 →
      uibotFiniteRootWindow m ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2 = some (W p))
    (v : Fin (2*m) → Fin 3) :
    let p := ∫⁻ w, (Nat.card {j : Fin n // uibotFiniteRootWindow m w j = some v} : ℝ≥0∞) /
      (n : ℝ≥0∞) ∂(uibotFiniteIIDWordLaw n)[|{w | KMSWWalkAdmissible ℓ ρ n w}]
    p ≤ uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne {s | W s = v} ∧
      uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne {s | W s = v} ≤
        p + (2*m : ℕ)/(n : ℝ≥0∞) := by
  let : MeasurableSpace (Option (Fin (2*m) → Fin 3)) := ⊤
  let := uibotFiniteMapFintype ℓ ρ n hn
  dsimp only
  rw [← uibotFiniteRootWindowLaw_pattern_mass ℓ ρ n hℓ hρ hn hne m v]
  let μ := uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne
  let f := fun p : KMSWMapIsoClass ℓ ρ n × Fin n =>
    uibotFiniteRootWindow m ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2
  have hm : ∀ t, uibotFiniteRootWindowLaw ℓ ρ n hℓ hρ hn hne m t = μ (f ⁻¹' t) := by
    intro t
    exact Measure.map_apply (measurable_of_countable _) (Set.to_countable t).measurableSet
  rw [hm]
  constructor
  · apply measure_mono
    intro s hs
    have hs' : f s = some v := hs
    have hh : UIBOTRootWindowValid m s.2 :=
      (uibotFiniteRootWindow_ne_none_iff
        ((kmswProcedureEquiv ℓ ρ n hn).symm s.1).val s.2).mp (by
          change f s ≠ none
          rw [hs']
          exact Option.some_ne_none v)
    exact Option.some.inj ((hW s hh).symm.trans hs')
  · have hb : μ (f ⁻¹' {none}) ≤ (2*m : ℕ)/(n : ℝ≥0∞) := by
      rw [← hm]
      exact uibotFiniteRootWindowLaw_none_bound ℓ ρ n hℓ hρ hn hne m
    calc
      _ ≤ μ ((f ⁻¹' {some v}) ∪ (f ⁻¹' {none})) := by
        apply measure_mono
        intro s hs
        by_cases hh : UIBOTRootWindowValid m s.2
        · exact Or.inl ((hW s hh).trans (congrArg some hs))
        · apply Or.inr
          change f s = none
          simpa only [not_not] using (not_congr
            (uibotFiniteRootWindow_ne_none_iff (m := m)
              ((kmswProcedureEquiv ℓ ρ n hn).symm s.1).val s.2)).mpr hh
      _ ≤ _ + _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl hb

end ActualPatternBoundary

end DirectedDistances.PaperProofs.Section3
