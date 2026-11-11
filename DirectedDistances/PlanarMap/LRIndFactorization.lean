/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBoltzmannMapLaw
public import DirectedDistances.PlanarMap.LRIndClassPredicates
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PlanarMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory




section DiscreteFactorization

variable {A B F : Type*}
variable [Countable A] [Countable B] [Countable F]

local instance instMeasurableSpaceA : MeasurableSpace A := ⊤
local instance instMeasurableSpaceB : MeasurableSpace B := ⊤
local instance instMeasurableSpaceF : MeasurableSpace F := ⊤




@[expose] noncomputable def normalizedWeightLaw (w : A → ℝ≥0∞) : Measure A :=
  (∑' a, w a)⁻¹ • Measure.sum (fun a => w a • Measure.dirac a)





theorem normalizedWeightLaw_equiv_prod
    (wA : A → ℝ≥0∞) (wB : B → ℝ≥0∞) (wF : F → ℝ≥0∞)
    (e : A × B ≃ F) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hZA0 : (∑' a, wA a) ≠ 0) (hZAtop : (∑' a, wA a) ≠ ⊤)
    (hZB0 : (∑' b, wB b) ≠ 0) (hZBtop : (∑' b, wB b) ≠ ⊤)
    (hweight : ∀ a b, wF (e (a, b)) = c * wA a * wB b) :
    normalizedWeightLaw wF =
      ((normalizedWeightLaw wA).prod (normalizedWeightLaw wB)).map e := by
  classical
  have hZF : (∑' f, wF f) = c * (∑' a, wA a) * (∑' b, wB b) := by
    calc
      (∑' f, wF f) = ∑' p : A × B, wF (e p) := by
        simpa using (e.symm.tsum_eq (fun p : A × B => wF (e p)))
      _ = ∑' p : A × B, c * (wA p.1 * wB p.2) := by
        refine tsum_congr fun p => ?_
        rw [hweight]
        simp only [mul_assoc]
      _ = c * (∑' p : A × B, wA p.1 * wB p.2) := by
        rw [ENNReal.tsum_mul_left]
      _ = c * (∑' a, ∑' b, wA a * wB b) := by rw [tsum_prod']
      _ = c * ((∑' a, wA a) * (∑' b, wB b)) := by
        congr 1
        calc
          (∑' a, ∑' b, wA a * wB b) = ∑' a, wA a * (∑' b, wB b) := by
            congr 1
            funext a
            rw [← ENNReal.tsum_mul_left]
          _ = (∑' a, wA a) * (∑' b, wB b) := by rw [ENNReal.tsum_mul_right]
      _ = c * (∑' a, wA a) * (∑' b, wB b) := by rw [mul_assoc]
  apply Measure.ext_of_singleton
  intro f
  rw [normalizedWeightLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_smul_dirac_singleton]
  have hpre : e ⁻¹' {f} = {e.symm f} := by
    ext p
    exact e.eq_symm_apply.symm
  have hrect : ({e.symm f} : Set (A × B)) =
      ({(e.symm f).1} : Set A) ×ˢ ({(e.symm f).2} : Set B) := by
    ext p
    simp
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton f)]
  rw [hpre, hrect]
  rw [Measure.prod_prod]
  simp only [normalizedWeightLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_smul_dirac_singleton]
  rw [hZF]
  have hepair : ((e.symm f).1, (e.symm f).2) = e.symm f := Prod.eta (e.symm f)
  have heval : e ((e.symm f).1, (e.symm f).2) = f := by
    rw [hepair, e.apply_symm_apply]
  have hwt := hweight (e.symm f).1 (e.symm f).2
  rw [heval] at hwt
  have hZAB0 : (∑' a, wA a) * (∑' b, wB b) ≠ 0 :=
    mul_ne_zero hZA0 hZB0
  have hZABtop : (∑' a, wA a) * (∑' b, wB b) ≠ ⊤ :=
    ENNReal.mul_ne_top hZAtop hZBtop
  rw [← ENNReal.div_eq_inv_mul, ← ENNReal.div_eq_inv_mul,
    ← ENNReal.div_eq_inv_mul, hwt]
  calc
    (c * wA (e.symm f).1 * wB (e.symm f).2) /
        (c * (∑' a, wA a) * ∑' b, wB b) =
        (c / c) *
          ((wA (e.symm f).1 * wB (e.symm f).2) /
            ((∑' a, wA a) * ∑' b, wB b)) := by
          simpa only [mul_assoc] using
            (ENNReal.mul_div_mul_comm (a := c)
              (b := wA (e.symm f).1 * wB (e.symm f).2)
              (c := c) (d := (∑' a, wA a) * ∑' b, wB b)
              (Or.inr hZABtop) (Or.inr hZAB0))
    _ = (wA (e.symm f).1 / (∑' a, wA a)) *
        (wB (e.symm f).2 / (∑' b, wB b)) := by
          rw [ENNReal.div_self hc0 hctop, one_mul,
            ENNReal.mul_div_mul_comm (Or.inr hZBtop) (Or.inr hZB0)]

end DiscreteFactorization

section DiscreteWeightConditionals

variable {Ω : Type*} [Countable Ω]

local instance instMeasurableSpaceΩ : MeasurableSpace Ω := ⊤





theorem normalizedWeightLaw_apply_set (w : Ω → ℝ≥0∞) (S : Set Ω) :
    normalizedWeightLaw w S =
      (∑' ω : {ω // ω ∈ S}, w ω.1) / (∑' ω, w ω) := by
  classical
  have htsum :
      (∑' ω : Ω, w ω * S.indicator 1 ω) =
        ∑' ω : {ω // ω ∈ S}, w ω.1 := by
    rw [tsum_subtype S]
    apply tsum_congr
    intro ω
    simp [Set.indicator_apply]
  have hmass :
      Measure.sum (fun ω : Ω => w ω • Measure.dirac ω) S =
        ∑' ω : Ω, w ω * S.indicator 1 ω := by
    rw [Measure.sum_apply _ (by simp)]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
      Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
  rw [normalizedWeightLaw, Measure.smul_apply, smul_eq_mul, hmass, htsum,
    div_eq_mul_inv, mul_comm]





theorem normalizedWeightLaw_singleton (w : Ω → ℝ≥0∞) (ω : Ω) :
    normalizedWeightLaw w {ω} = w ω / (∑' x, w x) := by
  rw [normalizedWeightLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_smul_dirac_singleton, div_eq_mul_inv, mul_comm]

omit [Countable Ω] in



theorem nonempty_of_weight_sum_ne_zero (w : Ω → ℝ≥0∞)
    (h : (∑' ω, w ω) ≠ 0) : Nonempty Ω := by
  by_contra hne
  have hEmpty : IsEmpty Ω := not_nonempty_iff.mp hne
  have hzero : ∀ ω, w ω = 0 := fun ω => False.elim (hEmpty.false ω)
  apply h
  rw [tsum_eq_zero_iff]
  exact hzero

omit [Countable Ω] in




theorem normalizedWeightLaw_isProbability (w : Ω → ℝ≥0∞)
    (h0 : (∑' ω, w ω) ≠ 0) (htop : (∑' ω, w ω) ≠ ⊤) :
    IsProbabilityMeasure (normalizedWeightLaw w) := by
  refine ⟨?_⟩
  rw [normalizedWeightLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  change (∑' ω, w ω)⁻¹ * (∑' ω, w ω) = 1
  exact ENNReal.inv_mul_cancel h0 htop

variable (S : Set Ω)

local instance instMeasurableSpaceSubtype : MeasurableSpace {ω // ω ∈ S} := ⊤





theorem normalizedWeightLaw_subtype_map_cond
    (w : Ω → ℝ≥0∞)
    (hZ0 : (∑' ω, w ω) ≠ 0) (hZtop : (∑' ω, w ω) ≠ ⊤) :
    (normalizedWeightLaw (fun ω : {ω // ω ∈ S} => w ω.1)).map Subtype.val =
      (normalizedWeightLaw w)[|S] := by
  classical
  apply Measure.ext_of_singleton
  intro ω
  have hμS := normalizedWeightLaw_apply_set w S
  have hμω := normalizedWeightLaw_apply_set w ({ω})
  have hSω :
      normalizedWeightLaw w (S ∩ {ω}) =
        if h : ω ∈ S then w ω / (∑' x, w x) else 0 := by
    by_cases h : ω ∈ S
    · simp [h, hμω]
    · simp [h]
  have hpre : Subtype.val ⁻¹' ({ω} : Set Ω) =
      if h : ω ∈ S then {⟨ω, h⟩} else ∅ := by
    by_cases h : ω ∈ S
    · have h' : (if h' : ω ∈ S then
          ({⟨ω, h'⟩} : Set {z // z ∈ S}) else ∅) = {⟨ω, h⟩} := by
        simp [h]
      rw [h']
      ext z
      change z.1 = ω ↔ z = ⟨ω, h⟩
      constructor
      · intro hz
        exact Subtype.ext hz
      · intro hz
        exact congrArg Subtype.val hz
    · have h' : (if h' : ω ∈ S then
          ({⟨ω, h'⟩} : Set {z // z ∈ S}) else ∅) = ∅ := by
        simp [h]
      rw [h']
      ext z
      change z.1 = ω ↔ False
      constructor
      · intro hz
        exact h (by rw [← hz]; exact z.property)
      · intro hz
        exact False.elim hz
  have hleft :
      normalizedWeightLaw (fun z : {z // z ∈ S} => w z.1)
          (Subtype.val ⁻¹' ({ω} : Set Ω)) =
        if h : ω ∈ S then
          w ω / (∑' z : {z // z ∈ S}, w z.1) else 0 := by
    rw [hpre]
    by_cases h : ω ∈ S
    · simp [h, normalizedWeightLaw_singleton]
    · simp [h]
  have hright : (normalizedWeightLaw w)[|S] {ω} =
      if h : ω ∈ S then w ω / (∑' z : {z // z ∈ S}, w z.1) else 0 := by
    rw [ProbabilityTheory.cond_apply (by simp : MeasurableSet S)
      (normalizedWeightLaw w) {ω}, hμS]
    by_cases h : ω ∈ S
    · have hmass : normalizedWeightLaw w (S ∩ {ω}) =
          w ω / (∑' x, w x) := by simpa [h] using hSω
      rw [hmass]
      have hcancel :
          ((∑' x : {x // x ∈ S}, w x.1) / (∑' x, w x))⁻¹ *
              (w ω / (∑' x, w x)) =
            w ω / (∑' x : {x // x ∈ S}, w x.1) := by
        rw [ENNReal.inv_div (Or.inl hZtop) (Or.inl hZ0)]
        calc
          (∑' x, w x) / (∑' x : {x // x ∈ S}, w x.1) *
              (w ω / (∑' x, w x)) =
            (w ω / (∑' x, w x)) *
              ((∑' x, w x) / (∑' x : {x // x ∈ S}, w x.1)) := by ac_rfl
          _ = w ω / (∑' x : {x // x ∈ S}, w x.1) :=
            ENNReal.div_mul_div_cancel hZ0 hZtop
      simpa [h] using hcancel
    · rw [hSω]
      simp [h]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton ω)]
  exact hleft.trans hright.symm

end DiscreteWeightConditionals

section BoltzmannFiberFactorization

variable (ℓ s r : ℕ) (x : XDP)

local instance instMeasurableSpaceML :
    MeasurableSpace {mL : BoltzmannSpace ℓ s // IsML x mL} := ⊤
local instance instMeasurableSpaceMR :
    MeasurableSpace {mR : BoltzmannSpace s r // IsMR x mR} := ⊤
local instance instMeasurableSpaceFiber :
    MeasurableSpace {m : BoltzmannSpace ℓ r // xdpLen x m = s} := ⊤





@[expose] noncomputable def boltzmannLRCutOutputPair
    (glue :
      ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR}) ≃
        {m : BoltzmannSpace ℓ r // xdpLen x m = s})
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    BoltzmannSpace ℓ r →
      ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR}) := fun m =>
      if hm : xdpLen x m = s then glue.symm ⟨m, hm⟩ else default





@[expose] noncomputable def boltzmannLRLeftCutOutput
    (glue :
      ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR}) ≃
        {m : BoltzmannSpace ℓ r // xdpLen x m = s})
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    BoltzmannSpace ℓ r → {mL : BoltzmannSpace ℓ s // IsML x mL} :=
  fun m => (boltzmannLRCutOutputPair ℓ s r x glue default m).1





@[expose] noncomputable def boltzmannLRRightCutOutput
    (glue :
      ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR}) ≃
        {m : BoltzmannSpace ℓ r // xdpLen x m = s})
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    BoltzmannSpace ℓ r → {mR : BoltzmannSpace s r // IsMR x mR} :=
  fun m => (boltzmannLRCutOutputPair ℓ s r x glue default m).2




theorem boltzmannLRCutOutputPair_glue
    (glue :
      ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR}) ≃
        {m : BoltzmannSpace ℓ r // xdpLen x m = s})
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) (p) :
    boltzmannLRCutOutputPair ℓ s r x glue default (glue p).1 = p := by
  simp [boltzmannLRCutOutputPair, (glue p).2]






theorem boltzmannLaw_cond_fiber_eq_map_glue
    (hC0 : boltzmannPartition ℓ r ≠ 0)
    (hCtop : boltzmannPartition ℓ r ≠ ⊤)
    (hZA0 : (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ 0)
    (hZAtop : (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ ⊤)
    (hZB0 : (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ 0)
    (hZBtop : (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ ⊤)
    (glue :
      ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR}) ≃
        {m : BoltzmannSpace ℓ r // xdpLen x m = s})
    (hweight : ∀ a b,
      boltzmannWeight (glue (a, b)).1 =
        (3 : ℝ≥0∞) ^ s * boltzmannWeight a.1 * boltzmannWeight b.1) :
    (boltzmannLaw ℓ r hC0 hCtop)[|
      boltzmannFiber (ℓ := ℓ) (r := r) x s] =
      ((normalizedWeightLaw (fun a : {mL : BoltzmannSpace ℓ s // IsML x mL} =>
          boltzmannWeight a.1)).prod
        (normalizedWeightLaw (fun b : {mR : BoltzmannSpace s r // IsMR x mR} =>
          boltzmannWeight b.1))).map (fun p => (glue p).1) := by
  classical
  let A := {mL : BoltzmannSpace ℓ s // IsML x mL}
  let B := {mR : BoltzmannSpace s r // IsMR x mR}
  let F := {m : BoltzmannSpace ℓ r // xdpLen x m = s}
  have hc0 : (3 : ℝ≥0∞) ^ s ≠ 0 := ENNReal.pow_ne_zero (by norm_num) s
  have hctop : (3 : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hfactor := normalizedWeightLaw_equiv_prod
    (wA := fun a : A => boltzmannWeight a.1)
    (wB := fun b : B => boltzmannWeight b.1)
    (wF := fun f : F => boltzmannWeight f.1)
    (e := glue) (c := (3 : ℝ≥0∞) ^ s)
    hc0 hctop hZA0 hZAtop hZB0 hZBtop hweight
  have hbridge := normalizedWeightLaw_subtype_map_cond
    (S := boltzmannFiber (ℓ := ℓ) (r := r) x s)
    (w := boltzmannWeight (ℓ := ℓ) (r := r)) hC0 hCtop
  calc
    (boltzmannLaw ℓ r hC0 hCtop)[|
        boltzmannFiber (ℓ := ℓ) (r := r) x s] =
      (normalizedWeightLaw (fun f : F => boltzmannWeight f.1)).map Subtype.val := by
        change (normalizedWeightLaw (boltzmannWeight (ℓ := ℓ) (r := r)))[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s] = _
        exact hbridge.symm
    _ = ((normalizedWeightLaw (fun a : A => boltzmannWeight a.1)).prod
          (normalizedWeightLaw (fun b : B => boltzmannWeight b.1))).map
          (fun p => (glue p).1) := by
        rw [hfactor, Measure.map_map (by fun_prop) (by fun_prop)]
        rfl






theorem boltzmannLaw_cond_fiber_IndepFun
    (hC0 : boltzmannPartition ℓ r ≠ 0)
    (hCtop : boltzmannPartition ℓ r ≠ ⊤)
    (hZA0 : (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ 0)
    (hZAtop : (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ ⊤)
    (hZB0 : (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ 0)
    (hZBtop : (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ ⊤)
    (hL0 : boltzmannPartition ℓ s ≠ 0)
    (hLtop : boltzmannPartition ℓ s ≠ ⊤)
    (hR0 : boltzmannPartition s r ≠ 0)
    (hRtop : boltzmannPartition s r ≠ ⊤)
    (glue :
      ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR}) ≃
        {m : BoltzmannSpace ℓ r // xdpLen x m = s})
    (hweight : ∀ a b,
      boltzmannWeight (glue (a, b)).1 =
        (3 : ℝ≥0∞) ^ s * boltzmannWeight a.1 * boltzmannWeight b.1)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    ProbabilityTheory.IndepFun
      (boltzmannLRLeftCutOutput ℓ s r x glue default)
      (boltzmannLRRightCutOutput ℓ s r x glue default)
      ((boltzmannLaw ℓ r hC0 hCtop)[|
        boltzmannFiber (ℓ := ℓ) (r := r) x s]) ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRLeftCutOutput ℓ s r x glue default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (boltzmannLaw ℓ s hL0 hLtop)[|{mL | IsML x mL}] ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRRightCutOutput ℓ s r x glue default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (boltzmannLaw s r hR0 hRtop)[|{mR | IsMR x mR}] := by
  classical
  let A := {mL : BoltzmannSpace ℓ s // IsML x mL}
  let B := {mR : BoltzmannSpace s r // IsMR x mR}
  let LA := normalizedWeightLaw (fun a : A => boltzmannWeight a.1)
  let LB := normalizedWeightLaw (fun b : B => boltzmannWeight b.1)
  let μ := (boltzmannLaw ℓ r hC0 hCtop)[|
    boltzmannFiber (ℓ := ℓ) (r := r) x s]
  let L := boltzmannLRLeftCutOutput ℓ s r x glue default
  let R := boltzmannLRRightCutOutput ℓ s r x glue default
  have hfactor := boltzmannLaw_cond_fiber_eq_map_glue ℓ s r x
    hC0 hCtop hZA0 hZAtop hZB0 hZBtop glue hweight
  have hLA : IsProbabilityMeasure LA :=
    normalizedWeightLaw_isProbability _ hZA0 hZAtop
  have hLB : IsProbabilityMeasure LB :=
    normalizedWeightLaw_isProbability _ hZB0 hZBtop
  have hleftComp : L ∘ (fun p : A × B => (glue p).1) = Prod.fst := by
    funext p
    change (boltzmannLRCutOutputPair ℓ s r x glue default ((glue p).1)).1 = p.1
    rw [boltzmannLRCutOutputPair_glue ℓ s r x glue default p]
  have hrightComp : R ∘ (fun p : A × B => (glue p).1) = Prod.snd := by
    funext p
    change (boltzmannLRCutOutputPair ℓ s r x glue default ((glue p).1)).2 = p.2
    rw [boltzmannLRCutOutputPair_glue ℓ s r x glue default p]
  let Q : BoltzmannSpace ℓ r → A × B :=
    fun m => (L m, R m)
  have hjoint : μ.map Q = LA.prod LB := by
    dsimp only [μ, Q]
    rw [hfactor, Measure.map_map (by fun_prop) (by fun_prop)]
    have hcomp : (fun m => (L m, R m)) ∘ (fun p : A × B => (glue p).1) = id := by
      funext p
      exact Prod.ext (congrFun hleftComp p) (congrFun hrightComp p)
    rw [hcomp, Measure.map_id]
  have hleftEvent (U : Set A) (hU : MeasurableSet U) :
      μ (L ⁻¹' U) = LA U := by
    have hpre : L ⁻¹' U = Q ⁻¹' (U ×ˢ Set.univ) := by
      ext m
      simp [Q]
    rw [hpre, ← Measure.map_apply (by fun_prop) (hU.prod MeasurableSet.univ),
      hjoint, Measure.prod_prod]
    simp [hLB.measure_univ]
  have hrightEvent (V : Set B) (hV : MeasurableSet V) :
      μ (R ⁻¹' V) = LB V := by
    have hpre : R ⁻¹' V = Q ⁻¹' (Set.univ ×ˢ V) := by
      ext m
      simp [Q]
    rw [hpre, ← Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hV),
      hjoint, Measure.prod_prod]
    simp [hLA.measure_univ]
  have hleftSub : μ.map L = LA := by
    apply Measure.ext
    intro U hU
    rw [Measure.map_apply (by fun_prop) hU]
    exact hleftEvent U hU
  have hrightSub : μ.map R = LB := by
    apply Measure.ext
    intro V hV
    rw [Measure.map_apply (by fun_prop) hV]
    exact hrightEvent V hV
  have hbridgeL : LA.map Subtype.val =
      (boltzmannLaw ℓ s hL0 hLtop)[|{mL | IsML x mL}] := by
    change (normalizedWeightLaw (fun a : A => boltzmannWeight a.1)).map
        Subtype.val =
      (normalizedWeightLaw (boltzmannWeight (ℓ := ℓ) (r := s)))[|
        {mL | IsML x mL}]
    exact normalizedWeightLaw_subtype_map_cond
      (S := {mL | IsML x mL})
      (w := boltzmannWeight (ℓ := ℓ) (r := s)) hL0 hLtop
  have hbridgeR : LB.map Subtype.val =
      (boltzmannLaw s r hR0 hRtop)[|{mR | IsMR x mR}] := by
    change (normalizedWeightLaw (fun b : B => boltzmannWeight b.1)).map
        Subtype.val =
      (normalizedWeightLaw (boltzmannWeight (ℓ := s) (r := r)))[|
        {mR | IsMR x mR}]
    exact normalizedWeightLaw_subtype_map_cond
      (S := {mR | IsMR x mR})
      (w := boltzmannWeight (ℓ := s) (r := r)) hR0 hRtop
  have hleftMarg : μ.map (Subtype.val ∘ L) =
      (boltzmannLaw ℓ s hL0 hLtop)[|{mL | IsML x mL}] := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hleftSub, hbridgeL]
  have hrightMarg : μ.map (Subtype.val ∘ R) =
      (boltzmannLaw s r hR0 hRtop)[|{mR | IsMR x mR}] := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hrightSub, hbridgeR]
  have hindep : ProbabilityTheory.IndepFun L R μ := by
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro U V hU hV
    have hpre : L ⁻¹' U ∩ R ⁻¹' V = Q ⁻¹' (U ×ˢ V) := by
      ext m
      simp [Q]
    rw [hpre, ← Measure.map_apply (by fun_prop) (hU.prod hV), hjoint,
      Measure.prod_prod]
    rw [← hleftEvent U hU, ← hrightEvent V hV]
  exact ⟨hindep, hleftMarg, hrightMarg⟩

end BoltzmannFiberFactorization

end DirectedDistances.PlanarMap
