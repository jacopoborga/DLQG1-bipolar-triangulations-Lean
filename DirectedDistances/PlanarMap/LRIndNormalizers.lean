/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.LRIndClassEquiv

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PlanarMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

private theorem lrFiberWeightSum_eq_lrFactor
    {x : XDP} {ℓ s r : ℕ} (d : LRCutGlueRepData x ℓ s r) :
    (∑' m : boltzmannFiber (ℓ := ℓ) (r := r) x s,
      boltzmannWeight m.1) =
      (3 : ℝ≥0∞) ^ s *
        (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
          boltzmannWeight a.1) *
        (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
          boltzmannWeight b.1) := by
  classical
  let A := {mL : BoltzmannSpace ℓ s // IsML x mL}
  let B := {mR : BoltzmannSpace s r // IsMR x mR}
  let F := boltzmannFiber (ℓ := ℓ) (r := r) x s
  let e := lrClassEquiv d
  let wA : A → ℝ≥0∞ := fun a => boltzmannWeight a.1
  let wB : B → ℝ≥0∞ := fun b => boltzmannWeight b.1
  let c : ℝ≥0∞ := (3 : ℝ≥0∞) ^ s
  calc
    (∑' m : F, boltzmannWeight m.1) =
        ∑' p : A × B, boltzmannWeight (e p).1 := by
      exact (e.tsum_eq (fun m : F => boltzmannWeight m.1)).symm
    _ = ∑' p : A × B, c * (wA p.1 * wB p.2) := by
      apply tsum_congr
      intro p
      change boltzmannWeight (lrClassEquiv d p).1 = _
      calc
        boltzmannWeight (lrClassEquiv d p).1 =
            (3 : ℝ≥0∞) ^ s * boltzmannWeight p.1.1 * boltzmannWeight p.2.1 :=
          lrClassEquiv_weight d p.1 p.2
        _ = c * (wA p.1 * wB p.2) := by
          dsimp [c, wA, wB]
          ac_rfl
    _ = c * (∑' p : A × B, wA p.1 * wB p.2) := by
      rw [ENNReal.tsum_mul_left]
    _ = c * ((∑' a : A, wA a) * (∑' b : B, wB b)) := by
      congr 1
      calc
        (∑' p : A × B, wA p.1 * wB p.2) =
            ∑' a : A, ∑' b : B, wA a * wB b :=
          tsum_prod (f := fun a b => wA a * wB b)
        _ = ∑' a : A, wA a * (∑' b : B, wB b) := by
          apply tsum_congr
          intro a
          exact ENNReal.tsum_mul_left
        _ = (∑' a : A, wA a) * (∑' b : B, wB b) :=
          ENNReal.tsum_mul_right
    _ = (3 : ℝ≥0∞) ^ s *
          (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
            boltzmannWeight a.1) *
          (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
            boltzmannWeight b.1) := by
      dsimp [c, wA, wB]
      ac_rfl

private theorem lrIndNormalizers
    {x : XDP} {ℓ s r : ℕ} (d : LRCutGlueRepData x ℓ s r)
    (hC0 : boltzmannPartition ℓ r ≠ 0)
    (hCtop : boltzmannPartition ℓ r ≠ ⊤)
    (hpos : boltzmannLaw ℓ r hC0 hCtop
      (boltzmannFiber (ℓ := ℓ) (r := r) x s) ≠ 0) :
    (∑' m : boltzmannFiber (ℓ := ℓ) (r := r) x s,
      boltzmannWeight m.1) ≠ 0 ∧
    (∑' m : boltzmannFiber (ℓ := ℓ) (r := r) x s,
      boltzmannWeight m.1) ≠ ⊤ ∧
    (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ 0 ∧
    (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ ⊤ ∧
    (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ 0 ∧
    (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ ⊤ := by
  classical
  let F := boltzmannFiber (ℓ := ℓ) (r := r) x s
  let μ := boltzmannLaw ℓ r hC0 hCtop
  have hpos' : μ[|F] ≠ 0 := by
    simpa [μ] using hpos
  have hμF : μ F ≠ 0 := by
    intro hμF0
    exact hpos' (ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hμF0)
  have hfiberMass :
      μ F = (∑' m : F, boltzmannWeight m.1) / boltzmannPartition ℓ r := by
    exact boltzmannLaw_fiber hC0 hCtop x s
  have hfiber0 : (∑' m : F, boltzmannWeight m.1) ≠ 0 := by
    have hdiv : (∑' m : F, boltzmannWeight m.1) / boltzmannPartition ℓ r ≠ 0 := by
      rw [← hfiberMass]
      exact hμF
    exact (ENNReal.div_ne_zero.mp hdiv).1
  have hfiber_le :
      (∑' m : F, boltzmannWeight m.1) ≤ boltzmannPartition ℓ r := by
    calc
      (∑' m : F, boltzmannWeight m.1) ≤
          ∑' m : (Set.univ : Set (BoltzmannSpace ℓ r)), boltzmannWeight m.1 :=
        tsum_le_of_subset (Set.subset_univ F)
      _ = boltzmannPartition ℓ r := by
        simp [boltzmannPartition]
  have hfiber_top : (∑' m : F, boltzmannWeight m.1) ≠ ⊤ := by
    intro htop
    apply hCtop
    exact top_unique (htop ▸ hfiber_le)
  have hsumEq := lrFiberWeightSum_eq_lrFactor d
  let ZA := ∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL}, boltzmannWeight a.1
  let ZB := ∑' b : {mR : BoltzmannSpace s r // IsMR x mR}, boltzmannWeight b.1
  let c : ℝ≥0∞ := (3 : ℝ≥0∞) ^ s
  have hsumEq' : (∑' m : F, boltzmannWeight m.1) = c * ZA * ZB := by
    simpa [ZA, ZB, c] using hsumEq
  have hZA0 : ZA ≠ 0 := by
    intro hZA
    apply hfiber0
    rw [hsumEq', hZA]
    simp
  have hZB0 : ZB ≠ 0 := by
    intro hZB
    apply hfiber0
    rw [hsumEq', hZB]
    simp
  have hc0 : c ≠ 0 := by
    exact ENNReal.pow_ne_zero (by norm_num) s
  have hprod_top : c * ZA * ZB ≠ ⊤ := by
    intro htop
    apply hfiber_top
    rw [hsumEq', htop]
  have hCZAtop : c * ZA ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_left hprod_top hZB0).ne
  have hZA_top : ZA ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_right hCZAtop hc0).ne
  have hCZA0 : c * ZA ≠ 0 := by
    simp [hc0, hZA0]
  have hZB_top : ZB ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_right hprod_top hCZA0).ne
  exact ⟨hfiber0, hfiber_top, hZA0, hZA_top, hZB0, hZB_top⟩

local instance instMeasurableSpaceLRNormalizersML {x : XDP} {ℓ s : ℕ} :
    MeasurableSpace {mL : BoltzmannSpace ℓ s // IsML x mL} :=
  instMeasurableSpaceLRML
local instance instMeasurableSpaceLRNormalizersMR {x : XDP} {s r : ℕ} :
    MeasurableSpace {mR : BoltzmannSpace s r // IsMR x mR} :=
  instMeasurableSpaceLRMR
local instance instMeasurableSpaceLRNormalizersFiber {x : XDP} {ℓ r s : ℕ} :
    MeasurableSpace (boltzmannFiber (ℓ := ℓ) (r := r) x s) :=
  instMeasurableSpaceLRFiber



theorem lem_lr_ind_reduced {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (hC0 : boltzmannPartition ℓ r ≠ 0)
    (hCtop : boltzmannPartition ℓ r ≠ ⊤)
    (hpos : boltzmannLaw ℓ r hC0 hCtop
      (boltzmannFiber (ℓ := ℓ) (r := r) x s) ≠ 0)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    ProbabilityTheory.IndepFun
      (boltzmannLRLeftCutOutput ℓ s r x (lrClassEquiv d) default)
      (boltzmannLRRightCutOutput ℓ s r x (lrClassEquiv d) default)
      ((boltzmannLaw ℓ r hC0 hCtop)[|
        boltzmannFiber (ℓ := ℓ) (r := r) x s]) ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRLeftCutOutput ℓ s r x
          (lrClassEquiv d) default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (normalizedWeightLaw (fun a : {mL : BoltzmannSpace ℓ s // IsML x mL} =>
        boltzmannWeight a.1)).map Subtype.val ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRRightCutOutput ℓ s r x
          (lrClassEquiv d) default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (normalizedWeightLaw (fun b : {mR : BoltzmannSpace s r // IsMR x mR} =>
        boltzmannWeight b.1)).map Subtype.val := by
  classical
  rcases lrIndNormalizers d hC0 hCtop hpos with
    ⟨_, _, hZA0, hZAtop, hZB0, hZBtop⟩
  let A := {mL : BoltzmannSpace ℓ s // IsML x mL}
  let B := {mR : BoltzmannSpace s r // IsMR x mR}
  let LA := normalizedWeightLaw (fun a : A => boltzmannWeight a.1)
  let LB := normalizedWeightLaw (fun b : B => boltzmannWeight b.1)
  let μ := (boltzmannLaw ℓ r hC0 hCtop)[|
    boltzmannFiber (ℓ := ℓ) (r := r) x s]
  let glue := lrClassEquiv d
  let L := boltzmannLRLeftCutOutput ℓ s r x glue default
  let R := boltzmannLRRightCutOutput ℓ s r x glue default
  have hfactor := boltzmannLaw_cond_fiber_eq_map_glue ℓ s r x
    hC0 hCtop hZA0 hZAtop hZB0 hZBtop glue (by
      intro a b
      exact lrClassEquiv_weight d a b)
  have hLA : IsProbabilityMeasure LA := normalizedWeightLaw_isProbability _ hZA0 hZAtop
  have hLB : IsProbabilityMeasure LB := normalizedWeightLaw_isProbability _ hZB0 hZBtop
  have hleftComp : L ∘ (fun p : A × B => (glue p).1) = Prod.fst := by
    funext p
    change (boltzmannLRCutOutputPair ℓ s r x glue default ((glue p).1)).1 = p.1
    rw [boltzmannLRCutOutputPair_glue ℓ s r x glue default p]
  have hrightComp : R ∘ (fun p : A × B => (glue p).1) = Prod.snd := by
    funext p
    change (boltzmannLRCutOutputPair ℓ s r x glue default ((glue p).1)).2 = p.2
    rw [boltzmannLRCutOutputPair_glue ℓ s r x glue default p]
  let Q : BoltzmannSpace ℓ r → A × B := fun m => (L m, R m)
  have hjoint : μ.map Q = LA.prod LB := by
    dsimp only [μ, Q]
    rw [hfactor, Measure.map_map (by fun_prop) (by fun_prop)]
    have hcomp :
        (fun m => (L m, R m)) ∘ (fun p : A × B => (glue p).1) = id := by
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
  have hindep : ProbabilityTheory.IndepFun L R μ := by
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro U V hU hV
    have hpre : L ⁻¹' U ∩ R ⁻¹' V = Q ⁻¹' (U ×ˢ V) := by
      ext m
      simp [Q]
    rw [hpre, ← Measure.map_apply (by fun_prop) (hU.prod hV), hjoint,
      Measure.prod_prod]
    rw [← hleftEvent U hU, ← hrightEvent V hV]
  have hleftMarg : μ.map (Subtype.val ∘ L) = LA.map Subtype.val := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hleftSub]
  have hrightMarg : μ.map (Subtype.val ∘ R) = LB.map Subtype.val := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hrightSub]
  exact ⟨hindep, hleftMarg, hrightMarg⟩



theorem lem_lr_ind_from_fiber_pos {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (hC0 : boltzmannPartition ℓ r ≠ 0)
    (hCtop : boltzmannPartition ℓ r ≠ ⊤)
    (hpos : boltzmannLaw ℓ r hC0 hCtop
      (boltzmannFiber (ℓ := ℓ) (r := r) x s) ≠ 0)
    (hL0 : boltzmannPartition ℓ s ≠ 0)
    (hLtop : boltzmannPartition ℓ s ≠ ⊤)
    (hR0 : boltzmannPartition s r ≠ 0)
    (hRtop : boltzmannPartition s r ≠ ⊤)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    ProbabilityTheory.IndepFun
      (boltzmannLRLeftCutOutput ℓ s r x (lrClassEquiv d) default)
      (boltzmannLRRightCutOutput ℓ s r x (lrClassEquiv d) default)
      ((boltzmannLaw ℓ r hC0 hCtop)[|
        boltzmannFiber (ℓ := ℓ) (r := r) x s]) ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRLeftCutOutput ℓ s r x
          (lrClassEquiv d) default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (boltzmannLaw ℓ s hL0 hLtop)[|{mL | IsML x mL}] ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRRightCutOutput ℓ s r x
          (lrClassEquiv d) default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (boltzmannLaw s r hR0 hRtop)[|{mR | IsMR x mR}] := by
  rcases lrIndNormalizers d hC0 hCtop hpos with
    ⟨_, _, hZA0, hZAtop, hZB0, hZBtop⟩
  exact lem_lr_ind_of_repData d hC0 hCtop hZA0 hZAtop hZB0 hZBtop
    hL0 hLtop hR0 hRtop default

end DirectedDistances.PlanarMap
