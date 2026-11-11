module

public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.RandomWalk.RConditionedWalk

/-! # Code relabelling, rotated unboundedness and first hits of the first coordinate

the step-set rotation `(L, R) ↦ (R, -L-R)` is realised on the iid codes by `c ↦ c + 1`; it
permutes the three linear forms `R`, `-L-R`, `L` of the code walk `(L, R)`.

Obtained from `ae_codeWalk_snd_unbounded_below` (`R` unbounded below) by rotating once and
twice: `-L-R` unbounded below (i.e. `L+R` unbounded above) and `L` unbounded below. Unbounded
above of `L` alone or of `R` alone does *not* follow from the rotation: the three forms
`R`, `-L-R`, `L` are all "below" statements. It follows from the reflection `(L, R) ↦ (-R, -L)`
(code swap `0 ↔ 1`), which exchanges "`L` above" with "`R` below" and "`R` above" with "`L` below". -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- Relabelling `c ↦ c + 1` of the codes, keeping the dummy time-zero code; it realises the
step-set rotation `stepRotate` (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
@[expose] def codeRelabel (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => if i = 0 then 0 else ω i + 1

/-- Measurability of the relabelling (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem measurable_codeRelabel : Measurable codeRelabel := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold codeRelabel
  by_cases h : i = 0
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]; exact (measurable_pi_apply i).add_const 1

private theorem rotate_add' (z w : ℤ × ℤ) :
    stepRotate (z + w) = stepRotate z + stepRotate w := by
  apply Prod.ext <;> dsimp [stepRotate]; omega

/-- The relabelled walk is the rotated walk (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem codeWalk_codeRelabel (ω : ℕ → Fin 3) (n : ℕ) :
    codeWalk (codeRelabel ω) n = stepRotate (codeWalk ω n) := by
  induction n with
  | zero => simp [codeWalk_zero, stepRotate]
  | succ n ih =>
    have h1 := codeWalk_succ_sub (codeRelabel ω) n
    have h2 := codeWalk_succ_sub ω n
    have h3 : codeRelabel ω (n + 1) = ω (n + 1) + 1 := by simp [codeRelabel]
    rw [h3, ← stepRotate_step] at h1
    have e1 : codeWalk (codeRelabel ω) (n + 1) =
        codeWalk (codeRelabel ω) n + stepRotate (lazyTwoDimensionalStep (ω (n + 1))) := by
      rw [← h1]; abel
    have e2 : codeWalk ω (n + 1) = codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by
      rw [← h2]; abel
    rw [e1, e2, ih, rotate_add']

/-- The relabelling preserves the iid code law (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem map_codeRelabel : iidCodeMeasure.map codeRelabel = iidCodeMeasure := by
  classical
  have hZ : ∀ᵐ ω ∂iidCodeMeasure, ω 0 = 0 := by
    filter_upwards [DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) uniformCodeMeasure) (0 : Fin 3)] with ω hω
    exact hω
  have hpre : ∀ n : ℕ,
      (iidCodeMeasure.map codeRelabel).map (fun ω => fun j : Fin (n + 1) => ω j.val) =
        iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) => ω j.val) := by
    intro n
    have hprefm : Measurable (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) :=
      Measurable.of_eval fun j => measurable_pi_apply j.val
    rw [Measure.map_map hprefm measurable_codeRelabel, iidCodeMeasure_map_prefix]
    apply Measure.ext_of_singleton
    intro q
    rw [Measure.map_apply (hprefm.comp measurable_codeRelabel) (measurableSet_singleton _)]
    have hmass : ∀ q' : Fin (n + 1) → Fin 3,
        iidCodeMeasure {ω | (fun j : Fin (n + 1) => ω j.val) = q'} =
          Measure.pi (fun j : Fin (n + 1) =>
            if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure) {q'} := by
      intro q'
      rw [← iidCodeMeasure_map_prefix,
        Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      rfl
    by_cases hq : q 0 = 0
    · let q' : Fin (n + 1) → Fin 3 := fun j => if j.val = 0 then 0 else q j - 1
      have key : ∀ ω : ℕ → Fin 3, ω 0 = 0 →
          ((fun j : Fin (n + 1) => codeRelabel ω j.val) = q ↔
            (fun j : Fin (n + 1) => ω j.val) = q') := by
        intro ω h0
        constructor
        · intro h
          funext j
          have := congrFun h j
          by_cases hj : j.val = 0
          · simp only [q', hj, ite_true]
            exact h0
          · simp only [codeRelabel, hj, ite_false] at this
            simp only [q', hj, ite_false]
            rw [← this]; simp
        · intro h
          funext j
          have := congrFun h j
          by_cases hj : j.val = 0
          · have hj0 : j = 0 := Fin.ext hj
            subst hj0
            simp [codeRelabel, hq]
          · simp only [q', hj, ite_false] at this
            simp only [codeRelabel, hj, ite_false]
            rw [this]; simp
      have hae : ((fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) ∘ codeRelabel) ⁻¹'
          {q} =ᵐ[iidCodeMeasure] {ω | (fun j : Fin (n + 1) => ω j.val) = q'} := by
        filter_upwards [hZ] with ω h0
        exact propext (key ω h0)
      rw [measure_congr hae, hmass q', Measure.pi_singleton, Measure.pi_singleton]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        subst hj0
        simp [q', hq]
      · simp [hj, q', uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton]
    · have hemp : ((fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) ∘ codeRelabel) ⁻¹'
          {q} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun ω h => hq ?_
        have h' : (fun j : Fin (n + 1) => codeRelabel ω j.val) = q := h
        have := congrFun h' 0
        simpa [codeRelabel] using this.symm
      rw [hemp, measure_empty, Measure.pi_singleton]
      refine (Finset.prod_eq_zero (Finset.mem_univ 0) ?_).symm
      simp [hq]
  have hrestrict : ∀ I : Finset ℕ,
      (iidCodeMeasure.map codeRelabel).map I.restrict = iidCodeMeasure.map I.restrict := by
    intro I
    let n := I.sup id
    let g : (Fin (n + 1) → Fin 3) → (I → Fin 3) := fun q i =>
      q ⟨i.1, by
        have := Finset.le_sup (f := id) i.property
        change i.1 ≤ I.sup id at this
        omega⟩
    have hg : Measurable g := measurable_of_countable g
    have hfac : (Finset.restrict (π := fun _ : ℕ => Fin 3) I) =
        g ∘ (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) := rfl
    have hf : Measurable (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) := by
      fun_prop
    rw [hfac, ← Measure.map_map hg hf, ← Measure.map_map hg hf, hpre n]
  exact (show IsProjectiveLimit (iidCodeMeasure.map codeRelabel)
      (fun I => iidCodeMeasure.map I.restrict) from hrestrict).unique
    (show IsProjectiveLimit iidCodeMeasure (fun I => iidCodeMeasure.map I.restrict) from
      fun I => rfl)

/-- Relabelling is measure preserving (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem measurePreserving_codeRelabel :
    MeasurePreserving codeRelabel iidCodeMeasure iidCodeMeasure :=
  ⟨measurable_codeRelabel, map_codeRelabel⟩

/-- The first coordinate `L` of the iid code walk is a.s. unbounded below: `ae_codeWalk_snd_unbounded_below`
rotated twice, `(L, R) ↦ (R, -L-R) ↦ (-L-R, L)` (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem ae_codeWalk_fst_unbounded_below :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ a : ℤ, ∃ n, (codeWalk ω n).1 ≤ a := by
  have h1 := measurePreserving_codeRelabel.quasiMeasurePreserving.ae
    ae_codeWalk_snd_unbounded_below
  have h2 := measurePreserving_codeRelabel.quasiMeasurePreserving.ae h1
  filter_upwards [h2] with ω hω a
  obtain ⟨n, hn⟩ := hω a
  refine ⟨n, ?_⟩
  rw [codeWalk_codeRelabel, codeWalk_codeRelabel] at hn
  dsimp only [stepRotate] at hn
  omega

/-- The sum `L + R` of the coordinates of the iid code walk is a.s. unbounded above: the form
`-L-R` is `ae_codeWalk_snd_unbounded_below` rotated once (`eqn-bdy-vertex-hit`, -/
theorem ae_codeWalk_fst_add_snd_unbounded_above :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ a : ℤ, ∃ n, a ≤ (codeWalk ω n).1 + (codeWalk ω n).2 := by
  have h1 := measurePreserving_codeRelabel.quasiMeasurePreserving.ae
    ae_codeWalk_snd_unbounded_below
  filter_upwards [h1] with ω hω a
  obtain ⟨n, hn⟩ := hω (-a)
  refine ⟨n, ?_⟩
  rw [codeWalk_codeRelabel] at hn
  dsimp only [stepRotate] at hn
  omega

private theorem codeWalk_fst_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).1 - 1 ≤ (codeWalk ω (n + 1)).1 := by
  have h := congrArg Prod.fst (codeWalk_succ_sub ω n)
  rw [Prod.fst_sub] at h
  have : -1 ≤ (lazyTwoDimensionalStep (ω (n + 1))).1 := by
    generalize ω (n + 1) = c
    fin_cases c <;> decide
  omega

private theorem exists_codeWalk_fst_eq_of_le (ω : ℕ → Fin 3) {a : ℤ} (ha : a ≤ 0)
    (h : ∃ n, (codeWalk ω n).1 ≤ a) : ∃ n, (codeWalk ω n).1 = a := by
  classical
  let n0 := Nat.find h
  have h0 : (codeWalk ω n0).1 ≤ a := Nat.find_spec h
  refine ⟨n0, ?_⟩
  by_cases hn : n0 = 0
  · have : (codeWalk ω n0).1 = 0 := by rw [hn, codeWalk_zero]
    omega
  · obtain ⟨m, hm⟩ : ∃ m, n0 = m + 1 := ⟨n0 - 1, by omega⟩
    have h1 : ¬ (codeWalk ω m).1 ≤ a := Nat.find_min h (by omega)
    have h2 := codeWalk_fst_succ_ge ω m
    rw [hm] at h0 ⊢
    omega

/-- Finiteness of the first hit of a level `a ≤ 0` by the first coordinate `L` of the code walk
second-coordinate version is `ae_exists_codeWalk_snd_eq`. -/
theorem ae_exists_codeWalk_fst_eq {a : ℤ} (ha : a ≤ 0) :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ n, (codeWalk ω n).1 = a := by
  filter_upwards [ae_codeWalk_fst_unbounded_below] with ω hω
  exact exists_codeWalk_fst_eq_of_le ω ha (hω a)

/-- First time the first coordinate `L` of the code walk equals `a`, valued in `ℕ∞` (`⊤` if
second-coordinate version is `codeSndFirstHit`. -/
@[expose] noncomputable def codeFstFirstHit (a : ℤ) (ω : ℕ → Fin 3) : ℕ∞ := by
  classical
  exact if h : ∃ n, (codeWalk ω n).1 = a then ((Nat.find h : ℕ) : ℕ∞) else ⊤

/-- The first hit time of a level by `L` is finite almost surely when `a ≤ 0`
second-coordinate version is `ae_codeSndFirstHit_lt_top`. -/
theorem ae_codeFstFirstHit_lt_top {a : ℤ} (ha : a ≤ 0) :
    ∀ᵐ ω ∂iidCodeMeasure, codeFstFirstHit a ω < ⊤ := by
  filter_upwards [ae_exists_codeWalk_fst_eq ha] with ω hω
  classical
  unfold codeFstFirstHit
  rw [dif_pos hω]
  exact ENat.coe_lt_top _

/-- The first hit time of a level by `L` is a stopping time for the past filtration
second-coordinate version is `measurableSet_codePast_codeSndFirstHit_eq`. -/
theorem measurableSet_codePast_codeFstFirstHit_eq (a : ℤ) (k : ℕ) :
    MeasurableSet[codePast k] {ω | codeFstFirstHit a ω = k} := by
  classical
  let wk : (Fin k → Fin 3) → ℕ → ℤ × ℤ := fun x j =>
    ∑ i ∈ Finset.range j, if h : i < k then lazyTwoDimensionalStep (x ⟨i, h⟩) else 0
  have hwk : ∀ (ω : ℕ → Fin 3) (j : ℕ), j ≤ k →
      codeWalk ω j = wk (fun i : Fin k => ω (i.val + 1)) j := by
    intro ω j hj
    unfold codeWalk
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i < k := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
    simp [this]
  let S : Set (Fin k → Fin 3) := {x | (wk x k).1 = a ∧ ∀ j < k, (wk x j).1 ≠ a}
  have hS : MeasurableSet S := (Set.toFinite S).measurableSet
  refine ⟨S, hS, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
  rw [← hwk ω k le_rfl]
  have hall : (∀ j < k, (wk (fun i : Fin k => ω (i.val + 1)) j).1 ≠ a) ↔
      ∀ j < k, (codeWalk ω j).1 ≠ a := by
    refine forall₂_congr fun j hj => ?_
    rw [hwk ω j hj.le]
  rw [hall]
  unfold codeFstFirstHit
  by_cases h : ∃ n, (codeWalk ω n).1 = a
  · rw [dif_pos h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dif_neg h]
    constructor
    · rintro ⟨hk, -⟩; exact absurd ⟨k, hk⟩ h
    · intro h'; exact absurd h' (ENat.top_ne_natCast k)

/-- Code swap `0 ↔ 1`, fixing `2`; it realises the reflection `(L, R) ↦ (-R, -L)` of the step set -/
@[expose] def codeSwap (c : Fin 3) : Fin 3 := if c = 0 then 1 else if c = 1 then 0 else 2

/-- The code swap is an involution (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem codeSwap_codeSwap (c : Fin 3) : codeSwap (codeSwap c) = c := by
  fin_cases c <;> decide

/-- The code swap realises the reflection of the step set (`eqn-bdy-vertex-hit`, -/
theorem lazyTwoDimensionalStep_codeSwap (c : Fin 3) :
    lazyTwoDimensionalStep (codeSwap c) =
      (-(lazyTwoDimensionalStep c).2, -(lazyTwoDimensionalStep c).1) := by
  fin_cases c <;> decide

/-- Reflection of the codes by the swap `0 ↔ 1`, keeping the dummy time-zero code -/
@[expose] def codeReflect (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => if i = 0 then 0 else codeSwap (ω i)

/-- Measurability of the reflection (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem measurable_codeReflect : Measurable codeReflect := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold codeReflect
  by_cases h : i = 0
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]
    exact (measurable_of_countable codeSwap).comp (measurable_pi_apply i)

/-- The reflected walk is the reflected walk (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem codeWalk_codeReflect (ω : ℕ → Fin 3) (n : ℕ) :
    codeWalk (codeReflect ω) n = (-(codeWalk ω n).2, -(codeWalk ω n).1) := by
  induction n with
  | zero => simp [codeWalk_zero]
  | succ n ih =>
    have h1 := codeWalk_succ_sub (codeReflect ω) n
    have h2 := codeWalk_succ_sub ω n
    have h3 : codeReflect ω (n + 1) = codeSwap (ω (n + 1)) := by simp [codeReflect]
    rw [h3, lazyTwoDimensionalStep_codeSwap] at h1
    have e1 : codeWalk (codeReflect ω) (n + 1) = codeWalk (codeReflect ω) n +
        (-(lazyTwoDimensionalStep (ω (n + 1))).2, -(lazyTwoDimensionalStep (ω (n + 1))).1) := by
      rw [← h1]; abel
    have e2 : codeWalk ω (n + 1) = codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by
      rw [← h2]; abel
    rw [e1, e2, ih]
    apply Prod.ext <;> simp <;> omega

/-- The reflection preserves the iid code law (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem map_codeReflect : iidCodeMeasure.map codeReflect = iidCodeMeasure := by
  classical
  have hZ : ∀ᵐ ω ∂iidCodeMeasure, ω 0 = 0 := by
    filter_upwards [DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) uniformCodeMeasure) (0 : Fin 3)] with ω hω
    exact hω
  have hpre : ∀ n : ℕ,
      (iidCodeMeasure.map codeReflect).map (fun ω => fun j : Fin (n + 1) => ω j.val) =
        iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) => ω j.val) := by
    intro n
    have hprefm : Measurable (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) :=
      Measurable.of_eval fun j => measurable_pi_apply j.val
    rw [Measure.map_map hprefm measurable_codeReflect, iidCodeMeasure_map_prefix]
    apply Measure.ext_of_singleton
    intro q
    rw [Measure.map_apply (hprefm.comp measurable_codeReflect) (measurableSet_singleton _)]
    have hmass : ∀ q' : Fin (n + 1) → Fin 3,
        iidCodeMeasure {ω | (fun j : Fin (n + 1) => ω j.val) = q'} =
          Measure.pi (fun j : Fin (n + 1) =>
            if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure) {q'} := by
      intro q'
      rw [← iidCodeMeasure_map_prefix,
        Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      rfl
    by_cases hq : q 0 = 0
    · let q' : Fin (n + 1) → Fin 3 := fun j => if j.val = 0 then 0 else codeSwap (q j)
      have key : ∀ ω : ℕ → Fin 3, ω 0 = 0 →
          ((fun j : Fin (n + 1) => codeReflect ω j.val) = q ↔
            (fun j : Fin (n + 1) => ω j.val) = q') := by
        intro ω h0
        constructor
        · intro h
          funext j
          have := congrFun h j
          by_cases hj : j.val = 0
          · simp only [q', hj, ite_true]
            exact h0
          · simp only [codeReflect, hj, ite_false] at this
            simp only [q', hj, ite_false]
            rw [← this, codeSwap_codeSwap]
        · intro h
          funext j
          have := congrFun h j
          by_cases hj : j.val = 0
          · have hj0 : j = 0 := Fin.ext hj
            subst hj0
            simp [codeReflect, hq]
          · simp only [q', hj, ite_false] at this
            simp only [codeReflect, hj, ite_false]
            rw [this, codeSwap_codeSwap]
      have hae : ((fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) ∘ codeReflect) ⁻¹'
          {q} =ᵐ[iidCodeMeasure] {ω | (fun j : Fin (n + 1) => ω j.val) = q'} := by
        filter_upwards [hZ] with ω h0
        exact propext (key ω h0)
      rw [measure_congr hae, hmass q', Measure.pi_singleton, Measure.pi_singleton]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        subst hj0
        simp [q', hq]
      · simp [hj, q', uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton]
    · have hemp : ((fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) ∘ codeReflect) ⁻¹'
          {q} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun ω h => hq ?_
        have h' : (fun j : Fin (n + 1) => codeReflect ω j.val) = q := h
        have := congrFun h' 0
        simpa [codeReflect] using this.symm
      rw [hemp, measure_empty, Measure.pi_singleton]
      refine (Finset.prod_eq_zero (Finset.mem_univ 0) ?_).symm
      simp [hq]
  have hrestrict : ∀ I : Finset ℕ,
      (iidCodeMeasure.map codeReflect).map I.restrict = iidCodeMeasure.map I.restrict := by
    intro I
    let n := I.sup id
    let g : (Fin (n + 1) → Fin 3) → (I → Fin 3) := fun q i =>
      q ⟨i.1, by
        have := Finset.le_sup (f := id) i.property
        change i.1 ≤ I.sup id at this
        omega⟩
    have hg : Measurable g := measurable_of_countable g
    have hfac : (Finset.restrict (π := fun _ : ℕ => Fin 3) I) =
        g ∘ (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) := rfl
    have hf : Measurable (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) := by
      fun_prop
    rw [hfac, ← Measure.map_map hg hf, ← Measure.map_map hg hf, hpre n]
  exact (show IsProjectiveLimit (iidCodeMeasure.map codeReflect)
      (fun I => iidCodeMeasure.map I.restrict) from hrestrict).unique
    (show IsProjectiveLimit iidCodeMeasure (fun I => iidCodeMeasure.map I.restrict) from
      fun I => rfl)

/-- The reflection is measure preserving (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem measurePreserving_codeReflect :
    MeasurePreserving codeReflect iidCodeMeasure iidCodeMeasure :=
  ⟨measurable_codeReflect, map_codeReflect⟩

/-- The first coordinate `L` of the iid code walk is a.s. unbounded above: the reflected walk has
`R = -L`, which is unbounded below (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem ae_codeWalk_fst_unbounded_above :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ a : ℤ, ∃ n, a ≤ (codeWalk ω n).1 := by
  have h1 := measurePreserving_codeReflect.quasiMeasurePreserving.ae
    ae_codeWalk_snd_unbounded_below
  filter_upwards [h1] with ω hω a
  obtain ⟨n, hn⟩ := hω (-a)
  refine ⟨n, ?_⟩
  rw [codeWalk_codeReflect] at hn
  dsimp only at hn
  omega

/-- The second coordinate `R` of the iid code walk is a.s. unbounded above: the reflected walk has
`L = -R`, which is unbounded below (`eqn-bdy-vertex-hit`, `eqn-flow-line-times`, -/
theorem ae_codeWalk_snd_unbounded_above :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ a : ℤ, ∃ n, a ≤ (codeWalk ω n).2 := by
  have h1 := measurePreserving_codeReflect.quasiMeasurePreserving.ae
    ae_codeWalk_fst_unbounded_below
  filter_upwards [h1] with ω hω a
  obtain ⟨n, hn⟩ := hω (-a)
  refine ⟨n, ?_⟩
  rw [codeWalk_codeReflect] at hn
  dsimp only at hn
  omega

private theorem codeWalk_fst_succ_le (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω (n + 1)).1 ≤ (codeWalk ω n).1 + 1 := by
  have h := congrArg Prod.fst (codeWalk_succ_sub ω n)
  rw [Prod.fst_sub] at h
  have : (lazyTwoDimensionalStep (ω (n + 1))).1 ≤ 1 := by
    generalize ω (n + 1) = c
    fin_cases c <;> decide
  omega

private theorem codeWalk_snd_succ_le (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω (n + 1)).2 ≤ (codeWalk ω n).2 + 1 := by
  have h := congrArg Prod.snd (codeWalk_succ_sub ω n)
  rw [Prod.snd_sub] at h
  have : (lazyTwoDimensionalStep (ω (n + 1))).2 ≤ 1 := by
    generalize ω (n + 1) = c
    fin_cases c <;> decide
  omega

private theorem exists_codeWalk_fst_eq_of_ge (ω : ℕ → Fin 3) {a : ℤ} (ha : 0 ≤ a)
    (h : ∃ n, a ≤ (codeWalk ω n).1) : ∃ n, (codeWalk ω n).1 = a := by
  classical
  let n0 := Nat.find h
  have h0 : a ≤ (codeWalk ω n0).1 := Nat.find_spec h
  refine ⟨n0, ?_⟩
  by_cases hn : n0 = 0
  · have : (codeWalk ω n0).1 = 0 := by rw [hn, codeWalk_zero]
    omega
  · obtain ⟨m, hm⟩ : ∃ m, n0 = m + 1 := ⟨n0 - 1, by omega⟩
    have h1 : ¬ a ≤ (codeWalk ω m).1 := Nat.find_min h (by omega)
    have h2 := codeWalk_fst_succ_le ω m
    rw [hm] at h0 ⊢
    omega

private theorem exists_codeWalk_snd_eq_of_ge (ω : ℕ → Fin 3) {a : ℤ} (ha : 0 ≤ a)
    (h : ∃ n, a ≤ (codeWalk ω n).2) : ∃ n, (codeWalk ω n).2 = a := by
  classical
  let n0 := Nat.find h
  have h0 : a ≤ (codeWalk ω n0).2 := Nat.find_spec h
  refine ⟨n0, ?_⟩
  by_cases hn : n0 = 0
  · have : (codeWalk ω n0).2 = 0 := by rw [hn, codeWalk_zero]
    omega
  · obtain ⟨m, hm⟩ : ∃ m, n0 = m + 1 := ⟨n0 - 1, by omega⟩
    have h1 : ¬ a ≤ (codeWalk ω m).2 := Nat.find_min h (by omega)
    have h2 := codeWalk_snd_succ_le ω m
    rw [hm] at h0 ⊢
    omega

/-- Every integer level is a.s. hit by the first coordinate `L` of the code walk -/
theorem ae_exists_codeWalk_fst_eq_int (a : ℤ) :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ n, (codeWalk ω n).1 = a := by
  by_cases ha : a ≤ 0
  · exact ae_exists_codeWalk_fst_eq ha
  · filter_upwards [ae_codeWalk_fst_unbounded_above] with ω hω
    exact exists_codeWalk_fst_eq_of_ge ω (by omega) (hω a)

/-- Every integer level is a.s. hit by the second coordinate `R` of the code walk -/
theorem ae_exists_codeWalk_snd_eq_int (a : ℤ) :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ n, (codeWalk ω n).2 = a := by
  by_cases ha : a ≤ 0
  · exact ae_exists_codeWalk_snd_eq ha
  · filter_upwards [ae_codeWalk_snd_unbounded_above] with ω hω
    exact exists_codeWalk_snd_eq_of_ge ω (by omega) (hω a)

/-- The first hit time of any integer level by `L` is finite almost surely -/
theorem ae_codeFstFirstHit_lt_top_int (a : ℤ) :
    ∀ᵐ ω ∂iidCodeMeasure, codeFstFirstHit a ω < ⊤ := by
  filter_upwards [ae_exists_codeWalk_fst_eq_int a] with ω hω
  classical
  unfold codeFstFirstHit
  rw [dif_pos hω]
  exact ENat.coe_lt_top _

/-- The first hit time of any integer level by `R` is finite almost surely -/
theorem ae_codeSndFirstHit_lt_top_int (a : ℤ) :
    ∀ᵐ ω ∂iidCodeMeasure, codeSndFirstHit a ω < ⊤ := by
  filter_upwards [ae_exists_codeWalk_snd_eq_int a] with ω hω
  classical
  unfold codeSndFirstHit
  rw [dif_pos hω]
  exact ENat.coe_lt_top _

end DirectedDistances.RandomWalk
