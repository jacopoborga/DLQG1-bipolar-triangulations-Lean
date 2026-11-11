/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.DiskWalkConv
public import DirectedDistances.KMSW.KMSWLeftWalkCut

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/

/-! # Uniform finite code and independent mark

Helper toward Proposition 5.16 (`prop-disk-bs-conv`,
the unconditioned finite code prefix and independent mark are uniform; not
the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open scoped ENNReal

private def diskCodePrefix (n : ℕ) (ω : ℕ → Fin 3) : Fin n → Fin 3 :=
  fun i => ω (i.val + 1)

private def shiftedFiniteCode (n : ℕ) (c : Fin n → Fin 3) : ℕ → Fin 3 :=
  fun j => if j = 0 then 0 else finiteCodeExtend (n := n + 1) c (j - 1)

private theorem measurable_diskCodePrefix (n : ℕ) : Measurable (diskCodePrefix n) := by
  exact Measurable.of_eval fun i => measurable_pi_apply (i.val + 1)

private theorem kmswLeftWalkAdmissible_iff_coneEvent_shiftedCode
    (ell n : ℕ) (c : Fin n → Fin 3) :
    KMSWLeftWalkAdmissible (ell + 1) n c ↔
      shiftedFiniteCode n c ∈ coneEvent (ell : ℤ) 0 n := by
  let w := finiteCodeExtend (n := n + 1) c
  let ω : ℕ → Fin 3 := fun j => if j = 0 then 0 else w (j - 1)
  have hshift : (fun i : ℕ => ω (i + 1)) = w := by
    funext i
    simp [ω]
  have hwalk (j : ℕ) : codeWalk ω j = integrateCodes w j := by
    rw [codeWalk_eq_integrateCodes, hshift]
  have hstart : ((ell + 1 : ℕ) : ℤ) - 1 = (ell : ℤ) := by
    omega
  change KMSWLeftWalkAdmissible (ell + 1) n c ↔ ω ∈ coneEvent (ell : ℤ) 0 n
  constructor
  · intro h
    unfold KMSWLeftWalkAdmissible at h
    rw [hstart] at h
    change (∀ j ≤ n,
        0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk ω j).1 ∧
          0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk ω j).2) ∧
      ((ell : ℤ), (0 : ℤ)) + codeWalk ω n = (0, 0)
    constructor
    · intro j hj
      have hj' : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hb := h.2 j hj'
      rw [hwalk j]
      exact hb
    · rw [hwalk n]
      exact h.1
  · intro h
    change (∀ j ≤ n,
        0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk ω j).1 ∧
          0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk ω j).2) ∧
      ((ell : ℤ), (0 : ℤ)) + codeWalk ω n = (0, 0) at h
    unfold KMSWLeftWalkAdmissible
    rw [hstart]
    constructor
    · have hend := h.2
      rw [hwalk n] at hend
      exact hend
    · intro k hk
      have hk' : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      have hb := h.1 k hk'
      rw [hwalk k] at hb
      exact hb

private theorem codeWalk_eq_shiftedFiniteCode (n : ℕ) (ω : ℕ → Fin 3)
    (j : ℕ) (hj : j ≤ n) :
    codeWalk ω j = codeWalk (shiftedFiniteCode n (diskCodePrefix n ω)) j := by
  rw [codeWalk_eq_integrateCodes, codeWalk_eq_integrateCodes]
  unfold integrateCodes
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := by
    have := Finset.mem_range.mp hi
    omega
  have hcode : ω (i + 1) = shiftedFiniteCode n (diskCodePrefix n ω) (i + 1) := by
    simp [shiftedFiniteCode, diskCodePrefix, finiteCodeExtend, hin]
  exact congrArg lazyTwoDimensionalStep hcode

private theorem diskCodePrefix_coneEvent_iff (ell n : ℕ) (ω : ℕ → Fin 3) :
    ω ∈ coneEvent (ell : ℤ) 0 n ↔
      KMSWLeftWalkAdmissible (ell + 1) n (diskCodePrefix n ω) := by
  have hevent :
      ω ∈ coneEvent (ell : ℤ) 0 n ↔
        shiftedFiniteCode n (diskCodePrefix n ω) ∈ coneEvent (ell : ℤ) 0 n := by
    change ((∀ j ≤ n,
        0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk ω j).1 ∧
          0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk ω j).2) ∧
      ((ell : ℤ), (0 : ℤ)) + codeWalk ω n = (0, 0)) ↔ _
    constructor
    · rintro ⟨hpath, hend⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [← codeWalk_eq_shiftedFiniteCode n ω j hj]
        exact hpath j hj
      · rw [← codeWalk_eq_shiftedFiniteCode n ω n le_rfl]
        exact hend
    · rintro ⟨hpath, hend⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [codeWalk_eq_shiftedFiniteCode n ω j hj]
        exact hpath j hj
      · rw [codeWalk_eq_shiftedFiniteCode n ω n le_rfl]
        exact hend
  constructor
  · intro h
    exact (kmswLeftWalkAdmissible_iff_coneEvent_shiftedCode ell n
      (diskCodePrefix n ω)).2 (hevent.mp h)
  · intro h
    have hs := (kmswLeftWalkAdmissible_iff_coneEvent_shiftedCode ell n
      (diskCodePrefix n ω)).mp h
    exact hevent.mpr hs

private theorem measurableSet_bridgeCone (ell n : ℕ) :
    MeasurableSet (coneEvent (ell : ℤ) 0 n) := by
  simp only [coneEvent, Set.ofPred_and]
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    have hj := (measurable_pi_apply j).comp measurable_codeWalk
    simp only [Set.ofPred_and]
    exact (measurableSet_le measurable_const (measurable_const.add hj.fst)).inter
      (measurableSet_le measurable_const (measurable_const.add hj.snd))
  · exact (measurable_const.add ((measurable_pi_apply n).comp measurable_codeWalk))
      (measurableSet_singleton (0, 0))

private theorem iidCodeMeasure_map_diskCodePrefix (n : ℕ) :
    iidCodeMeasure.map (diskCodePrefix n) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3)) := by
  classical
  have hf : diskCodePrefix n =
      (fun q : Fin (n + 1) → Fin 3 => fun i : Fin n => q i.succ) ∘
        (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) := by
    funext ω i
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), iidCodeMeasure_map_prefix]
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (n + 1) =>
      if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure) 0
  have hsnd :
      (fun q : Fin (n + 1) → Fin 3 => fun i : Fin n => q i.succ) =
        Prod.snd ∘ MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Fin 3) 0 := by
    funext q i
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [hsnd, ← Measure.map_map measurable_snd
    (MeasurableEquiv.measurable _), hmp.map_eq, Measure.map_snd_prod]
  simp only [Fin.val_zero, ite_true, measure_univ, one_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Fin.succAbove_zero]
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton, ENNReal.inv_pow]

private theorem iidCodeMeasure_coneEvent_eq_class_count (ell n : ℕ) :
    iidCodeMeasure (coneEvent (ell : ℤ) 0 n) =
      (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
        ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  classical
  let A : Set (Fin n → Fin 3) :=
    {c | KMSWLeftWalkAdmissible (ell + 1) n c}
  have hpre : coneEvent (ell : ℤ) 0 n = diskCodePrefix n ⁻¹' A := by
    ext ω
    simp only [Set.mem_preimage, A, Set.mem_ofPred_eq]
    exact diskCodePrefix_coneEvent_iff ell n ω
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  rw [hpre, ← Measure.map_apply (measurable_diskCodePrefix n) hA,
    iidCodeMeasure_map_diskCodePrefix, Measure.uniformOfFinset_apply]
  calc
    _ = (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) /
        (Finset.card (Finset.univ : Finset (Fin n → Fin 3)) : ℝ≥0∞) := by
      congr 1
      congr 1
      symm
      apply Fintype.card_of_subtype
      intro c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    _ = _ := by
      simp [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]

private theorem integrateCodes_succ_diskMark (c : ℕ → Fin 3) (j : ℕ) :
    integrateCodes c (j + 1) = integrateCodes c j + lazyTwoDimensionalStep (c j) :=
  Finset.sum_range_succ _ _




theorem kmswLeftWalkClass_nonempty_of_domain (ell n : ℕ) (hell : 1 ≤ ell)
    (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    Nonempty (KMSWLeftWalkClass (ell + 1) n) := by
  classical
  obtain ⟨q, hq⟩ := hmod
  have hqnonneg : 0 ≤ q := by omega
  let a := q.toNat
  have hnrepr : n = ell + 3 * a := by
    have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hqnonneg
    omega
  let code (j : ℕ) : Fin 3 :=
    if j < 3 * a then
      if j % 3 = 0 then 1 else if j % 3 = 1 then 2 else 0
    else 0
  let c : Fin n → Fin 3 := fun i => code i.val
  have hcode0 (t : ℕ) (ht : t < a) : code (3 * t) = 1 := by
    have hlt : 3 * t < 3 * a := by omega
    have hmod3 : (3 * t) % 3 = 0 := by omega
    simp [code, hlt, hmod3]
  have hcode1 (t : ℕ) (ht : t < a) : code (3 * t + 1) = 2 := by
    have hlt : 3 * t + 1 < 3 * a := by omega
    have hmod3 : (3 * t + 1) % 3 = 1 := by omega
    simp [code, hlt, hmod3]
  have hcode2 (t : ℕ) (ht : t < a) : code (3 * t + 2) = 0 := by
    have hlt : 3 * t + 2 < 3 * a := by omega
    have hmod3 : (3 * t + 2) % 3 = 2 := by omega
    simp [code, hlt, hmod3]
  have hcycle : ∀ t ≤ a, integrateCodes code (3 * t) = (0, 0) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        have htlt : t < a := by omega
        have hprev := ih (by omega)
        calc
          integrateCodes code (3 * (t + 1)) =
              integrateCodes code (3 * t) +
                lazyTwoDimensionalStep (code (3 * t)) +
                lazyTwoDimensionalStep (code (3 * t + 1)) +
                lazyTwoDimensionalStep (code (3 * t + 2)) := by
            rw [show 3 * (t + 1) = ((3 * t + 1) + 1) + 1 by omega,
              integrateCodes_succ_diskMark, integrateCodes_succ_diskMark,
              integrateCodes_succ_diskMark]
          _ = (0, 0) := by
            rw [hprev, hcode0 t htlt, hcode1 t htlt, hcode2 t htlt]
            simp
  have hprefix1 : ∀ t < a, integrateCodes code (3 * t + 1) = (0, 1) := by
    intro t ht
    rw [show 3 * t + 1 = (3 * t) + 1 by omega,
      integrateCodes_succ_diskMark, hcycle t (by omega), hcode0 t ht]
    simp
  have hprefix2 : ∀ t < a, integrateCodes code (3 * t + 2) = (1, 0) := by
    intro t ht
    rw [show 3 * t + 2 = (3 * t + 1) + 1 by omega,
      integrateCodes_succ_diskMark, hprefix1 t ht, hcode1 t ht]
    simp
  have hpostCode (s : ℕ) : code (3 * a + s) = 0 := by
    have hnot : ¬ 3 * a + s < 3 * a := by omega
    simp [code, hnot]
  have hpost : ∀ s ≤ ell, integrateCodes code (3 * a + s) = (-(s : ℤ), 0) := by
    intro s hs
    induction s with
    | zero => simpa using hcycle a le_rfl
    | succ s ih =>
        rw [show 3 * a + (s + 1) = (3 * a + s) + 1 by omega,
          integrateCodes_succ_diskMark, ih (by omega), hpostCode s]
        simp
        omega
  have hcone (j : ℕ) (hj : j ≤ n) :
      0 ≤ (((ell : ℤ), (0 : ℤ)) + integrateCodes code j).1 ∧
        0 ≤ (((ell : ℤ), (0 : ℤ)) + integrateCodes code j).2 := by
    by_cases hjpre : j ≤ 3 * a
    · let t := j / 3
      have hjdecomp : j = 3 * t + j % 3 := by
        dsimp [t]
        omega
      have ht : t ≤ a := by
        dsimp [t]
        omega
      have hrange : j % 3 < 3 := Nat.mod_lt _ (by omega)
      by_cases hr0 : j % 3 = 0
      · have hj' : j = 3 * t := by omega
        rw [hj', hcycle t ht]
        simp only [Prod.fst_add, Prod.snd_add]
        constructor <;> omega
      · by_cases hr1 : j % 3 = 1
        · have htlt : t < a := by omega
          have hj' : j = 3 * t + 1 := by omega
          rw [hj', hprefix1 t htlt]
          simp only [Prod.fst_add, Prod.snd_add]
          constructor <;> omega
        · have htlt : t < a := by omega
          have hr2 : j % 3 = 2 := by omega
          have hj' : j = 3 * t + 2 := by omega
          rw [hj', hprefix2 t htlt]
          simp only [Prod.fst_add, Prod.snd_add]
          constructor <;> omega
    · let s := j - 3 * a
      have hj' : j = 3 * a + s := by
        dsimp [s]
        omega
      have hs : s ≤ ell := by
        rw [hnrepr] at hj
        dsimp [s]
        omega
      rw [hj', hpost s hs]
      simp only [Prod.fst_add, Prod.snd_add]
      constructor <;> omega
  have hext : finiteCodeExtend (n := n + 1) c = code := by
    funext j
    simp only [finiteCodeExtend, Nat.add_sub_cancel]
    by_cases hj : j < n
    · simp [hj, c]
    · have hnot : ¬ j < 3 * a := by omega
      simp [hj, code, hnot]
  refine ⟨c, ?_⟩
  rw [KMSWLeftWalkAdmissible, hext]
  have hstart : ((ell + 1 : ℕ) : ℤ) - 1 = (ell : ℤ) := by omega
  rw [hstart]
  constructor
  · have hend := hpost ell le_rfl
    rw [show n = 3 * a + ell by omega, hend]
    simp
  · intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    exact hcone k hk'





theorem iidCodeMeasure_coneEvent_pos_of_domain (ell n : ℕ) (hell : 1 ≤ ell)
    (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    0 < iidCodeMeasure (coneEvent (ell : ℤ) 0 n) := by
  have hcard : 0 < Fintype.card (KMSWLeftWalkClass (ell + 1) n) :=
    Fintype.card_pos_iff.mpr
      (kmswLeftWalkClass_nonempty_of_domain ell n hell hle hmod)
  have hcardCast :
      0 < (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) := by
    exact_mod_cast hcard
  have hpow : 0 < ((3 : ℝ≥0∞) ^ n)⁻¹ :=
    bot_lt_iff_ne_bot.mpr (ENNReal.inv_ne_zero.mpr (by finiteness))
  rw [iidCodeMeasure_coneEvent_eq_class_count]
  exact ENNReal.mul_pos hcardCast.ne' hpow.ne'

/-- Under the unconditioned iid code law and an independent uniform mark, every
finite code word and one-based mark have their product uniform mass. This is a
helper toward Proposition 5.16, not the paper result. -/
theorem iidCodeUniformMark_prefix_fiber (ell n : ℕ)
    (c : Fin n → Fin 3) (k : Fin ell) :
    (iidCodeMeasure.prod (Measure.uniformOfFinset (Finset.Icc 1 ell)))
      {p | (∀ i : Fin n, p.1 (i.val + 1) = c i) ∧ p.2 = k.val + 1} =
        ((3 : ℝ≥0∞) ^ n)⁻¹ * (ell : ℝ≥0∞)⁻¹ := by
  classical
  have hfiber :
      {p : (ℕ → Fin 3) × ℕ |
        (∀ i : Fin n, p.1 (i.val + 1) = c i) ∧ p.2 = k.val + 1} =
        {ω | diskCodePrefix n ω = c} ×ˢ {k.val + 1} := by
    ext p
    change ((∀ i : Fin n, p.1 (i.val + 1) = c i) ∧ p.2 = k.val + 1) ↔
      (diskCodePrefix n p.1 = c ∧ p.2 = k.val + 1)
    constructor
    · rintro ⟨hp, hk⟩
      refine ⟨?_, hk⟩
      funext i
      exact hp i
    · rintro ⟨hp, hk⟩
      exact ⟨fun i => congrFun hp i, hk⟩
  have hcode : iidCodeMeasure {ω | diskCodePrefix n ω = c} =
      ((3 : ℝ≥0∞) ^ n)⁻¹ := by
    change iidCodeMeasure (diskCodePrefix n ⁻¹' {c}) = _
    rw [← Measure.map_apply (measurable_diskCodePrefix n) (measurableSet_singleton c),
      iidCodeMeasure_map_diskCodePrefix, Measure.uniformOfFinset_apply_singleton]
    simp [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have hk : k.val + 1 ∈ Finset.Icc 1 ell := by
    simp only [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  rw [hfiber, Measure.prod_prod, hcode,
    Measure.uniformOfFinset_apply_singleton_of_mem hk]
  simp

/-- Helper toward Proposition 5.16 (`prop-disk-bs-conv`,
conditioned code and independent uniform mark; not the paper result. -/
theorem bridgeLevelLaw_code_mark_fiber
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    ∀ c : KMSWLeftWalkClass (ell + 1) n, ∀ k : Fin ell,
      bridgeLevelLaw n ell
        {p | (∀ i : Fin n, p.1 (i.val + 1) = c.val i) ∧ p.2 = k.val + 1} =
          (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞)⁻¹ *
            (ell : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨q, hq⟩ := hmod
  have hellpos : 0 < ell := by omega
  have hleInt : (ell : ℤ) ≤ n := by exact_mod_cast hle
  have hqnonneg : 0 ≤ q := by omega
  have hnrepr : n = ell + 3 * q.toNat := by
    have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hqnonneg
    omega
  have hnpos : 0 < n := by
    rw [hnrepr]
    exact lt_of_lt_of_le hellpos (Nat.le_add_right _ _)
  have hpow0 : ((3 : ℝ≥0∞) ^ n)⁻¹ ≠ 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
    rw [ENNReal.inv_ne_zero, pow_succ]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      ENNReal.ofNat_ne_top
  have hpowtop : ((3 : ℝ≥0∞) ^ n)⁻¹ ≠ ∞ := by simp
  intro c k
  let E := coneEvent (ell : ℤ) 0 n
  let C := {ω | diskCodePrefix n ω = c.val}
  have hE : MeasurableSet E := measurableSet_bridgeCone ell n
  have hsub : C ⊆ E := by
    intro ω hω
    apply (diskCodePrefix_coneEvent_iff ell n ω).mpr
    rw [hω]
    exact c.property
  have hcode : iidCodeMeasure C = ((3 : ℝ≥0∞) ^ n)⁻¹ := by
    change iidCodeMeasure (diskCodePrefix n ⁻¹' {c.val}) = _
    rw [← Measure.map_apply (measurable_diskCodePrefix n) (measurableSet_singleton c.val),
      iidCodeMeasure_map_diskCodePrefix, Measure.uniformOfFinset_apply_singleton]
    simp [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have hdenom : iidCodeMeasure E =
      (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
        ((3 : ℝ≥0∞) ^ n)⁻¹ := iidCodeMeasure_coneEvent_eq_class_count ell n
  have hEpos : iidCodeMeasure E ≠ 0 :=
    (iidCodeMeasure_coneEvent_pos_of_domain ell n hell hle ⟨q, hq⟩).ne'
  have hcard0 :
      (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) ≠ 0 := by
    intro hzero
    apply hEpos
    rw [hdenom, hzero]
    simp
  have hfiber :
      {p : (ℕ → Fin 3) × ℕ |
        (∀ i : Fin n, p.1 (i.val + 1) = c.val i) ∧ p.2 = k.val + 1} =
        C ×ˢ {k.val + 1} := by
    ext p
    change ((∀ i : Fin n, p.1 (i.val + 1) = c.val i) ∧ p.2 = k.val + 1) ↔
      (diskCodePrefix n p.1 = c.val ∧ p.2 = k.val + 1)
    constructor
    · rintro ⟨hp, hk⟩
      refine ⟨?_, hk⟩
      funext i
      exact hp i
    · rintro ⟨hp, hk⟩
      exact ⟨fun i => congrFun hp i, hk⟩
  have hcond : (cond iidCodeMeasure E) C = (iidCodeMeasure E)⁻¹ * iidCodeMeasure C := by
    rw [ProbabilityTheory.cond_apply hE iidCodeMeasure, Set.inter_eq_right.mpr hsub]
  have hk : k.val + 1 ∈ Finset.Icc 1 ell := by
    simp only [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  have hcardtop :
      (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) ≠ ∞ := by simp
  have hcancel :
      ((Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
        ((3 : ℝ≥0∞) ^ n)⁻¹)⁻¹ * ((3 : ℝ≥0∞) ^ n)⁻¹ =
          (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞)⁻¹ := by
    have hprod0 :
        (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
            ((3 : ℝ≥0∞) ^ n)⁻¹ ≠ 0 := mul_ne_zero hcard0 hpow0
    have hprodtop :
        (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
            ((3 : ℝ≥0∞) ^ n)⁻¹ ≠ ∞ := ENNReal.mul_ne_top hcardtop hpowtop
    calc
      ((Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
          ((3 : ℝ≥0∞) ^ n)⁻¹)⁻¹ * ((3 : ℝ≥0∞) ^ n)⁻¹ =
          ((Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
            ((3 : ℝ≥0∞) ^ n)⁻¹)⁻¹ * ((3 : ℝ≥0∞) ^ n)⁻¹ *
              ((Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
                (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hcard0 hcardtop]
        simp
      _ = ((Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
          ((3 : ℝ≥0∞) ^ n)⁻¹)⁻¹ *
          ((Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞) *
            ((3 : ℝ≥0∞) ^ n)⁻¹) *
          (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞)⁻¹ := by ac_rfl
      _ = (Fintype.card (KMSWLeftWalkClass (ell + 1) n) : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.inv_mul_cancel hprod0 hprodtop, one_mul]
  rw [bridgeLevelLaw, hfiber, Measure.prod_prod, hcond, hcode,
    Measure.uniformOfFinset_apply_singleton_of_mem hk, hdenom]
  rw [hcancel]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]

end DirectedDistances.PaperProofs.Section5
