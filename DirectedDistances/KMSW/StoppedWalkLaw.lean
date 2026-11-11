/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StoppedStageMap
public import DirectedDistances.KMSW.FiniteWalkClass
import DirectedDistances.RandomWalk.QuadrantSplit

/-! # Stopped walk words for the KMSW Boltzmann lemma

This file proves walk-level helper statements for the conditional law in
The implemented code step set is `{(-1, 0), (0, 1), (1, -1)}`; legal-step convention and the
Theorem 3.5 bijection, so this file does not complete Lemma 3.11. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators


/-- The cylinder fixing the `n - 1` walk codes and the final down code. -/
@[expose] def stoppedCylinder {ell r n : ℕ}
    (c : KMSWWalkClass ell r n) : Set (ℕ → Fin 3) :=
  {ω | (∀ i : Fin (n - 1), ω (i.val + 1) = c.val i) ∧ ω n = 2}

/-- A prescribed stopped code cylinder has mass `3^(-n)` under the iid
source stream. The `n - 1` walk codes and the final code at time `n` together
fix exactly `n` random coordinates. Source: Lemma 3.11, -/
theorem iidCodeMeasure_stoppedCylinder_mass {ell r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ell r n) :
    iidCodeMeasure (stoppedCylinder c) = (1 / 3 : ENNReal) ^ n := by
  classical
  let q : Fin n → Fin 3 := fun j =>
    if hj : j.val < n - 1 then c.val ⟨j.val, hj⟩ else 2
  have hset : {ω | quadrantCodeTailPrefix n ω = q} = stoppedCylinder c := by
    ext ω
    constructor
    · intro h
      constructor
      · intro i
        let j : Fin n := ⟨i.val, by have := i.isLt; omega⟩
        have hj := congrFun h j
        have hv : q j = c.val i := by
          simp [q, j, i.isLt]
        simpa [quadrantCodeTailPrefix, j, hv] using hj
      · let j : Fin n := ⟨n - 1, by omega⟩
        have hj := congrFun h j
        have hq : q j = 2 := by simp [q, j]
        have hidx : j.val + 1 = n := by simp [j]; omega
        change ω (j.val + 1) = q j at hj
        rw [hidx, hq] at hj
        exact hj
    · rintro ⟨hprefix, hlast⟩
      funext j
      by_cases hj : j.val < n - 1
      · have hp := hprefix ⟨j.val, hj⟩
        simpa [quadrantCodeTailPrefix, q, hj] using hp
      · have hval : j.val = n - 1 := by have := j.isLt; omega
        change ω (j.val + 1) = q j
        rw [hval]
        have hidx : n - 1 + 1 = n := by omega
        have hq' : q j = 2 := by simp [q, hval]
        rw [hidx, hq']
        exact hlast
  rw [← hset]
  exact iidCodeMeasure_tailPrefix_mass n q

/-- The `tau - 1` source codes before the final step at the right-coordinate -/
@[expose] def stoppedWord (r : ℕ) (ω : ℕ → Fin 3) :
    Fin (boltzmannTau r ω - 1) → Fin 3 :=
  fun i => ω (i.val + 1)

private theorem boltzmann_no_prior_hit (r : ℕ) (ω : ℕ → Fin 3)
    (hE : ω ∈ boltzmannEvent r) :
    ∀ j < boltzmannTau r ω, (codeWalk ω j).2 ≠ -(r : ℤ) := by
  rcases hE with ⟨s, hs, _⟩
  let hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := ⟨s, hs⟩
  have hτ : boltzmannTau r ω = Nat.find hhit := by
    simp [boltzmannTau, hhit]
  intro j hj heq
  have hj' : j < Nat.find hhit := by simpa [hτ] using hj
  exact (Nat.find_min hhit hj') heq

private theorem codeWalk_snd_strict_before (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    ∀ j < boltzmannTau r ω, -(r : ℤ) < (codeWalk ω j).2 := by
  have hno := boltzmann_no_prior_hit r ω hE
  intro j hj
  induction j with
  | zero => rw [codeWalk_zero]; omega
  | succ j ih =>
    have hjt : j < boltzmannTau r ω := by omega
    have hprev := ih hjt
    have hstep : (codeWalk ω (j + 1)).2 - (codeWalk ω j).2 =
        (lazyTwoDimensionalStep (ω (j + 1))).2 := by
      simpa only [Prod.snd_sub] using congrArg Prod.snd (codeWalk_succ_sub ω j)
    have hlower : -1 ≤ (lazyTwoDimensionalStep (ω (j + 1))).2 := by
      generalize hc : ω (j + 1) = c
      fin_cases c <;> simp [lazyTwoDimensionalStep]
    have hnot := hno (j + 1) hj
    omega

private theorem codeWalk_eq_streamCoordinates (ω : ℕ → Fin 3) (n : ℕ) :
    L (boltzmannKMSWStream ω) n = (codeWalk ω n).1 ∧
      R (boltzmannKMSWStream ω) n = (codeWalk ω n).2 := by
  constructor
  · rw [kmsw_L_eq, codeWalk_eq_integrateCodes]
    rfl
  · rw [kmsw_R_eq, codeWalk_eq_integrateCodes]
    rfl

private theorem stoppedWord_integrate_eq (r : ℕ) (ω : ℕ → Fin 3)
    (k : ℕ) (hk : k ≤ boltzmannTau r ω - 1) :
    integrateCodes (finiteCodeExtend (stoppedWord r ω)) k = codeWalk ω k := by
  rw [codeWalk_eq_integrateCodes]
  unfold integrateCodes
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hit : i < boltzmannTau r ω - 1 := lt_of_lt_of_le hik hk
  simp [finiteCodeExtend, stoppedWord, hit]

/-- The stopped prefix is in the finite walk class, with its left-boundary
length represented by the natural number whose cast is `L w tau`. This proves
the walk side's endpoint and cone conditions for the implemented step set; -/
theorem stoppedWord_admissible (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    KMSWWalkAdmissible
      (L (boltzmannKMSWStream ω) (boltzmannTau r ω)).toNat r (boltzmannTau r ω)
      (stoppedWord r ω) ∧
      ((L (boltzmannKMSWStream ω) (boltzmannTau r ω)).toNat : ℤ) =
        L (boltzmannKMSWStream ω) (boltzmannTau r ω) := by
  let t := boltzmannTau r ω
  let w := boltzmannKMSWStream ω
  have hobs := boltzmann_boundary_observable r hr ω hE
  dsimp only [t, w] at hobs
  rcases hobs with ⟨ht, hlast, _, _, _, _, _, _⟩
  rcases hE with ⟨s, hs, hLnonneg⟩
  have hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := ⟨s, hs⟩
  have hτhit : (codeWalk ω t).2 = -(r : ℤ) := by
    dsimp [t]
    exact boltzmann_tau_spec r ω hhit
  have htle : t ≤ s := by
    have hτ : t = Nat.find hhit := by simp [t, boltzmannTau, hhit]
    rw [hτ]
    exact Nat.find_min' hhit hs
  have hLnonneg' : ∀ j ≤ t, 0 ≤ (codeWalk ω j).1 := by
    intro j hj
    have hj' : j ≤ s := le_trans hj htle
    exact hLnonneg j hj'
  have hLnonnegT : 0 ≤ (L w t) := by
    rw [(codeWalk_eq_streamCoordinates ω t).1]
    exact hLnonneg' t le_rfl
  have hlast' : ω t = 2 := by simpa [t] using hlast
  have hindex : (t - 1) + 1 = t := by omega
  have hstepSnd : (codeWalk ω t).2 - (codeWalk ω (t - 1)).2 =
      (lazyTwoDimensionalStep (ω t)).2 := by
    simpa only [hindex, Prod.snd_sub] using
      congrArg Prod.snd (codeWalk_succ_sub ω (t - 1))
  have hstepFst : (codeWalk ω t).1 - (codeWalk ω (t - 1)).1 =
      (lazyTwoDimensionalStep (ω t)).1 := by
    simpa only [hindex, Prod.fst_sub] using
      congrArg Prod.fst (codeWalk_succ_sub ω (t - 1))
  have hstepSnd' : (codeWalk ω t).2 - (codeWalk ω (t - 1)).2 = -1 := by
    rw [hstepSnd, hlast']
    rfl
  have hstepFst' : (codeWalk ω t).1 - (codeWalk ω (t - 1)).1 = 1 := by
    rw [hstepFst, hlast']
    rfl
  have hprevR : (codeWalk ω (t - 1)).2 = -(r : ℤ) + 1 := by
    have hbefore : -(r : ℤ) < (codeWalk ω (t - 1)).2 :=
      codeWalk_snd_strict_before r hr ω ⟨s, hs, hLnonneg⟩ (t - 1) (by omega)
    omega
  have hprevL : (codeWalk ω t).1 = (codeWalk ω (t - 1)).1 + 1 := by omega
  have hLnonnegPrev : 0 ≤ (codeWalk ω (t - 1)).1 := hLnonneg' (t - 1) (by omega)
  have hcast : ((L w t).toNat : ℤ) = L w t := Int.toNat_of_nonneg hLnonnegT
  have hcastMinus : ((L w t).toNat : ℤ) - 1 = (codeWalk ω (t - 1)).1 := by
    calc
      ((L w t).toNat : ℤ) - 1 = (codeWalk ω t).1 - 1 := by
        rw [hcast, (codeWalk_eq_streamCoordinates ω t).1]
      _ = (codeWalk ω (t - 1)).1 := by rw [hprevL]; omega
  have hwalkEnd : integrateCodes (finiteCodeExtend (stoppedWord r ω)) (t - 1) =
      (((L w t).toNat : ℤ) - 1, -(r : ℤ) + 1) := by
    rw [stoppedWord_integrate_eq r ω (t - 1) (by omega)]
    exact Prod.ext hcastMinus.symm hprevR
  have hcone : ∀ k ∈ Finset.range (t - 1 + 1),
      0 ≤ (integrateCodes (finiteCodeExtend (stoppedWord r ω)) k).1 ∧
        -(r : ℤ) + 1 ≤ (integrateCodes (finiteCodeExtend (stoppedWord r ω)) k).2 := by
    intro k hk
    have hk' : k ≤ t - 1 := by
      have := Finset.mem_range.mp hk
      omega
    have hw := stoppedWord_integrate_eq r ω k hk'
    have hL := hLnonneg' k (by omega)
    have hRstrict := codeWalk_snd_strict_before r hr ω ⟨s, hs, hLnonneg⟩ k (by omega)
    rw [hw]
    exact ⟨hL, by omega⟩
  refine ⟨?_, hcast⟩
  unfold KMSWWalkAdmissible
  exact ⟨hwalkEnd, hcone⟩

private theorem finiteWord_integrate_eq_codeWalk {ell r n : ℕ}
    (c : KMSWWalkClass ell r n) (ω : ℕ → Fin 3)
    (hprefix : ∀ i : Fin (n - 1), ω (i.val + 1) = c.val i)
    (k : ℕ) (hk : k ≤ n - 1) :
    integrateCodes (finiteCodeExtend c.val) k = codeWalk ω k := by
  rw [codeWalk_eq_integrateCodes]
  unfold integrateCodes
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hit : i < n - 1 := lt_of_lt_of_le hik hk
  simpa [finiteCodeExtend, hit] using
    congrArg lazyTwoDimensionalStep (hprefix ⟨i, hit⟩).symm

/-- Every class cylinder produces a first hit at time `n` and satisfies the
conditioning event. The finite walk constraints force the final code `2` to
reach `R=-r` only after all earlier coordinates remain at least `-r+1`. -/
theorem stoppedCylinder_subset_eventSlice {ell r n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ell r n) :
    stoppedCylinder c ⊆
      {ω | ω ∈ boltzmannEvent r ∧ boltzmannTau r ω = n} := by
  intro ω hω
  rcases hω with ⟨hprefix, hlast⟩
  rcases c.property with ⟨hend, hcone⟩
  have hprev : codeWalk ω (n - 1) = ((ell : ℤ) - 1, -(r : ℤ) + 1) := by
    rw [← finiteWord_integrate_eq_codeWalk c ω hprefix (n - 1) le_rfl]
    exact hend
  have hindex : (n - 1) + 1 = n := by omega
  have hstep : codeWalk ω n - codeWalk ω (n - 1) = (1, -1) := by
    simpa [hindex, hlast, lazyTwoDimensionalStep] using
      codeWalk_succ_sub ω (n - 1)
  have hwalk : codeWalk ω n = codeWalk ω (n - 1) + (1, -1) := by
    calc
      codeWalk ω n = (codeWalk ω n - codeWalk ω (n - 1)) + codeWalk ω (n - 1) := by abel
      _ = (1, -1) + codeWalk ω (n - 1) := by rw [hstep]
      _ = codeWalk ω (n - 1) + (1, -1) := by abel
  have hRhit : (codeWalk ω n).2 = -(r : ℤ) := by
    rw [hwalk, hprev]
    simp only [Prod.snd_add]
    omega
  have hLhit : (codeWalk ω n).1 = (ell : ℤ) := by
    rw [hwalk, hprev]
    simp only [Prod.fst_add]
    omega
  have hconeAt : ∀ j ≤ n - 1,
      0 ≤ (codeWalk ω j).1 ∧ -(r : ℤ) + 1 ≤ (codeWalk ω j).2 := by
    intro j hj
    have hjmem : j ∈ Finset.range (n - 1 + 1) := by
      simp only [Finset.mem_range]
      omega
    have hwalkj := finiteWord_integrate_eq_codeWalk c ω hprefix j hj
    rw [← hwalkj]
    exact hcone j hjmem
  have hnonneg : ∀ j ≤ n, 0 ≤ (codeWalk ω j).1 := by
    intro j hj
    by_cases hlastTime : j = n
    · subst j
      rw [hLhit]
      exact_mod_cast (Nat.zero_le ell)
    · have hj' : j ≤ n - 1 := by omega
      exact (hconeAt j hj').1
  have hnoPrior : ∀ j < n, (codeWalk ω j).2 ≠ -(r : ℤ) := by
    intro j hj
    have hR := (hconeAt j (by omega)).2
    omega
  have hhit : ∃ k, (codeWalk ω k).2 = -(r : ℤ) := ⟨n, hRhit⟩
  have hτ : boltzmannTau r ω = n := by
    unfold boltzmannTau
    rw [dite_eq_left hhit]
    exact (Nat.find_eq_iff hhit).2 ⟨hRhit, hnoPrior⟩
  refine ⟨?_, hτ⟩
  exact ⟨n, hRhit, hnonneg⟩

/-- The event slice with `tau = n` is exactly the union of the stopped
cylinders indexed by left length and the finite KMSW walk class.
This is the walk-level decomposition for Lemma 3.11; the map-level bijection -/
theorem stoppedEventSlice_eq_walkCylinders (r n : ℕ)
    (hr : 1 ≤ r) (hn : 1 ≤ n) :
    {ω | ω ∈ boltzmannEvent r ∧ boltzmannTau r ω = n} =
      ⋃ ell, ⋃ c : KMSWWalkClass ell r n, stoppedCylinder c := by
  ext ω
  constructor
  · rintro ⟨hE, hτ⟩
    have hadm := stoppedWord_admissible r hr ω hE
    let t := n
    cases hτ
    let ell := (L (boltzmannKMSWStream ω) t).toNat
    let c : KMSWWalkClass ell r t := ⟨stoppedWord r ω, by
      dsimp [ell]
      exact hadm.1⟩
    have hobs := boltzmann_boundary_observable r hr ω hE
    dsimp only at hobs
    rcases hobs with ⟨_, hlast, _, _, _, _, _, _⟩
    have hlast' : ω t = 2 := hlast
    refine Set.mem_iUnion.mpr ⟨ell, Set.mem_iUnion.mpr ⟨c, ?_⟩⟩
    constructor
    · intro i
      rfl
    · exact hlast'
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨ell, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨c, hcyl⟩
    exact stoppedCylinder_subset_eventSlice hn c hcyl

/-- Intersecting the conditioning event, the exact first-hit event, and a
fixed admissible word cylinder imposes precisely its final code `2`; hence
its unconditioned mass is `3^(-n)`. This is the walk-level mass statement for -/
theorem iidCodeMeasure_event_stoppedCylinder_mass {ell r n : ℕ}
    (hr : 1 ≤ r) (hn : 1 ≤ n) (c : KMSWWalkClass ell r n) :
    iidCodeMeasure {ω | ω ∈ boltzmannEvent r ∧ boltzmannTau r ω = n ∧
      ∀ i : Fin (n - 1), ω (i.val + 1) = c.val i} =
        (1 / 3 : ENNReal) ^ n := by
  have hset : {ω | ω ∈ boltzmannEvent r ∧ boltzmannTau r ω = n ∧
      ∀ i : Fin (n - 1), ω (i.val + 1) = c.val i} = stoppedCylinder c := by
    ext ω
    constructor
    · rintro ⟨hE, hτ, hprefix⟩
      have hobs := boltzmann_boundary_observable r hr ω hE
      dsimp only at hobs
      rcases hobs with ⟨_, hlast, _, _, _, _, _, _⟩
      have hlast' : ω n = 2 := by simpa [hτ] using hlast
      exact ⟨hprefix, hlast'⟩
    · rintro ⟨hprefix, hlast⟩
      have hslice := stoppedCylinder_subset_eventSlice hn c ⟨hprefix, hlast⟩
      exact ⟨hslice.1, hslice.2, hprefix⟩
  rw [hset]
  exact iidCodeMeasure_stoppedCylinder_mass hn c

private theorem measurable_stoppedCylinder {ell r n : ℕ}
    (c : KMSWWalkClass ell r n) : MeasurableSet (stoppedCylinder c) := by
  have hpref : Measurable (fun ω : ℕ → Fin 3 =>
      fun i : Fin (n - 1) => ω (i.val + 1)) :=
    Measurable.of_eval fun i => measurable_pi_apply (i.val + 1)
  have hlast : Measurable (fun ω : ℕ → Fin 3 => ω n) := measurable_pi_apply n
  rw [show stoppedCylinder c =
      {ω : ℕ → Fin 3 | (fun i : Fin (n - 1) => ω (i.val + 1)) = c.val} ∩
        {ω : ℕ → Fin 3 | ω n = 2} by
    ext ω
    simp [stoppedCylinder, funext_iff]]
  exact (hpref (measurableSet_singleton c.val)).inter
    (hlast (measurableSet_singleton 2))

/-- Under conditioning on `boltzmannEvent r`, each admissible stopped code
cylinder has probability `3^(-n) / P(E)`. This proves the walk-cylinder
conditional law in Lemma 3.11; converting it to the map law needs Theorem 3.5. -/
theorem boltzmann_cond_stoppedCylinder_mass {ell r n : ℕ}
    (_hr : 1 ≤ r) (hn : 1 ≤ n) (c : KMSWWalkClass ell r n) :
    iidCodeMeasure[|boltzmannEvent r] (stoppedCylinder c) =
      (1 / 3 : ENNReal) ^ n / iidCodeMeasure (boltzmannEvent r) := by
  have hsubset : stoppedCylinder c ⊆ boltzmannEvent r := by
    intro ω hω
    exact (stoppedCylinder_subset_eventSlice hn c hω).1
  rw [ProbabilityTheory.cond_apply' (measurable_stoppedCylinder c) iidCodeMeasure]
  rw [Set.inter_eq_right.mpr hsubset,
    iidCodeMeasure_stoppedCylinder_mass hn c]
  calc
    (iidCodeMeasure (boltzmannEvent r))⁻¹ * (1 / 3 : ENNReal) ^ n =
        (1 / 3 : ENNReal) ^ n * (iidCodeMeasure (boltzmannEvent r))⁻¹ := by
          rw [mul_comm]
    _ = (1 / 3 : ENNReal) ^ n / iidCodeMeasure (boltzmannEvent r) := by
          simpa only [mul_comm] using
            (ENNReal.div_eq_inv_mul).symm

/-- Equal finite stopped words give equal KMSW bookkeeping stages at the
stopping prefix (`kmswStage_eq_of_prefix`, `KMSWInverse.lean:107`). This is
the stage-code compatibility needed for the separate map-level argument.
The implemented step set is `{(-1, 0), (0, 1), (1, -1)}`; legal-step convention/S7 remain -/
theorem stoppedStage_eq_of_stoppedWord_eq (r : ℕ) (ω : ℕ → Fin 3)
    {ell : ℕ} (c : KMSWWalkClass ell r (boltzmannTau r ω))
    (hc : c.val = stoppedWord r ω) :
    kmswStage (codeExtend c) (boltzmannTau r ω - 1) =
      kmswStage (boltzmannKMSWStream ω) (boltzmannTau r ω - 1) := by
  apply kmswStage_eq_of_prefix
  intro i hi
  rw [codeExtend_of_lt c i hi, hc]
  rfl

end DirectedDistances.KMSW
