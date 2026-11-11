/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Count
public import Mathlib.Data.ENat.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Nat.Find
meta import Lean.Elab.Tactic.Omega

/-! # Generic positive-success ranks with an infinite nonoccurrence value

Generic infrastructure for the positive-time enumeration needed in Lemma 4.9
define the paper's renewal times or establish the geometric Lemma 4.8.
The independent account proof proposal is retained under allocation 27371762. -/

@[expose] public section
namespace DirectedDistances.RandomWalk
open scoped Classical

/-- Number of strictly positive successes through and including `n`. -/
noncomputable def positiveSuccessCount (S : ℕ → Prop) (n : ℕ) : ℕ :=
  Nat.count (fun j => 0 < j ∧ S j) (n + 1)

/-- The positive endpoint of a specified success rank. -/
def PositiveSuccessRank (S : ℕ → Prop) (m n : ℕ) : Prop :=
  0 < n ∧ S n ∧ positiveSuccessCount S n = m

/-- Graph of a generic extended-natural enumeration, including rank zero. -/
def IsPositiveSuccessTime (S : ℕ → Prop) (m : ℕ) (t : ℕ∞) : Prop :=
  if m = 0 then t = 0 else
    ENat.recTopCoe (∀ n, positiveSuccessCount S n < m)
      (fun n => PositiveSuccessRank S m n) t

@[simp] theorem positiveSuccessCount_zero (S : ℕ → Prop) :
    positiveSuccessCount S 0 = 0 := by
  simp [positiveSuccessCount, Nat.count_one]

theorem positiveSuccessCount_succ (S : ℕ → Prop) (n : ℕ) :
    positiveSuccessCount S (n + 1) =
      positiveSuccessCount S n + if S (n + 1) then 1 else 0 := by
  simp only [positiveSuccessCount, Nat.count_succ, Nat.zero_lt_succ, true_and]

theorem positiveSuccessCount_mono (S : ℕ → Prop) :
    Monotone (positiveSuccessCount S) := by
  intro n k hnk
  exact Nat.count_monotone _ (Nat.add_le_add_right hnk 1)

theorem positiveSuccessCount_eq_card (S : ℕ → Prop) (n : ℕ) :
    positiveSuccessCount S n = ((Finset.Icc 1 n).filter S).card := by
  rw [positiveSuccessCount, Nat.count_eq_card_filter_range]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hj, hjpos, hs⟩
    exact ⟨⟨by omega, by omega⟩, hs⟩
  · rintro ⟨⟨hjpos, hj⟩, hs⟩
    exact ⟨by omega, by omega, hs⟩

theorem positiveSuccessRank_unique (S : ℕ → Prop) {m n k : ℕ}
    (hn : PositiveSuccessRank S m n) (hk : PositiveSuccessRank S m k) : n = k := by
  have hn' : Nat.count (fun j => 0 < j ∧ S j) n + 1 = m := by
    simpa only [positiveSuccessCount, Nat.count_succ, ite_eq_left (show 0 < n ∧ S n from ⟨hn.1, hn.2.1⟩)]
      using hn.2.2
  have hk' : Nat.count (fun j => 0 < j ∧ S j) k + 1 = m := by
    simpa only [positiveSuccessCount, Nat.count_succ, ite_eq_left (show 0 < k ∧ S k from ⟨hk.1, hk.2.1⟩)]
      using hk.2.2
  exact Nat.count_injective (p := fun j => 0 < j ∧ S j) ⟨hn.1, hn.2.1⟩ ⟨hk.1, hk.2.1⟩ (by omega)

theorem exists_positiveSuccessRank_iff (S : ℕ → Prop) {m : ℕ} (hm : 0 < m) :
    (∃ n, PositiveSuccessRank S m n) ↔ ∃ n, m ≤ positiveSuccessCount S n := by
  constructor
  · rintro ⟨n, _, _, hcount⟩
    exact ⟨n, hcount.ge⟩
  · intro h
    have hr : 0 < Nat.find h := by
      by_contra hz
      have hz' : Nat.find h = 0 := by omega
      have hs := Nat.find_spec h
      rw [hz', positiveSuccessCount_zero] at hs
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    have hlo : positiveSuccessCount S k < m := by
      have hmin := Nat.find_min h (show k < Nat.find h by omega)
      omega
    have hhi := Nat.find_spec h
    rw [hk, positiveSuccessCount_succ] at hhi
    have hs : S (k + 1) := by
      by_contra hnot
      rw [ite_eq_right hnot] at hhi
      omega
    refine ⟨k + 1, Nat.zero_lt_succ _, hs, ?_⟩
    rw [positiveSuccessCount_succ, ite_eq_left hs]
    rw [ite_eq_left hs] at hhi
    omega

theorem existsUnique_positiveSuccessRank (S : ℕ → Prop) {m : ℕ} (hm : 0 < m)
    (h : ∃ n, m ≤ positiveSuccessCount S n) : ∃! n, PositiveSuccessRank S m n := by
  obtain ⟨n, hn⟩ := (exists_positiveSuccessRank_iff S hm).mpr h
  exact ⟨n, hn, fun k hk => positiveSuccessRank_unique S hk hn⟩

theorem isPositiveSuccessTime_zero_iff (S : ℕ → Prop) (t : ℕ∞) :
    IsPositiveSuccessTime S 0 t ↔ t = 0 := by
  simp only [IsPositiveSuccessTime, ite_true]

theorem isPositiveSuccessTime_natCast_iff (S : ℕ → Prop) {m : ℕ}
    (hm : 0 < m) (n : ℕ) :
    IsPositiveSuccessTime S m (n : ℕ∞) ↔ PositiveSuccessRank S m n := by
  simp only [IsPositiveSuccessTime, ite_eq_right (Nat.ne_of_gt hm), ENat.recTopCoe_natCast]

theorem isPositiveSuccessTime_top_iff (S : ℕ → Prop) {m : ℕ} (hm : 0 < m) :
    IsPositiveSuccessTime S m ⊤ ↔ ∀ n, positiveSuccessCount S n < m := by
  simp only [IsPositiveSuccessTime, ite_eq_right (Nat.ne_of_gt hm), ENat.recTopCoe_top]

theorem existsUnique_positiveSuccessTime (S : ℕ → Prop) (m : ℕ) :
    ∃! t : ℕ∞, IsPositiveSuccessTime S m t := by
  by_cases hm : m = 0
  · subst m
    exact ⟨0, (isPositiveSuccessTime_zero_iff S 0).mpr rfl,
      fun t ht => (isPositiveSuccessTime_zero_iff S t).mp ht⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  by_cases hex : ∃ n, m ≤ positiveSuccessCount S n
  · obtain ⟨n, hn, huniq⟩ := existsUnique_positiveSuccessRank S hmpos hex
    refine ⟨n, (isPositiveSuccessTime_natCast_iff S hmpos n).mpr hn, ?_⟩
    intro t ht
    induction t using ENat.recTopCoe with
    | top =>
      have hlt := (isPositiveSuccessTime_top_iff S hmpos).mp ht n
      have heq := hn.2.2
      omega
    | coe k =>
      exact congrArg (fun j : ℕ => (j : ℕ∞))
        (huniq k ((isPositiveSuccessTime_natCast_iff S hmpos k).mp ht))
  · refine ⟨⊤, (isPositiveSuccessTime_top_iff S hmpos).mpr ?_, ?_⟩
    · intro n
      exact Nat.lt_of_not_ge fun hn => hex ⟨n, hn⟩
    · intro t ht
      induction t using ENat.recTopCoe with
      | top => rfl
      | coe k =>
        have hk := (isPositiveSuccessTime_natCast_iff S hmpos k).mp ht
        exact False.elim (hex ⟨k, hk.2.2.ge⟩)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_positiveSuccessCount (S : Ω → ℕ → Prop)
    (hS : ∀ n, 0 < n → MeasurableSet {ω | S ω n}) (n : ℕ) :
    Measurable (fun ω => positiveSuccessCount (S ω) n) := by
  classical
  induction n with
  | zero => simpa only [positiveSuccessCount_zero] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℕ)))
  | succ n ih =>
      have hplus : Measurable (fun ω => positiveSuccessCount (S ω) n + 1) :=
        (measurable_of_countable (fun k : ℕ => k + 1)).comp ih
      have hite : Measurable (fun ω => if S ω (n + 1) then
          positiveSuccessCount (S ω) n + 1 else positiveSuccessCount (S ω) n) :=
        Measurable.ite (hS (n + 1) (Nat.zero_lt_succ n)) hplus ih
      simpa only [positiveSuccessCount_succ, add_ite,
        Nat.add_zero] using hite

theorem measurableSet_positiveSuccessRank (S : Ω → ℕ → Prop)
    (hS : ∀ n, 0 < n → MeasurableSet {ω | S ω n}) (m n : ℕ) :
    MeasurableSet {ω | PositiveSuccessRank (S ω) m n} := by
  by_cases hn : 0 < n
  · have hc : MeasurableSet {ω | positiveSuccessCount (S ω) n = m} :=
      (measurable_positiveSuccessCount S hS n) (measurableSet_singleton m)
    simp only [PositiveSuccessRank, hn, true_and]
    change MeasurableSet ({ω | S ω n} ∩ {ω | positiveSuccessCount (S ω) n = m})
    exact (hS n hn).inter hc
  · simp only [PositiveSuccessRank, hn, false_and, Set.ofPred_false, MeasurableSet.empty]

theorem measurableSet_isPositiveSuccessTime_natCast (S : Ω → ℕ → Prop)
    (hS : ∀ n, 0 < n → MeasurableSet {ω | S ω n}) (m n : ℕ) :
    MeasurableSet {ω | IsPositiveSuccessTime (S ω) m (n : ℕ∞)} := by
  by_cases hm : m = 0
  · subst m
    simp only [isPositiveSuccessTime_zero_iff]
    exact MeasurableSet.const _
  · simpa only [isPositiveSuccessTime_natCast_iff _ (Nat.pos_of_ne_zero hm)] using
      measurableSet_positiveSuccessRank S hS m n

theorem measurableSet_isPositiveSuccessTime_top (S : Ω → ℕ → Prop)
    (hS : ∀ n, 0 < n → MeasurableSet {ω | S ω n}) (m : ℕ) :
    MeasurableSet {ω | IsPositiveSuccessTime (S ω) m ⊤} := by
  by_cases hm : m = 0
  · subst m
    simp only [isPositiveSuccessTime_zero_iff]
    exact MeasurableSet.const _
  · simp only [isPositiveSuccessTime_top_iff _ (Nat.pos_of_ne_zero hm)]
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    exact (measurable_positiveSuccessCount S hS n)
      (Set.to_countable {k : ℕ | k < m}).measurableSet

end DirectedDistances.RandomWalk
