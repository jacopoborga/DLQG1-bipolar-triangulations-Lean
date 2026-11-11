/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.PitmanPrefixCompatibility
public import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-! # Deterministic record counts for lazy integer walks

The walk-side record characterizations and count identities used in
No map or boundary structure is represented here. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open scoped Classical

private theorem exists_walk_hit_of_le (p : ℕ → ℤ)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (i d : ℕ) (a : ℤ)
    (hstart : p i ≤ a) (hend : a ≤ p (i + d)) :
    ∃ k, k ≤ d ∧ p (i + k) = a := by
  induction d generalizing i with
  | zero =>
      have hend' : a ≤ p i := by simpa using hend
      have hval : p i = a := by omega
      exact ⟨0, le_rfl, by simpa using hval⟩
  | succ d ih =>
      by_cases hval : p i = a
      · exact ⟨0, by omega, by simpa using hval⟩
      · have hlt : p i < a := by omega
        have hstep' := abs_le.mp (hstep i)
        by_cases hcross : a ≤ p (i + 1)
        · have heq : p (i + 1) = a := by omega
          exact ⟨1, by omega, by simpa using heq⟩
        · have hnext : p (i + 1) < a := by omega
          have hidx : (i + 1) + d = i + (d + 1) := by omega
          have hend' : a ≤ p ((i + 1) + d) := by rw [hidx]; exact hend
          obtain ⟨k, hk, hpk⟩ := ih (i + 1) hnext.le hend'
          refine ⟨k + 1, ?_, ?_⟩
          · omega
          · have hidx' : i + (k + 1) = (i + 1) + k := by omega
            rw [hidx']
            exact hpk

private theorem exists_walk_hit_of_ge (p : ℕ → ℤ)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (i d : ℕ) (a : ℤ)
    (hstart : a ≤ p i) (hend : p (i + d) ≤ a) :
    ∃ k, k ≤ d ∧ p (i + k) = a := by
  have hneg : ∀ j, |(-p (j + 1)) - (-p j)| ≤ 1 := by
    intro j
    apply abs_le.mpr
    constructor
    · have h := (abs_le.mp (hstep j)).2
      omega
    · have h := (abs_le.mp (hstep j)).1
      omega
  obtain ⟨k, hk, hval⟩ :=
    exists_walk_hit_of_le (fun j => -p j) hneg i d (-a) (by omega) (by omega)
  exact ⟨k, hk, by omega⟩

private theorem globalLazyRunningMinimum_attained (p : ℕ → ℤ) (n : ℕ) :
    ∃ i, i ≤ n ∧ p i = globalLazyRunningMinimum p n := by
  classical
  obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.range (n + 1))
    (H := ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩) p
  refine ⟨i, Nat.le_of_lt_succ (Finset.mem_range.mp hi), ?_⟩
  exact hval.symm

/-- The last visit to a level between the prefix minimum and endpoint is a
future strict record. This is the upper-left characterization in -/
theorem future_strict_record_level_last_visit
    (p : ℕ → ℤ)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) (ℓ : ℤ)
    (hmin : globalLazyRunningMinimum p n ≤ ℓ) (hend : ℓ ≤ p n) :
    p (Nat.findGreatest (fun i => p i = ℓ) n) = ℓ ∧
      ∀ j, Nat.findGreatest (fun i => p i = ℓ) n < j → j ≤ n →
        ℓ + 1 ≤ p j := by
  classical
  obtain ⟨i, hin, hminval⟩ := globalLazyRunningMinimum_attained p n
  have hidx : i + (n - i) = n := by omega
  have hend' : ℓ ≤ p (i + (n - i)) := by rw [hidx]; exact hend
  obtain ⟨k, hk, hhit⟩ := exists_walk_hit_of_le p hstep i (n - i) ℓ
    (by rw [hminval]; exact hmin) hend'
  have hkn : i + k ≤ n := by omega
  let last := Nat.findGreatest (fun t => p t = ℓ) n
  have hlastn : last ≤ n := Nat.findGreatest_le n
  have hlastval : p last = ℓ := by
    simpa [last] using (Nat.findGreatest_spec (P := fun t => p t = ℓ)
      (m := i + k) (n := n) hkn hhit)
  constructor
  · exact hlastval
  · intro j hlastj hjn
    have hne : p j ≠ ℓ := by
      intro heq
      have hjlast : j ≤ last := Nat.le_findGreatest (P := fun i => p i = ℓ)
        (m := j) (n := n) hjn heq
      omega
    have hjgt : ℓ < p j := by
      by_contra hnot
      have hjle : p j ≤ ℓ := by omega
      by_cases heq : p j = ℓ
      · exact hne heq
      · have hjlt : p j < ℓ := by omega
        have hidx' : j + (n - j) = n := by omega
        have hend'' : ℓ ≤ p (j + (n - j)) := by rw [hidx']; exact hend
        obtain ⟨q, hq, hqval⟩ :=
          exists_walk_hit_of_le p hstep j (n - j) ℓ hjlt.le hend''
        have hqBound : j + q ≤ n := by omega
        have hqLast : j + q ≤ last := Nat.le_findGreatest (P := fun i => p i = ℓ)
          (m := j + q) (n := n) hqBound hqval
        have hqpos : 0 < q := by
          by_contra h
          have hq0 : q = 0 := by omega
          subst q
          have hqeq : p j = ℓ := by simpa using hqval
          exact heq hqeq
        omega
    omega

/-- Each integer level in the closed interval from the prefix minimum to
p n has exactly one time in the upper-left record set, namely its last -/
theorem future_strict_record_level_unique
    (p : ℕ → ℤ)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) (ℓ : ℤ)
    (hmin : globalLazyRunningMinimum p n ≤ ℓ) (hend : ℓ ≤ p n) :
    ∃! m, m ∈ ((Finset.range (n + 1)).filter
      (fun m => ∀ j, m < j → j ≤ n → p m + 1 ≤ p j)) ∧ p m = ℓ := by
  classical
  let last := Nat.findGreatest (fun i => p i = ℓ) n
  obtain ⟨hlastval, hlastrec⟩ :=
    future_strict_record_level_last_visit p hstep n ℓ hmin hend
  have hlastval' : p last = ℓ := by simpa [last] using hlastval
  have hlastrec' : ∀ j, last < j → j ≤ n → ℓ + 1 ≤ p j := by
    simpa [last] using hlastrec
  have hlastn : last ≤ n := Nat.findGreatest_le n
  refine ⟨last, ?_, ?_⟩
  · constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlastn)
      · intro j hj hjn
        simpa [hlastval'] using hlastrec' j hj hjn
    · exact hlastval
  · intro m hm
    rcases hm with ⟨hmrec, hmp⟩
    have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hmrec).1)
    have hmle : m ≤ last := Nat.le_findGreatest (P := fun i => p i = ℓ)
      (m := m) (n := n) hmn hmp
    have hlastle : last ≤ m := by
      by_contra hnot
      have hlt : m < last := by omega
      have h := (Finset.mem_filter.mp hmrec).2 last hlt hlastn
      rw [hmp, hlastval'] at h
      omega
    exact hmle.antisymm hlastle

/-- Each level from the prefix minimum through, but excluding, the endpoint
has exactly one shifted upper-right record time. It is one plus the last -/
theorem future_strict_record_shift_level_unique
    (p : ℕ → ℤ)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) (ℓ : ℤ)
    (hmin : globalLazyRunningMinimum p n ≤ ℓ) (hend : ℓ < p n) :
    ∃! m, m ∈ ((Finset.Icc 1 n).filter
      (fun m => ∀ j, m ≤ j → j ≤ n → p (m - 1) + 1 ≤ p j)) ∧
        p (m - 1) = ℓ := by
  classical
  let last := Nat.findGreatest (fun i => p i = ℓ) n
  have hlastn : last ≤ n := Nat.findGreatest_le n
  obtain ⟨hlastval, hlastrec⟩ :=
    future_strict_record_level_last_visit p hstep n ℓ hmin hend.le
  have hlastval' : p last = ℓ := by simpa [last] using hlastval
  have hlastrec' : ∀ j, last < j → j ≤ n → ℓ + 1 ≤ p j := by
    simpa [last] using hlastrec
  have hlastlt : last < n := by
    by_contra h
    have hEq : last = n := by omega
    have hpn : p n = ℓ := by simpa [hEq] using hlastval'
    rw [hpn] at hend
    omega
  refine ⟨last + 1, ?_, ?_⟩
  · constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro j hj hnj
        have hlastj : last < j := by omega
        have hsub : last + 1 - 1 = last := by omega
        simpa [last, hsub, hlastval'] using hlastrec' j hlastj hnj
    · have hsub : last + 1 - 1 = last := by omega
      simpa [last, hsub] using hlastval
  · intro m hm
    rcases hm with ⟨hmrec, hmp⟩
    have hmIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hmrec).1
    have hmpos : 1 ≤ m := hmIcc.1
    have hmn : m ≤ n := hmIcc.2
    let r := m - 1
    have hrlt : r < n := by dsimp [r]; omega
    have hrval : p r = ℓ := by simpa [r] using hmp
    have hrrec : ∀ j, r < j → j ≤ n → p r + 1 ≤ p j := by
      intro j hrj hjn
      have hmj : m ≤ j := by dsimp [r] at hrj; omega
      have h := (Finset.mem_filter.mp hmrec).2 j hmj hjn
      have hsub : m - 1 = r := by rfl
      rw [← hsub]
      exact h
    have hlastEq : r = last := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hrrec last hlt hlastn
        rw [hrval, hlastval'] at h
        omega
      · have h := hlastrec' r hgt (by omega)
        rw [hrval] at h
        omega
    have hmEq : m = r + 1 := by dsimp [r]; omega
    rw [hmEq, hlastEq]

/-- A strict new minimum at a negative level is its first hitting time in the -/
theorem strict_running_minimum_iff_first_hit
    (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n m : ℕ) (ℓ : ℤ)
    (hℓ : ℓ < 0) (hhit : ∃ i, p i = ℓ) :
    (m ∈ ((Finset.Icc 1 n).filter (fun m => ∀ j, j < m → p m < p j)) ∧
      p m = ℓ) ↔ m ≤ n ∧ p m = ℓ ∧ m = Nat.find hhit := by
  classical
  constructor
  · rintro ⟨hm, hpm⟩
    have hm' := Finset.mem_filter.mp hm
    have hmn := (Finset.mem_Icc.mp hm'.1).2
    have hfind : Nat.find hhit = m := by
      apply (Nat.find_eq_iff hhit).2
      constructor
      · exact hpm
      · intro j hj hjeq
        have h := hm'.2 j hj
        rw [hjeq] at h
        omega
    exact ⟨hmn, hpm, hfind.symm⟩
  · rintro ⟨hmn, hpm, hfm⟩
    have hfirst := (Nat.find_eq_iff hhit).1 hfm.symm
    have hrecord : ∀ j, j < m → p m < p j := by
      intro j hj
      by_contra hnot
      have hjle : p j ≤ ℓ := by omega
      have hstart : ℓ ≤ p 0 := by rw [hp0]; exact hℓ.le
      have hend : p (0 + j) ≤ ℓ := by simpa using hjle
      obtain ⟨t, ht, htval⟩ := exists_walk_hit_of_ge p hstep 0 j ℓ hstart hend
      have htval' : p t = ℓ := by simpa using htval
      exact hfirst.2 t (by omega) htval'
    have hmpos : 1 ≤ m := by
      by_contra h
      have hmzero : m = 0 := by omega
      rw [hmzero, hp0] at hpm
      omega
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hmpos, hmn⟩, hrecord⟩, hpm⟩

/-- A weak first minimum, including time zero, is the first hitting time of -/
theorem weak_first_minimum_iff_first_hit
    (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n m : ℕ) (ℓ : ℤ)
    (hℓ : ℓ ≤ 0) (hhit : ∃ i, p i = ℓ) :
    (m ∈ ((Finset.range (n + 1)).filter (fun m => ∀ j, j < m → p m < p j)) ∧
      p m = ℓ) ↔ m ≤ n ∧ p m = ℓ ∧ m = Nat.find hhit := by
  classical
  constructor
  · rintro ⟨hm, hpm⟩
    have hm' := Finset.mem_filter.mp hm
    have hmn := Nat.le_of_lt_succ (Finset.mem_range.mp hm'.1)
    have hfind : Nat.find hhit = m := by
      apply (Nat.find_eq_iff hhit).2
      constructor
      · exact hpm
      · intro j hj hjeq
        have h := hm'.2 j hj
        rw [hjeq] at h
        omega
    exact ⟨hmn, hpm, hfind.symm⟩
  · rintro ⟨hmn, hpm, hfm⟩
    have hfirst := (Nat.find_eq_iff hhit).1 hfm.symm
    have hrecord : ∀ j, j < m → p m < p j := by
      intro j hj
      by_contra hnot
      have hjle : p j ≤ ℓ := by omega
      have hstart : ℓ ≤ p 0 := by rw [hp0]; exact hℓ
      have hend : p (0 + j) ≤ ℓ := by simpa using hjle
      obtain ⟨t, ht, htval⟩ := exists_walk_hit_of_ge p hstep 0 j ℓ hstart hend
      have htval' : p t = ℓ := by simpa using htval
      exact hfirst.2 t (by omega) htval'
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmn), hrecord⟩, hpm⟩

/-- The lower-left strict-record times are in bijection with the levels in
[globalLazyRunningMinimum p n, 0). This is the counting characterization in -/
theorem strict_running_minimum_level_unique
    (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) (ℓ : ℤ)
    (hmin : globalLazyRunningMinimum p n ≤ ℓ) (hℓ : ℓ < 0) :
    ∃! m, m ∈ ((Finset.Icc 1 n).filter (fun m => ∀ j, j < m → p m < p j)) ∧
      p m = ℓ := by
  classical
  obtain ⟨i, hin, hminval⟩ := globalLazyRunningMinimum_attained p n
  have hstart : ℓ ≤ p 0 := by rw [hp0]; exact hℓ.le
  have hend : p (0 + i) ≤ ℓ := by simpa [Nat.zero_add, hminval] using hmin
  obtain ⟨k, hk, hhitval⟩ := exists_walk_hit_of_ge p hstep 0 i ℓ hstart hend
  have hidx : k ≤ n := by omega
  have hhit : ∃ t, p t = ℓ := ⟨0 + k, by simpa using hhitval⟩
  let first := Nat.find hhit
  have hfirstval : p first = ℓ := Nat.find_spec hhit
  have hfirstbound : first ≤ n := by
    have hfirstle := Nat.find_min' hhit (show p k = ℓ by simpa using hhitval)
    omega
  have hfirstmem : first ∈ ((Finset.Icc 1 n).filter
      (fun m => ∀ j, j < m → p m < p j)) := by
    have hchar := strict_running_minimum_iff_first_hit p hp0 hstep n first ℓ hℓ hhit
    have hp := (hchar).2 ⟨hfirstbound, hfirstval, rfl⟩
    exact hp.1
  refine ⟨first, ⟨hfirstmem, hfirstval⟩, ?_⟩
  intro m hm
  rcases hm with ⟨hmrec, hpm⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := (Finset.mem_filter.mp hfirstmem).2 m hlt
    rw [hfirstval, hpm] at h
    omega
  · have h := (Finset.mem_filter.mp hmrec).2 first hgt
    rw [hfirstval, hpm] at h
    omega

/-- The lower-right first-minimum times, including time zero, are in
bijection with the levels in [globalLazyRunningMinimum p n, 0]. This is the -/
theorem weak_first_minimum_level_unique
    (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) (ℓ : ℤ)
    (hmin : globalLazyRunningMinimum p n ≤ ℓ) (hℓ : ℓ ≤ 0) :
    ∃! m, m ∈ ((Finset.range (n + 1)).filter
      (fun m => ∀ j, j < m → p m < p j)) ∧ p m = ℓ := by
  classical
  obtain ⟨i, hin, hminval⟩ := globalLazyRunningMinimum_attained p n
  have hstart : ℓ ≤ p 0 := by rw [hp0]; exact hℓ
  have hend : p (0 + i) ≤ ℓ := by simpa [Nat.zero_add, hminval] using hmin
  obtain ⟨k, hk, hhitval⟩ := exists_walk_hit_of_ge p hstep 0 i ℓ hstart hend
  have hidx : k ≤ n := by omega
  have hhit : ∃ t, p t = ℓ := ⟨0 + k, by simpa using hhitval⟩
  let first := Nat.find hhit
  have hfirstval : p first = ℓ := Nat.find_spec hhit
  have hfirstbound : first ≤ n := by
    have hfirstle := Nat.find_min' hhit (show p k = ℓ by simpa using hhitval)
    omega
  have hfirstmem : first ∈ ((Finset.range (n + 1)).filter
      (fun m => ∀ j, j < m → p m < p j)) := by
    have hchar := weak_first_minimum_iff_first_hit p hp0 hstep n first ℓ hℓ hhit
    have hp := (hchar).2 ⟨hfirstbound, hfirstval, rfl⟩
    exact hp.1
  refine ⟨first, ⟨hfirstmem, hfirstval⟩, ?_⟩
  intro m hm
  rcases hm with ⟨hmrec, hpm⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := (Finset.mem_filter.mp hfirstmem).2 m hlt
    rw [hfirstval, hpm] at h
    omega
  · have h := (Finset.mem_filter.mp hmrec).2 first hgt
    rw [hfirstval, hpm] at h
    omega

/-- The number of upper-left future strict records is the endpoint minus the
closed-prefix minimum, plus one. Equation (3.2), -/
theorem card_future_strict_records
    (p : ℕ → ℤ) (_hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) :
    ((((Finset.range (n + 1)).filter
      (fun m => ∀ j, m < j → j ≤ n → p m + 1 ≤ p j)).card : ℕ) : ℤ) =
      p n - globalLazyRunningMinimum p n + 1 := by
  classical
  let records := (Finset.range (n + 1)).filter
    (fun m => ∀ j, m < j → j ≤ n → p m + 1 ≤ p j)
  let levels := Finset.Icc (globalLazyRunningMinimum p n) (p n)
  have hminn : globalLazyRunningMinimum p n ≤ p n :=
    globalLazyRunningMinimum_le p le_rfl
  have hcard : records.card = levels.card := by
    apply Finset.card_bij (s := records) (t := levels) (fun m _ => p m)
    · intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm'.1)
      refine Finset.mem_Icc.mpr ⟨globalLazyRunningMinimum_le p hmn, ?_⟩
      by_cases hEq : m = n
      · simp [hEq]
      · have hlt : m < n := by omega
        have h := hm'.2 n hlt le_rfl
        omega
    · intro m hm m' hm' heq
      have hmrec := (Finset.mem_filter.mp hm).2
      have hm'rec := (Finset.mem_filter.mp hm').2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hmrec m' hlt (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hm').1))
        rw [heq] at h
        omega
      · have h := hm'rec m hgt (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hm).1))
        rw [← heq] at h
        omega
    · intro ℓ hℓ
      obtain ⟨m, hm, hpm⟩ :=
        future_strict_record_level_unique p hstep n ℓ
          (Finset.mem_Icc.mp hℓ).1 (Finset.mem_Icc.mp hℓ).2
      exact ⟨m, hm.1, hm.2⟩
  rw [hcard, Int.card_Icc_of_le (a := globalLazyRunningMinimum p n)
    (b := p n) (by omega)]
  omega

/-- The number of shifted upper-right future strict records is the endpoint
minus the closed-prefix minimum. Equation (3.2), -/
theorem card_future_strict_records_shift
    (p : ℕ → ℤ) (_hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) :
    ((((Finset.Icc 1 n).filter
      (fun m => ∀ j, m ≤ j → j ≤ n → p (m - 1) + 1 ≤ p j)).card : ℕ) : ℤ) =
      p n - globalLazyRunningMinimum p n := by
  classical
  let records := (Finset.Icc 1 n).filter
    (fun m => ∀ j, m ≤ j → j ≤ n → p (m - 1) + 1 ≤ p j)
  let levels := Finset.Ico (globalLazyRunningMinimum p n) (p n)
  have hminn : globalLazyRunningMinimum p n ≤ p n :=
    globalLazyRunningMinimum_le p le_rfl
  have hcard : records.card = levels.card := by
    apply Finset.card_bij (s := records) (t := levels) (fun m _ => p (m - 1))
    · intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmn := Finset.mem_Icc.mp hm'.1
      have hprev : m - 1 ≤ n := by omega
      have hlemin := globalLazyRunningMinimum_le p hprev
      have hlt : p (m - 1) < p n := by
        have h := hm'.2 n hmn.2 le_rfl
        omega
      exact Finset.mem_Ico.mpr ⟨hlemin, hlt⟩
    · intro m hm m' hm' heq
      have hmrec := (Finset.mem_filter.mp hm).2
      have hm'rec := (Finset.mem_filter.mp hm').2
      have hmi := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
      have hm'i := Finset.mem_Icc.mp (Finset.mem_filter.mp hm').1
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hidx : m - 1 < m' - 1 := by omega
        have h := hmrec (m' - 1) (by omega) (by omega)
        rw [heq] at h
        omega
      · have hidx : m' - 1 < m - 1 := by omega
        have h := hm'rec (m - 1) (by omega) (by omega)
        rw [← heq] at h
        omega
    · intro ℓ hℓ
      obtain ⟨m, hm, hpm⟩ :=
        future_strict_record_shift_level_unique p hstep n ℓ
          (Finset.mem_Ico.mp hℓ).1 (Finset.mem_Ico.mp hℓ).2
      exact ⟨m, hm.1, hm.2⟩
  rw [hcard, Int.card_Ico_of_le (a := globalLazyRunningMinimum p n)
    (b := p n) hminn]

/-- The number of strict running-minimum times is the negative of the -/
theorem card_strict_running_minima
    (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) :
    ((((Finset.Icc 1 n).filter (fun m => ∀ j, j < m → p m < p j)).card : ℕ) : ℤ) =
      - globalLazyRunningMinimum p n := by
  classical
  let records := (Finset.Icc 1 n).filter (fun m => ∀ j, j < m → p m < p j)
  let levels := Finset.Ico (globalLazyRunningMinimum p n) 0
  have hmin0 : globalLazyRunningMinimum p n ≤ 0 := by
    have h := globalLazyRunningMinimum_le p (Nat.zero_le n)
    rw [hp0] at h
    exact h
  have hcard : records.card = levels.card := by
    apply Finset.card_bij (s := records) (t := levels) (fun m _ => p m)
    · intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmi := Finset.mem_Icc.mp hm'.1
      have hminm := globalLazyRunningMinimum_le p hmi.2
      have hzero : p m < 0 := by
        have hpos : 0 < m := by omega
        have h := hm'.2 0 (by omega)
        rw [hp0] at h
        exact h
      exact Finset.mem_Ico.mpr ⟨hminm, hzero⟩
    · intro m hm m' hm' heq
      have hmrec := (Finset.mem_filter.mp hm).2
      have hm'rec := (Finset.mem_filter.mp hm').2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hm'rec m hlt
        rw [heq] at h
        omega
      · have h := hmrec m' hgt
        rw [heq] at h
        omega
    · intro ℓ hℓ
      obtain ⟨m, hm, hpm⟩ := strict_running_minimum_level_unique p hp0 hstep n ℓ
        (Finset.mem_Ico.mp hℓ).1 (Finset.mem_Ico.mp hℓ).2
      exact ⟨m, hm.1, hm.2⟩
  rw [hcard, Int.card_Ico_of_le (a := globalLazyRunningMinimum p n)
    (b := 0) hmin0]
  omega

/-- The number of weak first-minimum times, including time zero, is one
minus the closed-prefix minimum. Equation (3.2), -/
theorem card_weak_first_minima
    (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (n : ℕ) :
    ((((Finset.range (n + 1)).filter (fun m => ∀ j, j < m → p m < p j)).card : ℕ) : ℤ) =
      - globalLazyRunningMinimum p n + 1 := by
  classical
  let records := (Finset.range (n + 1)).filter (fun m => ∀ j, j < m → p m < p j)
  let levels := Finset.Icc (globalLazyRunningMinimum p n) 0
  have hmin0 : globalLazyRunningMinimum p n ≤ 0 := by
    have h := globalLazyRunningMinimum_le p (Nat.zero_le n)
    rw [hp0] at h
    exact h
  have hcard : records.card = levels.card := by
    apply Finset.card_bij (s := records) (t := levels) (fun m _ => p m)
    · intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmn := Nat.le_of_lt_succ (Finset.mem_range.mp hm'.1)
      have hminm := globalLazyRunningMinimum_le p hmn
      have hnonpos : p m ≤ 0 := by
        by_cases hmzero : m = 0
        · simp [hmzero, hp0]
        · have hpos : 0 < m := by omega
          have h := hm'.2 0 (by omega)
          rw [hp0] at h
          omega
      exact Finset.mem_Icc.mpr ⟨hminm, hnonpos⟩
    · intro m hm m' hm' heq
      have hmrec := (Finset.mem_filter.mp hm).2
      have hm'rec := (Finset.mem_filter.mp hm').2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hm'rec m hlt
        rw [heq] at h
        omega
      · have h := hmrec m' hgt
        rw [heq] at h
        omega
    · intro ℓ hℓ
      obtain ⟨m, hm, hpm⟩ := weak_first_minimum_level_unique p hp0 hstep n ℓ
        (Finset.mem_Icc.mp hℓ).1 (Finset.mem_Icc.mp hℓ).2
      exact ⟨m, hm.1, hm.2⟩
  rw [hcard, Int.card_Icc_of_le (a := globalLazyRunningMinimum p n)
    (b := 0) (by omega)]
  omega

end DirectedDistances.KMSW
