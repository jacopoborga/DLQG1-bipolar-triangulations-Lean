/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.FirstHitBarrierDecomposition
public import DirectedDistances.RandomWalk.RenewalTimeRankBridge
import Mathlib.Data.Nat.Find
meta import Lean.Elab.Tactic.Omega

/-! Supporting lemmas for paper labels `lem-finite-ind` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.RandomWalk
open scoped Classical

private theorem conditionedSecondCoordinateFirstHit_eq_nat_iff
    (r n : ℕ) (p : ℕ → ℤ × ℤ) :
    conditionedSecondCoordinateFirstHit r p = (n : ℕ∞) ↔
      (p n).2 = -(r : ℤ) ∧ ∀ j < n, (p j).2 ≠ -(r : ℤ) := by
  unfold conditionedSecondCoordinateFirstHit
  by_cases h : ∃ j, (p j).2 = -(r : ℤ)
  · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dite_eq_right h]
    constructor
    · intro he
      exact absurd he (ENat.top_ne_natCast n)
    · rintro ⟨hn, _⟩
      exact absurd ⟨n, hn⟩ h

private theorem exists_level_hit_of_le_lastCut
    (p : ℕ → ℤ × ℤ) (r n : ℕ)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0) (hn : (p n).2 ≤ -(r : ℤ)) :
    ∃ j ≤ n, (p j).2 = -(r : ℤ) := by
  induction n with
  | zero =>
      have : (0 : ℤ) ≤ -(r : ℤ) := by simpa [h0] using hn
      exact ⟨0, le_rfl, by omega⟩
  | succ n ih =>
      by_cases hprev : (p n).2 ≤ -(r : ℤ)
      · obtain ⟨j, hj, hhit⟩ := ih hprev
        exact ⟨j, by omega, hhit⟩
      · have hhit : (p (n + 1)).2 = -(r : ℤ) := by
          have := hstep n
          omega
        exact ⟨n + 1, le_rfl, hhit⟩

private theorem positiveSuccessCount_le_lastCut
    (S : ℕ → Prop) (n : ℕ) : positiveSuccessCount S n ≤ n := by
  induction n with
  | zero => exact (positiveSuccessCount_zero S).le
  | succ n ih =>
      rw [positiveSuccessCount_succ]
      split <;> omega

/-- A finite graph value has rank at most its finite time. -/
theorem positiveSuccessTime_le_index
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ)
    (hT : ∀ m, IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (T m p))
    (m n : ℕ) (hfin : T m p ≤ (n : ℕ∞)) : m ≤ n := by
  by_cases hm : m = 0
  · omega
  have hne : T m p ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hfin (ENat.natCast_lt_top n))
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hne
  have htn : t ≤ n := by
    apply ENat.natCast_le_natCast.mp
    calc
      (t : ℕ∞) = T m p := ht
      _ ≤ (n : ℕ∞) := hfin
  have hgraph : IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (t : ℕ∞) := by
    rw [ht]
    exact hT m
  have hrank :=
    (isPositiveSuccessTime_natCast_iff _ (Nat.pos_of_ne_zero hm) t).mp hgraph
  have hcount := positiveSuccessCount_le_lastCut
    (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
      ∀ i, j ≤ i → (p j).1 ≤ (p i).1) t
  have hrankCount : positiveSuccessCount (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) t = m := hrank.2.2
  have hmle : m ≤ t := hrankCount.ge.trans hcount
  omega

/-- Finite graph values increase strictly with their positive ranks. -/
theorem positiveSuccessTime_strictMono_of_finite
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ)
    (hT : ∀ m, IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (T m p))
    {m n : ℕ} (hmn : m < n) (hmfin : T m p ≠ ⊤)
    (hnfin : T n p ≠ ⊤) : T m p < T n p := by
  obtain ⟨tm, htm⟩ := ENat.ne_top_iff_exists.mp hmfin
  obtain ⟨tn, htn⟩ := ENat.ne_top_iff_exists.mp hnfin
  by_cases hm : m = 0
  · subst m
    have hzero : T 0 p = 0 :=
      (isPositiveSuccessTime_zero_iff _ _).mp (hT 0)
    rw [hzero]
    have hgraph : IsPositiveSuccessTime (fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) n (tn : ℕ∞) := by
      rw [htn]
      exact hT n
    have hrank :=
      (isPositiveSuccessTime_natCast_iff _ (by omega) tn).mp hgraph
    calc
      0 < (tn : ℕ∞) := ENat.natCast_lt_natCast.mpr hrank.1
      _ = T n p := htn
  · have hgraphm : IsPositiveSuccessTime (fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (tm : ℕ∞) := by
      rw [htm]
      exact hT m
    have hgraphn : IsPositiveSuccessTime (fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) n (tn : ℕ∞) := by
      rw [htn]
      exact hT n
    have hrankm :=
      (isPositiveSuccessTime_natCast_iff _ (Nat.pos_of_ne_zero hm) tm).mp hgraphm
    have hrankn :=
      (isPositiveSuccessTime_natCast_iff _ (by omega) tn).mp hgraphn
    have hcountm : positiveSuccessCount (fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) tm = m := hrankm.2.2
    have hcountn : positiveSuccessCount (fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) tn = n := hrankn.2.2
    by_contra hlt
    have hle : (tn : ℕ∞) ≤ (tm : ℕ∞) := by
      calc
        (tn : ℕ∞) = T n p := htn
        _ ≤ T m p := le_of_not_gt hlt
        _ = (tm : ℕ∞) := htm.symm
    have hnat := ENat.natCast_le_natCast.mp hle
    have hcount := positiveSuccessCount_mono
      (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) hnat
    have horder : n ≤ m := by
      rw [← hcountn, ← hcountm]
      exact hcount
    omega

/-- The literal A∩B success condition at a positive time is a first-hit
barrier condition at its level. -/
theorem successTime_iff_firstHit (p : ℕ → ℤ × ℤ) (n : ℕ) (hn : 0 < n)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0) :
    ((∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      ∀ i, n ≤ i → (p n).1 ≤ (p i).1) ↔
    ∃ r, 1 ≤ r ∧
      conditionedSecondCoordinateFirstHit r p = (n : ℕ∞) ∧
      firstHitBarrier r p := by
  constructor
  · rintro ⟨hA, hB⟩
    have hneg : (p n).2 ≤ -1 := by
      simpa [h0] using hA 0 hn
    let r := Int.toNat (-(p n).2)
    have hr : 1 ≤ r := by
      dsimp [r]
      omega
    have hnlevel : (p n).2 = -(r : ℤ) := by
      dsimp [r]
      omega
    have hno : ∀ j < n, (p j).2 ≠ -(r : ℤ) := by
      intro j hj heq
      have := hA j hj
      rw [hnlevel, heq] at this
      omega
    have hhit :=
      (conditionedSecondCoordinateFirstHit_eq_nat_iff r n p).2
        ⟨hnlevel, hno⟩
    exact ⟨r, hr, hhit, ⟨n, hhit, fun i hi => hB i hi⟩⟩
  · rintro ⟨r, hr, hhit, hbar⟩
    rcases hbar with ⟨t, ht, hfuture⟩
    have htn : t = n := by
      have heq : (t : ℕ∞) = (n : ℕ∞) := ht.symm.trans hhit
      exact_mod_cast heq
    have hnlevel :=
      (conditionedSecondCoordinateFirstHit_eq_nat_iff r n p).mp hhit
    constructor
    · intro j hj
      have hgt : -(r : ℤ) < (p j).2 := by
        induction j with
        | zero =>
            rw [h0]
            omega
        | succ j ih =>
            have hprev := ih (by omega)
            have hnot := hnlevel.2 (j + 1) (by omega)
            have hs := hstep j
            omega
      rw [hnlevel.1]
      omega
    · intro i hi
      subst t
      exact hfuture i hi

private theorem exists_positiveSuccessTime_at_success
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ)
    (hT : ∀ m, IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (T m p))
    (n : ℕ) (hn : 0 < n)
    (hs : (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      ∀ i, n ≤ i → (p n).1 ≤ (p i).1) :
    ∃ m, 0 < m ∧ T m p = (n : ℕ∞) := by
  classical
  let S := fun j =>
    (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
      ∀ i, j ≤ i → (p j).1 ≤ (p i).1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hcount : positiveSuccessCount S (k + 1) ≠ 0 := by
    rw [positiveSuccessCount_succ, ite_eq_left hs]
    omega
  let m := positiveSuccessCount S (k + 1)
  have hm : 0 < m := Nat.pos_of_ne_zero hcount
  have hrank : PositiveSuccessRank S m (k + 1) := ⟨by omega, hs, rfl⟩
  have hgraph : IsPositiveSuccessTime S m ((k + 1 : ℕ) : ℕ∞) :=
    (isPositiveSuccessTime_natCast_iff S hm (k + 1)).mpr hrank
  obtain ⟨t, ht, huniq⟩ := existsUnique_positiveSuccessTime S m
  have htm : T m p = t := huniq (T m p) (hT m)
  have htn : ((k + 1 : ℕ) : ℕ∞) = t := huniq _ hgraph
  refine ⟨m, hm, ?_⟩
  exact htm.trans htn.symm

private theorem positiveSuccessTime_source_success
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ)
    (hT : ∀ m, IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (T m p))
    {m : ℕ} (hm : 0 < m) (hmfin : T m p ≠ ⊤) :
    ∃ n, 0 < n ∧
      ((∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        ∀ i, n ≤ i → (p n).1 ≤ (p i).1) ∧
      T m p = (n : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hmfin
  have hgraph : IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (n : ℕ∞) := by
    rw [hn]
    exact hT m
  have hrank :=
    (isPositiveSuccessTime_natCast_iff _ hm n).mp hgraph
  exact ⟨n, hrank.1, hrank.2.1, hn.symm⟩

private theorem firstHit_level_time_lt
    (p : ℕ → ℤ × ℤ) (r s tr ts : ℕ)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0) (hrs : r < s)
    (hτr : conditionedSecondCoordinateFirstHit r p = (tr : ℕ∞))
    (hτs : conditionedSecondCoordinateFirstHit s p = (ts : ℕ∞)) :
    tr < ts := by
  have hhitS :=
    (conditionedSecondCoordinateFirstHit_eq_nat_iff s ts p).mp hτs
  have hlevel : (p ts).2 ≤ -(r : ℤ) := by
    rw [hhitS.1]
    omega
  obtain ⟨j, hj, hjhit⟩ :=
    exists_level_hit_of_le_lastCut p r ts hstep h0 hlevel
  have hhitR :=
    (conditionedSecondCoordinateFirstHit_eq_nat_iff r tr p).mp hτr
  have htrj : tr ≤ j := by
    by_contra hnot
    exact hhitR.2 j (by omega) hjhit
  have hjts : j < ts := by
    by_contra hnot
    have : j = ts := by omega
    subst j
    omega
  omega

private theorem firstHit_level_time_le
    (p : ℕ → ℤ × ℤ) (r s tr ts : ℕ)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0) (hrs : r ≤ s)
    (hτr : conditionedSecondCoordinateFirstHit r p = (tr : ℕ∞))
    (hτs : conditionedSecondCoordinateFirstHit s p = (ts : ℕ∞)) :
    tr ≤ ts := by
  by_cases hrs' : r = s
  · subst s
    have heq : tr = ts := by exact_mod_cast hτr.symm.trans hτs
    exact le_of_eq heq
  · have hlt : r < s := by omega
    exact (firstHit_level_time_lt p r s tr ts hstep h0 hlt hτr hτs).le

private theorem firstHit_le_bounded_level
    (p : ℕ → ℤ × ℤ) (r k K : ℕ)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0) (hrk : r ≤ k)
    (hτk : conditionedSecondCoordinateFirstHit k p = (K : ℕ∞)) :
    ∃ R ≤ K,
      conditionedSecondCoordinateFirstHit r p = (R : ℕ∞) ∧
        (p R).2 = -(r : ℤ) := by
  have hhitK :=
    (conditionedSecondCoordinateFirstHit_eq_nat_iff k K p).mp hτk
  obtain ⟨R, hRK, hR⟩ :=
    exists_level_hit_of_le_lastCut p r K hstep h0 (by omega)
  have hex : ∃ j, (p j).2 = -(r : ℤ) := ⟨R, hR⟩
  let t := Nat.find hex
  have ht : (p t).2 = -(r : ℤ) := Nat.find_spec hex
  have hmin : ∀ j < t, (p j).2 ≠ -(r : ℤ) := by
    intro j hj hhit
    have := Nat.find_min' hex hhit
    omega
  have hτr :=
    (conditionedSecondCoordinateFirstHit_eq_nat_iff r t p).2 ⟨ht, hmin⟩
  have htK : t ≤ K := (Nat.find_min' hex hR).trans hRK
  exact ⟨t, htK, hτr, ht⟩





theorem exists_last_successTime_before_firstHit
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ) (k : ℕ)
    (_hk : 1 ≤ k)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0)
    (hT : ∀ m, IsPositiveSuccessTime (fun j =>
      (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (T m p))
    (hτ : conditionedSecondCoordinateFirstHit k p < ⊤) :
    ∃ mk,
      T mk p ≤ conditionedSecondCoordinateFirstHit k p ∧
      (∀ m, T m p ≤ conditionedSecondCoordinateFirstHit k p → m ≤ mk) ∧
      (∀ r, 1 ≤ r → r ≤ k →
        (T mk p = conditionedSecondCoordinateFirstHit r p ↔
          firstHitBarrier r p ∧
            ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s p)) ∧
      (T mk p = 0 ↔
        ∀ s, 1 ≤ s → s ≤ k → ¬ firstHitBarrier s p) := by
  classical
  let τk := conditionedSecondCoordinateFirstHit k p
  obtain ⟨K, hKraw⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hτ)
  have hK : τk = (K : ℕ∞) := hKraw.symm
  have hKhit := (conditionedSecondCoordinateFirstHit_eq_nat_iff k K p).mp hK
  have hzero : T 0 p = 0 :=
    (isPositiveSuccessTime_zero_iff _ _).mp (hT 0)
  let F := (Finset.Icc (0 : ℕ) K).filter fun m => T m p ≤ τk
  have hzeroMem : 0 ∈ F := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le K⟩
    · rw [hzero]
      exact bot_le
  have hFne : F.Nonempty := ⟨0, hzeroMem⟩
  let mk := F.max' hFne
  have hmkMem : mk ∈ F := Finset.max'_mem F hFne
  have hmkLe : T mk p ≤ τk := (Finset.mem_filter.mp hmkMem).2
  have hmax : ∀ m, T m p ≤ τk → m ≤ mk := by
    intro m hm
    have hmK : m ≤ K := by
      apply positiveSuccessTime_le_index T p hT m K
      simpa [τk, hK] using hm
    apply Finset.le_max' F m
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le m, hmK⟩, hm⟩
  have hbarrierSuccess (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ k)
      (hb : firstHitBarrier s p) :
      ∃ j, 0 < j ∧ T j p = conditionedSecondCoordinateFirstHit s p ∧
        T j p ≤ τk := by
    obtain ⟨ts, htsK, hτs, _⟩ :=
      firstHit_le_bounded_level p s k K hstep h0 hsk hK
    have htspos : 0 < ts := by
      by_contra hpos
      have hts0 : ts = 0 := by omega
      have hhit :=
        (conditionedSecondCoordinateFirstHit_eq_nat_iff s ts p).mp hτs
      rw [hts0, h0] at hhit
      omega
    have hsuc := (successTime_iff_firstHit p ts htspos hstep h0).2
      ⟨s, hs, hτs, hb⟩
    obtain ⟨j, hj, hjtime⟩ :=
      exists_positiveSuccessTime_at_success T p hT ts htspos hsuc
    have hτsK : conditionedSecondCoordinateFirstHit s p ≤ τk := by
      calc
        conditionedSecondCoordinateFirstHit s p = (ts : ℕ∞) := hτs
        _ ≤ (K : ℕ∞) := ENat.natCast_le_natCast.mpr htsK
        _ = τk := hK.symm
    refine ⟨j, hj, hjtime.trans hτs.symm, ?_⟩
    exact (hjtime.trans hτs.symm).le.trans hτsK
  have hmkFin : T mk p ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hmkLe hτ)
  have hmkSource (hmkpos : 0 < mk) :=
    positiveSuccessTime_source_success T p hT hmkpos hmkFin
  have hsourceBarrier (n : ℕ) (hn : 0 < n)
      (hs : (∀ i, i < n → (p n).2 ≤ (p i).2 - 1) ∧
        ∀ i, n ≤ i → (p n).1 ≤ (p i).1) :
      ∃ r, 1 ≤ r ∧
        conditionedSecondCoordinateFirstHit r p = (n : ℕ∞) ∧
          firstHitBarrier r p :=
    (successTime_iff_firstHit p n hn hstep h0).mp hs
  have hbarrierLevel_le_k (r n : ℕ) (hn : n ≤ K)
      (hr : 1 ≤ r)
      (hτr : conditionedSecondCoordinateFirstHit r p = (n : ℕ∞)) :
      r ≤ k := by
    by_contra hrk
    have hhitR :=
      (conditionedSecondCoordinateFirstHit_eq_nat_iff r n p).mp hτr
    have hlevel : (p n).2 ≤ -(k : ℤ) := by
      rw [hhitR.1]
      omega
    obtain ⟨j, hjn, hjk⟩ :=
      exists_level_hit_of_le_lastCut p k n hstep h0 hlevel
    have hjK : j = K := by
      by_contra hne
      have hjlt : j < K := by omega
      exact hKhit.2 j hjlt hjk
    have hEq : n = K := by omega
    subst n
    have heq : -(k : ℤ) = -(r : ℤ) := hKhit.1.symm.trans hhitR.1
    omega
  have hzeroMk : T mk p = 0 ↔ mk = 0 := by
    constructor
    · intro hval
      by_cases hmk0 : mk = 0
      · exact hmk0
      · have hmpos : 0 < mk := Nat.pos_of_ne_zero hmk0
        have hnot := not_isPositiveSuccessTime_zero
          (fun j => (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
            ∀ i, j ≤ i → (p j).1 ≤ (p i).1) hmpos
        have hfalse := hnot (by simpa [hval] using hT mk)
        exact False.elim hfalse
    · intro hm
      rw [hm]
      exact hzero
  refine ⟨mk, hmkLe, hmax, ?_, ?_⟩
  · intro r hr hrk
    constructor
    · intro hval
      obtain ⟨tr, _, hτrTime, _⟩ :=
        firstHit_le_bounded_level p r k K hstep h0 hrk hK
      have htrpos : 0 < tr := by
        by_contra hpos
        have htr0 : tr = 0 := by omega
        have hhit :=
          (conditionedSecondCoordinateFirstHit_eq_nat_iff r tr p).mp hτrTime
        rw [htr0, h0] at hhit
        omega
      have hmkpos : 0 < mk := by
        by_contra hnot
        have hmk0 : mk = 0 := by omega
        have hτrzero : conditionedSecondCoordinateFirstHit r p = 0 := by
          calc
            conditionedSecondCoordinateFirstHit r p = T mk p := hval.symm
            _ = 0 := by simpa [hmk0] using hzero
        have htrzero : tr = 0 := by
          have hcast : (tr : ℕ∞) = 0 := hτrTime.symm.trans hτrzero
          exact_mod_cast hcast
        omega
      obtain ⟨n, hn, hsrc, htime⟩ := hmkSource hmkpos
      have hτrn : conditionedSecondCoordinateFirstHit r p = (n : ℕ∞) :=
        hval.symm.trans htime
      refine ⟨⟨n, hτrn, fun i hi => hsrc.2 i hi⟩, ?_⟩
      intro s hrs hsk hs
      obtain ⟨j, hj, hjtime, hjle⟩ := hbarrierSuccess s (by omega) hsk hs
      obtain ⟨ts, _, hτs, _⟩ :=
        firstHit_le_bounded_level p s k K hstep h0 hsk hK
      have hlt := firstHit_level_time_lt p r s n ts hstep h0
        (by omega) hτrn hτs
      have htimeOrder : conditionedSecondCoordinateFirstHit r p <
          conditionedSecondCoordinateFirstHit s p := by
        rw [hτrn, hτs]
        exact ENat.natCast_lt_natCast.mpr hlt
      have hjmk : j ≤ mk := hmax j hjle
      by_cases hjmk' : j = mk
      · subst j
        have htimeEq : conditionedSecondCoordinateFirstHit r p =
            conditionedSecondCoordinateFirstHit s p := hval.symm.trans hjtime
        exact (ne_of_lt htimeOrder htimeEq).elim
      · have hjlt : j < mk := by omega
        have hTord := positiveSuccessTime_strictMono_of_finite
          T p hT hjlt (ne_of_lt (lt_of_le_of_lt hjle hτ)) hmkFin
        rw [hjtime, hval] at hTord
        exact (lt_asymm htimeOrder hTord).elim
    · rintro ⟨hbar, hnone⟩
      obtain ⟨j, hj, hjtime, hjle⟩ := hbarrierSuccess r hr hrk hbar
      have hjmk : j ≤ mk := hmax j hjle
      by_cases hjmk' : j = mk
      · subst j
        exact hjtime
      · have hjlt : j < mk := by omega
        obtain ⟨n, hn, hsrc, htime⟩ := hmkSource (by omega)
        obtain ⟨q, hq, hτq, hbq⟩ := hsourceBarrier n hn hsrc
        have hmkK : T mk p ≤ (K : ℕ∞) := by
          calc
            T mk p ≤ τk := hmkLe
            _ = (K : ℕ∞) := hK
        have hnK : n ≤ K := by
          apply ENat.natCast_le_natCast.mp
          calc
            (n : ℕ∞) = T mk p := htime.symm
            _ ≤ (K : ℕ∞) := hmkK
        have hqk := hbarrierLevel_le_k q n hnK hq hτq
        obtain ⟨tr, _, hτr, _⟩ :=
          firstHit_le_bounded_level p r k K hstep h0 hrk hK
        have hTord := positiveSuccessTime_strictMono_of_finite
          T p hT hjlt (ne_of_lt (lt_of_le_of_lt hjle hτ)) hmkFin
        have htrlt : tr < n := by
          have htimeOrder : conditionedSecondCoordinateFirstHit r p <
              (n : ℕ∞) := by
            calc
              conditionedSecondCoordinateFirstHit r p = T j p := hjtime.symm
              _ < T mk p := hTord
              _ = (n : ℕ∞) := htime
          rw [hτr] at htimeOrder
          exact ENat.natCast_lt_natCast.mp htimeOrder
        have hqgt : r < q := by
          by_contra hnot
          have hqr : q ≤ r := by omega
          have hle := firstHit_level_time_le p q r n tr hstep h0 hqr hτq hτr
          omega
        exact (hnone q hqgt hqk hbq).elim
  · constructor
    · intro hval
      have hmk0 := hzeroMk.mp hval
      subst mk
      intro s hs hsk hb
      obtain ⟨j, hj, _, hjle⟩ := hbarrierSuccess s hs hsk hb
      have hjmk := hmax j hjle
      omega
    · intro hnone
      by_cases hmk0 : mk = 0
      · exact hzeroMk.mpr hmk0
      · have hmkpos : 0 < mk := Nat.pos_of_ne_zero hmk0
        obtain ⟨n, hn, hsrc, htime⟩ := hmkSource hmkpos
        obtain ⟨r, hr, hτr, hbar⟩ := hsourceBarrier n hn hsrc
        have hmkK : T mk p ≤ (K : ℕ∞) := by
          calc
            T mk p ≤ τk := hmkLe
            _ = (K : ℕ∞) := hK
        have hnK : n ≤ K := by
          apply ENat.natCast_le_natCast.mp
          calc
            (n : ℕ∞) = T mk p := htime.symm
            _ ≤ (K : ℕ∞) := hmkK
        have hrk := hbarrierLevel_le_k r n hnK hr hτr
        exact (hnone r hr hrk hbar).elim

end DirectedDistances.RandomWalk
