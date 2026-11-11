/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1Window

import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Topology.UnitInterval

/-! # Billingsley modulus for càdlàg paths on a finite interval -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter TopologicalSpace
open scoped Topology

/-- A finite strictly increasing partition of `[0,T]`, with at least one block. -/
structure WindowPartition (T : ℝ) (hT : 0 < T) where
  n : ℕ
  n_pos : 0 < n
  time : Fin (n + 1) → Set.Icc (0 : ℝ) T
  first : time 0 = ⟨0, by simp [hT.le]⟩
  last : time (Fin.last n) = ⟨T, hT.le, le_rfl⟩
  strict : ∀ i : Fin n, (time i.castSucc).val < (time i.succ).val

/-- A partition is `δ`-sparse when each adjacent gap is strictly larger than `δ`.
Such partitions exist exactly when `δ < T`; hence for `δ ≥ T` there are none. -/
def WindowPartition.IsSparse {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (δ : ℝ) : Prop :=
  ∀ i : Fin p.n, δ < (p.time i.succ).val - (p.time i.castSucc).val

private def oneBlockPartition {T : ℝ} (hT : 0 < T) : WindowPartition T hT where
  n := 1
  n_pos := by norm_num
  time := fun i =>
    if hi : i.val = 0 then ⟨0, by simp [hT.le]⟩ else ⟨T, hT.le, le_rfl⟩
  first := by
    apply Subtype.ext
    simp
  last := by
    apply Subtype.ext
    simp [Fin.last]
  strict := by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    simp [hT]

/-- A `δ`-sparse partition of `[0,T]` exists exactly when `δ < T`.
For `δ ≥ T` the partition family is empty. -/
theorem windowPartition_sparse_nonempty_iff {T : ℝ} (hT : 0 < T) (δ : ℝ) :
    Nonempty {p : WindowPartition T hT // p.IsSparse δ} ↔ δ < T := by
  constructor
  · rintro ⟨⟨p, hp⟩⟩
    let i : Fin p.n := ⟨0, p.n_pos⟩
    have hi : i.castSucc = 0 := Fin.ext rfl
    have hzero : (p.time i.castSucc).val = 0 := by
      rw [hi, p.first]
    have hgap : (p.time i.succ).val - (p.time i.castSucc).val ≤ T := by
      rw [hzero, sub_zero]
      exact (p.time i.succ).property.2
    exact lt_of_lt_of_le (hp i) hgap
  · intro hδ
    refine ⟨⟨oneBlockPartition hT, ?_⟩⟩
    intro i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    simpa [oneBlockPartition] using hδ

private noncomputable def partitionOfFinset {T : ℝ} (hT : 0 < T)
    (s : Finset (Set.Icc (0 : ℝ) T))
    (h0 : ⟨0, ⟨le_rfl, hT.le⟩⟩ ∈ s)
    (hTmem : ⟨T, hT.le, le_rfl⟩ ∈ s) : WindowPartition T hT := by
  classical
  let k := s.card
  have hzero : (⟨0, ⟨le_rfl, hT.le⟩⟩ : Set.Icc (0 : ℝ) T) ≠
      ⟨T, hT.le, le_rfl⟩ := by
    intro h
    have := congrArg Subtype.val h
    simp at this
    linarith
  have hk : 2 ≤ k := by
    dsimp [k]
    exact Finset.one_lt_card.mpr ⟨_, h0, _, hTmem, hzero⟩
  have hlen : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  let hcard : s.card = k := rfl
  refine
    { n := k - 1
      n_pos := by omega
      time := fun i => s.orderEmbOfFin hcard (Fin.cast hlen i)
      first := ?_
      last := ?_
      strict := ?_ }
  · apply Subtype.ext
    have hi : Fin.cast hlen (0 : Fin (k - 1 + 1)) = ⟨0, by omega⟩ := by
      ext
      rfl
    rw [hi, Finset.orderEmbOfFin_zero hcard (by omega)]
    apply le_antisymm
    · exact Finset.min'_le _ _ h0
    · exact (s.min' ⟨_, h0⟩).property.1
  · apply Subtype.ext
    have hi : Fin.cast hlen (Fin.last (k - 1)) =
        ⟨k - 1, by omega⟩ := by
      ext
      rfl
    rw [hi, Finset.orderEmbOfFin_last hcard (by omega)]
    apply le_antisymm
    · exact (s.max' ⟨_, hTmem⟩).property.2
    · exact Finset.le_max' _ _ hTmem
  · intro i
    apply (s.orderEmbOfFin hcard).strictMono
    change Fin.cast hlen i.castSucc < Fin.cast hlen i.succ
    simp only [Fin.lt_def, Fin.val_cast]
    exact i.castSucc_lt_succ

private theorem partitionOfFinset_time_mem {T : ℝ} (hT : 0 < T)
    (s : Finset (Set.Icc (0 : ℝ) T))
    (h0 : ⟨0, ⟨le_rfl, hT.le⟩⟩ ∈ s)
    (hTmem : ⟨T, hT.le, le_rfl⟩ ∈ s)
    (i : Fin (s.card - 1 + 1)) :
    (partitionOfFinset hT s h0 hTmem).time i ∈ s := by
  classical
  let k := s.card
  have hk : 2 ≤ k := by
    dsimp [k]
    exact Finset.one_lt_card.mpr
      ⟨_, h0, _, hTmem, by
        intro h
        have := congrArg Subtype.val h
        simp at this
        linarith⟩
  have hlen : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  let hcard : s.card = k := rfl
  change s.orderEmbOfFin hcard (Fin.cast hlen i) ∈ s
  exact Finset.orderEmbOfFin_mem s hcard (Fin.cast hlen i)

private theorem partitionOfFinset_no_between {T : ℝ} (hT : 0 < T)
    (s : Finset (Set.Icc (0 : ℝ) T))
    (h0 : ⟨0, ⟨le_rfl, hT.le⟩⟩ ∈ s)
    (hTmem : ⟨T, hT.le, le_rfl⟩ ∈ s)
    (i : Fin (s.card - 1)) (c : Set.Icc (0 : ℝ) T) (hc : c ∈ s) :
    ¬ (((partitionOfFinset hT s h0 hTmem).time i.castSucc).val < c.val ∧
      c.val < ((partitionOfFinset hT s h0 hTmem).time i.succ).val) := by
  classical
  intro hbetween
  let k := s.card
  have hk : 2 ≤ k := by
    dsimp [k]
    exact Finset.one_lt_card.mpr
      ⟨_, h0, _, hTmem, by
        intro h
        have := congrArg Subtype.val h
        simp at this
        linarith⟩
  have hlen : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  let hcard : s.card = k := rfl
  change
    (s.orderEmbOfFin hcard (Fin.cast hlen i.castSucc)).val < c.val ∧
      c.val < (s.orderEmbOfFin hcard (Fin.cast hlen i.succ)).val at hbetween
  have hc_range : c ∈ Set.range (s.orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin]
    exact hc
  obtain ⟨j, hj⟩ := hc_range
  have hjval : (s.orderEmbOfFin hcard j).val = c.val :=
    congrArg Subtype.val hj
  have hleft :
      (s.orderEmbOfFin hcard (Fin.cast hlen i.castSucc)).val <
        (s.orderEmbOfFin hcard j).val := by
    rw [hjval]
    exact hbetween.1
  have hright :
      (s.orderEmbOfFin hcard j).val <
        (s.orderEmbOfFin hcard (Fin.cast hlen i.succ)).val := by
    rw [hjval]
    exact hbetween.2
  have hleft' := (s.orderEmbOfFin hcard).lt_iff_lt.mp hleft
  have hright' := (s.orderEmbOfFin hcard).lt_iff_lt.mp hright
  simp only [Fin.lt_def, Fin.val_cast] at hleft' hright'
  simp only [Fin.val_castSucc, Fin.val_succ] at hleft' hright'
  omega

private theorem exists_grid_segment {T : ℝ} (hT : 0 < T)
    (t : ℕ → Set.Icc (0 : ℝ) T) (M : ℕ)
    (_hmono : Monotone t) (hzero : (t 0).val = 0) (hlast : (t M).val = T)
    (s : Finset (Set.Icc (0 : ℝ) T))
    (hgrid : ∀ n ≤ M, t n ∈ s)
    {a b : Set.Icc (0 : ℝ) T} (_ha : a ∈ s) (_hb : b ∈ s)
    (hab : a.val < b.val)
    (hadj : ∀ c ∈ s, ¬ ((a.val < c.val) ∧ (c.val < b.val))) :
    ∃ n, n < M ∧ t n ≤ a ∧ b ≤ t (n + 1) := by
  have hbpos : 0 < b.val := lt_of_le_of_lt a.property.1 hab
  have hMpos : 0 < M := by
    by_contra hM
    have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM
    subst M
    have hz : (t 0).val = T := hlast
    rw [hzero] at hz
    linarith
  let q : Finset (Fin (M + 1)) :=
    Finset.univ.filter fun j => (t j.val).val < b.val
  have hq : q.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hzero]
    exact hbpos
  let j := q.max' hq
  have hjq : j ∈ q := Finset.max'_mem q hq
  have hjlt : (t j.val).val < b.val := by
    simpa only [q, Finset.mem_filter, Finset.mem_univ, true_and] using hjq
  have hjltM : j.val < M := by
    by_contra hnot
    have heq : j.val = M := by omega
    have hlt : (t M).val < b.val := by simpa [heq] using hjlt
    rw [hlast] at hlt
    exact (not_lt_of_ge b.property.2) hlt
  have hnext : b.val ≤ (t (j.val + 1)).val := by
    by_contra hnot
    have hklt : j.val + 1 < M + 1 := by omega
    let k : Fin (M + 1) := ⟨j.val + 1, hklt⟩
    have hkq : k ∈ q := by
      simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_not_ge hnot
    have hkj : k ≤ j := by
      have := Finset.le_max' q k hkq
      simpa only [j] using this
    change j.val + 1 ≤ j.val at hkj
    omega
  have hjmem : t j.val ∈ s := hgrid j.val (by omega)
  have hja : t j.val ≤ a := by
    by_contra hnot
    have hlt : a.val < (t j.val).val := lt_of_not_ge hnot
    exact (hadj (t j.val) hjmem) ⟨hlt, hjlt⟩
  exact ⟨j.val, hjltM, hja, hnext⟩

private theorem cadlag_near_oscillation {T : ℝ} (_hT : 0 < T)
    (f : CadlagWindow T) (ε : ℝ) (hε : 0 < ε)
    (x : Set.Icc (0 : ℝ) T) :
    ∃ r > 0, ∀ y z : Set.Icc (0 : ℝ) T,
      dist y x < r → dist z x < r →
        ((x ≤ y ∧ x ≤ z → |f.1 y - f.1 z| < ε) ∧
          (y < x ∧ z < x → |f.1 y - f.1 z| < ε)) := by
  have hright := (Metric.continuousWithinAt_iff).mp (f.2.isRightContinuous x)
  obtain ⟨rR, hrR, hright⟩ := hright (ε / 2) (by positivity)
  have hleft := f.2.tendsto_nhdsLT_leftLim x
  rw [Metric.tendsto_nhdsWithin_nhds] at hleft
  obtain ⟨rL, hrL, hleft⟩ := hleft (ε / 2) (by positivity)
  refine ⟨min rR rL, lt_min hrR hrL, ?_⟩
  intro y z hy hz
  constructor
  · intro hyz
    have hyR : dist y x < rR := lt_of_lt_of_le hy (min_le_left _ _)
    have hzR : dist z x < rR := lt_of_lt_of_le hz (min_le_left _ _)
    have hyf : |f.1 y - f.1 x| < ε / 2 := by
      rcases lt_or_eq_of_le hyz.1 with h | h
      · simpa only [Real.dist_eq] using hright h hyR
      · subst y
        simpa using (by positivity : 0 < ε / 2)
    have hzf : |f.1 z - f.1 x| < ε / 2 := by
      rcases lt_or_eq_of_le hyz.2 with h | h
      · simpa only [Real.dist_eq] using hright h hzR
      · subst z
        simpa using (by positivity : 0 < ε / 2)
    calc
      |f.1 y - f.1 z| ≤ |f.1 y - f.1 x| + |f.1 x - f.1 z| :=
        abs_sub_le _ _ _
      _ < ε := by
        rw [abs_sub_comm (f.1 x) (f.1 z)]
        linarith [add_lt_add hyf hzf]
  · intro hyz
    have hyL : dist y x < rL := lt_of_lt_of_le hy (min_le_right _ _)
    have hzL : dist z x < rL := lt_of_lt_of_le hz (min_le_right _ _)
    have hyf := hleft hyz.1 hyL
    have hzf := hleft hyz.2 hzL
    have hyf' : |f.1 y - f.1.leftLim x| < ε / 2 := by
      simpa only [Real.dist_eq] using hyf
    have hzf' : |f.1 z - f.1.leftLim x| < ε / 2 := by
      simpa only [Real.dist_eq] using hzf
    calc
      |f.1 y - f.1 z| ≤
          |f.1 y - f.1.leftLim x| + |f.1.leftLim x - f.1 z| :=
        abs_sub_le _ _ _
      _ < ε := by
        rw [abs_sub_comm (f.1.leftLim x) (f.1 z)]
        linarith [add_lt_add hyf' hzf']

/-- Oscillation of a path on the half-open block `[a,b)`, defined as the real supremum
of all pairwise absolute differences on that block. If `b.val ≤ a.val`, the defining
set is empty, so its `sSup` is `0`. -/
noncomputable def blockOscillation {T : ℝ}
    (f : CadlagWindow T)
    (a b : Set.Icc (0 : ℝ) T) : ℝ :=
  sSup {r : ℝ | ∃ s t : Set.Icc (0 : ℝ) T,
    a.val ≤ s.val ∧ s.val < b.val ∧ a.val ≤ t.val ∧ t.val < b.val ∧
      r = |f.1 s - f.1 t|}

/-- Empty-block convention for `blockOscillation`, a helper for E-STABLE / -/
theorem blockOscillation_eq_zero_of_le {T : ℝ}
    (f : CadlagWindow T) (a b : Set.Icc (0 : ℝ) T) (h : b.val ≤ a.val) :
    blockOscillation f a b = 0 := by
  unfold blockOscillation
  have hempty : {r : ℝ | ∃ s t : Set.Icc (0 : ℝ) T,
      a.val ≤ s.val ∧ s.val < b.val ∧ a.val ≤ t.val ∧ t.val < b.val ∧
        r = |f.1 s - f.1 t|} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hr
    rcases hr with ⟨s, t, has, hsb, _, _, _⟩
    exact (not_lt_of_ge h) (lt_of_le_of_lt has hsb)
  rw [hempty, Real.sSup_empty]

/-- The values whose supremum defines the oscillation on a block are bounded, because
càdlàg paths map the compact window to a bounded set. -/
theorem blockOscillation_values_bddAbove {T : ℝ}
    (f : CadlagWindow T) (a b : Set.Icc (0 : ℝ) T) :
    BddAbove {r : ℝ | ∃ s t : Set.Icc (0 : ℝ) T,
      a.val ≤ s.val ∧ s.val < b.val ∧ a.val ≤ t.val ∧ t.val < b.val ∧
        r = |f.1 s - f.1 t|} := by
  classical
  have hcompact : IsCompact (Set.univ : Set (Set.Icc (0 : ℝ) T)) :=
    isCompact_iff_isCompact_univ.mp isCompact_Icc
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
    (isBounded_image_of_isCadlag_of_isCompact f.2 hcompact)
  refine ⟨2 * C, ?_⟩
  rintro r ⟨s, t, hs, hsb, ht, htb, rfl⟩
  have hsC : |f.1 s| ≤ C := by
    have hsball : f.1 s ∈ Metric.closedBall 0 C :=
      hC ⟨s, Set.mem_univ s, rfl⟩
    simpa [Metric.mem_closedBall, Real.dist_eq] using hsball
  have htC : |f.1 t| ≤ C := by
    have htball : f.1 t ∈ Metric.closedBall 0 C :=
      hC ⟨t, Set.mem_univ t, rfl⟩
    simpa [Metric.mem_closedBall, Real.dist_eq] using htball
  calc
    |f.1 s - f.1 t| = |f.1 s + -f.1 t| := rfl
    _ ≤ |f.1 s| + |-f.1 t| := abs_add_le _ _
    _ = |f.1 s| + |f.1 t| := by simp
    _ ≤ C + C := add_le_add hsC htC
    _ = 2 * C := by rw [two_mul]

/-- A càdlàg path has a finite partition with arbitrarily small oscillation on
each half-open block. This is Billingsley, *Convergence of Probability Measures*,
2nd ed., Lemma 12.1; this helper is not the paper result. -/
theorem exists_partition_oscillation_lt {T : ℝ} (hT : 0 < T)
    (f : CadlagWindow T) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : WindowPartition T hT,
      ∀ i : Fin p.n,
        blockOscillation f (p.time i.castSucc) (p.time i.succ) < ε := by
  classical
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let rad : Set.Icc (0 : ℝ) T → ℝ := fun x =>
    Classical.choose (cadlag_near_oscillation hT f η hη x)
  have hrad (x : Set.Icc (0 : ℝ) T) : 0 < rad x :=
    (Classical.choose_spec (cadlag_near_oscillation hT f η hη x)).1
  have hnear (x : Set.Icc (0 : ℝ) T) :
      ∀ y z : Set.Icc (0 : ℝ) T,
        dist y x < rad x → dist z x < rad x →
          ((x ≤ y ∧ x ≤ z → |f.1 y - f.1 z| < η) ∧
            (y < x ∧ z < x → |f.1 y - f.1 z| < η)) :=
    (Classical.choose_spec (cadlag_near_oscillation hT f η hη x)).2
  have hopen (x : Set.Icc (0 : ℝ) T) :
      IsOpen (Metric.ball x (rad x)) := Metric.isOpen_ball
  have hcover :
      (Set.univ : Set (Set.Icc (0 : ℝ) T)) ⊆
        ⋃ x : Set.Icc (0 : ℝ) T, Metric.ball x (rad x) := by
    intro x _
    simp only [Set.mem_iUnion]
    exact ⟨x, Metric.mem_ball_self (hrad x)⟩
  obtain ⟨t, ht0, hmono, hfinish, hinterval⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hT.le
      (c := fun x : Set.Icc (0 : ℝ) T => Metric.ball x (rad x))
      hopen hcover
  obtain ⟨M, hM⟩ := hfinish
  have htlast : (t M).val = T := hM M le_rfl
  let center (n : ℕ) : Set.Icc (0 : ℝ) T := Classical.choose (hinterval n)
  have hcenter (n : ℕ) :
      Set.Icc (t n) (t (n + 1)) ⊆ Metric.ball (center n) (rad (center n)) :=
    Classical.choose_spec (hinterval n)
  let grid : Finset (Set.Icc (0 : ℝ) T) :=
    Finset.univ.image fun i : Fin (M + 1) => t i.val
  let centers : Finset (Set.Icc (0 : ℝ) T) :=
    Finset.univ.image fun i : Fin (M + 1) => center i.val
  let s := grid ∪ centers
  have hgrid (n : ℕ) (hn : n ≤ M) : t n ∈ s := by
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    refine ⟨⟨n, by omega⟩, Finset.mem_univ _, rfl⟩
  have hzero : t 0 = ⟨0, ⟨le_rfl, hT.le⟩⟩ := by
    apply Subtype.ext
    exact ht0
  have hlast : t M = ⟨T, hT.le, le_rfl⟩ := by
    apply Subtype.ext
    exact htlast
  have h0s : (⟨0, ⟨le_rfl, hT.le⟩⟩ : Set.Icc (0 : ℝ) T) ∈ s := by
    simpa only [hzero] using hgrid 0 (by omega)
  have hTs : (⟨T, hT.le, le_rfl⟩ : Set.Icc (0 : ℝ) T) ∈ s := by
    simpa only [hlast] using hgrid M le_rfl
  let p := partitionOfFinset hT s h0s hTs
  refine ⟨p, ?_⟩
  intro i
  let a := p.time i.castSucc
  let b := p.time i.succ
  have haS : a ∈ s := by
    exact partitionOfFinset_time_mem hT s h0s hTs i.castSucc
  have hbS : b ∈ s := by
    exact partitionOfFinset_time_mem hT s h0s hTs i.succ
  have hadj : ∀ c ∈ s, ¬ ((a.val < c.val) ∧ (c.val < b.val)) := by
    intro c hc
    exact partitionOfFinset_no_between hT s h0s hTs i c hc
  obtain ⟨n, hnM, hna, hbn⟩ :=
    exists_grid_segment hT t M hmono ht0 htlast s hgrid haS hbS
      (p.strict i) hadj
  have hcenterS : center n ∈ s := by
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨⟨n, by omega⟩, Finset.mem_univ _, rfl⟩
  have hside : center n ≤ a ∨ b ≤ center n := by
    by_cases hca : center n ≤ a
    · exact Or.inl hca
    · right
      apply le_of_not_gt
      intro hcb
      exact hadj (center n) hcenterS
        ⟨lt_of_not_ge hca, hcb⟩
  have hsmall {y z : Set.Icc (0 : ℝ) T}
      (hay : a.val ≤ y.val) (hyb : y.val < b.val)
      (haz : a.val ≤ z.val) (hzb : z.val < b.val) :
      |f.1 y - f.1 z| < η := by
    have hyIcc : y ∈ Set.Icc (t n) (t (n + 1)) := by
      constructor
      · change t n ≤ y
        exact hna.trans (show a ≤ y by exact hay)
      · change y ≤ t (n + 1)
        exact (show y ≤ b by exact le_of_lt hyb).trans hbn
    have hzIcc : z ∈ Set.Icc (t n) (t (n + 1)) := by
      constructor
      · change t n ≤ z
        exact hna.trans (show a ≤ z by exact haz)
      · change z ≤ t (n + 1)
        exact (show z ≤ b by exact le_of_lt hzb).trans hbn
    have hyball : dist y (center n) < rad (center n) :=
      Metric.mem_ball.mp (hcenter n hyIcc)
    have hzball : dist z (center n) < rad (center n) :=
      Metric.mem_ball.mp (hcenter n hzIcc)
    rcases hside with hleft | hright
    · exact (hnear (center n) y z hyball hzball).1
        ⟨hleft.trans (show a ≤ y by exact hay),
          hleft.trans (show a ≤ z by exact haz)⟩
    · exact (hnear (center n) y z hyball hzball).2
        ⟨lt_of_lt_of_le hyb hright, lt_of_lt_of_le hzb hright⟩
  have hnonempty :
      {r : ℝ | ∃ y z : Set.Icc (0 : ℝ) T,
        a.val ≤ y.val ∧ y.val < b.val ∧ a.val ≤ z.val ∧ z.val < b.val ∧
          r = |f.1 y - f.1 z|}.Nonempty := by
    refine ⟨0, a, a, le_rfl, p.strict i, le_rfl, p.strict i, ?_⟩
    simp
  have hsup :
      sSup {r : ℝ | ∃ y z : Set.Icc (0 : ℝ) T,
        a.val ≤ y.val ∧ y.val < b.val ∧ a.val ≤ z.val ∧ z.val < b.val ∧
          r = |f.1 y - f.1 z|} ≤ η := by
    apply csSup_le hnonempty
    rintro r ⟨y, z, hay, hyb, haz, hzb, rfl⟩
    exact (hsmall hay hyb haz hzb).le
  change sSup {r : ℝ | ∃ y z : Set.Icc (0 : ℝ) T,
      a.val ≤ y.val ∧ y.val < b.val ∧ a.val ≤ z.val ∧ z.val < b.val ∧
        r = |f.1 y - f.1 z|} < ε
  exact lt_of_le_of_lt hsup (by dsimp [η]; linarith)





noncomputable def cadlagModulus {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) (δ : ℝ) : ℝ :=
  if _h : δ < T then
    sInf (Set.range fun p : {p : WindowPartition T hT // p.IsSparse δ} =>
      sSup (Set.range fun i : Fin p.1.n =>
        blockOscillation f (p.1.time i.castSucc) (p.1.time i.succ)))
  else 0

private theorem blockOscillation_nonneg {T : ℝ} (f : CadlagWindow T)
    (a b : Set.Icc (0 : ℝ) T) (hab : a.val < b.val) :
    0 ≤ blockOscillation f a b := by
  unfold blockOscillation
  apply le_csSup (blockOscillation_values_bddAbove f a b)
  refine ⟨a, a, le_rfl, hab, le_rfl, hab, ?_⟩
  simp

private theorem partitionOscillation_nonneg {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) (p : WindowPartition T hT) :
    0 ≤ sSup (Set.range fun i : Fin p.n =>
      blockOscillation f (p.time i.castSucc) (p.time i.succ)) := by
  let i : Fin p.n := ⟨0, p.n_pos⟩
  have hblock : 0 ≤ blockOscillation f (p.time i.castSucc) (p.time i.succ) :=
    blockOscillation_nonneg f _ _ (p.strict i)
  have hle : blockOscillation f (p.time i.castSucc) (p.time i.succ) ≤
      sSup (Set.range fun j : Fin p.n =>
        blockOscillation f (p.time j.castSucc) (p.time j.succ)) :=
    le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
  exact hblock.trans hle

private theorem cadlagModulus_values_bddBelow {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) (δ : ℝ) :
    BddBelow (Set.range fun p : {p : WindowPartition T hT // p.IsSparse δ} =>
      sSup (Set.range fun i : Fin p.1.n =>
        blockOscillation f (p.1.time i.castSucc) (p.1.time i.succ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨p, rfl⟩
  exact partitionOscillation_nonneg f p.1

/-- Billingsley's càdlàg modulus is monotone in the sparsity scale below the window size. -/
theorem cadlagModulus_mono {T : ℝ} {hT : 0 < T} (f : CadlagWindow T)
    {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) (hδT : δ₂ < T) :
    cadlagModulus (hT := hT) f δ₁ ≤ cadlagModulus (hT := hT) f δ₂ := by
  have hδ₁T : δ₁ < T := lt_of_le_of_lt hδ hδT
  simp only [cadlagModulus, dite_eq_left hδ₁T, dite_eq_left hδT]
  apply csInf_le_csInf (cadlagModulus_values_bddBelow f δ₁)
  · obtain ⟨p⟩ := (windowPartition_sparse_nonempty_iff hT δ₂).2 hδT
    exact ⟨_, ⟨p, rfl⟩⟩
  · rintro x ⟨p, rfl⟩
    exact ⟨⟨p.1, fun i => lt_of_le_of_lt hδ (p.2 i)⟩, rfl⟩

/-- The modulus is zero at scales at least the window length, where its sparse
partition family is empty by convention. -/
theorem cadlagModulus_eq_zero_of_le {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) {δ : ℝ} (hδ : T ≤ δ) :
    cadlagModulus (hT := hT) f δ = 0 := by
  simp [cadlagModulus, not_lt_of_ge hδ]

private theorem cadlagModulus_nonneg {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) (δ : ℝ) : 0 ≤ cadlagModulus (hT := hT) f δ := by
  by_cases hδ : δ < T
  · unfold cadlagModulus
    rw [dite_eq_left hδ]
    have hne : (Set.range fun p : {p : WindowPartition T hT // p.IsSparse δ} =>
        sSup (Set.range fun i : Fin p.1.n =>
          blockOscillation f (p.1.time i.castSucc) (p.1.time i.succ))).Nonempty := by
      obtain ⟨p⟩ := (windowPartition_sparse_nonempty_iff hT δ).2 hδ
      exact ⟨_, ⟨p, rfl⟩⟩
    apply le_csInf hne
    rintro x ⟨p, rfl⟩
    exact partitionOscillation_nonneg f p.1
  · simp [cadlagModulus, hδ]

/-- Billingsley's càdlàg modulus tends to zero as the positive sparsity scale
tends to zero; this is a pathwise helper, not the paper's functional limit. -/
theorem cadlagModulus_tendsto_zero {T : ℝ} (hT : 0 < T)
    (f : CadlagWindow T) :
    Tendsto (fun δ : ℝ => cadlagModulus (hT := hT) f δ)
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨p, hp⟩ := exists_partition_oscillation_lt hT f hη
  let gap : Fin p.n → ℝ := fun i =>
    (p.time i.succ).val - (p.time i.castSucc).val
  let gaps : Finset ℝ := Finset.univ.image gap
  have hgaps : gaps.Nonempty := by
    refine ⟨gap ⟨0, p.n_pos⟩, ?_⟩
    exact Finset.mem_image.mpr
      ⟨⟨0, p.n_pos⟩, Finset.mem_univ _, rfl⟩
  let γ := gaps.min' hgaps
  have hγpos : 0 < γ := by
    obtain ⟨i, _, hgap⟩ := Finset.mem_image.mp (Finset.min'_mem gaps hgaps)
    change 0 < gaps.min' hgaps
    rw [← hgap]
    exact sub_pos.mpr (p.strict i)
  have hγle (i : Fin p.n) : γ ≤ gap i := by
    exact Finset.min'_le gaps (gap i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let ρ := min γ T
  have hρ : 0 < ρ := by dsimp [ρ]; exact lt_min hγpos hT
  have hsup :
      sSup (Set.range fun i : Fin p.n =>
        blockOscillation f (p.time i.castSucc) (p.time i.succ)) ≤ η := by
    apply csSup_le
    · exact ⟨_, ⟨⟨0, p.n_pos⟩, rfl⟩⟩
    · rintro x ⟨i, rfl⟩
      exact (hp i).le
  refine ⟨ρ, hρ, ?_⟩
  intro δ _hδpos hδ
  have habs : |δ| < ρ := by simpa [Real.dist_eq] using hδ
  have hδρ : δ < ρ := lt_of_le_of_lt (le_abs_self δ) habs
  have hδT : δ < T := lt_of_lt_of_le hδρ (min_le_right _ _)
  have hδγ : δ < γ := lt_of_lt_of_le hδρ (min_le_left _ _)
  have hsparse : p.IsSparse δ := by
    intro i
    exact lt_of_lt_of_le hδγ (hγle i)
  have hupper : cadlagModulus (hT := hT) f δ < ε := by
    calc
      cadlagModulus (hT := hT) f δ ≤
          sSup (Set.range fun i : Fin p.n =>
            blockOscillation f (p.time i.castSucc) (p.time i.succ)) := by
        unfold cadlagModulus
        rw [dite_eq_left hδT]
        exact csInf_le (cadlagModulus_values_bddBelow f δ)
          ⟨⟨p, hsparse⟩, rfl⟩
      _ ≤ η := hsup
      _ < ε := by dsimp [η]; linarith
  have hnonneg := cadlagModulus_nonneg (hT := hT) f δ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hupper

end DirectedDistances.Probability
