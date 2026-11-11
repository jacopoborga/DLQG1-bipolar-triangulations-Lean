/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PermutationSplit

/-! # Orbit classes after splitting one permutation cycle

This module records the two new orbits, unchanged orbits away from the splice,
and the resulting orbit-count increase (`sec-kmsw`, -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

/-- The first successor-swapped orbit: the point `a`, followed by powers after -/
@[expose] def rightSwapCycle0 (f : Equiv.Perm D) (a : D) (k m : ℕ) : Set D :=
  {x | x = a ∨ ∃ i, k + 1 ≤ i ∧ i < m ∧ (f ^ i) a = x}

/-- The second successor-swapped orbit: powers from one through the cut index -/
@[expose] def rightSwapCycle1 (f : Equiv.Perm D) (a : D) (k : ℕ) : Set D :=
  {x | ∃ i, 1 ≤ i ∧ i ≤ k ∧ (f ^ i) a = x}

private theorem split_pow_injective (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {i j : ℕ}
    (hi : i < (f.cycleOf a).support.card)
    (hj : j < (f.cycleOf a).support.card)
    (hpow : (f ^ i) a = (f ^ j) a) : i = j := by
  have hfa : f a ≠ a := by
    intro hfix
    exact hab (hs.eq_of_left hfix)
  have ha : a ∈ f.support := by
    rw [Equiv.Perm.mem_support]
    exact hfa
  have hca : a ∈ (f.cycleOf a).support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff' hfa]
  exact (f.isCycleOn_support_cycleOf a).injOn_pow_apply hca hi hj hpow

private theorem splitCycle0_excludes_b (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (_hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) : b ∉ rightSwapCycle0 f a k (f.cycleOf a).support.card := by
  intro hb0
  rcases hb0 with hba | ⟨i, hik, him, hix⟩
  · exact hab hba.symm
  · have hik' := split_pow_injective f hab hs him hkm (hix.trans hb.symm)
    omega

omit [Fintype D] [DecidableEq D] in
private theorem splitCycle1_subset_oldOrbit (f : Equiv.Perm D) (a : D) {k : ℕ}
    {x : D} (hx : x ∈ rightSwapCycle1 f a k) : f.SameCycle a x := by
  rcases hx with ⟨i, _, _, hix⟩
  rw [← hix]
  exact (Equiv.Perm.sameCycle_pow_right (f := f) (x := a) (y := a) (n := i)).2
    Equiv.Perm.SameCycle.rfl

private theorem splitCycle0_subset_oldOrbit (f : Equiv.Perm D) (a : D) {k : ℕ}
    {x : D} (hx : x ∈ rightSwapCycle0 f a k (f.cycleOf a).support.card) :
    f.SameCycle a x := by
  rcases hx with hxa | ⟨i, _, _, hix⟩
  · subst x
    exact Equiv.Perm.SameCycle.rfl
  · rw [← hix]
    exact (Equiv.Perm.sameCycle_pow_right (f := f) (x := a) (y := a) (n := i)).2
      Equiv.Perm.SameCycle.rfl

private theorem rightSwapCycle0_apply_closed (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (_hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) {x : D}
    (hx : x ∈ rightSwapCycle0 f a k (f.cycleOf a).support.card) :
    (f * Equiv.swap a b) x ∈ rightSwapCycle0 f a k (f.cycleOf a).support.card := by
  let g := f * Equiv.swap a b
  change x = a ∨ ∃ i, k + 1 ≤ i ∧ i < (f.cycleOf a).support.card ∧ (f ^ i) a = x at hx
  change g x = a ∨ ∃ i, k + 1 ≤ i ∧ i < (f.cycleOf a).support.card ∧ (f ^ i) a = g x
  rcases hx with hxa | ⟨i, hik, him, hix⟩
  · subst x
    have hga : g a = (f ^ (k + 1)) a := rightSwap_apply_a_of_pow f a b k hb
    by_cases hkend : k + 1 = (f.cycleOf a).support.card
    · left
      rw [hga, hkend, sameCycle_split_period]
    · right
      refine ⟨k + 1, by omega, by omega, ?_⟩
      exact hga.symm
  · subst x
    have hia : (f ^ i) a ≠ a := by
      intro heq
      have hmpos : 0 < (f.cycleOf a).support.card := by omega
      have hi0 := split_pow_injective f hab hs him hmpos (by simpa using heq)
      omega
    have hib : (f ^ i) a ≠ b := by
      intro heq
      have hik' := split_pow_injective f hab hs him hkm (heq.trans hb.symm)
      omega
    have hsucc : g ((f ^ i) a) = (f ^ (i + 1)) a := by
      change (f * Equiv.swap a b) ((f ^ i) a) = _
      rw [rightSwap_apply_of_ne f hia hib]
      simp only [pow_succ', Equiv.Perm.mul_apply]
    by_cases hiend : i + 1 = (f.cycleOf a).support.card
    · left
      rw [hsucc, hiend, sameCycle_split_period]
    · right
      refine ⟨i + 1, by omega, by omega, hsucc.symm⟩

private theorem rightSwapCycle1_apply_closed (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (_hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) {x : D}
    (hx : x ∈ rightSwapCycle1 f a k) :
    (f * Equiv.swap a b) x ∈ rightSwapCycle1 f a k := by
  let g := f * Equiv.swap a b
  change (∃ i, 1 ≤ i ∧ i ≤ k ∧ (f ^ i) a = x) at hx
  change ∃ i, 1 ≤ i ∧ i ≤ k ∧ (f ^ i) a = g x
  obtain ⟨i, hi, hik, hix⟩ := hx
  subst x
  by_cases hik' : i = k
  · subst i
    rw [hb, rightSwap_apply_b]
    exact ⟨1, by omega, by omega, rfl⟩
  · have hiklt : i < k := by omega
    have him : i < (f.cycleOf a).support.card := by omega
    have hia : (f ^ i) a ≠ a := by
      intro heq
      have hmpos : 0 < (f.cycleOf a).support.card := by omega
      have hi0 := split_pow_injective f hab hs him hmpos (by simpa using heq)
      omega
    have hib : (f ^ i) a ≠ b := by
      intro heq
      have hi0 := split_pow_injective f hab hs him hkm (heq.trans hb.symm)
      omega
    rw [rightSwap_apply_of_ne f hia hib]
    refine ⟨i + 1, by omega, by omega, ?_⟩
    simp only [pow_succ', Equiv.Perm.mul_apply]

private theorem rightSwapCycle0_reachable (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (_hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) {i : ℕ}
    (hik : k + 1 ≤ i) (him : i < (f.cycleOf a).support.card) :
    (f * Equiv.swap a b).SameCycle a ((f ^ i) a) := by
  let g := f * Equiv.swap a b
  have hstart : g.SameCycle a ((f ^ (k + 1)) a) := by
    exact ⟨1, rightSwap_apply_a_of_pow f a b k hb⟩
  have hsteps : ∀ j, k + 1 ≤ j → j < (f.cycleOf a).support.card →
      g.SameCycle a ((f ^ j) a) := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj hjm
      by_cases hjbase : j + 1 = k + 1
      · rw [hjbase]
        exact hstart
      · have hjlow : k + 1 ≤ j := by omega
        have hjlt : j < (f.cycleOf a).support.card := by omega
        have hprev := ih hjlow hjlt
        have hja : (f ^ j) a ≠ a := by
          intro heq
          have hmpos : 0 < (f.cycleOf a).support.card := by omega
          have hidx := split_pow_injective f hab hs hjlt hmpos (by simpa using heq)
          omega
        have hjb : (f ^ j) a ≠ b := by
          intro heq
          have hidx := split_pow_injective f hab hs hjlt hkm (heq.trans hb.symm)
          omega
        have hstep : g.SameCycle ((f ^ j) a) ((f ^ (j + 1)) a) := by
          have hstepEq : g ((f ^ j) a) = (f ^ (j + 1)) a := by
            change (f * Equiv.swap a b) ((f ^ j) a) = _
            rw [rightSwap_apply_of_ne f hja hjb]
            simp only [pow_succ', Equiv.Perm.mul_apply]
          exact ⟨1, by simpa [g] using hstepEq⟩
        exact hprev.trans hstep
  exact hsteps i hik him

private theorem rightSwapCycle1_reachable (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (_hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) {i : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) :
    (f * Equiv.swap a b).SameCycle b ((f ^ i) a) := by
  let g := f * Equiv.swap a b
  have hstart : g.SameCycle b ((f ^ 1) a) := by
    exact ⟨1, by simp [g, rightSwap_apply_b]⟩
  have hsteps : ∀ j, 1 ≤ j → j ≤ k → g.SameCycle b ((f ^ j) a) := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj hjk
      by_cases hjbase : j + 1 = 1
      · rw [hjbase]
        exact hstart
      · have hjpos : 1 ≤ j := by omega
        have hjle : j ≤ k := by omega
        have hjlt : j < k := by omega
        have hjm : j < (f.cycleOf a).support.card := by omega
        have hprev := ih hjpos hjle
        have hja : (f ^ j) a ≠ a := by
          intro heq
          have hmpos : 0 < (f.cycleOf a).support.card := by omega
          have hidx := split_pow_injective f hab hs hjm hmpos (by simpa using heq)
          omega
        have hjb : (f ^ j) a ≠ b := by
          intro heq
          have hidx := split_pow_injective f hab hs hjm hkm (heq.trans hb.symm)
          omega
        have hstep : g.SameCycle ((f ^ j) a) ((f ^ (j + 1)) a) := by
          have hstepEq : g ((f ^ j) a) = (f ^ (j + 1)) a := by
            change (f * Equiv.swap a b) ((f ^ j) a) = _
            rw [rightSwap_apply_of_ne f hja hjb]
            simp only [pow_succ', Equiv.Perm.mul_apply]
          exact ⟨1, by simpa [g] using hstepEq⟩
        exact hprev.trans hstep
  exact hsteps i hi hik

/-- The two successor-swapped power ranges are disjoint, including singleton -/
theorem rightSwapCycles_disjoint (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (_hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (_hb : (f ^ k) a = b) :
    Disjoint (rightSwapCycle0 f a k (f.cycleOf a).support.card)
      (rightSwapCycle1 f a k) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  change x = a ∨ ∃ i, k + 1 ≤ i ∧ i < (f.cycleOf a).support.card ∧ (f ^ i) a = x at hx0
  change ∃ j, 1 ≤ j ∧ j ≤ k ∧ (f ^ j) a = x at hx1
  rcases hx0 with hxa | ⟨i, hik, him, hix⟩
  · rcases hx1 with ⟨j, hj, hjk, hjx⟩
    have hmpos : 0 < (f.cycleOf a).support.card := by omega
    have hpow : (f ^ j) a = (f ^ 0) a := by simpa [hxa] using hjx
    have hij := split_pow_injective f hab hs (i := j) (j := 0) (by omega) hmpos hpow
    omega
  · rcases hx1 with ⟨j, hj, hjk, hjx⟩
    have hij := split_pow_injective f hab hs him (by omega) (hix.trans hjx.symm)
    omega

/-- Both successor-swapped power ranges are nonempty (`sec-kmsw`, -/
theorem rightSwapCycles_nonempty (f : Equiv.Perm D) {a b : D}
    (_hab : a ≠ b) (_hs : f.SameCycle a b) {k : ℕ}
    (hk : 1 ≤ k) (_hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) :
    (rightSwapCycle0 f a k (f.cycleOf a).support.card).Nonempty ∧
      (rightSwapCycle1 f a k).Nonempty := by
  constructor
  · exact ⟨a, Or.inl rfl⟩
  · exact ⟨b, ⟨k, hk, le_rfl, hb⟩⟩

private theorem rightSwap_a_sameCycle_iff_cycle0 (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) (x : D) :
    (f * Equiv.swap a b).SameCycle a x ↔
      x ∈ rightSwapCycle0 f a k (f.cycleOf a).support.card := by
  let g := f * Equiv.swap a b
  constructor
  · intro h
    obtain ⟨n, hpow⟩ := h.exists_nat_pow_eq
    have hclosed : ∀ n, (g ^ n) a ∈ rightSwapCycle0 f a k (f.cycleOf a).support.card := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        have hstep := rightSwapCycle0_apply_closed f hab hs hk hkm hb ih
        simpa only [g, pow_succ', Equiv.Perm.mul_apply] using hstep
    exact hpow ▸ hclosed n
  · intro hx
    change x = a ∨ ∃ i, k + 1 ≤ i ∧ i < (f.cycleOf a).support.card ∧ (f ^ i) a = x at hx
    rcases hx with hxa | ⟨i, hik, him, hix⟩
    · subst x
      exact Equiv.Perm.SameCycle.rfl
    · subst x
      exact rightSwapCycle0_reachable f hab hs hk hkm hb hik him

private theorem rightSwap_b_sameCycle_iff_cycle1 (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) (x : D) :
    (f * Equiv.swap a b).SameCycle b x ↔ x ∈ rightSwapCycle1 f a k := by
  let g := f * Equiv.swap a b
  constructor
  · intro h
    obtain ⟨n, hpow⟩ := h.exists_nat_pow_eq
    have hclosed : ∀ n, (g ^ n) b ∈ rightSwapCycle1 f a k := by
      intro n
      induction n with
      | zero => exact ⟨k, hk, le_rfl, hb⟩
      | succ n ih =>
        have hstep := rightSwapCycle1_apply_closed f hab hs hk hkm hb ih
        simpa only [g, pow_succ', Equiv.Perm.mul_apply] using hstep
    exact hpow ▸ hclosed n
  · intro hx
    change ∃ i, 1 ≤ i ∧ i ≤ k ∧ (f ^ i) a = x at hx
    obtain ⟨i, hi, hik, hix⟩ := hx
    subst x
    exact rightSwapCycle1_reachable f hab hs hk hkm hb hi hik

/-- On the old orbit of `a`, the orbit of `a` after the successor swap is the -/
theorem rightSwap_sameCycle_a_iff (f : Equiv.Perm D) {a b x : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) (_hx : f.SameCycle a x) :
    (f * Equiv.swap a b).SameCycle a x ↔
      x = a ∨ ∃ i, k + 1 ≤ i ∧ i < (f.cycleOf a).support.card ∧ (f ^ i) a = x := by
  have hclass := rightSwap_a_sameCycle_iff_cycle0 f hab hs hk hkm hb x
  change (f * Equiv.swap a b).SameCycle a x ↔ x ∈
    rightSwapCycle0 f a k (f.cycleOf a).support.card at hclass
  simpa [rightSwapCycle0] using hclass

/-- On the old orbit of `a`, the orbit of `b` after the successor swap is the -/
theorem rightSwap_sameCycle_b_iff (f : Equiv.Perm D) {a b x : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) {k : ℕ}
    (hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) (_hx : f.SameCycle a x) :
    (f * Equiv.swap a b).SameCycle b x ↔
      ∃ i, 1 ≤ i ∧ i ≤ k ∧ (f ^ i) a = x := by
  have hclass := rightSwap_b_sameCycle_iff_cycle1 f hab hs hk hkm hb x
  change (f * Equiv.swap a b).SameCycle b x ↔ x ∈ rightSwapCycle1 f a k at hclass
  simpa [rightSwapCycle1] using hclass

/-- If `x` and `y` lie outside the old orbit containing `a` and `b`, the
successor swap does not change whether they share an orbit (`sec-kmsw`, -/
theorem rightSwap_sameCycle_iff_of_outside (f : Equiv.Perm D) {a b x y : D}
    (hs : f.SameCycle a b)
    (hxa : ¬ f.SameCycle a x) (_hya : ¬ f.SameCycle a y) :
    (f * Equiv.swap a b).SameCycle x y ↔ f.SameCycle x y := by
  let g := f * Equiv.swap a b
  have hnot : ∀ n, ¬ f.SameCycle a ((f ^ n) x) := by
    intro n hcycle
    exact hxa ((Equiv.Perm.sameCycle_pow_right (f := f) (x := a) (y := x) (n := n)).1 hcycle)
  have hneA : ∀ n, (f ^ n) x ≠ a := by
    intro n heq
    apply hnot n
    simpa [heq] using (Equiv.Perm.SameCycle.rfl : f.SameCycle a a)
  have hneB : ∀ n, (f ^ n) x ≠ b := by
    intro n heq
    apply hnot n
    rw [heq]
    exact hs
  have hiter : ∀ n, (g ^ n) x = (f ^ n) x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      calc
        (g ^ (n + 1)) x = g ((g ^ n) x) := by simp [pow_succ']
        _ = f ((f ^ n) x) := by
          rw [ih]
          change (f * Equiv.swap a b) ((f ^ n) x) = _
          exact rightSwap_apply_of_ne f (hneA n) (hneB n)
        _ = (f ^ (n + 1)) x := by simp [pow_succ']
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast] using (hiter n).symm.trans hn
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast] using (hiter n).trans hn

noncomputable local instance orbitQuotientFintype (f : Equiv.Perm D) :
    Fintype (Quotient (Equiv.Perm.SameCycle.setoid f)) := Fintype.ofFinite _

private noncomputable def splitOrbitQuotientMap (f : Equiv.Perm D) (a b : D)
    (hs : f.SameCycle a b) (_hab : a ≠ b) (_k : ℕ)
    (_hk : 1 ≤ _k) (_hkm : _k < (f.cycleOf a).support.card)
    (_hb : (f ^ _k) a = b) :
    Quotient (Equiv.Perm.SameCycle.setoid f) →
      Quotient (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) := by
  classical
  refine Quotient.lift (fun x =>
    if f.SameCycle a x then
      Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) a
    else Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) x) ?_
  intro x y hxy
  by_cases hax : f.SameCycle a x
  · have hay : f.SameCycle a y := hax.trans hxy
    simp [hax, hay]
  · have hay : ¬ f.SameCycle a y := by
      intro h
      exact hax (h.trans hxy.symm)
    simp [hax, hay]
    apply Quotient.sound
    exact (rightSwap_sameCycle_iff_of_outside f hs hax hay).2 hxy

private theorem splitOrbitQuotientMap_mk (f : Equiv.Perm D) (a b : D)
    (hs : f.SameCycle a b) (hab : a ≠ b) (k : ℕ)
    (hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) (x : D) :
    splitOrbitQuotientMap f a b hs hab k hk hkm hb
        (Quotient.mk (Equiv.Perm.SameCycle.setoid f) x) =
      if f.SameCycle a x then
        Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) a
      else Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) x := by
  rfl

private noncomputable def splitOrbitQuotientEquiv (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) (k : ℕ)
    (hk : 1 ≤ k) (hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) :
    Quotient (Equiv.Perm.SameCycle.setoid f) ⊕ PUnit.{u + 1} ≃
      Quotient (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) := by
  classical
  let qf := Quotient (Equiv.Perm.SameCycle.setoid f)
  let qg := Quotient (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b))
  let map := splitOrbitQuotientMap f a b hs hab k hk hkm hb
  apply Equiv.ofBijective
    (fun q : qf ⊕ PUnit.{u + 1} =>
      match q with
      | Sum.inl c => map c
      | Sum.inr _ => Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) b)
  constructor
  · intro q r h
    cases q with
    | inl q =>
      cases r with
      | inl r =>
        revert h
        refine Quotient.inductionOn₂ q r ?_
        intro x y h
        by_cases hax : f.SameCycle a x
        · by_cases hay : f.SameCycle a y
          · have hxy : f.SameCycle x y := hax.symm.trans hay
            apply congrArg Sum.inl
            exact Quotient.sound hxy
          · have hxy := Quotient.exact (by
              simpa [map, splitOrbitQuotientMap_mk, hax, hay] using h)
            have hy0 := (rightSwap_a_sameCycle_iff_cycle0 f hab hs hk hkm hb y).1 hxy
            exact False.elim (hay (splitCycle0_subset_oldOrbit f a hy0))
        · by_cases hay : f.SameCycle a y
          · have hxy := Quotient.exact (by
              simpa [map, splitOrbitQuotientMap_mk, hax, hay] using h)
            have hx0 := (rightSwap_a_sameCycle_iff_cycle0 f hab hs hk hkm hb x).1 hxy.symm
            exact False.elim (hax (splitCycle0_subset_oldOrbit f a hx0))
          · have hxyg := Quotient.exact (by
              simpa [map, splitOrbitQuotientMap_mk, hax, hay] using h)
            have hxyf := (rightSwap_sameCycle_iff_of_outside f hs hax hay).1 hxyg
            apply congrArg Sum.inl
            exact Quotient.sound hxyf
      | inr u =>
        revert h
        refine Quotient.inductionOn q ?_
        intro x h
        by_cases hax : f.SameCycle a x
        · have hxab : (f * Equiv.swap a b).SameCycle a b := Quotient.exact (by
            simpa [map, splitOrbitQuotientMap_mk, hax] using h)
          have hb0 := (rightSwap_a_sameCycle_iff_cycle0 f hab hs hk hkm hb b).1 hxab
          exact False.elim (splitCycle0_excludes_b f hab hs hk hkm hb hb0)
        · have hxb : (f * Equiv.swap a b).SameCycle x b := Quotient.exact (by
            simpa [map, splitOrbitQuotientMap_mk, hax] using h)
          have hb1 := (rightSwap_b_sameCycle_iff_cycle1 f hab hs hk hkm hb x).1 hxb.symm
          exact False.elim (hax (splitCycle1_subset_oldOrbit f a hb1))
    | inr u =>
      cases r with
      | inl r =>
        revert h
        refine Quotient.inductionOn r ?_
        intro x h
        by_cases hax : f.SameCycle a x
        · have hxab : (f * Equiv.swap a b).SameCycle a b := Quotient.exact (by
            simpa [map, splitOrbitQuotientMap_mk, hax] using h.symm)
          have hb0 := (rightSwap_a_sameCycle_iff_cycle0 f hab hs hk hkm hb b).1 hxab
          exact False.elim (splitCycle0_excludes_b f hab hs hk hkm hb hb0)
        · have hxb : (f * Equiv.swap a b).SameCycle x b := Quotient.exact (by
            simpa [map, splitOrbitQuotientMap_mk, hax] using h.symm)
          have hb1 := (rightSwap_b_sameCycle_iff_cycle1 f hab hs hk hkm hb x).1 hxb.symm
          exact False.elim (hax (splitCycle1_subset_oldOrbit f a hb1))
      | inr v => exact congrArg Sum.inr (Subsingleton.elim _ _)
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hax : f.SameCycle a x
    · rcases sameCycle_split_index_partition f hab k hk hkm hb hax with
        hxa | ⟨i, hi, him, hix⟩ | ⟨i, hi, hik, hix⟩
      · subst x
        exact ⟨Sum.inl (Quotient.mk _ a), by simp [map, splitOrbitQuotientMap_mk]⟩
      · have hcycle := rightSwapCycle0_reachable f hab hs hk hkm hb hi him
        have hcycle' : (f * Equiv.swap a b).SameCycle a x := by simpa [hix] using hcycle
        refine ⟨Sum.inl (Quotient.mk _ a), ?_⟩
        change map (Quotient.mk (Equiv.Perm.SameCycle.setoid f) a) =
          Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) x
        have hmap : map (Quotient.mk (Equiv.Perm.SameCycle.setoid f) a) =
            Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) a := by
          change splitOrbitQuotientMap f a b hs hab k hk hkm hb
            (Quotient.mk (Equiv.Perm.SameCycle.setoid f) a) = _
          rw [splitOrbitQuotientMap_mk]
          simp
        rw [hmap]
        apply Quotient.sound
        exact hcycle'
      · have hcycle := rightSwapCycle1_reachable f hab hs hk hkm hb hi hik
        have hcycle' : (f * Equiv.swap a b).SameCycle b x := by simpa [hix] using hcycle
        refine ⟨Sum.inr PUnit.unit, ?_⟩
        change Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) b =
          Quotient.mk (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b)) x
        exact Quotient.sound hcycle'
    · refine ⟨Sum.inl (Quotient.mk _ x), ?_⟩
      simp [map, splitOrbitQuotientMap_mk, hax]

/-- Right multiplication by a transposition at two points in one cycle
increases the number of `SameCycle` classes by one (`sec-kmsw`, -/
theorem sameCycle_split_orbit_count (f : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hs : f.SameCycle a b) :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b))) =
      Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f)) + 1 := by
  classical
  obtain ⟨k, ⟨hk, hkm, hb⟩, _⟩ := sameCycle_split_index_unique f hab hs
  calc
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (f * Equiv.swap a b))) =
        Fintype.card
          (Quotient (Equiv.Perm.SameCycle.setoid f) ⊕ PUnit.{u + 1}) :=
      Fintype.card_congr (splitOrbitQuotientEquiv f hab hs k hk hkm hb).symm
    _ = Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f)) + 1 := by simp

end DirectedDistances.PlanarMap

