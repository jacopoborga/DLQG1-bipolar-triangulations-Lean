/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
meta import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! # Nondegeneracy from the SDP master recursion

This module proves the analytic conclusion of Lemma 6.12 conditionally on the
exact master recursion in Proposition 6.11. The geometric proof of that
675–728`. -/

public section
namespace DirectedDistances.Recursive

private theorem pmf_atom_le_one {p : ℤ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hps : HasSum p 1) (c : ℤ) : p c ≤ 1 := by
  have h := hps.summable.sum_le_tsum ({c} : Finset ℤ) (fun x _ => hp x)
  rw [hps.tsum_eq] at h
  simpa using h

private theorem pmf_two_atoms_le_one {p : ℤ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hps : HasSum p 1) {c d : ℤ} (hcd : c ≠ d) : p c + p d ≤ 1 := by
  have h := hps.summable.sum_le_tsum ({c, d} : Finset ℤ) (fun x _ => hp x)
  rw [hps.tsum_eq] at h
  simpa [hcd] using h

private theorem pmf_atom_one_vanish {p : ℤ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hps : HasSum p 1) {c x : ℤ} (hc : p c = 1) (hxc : x ≠ c) : p x = 0 := by
  have hpair : p c + p x ≤ 1 := pmf_two_atoms_le_one hp hps hxc.symm
  rw [hc] at hpair
  linarith [hp x]

private theorem sdp_convolution_eq_two_mul {g : ℤ → ℝ}
    (hgneg : g (-1) = 0) (y : ℤ) (hy : 1 ≤ y)
    (hprev : ∀ j : ℤ, 0 < j → j < y → g j = 0) :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) =
      2 * g 0 * g y := by
  classical
  have hsub : insert 0 {y} ⊆ Finset.Icc (-1 : ℤ) (y + 1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have hsum := Finset.sum_subset (f := fun j : ℤ => g j * g (y - j))
      (s₁ := insert 0 {y})
      (s₂ := Finset.Icc (-1 : ℤ) (y + 1)) hsub
    (fun j hj hjs => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjs
      have hji := Finset.mem_Icc.mp hj
      by_cases hjm : j = -1
      · subst j
        simp [hgneg]
      · by_cases hjend : j = y + 1
        · subst j
          have harg : y - (y + 1) = -1 := by omega
          rw [harg, hgneg]
          simp
        · have hjpos : 0 < j := by omega
          have hjlt : j < y := by omega
          rw [hprev j hjpos hjlt]
          simp)
  rw [← hsum]
  have hy0 : y ≠ 0 := by omega
  calc
    (∑ j ∈ insert 0 {y}, g j * g (y - j)) =
        g 0 * g y + g y * g 0 := by
          have hnot : (0 : ℤ) ∉ ({y} : Finset ℤ) := by
            simp only [Finset.mem_singleton]
            exact Ne.symm hy0
          rw [Finset.sum_insert hnot, Finset.sum_singleton]
          simp [sub_zero, sub_self]
    _ = 2 * g 0 * g y := by ring

private theorem sdp_interval_neg_one_zero :
    Finset.Icc (-1 : ℤ) 0 = insert (-1) {0} := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem sdp_interval_neg_one_one :
    Finset.Icc (-1 : ℤ) 1 = insert (-1) (insert 0 {1}) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem sdp_interval_conv_neg_one (g : ℤ → ℝ) :
    (∑ j ∈ Finset.Icc (-1 : ℤ) 0, g j * g (-1 - j)) =
      2 * g (-1) * g 0 := by
  rw [sdp_interval_neg_one_zero]
  simp
  ring

private theorem sdp_interval_conv_zero {g : ℤ → ℝ} (hgneg : g (-1) = 0) :
    (∑ j ∈ Finset.Icc (-1 : ℤ) 1, g j * g (0 - j)) = g 0 * g 0 := by
  rw [sdp_interval_neg_one_one]
  simp [hgneg]

/-- The SDP recursion implies the nondegeneracy assertions of Lemma 6.12.
The recursion is Proposition 6.11, equation `eq:master-eq` in
`lem:Y-not-const2` at lines 675–728. -/
theorem sdp_pmf_nondegenerate_of_master
    {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0)) :
    (∀ c : ℤ, f c < 1) ∧ 0 < f 0 ∧ 0 < g (-1) := by
  have hf_le_one (x : ℤ) : f x ≤ 1 := pmf_atom_le_one hf hfs x
  have hg_le_one (x : ℤ) : g x ≤ 1 := pmf_atom_le_one hg hgs x

  have hgneg : 0 < g (-1) := by
    by_contra hnot
    have hzero : g (-1) = 0 := le_antisymm (le_of_not_gt hnot) (hg (-1))
    have hallzero : ∀ y : ℤ, g y = 0 := by
      intro y
      have h := hrec (y + 1) (-1) (by omega)
      have hconv : 0 ≤ ∑ j ∈ Finset.Icc (-1 : ℤ) 0, g j * g (-1 - j) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hg j) (hg (-1 - j))
      have htail : 0 ≤ ∑' j : {j : ℤ // j ≤ -2},
          f j * f ((y + 1) - (j : ℤ) - 1) :=
        tsum_nonneg fun j => mul_nonneg (hf (j : ℤ))
          (hf ((y + 1) - (j : ℤ) - 1))
      have hterm : 0 ≤ f (y + 1) *
          (f (-1) + ∑ j ∈ Finset.Icc (-1 : ℤ) 0, g j * g (-1 - j)) :=
        mul_nonneg (hf _) (add_nonneg (hf _) hconv)
      rw [hzero] at h
      rw [show (-1 : ℤ) + 1 = 0 by omega] at h
      have harg : y + 1 - 1 = y := by omega
      rw [harg] at h
      simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h
      rw [ite_eq_left (show True from trivial)] at h
      have hgy : g y ≤ 0 := by linarith [hterm, htail, h]
      exact le_antisymm hgy (hg y)
    have hgeq : g = fun _ => (0 : ℝ) := funext hallzero
    have hzeroHas : HasSum g 0 := by
      simp [hgeq]
    have hbad := hgs.unique hzeroHas
    norm_num at hbad

  have hfzero : 0 < f 0 := by
    by_contra hnot
    have hzero : f 0 = 0 := le_antisymm (le_of_not_gt hnot) (hf 0)
    have h := hrec 0 (-1) (by omega)
    have htail : 0 ≤ ∑' j : {j : ℤ // j ≤ -2}, f j * f (0 - (j : ℤ) - 1) :=
      tsum_nonneg fun j => mul_nonneg (hf (j : ℤ)) (hf (0 - (j : ℤ) - 1))
    have hlast : 0 ≤ (g (-1)) ^ 2 * f 1 := mul_nonneg (sq_nonneg _) (hf 1)
    rw [hzero] at h
    rw [show (-1 : ℤ) + 1 = 0 by omega,
      show (0 : ℤ) + 1 = 1 by omega, show (0 : ℤ) - 1 = -1 by omega] at h
    simp only [mul_zero, zero_mul] at h
    rw [ite_eq_left (show True from trivial)] at h
    have hbad : g (-1) ≤ 0 := by
      have hnonneg : 0 ≤ (∑' j : {j : ℤ // j ≤ -2},
          f j * f (0 - (j : ℤ) - 1)) + (g (-1)) ^ 2 * f 1 := add_nonneg htail hlast
      linarith [h, hnonneg]
    exact (not_lt_of_ge hbad) hgneg

  have hfzero_lt_one : f 0 < 1 := by
    by_contra hnot
    have hfzero_one : f 0 = 1 := le_antisymm (hf_le_one 0) (le_of_not_gt hnot)
    have hfconcentrated : ∀ x : ℤ, x ≠ 0 → f x = 0 := by
      intro x hx
      exact pmf_atom_one_vanish hf hfs hfzero_one hx
    have hgzeroone : g (-1) = 0 := by
      have h := hrec 0 (-1) (by omega)
      have hconv := sdp_interval_conv_neg_one g
      have htail : (∑' j : {j : ℤ // j ≤ -2}, f j * f (0 - (j : ℤ) - 1)) = 0 := by
        have hterms : ∀ j : {j : ℤ // j ≤ -2},
            f (j : ℤ) * f (0 - (j : ℤ) - 1) = 0 := by
          intro j
          have hj : (j : ℤ) ≠ 0 := by omega
          rw [hfconcentrated (j : ℤ) hj, zero_mul]
        have hzeroFun : (fun j : {j : ℤ // j ≤ -2} =>
            f (j : ℤ) * f (0 - (j : ℤ) - 1)) = fun _ => (0 : ℝ) := by
          funext j
          exact hterms j
        have htailHas : HasSum (fun j : {j : ℤ // j ≤ -2} =>
            f (j : ℤ) * f (0 - (j : ℤ) - 1)) 0 := by
          rw [hzeroFun]
          exact hasSum_zero
        exact htailHas.tsum_eq
      have hfminus : f (-1) = 0 := hfconcentrated (-1) (by omega)
      have hfplus : f 1 = 0 := hfconcentrated 1 (by omega)
      rw [show (-1 : ℤ) + 1 = 0 by omega,
        show (0 : ℤ) + 1 = 1 by omega, show (0 : ℤ) - 1 = -1 by omega,
        hfzero_one, hfminus, hfplus, hconv, htail] at h
      simp at h
      have hfac : g (-1) * (1 - g 0) = 0 := by nlinarith [h]
      rcases mul_eq_zero.mp hfac with ha | hb
      · exact ha
      · have hg0one : g 0 = 1 := by linarith
        have hgminus : g (-1) = 0 :=
          pmf_atom_one_vanish hg hgs hg0one (by omega)
        have hzero := hrec 0 0 (by omega)
        rw [show (0 : ℤ) + 1 = 1 by omega, hfzero_one, hgminus,
          sdp_interval_conv_zero hgminus] at hzero
        norm_num [hg0one] at hzero
    have hzeroeq := hrec 0 0 (by omega)
    rw [show (0 : ℤ) + 1 = 1 by omega, hfzero_one, hgzeroone,
      sdp_interval_conv_zero hgzeroone] at hzeroeq
    simp at hzeroeq
    have hbhalf : g 0 ≤ 1 / 2 := by
      have hb2 : g 0 * g 0 ≤ g 0 := by
        nlinarith [mul_nonneg (hg 0) (sub_nonneg.mpr (hg_le_one 0))]
      linarith [hzeroeq, hb2]
    have hpos : ∀ n : ℕ, g ((n + 1 : ℕ) : ℤ) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        let y : ℤ := ((n + 1 : ℕ) : ℤ)
        have hy : 1 ≤ y := by dsimp [y]; omega
        have hprev : ∀ j : ℤ, 0 < j → j < y → g j = 0 := by
          intro j hj0 hjy
          have hjcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (le_of_lt hj0)
          have hjle : j.toNat ≤ n := by dsimp [y] at hjy; omega
          have hlt : j.toNat - 1 < n := by omega
          have hih := ih (j.toNat - 1) hlt
          have hnat : (((j.toNat - 1) + 1 : ℕ) : ℤ) = j := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ j.toNat)]
            exact hjcast
          rw [hnat] at hih
          exact hih
        have hconv := sdp_convolution_eq_two_mul hgzeroone y hy hprev
        have heq := hrec 0 y (by omega)
        have hfy : f y = 0 := hfconcentrated y (by omega)
        rw [hfzero_one, hfy, hgzeroone, hconv] at heq
        have hyne1 : y ≠ -1 := by omega
        simp [hyne1] at heq
        have hmul : 2 * g 0 * g y ≤ g y := by
          have hcoeff : 2 * g 0 ≤ 1 := by linarith
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff (hg y)
        have hgy : g y = 0 := by nlinarith [heq, hmul, hg y]
        simpa [y] using hgy
    have hallzero_except_zero : ∀ y : ℤ, y ≠ 0 → g y = 0 := by
      intro y hy
      by_cases hyneg : y < -1
      · exact hgsupp y hyneg
      · by_cases hym1 : y = -1
        · subst y
          exact hgzeroone
        · have hypos : 0 < y := by omega
          have hcast : (((y.toNat - 1) + 1 : ℕ) : ℤ) = y := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ y.toNat)]
            exact Int.toNat_of_nonneg (le_of_lt hypos)
          have hval := hpos (y.toNat - 1)
          rw [hcast] at hval
          exact hval
    have hsingle : HasSum g (g 0) := hasSum_single 0 hallzero_except_zero
    have htotal : (1 : ℝ) = g 0 := hgs.unique hsingle
    linarith [hbhalf]

  have hfc_lt_one : ∀ c : ℤ, f c < 1 := by
    intro c
    by_cases hc0 : c = 0
    · simpa [hc0] using hfzero_lt_one
    · by_contra hnot
      have hceq : f c = 1 := le_antisymm (hf_le_one c) (le_of_not_gt hnot)
      have hpair : f c + f (-c) ≤ 1 := by
        apply pmf_two_atoms_le_one hf hfs
        intro h
        have hc : c = 0 := by omega
        exact hc0 hc
      rw [hsymm c, hceq] at hpair
      linarith
  exact ⟨hfc_lt_one, hfzero, hgneg⟩

end DirectedDistances.Recursive
