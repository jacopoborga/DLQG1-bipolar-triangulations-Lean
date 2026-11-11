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
import DirectedDistances.Tauberian.RecursionZero
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
meta import Lean.Elab.Tactic.Omega

/-! Supporting lemmas for paper labels `lem:Y-not-const` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.Recursive

private theorem pmf_atom_le_one {p : ℤ → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hps : HasSum p 1) (c : ℤ) : p c ≤ 1 := by
  have h := hps.summable.sum_le_tsum ({c} : Finset ℤ) (fun x _ => hp x)
  rw [hps.tsum_eq] at h
  simpa using h

private theorem pmf_two_atoms_le_one {p : ℤ → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hps : HasSum p 1) {c d : ℤ} (hcd : c ≠ d) :
    p c + p d ≤ 1 := by
  have h := hps.summable.sum_le_tsum ({c, d} : Finset ℤ) (fun x _ => hp x)
  rw [hps.tsum_eq] at h
  simpa [hcd] using h

private theorem pmf_atom_one_vanish {p : ℤ → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hps : HasSum p 1) {c x : ℤ}
    (hc : p c = 1) (hxc : x ≠ c) : p x = 0 := by
  have hsum := pmf_two_atoms_le_one hp hps hxc.symm
  rw [hc] at hsum
  linarith [hp x]

private theorem pmf_shift_product_tsum_nonneg {p : ℤ → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hps : HasSum p (1 : ℝ)) (x : ℤ) :
    0 ≤ ∑' j : ℕ, p ((j : ℤ) + x + 1) * p (-(j : ℤ)) := by
  have hpNs : Summable (fun z : ℤ => (p z).toNNReal) :=
    hps.toNNReal hp |>.summable
  have hi : Function.Injective (fun j : ℕ => (j : ℤ) + x + 1) := by
    intro j k h
    exact Int.natCast_inj.mp (add_right_cancel (add_right_cancel h))
  have hshiftN : Summable (fun j : ℕ => (p ((j : ℤ) + x + 1)).toNNReal) :=
    NNReal.summable_comp_injective hpNs hi
  have hshift : Summable (fun j : ℕ => p ((j : ℤ) + x + 1)) := by
    have hcoe : Summable (fun j : ℕ => ((p ((j : ℤ) + x + 1)).toNNReal : ℝ)) :=
      NNReal.summable_coe.mpr hshiftN
    convert hcoe using 1
    funext j
    rw [Real.coe_toNNReal _ (hp _)]
  have htermnonneg (j : ℕ) :
      0 ≤ p ((j : ℤ) + x + 1) * p (-(j : ℤ)) :=
    mul_nonneg (hp _) (hp _)
  have htermle (j : ℕ) :
      p ((j : ℤ) + x + 1) * p (-(j : ℤ)) ≤ p ((j : ℤ) + x + 1) :=
    mul_le_of_le_one_right (hp _) (pmf_atom_le_one hp hps _)
  have hts : Summable (fun j : ℕ => p ((j : ℤ) + x + 1) * p (-(j : ℤ))) :=
    Summable.of_nonneg_of_le htermnonneg htermle hshift
  calc
    0 = ∑' j : ℕ, (0 : ℝ) := by simp
    _ ≤ ∑' j : ℕ, p ((j : ℤ) + x + 1) * p (-(j : ℤ)) :=
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))).tsum_le_tsum
        htermnonneg hts

private theorem sum_Icc_int_one_reindex (n : ℕ) (φ : ℤ → ℝ) :
    (∑ j ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), φ j) =
      ∑ k ∈ Finset.range (n + 1), φ ((k : ℤ) + 1) := by
  symm
  apply Finset.sum_nbij' (fun k : ℕ => (k : ℤ) + 1)
    (fun j : ℤ => (j - 1).toNat)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_range]
    have hcast : (((j - 1).toNat : ℕ) : ℤ) = j - 1 :=
      Int.toNat_of_nonneg (by omega)
    omega
  · intro k hk
    apply Int.natCast_inj.mp
    rw [Int.toNat_of_nonneg (by simp [Finset.mem_range] at hk; omega)]
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    have hcast : (((j - 1).toNat : ℕ) : ℤ) = j - 1 :=
      Int.toNat_of_nonneg (by omega)
    rw [hcast]
    omega
  · intro k hk
    rfl

/-- The LDP master recursion forces every atom of the symmetric pmf to have
mass strictly below one, and forces positive mass at zero. This is a
conditional form of Lemma 6.6 (`lem:Y-not-const`), using -/
theorem ldp_pmf_nondegenerate_of_master
    {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) +
            g (-x - 1)
         else 0)) :
    (∀ c : ℤ, f c < 1) ∧ 0 < f 0 := by
  have hf0le : f 0 ≤ 1 := pmf_atom_le_one hf hfs 0
  have hf0lt : f 0 < 1 := by
    by_contra hnot
    have hf0eq : f 0 = 1 := le_antisymm hf0le (le_of_not_gt hnot)
    have hvanish : ∀ x : ℤ, x ≠ 0 → f x = 0 := by
      intro x hx
      exact pmf_atom_one_vanish hf hfs hf0eq (by simpa using hx)
    let a : ℕ → ℝ := fun n => g (-((n : ℤ) + 1))
    have hgminus : g (-1) = 0 := by
      have htsum : (∑' j : ℕ, f ((j : ℤ) + 1) * f (-(j : ℤ))) = 0 := by
        calc
          (∑' j : ℕ, f ((j : ℤ) + 1) * f (-(j : ℤ))) =
              ∑' _ : ℕ, (0 : ℝ) := tsum_congr fun j => by
                have hj : (j : ℤ) + 1 ≠ 0 := by omega
                rw [hvanish _ hj, zero_mul]
          _ = 0 := tsum_zero
      have h := hrec 0 (-1) (by omega)
      have hfminus : f (-1) = 0 := hvanish (-1) (by omega)
      simp [hf0eq, hfminus, htsum] at h
      linarith
    have hsimple (y : ℤ) (hy : y ≤ -2) :
        3 * g y = f y + ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1),
          g (y + j) * g (-j) := by
      have h := hrec 0 y (by omega)
      have hyne : y ≠ -1 := by omega
      simpa [hf0eq, ite_eq_right hyne] using h
    have hrecA (n : ℕ) :
        3 * a (n + 1) = ∑ k ∈ Finset.range (n + 1), a k * a (n - k) := by
      let y : ℤ := -((n : ℤ) + 2)
      have hy : y ≤ -2 := by dsimp [y]; omega
      have h := hsimple y hy
      have hyne0 : y ≠ 0 := by omega
      rw [hvanish y hyne0] at h
      simp only [zero_add] at h
      have htop : -y - 1 = (n : ℤ) + 1 := by dsimp [y]; omega
      rw [htop] at h
      have hreindex := sum_Icc_int_one_reindex n
        (fun j => g (y + j) * g (-j))
      rw [hreindex] at h
      have hterms :
          (∑ k ∈ Finset.range (n + 1),
              g (y + ((k : ℤ) + 1)) * g (-((k : ℤ) + 1))) =
            ∑ k ∈ Finset.range (n + 1), a k * a (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := by simp only [Finset.mem_range] at hk; omega
        have hcast : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by
          norm_cast
        have hindex : y + ((k : ℤ) + 1) = -(((n - k : ℕ) : ℤ) + 1) := by
          dsimp [y]
          rw [hcast]
          ring
        dsimp [a]
        rw [hindex]
        ring
      rw [hterms] at h
      have haeq : a (n + 1) = g y := by
        dsimp [a, y]
        congr 1
      rw [← haeq] at h
      exact h
    have ha0 : a 0 = 0 := by
      change g (-1) = 0
      exact hgminus
    have ha := DirectedDistances.Tauberian.convolution_eq_zero_of_zero_initial
      a ha0 hrecA
    have hgv : ∀ y : ℤ, g y = 0 := by
      intro y
      by_cases hy : y ≤ -1
      · let n : ℕ := (-y - 1).toNat
        have hncast : (n : ℤ) = -y - 1 := by
          dsimp [n]
          exact Int.toNat_of_nonneg (by omega)
        have hy' : -((n : ℤ) + 1) = y := by rw [hncast]; omega
        rw [← hy']
        simpa [a] using ha n
      · exact hgsupp y (by omega)
    have hgeq : g = fun _ => (0 : ℝ) := funext hgv
    have hzero : HasSum g 0 := by
      simp [hgeq]
    have hbad := hgs.unique hzero
    norm_num at hbad
  constructor
  · intro c
    have hcle : f c ≤ 1 := pmf_atom_le_one hf hfs c
    by_contra hnot
    have hceq : f c = 1 := le_antisymm hcle (le_of_not_gt hnot)
    by_cases hc0 : c = 0
    · subst c
      exact hnot hf0lt
    · have hpair : f c + f (-c) ≤ 1 := by
        apply pmf_two_atoms_le_one hf hfs
        intro h
        have : c = 0 := by omega
        exact hc0 this
      rw [hsymm c, hceq] at hpair
      linarith
  · have hgminuspos : 0 < g (-1) := by
      by_contra hnot
      have hgminuseq : g (-1) = 0 := le_antisymm (le_of_not_gt hnot) (hg (-1))
      have hzeroall : ∀ y : ℤ, g y = 0 := by
        intro y
        have h := hrec (-y - 1) (-1) (by omega)
        have htsum := pmf_shift_product_tsum_nonneg hf hfs (-y - 1)
        have hprod : 0 ≤ f (-y - 1) * f (-1) := mul_nonneg (hf _) (hf _)
        rw [hgminuseq] at h
        simp at h
        have hy : g y = 0 := by
          have hgy : 0 ≤ g y := hg y
          linarith [h, hprod, htsum, hgy]
        exact hy
      have hgeq : g = fun _ => (0 : ℝ) := funext hzeroall
      have hzero : HasSum g 0 := by
        simp [hgeq]
      have hbad := hgs.unique hzero
      norm_num at hbad
    by_contra hnot
    have hf0eq : f 0 = 0 := le_antisymm (le_of_not_gt hnot) (hf 0)
    have h := hrec 0 (-1) (by omega)
    have htsum := pmf_shift_product_tsum_nonneg hf hfs 0
    simp only [add_zero] at htsum
    rw [hf0eq] at h
    simp at h
    linarith [h, htsum, hgminuspos]

end DirectedDistances.Recursive
