/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega

/-! Supporting lemmas for paper labels `lem-lazy-walk-flip` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.RandomWalk
/-- The literal source n-step integer paths with start zero and lazy increments. -/
@[expose] def LazyPath (n : ℕ) :=
  {p : Fin (n + 1) → ℤ // p 0 = 0 ∧
    ∀ i : Fin n, p i.succ - p i.castSucc ∈ ({-1, 0, 1} : Set ℤ)}
/-- The actual subclass of lazy paths whose every coordinate is nonnegative. -/
@[expose] def NonnegativeLazyPath (n : ℕ) :=
  {p : LazyPath n // ∀ j : Fin (n + 1), 0 ≤ p.val j}
/-- The actual minimum over the nonempty finite initial segment ending at j. -/
@[expose] noncomputable def runningMinimum {n : ℕ} (p : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) : ℤ :=
  (Finset.Iic j).inf' ⟨j, Finset.mem_Iic.mpr le_rfl⟩ p
/-- The actual minimum over the nonempty finite terminal segment starting at j. -/
@[expose] noncomputable def futureMinimum {n : ℕ} (p : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) : ℤ :=
  (Finset.Ici j).inf' ⟨j, Finset.mem_Ici.mpr le_rfl⟩ p
/-- The literal forward Pitman transform before its path-membership proof. -/
@[expose] noncomputable def lazyPhiValues {n : ℕ} (p : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) : ℤ := p j - 2 * runningMinimum p j
/-- The literal inverse transform before its path-membership proof. -/
@[expose] noncomputable def lazyPsiValues {n : ℕ} (q : Fin (n + 1) → ℤ)
    (k : ℤ) (j : Fin (n + 1)) : ℤ := q j - 2 * min k (futureMinimum q j)

/-- A lazy increment is exactly an integer between minus one and one. -/
theorem lazy_increment_iff {d : ℤ} :
    d ∈ ({-1, 0, 1} : Set ℤ) ↔ -1 ≤ d ∧ d ≤ 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- The running minimum is below every earlier coordinate. -/
theorem runningMinimum_le {n : ℕ} (p : Fin (n + 1) → ℤ)
    {i j : Fin (n + 1)} (hij : i ≤ j) : runningMinimum p j ≤ p i :=
  Finset.inf'_le p (Finset.mem_Iic.mpr hij)

/-- Every lower bound of the initial segment bounds its actual minimum. -/
theorem le_runningMinimum {n : ℕ} (p : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) {a : ℤ} (ha : ∀ i ≤ j, a ≤ p i) :
    a ≤ runningMinimum p j :=
  Finset.le_inf' _ _ (fun i hi => ha i (Finset.mem_Iic.mp hi))

/-- A future minimum is below every later coordinate. -/
theorem futureMinimum_le {n : ℕ} (p : Fin (n + 1) → ℤ)
    {i j : Fin (n + 1)} (hji : j ≤ i) : futureMinimum p j ≤ p i :=
  Finset.inf'_le p (Finset.mem_Ici.mpr hji)

/-- Every lower bound of the terminal segment bounds its actual minimum. -/
theorem le_futureMinimum {n : ℕ} (p : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) {a : ℤ} (ha : ∀ i, j ≤ i → a ≤ p i) :
    a ≤ futureMinimum p j :=
  Finset.le_inf' _ _ (fun i hi => ha i (Finset.mem_Ici.mp hi))

@[simp] theorem runningMinimum_zero {n : ℕ} (p : Fin (n + 1) → ℤ) :
    runningMinimum p 0 = p 0 := by
  apply le_antisymm (runningMinimum_le p le_rfl)
  apply le_runningMinimum
  intro i hi
  have : i = 0 := le_antisymm hi (Fin.zero_le i)
  rw [this]

@[simp] theorem futureMinimum_last {n : ℕ} (p : Fin (n + 1) → ℤ) :
    futureMinimum p (Fin.last n) = p (Fin.last n) := by
  apply le_antisymm (futureMinimum_le p le_rfl)
  apply le_futureMinimum
  intro i hi
  have : i = Fin.last n := le_antisymm (Fin.le_last i) hi
  rw [this]

/-- The actual running minima decrease under inclusion of initial segments. -/
theorem runningMinimum_antitone {n : ℕ} (p : Fin (n + 1) → ℤ) :
    Antitone (runningMinimum p) := by
  intro i j hij
  exact le_runningMinimum p i (fun k hki => runningMinimum_le p (hki.trans hij))

/-- The actual future minima increase under restriction of terminal segments. -/
theorem futureMinimum_monotone {n : ℕ} (p : Fin (n + 1) → ℤ) :
    Monotone (futureMinimum p) := by
  intro i j hij
  exact le_futureMinimum p j (fun k hjk => futureMinimum_le p (hij.trans hjk))

/-- Adding the next coordinate gives the ordinary running-minimum recursion. -/
theorem runningMinimum_succ {n : ℕ} (p : Fin (n + 1) → ℤ) (i : Fin n) :
    runningMinimum p i.succ = min (runningMinimum p i.castSucc) (p i.succ) := by
  apply le_antisymm
  · exact le_min ((runningMinimum_antitone p) (by change i.val ≤ i.val + 1; omega)) (runningMinimum_le p le_rfl)
  · apply le_runningMinimum
    intro j hj
    by_cases h : j = i.succ
    · rw [h]; exact min_le_right _ _
    · have hji : j ≤ i.castSucc := by
        change j.val ≤ i.val
        have hj' : j.val ≤ i.val + 1 := hj
        have hjne : j.val ≠ i.val + 1 := by
          intro heq; exact h (Fin.ext heq)
        omega
      exact (min_le_left _ _).trans (runningMinimum_le p hji)

/-- Removing the current coordinate gives the ordinary future-minimum recursion. -/
theorem futureMinimum_castSucc {n : ℕ} (p : Fin (n + 1) → ℤ) (i : Fin n) :
    futureMinimum p i.castSucc = min (p i.castSucc) (futureMinimum p i.succ) := by
  apply le_antisymm
  · exact le_min (futureMinimum_le p le_rfl) ((futureMinimum_monotone p) (by change i.val ≤ i.val + 1; omega))
  · apply le_futureMinimum
    intro j hj
    by_cases h : j = i.castSucc
    · rw [h]; exact min_le_left _ _
    · have hij : i.succ ≤ j := by
        change i.val + 1 ≤ j.val
        have hj' : i.val ≤ j.val := hj
        have hjne : j.val ≠ i.val := by
          intro heq; exact h (Fin.ext heq)
        omega
      exact (min_le_right _ _).trans (futureMinimum_le p hij)

/-- The literal Pitman transform has the same start and valid lazy increments. -/
theorem lazyPhiValues_isLazyPath {n : ℕ} (p : LazyPath n) :
    lazyPhiValues p.val 0 = 0 ∧
      ∀ i : Fin n, lazyPhiValues p.val i.succ - lazyPhiValues p.val i.castSucc ∈
        ({-1, 0, 1} : Set ℤ) := by
  constructor
  · simp only [lazyPhiValues, runningMinimum_zero, p.property.1]
    omega
  · intro i
    rw [lazy_increment_iff]
    have hstep := lazy_increment_iff.mp (p.property.2 i)
    have hm := runningMinimum_le p.val (i := i.castSucc) le_rfl
    dsimp only [lazyPhiValues]
    rw [runningMinimum_succ]
    by_cases h : runningMinimum p.val i.castSucc ≤ p.val i.succ
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right (le_of_not_ge h)]
      omega

/-- Nonnegativity follows from the actual minimum being below zero and p(j). -/
theorem lazyPhiValues_nonneg {n : ℕ} (p : LazyPath n) (j : Fin (n + 1)) :
    0 ≤ lazyPhiValues p.val j := by
  have hm := runningMinimum_le p.val (i := j) le_rfl
  have hz := runningMinimum_le p.val (Fin.zero_le j)
  rw [p.property.1] at hz
  dsimp only [lazyPhiValues]
  omega

/-- The actual Pitman transform into the nonnegative lazy-path carrier. -/
@[expose] noncomputable def lazyPhi {n : ℕ} (p : LazyPath n) : NonnegativeLazyPath n :=
  ⟨⟨lazyPhiValues p.val, lazyPhiValues_isLazyPath p⟩, lazyPhiValues_nonneg p⟩

@[simp] theorem lazyPhi_apply {n : ℕ} (p : LazyPath n) (j : Fin (n + 1)) :
    (lazyPhi p).val.val j = p.val j - 2 * runningMinimum p.val j := rfl


/-- The future minimum of a nonnegative path starting at zero is zero at zero. -/
@[simp] theorem futureMinimum_zero_of_nonnegative {n : ℕ} (q : NonnegativeLazyPath n) :
    futureMinimum q.val.val 0 = 0 := by
  apply le_antisymm
  · have hh := futureMinimum_le q.val.val (i := 0) le_rfl
    rw [q.val.property.1] at hh
    exact hh
  · exact le_futureMinimum _ _ (fun i _ => q.property i)

/-- At an increase of the capped future minimum, the underlying path takes
exactly the corresponding upward unit step. -/
theorem capped_futureMinimum_step {n : ℕ} (q : LazyPath n) (k : ℤ) (i : Fin n) :
    min k (futureMinimum q.val i.castSucc) ≤ min k (futureMinimum q.val i.succ) ∧
    min k (futureMinimum q.val i.succ) ≤ min k (futureMinimum q.val i.castSucc) + 1 ∧
    (min k (futureMinimum q.val i.castSucc) < min k (futureMinimum q.val i.succ) →
      q.val i.castSucc = min k (futureMinimum q.val i.castSucc) ∧
      q.val i.succ = min k (futureMinimum q.val i.succ)) := by
  have hstep := lazy_increment_iff.mp (q.property.2 i)
  have hm := futureMinimum_le q.val (i := i.succ) le_rfl
  have hrec := futureMinimum_castSucc q.val i
  omega

/-- The literal future-minimum transform has a valid lazy-path start and
steps for every nonnegative parameter. -/
theorem lazyPsiValues_isLazyPath {n : ℕ} (q : NonnegativeLazyPath n)
    {k : ℤ} (hk : 0 ≤ k) :
    lazyPsiValues q.val.val k 0 = 0 ∧
      ∀ i : Fin n, lazyPsiValues q.val.val k i.succ -
        lazyPsiValues q.val.val k i.castSucc ∈ ({-1, 0, 1} : Set ℤ) := by
  constructor
  · simp only [lazyPsiValues, futureMinimum_zero_of_nonnegative, q.val.property.1,
      min_eq_right hk]
    omega
  · intro i
    rw [lazy_increment_iff]
    have hstep := lazy_increment_iff.mp (q.val.property.2 i)
    have hdata := capped_futureMinimum_step q.val k i
    dsimp only [lazyPsiValues]
    omega

/-- The source inverse transform on its literal terminal-height parameter domain. -/
@[expose] noncomputable def lazyPsi {n : ℕ} (q : NonnegativeLazyPath n)
    (k : {k : ℤ // 0 ≤ k ∧ k ≤ q.val.val (Fin.last n)}) : LazyPath n :=
  ⟨lazyPsiValues q.val.val k.val, lazyPsiValues_isLazyPath q k.property.1⟩

@[simp] theorem lazyPsi_apply {n : ℕ} (q : NonnegativeLazyPath n)
    (k : {k : ℤ // 0 ≤ k ∧ k ≤ q.val.val (Fin.last n)}) (j : Fin (n + 1)) :
    (lazyPsi q k).val j = q.val.val j - 2 * min k.val (futureMinimum q.val.val j) := rfl

/-- The running minimum of the literal inverse transform is the negative
capped future minimum. This is derived from the actual path, not assumed. -/
theorem runningMinimum_lazyPsiValues {n : ℕ} (q : NonnegativeLazyPath n)
    {k : ℤ} (hk : 0 ≤ k) (j : Fin (n + 1)) :
    runningMinimum (lazyPsiValues q.val.val k) j = -min k (futureMinimum q.val.val j) := by
  induction j using Fin.induction with
  | zero =>
      rw [runningMinimum_zero]
      simp only [lazyPsiValues, futureMinimum_zero_of_nonnegative, q.val.property.1,
        min_eq_right hk]
      omega
  | succ i ih =>
      rw [runningMinimum_succ, ih]
      have hdata := capped_futureMinimum_step q.val k i
      have hle := futureMinimum_le q.val.val (i := i.succ) le_rfl
      dsimp only [lazyPsiValues]
      omega

/-- The forward transform of the inverse returns the actual nonnegative path. -/
theorem lazyPhi_lazyPsi {n : ℕ} (q : NonnegativeLazyPath n)
    (k : {k : ℤ // 0 ≤ k ∧ k ≤ q.val.val (Fin.last n)}) :
    lazyPhi (lazyPsi q k) = q := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change lazyPsiValues q.val.val k.val j -
    2 * runningMinimum (lazyPsiValues q.val.val k.val) j = q.val.val j
  rw [runningMinimum_lazyPsiValues q k.property.1]
  dsimp only [lazyPsiValues]
  omega


/- The capped future minimum of the actual forward transform recovers -/
theorem capped_futureMinimum_lazyPhiValues {n : ℕ} (p : LazyPath n)
    (j : Fin (n + 1)) :
    min (-runningMinimum p.val (Fin.last n))
      (futureMinimum (lazyPhiValues p.val) j) = -runningMinimum p.val j := by
  induction j using Fin.reverseInduction with
  | last =>
      rw [futureMinimum_last]
      have hm := runningMinimum_le p.val (i := Fin.last n) le_rfl
      dsimp only [lazyPhiValues]
      omega
  | cast i ih =>
      rw [futureMinimum_castSucc]
      have hm := runningMinimum_le p.val (i := i.castSucc) le_rfl
      have hstep := lazy_increment_iff.mp (p.property.2 i)
      have hrec := runningMinimum_succ p.val i
      dsimp only [lazyPhiValues]
      omega

/-- The genuine inverse parameter belongs to the full terminal-height domain. -/
@[expose] noncomputable def lazyInverseParameter {n : ℕ} (p : LazyPath n) :
    {k : ℤ // 0 ≤ k ∧ k ≤ (lazyPhi p).val.val (Fin.last n)} := by
  refine ⟨-runningMinimum p.val (Fin.last n), ?_⟩
  have hm := runningMinimum_le p.val (i := Fin.last n) le_rfl
  have hz := runningMinimum_le p.val (Fin.zero_le (Fin.last n))
  rw [p.property.1] at hz
  rw [lazyPhi_apply]
  omega

 
@[simp] theorem lazyInverseParameter_val {n : ℕ} (p : LazyPath n) :
    (lazyInverseParameter p).val = -runningMinimum p.val (Fin.last n) := rfl

/-- The inverse transform with its derived parameter returns the actual original path. -/
theorem lazyPsi_lazyPhi {n : ℕ} (p : LazyPath n) :
    lazyPsi (lazyPhi p) (lazyInverseParameter p) = p := by
  apply Subtype.ext
  funext j
  change lazyPhiValues p.val j - 2 * min (-runningMinimum p.val (Fin.last n))
    (futureMinimum (lazyPhiValues p.val) j) = p.val j
  rw [capped_futureMinimum_lazyPhiValues]
  dsimp only [lazyPhiValues]
  omega

/-- Every valid inverse parameter is visible at the terminal coordinate. -/
theorem lazyPsi_last {n : ℕ} (q : NonnegativeLazyPath n)
    (k : {k : ℤ // 0 ≤ k ∧ k ≤ q.val.val (Fin.last n)}) :
    (lazyPsi q k).val (Fin.last n) = q.val.val (Fin.last n) - 2 * k.val := by
  rw [lazyPsi_apply, futureMinimum_last, min_eq_left k.property.2]

/-- Distinct valid parameters give distinct preimages, as needed for the
source's fiber count. -/
theorem lazyPsi_injective {n : ℕ} (q : NonnegativeLazyPath n) :
    Function.Injective (lazyPsi q) := by
  intro k l h
  have he := congrArg (fun p : LazyPath n => p.val (Fin.last n)) h
  rw [lazyPsi_last, lazyPsi_last] at he
  apply Subtype.ext
  omega

/-- The complete actual fiber parameterization; the preimage direction uses
the proved inverse parameter, not a counting assumption. -/
theorem lazyPhi_fiber_iff {n : ℕ} (p : LazyPath n) (q : NonnegativeLazyPath n) :
    lazyPhi p = q ↔ ∃ k : {k : ℤ // 0 ≤ k ∧ k ≤ q.val.val (Fin.last n)},
      lazyPsi q k = p := by
  constructor
  · intro h
    subst q
    exact ⟨lazyInverseParameter p, lazyPsi_lazyPhi p⟩
  · rintro ⟨k, rfl⟩
    exact lazyPhi_lazyPsi q k

/-- The parameter interval is in bijection with the literal fiber of Phi. -/
@[expose] noncomputable def lazyPhiFiberEquiv {n : ℕ} (q : NonnegativeLazyPath n) :
    {k : ℤ // 0 ≤ k ∧ k ≤ q.val.val (Fin.last n)} ≃
      {p : LazyPath n // lazyPhi p = q} :=
  Equiv.ofBijective (fun k => ⟨lazyPsi q k, lazyPhi_lazyPsi q k⟩)
    ⟨fun k l h => lazyPsi_injective q (congrArg Subtype.val h), by
      intro p
      obtain ⟨k, hk⟩ := (lazyPhi_fiber_iff p.val q).mp p.property
      exact ⟨k, Subtype.ext hk⟩⟩


/-- The literal integer parameter interval is equivalent to a finite interval
of the claimed size, including zero terminal height. -/
@[expose] noncomputable def lazyParameterFinEquiv {n : ℕ} (q : NonnegativeLazyPath n) :
    Fin ((q.val.val (Fin.last n)).toNat + 1) ≃
      {k : ℤ // 0 ≤ k ∧ k ≤ q.val.val (Fin.last n)} where
  toFun k := ⟨(k.val : ℤ), by have hq := q.property (Fin.last n); have hk := k.isLt; omega⟩
  invFun k := ⟨k.val.toNat, by have hq := q.property (Fin.last n); have hk := k.property; omega⟩
  left_inv k := by apply Fin.ext; dsimp
  right_inv k := by apply Subtype.ext; dsimp; have hk := k.property; omega

/-- A finite interval of exactly terminal-height-plus-one elements
parameterizes the actual fiber. -/
@[expose] noncomputable def lazyPhiFiberFinEquiv {n : ℕ} (q : NonnegativeLazyPath n) :
    Fin ((q.val.val (Fin.last n)).toNat + 1) ≃
      {p : LazyPath n // lazyPhi p = q} :=
  (lazyParameterFinEquiv q).trans (lazyPhiFiberEquiv q)

/-- The actual fiber is finite, independently of any convention for infinite cardinality. -/
instance finite_lazyPhiFiber {n : ℕ} (q : NonnegativeLazyPath n) :
    Finite {p : LazyPath n // lazyPhi p = q} :=
  Finite.of_equiv _ (lazyPhiFiberFinEquiv q)

/-- The source's terminal-height-plus-one fiber count. -/
theorem card_lazyPhiFiber {n : ℕ} (q : NonnegativeLazyPath n) :
    Nat.card {p : LazyPath n // lazyPhi p = q} = (q.val.val (Fin.last n)).toNat + 1 := by
  rw [← Nat.card_congr (lazyPhiFiberFinEquiv q), Nat.card_fin]

/-- Every actual lazy path has the deterministic speed-one coordinate bound. -/
theorem lazyPath_coordinate_bounds {n : ℕ} (p : LazyPath n) (j : Fin (n + 1)) :
    -(j.val : ℤ) ≤ p.val j ∧ p.val j ≤ (j.val : ℤ) := by
  induction j using Fin.induction with
  | zero => rw [p.property.1]; omega
  | succ i ih =>
      have hstep := lazy_increment_iff.mp (p.property.2 i)
      change -(i.val : ℤ) ≤ p.val i.castSucc ∧ p.val i.castSucc ≤ (i.val : ℤ) at ih
      change -((i.val + 1 : ℕ) : ℤ) ≤ p.val i.succ ∧
        p.val i.succ ≤ ((i.val + 1 : ℕ) : ℤ)
      omega

/-- Encode the literal coordinates in a proved finite coordinate box. -/
@[expose] def lazyPathEncode {n : ℕ} (p : LazyPath n) :
    Fin (n + 1) → Fin (2 * n + 1) := fun j =>
  ⟨(p.val j + (n : ℤ)).toNat, by
    have hb := lazyPath_coordinate_bounds p j
    have hj := j.isLt
    omega⟩

/-- The finite-box encoding retains every path coordinate. -/
theorem lazyPathEncode_injective {n : ℕ} : Function.Injective (@lazyPathEncode n) := by
  intro p q h
  apply Subtype.ext
  funext j
  have he := congrArg Fin.val (congrFun h j)
  change (p.val j + (n : ℤ)).toNat = (q.val j + (n : ℤ)).toNat at he
  have hp := lazyPath_coordinate_bounds p j
  have hq := lazyPath_coordinate_bounds q j
  have hj := j.isLt
  omega

/-- Actual lazy paths form a finite type, derived from their finite coordinate bounds. -/
noncomputable instance instFintypeLazyPath (n : ℕ) : Fintype (LazyPath n) :=
  Fintype.ofInjective lazyPathEncode lazyPathEncode_injective

/-- The actual nonnegative subclass is finite as well. -/
noncomputable instance instFintypeNonnegativeLazyPath (n : ℕ) : Fintype (NonnegativeLazyPath n) := by
  classical
  unfold NonnegativeLazyPath
  infer_instance


/-- The natural-coordinate version of the actual nonnegative integer path. -/
@[expose] def nonnegativeLazyPathToNat {n : ℕ} (q : NonnegativeLazyPath n) :
    Fin (n + 1) → ℕ := fun j => (q.val.val j).toNat

/-- Passing to natural coordinates retains the literal integer coordinate. -/
@[simp] theorem nonnegativeLazyPathToNat_coe {n : ℕ} (q : NonnegativeLazyPath n)
    (j : Fin (n + 1)) : (nonnegativeLazyPathToNat q j : ℤ) = q.val.val j :=
  Int.toNat_of_nonneg (q.property j)

@[simp] theorem nonnegativeLazyPathToNat_zero {n : ℕ} (q : NonnegativeLazyPath n) :
    nonnegativeLazyPathToNat q 0 = 0 := by
  dsimp only [nonnegativeLazyPathToNat]
  rw [q.val.property.1]
  rfl

/-- Actual neighboring natural coordinates satisfy the conditioned-kernel step support. -/
theorem nonnegativeLazyPathToNat_step {n : ℕ} (q : NonnegativeLazyPath n) (i : Fin n) :
    |(nonnegativeLazyPathToNat q i.succ : ℤ) -
      (nonnegativeLazyPathToNat q i.castSucc : ℤ)| ≤ 1 := by
  rw [nonnegativeLazyPathToNat_coe, nonnegativeLazyPathToNat_coe]
  have h := q.val.property.2 i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h
  all_goals rw [h]; decide

end DirectedDistances.RandomWalk
