/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FiniteWalkClass
public import DirectedDistances.RandomWalk.PitmanCodes

/-! Supporting lemmas for paper labels `def-kmsw`, `thm-kmsw` (see CORRESPONDENCE.md). -/

/-! # Step codes for finite KMSW walks

helpers are not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open scoped BigOperators





theorem kmswStepTable :
    lazyTwoDimensionalStep 0 = (-1, 0) ∧
    lazyTwoDimensionalStep 1 = (0, 1) ∧
    lazyTwoDimensionalStep 2 = (1, -1) ∧
    Function.Injective lazyTwoDimensionalStep ∧
    Set.range lazyTwoDimensionalStep = {(-1, 0), (0, 1), (1, -1)} := by
  constructor
  · exact lazyTwoDimensionalStep_zero
  constructor
  · exact lazyTwoDimensionalStep_one
  constructor
  · exact lazyTwoDimensionalStep_two
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp [lazyTwoDimensionalStep] at h ⊢
  · ext z
    constructor
    · rintro ⟨c, rfl⟩
      fin_cases c <;> simp [lazyTwoDimensionalStep]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h
      · subst z
        exact ⟨0, lazyTwoDimensionalStep_zero⟩
      · subst z
        exact ⟨1, lazyTwoDimensionalStep_one⟩
      · subst z
        exact ⟨2, lazyTwoDimensionalStep_two⟩



@[expose] def stepCode (z : ℤ × ℤ) : Fin 3 :=
  if z = (-1, 0) then 0 else if z = (0, 1) then 1 else 2

/-- On every step in the procedure-reading table, `stepCode` decodes the -/
theorem lazyTwoDimensionalStep_stepCode_of_mem (z : ℤ × ℤ)
    (hz : z ∈ ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ))) :
    lazyTwoDimensionalStep (stepCode z) = z := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h | h | h
  · subst z
    simp [stepCode]
  · subst z
    simp [stepCode]
  · subst z
    simp [stepCode]



@[expose] def codesOfWalk {n : ℕ} (Z : Fin n → ℤ × ℤ) :
    Fin (n - 1) → Fin 3 :=
  fun i => stepCode
    (Z ⟨i.val + 1, by omega⟩ - Z ⟨i.val, by omega⟩)




theorem integrateCodes_codesOfWalk {n : ℕ} (Z : Fin n → ℤ × ℤ)
    (hn : 0 < n) (hstart : Z ⟨0, hn⟩ = (0, 0))
    (hsteps : ∀ i : Fin (n - 1),
      Z ⟨i.val + 1, by omega⟩ - Z ⟨i.val, by omega⟩ ∈
        ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)))
    (k : ℕ) (hk : k < n) :
    integrateCodes (finiteCodeExtend (codesOfWalk Z)) k = Z ⟨k, hk⟩ := by
  have hwalk : ∀ k (hk : k < n),
      integrateCodes (finiteCodeExtend (codesOfWalk Z)) k = Z ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk0
        simp only [integrateCodes, Finset.range_zero, Finset.sum_empty]
        have hidx : (⟨0, hn⟩ : Fin n) = ⟨0, hk0⟩ := Fin.ext rfl
        rw [hidx] at hstart
        exact hstart.symm
    | succ k ih =>
        intro hk
        have hklt : k < n := by omega
        have hcodeidx : k < n - 1 := by omega
        have hsource :
            Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩ ∈
              ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
          simpa using hsteps ⟨k, hcodeidx⟩
        have hdecode := lazyTwoDimensionalStep_stepCode_of_mem
          (Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩) hsource
        have hcode : finiteCodeExtend (codesOfWalk Z) k =
            stepCode (Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩) := by
          simp [finiteCodeExtend, codesOfWalk, hcodeidx]
        have hsum :
            integrateCodes (finiteCodeExtend (codesOfWalk Z)) (k + 1) =
              integrateCodes (finiteCodeExtend (codesOfWalk Z)) k +
                lazyTwoDimensionalStep (finiteCodeExtend (codesOfWalk Z) k) := by
          simp [integrateCodes, Finset.sum_range_succ]
        have hprev : integrateCodes (finiteCodeExtend (codesOfWalk Z)) k =
            Z ⟨k, by omega⟩ := by
          simpa using ih hklt
        have hstep : Z ⟨k + 1, by omega⟩ =
            Z ⟨k, by omega⟩ +
              lazyTwoDimensionalStep
                (stepCode (Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩)) := by
          calc
            Z ⟨k + 1, by omega⟩ =
                (Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩) + Z ⟨k, by omega⟩ := by
                  abel
            _ = lazyTwoDimensionalStep
                  (stepCode (Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩)) +
                    Z ⟨k, by omega⟩ := by
                    exact congrArg (fun v : ℤ × ℤ => v + Z ⟨k, by omega⟩)
                      hdecode.symm
            _ = Z ⟨k, by omega⟩ +
                  lazyTwoDimensionalStep
                    (stepCode (Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩)) := by
                    abel
        calc
          integrateCodes (finiteCodeExtend (codesOfWalk Z)) (k + 1) =
              integrateCodes (finiteCodeExtend (codesOfWalk Z)) k +
                lazyTwoDimensionalStep (finiteCodeExtend (codesOfWalk Z) k) := hsum
          _ = Z ⟨k, by omega⟩ + lazyTwoDimensionalStep
                (stepCode (Z ⟨k + 1, by omega⟩ - Z ⟨k, by omega⟩)) := by
                  rw [hprev, hcode]
          _ = Z ⟨k + 1, by omega⟩ := hstep.symm
  exact hwalk k hk




theorem kmswWalkAdmissible_codesOfWalk_iff {ℓ r n : ℕ}
    (Z : Fin n → ℤ × ℤ) (hn : 0 < n)
    (hstart : Z ⟨0, hn⟩ = (0, 0))
    (hsteps : ∀ i : Fin (n - 1),
      Z ⟨i.val + 1, by omega⟩ - Z ⟨i.val, by omega⟩ ∈
        ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ))) :
    KMSWWalkAdmissible ℓ r n (codesOfWalk Z) ↔
      Z ⟨n - 1, by omega⟩ = ((ℓ : ℤ) - 1, -(r : ℤ) + 1) ∧
        ∀ k : Fin n, 0 ≤ (Z k).1 ∧ -(r : ℤ) + 1 ≤ (Z k).2 := by
  constructor
  · intro hadm
    change integrateCodes (finiteCodeExtend (codesOfWalk Z)) (n - 1) = _ ∧ _ at hadm
    constructor
    · have hlast := integrateCodes_codesOfWalk Z hn hstart hsteps (n - 1) (by omega)
      calc
        Z ⟨n - 1, by omega⟩ =
            integrateCodes (finiteCodeExtend (codesOfWalk Z)) (n - 1) := hlast.symm
        _ = ((ℓ : ℤ) - 1, -(r : ℤ) + 1) := hadm.1
    · intro k
      have hk : k.val ∈ Finset.range (n - 1 + 1) := by
        apply Finset.mem_range.mpr
        omega
      have hpos := hadm.2 k.val hk
      have hwalk := integrateCodes_codesOfWalk Z hn hstart hsteps k.val k.isLt
      rw [hwalk] at hpos
      exact hpos
  · rintro ⟨hend, hcone⟩
    change integrateCodes (finiteCodeExtend (codesOfWalk Z)) (n - 1) = _ ∧
      ∀ k ∈ Finset.range (n - 1 + 1),
        0 ≤ (integrateCodes (finiteCodeExtend (codesOfWalk Z)) k).1 ∧
          -(r : ℤ) + 1 ≤ (integrateCodes (finiteCodeExtend (codesOfWalk Z)) k).2
    constructor
    · have hlast := integrateCodes_codesOfWalk Z hn hstart hsteps (n - 1) (by omega)
      calc
        integrateCodes (finiteCodeExtend (codesOfWalk Z)) (n - 1) =
            Z ⟨n - 1, by omega⟩ := hlast
        _ = ((ℓ : ℤ) - 1, -(r : ℤ) + 1) := hend
    · intro k hk
      have hkfin : k < n := by
        have := Finset.mem_range.mp hk
        omega
      have hpoint := hcone ⟨k, hkfin⟩
      have hwalk := integrateCodes_codesOfWalk Z hn hstart hsteps k hkfin
      rw [hwalk]
      exact hpoint

private theorem stepCode_lazyTwoDimensionalStep (c : Fin 3) :
    stepCode (lazyTwoDimensionalStep c) = c := by
  fin_cases c <;> simp [stepCode, lazyTwoDimensionalStep]



@[expose] def walkClassOfWalk {ℓ r n : ℕ} (Z : Fin n → ℤ × ℤ)
    (hn : 0 < n) (hstart : Z ⟨0, hn⟩ = (0, 0))
    (hsteps : ∀ i : Fin (n - 1),
      Z ⟨i.val + 1, by omega⟩ - Z ⟨i.val, by omega⟩ ∈
        ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)))
    (hend : Z ⟨n - 1, by omega⟩ = ((ℓ : ℤ) - 1, -(r : ℤ) + 1))
    (hcone : ∀ k : Fin n, 0 ≤ (Z k).1 ∧ -(r : ℤ) + 1 ≤ (Z k).2) :
    KMSWWalkClass ℓ r n :=
  ⟨codesOfWalk Z,
    (kmswWalkAdmissible_codesOfWalk_iff Z hn hstart hsteps).2 ⟨hend, hcone⟩⟩



theorem codesOfWalk_integrateCodes_codeExtend {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) :
    codesOfWalk (fun k : Fin n => integrateCodes (codeExtend c) k.val) = c.val := by
  funext i
  have hi : i.val < n - 1 := i.isLt
  have hcode := codeExtend_of_lt c i.val hi
  have hsum :
      integrateCodes (codeExtend c) (i.val + 1) =
        integrateCodes (codeExtend c) i.val +
          lazyTwoDimensionalStep (codeExtend c i.val) := by
    simp [integrateCodes, Finset.sum_range_succ]
  have hdiff :
      integrateCodes (codeExtend c) (i.val + 1) -
          integrateCodes (codeExtend c) i.val = lazyTwoDimensionalStep (c.val i) := by
    rw [hsum, hcode]
    abel
  change stepCode (integrateCodes (codeExtend c) (i.val + 1) -
      integrateCodes (codeExtend c) i.val) = c.val i
  rw [hdiff]
  exact stepCode_lazyTwoDimensionalStep (c.val i)

end DirectedDistances.KMSW
