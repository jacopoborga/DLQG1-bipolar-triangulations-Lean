/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantBridgePaddingEmbedding
public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteRootWindow
public import DirectedDistances.KMSW.FiniteWalkClass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! # The finite admissible carrier toward Proposition 3.9

These identities concern the implemented source step alphabet. The existing
legal-step convention qualification in `FiniteWalkClass` remains in force. Translation of the
walk by `(0, ρ-1)` changes neither its letters nor the `n` available edge roots. -/

public section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap
open scoped ENNReal BigOperators

private theorem displacement_ofFn (m : ℕ) (w : Fin m → Fin 3) :
    paddingWordDisplacement (List.ofFn w) =
      ∑ i : Fin m, lazyTwoDimensionalStep (w i) := by
  induction m with
  | zero => simp [paddingWordDisplacement]
  | succ m ih =>
      rw [List.ofFn_succ', List.concat_eq_append, paddingWordDisplacement_append, ih,
        Fin.sum_univ_castSucc]
      simp [paddingWordDisplacement]

private theorem take_ofFn (m j : ℕ) (hj : j ≤ m) (w : Fin m → Fin 3) :
    List.ofFn (fun i : Fin j => w (Fin.castLE hj i)) = (List.ofFn w).take j := by
  apply List.ext_get
  · simp [hj]
  · intro i hi₁ hi₂
    simp [Fin.castLE]

/-- Helper toward Proposition 3.9: list partial displacement agrees with
the integrated finite KMSW word at every time through its final step. -/
theorem paddingWordDisplacement_ofFn_take_eq_integrateCodes
    (n : ℕ) (w : Fin (n - 1) → Fin 3) (j : ℕ) (hj : j ≤ n - 1) :
    paddingWordDisplacement ((List.ofFn w).take j) =
      integrateCodes (finiteCodeExtend w) j := by
  rw [← take_ofFn (n - 1) j hj w, displacement_ofFn]
  rw [integrateCodes, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [finiteCodeExtend, lt_of_lt_of_le i.isLt hj, Fin.castLE]

private theorem translated_position (ρ n : ℕ) (w : Fin (n - 1) → Fin 3)
    (j : ℕ) (hj : j ≤ n - 1) :
    paddingWordPosition (0, ((ρ - 1 : ℕ) : ℤ)) (List.ofFn w) j =
      ((integrateCodes (finiteCodeExtend w) j).1,
        ((ρ - 1 : ℕ) : ℤ) + (integrateCodes (finiteCodeExtend w) j).2) := by
  rw [paddingWordPosition, paddingWordDisplacement_ofFn_take_eq_integrateCodes n w j hj]
  apply Prod.ext <;> simp

/-- Helper toward Proposition 3.9: the exact admissible finite word is a
length-`n-1` closed-quadrant bridge from `(0,ρ-1)` to `(ℓ-1,0)` after translation.
The equivalence retains every integer time, including both endpoints. -/
theorem kmswWalkAdmissible_iff_quadrantBridgeWords
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (_hn : 1 ≤ n)
    (w : Fin (n - 1) → Fin 3) :
    KMSWWalkAdmissible ℓ ρ n w ↔
      ∃ b : QuadrantBridgeWords (n - 1) (0, ρ - 1) (ℓ - 1, 0),
        b.val = List.ofFn w := by
  have hℓcast : ((ℓ - 1 : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by omega
  have hρcast : ((ρ - 1 : ℕ) : ℤ) = (ρ : ℤ) - 1 := by omega
  constructor
  · rintro ⟨hend, hcone⟩
    refine ⟨⟨List.ofFn w, List.length_ofFn, ?_, ?_⟩, rfl⟩
    · simp only [Nat.cast_zero]
      rw [translated_position ρ n w (n - 1) le_rfl, hend]
      apply Prod.ext <;> simp [hℓcast, hρcast]
    · intro j hj
      have hc := hcone j (Finset.mem_range.mpr (by omega))
      simp only [Nat.cast_zero]
      rw [translated_position ρ n w j hj]
      simp only [hρcast]
      constructor <;> omega
  · rintro ⟨b, hb⟩
    have hend := b.property.2.1
    have hcone := b.property.2.2
    simp only [Nat.cast_zero] at hend hcone
    rw [hb, translated_position ρ n w (n - 1) le_rfl] at hend
    have hx := congrArg Prod.fst hend
    have hy := congrArg Prod.snd hend
    simp only [hℓcast, hρcast] at hx hy
    refine ⟨?_, ?_⟩
    · apply Prod.ext <;> omega
    · intro j hj
      have hj' : j ≤ n - 1 := by
        have := Finset.mem_range.mp hj
        omega
      have hc := hcone j hj'
      rw [hb, translated_position ρ n w j hj'] at hc
      simp only [hρcast] at hc
      constructor <;> omega

/-- Helper toward Proposition 3.9: words indexed by `Fin m` are equivalent
to lists of exactly `m` letters, through `List.ofFn`. -/
@[expose] def uibotFiniteWordEquiv (m : ℕ) :
    (Fin m → Fin 3) ≃ {w : List (Fin 3) // w.length = m} where
  toFun w := ⟨List.ofFn w, by simp⟩
  invFun w i := w.1.get (Fin.cast w.2.symm i)
  left_inv w := by funext i; simp
  right_inv w := by
    apply Subtype.ext
    change List.ofFn (fun i : Fin m => w.1.get (Fin.cast w.2.symm i)) = w.1
    rw [List.ofFn_congr w.2.symm]
    simp [Fin.cast]

/-- Helper toward Proposition 3.9: `List.ofFn` bijects the actual admissible
word class with the translated quadrant-bridge list carrier. -/
@[expose] noncomputable def kmswWalkClassEquivQuadrantBridgeWords
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n) :
    KMSWWalkClass ℓ ρ n ≃
      QuadrantBridgeWords (n - 1) (0, ρ - 1) (ℓ - 1, 0) := by
  classical
  let f : KMSWWalkClass ℓ ρ n →
      QuadrantBridgeWords (n - 1) (0, ρ - 1) (ℓ - 1, 0) := fun w =>
    ⟨List.ofFn w.val, by
      obtain ⟨b, hb⟩ :=
        (kmswWalkAdmissible_iff_quadrantBridgeWords ℓ ρ n hℓ hρ hn w.1).mp w.2
      rw [← hb]
      exact b.property⟩
  have hf (w : KMSWWalkClass ℓ ρ n) : (f w).val = List.ofFn w.val := rfl
  apply Equiv.ofBijective f
  constructor
  · intro w z h
    apply Subtype.ext
    apply List.ofFn_injective
    rw [← hf w, ← hf z, h]
  · intro b
    let w := (uibotFiniteWordEquiv (n - 1)).symm ⟨b.1, b.2.1⟩
    have hw : List.ofFn w = b.val :=
      congrArg Subtype.val ((uibotFiniteWordEquiv (n - 1)).apply_symm_apply ⟨b.1, b.2.1⟩)
    have ha : KMSWWalkAdmissible ℓ ρ n w :=
      (kmswWalkAdmissible_iff_quadrantBridgeWords ℓ ρ n hℓ hρ hn w).mpr ⟨b, hw.symm⟩
    refine ⟨⟨w, ha⟩, ?_⟩
    apply Subtype.ext
    exact (hf ⟨w, ha⟩).trans hw

/-- Helper toward Proposition 3.9: the bridge equivalence sends each
admissible word to precisely its list of letters. -/
@[simp] theorem kmswWalkClassEquivQuadrantBridgeWords_apply_val
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (w : KMSWWalkClass ℓ ρ n) :
    (kmswWalkClassEquivQuadrantBridgeWords ℓ ρ n hℓ hρ hn w).val =
      List.ofFn w.val := rfl

/-- Helper toward Proposition 3.9: nonempty admissible words force the
size-boundary congruence `n+ℓ+ρ ≡ 0 (mod 3)` for the implemented source steps. -/
theorem kmswWalkAdmissible_size_modEq
    (ℓ ρ n : ℕ) (hn : 1 ≤ n) (w : Fin (n - 1) → Fin 3)
    (hw : KMSWWalkAdmissible ℓ ρ n w) :
    n + ℓ + ρ ≡ 0 [MOD 3] := by
  have hd := paddingWordDisplacement_difference_modEq (List.ofFn w)
  have he := paddingWordDisplacement_ofFn_take_eq_integrateCodes n w (n - 1) le_rfl
  rw [List.take_of_length_le (by simp)] at he
  rw [he, hw.1, List.length_ofFn] at hd
  simp only [Int.ModEq] at hd
  unfold Nat.ModEq
  omega

/-- Helper toward Proposition 3.9: nonemptiness of the admissible word
carrier implies the necessary size-boundary congruence. -/
theorem kmswWalkClass_nonempty_size_modEq
    (ℓ ρ n : ℕ) (hn : 1 ≤ n) (hne : Nonempty (KMSWWalkClass ℓ ρ n)) :
    n + ℓ + ρ ≡ 0 [MOD 3] := by
  obtain ⟨w⟩ := hne
  exact kmswWalkAdmissible_size_modEq ℓ ρ n hn w.val w.property

section WordLaw
local instance : MeasurableSpace (Fin 3) := ⊤

/-- Helper toward Proposition 3.9: the iid admissibility probability is
exactly the number of translated bridges divided by `3^(n-1)`. -/
theorem uibotFiniteIIDWordLaw_admissible_eq_card_quadrantBridgeWords
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n) :
    uibotFiniteIIDWordLaw n {w | KMSWWalkAdmissible ℓ ρ n w} =
      (Nat.card (QuadrantBridgeWords (n - 1) (0, ρ - 1) (ℓ - 1, 0)) : ℝ≥0∞) /
        (3 : ℝ≥0∞) ^ (n - 1) := by
  rw [uibotFiniteIIDWordLaw_eq_uniform, uniformCountingMeasure, Measure.smul_apply,
    smul_eq_mul, Measure.count_apply (Set.to_countable _).measurableSet,
    Set.encard, ENat.card_eq_coe_natCard]
  have hc : Nat.card {w : Fin (n - 1) → Fin 3 | KMSWWalkAdmissible ℓ ρ n w} =
      Nat.card (QuadrantBridgeWords (n - 1) (0, ρ - 1) (ℓ - 1, 0)) :=
    Nat.card_congr (kmswWalkClassEquivQuadrantBridgeWords ℓ ρ n hℓ hρ hn)
  rw [hc]
  simp [Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv, mul_comm]

end WordLaw
end DirectedDistances.PaperProofs.Section3
