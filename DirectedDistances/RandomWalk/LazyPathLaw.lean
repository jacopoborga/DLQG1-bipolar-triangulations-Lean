/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyPath
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.BigOperators.Fin







public section
namespace DirectedDistances.RandomWalk

open scoped ENNReal

/-- The source path carrier inherits the canonical coordinate/subtype sigma algebra. -/
instance measurableSpaceLazyPath (n : ℕ) : MeasurableSpace (LazyPath n) := by
  unfold LazyPath
  infer_instance

/-- Singleton source paths are measurable in the inherited discrete structure. -/
instance measurableSingletonClassLazyPath (n : ℕ) : MeasurableSingletonClass (LazyPath n) := by
  unfold LazyPath
  infer_instance

/-- The nonnegative subclass inherits its source path sigma algebra. -/
instance measurableSpaceNonnegativeLazyPath (n : ℕ) : MeasurableSpace (NonnegativeLazyPath n) := by
  unfold NonnegativeLazyPath
  infer_instance

/-- Singleton nonnegative paths are measurable as actual subtype singletons. -/
instance measurableSingletonClassNonnegativeLazyPath (n : ℕ) :
    MeasurableSingletonClass (NonnegativeLazyPath n) := by
  unfold NonnegativeLazyPath
  infer_instance

/-- Integrate a finite word of increments -1,0,1 on the actual time carrier. -/
@[expose] def lazyWordValues {n : ℕ} (w : Fin n → Fin 3) (j : Fin (n + 1)) : ℤ :=
  ∑ i : Fin n with i.val < j.val, ((w i : ℤ) - 1)

/-- Every integrated word starts at zero. -/
theorem lazyWordValues_zero {n : ℕ} (w : Fin n → Fin 3) : lazyWordValues w 0 = 0 := by
  simp only [lazyWordValues, Fin.val_zero, not_lt_zero, Finset.filter_false, Finset.sum_empty]

/-- The increment of the integrated word is the literal encoded step. -/
theorem lazyWordValues_step {n : ℕ} (w : Fin n → Fin 3) (j : Fin n) :
    lazyWordValues w j.succ - lazyWordValues w j.castSucc = (w j : ℤ) - 1 := by
  classical
  have he : (Finset.univ.filter (fun i : Fin n => i.val < j.succ.val)) =
      insert j (Finset.univ.filter (fun i : Fin n => i.val < j.castSucc.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ,
      Fin.val_castSucc, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (by have : i.val ≠ j.val := fun h => hij (Fin.ext h); omega)
    · rintro (rfl | hi) <;> omega
  unfold lazyWordValues
  rw [he, Finset.sum_insert (by simp only [Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.val_castSucc, lt_self_iff_false, not_false_eq_true])]
  exact add_sub_cancel_right _ _

/-- The integrated word is an actual lazy path with all source obligations proved. -/
@[expose] def lazyPathOfWord {n : ℕ} (w : Fin n → Fin 3) : LazyPath n :=
  ⟨lazyWordValues w, lazyWordValues_zero w, fun i => by
    rw [lazyWordValues_step]
    apply lazy_increment_iff.mpr
    have h := (w i).isLt
    constructor <;> omega⟩

/-- Recover the actual finite increment word of a source lazy path. -/
@[expose] def lazyPathWord {n : ℕ} (p : LazyPath n) (i : Fin n) : Fin 3 :=
  ⟨(p.val i.succ - p.val i.castSucc + 1).toNat, by
    have h := lazy_increment_iff.mp (p.property.2 i)
    omega⟩

/-- Casting a recovered code back to integers recovers step+1 exactly. -/
theorem lazyPathWord_coe {n : ℕ} (p : LazyPath n) (i : Fin n) :
    (lazyPathWord p i : ℤ) = p.val i.succ - p.val i.castSucc + 1 := by
  change ((p.val i.succ - p.val i.castSucc + 1).toNat : ℤ) = _
  apply Int.toNat_of_nonneg
  have h := lazy_increment_iff.mp (p.property.2 i)
  omega

/-- Word integration followed by increment extraction is the identity. -/
theorem lazyPathWord_ofWord {n : ℕ} (w : Fin n → Fin 3) :
    lazyPathWord (lazyPathOfWord w) = w := by
  funext i
  apply Fin.ext
  have h := lazyPathWord_coe (lazyPathOfWord w) i
  change (lazyPathWord (lazyPathOfWord w) i : ℤ) =
    lazyWordValues w i.succ - lazyWordValues w i.castSucc + 1 at h
  rw [lazyWordValues_step] at h
  omega

/-- Extracting the increments and integrating recovers every source coordinate. -/
theorem lazyPathOfWord_word {n : ℕ} (p : LazyPath n) :
    lazyPathOfWord (lazyPathWord p) = p := by
  apply Subtype.ext
  funext j
  change lazyWordValues (lazyPathWord p) j = p.val j
  induction j using Fin.induction with
  | zero => rw [lazyWordValues_zero, p.property.1]
  | succ i ih =>
    have h := lazyWordValues_step (lazyPathWord p) i
    rw [lazyPathWord_coe] at h
    change lazyWordValues (lazyPathWord p) i.castSucc = p.val i.castSucc at ih
    omega

/-- The actual n-step lazy paths are in bijection with all n-letter step words. -/
@[expose] def lazyPathWordEquiv (n : ℕ) : LazyPath n ≃ (Fin n → Fin 3) where
  toFun := lazyPathWord
  invFun := lazyPathOfWord
  left_inv := lazyPathOfWord_word
  right_inv := lazyPathWord_ofWord

/-- There are exactly 3^n actual n-step source paths. -/
theorem card_lazyPath (n : ℕ) : Fintype.card (LazyPath n) = 3 ^ n := by
  rw [Fintype.card_congr (lazyPathWordEquiv n), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- The source path carrier is nonempty, including n=0. -/
instance nonempty_lazyPath (n : ℕ) : Nonempty (LazyPath n) :=
  ⟨lazyPathOfWord (fun _ => (1 : Fin 3))⟩

/-- The actual constant weights on the finite source path carrier sum to one. -/
theorem sum_uniform_lazyPath (n : ℕ) :
    (∑ _p : LazyPath n, (Fintype.card (LazyPath n) : ℝ≥0∞)⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply ENNReal.mul_inv_cancel
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _

/-- The literal uniform PMF on the actual source n-step lazy paths. -/
@[expose] noncomputable def uniformLazyPath (n : ℕ) : PMF (LazyPath n) :=
  PMF.ofFintype (fun _ => (Fintype.card (LazyPath n) : ℝ≥0∞)⁻¹) (sum_uniform_lazyPath n)

/-- Every actual source lazy path has the same uniform point mass. -/
theorem uniformLazyPath_apply {n : ℕ} (p : LazyPath n) :
    uniformLazyPath n p = (Fintype.card (LazyPath n) : ℝ≥0∞)⁻¹ := rfl

/-- Each actual source path has mass 3^(-n), derived from the word bijection. -/
theorem uniformLazyPath_apply_pow {n : ℕ} (p : LazyPath n) :
    uniformLazyPath n p = (1 / 3 : ℝ≥0∞) ^ n := by
  rw [uniformLazyPath_apply, card_lazyPath]
  simp only [Nat.cast_pow, Nat.cast_ofNat, one_div, ENNReal.inv_pow]

/-- The actual image PMF under the proved finite Pitman map. -/
@[expose] noncomputable def pitmanLazyPathLaw (n : ℕ) : PMF (NonnegativeLazyPath n) :=
  (uniformLazyPath n).map lazyPhi

/-- The point mass of the actual image is the proved fiber count divided by
its actual uniform-domain cardinality, without assuming the desired law. -/
theorem pitmanLazyPathLaw_apply_card {n : ℕ} (q : NonnegativeLazyPath n) :
    pitmanLazyPathLaw n q =
      ((q.val.val (Fin.last n)).toNat + 1 : ℕ) / (Fintype.card (LazyPath n) : ℝ≥0∞) := by
  classical
  rw [pitmanLazyPathLaw, PMF.map_apply, tsum_fintype]
  simp_rw [uniformLazyPath_apply, eq_comm (a := q), ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : Fintype.card {p : LazyPath n // lazyPhi p = q} =
      (q.val.val (Fin.last n)).toNat + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_lazyPhiFiber q
  rw [← Fintype.card_subtype, hc]
  rfl

/-- The actual Pitman image mass is the endpoint weight times 3^(-n). -/
theorem pitmanLazyPathLaw_apply {n : ℕ} (q : NonnegativeLazyPath n) :
    pitmanLazyPathLaw n q =
      (((q.val.val (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ n := by
  rw [pitmanLazyPathLaw_apply_card, card_lazyPath]
  simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul, ENNReal.inv_pow]

/-- The endpoint-weighted nonnegative path masses are genuinely normalized. -/
theorem hasSum_endpoint_weighted_nonnegative_lazyPath (n : ℕ) :
    HasSum (fun q : NonnegativeLazyPath n =>
      (((q.val.val (Fin.last n)).toNat + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ n) 1 := by
  apply (pitmanLazyPathLaw n).hasSum_coe_one.congr_fun
  intro q
  exact (pitmanLazyPathLaw_apply q).symm

end DirectedDistances.RandomWalk
