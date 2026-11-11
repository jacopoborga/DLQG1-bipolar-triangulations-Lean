module

public import DirectedDistances.RandomWalk.SecondCoordinateUnbounded
public import DirectedDistances.RandomWalk.ExcursionWordSupport
public import DirectedDistances.RandomWalk.UIBHBOTEncodingGeneral
public import DirectedDistances.KMSW.UIBHBOTBlockRecords






public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open DirectedDistances.KMSW

/-- For any family of stopped excursion words, block boundaries force the first coordinate -/
theorem uibhbotConcatWalk_fst_unbounded_below_of_stopped
    (w : ℤ → List (Fin 3)) (hw : ∀ k, IsStoppedExcursionWord (w k)) :
    ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).1 ≤ a := by
  intro a
  let k : ℕ := (-a).toNat
  have hka : -(k : ℤ) ≤ a := by
    dsimp [k]
    by_cases ha : a < 0
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ -a)]
      omega
    · have ha0 : 0 ≤ a := by omega
      have hz : (-a).toNat = 0 := by
        simp [Int.toNat_of_nonpos (show -a ≤ 0 by omega)]
      rw [hz]
      omega
  have htime0 : 0 ≤ uibhbotBlockBoundary w (k : ℤ) := by
    rw [uibhbotBlockBoundary,
      ite_eq_left (show (0 : ℤ) ≤ (k : ℤ) by positivity)]
    exact Finset.sum_nonneg fun i hi => Int.natCast_nonneg _
  have htime :
      ((uibhbotBlockBoundary w (k : ℤ)).toNat : ℤ) =
        uibhbotBlockBoundary w (k : ℤ) := Int.toNat_of_nonneg htime0
  refine ⟨(uibhbotBlockBoundary w (k : ℤ)).toNat, ?_⟩
  rw [htime]
  calc
    (uibhbotConcatWalk w (uibhbotBlockBoundary w (k : ℤ))).1 = -(k : ℤ) :=
      uibhbotConcatWalk_stopped_blockBoundary_fst w hw (k : ℤ)
    _ ≤ a := hka

/-- Almost surely, every word in the canonical family is a stopped excursion word. -/
theorem ae_uibhbotWordFamily_all_stopped :
    ∀ᵐ w ∂uibhbotWordFamilyLaw, ∀ k : ℤ, IsStoppedExcursionWord (w k) := by
  rw [ae_all_iff]
  intro k
  have heval := uibhbotWordFamilyLaw_map_eval k
  have hae := ae_isStoppedExcursionWord_excursionWordLaw
  rw [← heval] at hae
  exact (ae_map_iff (measurable_pi_apply k).aemeasurable
    (MeasurableSet.of_discrete)).mp hae



theorem ae_uibhbotConcatWalk_fst_unbounded_below :
    ∀ᵐ w ∂uibhbotWordFamilyLaw, ∀ a : ℤ, ∃ n : ℕ,
      (uibhbotConcatWalk w n).1 ≤ a := by
  filter_upwards [ae_uibhbotWordFamily_all_stopped] with w hw
  exact uibhbotConcatWalk_fst_unbounded_below_of_stopped w hw

end DirectedDistances.RandomWalk
