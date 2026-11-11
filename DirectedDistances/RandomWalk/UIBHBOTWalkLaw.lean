module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel
public import DirectedDistances.KMSW.UIBHBOTWholePlaneWord

/-! # The UIBHBOT two-sided walk law

The code-built integrated walk has the same law as the two-sided concatenation of iid stopped -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5

private theorem measurable_wholePlaneWordIntegralAt (t : ℤ) :
    Measurable (fun W : ℤ → Fin 3 => wholePlaneWordIntegral W t) := by
  have hm (xs : List ℤ) (f : ℤ → ℤ) :
      Measurable (fun W : ℤ → Fin 3 =>
        (xs.map (fun i => lazyTwoDimensionalStep (W (f i)))).sum) := by
    induction xs with
    | nil => exact measurable_const
    | cons a xs ih =>
        exact ((measurable_of_countable lazyTwoDimensionalStep).comp
          (measurable_pi_apply (f a))).add ih
  unfold wholePlaneWordIntegral
  split
  · exact hm _ id
  · exact (hm _ (fun i => -i - 1)).neg

/-- The integrated code path is measurable into the product sigma-algebra on -/
theorem measurable_wholePlaneWordIntegralPath :
    Measurable (fun W : ℤ → Fin 3 => fun t : ℤ => wholePlaneWordIntegral W t) :=
  measurable_pi_iff.mpr measurable_wholePlaneWordIntegralAt

private theorem flatMap_map_words {α β : Type*} (xs : List α) (f : α → List β) :
    xs.flatMap f = (xs.map f).flatMap id := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem finRange_map_val_eq_range (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.finRange_succ]
      change 0 :: ((List.finRange n).map Fin.succ).map Fin.val = List.range (n + 1)
      have htail : ((List.finRange n).map Fin.succ).map Fin.val =
          List.map Nat.succ (List.map Fin.val (List.finRange n)) := by
        simp only [List.map_map, Function.comp_def, Fin.val_succ]
      rw [htail, ih]
      simp [List.range_succ_eq_map]

private theorem rangeCast_eq_finRange (n : ℕ) :
    (List.range n).map (fun k : ℕ => (k : ℤ)) =
      (List.finRange n).map (fun i : Fin n => (i : ℤ)) := by
  rw [← finRange_map_val_eq_range n]
  simp only [List.map_map, Function.comp_def]

private theorem flatMap_map_index {α β γ : Type*} (xs : List α) (g : α → β)
    (f : β → List γ) :
    xs.flatMap (fun x => f (g x)) = (xs.map g).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem rangeCast_flatMap_finRange {β : Type*} (n : ℕ) (f : ℤ → List β) :
    ((List.range n).map (fun k : ℕ => (k : ℤ))).flatMap f =
      (List.finRange n).flatMap (fun i : Fin n => f (i : ℤ)) := by
  rw [rangeCast_eq_finRange n]
  exact (flatMap_map_index (List.finRange n) (fun i : Fin n => (i : ℤ)) f).symm

private def walkFromWordBlocks (n : ℕ) (blocks : Fin n → List (Fin 3)) : ℤ × ℤ :=
  ((((List.finRange n).flatMap blocks).take n).map lazyTwoDimensionalStep).sum

private theorem measurable_uibhbotConcatWalkAt (t : ℤ) :
    Measurable (fun w : ℤ → List (Fin 3) => uibhbotConcatWalk w t) := by
  by_cases ht : 0 ≤ t
  · let n := t.toNat
    have hblocks : Measurable
        (fun w : ℤ → List (Fin 3) => fun i : Fin n => w (i : ℤ)) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℤ)
    have hfinish : Measurable (walkFromWordBlocks n) := measurable_of_countable _
    have hPoint (w : ℤ → List (Fin 3)) :
        uibhbotConcatWalk w t = walkFromWordBlocks n (fun i => w (i : ℤ)) := by
      rw [uibhbotConcatWalk, if_pos ht, walkFromWordBlocks]
      simp only [bind_pure_comp]
      change (((((List.range n).map (fun k : ℕ => (k : ℤ))).flatMap
          (fun k : ℤ => w k)).take n).map lazyTwoDimensionalStep).sum =
        ((((List.finRange n).flatMap (fun i : Fin n => w (i : ℤ))).take n).map
          lazyTwoDimensionalStep).sum
      rw [rangeCast_flatMap_finRange]
    have hEq : (fun w : ℤ → List (Fin 3) => uibhbotConcatWalk w t) =
        fun w => walkFromWordBlocks n (fun i => w (i : ℤ)) := funext hPoint
    rw [hEq]
    exact hfinish.comp hblocks
  · let n := (-t).toNat
    have hblocks : Measurable
        (fun w : ℤ → List (Fin 3) => fun i : Fin n => (w (-(i : ℤ) - 1)).reverse) :=
      measurable_pi_iff.mpr fun i =>
        (measurable_of_countable List.reverse).comp (measurable_pi_apply (-(i : ℤ) - 1))
    have hfinish : Measurable (walkFromWordBlocks n) := measurable_of_countable _
    have hPoint (w : ℤ → List (Fin 3)) :
        uibhbotConcatWalk w t =
          -(walkFromWordBlocks n (fun i => (w (-(i : ℤ) - 1)).reverse)) := by
      rw [uibhbotConcatWalk, if_neg ht, walkFromWordBlocks]
      simp only [bind_pure_comp]
      change -(((((List.range n).map (fun k : ℕ => (k : ℤ))).flatMap
          (fun k : ℤ => (w (-k - 1)).reverse)).take n).map
          lazyTwoDimensionalStep).sum =
        -(((((List.finRange n).flatMap
          (fun i : Fin n => (w (-(i : ℤ) - 1)).reverse)).take n).map
          lazyTwoDimensionalStep).sum)
      rw [rangeCast_flatMap_finRange]
    have hEq : (fun w : ℤ → List (Fin 3) => uibhbotConcatWalk w t) =
        fun w => -(walkFromWordBlocks n (fun i => (w (-(i : ℤ) - 1)).reverse)) := funext hPoint
    rw [hEq]
    exact hfinish.comp hblocks |>.neg

/-- The iid stopped-block concatenation is measurable into the product sigma-algebra on -/
theorem measurable_uibhbotConcatWalk : Measurable uibhbotConcatWalk :=
  measurable_pi_iff.mpr measurable_uibhbotConcatWalkAt

/-- The integrated two-sided code path and the iid stopped-block concatenation have the same
law. The equality uses the almost-sure stopped-block/code agreement and preserves the source -/
theorem uibhbotCodeLawRel_map_walk :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun W : ℤ → Fin 3 => fun t : ℤ => wholePlaneWordIntegral W t) =
      uibhbotWordFamilyLaw.map uibhbotConcatWalk := by
  change (uibhbotWordFamilyLaw.map uibhbotCodeWordRel).map
      (fun W : ℤ → Fin 3 => fun t : ℤ => wholePlaneWordIntegral W t) = _
  rw [Measure.map_map measurable_wholePlaneWordIntegralPath measurable_uibhbotCodeWordRel]
  apply Measure.map_congr
  filter_upwards [uibhbotWordFamilyLaw_ae_codeWordRel] with w hw
  obtain ⟨hwords, hcode⟩ := hw
  funext t
  change wholePlaneWordIntegral (uibhbotCodeWordRel w) t = uibhbotConcatWalk w t
  rw [hcode]
  exact wholePlaneWordIntegral_uibhbotCodeWord w (fun k => (hwords k).1) t

end DirectedDistances.RandomWalk
end
