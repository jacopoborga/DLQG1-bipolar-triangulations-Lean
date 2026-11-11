module

public import DirectedDistances.RandomWalk.UIBHBOTPastRUnbounded
public import DirectedDistances.RandomWalk.ExcursionWordSupport






public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- The non-lazy letters of a word, in their original order.
k140 step 6). -/
@[expose] def excursionSkeleton (v : List (Fin 3)) : List (Fin 3) :=
  v.filter (fun c => c ≠ 1)

@[expose] def excursionSkeletonGapLengthsAux (pending : ℕ) : List (Fin 3) → List ℕ
  | [] => [pending]
  | c :: cs =>
      if c = 1 then excursionSkeletonGapLengthsAux (pending + 1) cs
      else pending :: excursionSkeletonGapLengthsAux 0 cs

/-- The lazy-run lengths in a word, including the terminal run after its skeleton.
k140 step 6). -/
@[expose]
def excursionSkeletonGapLengths (v : List (Fin 3)) : List ℕ :=
  excursionSkeletonGapLengthsAux 0 v

/-- The number of code-2 letters in a word.
k140 step 6). -/
@[expose] def excursionTwoCount (v : List (Fin 3)) : ℕ := v.count 2

private theorem excursionSkeletonGapLengthsAux_sum (pending : ℕ) (v : List (Fin 3)) :
    (excursionSkeletonGapLengthsAux pending v).sum = pending + v.count 1 := by
  induction v generalizing pending with
  | nil => simp [excursionSkeletonGapLengthsAux]
  | cons c cs ih =>
      by_cases hc : c = 1
      · simp [excursionSkeletonGapLengthsAux, hc, ih, Nat.add_assoc]
        omega
      · simp [excursionSkeletonGapLengthsAux, hc, ih]

private theorem excursionSkeletonGapLengthsAux_append_zero (pending : ℕ)
    (v : List (Fin 3)) :
    excursionSkeletonGapLengthsAux pending (v ++ [0]) =
      excursionSkeletonGapLengthsAux pending v ++ [0] := by
  induction v generalizing pending with
  | nil => simp [excursionSkeletonGapLengthsAux]
  | cons c cs ih =>
      by_cases hc : c = 1
      · simp [excursionSkeletonGapLengthsAux, hc, ih]
      · simp [excursionSkeletonGapLengthsAux, hc, ih 0]

private theorem excursionWordSecondSum_eq_count (v : List (Fin 3)) :
    ((v.map lazyTwoDimensionalStep).sum).2 =
      (v.count 1 : ℤ) - (v.count 2 : ℤ) := by
  induction v with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, Prod.snd_add, List.count_cons]
      rw [ih]
      fin_cases c <;> simp [lazyTwoDimensionalStep] <;> omega




theorem excursionSkeletonGapLengths_terminal_zero (v : List (Fin 3))
    (hv : IsStoppedExcursionWord v) :
    (excursionSkeletonGapLengths v).getLast? = some 0 := by
  rcases hv with ⟨hpos, htotal, hprefix⟩
  have hne : v ≠ [] := by
    intro h
    subst v
    simp at hpos
  let pre := v.dropLast
  have hdecomp : pre ++ [v.getLast hne] = v := by
    exact List.dropLast_append_getLast hne
  have hprelen : pre.length < v.length := by
    rw [← hdecomp]
    simp
  have hprefixPre : -1 < ((pre.map lazyTwoDimensionalStep).sum).1 := by
    have h := hprefix pre.length hprelen
    have htake : v.take pre.length = pre := by
      rw [← hdecomp]
      simp
    rw [htake] at h
    exact h
  have hsum : ((v.map lazyTwoDimensionalStep).sum).1 =
      ((pre.map lazyTwoDimensionalStep).sum).1 +
        (lazyTwoDimensionalStep (v.getLast hne)).1 := by
    have hsum' := congrArg (fun w : List (Fin 3) =>
      ((w.map lazyTwoDimensionalStep).sum).1) hdecomp
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Prod.fst_add] at hsum'
    exact hsum'.symm
  let c : Fin 3 := v.getLast hne
  have hlastStep : (lazyTwoDimensionalStep (v.getLast hne)).1 = -1 := by
    have hpreNonneg : 0 ≤ ((pre.map lazyTwoDimensionalStep).sum).1 := by omega
    have hstepGe : -1 ≤ (lazyTwoDimensionalStep (v.getLast hne)).1 := by
      have hcast : (0 : ℤ) ≤ (c : ℤ) := by positivity
      simp only [lazyTwoDimensionalStep]
      omega
    rw [hsum] at htotal
    omega
  have hlastCode : c = 0 := by
    change (c.val : ℤ) - 1 = -1 at hlastStep
    have hval : c.val = 0 := by omega
    exact Fin.ext hval
  have hlast : v.getLast? = some 0 := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne]
    exact congrArg some (by simpa [c] using hlastCode)
  have hlastCode' : v.getLast hne = 0 := by simpa [c] using hlastCode
  have hgap : excursionSkeletonGapLengths v =
      excursionSkeletonGapLengthsAux 0 pre ++ [0] := by
    calc
      excursionSkeletonGapLengths v = excursionSkeletonGapLengthsAux 0 v := rfl
      _ = excursionSkeletonGapLengthsAux 0 (pre ++ [v.getLast hne]) :=
        congrArg (excursionSkeletonGapLengthsAux 0) hdecomp.symm
      _ = excursionSkeletonGapLengthsAux 0 pre ++ [0] := by
        rw [hlastCode']
        exact excursionSkeletonGapLengthsAux_append_zero 0 pre
  rw [hgap]
  simp

private theorem excursionSkeletonGapLengthsAux_length (pending : ℕ) (v : List (Fin 3)) :
    (excursionSkeletonGapLengthsAux pending v).length = (excursionSkeleton v).length + 1 := by
  induction v generalizing pending with
  | nil => simp [excursionSkeletonGapLengthsAux, excursionSkeleton]
  | cons c cs ih =>
      by_cases hc : c = 1
      · simpa [excursionSkeletonGapLengthsAux, excursionSkeleton, hc] using ih (pending + 1)
      · simpa [excursionSkeletonGapLengthsAux, excursionSkeleton, hc] using ih 0




theorem excursionSkeletonGapLengths_length (v : List (Fin 3)) :
    (excursionSkeletonGapLengths v).length = (excursionSkeleton v).length + 1 := by
  simpa [excursionSkeletonGapLengths] using excursionSkeletonGapLengthsAux_length 0 v




theorem excursionSkeletonGapLengths_sum (v : List (Fin 3)) :
    (excursionSkeletonGapLengths v).sum = v.count 1 := by
  simpa [excursionSkeletonGapLengths] using excursionSkeletonGapLengthsAux_sum 0 v








theorem excursionWordRDisplacement_eq_gap_sum_sub_twoCount (v : List (Fin 3)) :
    uibhbotWordRDisplacement v =
      (excursionSkeletonGapLengths v).sum - (excursionTwoCount v : ℤ) := by
  rw [uibhbotWordRDisplacement, excursionWordSecondSum_eq_count,
    excursionSkeletonGapLengths_sum, excursionTwoCount]

end DirectedDistances.RandomWalk
