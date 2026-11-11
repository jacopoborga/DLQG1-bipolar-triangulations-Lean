module

public import DirectedDistances.RandomWalk.ExcursionBlockFlatLaw
public import DirectedDistances.RandomWalk.ExcursionSkeletonGaps





public section
namespace DirectedDistances.RandomWalk

local notation "passageFst" u:max => Prod.fst (List.sum (List.map lazyTwoDimensionalStep u))

private theorem passageFst_append (u v : List (Fin 3)) :
    passageFst (u ++ v) = passageFst u + passageFst v := by
  simp [List.map_append, List.sum_append]

private theorem passageFst_eq_count (u : List (Fin 3)) :
    passageFst u = (u.count 2 : ℤ) - (u.count 0 : ℤ) := by
  induction u with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, Prod.fst_add, List.count_cons]
      rw [ih]
      fin_cases c <;> simp [lazyTwoDimensionalStep] <;> omega

private theorem excursionSkeleton_length_cons (c : Fin 3) (cs : List (Fin 3)) :
    (excursionSkeleton (c :: cs)).length =
      (if c = 1 then (excursionSkeleton cs).length
       else (excursionSkeleton cs).length + 1) := by
  by_cases hc : c = 1
  · simp [excursionSkeleton, hc]
  · simp [excursionSkeleton, hc]

private theorem excursionSkeleton_length_eq_counts (u : List (Fin 3)) :
    (excursionSkeleton u).length = u.count 0 + u.count 2 := by
  induction u with
  | nil => simp [excursionSkeleton]
  | cons c cs ih =>
      rw [excursionSkeleton_length_cons]
      fin_cases c <;> simp [ih] <;> omega




theorem excursionPassage_getLast {k : ℕ} {u : List (Fin 3)}
    (h : excursionPassage k u) : u.getLast? = some 0 := by
  rcases h with ⟨hpos, htotal, hprefix⟩
  have hne : u ≠ [] := by
    intro he
    subst u
    simp at hpos
  let pre := u.dropLast
  have hdecomp : pre ++ [u.getLast hne] = u := List.dropLast_append_getLast hne
  have hprelen : pre.length < u.length := by
    rw [← hdecomp]
    simp
  have hprefixPre : -(k : ℤ) < passageFst pre := by
    have h := hprefix pre.length hprelen
    have htake : u.take pre.length = pre := by
      rw [← hdecomp]
      simp
    rw [htake] at h
    exact h
  have hsum : passageFst u = passageFst pre +
      (lazyTwoDimensionalStep (u.getLast hne)).1 := by
    have hsum' := congrArg (fun w : List (Fin 3) => passageFst w) hdecomp
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Prod.fst_add] at hsum'
    exact hsum'.symm
  have hlastStep : (lazyTwoDimensionalStep (u.getLast hne)).1 = -1 := by
    have hstepGe : -1 ≤ (lazyTwoDimensionalStep (u.getLast hne)).1 := by
      have hcast : (0 : ℤ) ≤ ((u.getLast hne : Fin 3) : ℤ) := by positivity
      simp only [lazyTwoDimensionalStep]
      omega
    have htotal' : passageFst pre +
        (lazyTwoDimensionalStep (u.getLast hne)).1 = -(k : ℤ) := by
      rw [← hsum]
      exact htotal
    omega
  have hlastCode : u.getLast hne = 0 := by
    have hval : (u.getLast hne : Fin 3).val = 0 := by
      change ((u.getLast hne : Fin 3) : ℤ) - 1 = -1 at hlastStep
      omega
    exact Fin.ext hval
  rw [List.getLast?_eq_getLast_of_ne_nil hne]
  exact congrArg some hlastCode




theorem excursionPassage_count_zero {k : ℕ} {u : List (Fin 3)}
    (h : excursionPassage k u) : u.count 0 = u.count 2 + k := by
  have htotal := h.2.1
  rw [passageFst_eq_count] at htotal
  omega




theorem excursionPassage_skeleton_length {k : ℕ} {u : List (Fin 3)}
    (h : excursionPassage k u) :
    (excursionSkeleton u).length = 2 * u.count 2 + k := by
  rw [excursionSkeleton_length_eq_counts, excursionPassage_count_zero h]
  omega




theorem excursionPassage_rdisp {k : ℕ} {u : List (Fin 3)}
    (h : excursionPassage k u) :
    2 * uibhbotWordRDisplacement u =
      2 * ((excursionSkeletonGapLengths u).sum : ℤ) - (excursionSkeleton u).length + k := by
  rw [excursionWordRDisplacement_eq_gap_sum_sub_twoCount]
  simp only [excursionTwoCount]
  have hlen := excursionPassage_skeleton_length h
  omega

end DirectedDistances.RandomWalk
