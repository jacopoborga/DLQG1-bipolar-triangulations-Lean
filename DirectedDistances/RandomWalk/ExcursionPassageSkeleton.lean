module

public import DirectedDistances.RandomWalk.ExcursionSkeletonLaw
public import DirectedDistances.RandomWalk.ExcursionBlockFlatLaw






public section
namespace DirectedDistances.RandomWalk




theorem excursionSkeleton_firstCoordinate_sum (u : List (Fin 3)) :
    ((u.map lazyTwoDimensionalStep).sum).1 =
      (((excursionSkeleton u).map lazyTwoDimensionalStep).sum).1 := by
  induction u with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c = 1
      · simp [excursionSkeleton, lazyTwoDimensionalStep, hc, ih]
      · simp [excursionSkeleton, lazyTwoDimensionalStep, hc, ih]




theorem excursionSkeleton_prefix_firstCoordinate (u : List (Fin 3)) (i : ℕ) :
    ∃ s t : List (Fin 3), s = excursionSkeleton (u.take i) ∧
      t = excursionSkeleton (u.drop i) ∧ excursionSkeleton u = s ++ t ∧
      ((u.take i).map lazyTwoDimensionalStep).sum.1 =
        (s.map lazyTwoDimensionalStep).sum.1 := by
  refine ⟨excursionSkeleton (u.take i), excursionSkeleton (u.drop i), rfl, rfl, ?_, ?_⟩
  · have h := congrArg excursionSkeleton (List.take_append_drop i u)
    simpa only [excursionSkeleton, List.filter_append] using h.symm
  · exact excursionSkeleton_firstCoordinate_sum (u.take i)

private theorem excursionSkeleton_prefix_sum_occurs_aux (u : List (Fin 3)) :
    ∀ j ≤ (excursionSkeleton u).length,
      ∃ i, i ≤ u.length ∧ (j < (excursionSkeleton u).length → i < u.length) ∧
        ((u.take i).map lazyTwoDimensionalStep).sum.1 =
          (((excursionSkeleton u).take j).map lazyTwoDimensionalStep).sum.1 := by
  induction u with
  | nil =>
      intro j hj
      have hj0 : j = 0 := by simpa [excursionSkeleton] using hj
      subst j
      refine ⟨0, And.intro ?_ (And.intro ?_ ?_)⟩
      · simp
      · intro hlt
        simp [excursionSkeleton] at hlt
      · simp [excursionSkeleton]
  | cons c cs ih =>
      intro j hj
      by_cases hc : c = 1
      · have hj' : j ≤ (excursionSkeleton cs).length := by
          simpa [excursionSkeleton, hc] using hj
        obtain ⟨i, hi, hstrict, hsum⟩ := ih j hj'
        refine ⟨i + 1, by simp; omega, ?_, ?_⟩
        · intro hproper
          have hproper' : j < (excursionSkeleton cs).length := by
            simpa [excursionSkeleton, hc] using hproper
          have hi' := hstrict hproper'
          simp only [List.length_cons]
          omega
        · have hsum' := hsum
          rw [List.map_take, List.map_take] at hsum'
          have htake : (c :: cs).take (i + 1) = c :: cs.take i := by simp
          rw [htake]
          simpa [excursionSkeleton, hc, lazyTwoDimensionalStep] using hsum'
      · have hlen : j ≤ (excursionSkeleton cs).length + 1 := by
          simpa [excursionSkeleton, hc, Nat.add_comm] using hj
        cases j with
        | zero =>
            exact ⟨0, by simp, by simp, by simp [excursionSkeleton]⟩
        | succ j =>
            have hj' : j ≤ (excursionSkeleton cs).length := by omega
            obtain ⟨i, hi, hstrict, hsum⟩ := ih j hj'
            refine ⟨i + 1, by simp; omega, ?_, ?_⟩
            · intro hproper
              have hproper' : j < (excursionSkeleton cs).length := by
                have : j + 1 < (excursionSkeleton cs).length + 1 := by
                  simpa [excursionSkeleton, hc] using hproper
                omega
              have hi' := hstrict hproper'
              simp only [List.length_cons]
              omega
            · have hsum' := hsum
              rw [List.map_take, List.map_take] at hsum'
              have htake : (c :: cs).take (i + 1) = c :: cs.take i := by simp
              rw [htake]
              simpa [excursionSkeleton, hc] using hsum'




theorem excursionSkeleton_prefix_sum_occurs (u : List (Fin 3)) (j : ℕ)
    (hj : j ≤ (excursionSkeleton u).length) :
    ∃ i, i ≤ u.length ∧ (j < (excursionSkeleton u).length → i < u.length) ∧
      ((u.take i).map lazyTwoDimensionalStep).sum.1 =
        (((excursionSkeleton u).take j).map lazyTwoDimensionalStep).sum.1 :=
  excursionSkeleton_prefix_sum_occurs_aux u j hj

private theorem excursionSkeleton_drop_nonempty_of_last (u : List (Fin 3)) (i : ℕ)
    (c : Fin 3) (hi : i < u.length) (hlast : u.getLast? = some c) (hc : c ≠ 1) :
    excursionSkeleton (u.drop i) ≠ [] := by
  have hdrop : u.drop i ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
    omega
  have hlastDrop : (u.drop i).getLast? = some c := by
    rw [← List.getLast?_append_of_ne_nil (u.take i) hdrop,
      List.take_append_drop]
    exact hlast
  have hget : (u.drop i).getLast hdrop = c := by
    have h := List.getLast?_eq_getLast_of_ne_nil hdrop
    rw [hlastDrop] at h
    exact Option.some.inj h.symm
  have hmem : c ∈ u.drop i := by
    rw [← hget]
    exact List.getLast_mem hdrop
  intro hempty
  have : c ∈ excursionSkeleton (u.drop i) := by
    simp [excursionSkeleton, hmem, hc]
  simp [hempty] at this





theorem excursionSkeleton_properPrefix_firstCoordinate_gt_iff (u : List (Fin 3))
    (c : Fin 3) (k : ℕ) (hlast : u.getLast? = some c) (hc : c ≠ 1) :
    (∀ i < u.length, -(k : ℤ) < ((u.take i).map lazyTwoDimensionalStep).sum.1) ↔
      ∀ j < (excursionSkeleton u).length,
        -(k : ℤ) < (((excursionSkeleton u).take j).map lazyTwoDimensionalStep).sum.1 := by
  constructor
  · intro hu j hj
    obtain ⟨i, hi, hproper, hsum⟩ := excursionSkeleton_prefix_sum_occurs u j (le_of_lt hj)
    calc
      -(k : ℤ) < ((u.take i).map lazyTwoDimensionalStep).sum.1 := hu i (hproper hj)
      _ = (((excursionSkeleton u).take j).map lazyTwoDimensionalStep).sum.1 := hsum
  · intro hs i hi
    obtain ⟨s, t, _hsPrefix, ht, hsplit, hsum⟩ :=
      excursionSkeleton_prefix_firstCoordinate u i
    have hdrop := excursionSkeleton_drop_nonempty_of_last u i c hi hlast hc
    have hj : s.length < (excursionSkeleton u).length := by
      rw [hsplit]
      simp only [List.length_append]
      have hpos : 0 < t.length := by
        rw [ht]
        exact List.length_pos_iff_ne_nil.mpr hdrop
      omega
    have hprefix : (excursionSkeleton u).take s.length = s := by
      rw [hsplit]
      simp
    rw [hsum, ← hprefix]
    exact hs s.length hj



theorem excursionInterleave_skeleton_gapsAux (pending : ℕ) (cs : List (Fin 3)) :
    excursionInterleave (cs.filter (fun c => c ≠ 1))
      (excursionSkeletonGapLengthsAux pending cs) = List.replicate pending 1 ++ cs := by
  induction cs generalizing pending with
  | nil => simp [excursionSkeletonGapLengthsAux, excursionInterleave]
  | cons c cs ih =>
      by_cases hc : c = 1
      · subst c
        simpa [excursionSkeletonGapLengthsAux, List.replicate_add,
          List.append_assoc] using ih (pending + 1)
      · simp only [List.filter_cons, show decide (c ≠ 1) = true by simp [hc],
          ↓reduceIte, excursionSkeletonGapLengthsAux, hc, excursionInterleave]
        rw [ih 0]
        simp



theorem excursionInterleave_skeleton_gaps (u : List (Fin 3)) :
    excursionInterleave (excursionSkeleton u) (excursionSkeletonGapLengths u) = u := by
  simpa [excursionSkeleton, excursionSkeletonGapLengths] using
    excursionInterleave_skeleton_gapsAux 0 u



theorem excursionPassage_getLast {k : ℕ} {u : List (Fin 3)}
    (hu : excursionPassage k u) : u.getLast? = some 0 := by
  have hne : u ≠ [] := List.ne_nil_of_length_pos hu.1
  let pre := u.dropLast
  have he : pre ++ [u.getLast hne] = u := List.dropLast_append_getLast hne
  have hlt : pre.length < u.length := by rw [← he]; simp
  have hp := hu.2.2 pre.length hlt
  have ht : u.take pre.length = pre := by rw [← he]; simp
  rw [ht] at hp
  have hsum := congrArg (fun w : List (Fin 3) =>
    ((w.map lazyTwoDimensionalStep).sum).1) he
  simp only [List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton, Prod.fst_add] at hsum
  have hc : u.getLast hne = 0 := by
    have hh := hu.2.1
    change _ + (((u.getLast hne).val : ℤ) - 1) = _ at hsum
    apply Fin.ext
    omega
  rw [List.getLast?_eq_getLast_of_ne_nil hne, hc]

private theorem interleave_getLast (s : List (Fin 3)) (g : List ℕ)
    (hg : g.length = s.length + 1) (hz : g.getLast? = some 0) :
    (excursionInterleave s g).getLast? = s.getLast? := by
  induction s generalizing g with
  | nil =>
      cases g with
      | nil => simp at hg
      | cons n g =>
          have ht : g = [] := by simpa using hg
          subst g
          have hn : n = 0 := by simpa using hz
          subst n
          rfl
  | cons c s ih =>
      cases g with
      | nil => simp at hg
      | cons n g =>
          have hl : g.length = s.length + 1 := by simpa using hg
          have hgn : g ≠ [] := by intro h; simp [h] at hl
          have hz' : g.getLast? = some 0 := by
            rw [← List.getLast?_append_of_ne_nil [n] hgn]
            exact hz
          have hh := ih g hl hz'
          simp only [excursionInterleave, List.getLast?_append_cons]
          cases s with
          | nil =>
              have he : excursionInterleave [] g = [] := by
                cases h : excursionInterleave [] g with
                | nil => rfl
                | cons a l => simp [h] at hh
              simp [he]
          | cons d s =>
              have hn : excursionInterleave (d :: s) g ≠ [] := by
                intro he
                have hlen := excursionInterleave_length (d :: s) g
                simp [he] at hlen
                omega
              rw [← List.singleton_append, List.getLast?_append_of_ne_nil [c] hn, hh,
                List.getLast?_cons_cons]



theorem excursionPassage_skeleton_iff {k : ℕ} {u : List (Fin 3)}
    (hlast : u.getLast? = some 0) :
    excursionPassage k u ↔ excursionPassage k (excursionSkeleton u) := by
  have hn : u ≠ [] := by intro h; simp [h] at hlast
  have hsn : excursionSkeleton u ≠ [] :=
    excursionSkeleton_drop_nonempty_of_last u 0 0
      (List.length_pos_iff_ne_nil.mpr hn) hlast (by decide)
  have hsum := excursionSkeleton_firstCoordinate_sum u
  have hp := excursionSkeleton_properPrefix_firstCoordinate_gt_iff u 0 k hlast (by decide)
  simp only [excursionPassage]
  rw [hsum, hp]
  simp only [List.length_pos_iff_ne_nil]
  constructor
  · intro h
    exact ⟨hsn, h.2⟩
  · intro h
    exact ⟨hn, h.2⟩



theorem excursionPassage_interleave_iff {k : ℕ} {s : List (Fin 3)} {g : List ℕ}
    (hs : ∀ c ∈ s, c ≠ 1) (hg : g.length = s.length + 1)
    (hz : g.getLast? = some 0) :
    excursionPassage k (excursionInterleave s g) ↔ excursionPassage k s := by
  have hsk := excursionSkeleton_interleave s g hs
  constructor
  · intro hu
    have hh := (excursionPassage_skeleton_iff (excursionPassage_getLast hu)).mp hu
    rwa [hsk] at hh
  · intro hu
    have hl : (excursionInterleave s g).getLast? = some 0 := by
      rw [interleave_getLast s g hg hz]
      exact excursionPassage_getLast hu
    apply (excursionPassage_skeleton_iff hl).mpr
    rwa [hsk]

end DirectedDistances.RandomWalk
