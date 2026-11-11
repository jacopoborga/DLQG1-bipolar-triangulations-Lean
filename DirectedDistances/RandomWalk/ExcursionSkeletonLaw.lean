module

public import DirectedDistances.RandomWalk.ExcursionSkeletonGaps






public section
namespace DirectedDistances.RandomWalk

/-- Insert each listed lazy run before a skeleton letter, with remaining runs terminal. -/
@[expose] def excursionInterleave : List (Fin 3) → List ℕ → List (Fin 3)
  | [], gaps => List.replicate gaps.sum 1
  | c :: skeleton, [] => c :: excursionInterleave skeleton []
  | c :: skeleton, n :: gaps =>
      List.replicate n 1 ++ c :: excursionInterleave skeleton gaps

/-- Interleaving contributes `gaps.sum` lazy letters and one letter per skeleton entry. -/
theorem excursionInterleave_length (skeleton : List (Fin 3)) (gaps : List ℕ) :
    (excursionInterleave skeleton gaps).length = skeleton.length + gaps.sum := by
  induction skeleton generalizing gaps with
  | nil => simp [excursionInterleave]
  | cons c skeleton ih =>
      cases gaps with
      | nil => simp [excursionInterleave, ih]
      | cons n gaps =>
          simp [excursionInterleave, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- If the skeleton has no lazy letters, interleaving preserves it under skeleton extraction. -/
theorem excursionSkeleton_interleave (skeleton : List (Fin 3)) (gaps : List ℕ)
    (hs : ∀ c ∈ skeleton, c ≠ 1) :
    excursionSkeleton (excursionInterleave skeleton gaps) = skeleton := by
  induction skeleton generalizing gaps with
  | nil => simp [excursionInterleave, excursionSkeleton]
  | cons c skeleton ih =>
      have hc : c ≠ 1 := hs c (by simp)
      have hs' : ∀ d ∈ skeleton, d ≠ 1 := by
        intro d hd
        exact hs d (by simp [hd])
      cases gaps with
      | nil =>
          simp [excursionInterleave, excursionSkeleton, hc]
          exact ih [] hs'
      | cons n gaps =>
          simp [excursionInterleave, excursionSkeleton, hc]
          exact ih gaps hs'

private theorem excursionSkeletonGapLengthsAux_replicate (pending n : ℕ) (c : Fin 3)
    (w : List (Fin 3)) (hc : c ≠ 1) :
    excursionSkeletonGapLengthsAux pending (List.replicate n 1 ++ c :: w) =
      [pending + n] ++ excursionSkeletonGapLengthsAux 0 w := by
  induction n generalizing pending with
  | zero => simp [excursionSkeletonGapLengthsAux, hc]
  | succ n ih =>
      simp only [Nat.add_one, List.replicate_succ, List.cons_append,
        excursionSkeletonGapLengthsAux]
      rw [ih (pending + 1)]
      change [pending + 1 + n] ++ excursionSkeletonGapLengthsAux 0 w =
        [pending + (n + 1)] ++ excursionSkeletonGapLengthsAux 0 w
      rw [show pending + 1 + n = pending + (n + 1) by omega]

private theorem excursionSkeletonGapLengthsAux_replicate_only (pending n : ℕ) :
    excursionSkeletonGapLengthsAux pending (List.replicate n 1) = [pending + n] := by
  induction n generalizing pending with
  | zero => simp [excursionSkeletonGapLengthsAux]
  | succ n ih =>
      simp only [Nat.add_one, List.replicate_succ, excursionSkeletonGapLengthsAux]
      rw [ih (pending + 1)]
      change [pending + 1 + n] = [pending + (n + 1)]
      rw [show pending + 1 + n = pending + (n + 1) by omega]

/-- Recover a valid gap list after interleaving a skeleton without lazy letters.
k140 step 6). -/
theorem excursionSkeletonGapLengths_interleave (skeleton : List (Fin 3)) (gaps : List ℕ)
    (hs : ∀ c ∈ skeleton, c ≠ 1) (hg : gaps.length = skeleton.length + 1) :
    excursionSkeletonGapLengths (excursionInterleave skeleton gaps) = gaps := by
  induction skeleton generalizing gaps with
  | nil =>
      cases gaps with
      | nil => simp at hg
      | cons n gaps =>
          have hnil : gaps = [] := by simp at hg; simp_all
          subst gaps
          simp [excursionInterleave, excursionSkeletonGapLengths,
            excursionSkeletonGapLengthsAux_replicate_only]
  | cons c skeleton ih =>
      cases gaps with
      | nil => simp at hg
      | cons n gaps =>
          have hg' : gaps.length = skeleton.length + 1 := by simp at hg; omega
          have hc : c ≠ 1 := hs c (by simp)
          have hs' : ∀ d ∈ skeleton, d ≠ 1 := by
            intro d hd
            exact hs d (by simp [hd])
          change excursionSkeletonGapLengthsAux 0
              (List.replicate n 1 ++ c :: excursionInterleave skeleton gaps) = n :: gaps
          rw [excursionSkeletonGapLengthsAux_replicate 0 n c _ hc]
          have htail := ih gaps hs' hg'
          change excursionSkeletonGapLengthsAux 0
              (excursionInterleave skeleton gaps) = gaps at htail
          rw [htail]
          simp

private theorem excursionSkeleton_length_add_count_one (v : List (Fin 3)) :
    v.length = (excursionSkeleton v).length + v.count 1 := by
  induction v with
  | nil => simp [excursionSkeleton]
  | cons c cs ih =>
      by_cases hc : c = 1 <;> simp [excursionSkeleton, hc, ih] <;> omega

private theorem excursionGapFactorization (gaps : List ℕ) :
    (1 / 2 : ℝ) ^ gaps.length *
        (gaps.map (fun n => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ n)).prod =
      (1 / 3 : ℝ) ^ (gaps.length + gaps.sum) := by
  induction gaps with
  | nil => norm_num
  | cons n gaps ih =>
      simp only [List.length_cons, List.map_cons, List.prod_cons, List.sum_cons]
      rw [show gaps.length + 1 = Nat.succ gaps.length by omega, pow_succ]
      calc
        (1 / 2 : ℝ) ^ gaps.length * (1 / 2 : ℝ) *
            ((2 / 3 : ℝ) * (1 / 3 : ℝ) ^ n *
              (gaps.map (fun k => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ k)).prod) =
            ((1 / 2 : ℝ) ^ gaps.length *
                (gaps.map (fun k => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ k)).prod) *
              ((1 / 2 : ℝ) * (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ n) := by ring
        _ = (1 / 3 : ℝ) ^ (gaps.length + gaps.sum) * (1 / 3 : ℝ) ^ (n + 1) := by
          rw [ih]
          congr 1
          rw [show n + 1 = Nat.succ n by omega, pow_succ]
          ring
        _ = (1 / 3 : ℝ) ^ ((gaps.length + gaps.sum) + (n + 1)) := by
          rw [← pow_add]
        _ = (1 / 3 : ℝ) ^ (Nat.succ gaps.length + (n + gaps.sum)) := by
          exact congrArg (fun k : ℕ => (1 / 3 : ℝ) ^ k) (by omega)




theorem excursionWord_atom_factorization (v : List (Fin 3))
    (hv : IsStoppedExcursionWord v) :
    (1 / 3 : ℝ) ^ v.length =
      (1 / 2 : ℝ) ^ (excursionSkeleton v).length *
        ((excursionSkeletonGapLengths v).dropLast.map
          (fun n => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ n)).prod := by
  let gaps := excursionSkeletonGapLengths v
  have hlen : gaps.length = (excursionSkeleton v).length + 1 := by
    dsimp [gaps]
    exact excursionSkeletonGapLengths_length v
  have hne : gaps ≠ [] := by
    intro h
    simp [h] at hlen
  have hlast : gaps.getLast hne = 0 := by
    have h := excursionSkeletonGapLengths_terminal_zero v hv
    rw [List.getLast?_eq_getLast_of_ne_nil hne] at h
    exact Option.some.inj h
  have hdecomp : gaps.dropLast ++ [gaps.getLast hne] = gaps :=
    List.dropLast_append_getLast hne
  have hdropLen : gaps.dropLast.length = (excursionSkeleton v).length := by
    have h := congrArg List.length hdecomp
    simp only [List.length_append, List.length_singleton] at h
    rw [hlen] at h
    omega
  have hdropSum : gaps.dropLast.sum = gaps.sum := by
    have h := congrArg List.sum hdecomp
    simp [hlast] at h
    omega
  have hvlen : v.length = gaps.dropLast.length + gaps.dropLast.sum := by
    rw [hdropLen, hdropSum]
    rw [show gaps.sum = v.count 1 by
      dsimp [gaps]
      exact excursionSkeletonGapLengths_sum v]
    exact excursionSkeleton_length_add_count_one v
  calc
    (1 / 3 : ℝ) ^ v.length =
        (1 / 3 : ℝ) ^ (gaps.dropLast.length + gaps.dropLast.sum) := by rw [hvlen]
    _ = (1 / 2 : ℝ) ^ gaps.dropLast.length *
        (gaps.dropLast.map (fun n => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ n)).prod :=
      (excursionGapFactorization gaps.dropLast).symm
    _ = (1 / 2 : ℝ) ^ (excursionSkeleton v).length *
        (gaps.dropLast.map (fun n => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ n)).prod := by
      rw [hdropLen]

end DirectedDistances.RandomWalk
