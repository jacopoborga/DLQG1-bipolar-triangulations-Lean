module

public import DirectedDistances.RandomWalk.UIBHBOTEncodingWalk

/-! # Reindexing invariance of the UIBHBOT word family

These are walk-level helpers toward `def-uihbot` and `prop-uihbot-sym`
In particular, word-family reversal does not establish map-level symmetry. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private def uibhbotIndexShiftEquiv (t : ℤ) : ℤ ≃ ℤ where
  toFun := fun k => k + t
  invFun := fun k => k - t
  left_inv := by intro k; change k + t - t = k; omega
  right_inv := by intro k; change k - t + t = k; omega

private def uibhbotIndexReflectEquiv : ℤ ≃ ℤ where
  toFun := fun k => -k - 1
  invFun := fun k => -k - 1
  left_inv := by intro k; change -(-k - 1) - 1 = k; omega
  right_inv := by intro k; change -(-k - 1) - 1 = k; omega

private theorem take_flatMap_prefix {α β : Type*} (f : α → List β) :
    ∀ n (xs : List α), n ≤ xs.length →
      (∀ x ∈ xs, 0 < (f x).length) →
      (xs.flatMap f).take n = ((xs.take n).flatMap f).take n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs hlen hpos
      cases xs with
      | nil => simp
      | cons a xs =>
          cases n with
          | zero => simp
          | succ n =>
              have hlen' : n ≤ xs.length := by simpa using hlen
              have hposa : 0 < (f a).length := hpos a (by simp)
              have hposxs : ∀ x ∈ xs, 0 < (f x).length := by
                intro x hx
                exact hpos x (by simp [hx])
              let r := n + 1 - (f a).length
              have hrn : r ≤ n := by
                dsimp [r]
                omega
              have hrlt : r < n + 1 := by omega
              have hleft := ih r hrlt xs (by omega) hposxs
              have htakeLen : n ≤ (xs.take n).length := by
                simp [List.length_take, Nat.min_eq_left (by omega : n ≤ xs.length)]
              have hposTake : ∀ x ∈ xs.take n, 0 < (f x).length := by
                intro x hx
                exact hposxs x (List.mem_of_mem_take hx)
              have hright := ih r hrlt (xs.take n) (by omega) hposTake
              simp only [List.flatMap_cons]
              rw [show (a :: xs).take (n + 1) = a :: xs.take n by rfl]
              simp only [List.flatMap_cons]
              rw [List.take_append, List.take_append]
              have hrtake : (xs.take n).take r = xs.take r := by
                simp [List.take_take, Nat.min_eq_left hrn]
              rw [hrtake] at hright
              dsimp [r] at hleft hright ⊢
              exact congrArg (fun tail => (f a).take (n + 1) ++ tail)
                (hleft.trans hright.symm)

private theorem take_flatMap_split_first {α : Type*} (f : ℕ → List α)
    (n m : ℕ) (hn : (f 0).length = n + 1)
    (hpos : ∀ k : ℕ, 0 < (f k).length) :
    ((List.range (n + 1 + m)).flatMap f).take (n + 1 + m) =
      f 0 ++ ((List.range m).flatMap (fun k => f (k + 1))).take m := by
  have hN : n + 1 + m = (n + m) + 1 := by omega
  have hrange : List.range (n + 1 + m) =
      0 :: (List.range (n + m)).map Nat.succ := by
    rw [hN, List.range_succ_eq_map]
  rw [hrange, List.flatMap_cons, List.flatMap_map]
  rw [List.take_append]
  have hlen : (f 0).length ≤ n + 1 + m := by rw [hn]; omega
  simp only [hn, Nat.add_sub_cancel_left, List.take_of_length_le hlen]
  have hprefix := take_flatMap_prefix (fun k => f (k + 1)) m
    (List.range (n + m)) (by rw [List.length_range]; omega)
    (by intro k hk; exact hpos (k + 1))
  rw [hprefix, List.take_range]
  simp

/-- Reindexing the iid word coordinates by a bijection preserves their joint law.
Walk-level helper toward `def-uihbot` and `prop-uihbot-sym` -/
theorem uibhbotWordFamilyLaw_map_reindex (σ : ℤ ≃ ℤ) :
    uibhbotWordFamilyLaw.map (fun w : ℤ → List (Fin 3) => fun k => w (σ k)) =
      uibhbotWordFamilyLaw := by
  have hfun : (fun w : ℤ → List (Fin 3) => fun k => w (σ k)) =
      (MeasurableEquiv.piCongrLeft (fun _ : ℤ => List (Fin 3)) σ.symm) := by
    funext w k
    simpa using (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ℤ => List (Fin 3)) σ.symm w (σ k)).symm
  rw [uibhbotWordFamilyLaw, hfun]
  simpa using (Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : ℤ => excursionWordLaw) σ.symm)

/-- The iid word family is stationary under integer translation of its indices.
Walk-level helper toward `def-uihbot` and `prop-uihbot-sym` -/
theorem uibhbotWordFamilyLaw_map_shift (t : ℤ) :
    uibhbotWordFamilyLaw.map (fun w : ℤ → List (Fin 3) => fun k => w (k + t)) =
      uibhbotWordFamilyLaw := by
  simpa [uibhbotIndexShiftEquiv] using
    uibhbotWordFamilyLaw_map_reindex (uibhbotIndexShiftEquiv t)

/-- The iid word family is invariant under reflection of its integer indices.
Walk-level helper toward `def-uihbot` and `prop-uihbot-sym` -/
theorem uibhbotWordFamilyLaw_map_reflect :
    uibhbotWordFamilyLaw.map (fun w : ℤ → List (Fin 3) => fun k => w (-k - 1)) =
      uibhbotWordFamilyLaw := by
  simpa [uibhbotIndexReflectEquiv] using
    uibhbotWordFamilyLaw_map_reindex uibhbotIndexReflectEquiv

/-- Translation of the word indices is measure preserving.
Walk-level helper toward `def-uihbot` and `prop-uihbot-sym` -/
theorem uibhbotWordFamilyLaw_measurePreserving_shift (t : ℤ) :
    MeasurePreserving
      (fun w : ℤ → List (Fin 3) => fun k => w (k + t))
      uibhbotWordFamilyLaw uibhbotWordFamilyLaw := by
  exact ⟨by fun_prop, uibhbotWordFamilyLaw_map_shift t⟩

/-- Reflection of the word indices is measure preserving.
Walk-level helper toward `def-uihbot` and `prop-uihbot-sym` -/
theorem uibhbotWordFamilyLaw_measurePreserving_reflect :
    MeasurePreserving
      (fun w : ℤ → List (Fin 3) => fun k => w (-k - 1))
      uibhbotWordFamilyLaw uibhbotWordFamilyLaw := by
  exact ⟨by fun_prop, uibhbotWordFamilyLaw_map_reflect⟩

/-- Reindexing the words by one starts the concatenated walk at the end of the
first word, with the shift given by that word's length. This is a walk-level
helper toward `def-uihbot` and `prop-uihbot-sym` -/
theorem uibhbotConcatWalk_shift_after_first_word
    (w : ℤ → List (Fin 3)) (t : ℤ) (ht : 0 ≤ t)
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) :
    uibhbotConcatWalk (fun k => w (k + 1)) t =
      uibhbotConcatWalk w (t + ((w 0).length : ℤ)) -
        uibhbotConcatWalk w ((w 0).length : ℤ) := by
  let m : ℕ := t.toNat
  let N : ℕ := (w 0).length
  let q : ℕ := N - 1
  let f : ℕ → List (Fin 3) := fun k => w (k : ℤ)
  have hNpos : 0 < N := by
    dsimp [N]
    have h := hwords 0
    omega
  have hq : q + 1 = N := by dsimp [q]; exact Nat.sub_add_cancel hNpos
  have hm : (m : ℤ) = t := by dsimp [m]; exact Int.toNat_of_nonneg ht
  have htadd : t + (N : ℤ) = ((N + m : ℕ) : ℤ) := by
    rw [← hm]
    push_cast
    ring
  have htime : (t + (N : ℤ)).toNat = N + m := by
    rw [htadd]
    push_cast
    rfl
  have hblock : (f 0).length = q + 1 := by
    dsimp [f, q, N]
    exact hq.symm
  have hpos : ∀ k : ℕ, 0 < (f k).length := by
    intro k
    dsimp [f]
    have := hwords (k : ℤ)
    omega
  let g : ℕ → List (Fin 3) := fun k => w ((k : ℤ) + 1)
  have hsplit := take_flatMap_split_first f q m hblock hpos
  have hprefix :
      ((List.range (N + m)).flatMap f).take (N + m) =
        w 0 ++ ((List.range m).flatMap g).take m := by
    simpa [f, g, q, hq, Nat.cast_add] using hsplit
  have hshift :
      ((List.range m).flatMap (fun k : ℕ => w ((k + 1 : ℕ) : ℤ))).take m =
        (((List.range m).map (fun k : ℕ => (k : ℤ))).flatMap
          (fun k : ℤ => w (k + 1))).take m := by
    congr 1
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro k hk
    simp only [Nat.cast_add, Nat.cast_one]
  have hprefixCast :
      ((List.range (N + m)).flatMap f).take (N + m) =
        w 0 ++ (((List.range m).map (fun k : ℕ => (k : ℤ))).flatMap
          (fun k : ℤ => w (k + 1))).take m := by
    calc
      _ = w 0 ++ ((List.range m).flatMap g).take m := hprefix
      _ = _ := by simpa [g] using congrArg (fun xs => w 0 ++ xs) hshift
  have hcastFlat (g₀ : ℤ → List (Fin 3)) (r : ℕ) :
      ((List.range r).map (fun k : ℕ => (k : ℤ))).flatMap g₀ =
        (List.range r).flatMap (fun k : ℕ => g₀ (k : ℤ)) := by
    rw [List.flatMap_map]
  have hbase : ((List.range N).flatMap f).take N = w 0 := by
    have hb := take_flatMap_split_first f q 0 hblock hpos
    simpa [f, q, hq] using hb
  have hbaseCast :
      (((List.range N).map (fun k : ℕ => (k : ℤ))).flatMap
        (fun k : ℤ => w k)).take N = w 0 := by
    rw [hcastFlat]
    exact hbase
  have hprefixAllCast :
      (((List.range (N + m)).map (fun k : ℕ => (k : ℤ))).flatMap
        (fun k : ℤ => w k)).take (N + m) =
        w 0 ++ (((List.range m).map (fun k : ℕ => (k : ℤ))).flatMap
          (fun k : ℤ => w (k + 1))).take m := by
    rw [hcastFlat]
    exact hprefixCast
  have htn : 0 ≤ t + (N : ℤ) := by omega
  have hNcast : 0 ≤ (N : ℤ) := by positivity
  simp only [uibhbotConcatWalk]
  split_ifs
  rw [htime, Int.toNat_natCast]
  simp only [bind_pure_comp, List.map_eq_map]
  rw [hprefixAllCast, hbaseCast, List.map_append, List.sum_append]
  simp [add_sub_cancel_left, m]

end DirectedDistances.RandomWalk
