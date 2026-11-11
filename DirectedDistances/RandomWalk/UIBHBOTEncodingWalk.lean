module

public import DirectedDistances.RandomWalk.ExcursionWords
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! # The bi-infinite UIBHBOT encoding walk

Concatenation of an iid family of stopped excursion words, together with its finite window law.
These are helper statements toward the corrected Lemma 5.18 characterization -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- Concatenate stopped excursion words around time zero. Forward time reads words starting at
index zero; backward time reads preceding words nearest first, reversing each word and negating -/
@[expose] def uibhbotConcatWalk (w : ℤ → List (Fin 3)) (t : ℤ) : ℤ × ℤ :=
  if 0 ≤ t then
    ((((List.range t.toNat).flatMap fun k => w (k : ℤ)).take t.toNat).map
      lazyTwoDimensionalStep).sum
  else
    -((((List.range (-t).toNat).flatMap fun k => (w (-(k : ℤ) - 1)).reverse).take
      (-t).toNat).map lazyTwoDimensionalStep).sum

/-- The iid family of all two-sided stopped excursion words. -/
@[expose] noncomputable def uibhbotWordFamilyLaw : Measure (ℤ → List (Fin 3)) :=
  Measure.infinitePi (fun _ : ℤ => excursionWordLaw)

/-- The finite restriction of the concatenated encoding walk to `[-N,N]`. -/
@[expose] noncomputable def uibhbotEncodingWindowLaw (N : ℕ) :
    Measure (Fin (2 * N + 1) → ℤ × ℤ) :=
  uibhbotWordFamilyLaw.map (fun w (j : Fin (2 * N + 1)) =>
    uibhbotConcatWalk w ((j : ℤ) - N))

/-- The concatenated walk starts at the origin. -/
theorem uibhbotConcatWalk_zero (w : ℤ → List (Fin 3)) :
    uibhbotConcatWalk w 0 = 0 := by
  simp [uibhbotConcatWalk]

/-- Almost every stopped excursion word contains at least one step -/
theorem ae_one_le_excursionWord_length :
    ∀ᵐ v ∂excursionWordLaw, 1 ≤ v.length := by
  rw [excursionWordLaw, ae_map_iff (measurable_excursionWord).aemeasurable
    (measurableSet_le measurable_const
      (measurable_of_countable fun v : List (Fin 3) => v.length))]
  exact ae_one_le_excursionLength.mono fun ω hω => by
    simpa [excursionWord, List.length_map, List.length_range] using hω

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

private theorem map_val_finRange_take (d N : ℕ) (hd : d ≤ N) :
    ((List.finRange N).take d).map Fin.val = List.range d := by
  induction d generalizing N with
  | zero => simp
  | succ d ih =>
      cases N with
      | zero => omega
      | succ N =>
          have hdN : d ≤ N := by omega
          rw [List.finRange_succ]
          change (0 :: ((List.finRange N).map Fin.succ).take d).map Fin.val =
            List.range (d + 1)
          simp only [List.map_cons, Fin.val_zero]
          rw [← List.map_take]
          simp only [List.map_map, Function.comp_def, Fin.val_succ]
          have htail :
              List.map (fun x : Fin N => x.val + 1) ((List.finRange N).take d) =
                List.map Nat.succ (List.range d) := by
            calc
              _ = List.map Nat.succ
                    (List.map Fin.val ((List.finRange N).take d)) := by
                rw [show (fun x : Fin N => x.val + 1) = Nat.succ ∘ Fin.val by
                  funext x; simp [Nat.succ_eq_add_one]]
                rw [← List.map_map]
              _ = _ := by rw [ih N hdN]
          rw [htail]
          simp [List.range_succ_eq_map]



theorem uibhbotConcatWalk_forward_eq_windowFromWords (N : ℕ)
    (w : ℤ → List (Fin 3))
    (hnonempty : ∀ k : ℤ, -(N : ℤ) ≤ k → k < (N : ℤ) → 1 ≤ (w k).length)
    (j : Fin (2 * N + 1)) (hj : N < j.val) :
    uibhbotConcatWalk w ((j : ℤ) - N) =
      uibhbotWindowFromWords N
        (fun i : Fin (2 * N) =>
          if i.val < N then w (i.val : ℤ)
          else w (-((i.val - N : ℕ) : ℤ) - 1)) j := by
  classical
  let words : Fin (2 * N) → List (Fin 3) := fun i =>
    if i.val < N then w (i.val : ℤ)
    else w (-((i.val - N : ℕ) : ℤ) - 1)
  let d : ℕ := j.val - N
  have hdN : d ≤ N := by dsimp [d]; omega
  have ht : ((j : ℤ) - N) = (d : ℤ) := by
    dsimp [d]
    omega
  have hword (i : Fin N) : words ⟨i.val, by omega⟩ = w (i.val : ℤ) := by
    simp [words, i.isLt]
  have hpos : ∀ i ∈ List.finRange N, 0 < (w (i.val : ℤ)).length := by
    intro i hi
    have hiN : i.val < N := i.isLt
    have h := hnonempty (i.val : ℤ) (by omega) (by omega)
    omega
  have hprefix := take_flatMap_prefix (fun i : Fin N => w (i.val : ℤ)) d
    (List.finRange N) (by simpa using hdN) hpos
  have hblocks :
      (List.range d).flatMap (fun k => w (k : ℤ)) =
        ((List.finRange N).take d).flatMap (fun i : Fin N => w (i.val : ℤ)) := by
    rw [← map_val_finRange_take d N hdN]
    have hmap (xs : List (Fin N)) :
        (xs.map Fin.val).flatMap (fun k => w (k : ℤ)) =
          xs.flatMap (fun i => w (i.val : ℤ)) := by
      induction xs with
      | nil => simp
      | cons i xs ih =>
          simp only [List.map_cons, List.flatMap_cons]
          exact congrArg (fun tail => w (i.val : ℤ) ++ tail) ih
    exact hmap ((List.finRange N).take d)
  have hflat :
      ((List.range d).flatMap (fun k => w (k : ℤ))).take d =
        ((List.finRange N).flatMap (fun i : Fin N => w (i.val : ℤ))).take d := by
    calc
      _ = (((List.finRange N).take d).flatMap (fun i : Fin N => w (i.val : ℤ))).take d :=
        congrArg (fun xs => xs.take d) hblocks
      _ = _ := hprefix.symm
  have hsrc : uibhbotConcatWalk w ((j : ℤ) - N) =
      ((((List.range d).flatMap fun k => w (k : ℤ)).take d).map
        lazyTwoDimensionalStep).sum := by
    simp [uibhbotConcatWalk, ht, d]
  have hdst : uibhbotWindowFromWords N words j =
      ((((List.finRange N).flatMap fun i => w (i.val : ℤ)).take d).map
        lazyTwoDimensionalStep).sum := by
    have hj' : ¬ j.val ≤ N := by omega
    simp [uibhbotWindowFromWords, hj', words, hword, d]
  calc
    uibhbotConcatWalk w ((j : ℤ) - N) =
        ((((List.range d).flatMap fun k => w (k : ℤ)).take d).map
          lazyTwoDimensionalStep).sum := hsrc
    _ = ((((List.finRange N).flatMap fun i => w (i.val : ℤ)).take d).map
          lazyTwoDimensionalStep).sum := by
      exact congrArg (fun xs => (xs.map lazyTwoDimensionalStep).sum) hflat
    _ = uibhbotWindowFromWords N words j := hdst.symm



theorem uibhbotConcatWalk_backward_eq_windowFromWords (N : ℕ)
    (w : ℤ → List (Fin 3))
    (hnonempty : ∀ k : ℤ, -(N : ℤ) ≤ k → k < (N : ℤ) → 1 ≤ (w k).length)
    (j : Fin (2 * N + 1)) (hj : j.val < N) :
    uibhbotConcatWalk w ((j : ℤ) - N) =
      uibhbotWindowFromWords N
        (fun i : Fin (2 * N) =>
          if i.val < N then w (i.val : ℤ)
          else w (-((i.val - N : ℕ) : ℤ) - 1)) j := by
  classical
  let words : Fin (2 * N) → List (Fin 3) := fun i =>
    if i.val < N then w (i.val : ℤ)
    else w (-((i.val - N : ℕ) : ℤ) - 1)
  let d : ℕ := N - j.val
  have hdN : d ≤ N := by dsimp [d]; omega
  have hdpos : 0 < d := by dsimp [d]; omega
  have ht : ((j : ℤ) - N) = - (d : ℤ) := by
    dsimp [d]
    omega
  have hword (i : Fin N) :
      words ⟨N + i.val, by omega⟩ = w (- (i.val : ℤ) - 1) := by
    simp [words]
  have hpos : ∀ i ∈ List.finRange N, 0 < (w (-(i.val : ℤ) - 1)).length := by
    intro i hi
    have hiN : i.val < N := i.isLt
    have h := hnonempty (-(i.val : ℤ) - 1) (by omega) (by omega)
    have h' : 0 < (w (-(i.val : ℤ) - 1)).length := by omega
    simpa [List.length_reverse] using h'
  have hposrev : ∀ i ∈ List.finRange N,
      0 < ((w (-(i.val : ℤ) - 1)).reverse).length := by
    intro i hi
    simpa [List.length_reverse] using hpos i hi
  have hprefix := take_flatMap_prefix
    (fun i : Fin N => (w (-(i.val : ℤ) - 1)).reverse) d
    (List.finRange N) (by simpa using hdN) hposrev
  have hblocks :
      (List.range d).flatMap (fun k => (w (-(k : ℤ) - 1)).reverse) =
        ((List.finRange N).take d).flatMap
          (fun i : Fin N => (w (-(i.val : ℤ) - 1)).reverse) := by
    rw [← map_val_finRange_take d N hdN]
    have hmap (xs : List (Fin N)) :
        (xs.map Fin.val).flatMap (fun k => (w (-(k : ℤ) - 1)).reverse) =
          xs.flatMap (fun i => (w (-(i.val : ℤ) - 1)).reverse) := by
      induction xs with
      | nil => simp
      | cons i xs ih =>
          simp only [List.map_cons, List.flatMap_cons]
          exact congrArg (fun tail => (w (-(i.val : ℤ) - 1)).reverse ++ tail) ih
    exact hmap ((List.finRange N).take d)
  have hflat :
      ((List.range d).flatMap (fun k => (w (-(k : ℤ) - 1)).reverse)).take d =
        ((List.finRange N).flatMap
          (fun i : Fin N => (w (-(i.val : ℤ) - 1)).reverse)).take d := by
    calc
      _ = (((List.finRange N).take d).flatMap
          (fun i : Fin N => (w (-(i.val : ℤ) - 1)).reverse)).take d :=
        congrArg (fun xs => xs.take d) hblocks
      _ = _ := hprefix.symm
  have hneg (xs : List (Fin 3)) :
      ((xs.map fun c => -lazyTwoDimensionalStep c).sum) =
        -((xs.map lazyTwoDimensionalStep).sum) := by
    induction xs with
    | nil => simp
    | cons c xs ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        abel
  have hsrc : uibhbotConcatWalk w ((j : ℤ) - N) =
      -((((List.range d).flatMap fun k => (w (-(k : ℤ) - 1)).reverse).take d).map
        lazyTwoDimensionalStep).sum := by
    simp [uibhbotConcatWalk, ht, d, hdpos.ne']
  have hdst : uibhbotWindowFromWords N words j =
      ((((List.finRange N).flatMap fun i =>
          (w (-(i.val : ℤ) - 1)).reverse).take d).map
        (fun c => -lazyTwoDimensionalStep c)).sum := by
    have hj' : j.val ≤ N := by omega
    have hword' (i : Fin N) :
        words ⟨N + i.val, by omega⟩ = w (-(i.val : ℤ) - 1) := hword i
    simp [uibhbotWindowFromWords, hj', words, hword', d, List.map_take,
      List.map_flatMap]
  have htargetNeg :
      ((((List.finRange N).flatMap fun i =>
          (w (-(i.val : ℤ) - 1)).reverse).take d).map
        (fun c => -lazyTwoDimensionalStep c)).sum =
        -((((List.finRange N).flatMap fun i =>
          (w (-(i.val : ℤ) - 1)).reverse).take d).map
          lazyTwoDimensionalStep).sum := hneg _
  calc
    uibhbotConcatWalk w ((j : ℤ) - N) =
        -((((List.range d).flatMap fun k => (w (-(k : ℤ) - 1)).reverse).take d).map
          lazyTwoDimensionalStep).sum := hsrc
    _ = -((((List.finRange N).flatMap fun i =>
          (w (-(i.val : ℤ) - 1)).reverse).take d).map
          lazyTwoDimensionalStep).sum := by
      exact congrArg Neg.neg
        (congrArg (fun xs => (xs.map lazyTwoDimensionalStep).sum) hflat)
    _ = uibhbotWindowFromWords N words j := by rw [← htargetNeg, hdst]



theorem uibhbotConcatWalk_eq_uibhbotWindowFromWords (N : ℕ)
    (w : ℤ → List (Fin 3))
    (hnonempty : ∀ k : ℤ, -(N : ℤ) ≤ k → k < (N : ℤ) → 1 ≤ (w k).length)
    (j : Fin (2 * N + 1)) :
    uibhbotConcatWalk w ((j : ℤ) - N) =
      uibhbotWindowFromWords N
        (fun i : Fin (2 * N) =>
          if i.val < N then w (i.val : ℤ)
          else w (-((i.val - N : ℕ) : ℤ) - 1)) j := by
  classical
  by_cases hj : j.val < N
  · exact uibhbotConcatWalk_backward_eq_windowFromWords N w hnonempty j hj
  · by_cases hj' : N < j.val
    · exact uibhbotConcatWalk_forward_eq_windowFromWords N w hnonempty j hj'
    · have heq : j.val = N := by omega
      have ht : ((j : ℤ) - N) = 0 := by omega
      rw [ht, uibhbotConcatWalk_zero]
      simp [uibhbotWindowFromWords, heq]

private def uibhbotWordIndex (N : ℕ) (i : Fin (2 * N)) : ℤ :=
  if i.val < N then (i.val : ℤ) else -((i.val - N : ℕ) : ℤ) - 1

private theorem uibhbotWordIndex_injective (N : ℕ) :
    Function.Injective (uibhbotWordIndex N) := by
  intro i j hij
  by_cases hi : i.val < N <;> by_cases hj : j.val < N
  · simp [uibhbotWordIndex, hi, hj] at hij
    exact Fin.ext (by omega)
  · simp [uibhbotWordIndex, hi, hj] at hij
    exfalso
    omega
  · simp [uibhbotWordIndex, hi, hj] at hij
    exfalso
    omega
  · simp [uibhbotWordIndex, hi, hj] at hij
    exact Fin.ext (by omega)

instance : IsProbabilityMeasure uibhbotWordFamilyLaw := by
  unfold uibhbotWordFamilyLaw
  infer_instance

/-- Each coordinate of the canonical two-sided family is measurable. -/
theorem measurable_uibhbotWordFamilyEval (k : ℤ) :
    Measurable (fun x : ℤ → List (Fin 3) => x k) :=
  measurable_pi_apply k

/-- Every canonical coordinate has the one-excursion word law. -/
theorem uibhbotWordFamilyLaw_map_eval (k : ℤ) :
    uibhbotWordFamilyLaw.map (fun x : ℤ → List (Fin 3) => x k) = excursionWordLaw := by
  rw [uibhbotWordFamilyLaw, Measure.infinitePi_map_eval]

/-- The coordinates of the canonical two-sided word family are independent. -/
theorem iIndepFun_uibhbotWordFamilyEval :
    iIndepFun (fun k (x : ℤ → List (Fin 3)) => x k) uibhbotWordFamilyLaw := by
  simpa [uibhbotWordFamilyLaw] using
    (iIndepFun_infinitePi (P := fun _ : ℤ => excursionWordLaw)
      (X := fun _ (x : List (Fin 3)) => x) (by intro; exact measurable_id))




theorem uibhbotEncodingWindowLaw_eq_uibhbotExcursionWindowLaw (N : ℕ) :
    uibhbotEncodingWindowLaw N = uibhbotExcursionWindowLaw N := by
  classical
  let coords : (ℤ → List (Fin 3)) → Fin (2 * N) → List (Fin 3) := fun x i =>
    x (uibhbotWordIndex N i)
  have hcoordsMeas : Measurable coords :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (uibhbotWordIndex N i)
  have hcoordsLaw : uibhbotWordFamilyLaw.map coords = excursionWordProductLaw N := by
    change (Measure.infinitePi (fun _ : ℤ => excursionWordLaw)).map coords = _
    rw [Measure.map_infinitePi_infinitePi_of_inj (uibhbotWordIndex_injective N),
      Measure.infinitePi_eq_pi]
    rfl
  have hcoordsNonempty : ∀ᵐ x ∂uibhbotWordFamilyLaw,
      ∀ i : Fin (2 * N), 1 ≤ (x (uibhbotWordIndex N i)).length := by
    rw [ae_all_iff]
    intro i
    have heval :
        uibhbotWordFamilyLaw.map (fun x => x (uibhbotWordIndex N i)) = excursionWordLaw := by
      rw [uibhbotWordFamilyLaw, Measure.infinitePi_map_eval]
    have hae := ae_one_le_excursionWord_length
    rw [← heval] at hae
    exact (ae_map_iff (measurable_pi_apply (uibhbotWordIndex N i)).aemeasurable
      (measurableSet_le measurable_const
        (measurable_of_countable fun v : List (Fin 3) => v.length))).mp
      hae
  have hnonempty : ∀ᵐ x ∂uibhbotWordFamilyLaw,
      ∀ k : ℤ, -(N : ℤ) ≤ k → k < (N : ℤ) → 1 ≤ (x k).length := by
    filter_upwards [hcoordsNonempty] with x hx
    intro k hk₁ hk₂
    by_cases hk : 0 ≤ k
    · let i : Fin (2 * N) := ⟨k.toNat, by omega⟩
      have hik : k.toNat < N := by omega
      have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
      have hindex : uibhbotWordIndex N i = k := by
        simp [uibhbotWordIndex, i, hik, hcast]
      simpa [hindex] using hx i
    · have hqnonneg : 0 ≤ -k - 1 := by omega
      let q : ℕ := (-k - 1).toNat
      have hq : (q : ℤ) = -k - 1 := Int.toNat_of_nonneg hqnonneg
      let i : Fin (2 * N) := ⟨N + q, by omega⟩
      have hindex : uibhbotWordIndex N i = k := by
        simp [uibhbotWordIndex, i, q]
        omega
      simpa [hindex] using hx i
  have hwindow :
      (fun x (j : Fin (2 * N + 1)) => uibhbotConcatWalk x ((j : ℤ) - N)) =ᵐ[
        uibhbotWordFamilyLaw]
      (fun x j => uibhbotWindowFromWords N (coords x) j) := by
    filter_upwards [hnonempty] with x hx
    funext j
    have hcoordEq :
        (fun i : Fin (2 * N) =>
          if i.val < N then x (i.val : ℤ)
          else x (-((i.val - N : ℕ) : ℤ) - 1)) = coords x := by
      funext i
      by_cases hi : i.val < N <;> simp [coords, uibhbotWordIndex, hi]
    rw [← hcoordEq]
    exact uibhbotConcatWalk_eq_uibhbotWindowFromWords N x hx j
  rw [uibhbotEncodingWindowLaw, Measure.map_congr hwindow]
  calc
    uibhbotWordFamilyLaw.map (fun x => uibhbotWindowFromWords N (coords x)) =
        (uibhbotWordFamilyLaw.map coords).map (uibhbotWindowFromWords N) := by
      rw [Measure.map_map (measurable_uibhbotWindowFromWords N) hcoordsMeas]
      rfl
    _ = uibhbotExcursionWindowLaw N := by rw [hcoordsLaw]; rfl
end DirectedDistances.RandomWalk
