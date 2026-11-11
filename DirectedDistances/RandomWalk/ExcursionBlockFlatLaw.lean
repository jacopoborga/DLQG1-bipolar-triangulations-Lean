module

public import DirectedDistances.RandomWalk.ExcursionWordSupport
public import DirectedDistances.RandomWalk.UIBHBOTPastRUnbounded
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.BigOperators.Fin




public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators




@[expose] def excursionPassage (k : ℕ) (u : List (Fin 3)) : Prop :=
  0 < u.length ∧ ((u.map lazyTwoDimensionalStep).sum).1 = -(k : ℤ) ∧
    ∀ i < u.length, -(k : ℤ) < (((u.take i).map lazyTwoDimensionalStep).sum).1

local notation "blockFst" u:max => Prod.fst (List.sum (List.map lazyTwoDimensionalStep u))

private theorem blockFst_append (u v : List (Fin 3)) :
    blockFst (u ++ v) = blockFst u + blockFst v := by
  simp [List.map_append, List.sum_append]




theorem excursionPassage_one_iff (u : List (Fin 3)) :
    excursionPassage 1 u ↔ IsStoppedExcursionWord u := by
  rfl




theorem partialSum_eq_rdisp_cat {k : ℕ} (w : Fin k → List (Fin 3)) :
    ∑ j, uibhbotWordRDisplacement (w j) =
      uibhbotWordRDisplacement ((List.ofFn w).flatten) := by
  induction k with
  | zero => simp [uibhbotWordRDisplacement]
  | succ k ih =>
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.flatten_cons]
      rw [ih]
      simp [uibhbotWordRDisplacement, List.map_append, List.sum_append]

private theorem passage_append {a b : ℕ} {u v : List (Fin 3)}
    (hu : excursionPassage a u) (hv : excursionPassage b v) :
    excursionPassage (a + b) (u ++ v) := by
  have hul := hu.1
  refine ⟨by simp only [List.length_append]; omega, ?_, ?_⟩
  · rw [blockFst_append, hu.2.1, hv.2.1]
    push_cast
    omega
  · intro i hi
    simp only [List.length_append] at hi
    by_cases hil : i < u.length
    · rw [List.take_append_of_le_length hil.le]
      have h := hu.2.2 i hil
      push_cast
      omega
    · have heq : i = u.length + (i - u.length) := by omega
      rw [heq, List.take_length_add_append]
      change -((a + b : ℕ) : ℤ) < blockFst (u ++ v.take (i - u.length))
      rw [blockFst_append, hu.2.1]
      have h := hv.2.2 (i - u.length) (by omega)
      push_cast
      omega

private theorem first_hit_exists (u : List (Fin 3)) (n : ℕ) (hn : n ≤ u.length)
    (hneg : blockFst (u.take n) ≤ -1) :
    ∃ i ≤ n, blockFst (u.take i) = -1 := by
  induction n with
  | zero => simp at hneg
  | succ n ih =>
      by_cases hprev : blockFst (u.take n) ≤ -1
      · obtain ⟨i, hi, he⟩ := ih (by omega) hprev
        exact ⟨i, by omega, he⟩
      · have hs : -1 ≤ (lazyTwoDimensionalStep u[n]).1 := by
          simp only [lazyTwoDimensionalStep]
          have hc : (0 : ℤ) ≤ (u[n] : ℤ) := by positivity
          omega
        have he : blockFst (u.take (n + 1)) =
            blockFst (u.take n) + (lazyTwoDimensionalStep u[n]).1 := by
          rw [List.take_succ_eq_append_getElem (by omega), blockFst_append]
          simp
        exact ⟨n + 1, le_rfl, by omega⟩

private theorem passage_split {k : ℕ} (hk : 1 ≤ k) {u : List (Fin 3)}
    (hu : excursionPassage (k + 1) u) :
    ∃ v t, IsStoppedExcursionWord v ∧ excursionPassage k t ∧ v ++ t = u := by
  classical
  have hneg : blockFst (u.take u.length) ≤ -1 := by
    rw [List.take_length, hu.2.1]
    omega
  obtain ⟨i, hi, he⟩ := first_hit_exists u u.length le_rfl hneg
  have hex : ∃ n, n ≤ u.length ∧ blockFst (u.take n) = -1 := ⟨i, hi, he⟩
  let n := Nat.find hex
  have hn : n ≤ u.length ∧ blockFst (u.take n) = -1 := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    simp [hz] at hn
  have hnlt : n < u.length := by
    by_contra h
    have heq : n = u.length := by omega
    have htotal := hu.2.1
    rw [heq, List.take_length] at hn
    omega
  have hbefore : ∀ j < n, -1 < blockFst (u.take j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        have hne : blockFst (u.take (j + 1)) ≠ -1 := by
          intro heq
          exact Nat.find_min hex hj ⟨by omega, heq⟩
        have hs : -1 ≤ (lazyTwoDimensionalStep u[j]).1 := by
          simp only [lazyTwoDimensionalStep]
          have hc : (0 : ℤ) ≤ (u[j] : ℤ) := by positivity
          omega
        have heq : blockFst (u.take (j + 1)) =
            blockFst (u.take j) + (lazyTwoDimensionalStep u[j]).1 := by
          rw [List.take_succ_eq_append_getElem (by omega), blockFst_append]
          simp
        omega
  have hcat : u.take n ++ u.drop n = u := List.take_append_drop n u
  have htotal : blockFst (u.take n) + blockFst (u.drop n) = -((k + 1 : ℕ) : ℤ) := by
    rw [← blockFst_append, hcat]
    exact hu.2.1
  refine ⟨u.take n, u.drop n, ?_, ?_, hcat⟩
  · refine ⟨by simp [List.length_take, Nat.min_eq_left hn.1]; omega, hn.2, ?_⟩
    intro j hj
    simp only [List.length_take, Nat.min_eq_left hn.1] at hj
    rw [List.take_take, Nat.min_eq_left hj.le]
    exact hbefore j hj
  · refine ⟨by simp only [List.length_drop]; omega, by omega, ?_⟩
    intro j hj
    have hjn : n + j < u.length := by simp only [List.length_drop] at hj; omega
    have hproper := hu.2.2 (n + j) hjn
    have heq : blockFst (u.take (n + j)) =
        blockFst (u.take n) + blockFst ((u.drop n).take j) := by
      have hl : (u.take n).length = n := by
        simp [List.length_take, Nat.min_eq_left hn.1]
      calc
        _ = blockFst ((u.take n ++ u.drop n).take ((u.take n).length + j)) := by
          rw [hl, hcat]
        _ = _ := by rw [List.take_length_add_append, blockFst_append]
    rw [heq, hn.2] at hproper
    omega

private theorem stopped_prefix_eq {u v : List (Fin 3)}
    (hu : IsStoppedExcursionWord u) (hv : IsStoppedExcursionWord v) (h : u <+: v) :
    u = v := by
  have hle := h.length_le
  by_cases he : u.length = v.length
  · exact h.eq_of_length he
  · have hlt : u.length < v.length := by omega
    have hb := hv.2.2 u.length hlt
    rw [← List.prefix_iff_eq_take.mp h, hu.2.1] at hb
    omega

private theorem flat_injective {k : ℕ} (w z : Fin k → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) (hz : ∀ j, IsStoppedExcursionWord (z j))
    (he : (List.ofFn w).flatten = (List.ofFn z).flatten) : w = z := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at he
      have hpw : w 0 <+: w 0 ++ (List.ofFn fun j => w j.succ).flatten := ⟨_, rfl⟩
      have hpz : z 0 <+: w 0 ++ (List.ofFn fun j => w j.succ).flatten := by
        rw [he]
        exact ⟨_, rfl⟩
      have hh : w 0 = z 0 := by
        rcases List.prefix_or_prefix_of_prefix hpw hpz with h | h
        · exact stopped_prefix_eq (hw 0) (hz 0) h
        · exact (stopped_prefix_eq (hz 0) (hw 0) h).symm
      have ht : (List.ofFn fun j => w j.succ).flatten =
          (List.ofFn fun j => z j.succ).flatten := by
        rw [hh] at he
        exact List.append_cancel_left he
      have htail := ih (fun j => w j.succ) (fun j => z j.succ)
        (fun j => hw j.succ) (fun j => hz j.succ) ht
      funext j
      exact Fin.cases hh (fun i => congrFun htail i) j

private theorem passage_flat {k : ℕ} (hk : 1 ≤ k) (w : Fin k → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) :
    excursionPassage k (List.ofFn w).flatten := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons]
      cases k with
      | zero =>
          have hh : excursionPassage 1 (w 0) := hw 0
          simpa only [List.ofFn_zero, List.flatten_nil, List.append_nil] using hh
      | succ k =>
          have ht := ih (by omega) (fun j => w j.succ) (fun j => hw j.succ)
          have hh : excursionPassage 1 (w 0) := hw 0
          simpa only [Nat.add_comm 1 (k + 1)] using passage_append hh ht

private theorem passage_decode {k : ℕ} (hk : 1 ≤ k) (u : List (Fin 3))
    (hu : excursionPassage k u) :
    ∃ w : Fin k → List (Fin 3), (∀ j, IsStoppedExcursionWord (w j)) ∧
      (List.ofFn w).flatten = u := by
  induction k generalizing u with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          refine ⟨fun _ => u, fun _ => hu, ?_⟩
          simp [List.ofFn_succ]
      | succ k =>
          obtain ⟨v, t, hv, ht, he⟩ := passage_split (by omega) hu
          obtain ⟨w, hw, hflat⟩ := ih (by omega) t ht
          refine ⟨Fin.cons v w, ?_, ?_⟩
          · intro j
            exact Fin.cases hv (fun i => hw i) j
          · rw [List.ofFn_succ, List.flatten_cons]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hflat]
            exact he




theorem excursionPassage_flat_bijOn {k : ℕ} (hk : 1 ≤ k) :
    Set.BijOn (fun w : Fin k → List (Fin 3) => (List.ofFn w).flatten)
      {w | ∀ j, IsStoppedExcursionWord (w j)} {u | excursionPassage k u} := by
  refine ⟨fun w hw => passage_flat hk w hw, ?_, ?_⟩
  · intro w hw z hz he
    exact flat_injective w z hw hz he
  · intro u hu
    obtain ⟨w, hw, he⟩ := passage_decode hk u hu
    exact ⟨w, hw, he⟩

private theorem word_atom_zero {u : List (Fin 3)} (hu : ¬ IsStoppedExcursionWord u) :
    excursionWordLaw {u} = 0 := by
  apply measure_mono_null _ (ae_iff.mp ae_isStoppedExcursionWord_excursionWordLaw)
  simpa only [Set.singleton_subset_iff, Set.mem_ofPred_eq] using hu

private theorem tuple_atom {k : ℕ} (w : Fin k → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) :
    (Measure.pi fun _ : Fin k => excursionWordLaw) {w} =
      (1 / 3 : ℝ≥0∞) ^ (List.ofFn w).flatten.length := by
  rw [Measure.pi_singleton]
  simp_rw [excursionWordLaw_singleton _ (hw _)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp [List.sum_ofFn]

open Classical in



theorem lintegral_flat {k : ℕ} (hk : 1 ≤ k) (f : List (Fin 3) → ℝ≥0∞) :
    ∫⁻ w, f ((List.ofFn w).flatten) ∂(Measure.pi fun _ : Fin k => excursionWordLaw) =
      ∑' u, (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) * f u := by
  classical
  let S : Set (Fin k → List (Fin 3)) := {w | ∀ j, IsStoppedExcursionWord (w j)}
  let T : Set (List (Fin 3)) := {u | excursionPassage k u}
  let F := fun w : Fin k → List (Fin 3) => f ((List.ofFn w).flatten) *
    (Measure.pi fun _ : Fin k => excursionWordLaw) {w}
  let G := fun u : List (Fin 3) =>
    (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) * f u
  have hsupport : Function.support F ⊆ S := by
    intro w hw
    by_contra hn
    have hn' : ¬ ∀ j, IsStoppedExcursionWord (w j) := hn
    obtain ⟨j, hj⟩ := not_forall.mp hn'
    have hz : (Measure.pi fun _ : Fin k => excursionWordLaw) {w} = 0 := by
      rw [Measure.pi_singleton]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (word_atom_zero hj)
    apply hw
    change f ((List.ofFn w).flatten) *
      (Measure.pi fun _ : Fin k => excursionWordLaw) {w} = 0
    rw [hz, mul_zero]
  have hsupportG : Function.support G ⊆ T := by
    intro u hu
    by_contra hn
    have hn' : ¬ excursionPassage k u := hn
    apply hu
    change (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) * f u = 0
    rw [ite_eq_right hn', zero_mul]
  let cat : S → T := fun w =>
    ⟨(List.ofFn w.val).flatten, passage_flat hk w.val w.property⟩
  have hcat : Function.Bijective cat := by
    constructor
    · intro w z he
      apply Subtype.ext
      exact flat_injective w.val z.val w.property z.property (congrArg Subtype.val he)
    · intro u
      obtain ⟨w, hw, he⟩ := passage_decode hk u.val u.property
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩
  calc
    _ = ∑' w, F w := lintegral_countable' _
    _ = ∑' w : S, F w := (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' w : S, G (cat w) := by
      apply tsum_congr
      intro w
      simp only [F, G, cat, ite_eq_left (passage_flat hk w.val w.property)]
      rw [tuple_atom w.val w.property, mul_comm]
    _ = ∑' u : T, G u := tsum_comp_eq_tsum_of_bijective hcat (fun u : T => G u.val)
    _ = ∑' u, G u := tsum_subtype_eq_of_support_subset hsupportG

end DirectedDistances.RandomWalk
