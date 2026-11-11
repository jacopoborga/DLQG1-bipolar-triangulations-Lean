module

public import DirectedDistances.RandomWalk.ExcursionPassageSkeleton
public import DirectedDistances.Probability.GeometricCenteredMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.BigOperators.Fin




public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open DirectedDistances.Probability
open scoped ENNReal BigOperators



@[expose] def ValidSkel (k : ℕ) (s : List (Fin 3)) : Prop :=
  (∀ c ∈ s, c ≠ 1) ∧ excursionPassage k s

private theorem gapsAux_last_zero (u : List (Fin 3)) (pending : ℕ)
    (hu : u.getLast? = some 0) :
    (excursionSkeletonGapLengthsAux pending u).getLast? = some 0 := by
  induction u generalizing pending with
  | nil => simp at hu
  | cons c cs ih =>
      cases cs with
      | nil =>
          have hc : c = 0 := by simpa using hu
          subst c
          simp [excursionSkeletonGapLengthsAux]
      | cons d cs =>
          have ht : (d :: cs).getLast? = some 0 := by
            simpa only [List.getLast?_cons_cons] using hu
          by_cases hc : c = 1
          · simpa [excursionSkeletonGapLengthsAux, hc] using ih (pending + 1) ht
          · have hh := ih 0 ht
            rw [excursionSkeletonGapLengthsAux, ite_eq_right hc]
            rw [List.getLast?_cons, hh]
            rfl



theorem excursionPassage_gap_terminal_zero {k : ℕ} {u : List (Fin 3)}
    (hu : excursionPassage k u) :
    (excursionSkeletonGapLengths u).getLast? = some 0 :=
  gapsAux_last_zero u 0 (excursionPassage_getLast hu)



theorem excursionPassage_validSkel {k : ℕ} {u : List (Fin 3)}
    (hu : excursionPassage k u) : ValidSkel k (excursionSkeleton u) := by
  refine ⟨?_, (excursionPassage_skeleton_iff (excursionPassage_getLast hu)).mp hu⟩
  intro c hc
  exact (List.mem_filter.mp hc).2 |> of_decide_eq_true

private def interleavePassage {k : ℕ}
    (p : Σ s : {s // ValidSkel k s}, Fin s.val.length → ℕ) :
    {u // excursionPassage k u} :=
  ⟨excursionInterleave p.1.val (List.ofFn p.2 ++ [0]),
    (excursionPassage_interleave_iff p.1.property.1
      (by simp) (by simp)).mpr p.1.property.2⟩

private theorem interleavePassage_bijective (k : ℕ) :
    Function.Bijective (@interleavePassage k) := by
  constructor
  · rintro ⟨s, g⟩ ⟨t, h⟩ he
    have he' := congrArg Subtype.val he
    have hs : s = t := by
      apply Subtype.ext
      have hh := congrArg excursionSkeleton he'
      simpa only [interleavePassage,
        excursionSkeleton_interleave _ _ s.property.1,
        excursionSkeleton_interleave _ _ t.property.1] using hh
    subst t
    have hg : g = h := by
      apply List.ofFn_injective
      have hh := congrArg excursionSkeletonGapLengths he'
      have hgl : (List.ofFn g ++ [0]).length = s.val.length + 1 := by simp
      have hhl : (List.ofFn h ++ [0]).length = s.val.length + 1 := by simp
      change excursionSkeletonGapLengths (excursionInterleave s.val (List.ofFn g ++ [0])) =
        excursionSkeletonGapLengths (excursionInterleave s.val (List.ofFn h ++ [0])) at hh
      rw [excursionSkeletonGapLengths_interleave _ _ s.property.1 hgl,
        excursionSkeletonGapLengths_interleave _ _ s.property.1 hhl] at hh
      exact List.append_cancel_right hh
    subst h
    rfl
  · intro u
    let s : {s // ValidSkel k s} := ⟨excursionSkeleton u.val,
      excursionPassage_validSkel u.property⟩
    let gaps := excursionSkeletonGapLengths u.val
    have hd : gaps.dropLast ++ [0] = gaps :=
      List.dropLast_append_getLast? 0 (excursionPassage_gap_terminal_zero u.property)
    have hl : gaps.dropLast.length = s.val.length := by
      have hh := congrArg List.length hd
      have hlen := excursionSkeletonGapLengths_length u.val
      change gaps.length = s.val.length + 1 at hlen
      simp only [List.length_append, List.length_singleton] at hh
      omega
    let g : Fin s.val.length → ℕ := fun i => gaps.dropLast[i.val]'(by omega)
    have hg : List.ofFn g = gaps.dropLast := by
      apply List.ext_getElem
      · simpa using hl.symm
      · intro i hi hj
        simp [g]
    refine ⟨⟨s, g⟩, Subtype.ext ?_⟩
    change excursionInterleave s.val (List.ofFn g ++ [0]) = u.val
    rw [hg, hd]
    exact excursionInterleave_skeleton_gaps u.val

private theorem geomTwoThirds_atom (n : ℕ) :
    geomTwoThirds {n} = (2 / 3 : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ n := by
  rw [geomTwoThirds, Measure.sum_smul_dirac_singleton,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
  norm_num [ENNReal.ofReal_div_of_pos]

private theorem gap_factorization (g : List ℕ) :
    (1 / 3 : ℝ≥0∞) ^ (g.length + g.sum) =
      (1 / 2 : ℝ≥0∞) ^ g.length *
        (g.map (fun n => (2 / 3 : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ n)).prod := by
  induction g with
  | nil => simp
  | cons n g ih =>
      simp only [List.length_cons, List.sum_cons, List.map_cons, List.prod_cons]
      rw [show g.length + 1 + (n + g.sum) = (g.length + g.sum) + (n + 1) by omega,
        pow_add, ih, pow_succ, pow_succ]
      have hh : (1 / 2 : ℝ≥0∞) * (2 / 3) = 1 / 3 :=
        ENNReal.div_mul_div_cancel (by norm_num) (by norm_num)
      calc
        _ = ((1 / 2 : ℝ≥0∞) ^ g.length *
            (g.map (fun n => (2 / 3 : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ n)).prod) *
            ((1 / 3 : ℝ≥0∞) ^ n * ((1 / 2) * (2 / 3))) := by rw [hh]
        _ = _ := by ac_rfl



theorem excursionInterleave_atom_factorization (s : List (Fin 3))
    (g : Fin s.length → ℕ) :
    (1 / 3 : ℝ≥0∞) ^ (excursionInterleave s (List.ofFn g ++ [0])).length =
      (1 / 2 : ℝ≥0∞) ^ s.length *
        (Measure.pi fun _ : Fin s.length => geomTwoThirds) {g} := by
  rw [excursionInterleave_length, Measure.pi_singleton]
  simp_rw [geomTwoThirds_atom]
  have hh := gap_factorization (List.ofFn g)
  simpa [List.map_ofFn, Fin.prod_ofFn] using hh



theorem excursionSkeleton_gap_lintegral (m : ℕ) (F : ℝ → ℝ≥0∞) :
    (∑' g : Fin m → ℕ,
      (Measure.pi fun _ : Fin m => geomTwoThirds) {g} * F (∑ i, (g i : ℝ))) =
      ∫⁻ g, F (∑ i, (g i : ℝ)) ∂(Measure.pi fun _ : Fin m => geomTwoThirds) := by
  rw [lintegral_countable']
  apply tsum_congr
  intro g
  exact mul_comm _ _

open Classical in


theorem tsum_passage_eq {k : ℕ} (_hk : 1 ≤ k) (F : ℕ → ℝ → ℝ≥0∞) :
    (∑' u, (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) *
      F (excursionSkeleton u).length ((excursionSkeletonGapLengths u).sum : ℝ)) =
    ∑' s, (if ValidSkel k s then (1 / 2 : ℝ≥0∞) ^ s.length else 0) *
      ∫⁻ g, F s.length (∑ i, (g i : ℝ))
        ∂(Measure.pi fun _ : Fin s.length => geomTwoThirds) := by
  classical
  let W := fun u : List (Fin 3) =>
    (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) *
      F (excursionSkeleton u).length ((excursionSkeletonGapLengths u).sum : ℝ)
  let V := fun s : List (Fin 3) =>
    (if ValidSkel k s then (1 / 2 : ℝ≥0∞) ^ s.length else 0) *
      ∫⁻ g, F s.length (∑ i, (g i : ℝ))
        ∂(Measure.pi fun _ : Fin s.length => geomTwoThirds)
  have hw : Function.support W ⊆ {u | excursionPassage k u} := by
    intro u hu
    by_contra hn
    have hn' : ¬ excursionPassage k u := hn
    apply hu
    change (if excursionPassage k u then (1 / 3 : ℝ≥0∞) ^ u.length else 0) *
      F (excursionSkeleton u).length ((excursionSkeletonGapLengths u).sum : ℝ) = 0
    rw [ite_eq_right hn', zero_mul]
  have hv : Function.support V ⊆ {s | ValidSkel k s} := by
    intro s hs
    by_contra hn
    have hn' : ¬ ValidSkel k s := hn
    apply hs
    change (if ValidSkel k s then (1 / 2 : ℝ≥0∞) ^ s.length else 0) *
      (∫⁻ g, F s.length (∑ i, (g i : ℝ))
        ∂(Measure.pi fun _ : Fin s.length => geomTwoThirds)) = 0
    rw [ite_eq_right hn', zero_mul]
  calc
    _ = ∑' u : {u // excursionPassage k u}, W u :=
      (tsum_subtype_eq_of_support_subset hw).symm
    _ = ∑' p : Σ s : {s // ValidSkel k s}, Fin s.val.length → ℕ,
        W (interleavePassage p).val :=
      (tsum_comp_eq_tsum_of_bijective (interleavePassage_bijective k)
        (fun u => W u.val)).symm
    _ = ∑' s : {s // ValidSkel k s}, V s := by
      rw [tsum_sigma']
      apply tsum_congr
      intro s
      dsimp [V]
      rw [ite_eq_left s.property, ← excursionSkeleton_gap_lintegral,
        ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro g
      have hp := (interleavePassage (⟨s, g⟩)).property
      dsimp [W]
      rw [ite_eq_left hp]
      change (1 / 3 : ℝ≥0∞) ^
          (excursionInterleave s.val (List.ofFn g ++ [0])).length *
        F (excursionSkeleton (excursionInterleave s.val (List.ofFn g ++ [0]))).length
          ((excursionSkeletonGapLengths
            (excursionInterleave s.val (List.ofFn g ++ [0]))).sum : ℝ) = _
      rw [excursionSkeleton_interleave _ _ s.property.1,
        excursionSkeletonGapLengths_interleave _ _ s.property.1 (by simp),
        excursionInterleave_atom_factorization]
      simp only [List.sum_append, List.sum_singleton, add_zero]
      have hsum : ((List.ofFn g).sum : ℝ) = ∑ i, (g i : ℝ) := by
        rw [List.sum_ofFn, Nat.cast_sum]
      rw [hsum, mul_assoc]
    _ = ∑' s, V s := tsum_subtype_eq_of_support_subset hv

end DirectedDistances.RandomWalk
