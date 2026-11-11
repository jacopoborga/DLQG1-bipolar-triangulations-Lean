module

public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory
public import DirectedDistances.RandomWalk.IIDVectorWalk
public import DirectedDistances.RandomWalk.ConditionedStrongMarkov
public import DirectedDistances.PaperProofs.Section3.BoltzmannFinite
import Mathlib.MeasureTheory.Integral.Lebesgue.Map






public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open DirectedDistances.PaperProofs.Section3
open scoped ENNReal

private def firstHitCodePrefix (k : ℕ) (ω : ℕ → Fin 3) :
    Fin (k + 1) → ℤ × ℤ := fun j => codeWalk ω j.val

private def firstHitCodeWord (k : ℕ) (ω : ℕ → Fin 3) : Fin k → Fin 3 :=
  fun i => ω (i.val + 1)

private theorem firstHitCodePrefix_eq_lazyPrefix (k : ℕ) (ω : ℕ → Fin 3) :
    firstHitCodePrefix k ω =
      lazyTwoDimensionalPrefix 0 0 (firstHitCodeWord k ω) := by
  funext j
  have hsum (f : Fin 3 → ℤ) :
      ∑ i ∈ Finset.range j.val, f (ω (i + 1)) =
        ∑ i : Fin k with i.val < j.val, f (ω (i.val + 1)) := by
    have hs : Finset.range j.val = (Finset.range k).filter (fun i => i < j.val) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    rw [hs, Finset.sum_filter, Finset.sum_filter,
      Fin.sum_univ_eq_sum_range (fun i => if i < j.val then f (ω (i + 1)) else 0) k]
  unfold firstHitCodePrefix firstHitCodeWord codeWalk lazyTwoDimensionalPrefix
  apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, zero_add] <;>
    first | exact hsum (fun c => (lazyTwoDimensionalStep c).1)
          | exact hsum (fun c => (lazyTwoDimensionalStep c).2)

private theorem iidCodeMeasure_map_firstHitCodeWord (k : ℕ) :
    iidCodeMeasure.map (firstHitCodeWord k) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3)) := by
  classical
  have hf : firstHitCodeWord k =
      (fun q : Fin (k + 1) → Fin 3 => fun i : Fin k => q i.succ) ∘
        (fun ω : ℕ → Fin 3 => fun j : Fin (k + 1) => ω j.val) := by
    funext ω i
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    iidCodeMeasure_map_prefix]
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (k + 1) => if j.val = 0 then
      Measure.dirac (0 : Fin 3) else uniformCodeMeasure) 0
  have hsnd : (fun q : Fin (k + 1) → Fin 3 => fun i : Fin k => q i.succ) =
      Prod.snd ∘ MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => Fin 3) 0 := by
    funext q i
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [hsnd, ← Measure.map_map measurable_snd (MeasurableEquiv.measurable _),
    hmp.map_eq, Measure.map_snd_prod]
  simp only [Fin.val_zero, ite_true, measure_univ, one_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Fin.succAbove_zero]
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton, ENNReal.inv_pow]

private theorem iidCodeMeasure_map_firstHitCodePrefix (k : ℕ) :
    iidCodeMeasure.map (firstHitCodePrefix k) =
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0) := by
  have hw : Measurable (firstHitCodeWord k) :=
    Measurable.of_eval fun i => measurable_pi_apply (i.val + 1)
  rw [show firstHitCodePrefix k =
      (lazyTwoDimensionalPrefix 0 0) ∘ firstHitCodeWord k from by
        funext ω
        exact firstHitCodePrefix_eq_lazyPrefix k ω]
  rw [← Measure.map_map (measurable_of_countable _) hw,
    iidCodeMeasure_map_firstHitCodeWord]

/-- Fixed-time bridge from the conditioned path prefix to the iid code walk.
Every path in `S` is nonnegative through time `k` and ends at first -/
theorem conditionedVectorPathLaw_zero_zero_prefix_bridge
    (k ell : ℕ) (S : Set (Fin (k + 1) → ℤ × ℤ))
    (hS : S ⊆ {q | (∀ j, 0 ≤ (q j).1) ∧
      (q (Fin.last k)).1 = (ell : ℤ)}) :
    conditionedVectorPathLaw 0 0
        {p | (fun j : Fin (k + 1) => p j.val) ∈ S} =
      (ell + 1 : ℝ≥0∞) * iidCodeMeasure
        {ω | (fun j : Fin (k + 1) => codeWalk ω j.val) ∈ S} := by
  classical
  let pref : (ℕ → ℤ × ℤ) → Fin (k + 1) → ℤ × ℤ :=
    fun p j => p j.val
  let dens : (Fin (k + 1) → ℤ × ℤ) → ℝ≥0∞ := fun q =>
    if ∀ j, 0 ≤ (q j).1 then
      ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0
  have hSmeas : MeasurableSet S := (Set.to_countable S).measurableSet
  have hpref : Measurable pref := Measurable.of_eval fun j => measurable_pi_apply j.val
  have hprefix := conditionedVectorPathLaw_map_prefix 0 0 k
  have hmap : (conditionedVectorPathLaw 0 0).map pref =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity dens := by
    simpa [pref, dens] using hprefix
  have hdens_eq : ∀ q ∈ S, dens q = (ell + 1 : ℝ≥0∞) := by
    intro q hq
    have hq' := hS hq
    change (if ∀ j, 0 ≤ (q j).1 then
      ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0) = _
    rw [ite_eq_left hq'.1]
    have hend : (q (Fin.last k)).1 = (ell : ℤ) := hq'.2
    rw [hend]
    have hcast : ((ell : ℤ) : ℝ) + 1 = ((ell + 1 : ℕ) : ℝ) := by
      norm_cast
    rw [hcast]
    have hdiv : ((ell + 1 : ℕ) : ℝ) / ((0 : ℝ) + 1) =
        ((ell + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hdiv]
    rw [ENNReal.ofReal_natCast]
    norm_num
  have hintegral :
      ∫⁻ q in S, dens q
          ∂((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
            (lazyTwoDimensionalPrefix 0 0)) =
        (ell + 1 : ℝ≥0∞) *
          ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
            (lazyTwoDimensionalPrefix 0 0)) S := by
    calc
      _ = ∫⁻ q in S, (ell + 1 : ℝ≥0∞)
          ∂((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
            (lazyTwoDimensionalPrefix 0 0)) := by
          apply setLIntegral_congr_fun hSmeas
          exact hdens_eq
      _ = _ := by rw [setLIntegral_const, mul_comm]
  calc
    conditionedVectorPathLaw 0 0 {p | pref p ∈ S} =
        ((conditionedVectorPathLaw 0 0).map pref) S := by
      change conditionedVectorPathLaw 0 0 (pref ⁻¹' S) = _
      exact (Measure.map_apply hpref hSmeas).symm
    _ = (((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity dens) S := by rw [hmap]
    _ = ∫⁻ q in S, dens q
        ∂((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)) := withDensity_apply _ hSmeas
    _ = (ell + 1 : ℝ≥0∞) *
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)) S := hintegral
    _ = (ell + 1 : ℝ≥0∞) * iidCodeMeasure
        {ω | (fun j : Fin (k + 1) => codeWalk ω j.val) ∈ S} := by
      rw [← iidCodeMeasure_map_firstHitCodePrefix k]
      have hcode : Measurable (firstHitCodePrefix k) := by
        change Measurable (fun ω : ℕ → Fin 3 =>
          fun j : Fin (k + 1) => codeWalk ω j.val)
        exact Measurable.of_eval fun j =>
          (measurable_pi_apply j.val).comp measurable_codeWalk
      rw [Measure.map_apply hcode hSmeas]
      have hpre : firstHitCodePrefix k ⁻¹' S =
          {ω | (fun j : Fin (k + 1) => codeWalk ω j.val) ∈ S} := by
        ext ω
        rfl
      rw [hpre]

private theorem conditionedVectorPathLaw_prefix_inter_nonnegative
    (k : ℕ) (S : Set (Fin (k + 1) → ℤ × ℤ)) :
    conditionedVectorPathLaw 0 0
        {p | conditionedVectorPrefix k p ∈ S} =
      conditionedVectorPathLaw 0 0
        {p | conditionedVectorPrefix k p ∈ S ∩
          {q | ∀ j, 0 ≤ (q j).1}} := by
  classical
  let pref : (ℕ → ℤ × ℤ) → Fin (k + 1) → ℤ × ℤ :=
    fun p j => p j.val
  let nonneg : Set (Fin (k + 1) → ℤ × ℤ) :=
    {q | ∀ j, 0 ≤ (q j).1}
  let bad : Set (Fin (k + 1) → ℤ × ℤ) := S \ nonneg
  let dens : (Fin (k + 1) → ℤ × ℤ) → ℝ≥0∞ := fun q =>
    if ∀ j, 0 ≤ (q j).1 then
      ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) /
        ((0 : ℝ) + 1)) else 0
  have hbad : MeasurableSet bad := (Set.to_countable bad).measurableSet
  have hzero :
      conditionedVectorPathLaw 0 0 (pref ⁻¹' bad) = 0 := by
    have hmap : (conditionedVectorPathLaw 0 0).map pref =
        ((Measure.uniformOfFinset
          (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity dens := by
      rw [show pref = (fun p j => p j.val) from rfl,
        conditionedVectorPathLaw_map_prefix 0 0 k]
      congr 1
      funext q
      by_cases hq : ∀ j, 0 ≤ (q j).1 <;> simp [dens, hq]
    rw [← Measure.map_apply (Measurable.of_eval fun j =>
        measurable_pi_apply j.val) hbad,
      hmap, withDensity_apply _ hbad]
    apply setLIntegral_eq_zero hbad
    intro q hq
    simp only [bad, Set.mem_sdiff] at hq
    have hn : ¬ ∀ j, 0 ≤ (q j).1 := by
      simpa [nonneg] using hq.2
    simp [dens, hn]
  let good : Set (Fin (k + 1) → ℤ × ℤ) := S ∩ nonneg
  let badPath : Set (ℕ → ℤ × ℤ) := pref ⁻¹' bad
  let goodPath : Set (ℕ → ℤ × ℤ) := pref ⁻¹' good
  have hdecomp : pref ⁻¹' S = goodPath ∪ badPath := by
    ext p
    simp only [goodPath, badPath, Set.mem_preimage, good, bad,
      Set.mem_inter_iff, Set.mem_sdiff, Set.mem_union]
    tauto
  have hdisj : Disjoint goodPath badPath := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hq.2 hp.2
  have hgood : MeasurableSet goodPath :=
    (Set.to_countable good).measurableSet.preimage
      (measurable_conditionedVectorPrefix k)
  have hbadPath : MeasurableSet badPath :=
    hbad.preimage (measurable_conditionedVectorPrefix k)
  change conditionedVectorPathLaw 0 0 (pref ⁻¹' S) =
    conditionedVectorPathLaw 0 0 (pref ⁻¹' good)
  rw [hdecomp, measure_union hdisj hbadPath, hzero, add_zero]

private theorem conditionedFirstHit_eq_boltzmannTau
    (r : ℕ) (ω : ℕ → Fin 3)
    (hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ)) :
    conditionedSecondCoordinateFirstHit r (fun n => codeWalk ω n) =
      (boltzmannTau r ω : ℕ∞) := by
  classical
  simp [conditionedSecondCoordinateFirstHit, boltzmannTau, hhit]

private theorem conditionedFirstHit_value (r k : ℕ)
    (p : ℕ → ℤ × ℤ)
    (hτ : conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)) :
    (p k).2 = -(r : ℤ) := by
  classical
  unfold conditionedSecondCoordinateFirstHit at hτ
  by_cases h : ∃ n, (p n).2 = -(r : ℤ)
  · rw [dite_eq_left h] at hτ
    have hk : Nat.find h = k := by exact_mod_cast hτ
    rw [← hk]
    exact Nat.find_spec h
  · rw [dite_eq_right h] at hτ
    exact (ENat.top_ne_natCast k hτ).elim

private theorem boltzmannTau_le_hit (r t : ℕ) (ω : ℕ → Fin 3)
    (ht : (codeWalk ω t).2 = -(r : ℤ)) : boltzmannTau r ω ≤ t := by
  unfold boltzmannTau
  have hex : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := ⟨t, ht⟩
  rw [dite_eq_left hex]
  exact Nat.find_min' hex ht

private def firstHitCodePath (ω : ℕ → Fin 3) : ℕ → ℤ × ℤ :=
  fun n => codeWalk ω n

private def firstHitPathSlice (r ell k : ℕ) (A : Set (ℕ → ℤ × ℤ)) :
    Set (ℕ → ℤ × ℤ) :=
  A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
    {p | (p k).1 = (ell : ℤ)}

private def firstHitCodeSlice (r ell k : ℕ) (A : Set (ℕ → ℤ × ℤ)) :
    Set (ℕ → Fin 3) :=
  {ω | firstHitCodePath ω ∈ A} ∩
    {ω | conditionedSecondCoordinateFirstHit r (firstHitCodePath ω) =
      (k : ℕ∞)} ∩ boltzmannEvent r ∩
    {ω | (codeWalk ω k).1 = (ell : ℤ)}

private theorem firstHit_path_slice_eq_prefix (r ell k : ℕ)
    (A : Set (ℕ → ℤ × ℤ))
    (S : Set (Fin (k + 1) → ℤ × ℤ))
    (hA : A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
      conditionedVectorPrefix k ⁻¹' S) :
    conditionedVectorPathLaw 0 0 (firstHitPathSlice r ell k A) =
      conditionedVectorPathLaw 0 0
        {p | conditionedVectorPrefix k p ∈
          S ∩ {q | (∀ j, 0 ≤ (q j).1) ∧
            (q (Fin.last k)).1 = (ell : ℤ)}} := by
  have hset : firstHitPathSlice r ell k A =
      {p | conditionedVectorPrefix k p ∈
        S ∩ {q | (q (Fin.last k)).1 = (ell : ℤ)}} := by
    ext p
    simp only [firstHitPathSlice, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hpA, hτ⟩, hend⟩
      have hmem : p ∈ A ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} :=
        ⟨hpA, hτ⟩
      rw [hA] at hmem
      exact ⟨hmem, by simpa [conditionedVectorPrefix, Fin.val_last] using hend⟩
    · rintro ⟨hmem, hend⟩
      have hmem' : p ∈ A ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
        rw [hA]
        exact hmem
      exact ⟨hmem', by simpa [conditionedVectorPrefix, Fin.val_last] using hend⟩
  rw [hset]
  have hnonneg := conditionedVectorPathLaw_prefix_inter_nonnegative k
    (S ∩ {q | (q (Fin.last k)).1 = (ell : ℤ)})
  calc
    _ = conditionedVectorPathLaw 0 0
        {p | conditionedVectorPrefix k p ∈
          (S ∩ {q | (q (Fin.last k)).1 = (ell : ℤ)}) ∩
            {q | ∀ j, 0 ≤ (q j).1}} := hnonneg
    _ = _ := by
      congr 1
      ext q
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto

private theorem firstHit_code_slice_eq_prefix (r ell k : ℕ)
    (A : Set (ℕ → ℤ × ℤ))
    (S : Set (Fin (k + 1) → ℤ × ℤ))
    (hA : A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
      conditionedVectorPrefix k ⁻¹' S) :
    firstHitCodeSlice r ell k A =
      {ω | firstHitCodePrefix k ω ∈
        S ∩ {q | (∀ j, 0 ≤ (q j).1) ∧
          (q (Fin.last k)).1 = (ell : ℤ)}} := by
  ext ω
  constructor
  · rintro ⟨⟨⟨hAω, hτ⟩, hE⟩, hend⟩
    have hpre : firstHitCodePrefix k ω ∈ S := by
      have hmem : firstHitCodePath ω ∈ A ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} :=
        ⟨hAω, hτ⟩
      rw [hA] at hmem
      have heq : firstHitCodePrefix k ω =
          conditionedVectorPrefix k (firstHitCodePath ω) := rfl
      simpa only [Set.mem_preimage, heq] using hmem
    have hnonneg : ∀ j, 0 ≤ (firstHitCodePrefix k ω j).1 := by
      intro j
      obtain ⟨t, ht, hstay⟩ := hE
      have hle := boltzmannTau_le_hit r t ω ht
      have hτeq := conditionedFirstHit_eq_boltzmannTau r ω ⟨t, ht⟩
      have hk : boltzmannTau r ω = k := by
        have : (boltzmannTau r ω : ℕ∞) = (k : ℕ∞) := hτeq.symm.trans hτ
        exact_mod_cast this
      have hjk : j.val ≤ k := by omega
      have hj : j.val ≤ t := by
        exact le_trans (by simpa [hk] using hjk) hle
      simpa [firstHitCodePrefix, codeWalk] using hstay j.val hj
    have hend' : (firstHitCodePrefix k ω (Fin.last k)).1 = (ell : ℤ) := by
      simpa [firstHitCodePrefix, Fin.val_last] using hend
    exact ⟨hpre, hnonneg, hend'⟩
  · intro h
    rcases h with ⟨hpre, hnonneg, hend⟩
    have hτ : conditionedSecondCoordinateFirstHit r (firstHitCodePath ω) =
        (k : ℕ∞) := by
      have hmem : firstHitCodePath ω ∈
          conditionedVectorPrefix k ⁻¹' S := by
        have heq : firstHitCodePrefix k ω =
            conditionedVectorPrefix k (firstHitCodePath ω) := rfl
        simpa only [Set.mem_preimage, heq] using hpre
      have hpair : firstHitCodePath ω ∈ A ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
        rw [hA]
        exact hmem
      exact hpair.2
    have hhit : (codeWalk ω k).2 = -(r : ℤ) := by
      exact conditionedFirstHit_value r k _ hτ
    have hnonneg' : ∀ j ≤ k, 0 ≤ (codeWalk ω j).1 := by
      intro j hj
      have := hnonneg ⟨j, by omega⟩
      simpa [firstHitCodePrefix] using this
    have hE : ω ∈ boltzmannEvent r := ⟨k, hhit, hnonneg'⟩
    have hτcode := conditionedFirstHit_eq_boltzmannTau r ω ⟨k, hhit⟩
    have hτ' : boltzmannTau r ω = k := by exact_mod_cast hτcode.symm.trans hτ
    have hAω : firstHitCodePath ω ∈ A := by
      have hmem : firstHitCodePath ω ∈
          conditionedVectorPrefix k ⁻¹' S := by
        have heq : firstHitCodePrefix k ω =
            conditionedVectorPrefix k (firstHitCodePath ω) := rfl
        simpa only [Set.mem_preimage, heq] using hpre
      have hpair : firstHitCodePath ω ∈ A ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
        rw [hA]
        exact hmem
      exact hpair.1
    have hend' : (codeWalk ω k).1 = (ell : ℤ) := by
      simpa [firstHitCodePrefix, Fin.val_last] using hend
    refine ⟨⟨⟨hAω, hτ⟩, hE⟩, ?_⟩
    simpa [hτ'] using hend'



theorem conditionedVectorPathLaw_zero_zero_firstHit_bridge
    (r ell : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (S : ∀ k : ℕ, Set (Fin (k + 1) → ℤ × ℤ))
    (hA : ∀ k : ℕ,
      A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
        conditionedVectorPrefix k ⁻¹' S k) :
    conditionedVectorPathLaw 0 0
        (A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
          {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
            (ell : ℤ)}) =
      (ell + 1 : ℝ≥0∞) * iidCodeMeasure
        ((fun ω n => codeWalk ω n) ⁻¹' A ∩ boltzmannEvent r ∩
          {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}) := by
  classical
  let τ := conditionedSecondCoordinateFirstHit r
  let P : (ℕ → Fin 3) → (ℕ → ℤ × ℤ) := fun ω n => codeWalk ω n
  let C : ℕ → Set (ℕ → ℤ × ℤ) := fun k => firstHitPathSlice r ell k A
  let D : ℕ → Set (ℕ → Fin 3) := fun k => firstHitCodeSlice r ell k A
  let X : Set (ℕ → ℤ × ℤ) :=
    A ∩ {p | τ p < ⊤} ∩
      {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let Y : Set (ℕ → Fin 3) :=
    P ⁻¹' A ∩ boltzmannEvent r ∩
      {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}
  have hX : X = ⋃ k, C k := by
    ext p
    simp only [X, C, firstHitPathSlice, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_ofPred_eq, τ]
    constructor
    · rintro ⟨⟨hpA, hfinite⟩, hend⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite.ne
      have hτk : conditionedSecondCoordinateFirstHit r p = (k : ℕ∞) :=
        hk.symm
      have hto :
          (conditionedSecondCoordinateFirstHit r p).toNat = k := by
        simp [hτk]
      refine ⟨k, ⟨⟨hpA, hτk⟩, ?_⟩⟩
      simpa [hto] using hend
    · rintro ⟨k, ⟨⟨hpA, hτk⟩, hend⟩⟩
      refine ⟨⟨hpA, ?_⟩, ?_⟩
      · rw [hτk]
        exact ENat.natCast_lt_top k
      · simpa [hτk] using hend
  have hY : Y = ⋃ k, D k := by
    ext ω
    simp only [Y, D, firstHitCodeSlice, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, P]
    constructor
    · intro hh
      have hAω := hh.1.1
      have hevent := hh.1.2
      have hend := hh.2
      let k := boltzmannTau r ω
      obtain ⟨t, ht, hstay⟩ := hevent
      have hevent' : ω ∈ boltzmannEvent r := ⟨t, ht, hstay⟩
      have hτk :
          conditionedSecondCoordinateFirstHit r (fun n => codeWalk ω n) =
            (k : ℕ∞) := by
        simpa [k] using conditionedFirstHit_eq_boltzmannTau r ω ⟨t, ht⟩
      refine ⟨k, ⟨⟨⟨hAω, hτk⟩, hevent'⟩, ?_⟩⟩
      simpa [k] using hend
    · rintro ⟨k, ⟨⟨⟨hAω, hτk⟩, hevent⟩, hend⟩⟩
      obtain ⟨t, ht, hstay⟩ := hevent
      have hevent' : ω ∈ boltzmannEvent r := ⟨t, ht, hstay⟩
      have hτcode := conditionedFirstHit_eq_boltzmannTau r ω ⟨t, ht⟩
      have htk : boltzmannTau r ω = k := by
        exact_mod_cast hτcode.symm.trans hτk
      refine ⟨⟨hAω, hevent'⟩, ?_⟩
      simpa [htk] using hend
  have hCmeas : ∀ k, MeasurableSet (C k) := by
    intro k
    have hset : C k = conditionedVectorPrefix k ⁻¹' S k ∩
        {p | (p k).1 = (ell : ℤ)} := by
      ext p
      simp only [C, firstHitPathSlice, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · rintro ⟨⟨hpA, hτ⟩, hend⟩
        have hmem : p ∈ A ∩
            {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} :=
          ⟨hpA, hτ⟩
        rw [hA k] at hmem
        exact ⟨hmem, hend⟩
      · rintro ⟨hmem, hend⟩
        have hpair : p ∈ A ∩
            {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
          rw [hA k]
          exact hmem
        exact ⟨hpair, hend⟩
    rw [hset]
    exact ((Set.to_countable _).measurableSet.preimage
      (measurable_conditionedVectorPrefix k)).inter
        ((measurableSet_singleton _).preimage
          (measurable_fst.comp (measurable_pi_apply k)))
  have hDmeas : ∀ k, MeasurableSet (D k) := by
    intro k
    have hset : D k = {ω | firstHitCodePrefix k ω ∈
        S k ∩ {q | (∀ j, 0 ≤ (q j).1) ∧
          (q (Fin.last k)).1 = (ell : ℤ)}} := by
      change firstHitCodeSlice r ell k A = _
      exact firstHit_code_slice_eq_prefix r ell k A (S k) (hA k)
    rw [hset]
    exact (Set.to_countable _).measurableSet.preimage
      (Measurable.of_eval fun j =>
        (measurable_pi_apply j.val).comp measurable_codeWalk)
  have hCdisj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro p hpi hpj
    apply hij
    exact_mod_cast hpi.1.2.symm.trans hpj.1.2
  have hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hωi hωj
    apply hij
    exact_mod_cast hωi.1.1.2.symm.trans hωj.1.1.2
  have hslice : ∀ k, conditionedVectorPathLaw 0 0 (C k) =
      (ell + 1 : ℝ≥0∞) * iidCodeMeasure (D k) := by
    intro k
    let G : Set (Fin (k + 1) → ℤ × ℤ) :=
      S k ∩ {q | (∀ j, 0 ≤ (q j).1) ∧
        (q (Fin.last k)).1 = (ell : ℤ)}
    have hbridge := conditionedVectorPathLaw_zero_zero_prefix_bridge
      k ell G (by
        intro q hq
        exact hq.2)
    have hpath := firstHit_path_slice_eq_prefix r ell k A (S k) (hA k)
    have hcode := firstHit_code_slice_eq_prefix r ell k A (S k) (hA k)
    have hCodeSet :
        {ω | (fun j : Fin (k + 1) => codeWalk ω j.val) ∈ G} =
          {ω | firstHitCodePrefix k ω ∈ G} := by
      ext ω
      rfl
    calc
      conditionedVectorPathLaw 0 0 (C k) =
          conditionedVectorPathLaw 0 0
            {p | conditionedVectorPrefix k p ∈ G} := by
        simpa [C, G] using hpath
      _ = (ell + 1 : ℝ≥0∞) * iidCodeMeasure
          {ω | (fun j : Fin (k + 1) => codeWalk ω j.val) ∈ G} := hbridge
      _ = (ell + 1 : ℝ≥0∞) * iidCodeMeasure (D k) := by
        rw [hCodeSet, ← hcode]
  calc
    conditionedVectorPathLaw 0 0 X =
        ∑' k, conditionedVectorPathLaw 0 0 (C k) := by
      rw [hX, measure_iUnion hCdisj hCmeas]
    _ = ∑' k, (ell + 1 : ℝ≥0∞) * iidCodeMeasure (D k) := by
      exact tsum_congr hslice
    _ = (ell + 1 : ℝ≥0∞) * ∑' k, iidCodeMeasure (D k) := by
      rw [ENNReal.tsum_mul_left]
    _ = (ell + 1 : ℝ≥0∞) * iidCodeMeasure Y := by
      rw [hY, measure_iUnion hDdisj hDmeas]

private theorem measurableSet_of_conditionedVectorPast (k : ℕ)
    (C : Set (ℕ → ℤ × ℤ))
    (hC : MeasurableSet[conditionedVectorPast k] C) : MeasurableSet C := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hC
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix k)

private theorem measurableSet_conditionedVectorPast_endpoint
    (ell k : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      {p : ℕ → ℤ × ℤ | (p k).1 = (ell : ℤ)} := by
  refine ⟨{q : Fin (k + 1) → ℤ × ℤ |
    (q (Fin.last k)).1 = (ell : ℤ)},
    (Set.to_countable _).measurableSet, ?_⟩
  rfl

private theorem measurableSet_firstHitPathEndpointSlice
    (r ell k : ℕ) :
    MeasurableSet
      ({p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  exact measurableSet_of_conditionedVectorPast k _
    ((measurableSet_conditionedVectorPast_firstHit_eq r k).inter
      (measurableSet_conditionedVectorPast_endpoint ell k))

private theorem firstHitCodePrefix_measurable (k : ℕ) :
    Measurable (firstHitCodePrefix k) := by
  exact Measurable.of_eval fun j =>
    (measurable_pi_apply j.val).comp measurable_codeWalk

private def conditionedFirstHitPrefixSet (r k : ℕ) :
    Set (Fin (k + 1) → ℤ × ℤ) :=
  {q | (q (Fin.last k)).2 = -(r : ℤ) ∧
    ∀ j : ℕ, ∀ hj : j < k,
      (q ⟨j, by omega⟩).2 ≠ -(r : ℤ)}

private theorem conditionedVectorFirstHit_preimage (r k : ℕ) :
    conditionedVectorPrefix k ⁻¹' conditionedFirstHitPrefixSet r k =
      {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
  ext p
  have hpref : conditionedVectorPrefix k p ∈
      conditionedFirstHitPrefixSet r k ↔
        (p k).2 = -(r : ℤ) ∧ ∀ j < k, (p j).2 ≠ -(r : ℤ) := by
    simp only [conditionedFirstHitPrefixSet, Set.mem_ofPred_eq,
      conditionedVectorPrefix, Fin.val_last]
  have hhit : conditionedSecondCoordinateFirstHit r p = (k : ℕ∞) ↔
      (p k).2 = -(r : ℤ) ∧ ∀ j < k, (p j).2 ≠ -(r : ℤ) := by
    unfold conditionedSecondCoordinateFirstHit
    by_cases h : ∃ n, (p n).2 = -(r : ℤ)
    · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
    · rw [dite_eq_right h]
      constructor
      · intro he
        exact False.elim (ENat.top_ne_natCast k he)
      · rintro ⟨hk, _⟩
        exact False.elim (h ⟨k, hk⟩)
  exact hpref.trans hhit.symm



theorem conditionedVectorPathLaw_zero_zero_firstHit_conditional
    (r ell : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (S : ∀ k : ℕ, Set (Fin (k + 1) → ℤ × ℤ))
    (hA : ∀ k : ℕ,
      A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
        conditionedVectorPrefix k ⁻¹' S k)
    (hpos : 0 < iidCodeMeasure
      (boltzmannEvent r ∩
        {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)})) :
    (conditionedVectorPathLaw 0 0)[A |
      {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
          (ell : ℤ)}] =
    iidCodeMeasure[(fun ω n => codeWalk ω n) ⁻¹' A |
      boltzmannEvent r ∩
        {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}] := by
  classical
  let τ := conditionedSecondCoordinateFirstHit r
  let P : (ℕ → Fin 3) → (ℕ → ℤ × ℤ) := fun ω n => codeWalk ω n
  let E : Set (ℕ → ℤ × ℤ) :=
    {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let F : Set (ℕ → Fin 3) :=
    boltzmannEvent r ∩
      {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}
  let C : ℕ → Set (ℕ → ℤ × ℤ) := fun k =>
    {p | τ p = (k : ℕ∞)} ∩ {p | (p k).1 = (ell : ℤ)}
  let D : ℕ → Set (ℕ → Fin 3) := fun k =>
    firstHitCodeSlice r ell k Set.univ
  let H : ∀ k : ℕ, Set (Fin (k + 1) → ℤ × ℤ) :=
    fun k => conditionedFirstHitPrefixSet r k
  have hAuniv : ∀ k : ℕ,
      Set.univ ∩ {p | τ p = (k : ℕ∞)} =
        conditionedVectorPrefix k ⁻¹' H k := by
    intro k
    ext p
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and,
      Set.mem_preimage]
    rw [show H k = conditionedFirstHitPrefixSet r k from rfl,
      ← conditionedVectorFirstHit_preimage]
    simp
  have hbase : conditionedVectorPathLaw 0 0 E =
      (ell + 1 : ℝ≥0∞) * iidCodeMeasure F := by
    simpa [E, F, τ, P, Set.inter_assoc] using
      (conditionedVectorPathLaw_zero_zero_firstHit_bridge
        r ell Set.univ H hAuniv)
  have hnum : conditionedVectorPathLaw 0 0 (A ∩ E) =
      (ell + 1 : ℝ≥0∞) * iidCodeMeasure (P ⁻¹' A ∩ F) := by
    simpa [E, F, τ, P, Set.inter_assoc] using
      (conditionedVectorPathLaw_zero_zero_firstHit_bridge r ell A S hA)
  have hCunion : E = ⋃ k, C k := by
    ext p
    simp only [E, C, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, τ]
    constructor
    · rintro ⟨hfinite, hend⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite.ne
      have hτk : conditionedSecondCoordinateFirstHit r p = (k : ℕ∞) :=
        hk.symm
      have hto :
          (conditionedSecondCoordinateFirstHit r p).toNat = k := by
        simp [hτk]
      refine ⟨k, hτk, ?_⟩
      simpa [hto] using hend
    · rintro ⟨k, hτk, hend⟩
      refine ⟨?_, ?_⟩
      · rw [hτk]
        exact ENat.natCast_lt_top k
      · simpa [hτk] using hend
  have hCmeas : ∀ k, MeasurableSet (C k) := by
    intro k
    exact measurableSet_firstHitPathEndpointSlice r ell k
  have hEmeas : MeasurableSet E := by
    rw [hCunion]
    exact MeasurableSet.iUnion hCmeas
  have hDmeas : ∀ k, MeasurableSet (D k) := by
    intro k
    have hset : D k = {ω | firstHitCodePrefix k ω ∈
        H k ∩ {q | (∀ j, 0 ≤ (q j).1) ∧
          (q (Fin.last k)).1 = (ell : ℤ)}} := by
      change firstHitCodeSlice r ell k Set.univ = _
      exact firstHit_code_slice_eq_prefix r ell k Set.univ (H k)
        (hAuniv k)
    rw [hset]
    exact (Set.to_countable _).measurableSet.preimage
      (firstHitCodePrefix_measurable k)
  have hFunion : F = ⋃ k, D k := by
    ext ω
    simp only [F, D, firstHitCodeSlice, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hevent, hend⟩
      obtain ⟨t, ht, hstay⟩ := hevent
      have hevent' : ω ∈ boltzmannEvent r := ⟨t, ht, hstay⟩
      let k := boltzmannTau r ω
      have hτtmp := conditionedFirstHit_eq_boltzmannTau r ω ⟨t, ht⟩
      have hτk :
          conditionedSecondCoordinateFirstHit r (firstHitCodePath ω) =
            (k : ℕ∞) := by
        change conditionedSecondCoordinateFirstHit r
          (fun n => codeWalk ω n) = (k : ℕ∞)
        exact hτtmp
      refine ⟨k, ⟨⟨⟨Set.mem_univ _, hτk⟩, hevent'⟩, ?_⟩⟩
      simpa [k] using hend
    · rintro ⟨k, ⟨⟨⟨_, hτk⟩, hevent⟩, hend⟩⟩
      obtain ⟨t, ht, hstay⟩ := hevent
      have hevent' : ω ∈ boltzmannEvent r := ⟨t, ht, hstay⟩
      have hτtmp := conditionedFirstHit_eq_boltzmannTau r ω ⟨t, ht⟩
      have hτcode :
          conditionedSecondCoordinateFirstHit r (firstHitCodePath ω) =
            (boltzmannTau r ω : ℕ∞) := by
        change conditionedSecondCoordinateFirstHit r
          (fun n => codeWalk ω n) = (boltzmannTau r ω : ℕ∞)
        exact hτtmp
      have htk : boltzmannTau r ω = k := by
        exact_mod_cast hτcode.symm.trans hτk
      refine ⟨hevent', ?_⟩
      simpa [htk] using hend
  have hFmeas : MeasurableSet F := by
    rw [hFunion]
    exact MeasurableSet.iUnion hDmeas
  have hc0 : (ell + 1 : ℝ≥0∞) ≠ 0 := by positivity
  have hctop : (ell + 1 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hFne : iidCodeMeasure F ≠ 0 := ne_of_gt hpos
  have hFtop : iidCodeMeasure F ≠ ⊤ := measure_ne_top _ _
  have hnum' : conditionedVectorPathLaw 0 0 (E ∩ A) =
      (ell + 1 : ℝ≥0∞) * iidCodeMeasure (P ⁻¹' A ∩ F) := by
    calc
      _ = conditionedVectorPathLaw 0 0 (A ∩ E) := by
        congr 1
        exact Set.inter_comm _ _
      _ = (ell + 1 : ℝ≥0∞) * iidCodeMeasure
          (P ⁻¹' A ∩ F) := hnum
  change (conditionedVectorPathLaw 0 0)[A | E] =
    iidCodeMeasure[P ⁻¹' A | F]
  rw [ProbabilityTheory.cond_apply hEmeas,
    ProbabilityTheory.cond_apply hFmeas]
  rw [hbase, hnum']
  calc
    ((ell + 1 : ℝ≥0∞) * iidCodeMeasure F)⁻¹ *
        ((ell + 1 : ℝ≥0∞) * iidCodeMeasure (P ⁻¹' A ∩ F)) =
      (iidCodeMeasure F)⁻¹ * iidCodeMeasure (F ∩ P ⁻¹' A) := by
        rw [ENNReal.mul_inv (Or.inr hFtop) (Or.inr hFne)]
        rw [show (P ⁻¹' A ∩ F) = (F ∩ P ⁻¹' A) from Set.inter_comm _ _]
        calc
          _ = ((ell + 1 : ℝ≥0∞)⁻¹ * (ell + 1 : ℝ≥0∞)) *
              ((iidCodeMeasure F)⁻¹ *
                iidCodeMeasure (F ∩ P ⁻¹' A)) := by ac_rfl
          _ = _ := by
            rw [ENNReal.inv_mul_cancel hc0 hctop]
            simp

end DirectedDistances.RandomWalk
