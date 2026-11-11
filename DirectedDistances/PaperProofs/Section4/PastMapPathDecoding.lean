module

public import DirectedDistances.KMSW.KMSWMapLawFromWalk
public import DirectedDistances.RandomWalk.ConditionedStrongMarkov
import DirectedDistances.RandomWalk.ConditionedVectorPrefixSupport
import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefixRange

/-! paths to KMSW codes for the stopped past map at the first hit of R = −r; the -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open MeasureTheory
open scoped BigOperators

/-- is not used; not the paper result. -/
@[expose] def pathCode (p : ℕ → ℤ × ℤ) (i : ℕ) : Fin 3 :=
  if i = 0 then 0 else
    if (p i - p (i - 1)).1 = -1 then 0 else
      if (p i - p (i - 1)).1 = 0 then 1 else 2

 
@[simp] theorem pathCode_zero (p : ℕ → ℤ × ℤ) : pathCode p 0 = 0 := by
  simp only [pathCode, ↓reduceIte]

 
theorem measurable_pathCode : Measurable pathCode := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [pathCode_zero] using (measurable_const : Measurable
      (fun _ : ℕ → ℤ × ℤ => (0 : Fin 3)))
  · let d : ℤ × ℤ → Fin 3 := fun z => if z.1 = -1 then 0 else if z.1 = 0 then 1 else 2
    have hm : Measurable (fun p : ℕ → ℤ × ℤ => p i - p (i - 1)) :=
      (measurable_pi_apply i).sub (measurable_pi_apply (i - 1))
    simpa only [pathCode, ite_eq_right hi, Function.comp_def, d] using
      (measurable_of_countable d).comp hm

private theorem decode_step (c : Fin 3) :
    (if (lazyTwoDimensionalStep c).1 = -1 then (0 : Fin 3)
      else if (lazyTwoDimensionalStep c).1 = 0 then 1 else 2) = c := by
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

/-- positive code coordinates; the coordinate at zero is deliberately excluded. -/
theorem pathCode_codeWalk (ω : ℕ → Fin 3) (i : ℕ) (hi : 1 ≤ i) :
    pathCode (fun n => codeWalk ω n) i = ω i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [pathCode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, codeWalk_succ_sub]
  exact decode_step _

/-- are recovered exactly, including their second coordinate. -/
theorem step_pathCode (p : ℕ → ℤ × ℤ) (n : ℕ)
    (hn : p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) :
    lazyTwoDimensionalStep (pathCode p (n + 1)) = p (n + 1) - p n := by
  obtain ⟨c, hc⟩ := hn
  simp only [pathCode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, ← hc, decode_step]

/-- legal decoded paths recovers the path relative to its initial value. -/
theorem codeWalk_pathCode (p : ℕ → ℤ × ℤ)
    (hp : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) (n : ℕ) :
    codeWalk (pathCode p) n = p n - p 0 := by
  induction n with
  | zero => simp only [codeWalk_zero, sub_self]; rfl
  | succ n ih =>
    have h := codeWalk_succ_sub (pathCode p) n
    rw [step_pathCode p n (hp n), ih] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (by abel)

/-- walk ignores its dummy coordinate. -/
theorem codeWalk_congr_positive (ω ω' : ℕ → Fin 3)
    (h : ∀ i, 1 ≤ i → ω i = ω' i) (n : ℕ) : codeWalk ω n = codeWalk ω' n := by
  unfold codeWalk
  apply Finset.sum_congr rfl
  intro i _
  rw [h (i + 1) (by omega)]

/-- event ignores its dummy coordinate. -/
theorem boltzmannEvent_congr_positive (r : ℕ) (ω ω' : ℕ → Fin 3)
    (h : ∀ i, 1 ≤ i → ω i = ω' i) :
    ω ∈ boltzmannEvent r ↔ ω' ∈ boltzmannEvent r := by
  simp only [boltzmannEvent, Set.mem_ofPred_eq, codeWalk_congr_positive ω ω' h]

/-- ignores its dummy coordinate. -/
theorem boltzmannTau_congr_positive (r : ℕ) (ω ω' : ℕ → Fin 3)
    (h : ∀ i, 1 ≤ i → ω i = ω' i) : boltzmannTau r ω = boltzmannTau r ω' := by
  classical
  have he : codeWalk ω = codeWalk ω' := funext (codeWalk_congr_positive ω ω' h)
  let t : (ℕ → ℤ × ℤ) → ℕ := fun p =>
    if hh : ∃ n, (p n).2 = -(r : ℤ) then Nat.find hh else 0
  exact congrArg t he

/-- index ignores its dummy coordinate. -/
theorem stoppedIndex_congr_positive (r : ℕ) (hr : 1 ≤ r) (ω ω' : ℕ → Fin 3)
    (h : ∀ i, 1 ≤ i → ω i = ω' i) : stoppedIndex r hr ω = stoppedIndex r hr ω' := by
  classical
  have hc (i : StoppedWalkIndex r) :
      ω ∈ stoppedWalkIndexSet i ↔ ω' ∈ stoppedWalkIndexSet i := by
    by_cases hn : 1 ≤ i.1
    · simp only [stoppedWalkIndexSet, hn, ↓reduceIte, stoppedCylinder,
        Set.mem_ofPred_eq]
      apply and_congr
      · apply forall_congr'
        intro j
        rw [h (j.val + 1) (by omega)]
      · rw [h i.1 hn]
    · simp only [stoppedWalkIndexSet, hn, ↓reduceIte, Set.mem_empty_iff_false]
  cases hx : stoppedIndex r hr ω with
  | none =>
    cases hy : stoppedIndex r hr ω' with
    | none => rfl
    | some j =>
      have hj : ω' ∈ stoppedWalkIndexSet j := by
        rw [← stoppedIndex_preimage_singleton r hr j]
        exact hy
      have hj' := (hc j).mpr hj
      rw [← stoppedIndex_preimage_singleton r hr j] at hj'
      change stoppedIndex r hr ω = some j at hj'
      rw [hx] at hj'
      contradiction
  | some i =>
    have hi : ω ∈ stoppedWalkIndexSet i := by
      rw [← stoppedIndex_preimage_singleton r hr i]
      exact hx
    have hi' := (hc i).mp hi
    rw [← stoppedIndex_preimage_singleton r hr i] at hi'
    exact hi'.symm

/-- map ignores its dummy coordinate. -/
theorem stoppedMap_congr_positive (r : ℕ) (hr : 1 ≤ r) (ω ω' : ℕ → Fin 3)
    (h : ∀ i, 1 ≤ i → ω i = ω' i) : stoppedMap r hr ω = stoppedMap r hr ω' := by
  unfold stoppedMap
  rw [stoppedIndex_congr_positive r hr ω ω' h]

/-- reintegration leave the stopped map unchanged. -/
theorem stoppedMap_pathCode_codeWalk (r : ℕ) (hr : 1 ≤ r) (ω : ℕ → Fin 3) :
    stoppedMap r hr (pathCode (fun n => codeWalk ω n)) = stoppedMap r hr ω := by
  exact stoppedMap_congr_positive r hr _ ω (pathCode_codeWalk ω)

/-- the conditioned path starts at zero and has only the three literal source increments. -/
theorem conditionedVectorPathLaw_ae_legal :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      p 0 = (0, 0) ∧ ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep := by
  have h := conditionedSource_ae_all_prefixes_mem_range 0 0
    (conditionedVectorPathLaw 0 0) (conditionedVectorPathLaw_map_prefix 0 0)
  filter_upwards [h] with p hp
  constructor
  · exact ((mem_range_lazyTwoDimensionalPrefix_iff 0 0 _).mp (hp 0)).1
  · intro n
    have hs := ((mem_range_lazyTwoDimensionalPrefix_iff 0 0 _).mp (hp (n + 1))).2
    obtain ⟨c, hc⟩ := hs ⟨n, by omega⟩
    refine ⟨c, ?_⟩
    change p (n + 1) = p n + lazyTwoDimensionalStep c at hc
    rw [hc]
    abel

private theorem codeWalk_congr_prefix (ω ω' : ℕ → Fin 3) (k : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ k → ω i = ω' i) (n : ℕ) (hn : n ≤ k) :
    codeWalk ω n = codeWalk ω' n := by
  unfold codeWalk
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  rw [h (j + 1) (by omega) (by omega)]

private theorem stoppedMap_congr_firstHit_prefix (r : ℕ) (hr : 1 ≤ r)
    (ω ω' : ℕ → Fin 3) (k : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ k → ω i = ω' i)
    (hk : (codeWalk ω k).2 = -(r : ℤ) ∧
      ∀ j < k, (codeWalk ω j).2 ≠ -(r : ℤ)) :
    stoppedMap r hr ω = stoppedMap r hr ω' := by
  classical
  have hw := codeWalk_congr_prefix ω ω' k h
  have hk' : (codeWalk ω' k).2 = -(r : ℤ) ∧
      ∀ j < k, (codeWalk ω' j).2 ≠ -(r : ℤ) := by
    constructor
    · rw [← hw k le_rfl]; exact hk.1
    · intro j hj
      rw [← hw j (by omega)]
      exact hk.2 j hj
  have ht (w : ℕ → Fin 3)
      (hf : (codeWalk w k).2 = -(r : ℤ) ∧
        ∀ j < k, (codeWalk w j).2 ≠ -(r : ℤ)) : boltzmannTau r w = k := by
    have hex : ∃ j, (codeWalk w j).2 = -(r : ℤ) := ⟨k, hf.1⟩
    simpa only [boltzmannTau, dite_eq_left hex] using ((Nat.find_eq_iff hex).mpr hf)
  have htau := ht ω hk
  have hevent (w : ℕ → Fin 3)
      (hf : (codeWalk w k).2 = -(r : ℤ) ∧
        ∀ j < k, (codeWalk w j).2 ≠ -(r : ℤ)) :
      w ∈ boltzmannEvent r ↔ ∀ j ≤ k, 0 ≤ (codeWalk w j).1 := by
    constructor
    · rintro ⟨t, hhit, hnonneg⟩ j hj
      have hkt : k ≤ t := by
        by_contra hnot
        exact hf.2 t (by omega) hhit
      exact hnonneg j (by omega)
    · intro hnonneg
      exact ⟨k, hf.1, hnonneg⟩
  have hE : ω ∈ boltzmannEvent r ↔ ω' ∈ boltzmannEvent r := by
    rw [hevent ω hk, hevent ω' hk']
    exact forall_congr' fun j => forall_congr' fun hj => by rw [hw j hj]
  unfold stoppedMap
  congr 1
  by_cases hmem : ω ∈ boltzmannEvent r
  · cases hx : stoppedIndex r hr ω with
    | none => simp [stoppedIndex, hmem] at hx
    | some i =>
      have hi : ω ∈ stoppedWalkIndexSet i := by
        rw [← stoppedIndex_preimage_singleton r hr i]
        exact hx
      have hpos : 1 ≤ i.1 := by
        by_contra hn
        simp only [stoppedWalkIndexSet, ite_eq_right hn, Set.mem_empty_iff_false] at hi
      have hicyl : ω ∈ stoppedCylinder i.2.2 := by
        simpa only [stoppedWalkIndexSet, ite_eq_left hpos] using hi
      have htime : i.1 = k :=
        (stoppedCylinder_subset_eventSlice hpos i.2.2 hicyl).2.symm.trans htau
      have hi' : ω' ∈ stoppedWalkIndexSet i := by
        simp only [stoppedWalkIndexSet, hpos, ↓reduceIte, stoppedCylinder,
          Set.mem_ofPred_eq] at hi ⊢
        constructor
        · intro j
          rw [← h (j.val + 1) (by omega) (by have := j.isLt; omega)]
          exact hi.1 j
        · rw [← h i.1 hpos (by omega)]
          exact hi.2
      rw [← stoppedIndex_preimage_singleton r hr i] at hi'
      exact hi'.symm
  · have hmem' : ω' ∉ boltzmannEvent r := fun he => hmem (hE.mpr he)
    simp only [stoppedIndex, dite_eq_right hmem, dite_eq_right hmem']

private theorem codeWalk_pathCode_prefix (p : ℕ → ℤ × ℤ) (k : ℕ)
    (hp : ∀ n < k, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (n : ℕ) (hn : n ≤ k) : codeWalk (pathCode p) n = p n - p 0 := by
  induction n with
  | zero => simp only [codeWalk_zero, sub_self]; rfl
  | succ n ih =>
    have h := codeWalk_succ_sub (pathCode p) n
    rw [step_pathCode p n (hp n (by omega)), ih (by omega)] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (by abel)

private theorem firstHit_eq_iff (r k : ℕ) (p : ℕ → ℤ × ℤ) :
    conditionedSecondCoordinateFirstHit r p = (k : ℕ∞) ↔
      (p k).2 = -(r : ℤ) ∧ ∀ j < k, (p j).2 ≠ -(r : ℤ) := by
  classical
  unfold conditionedSecondCoordinateFirstHit
  by_cases h : ∃ n, (p n).2 = -(r : ℤ)
  · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dite_eq_right h]
    constructor
    · intro he
      exact (ENat.top_ne_natCast k he).elim
    · rintro ⟨hk, _⟩
      exact (h ⟨k, hk⟩).elim

/-- slices are past-measurable on paths starting at zero with legal increments through
the first hit. This is exactly the stopped-past hypothesis for the event displayed
in the first set-builder. The restriction has full conditioned-path probability.
not the paper result. -/
theorem measurableSet_stoppedMap_pathCode_firstHit_legal
    (r : ℕ) (hr : 1 ≤ r) (T : Set (Option (AllBoltzmannSpace r))) (k ell : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      ({p | stoppedMap r hr (pathCode p) ∈ T ∧ p 0 = (0, 0) ∧
          ∀ n < (conditionedSecondCoordinateFirstHit r p).toNat,
            p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep} ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  let S : Set (ℕ → ℤ × ℤ) :=
    {p | stoppedMap r hr (pathCode p) ∈ T ∧ p 0 = (0, 0) ∧
        ∀ n < (conditionedSecondCoordinateFirstHit r p).toNat,
          p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep} ∩
      {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
      {p | (p k).1 = (ell : ℤ)}
  refine ⟨conditionedVectorPrefix k '' S, (Set.to_countable _).measurableSet, ?_⟩
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    have hpref (j : ℕ) (hj : j ≤ k) : q j = p j :=
      congrFun hqp ⟨j, by omega⟩
    rcases hq with ⟨⟨⟨hmap, hq0, hlegal⟩, hτq⟩, hend⟩
    change conditionedSecondCoordinateFirstHit r q = (k : ℕ∞) at hτq
    change (q k).1 = (ell : ℤ) at hend
    have hfirst := (firstHit_eq_iff r k q).mp hτq
    have hτp : conditionedSecondCoordinateFirstHit r p = (k : ℕ∞) := by
      apply (firstHit_eq_iff r k p).mpr
      constructor
      · rw [← hpref k le_rfl]; exact hfirst.1
      · intro j hj
        rw [← hpref j (by omega)]
        exact hfirst.2 j hj
    have hlegalq : ∀ n < k, q (n + 1) - q n ∈ Set.range lazyTwoDimensionalStep := by
      simpa only [hτq, ENat.toNat_natCast] using hlegal
    have hw (n : ℕ) (hn : n ≤ k) : codeWalk (pathCode q) n = q n := by
      rw [codeWalk_pathCode_prefix q k hlegalq n hn, hq0]
      exact sub_zero _
    have hcodes (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
        pathCode q i = pathCode p i := by
      simp only [pathCode, hpref i hik, hpref (i - 1) (by omega)]
    have hfirstcode : (codeWalk (pathCode q) k).2 = -(r : ℤ) ∧
        ∀ j < k, (codeWalk (pathCode q) j).2 ≠ -(r : ℤ) := by
      constructor
      · rw [hw k le_rfl]; exact hfirst.1
      · intro j hj
        rw [hw j (by omega)]
        exact hfirst.2 j hj
    have hmaps := stoppedMap_congr_firstHit_prefix r hr (pathCode q) (pathCode p)
      k hcodes hfirstcode
    refine ⟨⟨⟨?_, ?_, ?_⟩, hτp⟩, ?_⟩
    · rw [← hmaps]; exact hmap
    · rw [← hpref 0 (by omega)]; exact hq0
    · rw [hτp, ENat.toNat_natCast]
      intro n hn
      rw [← hpref (n + 1) (by omega), ← hpref n (by omega)]
      exact hlegalq n hn
    · change (p k).1 = (ell : ℤ)
      rw [← hpref k le_rfl]; exact hend
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- restriction used for stopped-past measurability does not change the event almost surely.
not the paper result. -/
theorem stoppedMap_pathCode_legal_event_ae_eq
    (r : ℕ) (hr : 1 ≤ r) (T : Set (Option (AllBoltzmannSpace r))) :
    {p | stoppedMap r hr (pathCode p) ∈ T ∧ p 0 = (0, 0) ∧
        ∀ n < (conditionedSecondCoordinateFirstHit r p).toNat,
          p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep}
      =ᵐ[conditionedVectorPathLaw 0 0] {p | stoppedMap r hr (pathCode p) ∈ T} := by
  filter_upwards [conditionedVectorPathLaw_ae_legal] with p hp
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, hp.1, fun n _ => hp.2 n⟩⟩

end DirectedDistances.PaperProofs.Section4
