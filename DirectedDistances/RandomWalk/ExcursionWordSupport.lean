module

public import DirectedDistances.RandomWalk.ExcursionWords
public import DirectedDistances.RandomWalk.QuadrantSplit

/-! # Support for the stopped excursion word

Helpers toward the corrected Lemma 5.18 target characterization
has exact atoms `3 ^ (-length)`. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- A word of step codes whose first-coordinate partial sums stay above `-1` until the last step, -/
@[expose] def IsStoppedExcursionWord (v : List (Fin 3)) : Prop :=
  1 ≤ v.length ∧ ((v.map lazyTwoDimensionalStep).sum).1 = -1 ∧
    ∀ i < v.length, -1 < (((v.take i).map lazyTwoDimensionalStep).sum).1

private theorem sum_word_eq_codeWalk (ω : ℕ → Fin 3) (t : ℕ) :
    (((List.range t).map (fun i => ω (i + 1))).map lazyTwoDimensionalStep).sum =
      codeWalk ω t := by
  induction t with
  | zero => simp [codeWalk]
  | succ t ih =>
    have h : codeWalk ω (t + 1) = codeWalk ω t + lazyTwoDimensionalStep (ω (t + 1)) := by
      simp [codeWalk, Finset.sum_range_succ]
    rw [h, ← ih]
    simp [List.range_succ]

private theorem take_word (ω : ℕ → Fin 3) (i n : ℕ) :
    ((List.range n).map (fun j => ω (j + 1))).take i =
      (List.range (min i n)).map (fun j => ω (j + 1)) := by
  rw [← List.map_take, List.take_range]

private theorem fst_step_ge (c : Fin 3) : -1 ≤ (lazyTwoDimensionalStep c).1 := by
  simp only [lazyTwoDimensionalStep]
  have : (0 : ℤ) ≤ (c : ℤ) := by positivity
  omega

private theorem hit_spec (ω : ℕ → Fin 3) (n : ℕ) (hn : codeFstFirstHit (-1) ω = n) :
    (codeWalk ω n).1 = -1 ∧ ∀ m < n, (codeWalk ω m).1 ≠ -1 := by
  classical
  unfold codeFstFirstHit at hn
  split at hn
  · rename_i h
    have h' : Nat.find h = n := ENat.natCast_inj.mp hn
    subst h'
    exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩
  · exact absurd hn (ENat.top_ne_natCast n)

private theorem hit_eq (ω : ℕ → Fin 3) (n : ℕ) (h1 : (codeWalk ω n).1 = -1)
    (h2 : ∀ m < n, (codeWalk ω m).1 ≠ -1) : codeFstFirstHit (-1) ω = n := by
  classical
  have h : ∃ m, (codeWalk ω m).1 = -1 := ⟨n, h1⟩
  unfold codeFstFirstHit
  rw [dif_pos h]
  have : Nat.find h = n := (Nat.find_eq_iff h).mpr ⟨h1, fun m hm => h2 m hm⟩
  rw [this]

private theorem walk_gt_before (ω : ℕ → Fin 3) (n : ℕ)
    (h2 : ∀ m < n, (codeWalk ω m).1 ≠ -1) : ∀ t < n, -1 < (codeWalk ω t).1 := by
  intro t
  induction t with
  | zero => intro _; simp [codeWalk_zero]
  | succ t ih =>
    intro ht
    have h0 := ih (by omega)
    have hs := fst_step_ge (ω (t + 1))
    have hsucc : codeWalk ω (t + 1) = codeWalk ω t + lazyTwoDimensionalStep (ω (t + 1)) := by
      simp [codeWalk, Finset.sum_range_succ]
    have hne := h2 (t + 1) ht
    rw [hsucc] at hne ⊢
    simp only [Prod.fst_add] at hne ⊢
    omega

/-- A finite hit time yields a stopped excursion word. -/
theorem isStoppedExcursionWord_excursionWord (ω : ℕ → Fin 3)
    (hω : codeFstFirstHit (-1) ω ≠ ⊤) : IsStoppedExcursionWord (excursionWord ω) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hω
  have hn' : codeFstFirstHit (-1) ω = n := hn.symm
  obtain ⟨hs1, hs2⟩ := hit_spec ω n hn'
  have hlen : excursionLength ω = n := by simp [excursionLength, hn']
  have hword : excursionWord ω = (List.range n).map (fun i => ω (i + 1)) := by
    rw [excursionWord, hlen]
  rw [hword]
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_range]
    by_contra hcon
    have h0 : n = 0 := by omega
    subst h0
    simp [codeWalk_zero] at hs1
  · rw [sum_word_eq_codeWalk]; exact hs1
  · intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [take_word, sum_word_eq_codeWalk, min_eq_left hi.le]
    exact walk_gt_before ω n hs2 i hi

/-- The first hit of `L = -1` is almost surely finite. -/
theorem ae_codeFstFirstHit_ne_top :
    ∀ᵐ ω ∂iidCodeMeasure, codeFstFirstHit (-1) ω ≠ ⊤ := by
  filter_upwards [ae_codeFstFirstHit_lt_top (a := -1) (by norm_num)] with ω h
  exact h.ne

/-- The excursion word law is supported on stopped excursion words. -/
theorem ae_isStoppedExcursionWord_excursionWordLaw :
    ∀ᵐ v ∂excursionWordLaw, IsStoppedExcursionWord v := by
  unfold excursionWordLaw
  rw [ae_map_iff measurable_excursionWord.aemeasurable (MeasurableSet.of_discrete)]
  filter_upwards [ae_codeFstFirstHit_ne_top] with ω h
  exact isStoppedExcursionWord_excursionWord ω h

/-- Prefix uniqueness: a code sequence reading a stopped excursion word gives that excursion word. -/
theorem excursionWord_eq_of_prefix (v : List (Fin 3)) (hv : IsStoppedExcursionWord v)
    (ω : ℕ → Fin 3) (hω : ∀ i (h : i < v.length), ω (i + 1) = v[i]) :
    excursionWord ω = v := by
  obtain ⟨hv1, hv2, hv3⟩ := hv
  set n := v.length with hnv
  have hw : (List.range n).map (fun i => ω (i + 1)) = v := by
    apply List.ext_getElem
    · simp [hnv]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact hω i h2
  have hwalk : ∀ t ≤ n, codeWalk ω t = ((v.take t).map lazyTwoDimensionalStep).sum := by
    intro t ht
    rw [← hw, take_word, min_eq_left ht, sum_word_eq_codeWalk]
  have h1 : (codeWalk ω n).1 = -1 := by
    rw [hwalk n le_rfl, hnv, List.take_length]; exact hv2
  have h2 : ∀ m < n, (codeWalk ω m).1 ≠ -1 := by
    intro m hm
    rw [hwalk m hm.le]
    exact (hv3 m hm).ne'
  have hhit := hit_eq ω n h1 h2
  have hlen : excursionLength ω = n := by simp [excursionLength, hhit]
  rw [excursionWord, hlen]
  exact hw

private theorem excursionWord_getElem (ω : ℕ → Fin 3) (j : ℕ)
    (hj : j < (excursionWord ω).length) : (excursionWord ω)[j] = ω (j + 1) := by
  simp [excursionWord]

/-- Exact atoms of the stopped excursion-word law. -/
theorem excursionWordLaw_singleton (v : List (Fin 3)) (hv : IsStoppedExcursionWord v) :
    excursionWordLaw {v} = (1 / 3 : ENNReal) ^ v.length := by
  unfold excursionWordLaw
  rw [Measure.map_apply measurable_excursionWord (measurableSet_singleton v)]
  have hpre : excursionWord ⁻¹' {v} =
      {ω | quadrantCodeTailPrefix v.length ω = fun j : Fin v.length => v[j]} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      funext j
      subst h
      exact (excursionWord_getElem ω j.val j.isLt).symm
    · intro h
      refine excursionWord_eq_of_prefix v hv ω fun i hi => ?_
      exact congrFun h ⟨i, hi⟩
  rw [hpre]
  exact iidCodeMeasure_tailPrefix_mass _ _

end DirectedDistances.RandomWalk
