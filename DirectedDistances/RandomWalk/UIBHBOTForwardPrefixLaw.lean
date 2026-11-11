module

public import DirectedDistances.RandomWalk.UIBHBOTForwardUnbounded
public import DirectedDistances.RandomWalk.UIBHBOTEncodingWalk
public import DirectedDistances.RandomWalk.ExcursionWordSupport
import Mathlib.Probability.Independence.InfinitePi







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private theorem prefixLaw_word_sum (ω : ℕ → Fin 3) (n : ℕ) :
    ((((List.range n).map fun i => ω (i + 1)).map lazyTwoDimensionalStep).sum) =
      codeWalk ω n := by
  induction n with
  | zero => simp [codeWalk]
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton]
      rw [ih]
      simp [codeWalk, Finset.sum_range_succ]

private theorem prefixLaw_take_word (ω : ℕ → Fin 3) (p : List (Fin 3))
    (hp : ∀ i (hi : i < p.length), ω (i + 1) = p[i]) (n : ℕ) (hn : n ≤ p.length) :
    (List.range n).map (fun i => ω (i + 1)) = p.take n := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left hn]
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    exact hp i (by omega)

private theorem prefixLaw_hit_at_length (ω : ℕ → Fin 3)
    (hω : codeFstFirstHit (-1) ω ≠ ⊤) :
    (codeWalk ω (excursionLength ω)).1 = -1 := by
  classical
  unfold codeFstFirstHit at hω
  split at hω
  · rename_i h
    have hlen : excursionLength ω = Nat.find h := by
      simp [excursionLength, codeFstFirstHit, h]
    rw [hlen]
    exact Nat.find_spec h
  · exact (hω rfl).elim

private theorem prefixLaw_prefix_iff (p : List (Fin 3))
    (hp : ∀ i ≤ p.length, 0 ≤ (((p.take i).map lazyTwoDimensionalStep).sum).1)
    (ω : ℕ → Fin 3) (hω : codeFstFirstHit (-1) ω ≠ ⊤) :
    p <+: excursionWord ω ↔
      quadrantCodeTailPrefix p.length ω = fun j : Fin p.length => p[j] := by
  constructor
  · intro h
    funext j
    have hj := h.getElem j.isLt
    simpa [quadrantCodeTailPrefix, excursionWord] using hj.symm
  · intro h
    have hletters (i : ℕ) (hi : i < p.length) : ω (i + 1) = p[i] :=
      congrFun h ⟨i, hi⟩
    have hlen : p.length ≤ excursionLength ω := by
      by_contra hn
      have hn' : excursionLength ω ≤ p.length := by omega
      have hw := prefixLaw_take_word ω p hletters (excursionLength ω) hn'
      have hs := prefixLaw_word_sum ω (excursionLength ω)
      rw [hw] at hs
      have hnonneg := hp (excursionLength ω) hn'
      rw [hs, prefixLaw_hit_at_length ω hω] at hnonneg
      omega
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simpa [excursionWord] using hlen, ?_⟩
    intro i hi
    simpa [excursionWord] using (hletters i hi).symm




theorem excursionWordLaw_prefix (p : List (Fin 3))
    (hp : ∀ i ≤ p.length, 0 ≤ (((p.take i).map lazyTwoDimensionalStep).sum).1) :
    excursionWordLaw {v | p <+: v} = (1 / 3 : ENNReal) ^ p.length := by
  rw [excursionWordLaw, Measure.map_apply measurable_excursionWord
    (MeasurableSet.of_discrete)]
  have heq : excursionWord ⁻¹' {v | p <+: v} =ᵐ[iidCodeMeasure]
      {ω | quadrantCodeTailPrefix p.length ω = fun j : Fin p.length => p[j]} := by
    filter_upwards [ae_codeFstFirstHit_ne_top] with ω hω
    exact propext (prefixLaw_prefix_iff p hp ω hω)
  rw [measure_congr heq]
  exact iidCodeMeasure_tailPrefix_mass _ _

private theorem prefixLaw_iterated_shift (k : ℕ) (ω : ℕ → Fin 3) :
    iteratedExcursionCode k (codeShift (excursionLength ω) ω) =
      iteratedExcursionCode (k + 1) ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change codeShift _ (iteratedExcursionCode k (codeShift (excursionLength ω) ω)) = _
      rw [ih]
      rfl

private theorem prefixLaw_iterated_word_shift (k : ℕ) (ω : ℕ → Fin 3) :
    iteratedExcursionWord (k + 1) ω =
      iteratedExcursionWord k (codeShift (excursionLength ω) ω) :=
  congrArg excursionWord (prefixLaw_iterated_shift k ω).symm

private theorem prefixLaw_concat_prefix (N n : ℕ) (ω : ℕ → Fin 3) (hn : n ≤ N)
    (hpos : ∀ k < N, 1 ≤ (iteratedExcursionWord k ω).length) :
    ((List.range N).flatMap (fun k => iteratedExcursionWord k ω)).take n =
      (List.range n).map (fun i => ω (i + 1)) := by
  induction N generalizing n ω with
  | zero =>
      have : n = 0 := by omega
      subst n
      simp
  | succ N ih =>
      have htail : (List.range N).flatMap (fun k => iteratedExcursionWord (k + 1) ω) =
          (List.range N).flatMap (fun k =>
            iteratedExcursionWord k (codeShift (excursionLength ω) ω)) := by
        congr 1
        funext k
        exact prefixLaw_iterated_word_shift k ω
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      change (excursionWord ω ++
        (List.range N).flatMap (fun k => iteratedExcursionWord (k + 1) ω)).take n = _
      rw [htail]
      by_cases hnm : n ≤ excursionLength ω
      · rw [List.take_append_of_le_length (by simpa [excursionWord] using hnm)]
        simp [excursionWord, ← List.map_take, List.take_range, Nat.min_eq_left hnm]
      · have hm : excursionLength ω ≤ n := by omega
        have hmpos : 1 ≤ excursionLength ω := by
          simpa [iteratedExcursionWord, iteratedExcursionCode, excursionWord] using
            hpos 0 (by omega)
        have hrem : n - excursionLength ω ≤ N := by omega
        have hpos' : ∀ k < N,
            1 ≤ (iteratedExcursionWord k (codeShift (excursionLength ω) ω)).length := by
          intro k hk
          rw [← prefixLaw_iterated_word_shift]
          exact hpos (k + 1) (by omega)
        rw [List.take_append, List.take_of_length_le (by simpa [excursionWord] using hm)]
        simp only [excursionWord, List.length_map, List.length_range]
        rw [ih _ _ hrem hpos']
        conv_rhs => rw [show n = excursionLength ω + (n - excursionLength ω) by omega]
        rw [List.range_add, List.map_append, List.map_map]
        congr 1

private theorem prefixLaw_measurable_blocks (N : ℕ) :
    Measurable (fun w : ℕ → List (Fin 3) => (List.range N).flatMap w) := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact (measurable_of_countable (fun q : List (Fin 3) × List (Fin 3) =>
        q.1 ++ q.2)).comp (ih.prodMk (measurable_pi_apply N))

private theorem prefixLaw_measurable_letters (n : ℕ) :
    Measurable (fun w : ℕ → List (Fin 3) => ((List.range n).flatMap w).take n) :=
  (measurable_of_countable (fun v : List (Fin 3) => v.take n)).comp
    (prefixLaw_measurable_blocks n)

private theorem prefixLaw_map_iterated_words :
    iidCodeMeasure.map (fun ω k => iteratedExcursionWord k ω) =
      Measure.infinitePi (fun _ : ℕ => excursionWordLaw) := by
  have hm : Measurable (fun ω k => iteratedExcursionWord k ω) :=
    measurable_pi_iff.mpr measurable_iteratedExcursionWord
  apply IsProjectiveLimit.unique (P := fun s : Finset ℕ =>
    Measure.pi (fun _ : s => excursionWordLaw)) ?_
    (Measure.isProjectiveLimit_infinitePi _)
  intro s
  let N := s.sup id + 1
  let e : s → Fin N := fun i => ⟨i.val, by
    have hi := Finset.le_sup (f := id) i.property
    change i.val ≤ s.sup id at hi
    dsimp [N]
    omega⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Subtype.ext (congrArg Fin.val hij)
  calc
    (iidCodeMeasure.map (fun ω k => iteratedExcursionWord k ω)).map s.restrict =
        (iidCodeMeasure.map (fun ω (i : Fin N) => iteratedExcursionWord i.val ω)).map
          (fun q (i : s) => q (e i)) := by
      rw [Measure.map_map (by fun_prop) hm]
      rw [Measure.map_map (by fun_prop) (show Measurable
        (fun ω (i : Fin N) => iteratedExcursionWord i.val ω) from
          measurable_pi_iff.mpr fun i => measurable_iteratedExcursionWord i.val)]
      rfl
    _ = (Measure.pi (fun _ : Fin N => excursionWordLaw)).map
        (fun q (i : s) => q (e i)) := by rw [map_iteratedExcursionWords N]
    _ = Measure.pi (fun _ : s => excursionWordLaw) := by
      rw [← Measure.infinitePi_eq_pi, Measure.map_infinitePi_infinitePi_of_inj he,
        Measure.infinitePi_eq_pi]

private theorem prefixLaw_map_forward_words :
    uibhbotWordFamilyLaw.map (fun w (k : ℕ) => w (k : ℤ)) =
      iidCodeMeasure.map (fun ω k => iteratedExcursionWord k ω) := by
  rw [prefixLaw_map_iterated_words, uibhbotWordFamilyLaw,
    Measure.map_infinitePi_infinitePi_of_inj (show Function.Injective
      (fun k : ℕ => (k : ℤ)) from Int.ofNat_injective)]

private theorem prefixLaw_ae_iterated_positive :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ k : ℕ, 1 ≤ (iteratedExcursionWord k ω).length := by
  rw [ae_all_iff]
  intro k
  have h : ∀ᵐ v ∂iidCodeMeasure.map (iteratedExcursionWord k), 1 ≤ v.length := by
    rw [map_iteratedExcursionWord k]
    exact ae_one_le_excursionWord_length
  exact (ae_map_iff (measurable_iteratedExcursionWord k).aemeasurable
    (MeasurableSet.of_discrete)).mp h

private theorem prefixLaw_map_letters (n : ℕ) :
    uibhbotWordFamilyLaw.map
        (fun w => ((List.range n).flatMap (fun k : ℕ => w (k : ℤ))).take n) =
      iidCodeMeasure.map (fun ω => (List.range n).map (fun i => ω (i + 1))) := by
  have hm := prefixLaw_measurable_letters n
  calc
    _ = (uibhbotWordFamilyLaw.map (fun w (k : ℕ) => w (k : ℤ))).map
        (fun w => ((List.range n).flatMap w).take n) := by
      rw [Measure.map_map hm (by fun_prop)]
      rfl
    _ = (iidCodeMeasure.map (fun ω k => iteratedExcursionWord k ω)).map
        (fun w => ((List.range n).flatMap w).take n) := by
      rw [prefixLaw_map_forward_words]
    _ = _ := by
      rw [Measure.map_map hm
        (measurable_pi_iff.mpr measurable_iteratedExcursionWord)]
      apply Measure.map_congr
      filter_upwards [prefixLaw_ae_iterated_positive] with ω hω
      exact prefixLaw_concat_prefix n n ω le_rfl (fun k _ => hω k)

private theorem prefixLaw_raw_eq_ofFn (n : ℕ) (ω : ℕ → Fin 3) :
    (List.range n).map (fun i => ω (i + 1)) = List.ofFn (fun i : Fin n => ω (i.val + 1)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

private theorem prefixLaw_measurable_raw (n : ℕ) :
    Measurable (fun ω : ℕ → Fin 3 => (List.range n).map (fun i => ω (i + 1))) := by
  simp_rw [prefixLaw_raw_eq_ofFn]
  exact (measurable_of_countable (fun q : Fin n → Fin 3 => List.ofFn q)).comp
    (measurable_pi_iff.mpr fun i => measurable_pi_apply (i.val + 1))




theorem uibhbotWordFamilyLaw_forward_prefix (n : ℕ) (a : Fin n → Fin 3) :
    uibhbotWordFamilyLaw
        {w | ((List.range n).flatMap (fun k : ℕ => w (k : ℤ))).take n = List.ofFn a} =
      (1 / 3 : ENNReal) ^ n := by
  have hm : Measurable (fun w : ℤ → List (Fin 3) =>
      ((List.range n).flatMap (fun k : ℕ => w (k : ℤ))).take n) :=
    (prefixLaw_measurable_letters n).comp (show Measurable
      (fun w : ℤ → List (Fin 3) => fun k : ℕ => w (k : ℤ)) from by fun_prop)
  change uibhbotWordFamilyLaw ((fun w : ℤ → List (Fin 3) =>
    ((List.range n).flatMap (fun k : ℕ => w (k : ℤ))).take n) ⁻¹' {List.ofFn a}) = _
  rw [← Measure.map_apply hm (measurableSet_singleton (List.ofFn a)),
    prefixLaw_map_letters]
  rw [Measure.map_apply (prefixLaw_measurable_raw n)
    (measurableSet_singleton (List.ofFn a))]
  have heq : (fun ω => (List.range n).map (fun i => ω (i + 1))) ⁻¹' {List.ofFn a} =
      {ω | quadrantCodeTailPrefix n ω = a} := by
    ext ω
    change ((List.range n).map (fun i => ω (i + 1)) = List.ofFn a) ↔
      quadrantCodeTailPrefix n ω = a
    rw [prefixLaw_raw_eq_ofFn]
    exact List.ofFn_inj
  rw [heq]
  exact iidCodeMeasure_tailPrefix_mass n a

private theorem prefixLaw_measurable_forward :
    Measurable (fun w : ℤ → List (Fin 3) => fun n : ℕ => uibhbotConcatWalk w n) := by
  apply Measurable.of_eval
  intro n
  have hm := (prefixLaw_measurable_letters n).comp (show Measurable
    (fun w : ℤ → List (Fin 3) => fun k : ℕ => w (k : ℤ)) from by fun_prop)
  have hsum := (measurable_of_countable (fun v : List (Fin 3) =>
    (v.map lazyTwoDimensionalStep).sum)).comp hm
  simpa [Function.comp_def, uibhbotConcatWalk, List.flatMap_assoc] using hsum




theorem uibhbotWordFamilyLaw_map_forward_path :
    uibhbotWordFamilyLaw.map (fun w => fun n : ℕ => uibhbotConcatWalk w n) =
      iidCodeMeasure.map (fun ω => fun n : ℕ => codeWalk ω n) := by
  let F : (ℕ → List (Fin 3)) → ℕ → ℤ × ℤ := fun w n =>
    ((((List.range n).flatMap w).take n).map lazyTwoDimensionalStep).sum
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable (fun v : List (Fin 3) =>
      (v.map lazyTwoDimensionalStep).sum)).comp (prefixLaw_measurable_letters n)
  calc
    _ = (uibhbotWordFamilyLaw.map (fun w (k : ℕ) => w (k : ℤ))).map F := by
      rw [Measure.map_map hF (by fun_prop)]
      congr 1
      funext w n
      simp [uibhbotConcatWalk, F, List.flatMap_assoc]
    _ = (iidCodeMeasure.map (fun ω k => iteratedExcursionWord k ω)).map F := by
      rw [prefixLaw_map_forward_words]
    _ = _ := by
      rw [Measure.map_map hF
        (measurable_pi_iff.mpr measurable_iteratedExcursionWord)]
      apply Measure.map_congr
      filter_upwards [prefixLaw_ae_iterated_positive] with ω hω
      funext n
      dsimp [F]
      rw [prefixLaw_concat_prefix n n ω le_rfl (fun k _ => hω k)]
      exact prefixLaw_word_sum ω n




theorem ae_uibhbotConcatWalk_snd_unbounded_below :
    ∀ᵐ w ∂uibhbotWordFamilyLaw, ∀ a : ℤ, ∃ n : ℕ,
      (uibhbotConcatWalk w n).2 ≤ a := by
  have hS : MeasurableSet {p : ℕ → ℤ × ℤ | ∀ a : ℤ, ∃ n : ℕ, (p n).2 ≤ a} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun n =>
      measurableSet_le (measurable_pi_apply n).snd measurable_const
  have h : ∀ᵐ p ∂iidCodeMeasure.map (fun ω => fun n : ℕ => codeWalk ω n),
      ∀ a : ℤ, ∃ n : ℕ, (p n).2 ≤ a :=
    (ae_map_iff measurable_codeWalk.aemeasurable hS).mpr ae_codeWalk_snd_unbounded_below
  rw [← uibhbotWordFamilyLaw_map_forward_path] at h
  exact (ae_map_iff prefixLaw_measurable_forward.aemeasurable hS).mp h

end DirectedDistances.RandomWalk
