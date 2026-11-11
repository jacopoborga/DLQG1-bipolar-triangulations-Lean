module

public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
public import DirectedDistances.RandomWalk.FutureCodesAtHits
public import DirectedDistances.RandomWalk.IIDCodeRelabel
import DirectedDistances.Probability.FrontierIndependence
import DirectedDistances.Probability.ShiftIndependenceInduction

/-! # Excursion words and the UIBHBOT code window -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

-- Finite words use the discrete measurable space, as appropriate for this
-- countable state space.
instance : MeasurableSpace (List (Fin 3)) := ⊤

instance : MeasurableSingletonClass (List (Fin 3)) where
  measurableSet_singleton := by simp

/-- Length of the first-coordinate excursion through its first hit of `-1` -/
@[expose] noncomputable def excursionLength (ω : ℕ → Fin 3) : ℕ :=
  (codeFstFirstHit (-1) ω).toNat

/-- Codes of the steps from time zero through and including the first hit of `L = -1` -/
@[expose] noncomputable def excursionWord (ω : ℕ → Fin 3) : List (Fin 3) :=
  (List.range (excursionLength ω)).map (fun i => ω (i + 1))

private theorem codeList_eq_ofFn (k : ℕ) (ω : ℕ → Fin 3) :
    (List.range k).map (fun i => ω (i + 1)) =
      List.ofFn (fun i : Fin k => ω (i.val + 1)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_map, List.getElem_range, List.getElem_ofFn]

private theorem excursionWord_eq_prefix (k : ℕ) (ω : ℕ → Fin 3)
    (hτ : codeFstFirstHit (-1) ω = k) :
    excursionWord ω = List.ofFn (fun i : Fin k => ω (i.val + 1)) := by
  have hlen : excursionLength ω = k := by simp [excursionLength, hτ]
  rw [excursionWord, hlen]
  exact codeList_eq_ofFn k ω

private theorem measurable_excursionLength :
    Measurable (fun ω : ℕ → Fin 3 => excursionLength ω) := by
  let τ := fun ω : ℕ → Fin 3 => codeFstFirstHit (-1) ω
  have hfib : ∀ k : ℕ, MeasurableSet {ω | τ ω = k} := fun k =>
    codePast_le k _ (measurableSet_codePast_codeFstFirstHit_eq (-1) k)
  have htop : MeasurableSet {ω | τ ω = ⊤} := by
    have heq : {ω | τ ω = ⊤} = (⋃ k : ℕ, {ω | τ ω = k})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      constructor
      · intro h k hk
        rw [h] at hk
        exact ENat.top_ne_natCast k hk
      · intro h
        by_contra hn
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hn
        exact h k hk.symm
    rw [heq]
    exact (MeasurableSet.iUnion hfib).compl
  have hlen : Measurable (fun ω : ℕ → Fin 3 => (τ ω).toNat) := by
    refine measurable_to_countable' fun k => ?_
    by_cases hk : k = 0
    · subst k
      have heq : (fun ω : ℕ → Fin 3 => (τ ω).toNat) ⁻¹' ({0} : Set ℕ) =
          {ω | τ ω = 0} ∪ {ω | τ ω = ⊤} := by
        ext ω
        cases hω : τ ω <;> simp [hω]
      rw [heq]
      exact (hfib 0).union htop
    · have heq : (fun ω : ℕ → Fin 3 => (τ ω).toNat) ⁻¹' ({k} : Set ℕ) =
          {ω | τ ω = k} := by
        ext ω
        cases hω : τ ω with
        | top => simp [hω]; omega
        | coe n => simp [hω]
      rw [heq]
      exact hfib k
  simpa [excursionLength, τ] using hlen

/-- The excursion word is measurable as a countable-valued random variable. -/
theorem measurable_excursionWord : Measurable excursionWord := by
  classical
  refine measurable_to_countable' fun w => ?_
  let m := w.length
  let pref : (ℕ → Fin 3) → (Fin m → Fin 3) := fun ω i => ω (i.val + 1)
  have hpref : Measurable pref := Measurable.of_eval fun i => measurable_pi_apply (i.val + 1)
  let S : Set (Fin m → Fin 3) := {x | List.ofFn x = w}
  have hS : MeasurableSet S := (Set.toFinite S).measurableSet
  have heq : {ω | excursionWord ω = w} =
      {ω | excursionLength ω = m} ∩ pref ⁻¹' S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, pref, S]
    constructor
    · intro h
      have hlen : excursionLength ω = m := by
        have := congrArg List.length h
        simp [excursionWord] at this
        exact this
      refine ⟨hlen, ?_⟩
      have h' : (List.range m).map (fun i => ω (i + 1)) = w := by
        simpa [excursionWord, hlen] using h
      exact (codeList_eq_ofFn m ω).symm.trans h'
    · rintro ⟨hlen, h⟩
      have h' := (codeList_eq_ofFn m ω).trans h
      simpa [excursionWord, hlen] using h'
  change MeasurableSet {ω | excursionWord ω = w}
  rw [heq]
  exact (measurable_excursionLength (measurableSet_singleton _)).inter
    (hpref hS)

/-- Almost surely the first hit of `L = -1` takes at least one step. -/
theorem ae_one_le_excursionLength :
    ∀ᵐ ω ∂iidCodeMeasure, 1 ≤ excursionLength ω := by
  filter_upwards [ae_codeFstFirstHit_lt_top (a := -1) (by norm_num)] with ω hfin
  have hnot0 : codeFstFirstHit (-1) ω ≠ 0 := by
    intro hzero
    classical
    unfold codeFstFirstHit at hzero
    split at hzero
    · rename_i h
      have hn : Nat.find h = 0 := ENat.natCast_inj.mp hzero
      have hs := Nat.find_spec h
      rw [hn, codeWalk_zero] at hs
      omega
    · exact ENat.top_ne_natCast 0 hzero
  cases hτ : codeFstFirstHit (-1) ω with
  | top => simp [hτ] at hfin
  | coe n =>
    have hn : n ≠ 0 := by
      intro hn
      exact hnot0 (by simp [hτ, hn])
    simpa [excursionLength, hτ] using (Nat.one_le_iff_ne_zero.mpr hn)

private def excursionPrefixFunctional (k : ℕ) (p : ℕ → Fin 3) (_ : Unit) : List (Fin 3) :=
  List.ofFn (fun i : Fin k => p i.val)

/-- The shifted code sequence after the excursion endpoint has the original iid law -/
theorem map_excursionFuture_codeLaw :
    iidCodeMeasure.map
      (fun ω => codeShift (codeFstFirstHit (-1) ω).toNat ω) = iidCodeMeasure :=
  map_codeShift_codeFstFirstHit (-1)

/-- The stopped excursion word is independent of the future code sequence, and the future sequence -/
theorem indepFun_excursionWord_future :
    IndepFun excursionWord
      (fun ω => codeShift (codeFstFirstHit (-1) ω).toNat ω) iidCodeMeasure := by
  let τ := codeFstFirstHit (-1)
  let G : (ℕ → Fin 3) → Unit := fun _ => ()
  let H : (ℕ → Fin 3) → ℕ → Fin 3 := id
  have hGH : IndepFun G H iidCodeMeasure := indepFun_const_left () id
  have hF : ∀ k, Measurable (Function.uncurry (excursionPrefixFunctional k)) := by
    intro k
    have hp : Measurable (fun p : ℕ → Fin 3 => fun i : Fin k => p i.val) :=
      Measurable.of_eval fun i => measurable_pi_apply i.val
    have hf : Measurable (List.ofFn : (Fin k → Fin 3) → List (Fin 3)) :=
      measurable_of_countable _
    exact hf.comp (hp.comp measurable_fst)
  have hfront := DirectedDistances.Probability.indepFun_frontier_of_strongMarkov
    τ (measurableSet_codePast_codeFstFirstHit_eq (-1))
    (ae_codeFstFirstHit_lt_top (a := -1) (by norm_num))
    measurable_const measurable_id hGH excursionPrefixFunctional hF
  have hleft : (fun ω => excursionPrefixFunctional (τ ω).toNat
      (DirectedDistances.Probability.codePastVector τ ω)
      (G (codeShift (τ ω).toNat ω))) =ᵐ[iidCodeMeasure] excursionWord := by
    filter_upwards [ae_codeFstFirstHit_lt_top (a := -1) (by norm_num)] with ω hfinite
    cases ht : τ ω with
    | top => simp [τ, ht] at hfinite
    | coe k =>
      have hw := excursionWord_eq_prefix k ω ht
      have hpref : excursionPrefixFunctional k
          (DirectedDistances.Probability.codePastVector τ ω) () =
          List.ofFn (fun i : Fin k => ω (i.val + 1)) := by
        unfold excursionPrefixFunctional
        congr 1
        funext i
        simp [DirectedDistances.Probability.codePastVector, ht, i.isLt]
      change excursionPrefixFunctional k
        (DirectedDistances.Probability.codePastVector τ ω) () = excursionWord ω
      rw [hpref, hw]
  exact hfront.congr hleft (Filter.Eventually.of_forall fun _ => rfl)

 
@[expose] noncomputable def excursionWordLaw : Measure (List (Fin 3)) :=
  iidCodeMeasure.map excursionWord

instance : IsProbabilityMeasure excursionWordLaw := by
  unfold excursionWordLaw
  infer_instance

/-- The code sequence beginning immediately after its first `L = -1` hit -/
private noncomputable def excursionFuture (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  codeShift (excursionLength ω) ω

private theorem measurable_excursionFuture : Measurable excursionFuture := by
  change Measurable (fun ω : ℕ → Fin 3 =>
    codeShift (codeFstFirstHit (-1) ω).toNat ω)
  exact measurable_codeShift_toNat (fun ω : ℕ → Fin 3 => codeFstFirstHit (-1) ω)
    (measurableSet_codePast_codeFstFirstHit_eq (-1))

private theorem measurePreserving_excursionFuture :
    MeasurePreserving excursionFuture iidCodeMeasure iidCodeMeasure :=
  ⟨measurable_excursionFuture, map_excursionFuture_codeLaw⟩

/-- The iterated code after `k` first-coordinate excursions, with
`C₀(ω) = ω` and `Cₖ₊₁(ω) = codeShift (excursionLength (Cₖ(ω))) (Cₖ(ω))` -/
@[expose] noncomputable def iteratedExcursionCode :
    ℕ → (ℕ → Fin 3) → (ℕ → Fin 3)
  | 0 => fun ω => ω
  | k + 1 => fun ω =>
      codeShift (excursionLength (iteratedExcursionCode k ω))
        (iteratedExcursionCode k ω)

/-- The word of the `k`-th successive first-coordinate excursion -/
@[expose] noncomputable def iteratedExcursionWord (k : ℕ) (ω : ℕ → Fin 3) :
    List (Fin 3) := excursionWord (iteratedExcursionCode k ω)

/-- Every iterated post-excursion code is measurable. -/
theorem measurable_iteratedExcursionCode (k : ℕ) :
    Measurable (iteratedExcursionCode k) := by
  induction k with
  | zero => exact measurable_id
  | succ k ih =>
      change Measurable (fun ω => excursionFuture (iteratedExcursionCode k ω))
      exact measurable_excursionFuture.comp ih

/-- Every successive excursion word is measurable. -/
theorem measurable_iteratedExcursionWord (k : ℕ) :
    Measurable (iteratedExcursionWord k) :=
  measurable_excursionWord.comp (measurable_iteratedExcursionCode k)

private theorem iteratedExcursionCode_shift (k : ℕ) :
    (fun ω => iteratedExcursionCode k (excursionFuture ω)) =
      fun ω => iteratedExcursionCode (k + 1) ω := by
  funext ω
  induction k with
  | zero => rfl
  | succ k ih =>
      change excursionFuture (iteratedExcursionCode k (excursionFuture ω)) =
        excursionFuture (iteratedExcursionCode (k + 1) ω)
      rw [ih]

private theorem iteratedExcursionWord_shift (k : ℕ) :
    iteratedExcursionWord (k + 1) = iteratedExcursionWord k ∘ excursionFuture := by
  funext ω
  exact congrArg excursionWord (congrFun (iteratedExcursionCode_shift k) ω).symm

/-- Every successive excursion word has the one-excursion law -/
theorem map_iteratedExcursionWord (k : ℕ) :
    iidCodeMeasure.map (iteratedExcursionWord k) = excursionWordLaw := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedExcursionWord_shift]
      calc
        iidCodeMeasure.map (iteratedExcursionWord k ∘ excursionFuture) =
            (iidCodeMeasure.map excursionFuture).map (iteratedExcursionWord k) := by
          rw [← Measure.map_map (measurable_iteratedExcursionWord k)
            measurable_excursionFuture]
        _ = iidCodeMeasure.map (iteratedExcursionWord k) := by
          rw [measurePreserving_excursionFuture.map_eq]
        _ = excursionWordLaw := ih

private noncomputable def excursionWordEncode (w : List (Fin 3)) : ℤ :=
  Encodable.encode w

private noncomputable def excursionWordDecode (z : ℤ) : List (Fin 3) :=
  (Encodable.decode z.toNat).getD []

private theorem excursionWordDecode_encode (w : List (Fin 3)) :
    excursionWordDecode (excursionWordEncode w) = w := by
  simp [excursionWordDecode, excursionWordEncode, Encodable.encodek]

private theorem measurable_excursionWordEncode :
    Measurable excursionWordEncode := measurable_of_countable _

private theorem measurable_excursionWordDecode :
    Measurable excursionWordDecode := measurable_of_countable _

private theorem iIndepFun_iteratedExcursionWord :
    iIndepFun (fun k ω => excursionWordEncode (iteratedExcursionWord k ω))
      iidCodeMeasure := by
  let D : ℕ → (ℕ → Fin 3) → ℤ := fun k ω =>
    excursionWordEncode (iteratedExcursionWord k ω)
  have hD : ∀ k, Measurable (D k) := fun k =>
    measurable_excursionWordEncode.comp (measurable_iteratedExcursionWord k)
  have hshift : ∀ k, D (k + 1) =ᵐ[iidCodeMeasure] (D k ∘ excursionFuture) := by
    intro k
    filter_upwards with ω
    exact congrArg excursionWordEncode (congrFun (iteratedExcursionWord_shift k) ω)
  let tailFromCode : (ℕ → Fin 3) → ℕ → ℤ := fun ξ k =>
    excursionWordEncode (iteratedExcursionWord k ξ)
  have htailMeas : Measurable tailFromCode :=
    measurable_pi_iff.mpr fun k =>
      measurable_excursionWordEncode.comp (measurable_iteratedExcursionWord k)
  have hhead : IndepFun (D 0) (fun ω k => D (k + 1) ω) iidCodeMeasure := by
    have h := indepFun_excursionWord_future.comp (φ := excursionWordEncode)
      (ψ := tailFromCode) measurable_excursionWordEncode htailMeas
    have htail : (fun ω => tailFromCode (excursionFuture ω)) =ᵐ[iidCodeMeasure]
        (fun ω k => D (k + 1) ω) := by
      filter_upwards with ω
      funext k
      exact congrArg excursionWordEncode (congrFun (iteratedExcursionWord_shift k) ω).symm
    have hleft : (excursionWordEncode ∘ excursionWord) = D 0 := by
      funext ω
      rfl
    exact h.congr (Filter.Eventually.of_forall fun ω => congrFun hleft ω) htail
  exact DirectedDistances.Probability.iIndepFun_of_head_indep_tail_of_shift
    measurePreserving_excursionFuture hD hshift hhead

/-- The first `N` successive excursion words have the product of their -/
theorem map_iteratedExcursionWords (N : ℕ) :
    iidCodeMeasure.map (fun ω => fun i : Fin N => iteratedExcursionWord i.val ω) =
      Measure.pi (fun _ : Fin N => excursionWordLaw) := by
  let words : Fin N → (ℕ → Fin 3) → List (Fin 3) :=
    fun i ω => iteratedExcursionWord i.val ω
  have hind : iIndepFun (fun i ω => excursionWordEncode (words i ω)) iidCodeMeasure :=
    iIndepFun_iteratedExcursionWord.precomp Fin.val_injective
  have hdecode : iIndepFun words iidCodeMeasure := by
    have h := hind.comp (fun _ => excursionWordDecode)
      (fun _ => measurable_excursionWordDecode)
    apply h.congr
    intro i
    filter_upwards with ω
    exact excursionWordDecode_encode (words i ω)
  have hmap : iidCodeMeasure.map (fun ω i => words i ω) =
      Measure.pi (fun i => iidCodeMeasure.map (words i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin N => (measurable_iteratedExcursionWord i.val).aemeasurable)).mp hdecode
  calc
    iidCodeMeasure.map (fun ω i => iteratedExcursionWord i.val ω) =
        Measure.pi (fun i => iidCodeMeasure.map (iteratedExcursionWord i.val)) := hmap
    _ = Measure.pi (fun _ : Fin N => excursionWordLaw) := by
      congr 1
      funext i
      exact map_iteratedExcursionWord i.val

/-- A finite tuple of iid stopped excursion words. -/
@[expose] noncomputable def excursionWordProductLaw (N : ℕ) :
    Measure (Fin (2 * N) → List (Fin 3)) :=
  Measure.pi fun _ : Fin (2 * N) => excursionWordLaw

instance (N : ℕ) : IsProbabilityMeasure (excursionWordProductLaw N) := by
  unfold excursionWordProductLaw
  infer_instance






@[expose] def uibhbotWindowFromWords (N : ℕ)
    (words : Fin (2 * N) → List (Fin 3)) : Fin (2 * N + 1) → ℤ × ℤ := by
  classical
  exact fun j =>
    if hj : j.val ≤ N then
      let blocks := (List.finRange N).flatMap fun i =>
        ((words ⟨N + i.val, by omega⟩).reverse.map fun c => -lazyTwoDimensionalStep c)
      ((blocks.take (N - j.val)).map id).sum
    else
      let blocks := (List.finRange N).flatMap fun i => words ⟨i.val, by omega⟩
      ((blocks.take (j.val - N)).map lazyTwoDimensionalStep).sum

/-- The UIBHBOT excursion-window law on `[-N,N]`, built from `2N` iid stopped words. -/
@[expose] noncomputable def uibhbotExcursionWindowLaw (N : ℕ) :
    Measure (Fin (2 * N + 1) → ℤ × ℤ) :=
  (excursionWordProductLaw N).map (uibhbotWindowFromWords N)

theorem measurable_uibhbotWindowFromWords (N : ℕ) :
    Measurable (uibhbotWindowFromWords N) :=
  measurable_of_countable _

instance (N : ℕ) : IsProbabilityMeasure (uibhbotExcursionWindowLaw N) := by
  change IsProbabilityMeasure ((excursionWordProductLaw N).map (uibhbotWindowFromWords N))
  infer_instance





theorem uibhbotExcursionWindowLaw_eq_iidCodeMeasure_map (N : ℕ) :
    uibhbotExcursionWindowLaw N =
      iidCodeMeasure.map (fun ω => uibhbotWindowFromWords N
        (fun i : Fin (2 * N) => iteratedExcursionWord i.val ω)) := by
  let words : (ℕ → Fin 3) → Fin (2 * N) → List (Fin 3) :=
    fun ω i => iteratedExcursionWord i.val ω
  have hwords : iidCodeMeasure.map words =
      Measure.pi (fun _ : Fin (2 * N) => excursionWordLaw) := by
    exact map_iteratedExcursionWords (2 * N)
  have hwordsMeas : Measurable words :=
    measurable_pi_iff.mpr fun i => measurable_iteratedExcursionWord i.val
  calc
    uibhbotExcursionWindowLaw N =
        (Measure.pi (fun _ : Fin (2 * N) => excursionWordLaw)).map
          (uibhbotWindowFromWords N) := rfl
    _ = (iidCodeMeasure.map words).map (uibhbotWindowFromWords N) := by
      rw [hwords]
    _ = iidCodeMeasure.map (fun ω => uibhbotWindowFromWords N (words ω)) := by
      rw [Measure.map_map (measurable_uibhbotWindowFromWords N) hwordsMeas]
      apply congrArg (fun f => iidCodeMeasure.map f)
      funext ω
      rfl
    _ = iidCodeMeasure.map (fun ω => uibhbotWindowFromWords N
        (fun i : Fin (2 * N) => iteratedExcursionWord i.val ω)) := by
      apply congrArg (fun f => iidCodeMeasure.map f)
      funext ω
      rfl

end DirectedDistances.RandomWalk
