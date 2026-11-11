module

public import DirectedDistances.RandomWalk.IIDVectorWalk
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory




@[expose] def codeReversal (n : ℕ) (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => if 1 ≤ i ∧ i ≤ n then Equiv.swap (0 : Fin 3) 1 (ω (n + 1 - i))
    else ω i



theorem codeReversal_involutive (n : ℕ) (ω : ℕ → Fin 3) :
    codeReversal n (codeReversal n ω) = ω := by
  funext i
  by_cases hi : 1 ≤ i ∧ i ≤ n
  · have hj : 1 ≤ n + 1 - i ∧ n + 1 - i ≤ n := by omega
    have hidx : n + 1 - (n + 1 - i) = i := by omega
    simp [codeReversal, hi, hj, hidx, Equiv.swap_apply_self]
  · simp [codeReversal, hi]




theorem lazyTwoDimensionalStep_codeSwap (c : Fin 3) :
    DirectedDistances.RandomWalk.lazyTwoDimensionalStep
        (Equiv.swap (0 : Fin 3) 1 c) =
      -Prod.swap (DirectedDistances.RandomWalk.lazyTwoDimensionalStep c) := by
  fin_cases c <;> norm_num [Equiv.swap_apply_def,
    DirectedDistances.RandomWalk.lazyTwoDimensionalStep]




theorem codeWalk_codeReversal (n : ℕ) (ω : ℕ → Fin 3) {j : ℕ} (hj : j ≤ n) :
    DirectedDistances.RandomWalk.codeWalk (codeReversal n ω) j =
      Prod.swap (DirectedDistances.RandomWalk.codeWalk ω (n - j) -
        DirectedDistances.RandomWalk.codeWalk ω n) := by
  induction j with
  | zero => simp [DirectedDistances.RandomWalk.codeWalk_zero]
  | succ j ih =>
      have hjn : j < n := by omega
      have hIn : 1 ≤ j + 1 ∧ j + 1 ≤ n := by omega
      have hletter : codeReversal n ω (j + 1) =
          Equiv.swap (0 : Fin 3) 1 (ω (n - j)) := by
        have hidx : n + 1 - (j + 1) = n - j := by omega
        simp [codeReversal, hIn, hidx]
      have hstep : DirectedDistances.RandomWalk.codeWalk ω (n - j) -
          DirectedDistances.RandomWalk.codeWalk ω (n - (j + 1)) =
            DirectedDistances.RandomWalk.lazyTwoDimensionalStep (ω (n - j)) := by
        have hidx : n - (j + 1) + 1 = n - j := by omega
        rw [← hidx]
        exact DirectedDistances.RandomWalk.codeWalk_succ_sub ω (n - (j + 1))
      have hrevwalk : DirectedDistances.RandomWalk.codeWalk (codeReversal n ω) (j + 1) =
          DirectedDistances.RandomWalk.codeWalk (codeReversal n ω) j +
            DirectedDistances.RandomWalk.lazyTwoDimensionalStep
              (codeReversal n ω (j + 1)) := by
        have hs := DirectedDistances.RandomWalk.codeWalk_succ_sub
          (codeReversal n ω) j
        rw [← hs]
        abel
      rw [hrevwalk, hletter, lazyTwoDimensionalStep_codeSwap, ih (by omega)]
      rw [show n - (j + 1) = n - j - 1 by omega]
      have hswap : ∀ p q : ℤ × ℤ, Prod.swap (p - q) = Prod.swap p - Prod.swap q := by
        intro p q
        cases p
        cases q
        rfl
      have hstep' : DirectedDistances.RandomWalk.codeWalk ω (n - j) -
          DirectedDistances.RandomWalk.codeWalk ω (n - j - 1) =
            DirectedDistances.RandomWalk.lazyTwoDimensionalStep (ω (n - j)) := by
        rw [show n - (j + 1) = n - j - 1 by omega] at hstep
        exact hstep
      rw [← hstep', hswap]
      apply Prod.ext <;> simp [Prod.swap]

private def codeTail (ω : ℕ → Fin 3) : ℕ → Fin 3 := fun i => ω (i + 1)

private def insertDummy (x : ℕ → Fin 3) : ℕ → Fin 3 := fun i =>
  if i = 0 then 0 else x (i - 1)

private noncomputable def codeMarginalLaw (i : ℕ) : Measure (Fin 3) :=
  if i = 0 then Measure.dirac 0 else DirectedDistances.RandomWalk.uniformCodeMeasure

private instance codeMarginalLaw_probability (i : ℕ) :
    IsProbabilityMeasure (codeMarginalLaw i) := by
  unfold codeMarginalLaw
  split <;> infer_instance

private theorem measurable_codeTail : Measurable codeTail := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (i + 1)

private theorem measurable_insertDummy : Measurable insertDummy := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i = 0
  · simp [insertDummy, hi]
  · simpa [insertDummy, hi] using measurable_pi_apply (i - 1)

private theorem measurable_codeReversal (n : ℕ) :
    Measurable (codeReversal n) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : 1 ≤ i ∧ i ≤ n
  · simp [codeReversal, hi]
    exact (measurable_of_countable _).comp (measurable_pi_apply (n + 1 - i))
  · simp [codeReversal, hi]
    exact measurable_pi_apply i

private theorem map_code_coordinate (i : ℕ) :
    DirectedDistances.RandomWalk.iidCodeMeasure.map (fun ω => ω (i + 1)) =
      DirectedDistances.RandomWalk.uniformCodeMeasure := by
  let j : Fin (i + 1 + 1) := ⟨i + 1, by omega⟩
  have h := congrArg (fun μ : Measure (Fin (i + 1 + 1) → Fin 3) =>
    μ.map (Function.eval j))
    (DirectedDistances.RandomWalk.iidCodeMeasure_map_prefix (i + 1))
  rw [Measure.map_map (measurable_pi_apply j) (by fun_prop)] at h
  have hp : (Measure.pi (fun j : Fin (i + 1 + 1) => codeMarginalLaw j.val)).map
      (Function.eval j) = codeMarginalLaw j.val :=
    (measurePreserving_eval _ j).map_eq
  change _ = (Measure.pi (fun j : Fin (i + 1 + 1) => codeMarginalLaw j.val)).map
    (Function.eval j) at h
  rw [hp] at h
  simpa [codeMarginalLaw, j, Function.comp_def, Function.eval] using h

private theorem iIndepFun_codeTail :
    iIndepFun (fun i (ω : ℕ → Fin 3) => ω (i + 1))
      DirectedDistances.RandomWalk.iidCodeMeasure := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  let n := s.sup id + 1
  let e (i : s) : Fin (n + 1) := ⟨i.val + 1, by
    have hi := Finset.le_sup (f := id) i.property
    change i.val ≤ s.sup id at hi
    dsimp [n]
    omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    have := congrArg Fin.val h
    dsimp [e] at this
    omega
  let μ := Measure.pi (fun j : Fin (n + 1) => codeMarginalLaw j.val)
  have hind : iIndepFun (fun i : s => fun q : Fin (n + 1) → Fin 3 => q (e i)) μ :=
    (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).precomp he
  have hm : DirectedDistances.RandomWalk.iidCodeMeasure.map
      (fun ω => fun j : Fin (n + 1) => ω j.val) = μ := by
    exact DirectedDistances.RandomWalk.iidCodeMeasure_map_prefix n
  have hmass (t : Set (Fin (n + 1) → Fin 3)) :
      μ t = DirectedDistances.RandomWalk.iidCodeMeasure
        ((fun ω => fun j : Fin (n + 1) => ω j.val) ⁻¹' t) := by
    rw [← hm, Measure.map_apply (by fun_prop) ((Set.to_countable t).measurableSet)]
  have h := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : s => sets i.val)
    (fun _ _ => (Set.to_countable _).measurableSet)
  simp only [hmass] at h
  rw [← Finset.prod_coe_sort]
  convert h using 1
  · congr 1
    ext ω
    simp [e]
  · apply Finset.prod_congr rfl
    intro i _
    congr 1

private theorem iidCodeMeasure_map_codeTail :
    DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail =
      Measure.infinitePi (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure) := by
  have h := iIndepFun_codeTail.map_fun_eq_infinitePi_map (by fun_prop)
  calc
    DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail =
        Measure.infinitePi (fun i =>
          DirectedDistances.RandomWalk.iidCodeMeasure.map (fun ω => ω (i + 1))) := by
      change DirectedDistances.RandomWalk.iidCodeMeasure.map
          (fun ω i => ω (i + 1)) = _
      exact h
    _ = Measure.infinitePi
        (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure) := by
      congr 1
      funext i
      exact map_code_coordinate i

private theorem iidCodeMeasure_reconstruct :
    DirectedDistances.RandomWalk.iidCodeMeasure =
      (DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail).map insertDummy := by
  have hstart : ∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure, ω 0 = 0 := by
    rw [DirectedDistances.RandomWalk.iidCodeMeasure]
    exact DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) DirectedDistances.RandomWalk.uniformCodeMeasure) 0
  have hfun : insertDummy ∘ codeTail =ᵐ[
      DirectedDistances.RandomWalk.iidCodeMeasure] id := by
    filter_upwards [hstart] with ω hω
    funext i
    cases i with
    | zero => simpa [insertDummy, codeTail] using hω.symm
    | succ i => simp [insertDummy, codeTail]
  calc
    DirectedDistances.RandomWalk.iidCodeMeasure =
        DirectedDistances.RandomWalk.iidCodeMeasure.map id := by rw [Measure.map_id]
    _ = DirectedDistances.RandomWalk.iidCodeMeasure.map (insertDummy ∘ codeTail) :=
      Measure.map_congr hfun.symm
    _ = (DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail).map insertDummy :=
      (Measure.map_map measurable_insertDummy measurable_codeTail).symm

private def tailIndexReversal (n : ℕ) : ℕ ≃ ℕ where
  toFun i := if i < n then n - 1 - i else i
  invFun i := if i < n then n - 1 - i else i
  left_inv := by
    intro i
    by_cases hi : i < n
    · have hj : n - 1 - i < n := by omega
      simp [hi, hj]
      omega
    · simp [hi]
  right_inv := by
    intro i
    by_cases hi : i < n
    · have hj : n - 1 - i < n := by omega
      simp [hi, hj]
      omega
    · simp [hi]

private def tailLetterReversal (n : ℕ) (x : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => if i < n then Equiv.swap (0 : Fin 3) 1 (x i) else x i

private def tailReversal (n : ℕ) (x : ℕ → Fin 3) : ℕ → Fin 3 :=
  tailLetterReversal n (fun i => x (tailIndexReversal n i))

private theorem measurePreserving_tailIndexReversal (n : ℕ) :
    MeasurePreserving (fun x : ℕ → Fin 3 => fun i => x (tailIndexReversal n i))
      (Measure.infinitePi (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure))
      (Measure.infinitePi (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure)) := by
  have hfun : (fun x : ℕ → Fin 3 => fun i => x (tailIndexReversal n i)) =
      MeasurableEquiv.piCongrLeft (fun _ : ℕ => Fin 3) (tailIndexReversal n).symm := by
    funext x i
    simpa using (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ℕ => Fin 3) (tailIndexReversal n).symm x
      ((tailIndexReversal n) i)).symm
  rw [hfun]
  exact ⟨(MeasurableEquiv.piCongrLeft _ (tailIndexReversal n).symm).measurable,
    Measure.infinitePi_map_piCongrLeft
      (μ := fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure)
      (tailIndexReversal n).symm⟩

private theorem measurePreserving_tailLetterReversal (n : ℕ) :
    MeasurePreserving (tailLetterReversal n)
      (Measure.infinitePi (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure))
      (Measure.infinitePi (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure)) := by
  let f : ℕ → Fin 3 → Fin 3 := fun i c =>
    if i < n then Equiv.swap (0 : Fin 3) 1 c else c
  have hτ : (Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))).map
      (Equiv.swap (0 : Fin 3) 1) =
        Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)) := by
    apply Measure.ext_of_singleton
    intro c
    have hpre : (Equiv.swap (0 : Fin 3) 1) ⁻¹' ({c} : Set (Fin 3)) =
        {Equiv.swap (0 : Fin 3) 1 c} := by
      ext x
      simp [Equiv.swap_apply_eq_iff]
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton c),
      hpre]
    simp [Measure.uniformOfFinset_apply_singleton]
  have hf : ∀ i, MeasurePreserving (f i)
      DirectedDistances.RandomWalk.uniformCodeMeasure
      DirectedDistances.RandomWalk.uniformCodeMeasure := by
    intro i
    by_cases hi : i < n
    · have hs : MeasurePreserving (Equiv.swap (0 : Fin 3) 1)
          DirectedDistances.RandomWalk.uniformCodeMeasure
          DirectedDistances.RandomWalk.uniformCodeMeasure :=
        ⟨measurable_of_countable _, by
          simpa [DirectedDistances.RandomWalk.uniformCodeMeasure] using hτ⟩
      rw [show f i = Equiv.swap (0 : Fin 3) 1 from by simp [f, hi]]
      exact hs
    · have hid : MeasurePreserving (id : Fin 3 → Fin 3)
          DirectedDistances.RandomWalk.uniformCodeMeasure
          DirectedDistances.RandomWalk.uniformCodeMeasure :=
        ⟨measurable_id, Measure.map_id⟩
      rw [show f i = id from by simp [f, hi]; rfl]
      exact hid
  have hmap := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure) (f := f)
    (fun i => (hf i).measurable)
  have hfun : tailLetterReversal n = fun x i => f i (x i) := by
    funext x i
    rfl
  have hmeas : Measurable (tailLetterReversal n) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i < n
    · simp [tailLetterReversal, hi]
      exact (measurable_of_countable _).comp (measurable_pi_apply i)
    · simp [tailLetterReversal, hi]
      exact measurable_pi_apply i
  refine ⟨hmeas, ?_⟩
  rw [hfun, hmap]
  congr 1
  funext i
  exact (hf i).map_eq

private theorem measurePreserving_tailReversal (n : ℕ) :
    MeasurePreserving (tailReversal n)
      (Measure.infinitePi (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure))
      (Measure.infinitePi (fun _ : ℕ => DirectedDistances.RandomWalk.uniformCodeMeasure)) :=
  (measurePreserving_tailLetterReversal n).comp
    (measurePreserving_tailIndexReversal n)

private theorem codeTail_codeReversal (n : ℕ) (ω : ℕ → Fin 3) :
    codeTail (codeReversal n ω) = tailReversal n (codeTail ω) := by
  funext i
  change codeReversal n ω (i + 1) =
    tailLetterReversal n (fun k => codeTail ω (tailIndexReversal n k)) i
  by_cases hi : i < n
  · have hI : 1 ≤ i + 1 ∧ i + 1 ≤ n := by omega
    have hidx : n + 1 - (i + 1) = n - i := by omega
    have hidx' : n - 1 - i + 1 = n - i := by omega
    simp [codeTail, codeReversal, tailLetterReversal,
      tailIndexReversal, hi, hI, hidx, hidx']
  · have hnot : ¬ i + 1 ≤ n := by omega
    simp [codeTail, codeReversal, tailLetterReversal,
      tailIndexReversal, hi, hnot]




theorem measurePreserving_codeReversal (n : ℕ) :
    MeasurePreserving (codeReversal n)
      DirectedDistances.RandomWalk.iidCodeMeasure
      DirectedDistances.RandomWalk.iidCodeMeasure := by
  have htail :
      (DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n)).map codeTail =
        DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail := by
    calc
      _ = DirectedDistances.RandomWalk.iidCodeMeasure.map
          (codeTail ∘ codeReversal n) := by
            rw [Measure.map_map measurable_codeTail (measurable_codeReversal n)]
      _ = DirectedDistances.RandomWalk.iidCodeMeasure.map
          (tailReversal n ∘ codeTail) := by
            congr 1
            funext ω
            exact codeTail_codeReversal n ω
      _ = (DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail).map
          (tailReversal n) :=
            (Measure.map_map (measurePreserving_tailReversal n).measurable
              measurable_codeTail).symm
      _ = DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail := by
            rw [iidCodeMeasure_map_codeTail]
            exact (measurePreserving_tailReversal n).map_eq
  have hstart : ∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure, ω 0 = 0 := by
    rw [DirectedDistances.RandomWalk.iidCodeMeasure]
    exact DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) DirectedDistances.RandomWalk.uniformCodeMeasure) 0
  have hrec : ((DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n)).map
      codeTail).map insertDummy =
        DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n) := by
    have hfun : (insertDummy ∘ codeTail) ∘ codeReversal n =ᵐ[
        DirectedDistances.RandomWalk.iidCodeMeasure] codeReversal n := by
      filter_upwards [hstart] with ω hω
      funext i
      cases i with
      | zero => simp [insertDummy, codeReversal, hω]
      | succ i => simp [insertDummy, codeTail]
    calc
      ((DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n)).map
          codeTail).map insertDummy =
          DirectedDistances.RandomWalk.iidCodeMeasure.map
            ((insertDummy ∘ codeTail) ∘ codeReversal n) := by
              rw [Measure.map_map measurable_insertDummy measurable_codeTail,
                Measure.map_map (measurable_insertDummy.comp measurable_codeTail)
                  (measurable_codeReversal n)]
      _ = DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n) :=
        Measure.map_congr hfun
  refine ⟨measurable_codeReversal n, ?_⟩
  calc
    DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n) =
        ((DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n)).map
          codeTail).map insertDummy := hrec.symm
    _ = (DirectedDistances.RandomWalk.iidCodeMeasure.map codeTail).map insertDummy := by
      rw [htail]
    _ = DirectedDistances.RandomWalk.iidCodeMeasure := iidCodeMeasure_reconstruct.symm




theorem codeReversal_process_law (n : ℕ) :
    DirectedDistances.RandomWalk.iidCodeMeasure.map
        (fun ω => fun j : Fin (n + 1) =>
          Prod.swap (DirectedDistances.RandomWalk.codeWalk ω (n - j.val) -
            DirectedDistances.RandomWalk.codeWalk ω n)) =
      DirectedDistances.RandomWalk.iidCodeMeasure.map
        (fun ω => fun j : Fin (n + 1) =>
          DirectedDistances.RandomWalk.codeWalk ω j.val) := by
  let F : (ℕ → Fin 3) → Fin (n + 1) → ℤ × ℤ := fun ω j =>
    Prod.swap (DirectedDistances.RandomWalk.codeWalk ω (n - j.val) -
      DirectedDistances.RandomWalk.codeWalk ω n)
  let G : (ℕ → Fin 3) → Fin (n + 1) → ℤ × ℤ := fun ω j =>
    DirectedDistances.RandomWalk.codeWalk ω j.val
  have hG : Measurable G := by
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun ω =>
      DirectedDistances.RandomWalk.codeWalk ω j.val)
    exact (measurable_pi_apply j.val).comp
      DirectedDistances.RandomWalk.measurable_codeWalk
  have hpoint : F = G ∘ codeReversal n := by
    funext ω j
    exact (codeWalk_codeReversal n ω (by omega)).symm
  calc
    DirectedDistances.RandomWalk.iidCodeMeasure.map F =
        DirectedDistances.RandomWalk.iidCodeMeasure.map (G ∘ codeReversal n) :=
          congrArg (fun f => DirectedDistances.RandomWalk.iidCodeMeasure.map f) hpoint
    _ = (DirectedDistances.RandomWalk.iidCodeMeasure.map (codeReversal n)).map G :=
      (Measure.map_map hG (measurable_codeReversal n)).symm
    _ = DirectedDistances.RandomWalk.iidCodeMeasure.map G :=
      congrArg (fun μ => μ.map G) (measurePreserving_codeReversal n).map_eq

end DirectedDistances.PaperProofs.Section7
