module

public import Mathlib.Probability.Independence.Basic

/-! # Generic probability helpers for the item-Busemann-ind reduction -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- A measure-preserving shift and the almost-everywhere increment shift
identity make every increment have the first increment's law. Generic helper -/
theorem measure_map_shift_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {D : ℕ → Ω → ℤ}
    (hD : ∀ n, Measurable (D n))
    (hshift : ∀ n, D (n + 1) =ᵐ[μ] (D n ∘ T)) (n : ℕ) :
    μ.map (D n) = μ.map (D 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        μ.map (D (n + 1)) = μ.map (D n ∘ T) := Measure.map_congr (hshift n)
        _ = (μ.map T).map (D n) := by
          rw [← Measure.map_map (hD n) hT.measurable]
        _ = μ.map (D n) := by rw [hT.map_eq]
        _ = μ.map (D 0) := ih

/-- Independence is preserved when both variables are precomposed with a
measure-preserving map. Generic helper for the item-Busemann-ind reduction -/
theorem indepFun_comp_measurePreserving {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → α} {g : Ω → β}
    (hfg : IndepFun f g μ) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (f ∘ T) (g ∘ T) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hbase := hfg.measure_inter_preimage_eq_mul s t hs ht
  have hleft : μ ((f ∘ T) ⁻¹' s) = μ (f ⁻¹' s) := by
    rw [show (f ∘ T) ⁻¹' s = T ⁻¹' (f ⁻¹' s) by ext x; simp]
    rw [← Measure.map_apply hT.measurable (hs.preimage hf), hT.map_eq]
  have hright : μ ((g ∘ T) ⁻¹' t) = μ (g ⁻¹' t) := by
    rw [show (g ∘ T) ⁻¹' t = T ⁻¹' (g ⁻¹' t) by ext x; simp]
    rw [← Measure.map_apply hT.measurable (ht.preimage hg), hT.map_eq]
  have hboth : μ ((f ∘ T) ⁻¹' s ∩ (g ∘ T) ⁻¹' t) =
      μ (f ⁻¹' s ∩ g ⁻¹' t) := by
    rw [show (f ∘ T) ⁻¹' s ∩ (g ∘ T) ⁻¹' t =
      T ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) by ext x; simp]
    rw [← Measure.map_apply hT.measurable
      ((hs.preimage hf).inter (ht.preimage hg)), hT.map_eq]
  rw [hboth, hleft, hright]
  exact hbase


private theorem shift_iterate_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {D : ℕ → Ω → ℤ} (hshift : ∀ n, D (n + 1) =ᵐ[μ] (D n ∘ T))
    (n k : ℕ) : D (n + k) =ᵐ[μ] (D k ∘ T^[n]) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        D (n + 1 + k) =ᵐ[μ] D (n + k) ∘ T := by
          have hi : n + 1 + k = n + k + 1 := by omega
          rw [hi]
          exact hshift (n + k)
        _ =ᵐ[μ] (D k ∘ T^[n]) ∘ T :=
          hT.quasiMeasurePreserving.ae_eq_comp ih
        _ =ᵐ[μ] D k ∘ T^[n + 1] := by
          apply Filter.EventuallyEq.of_eq
          funext ω
          simp [Function.iterate_succ]

/-- The head remains independent of the entire future after shifting the
starting index. Generic helper for the item-Busemann-ind reduction -/
theorem indepFun_increment_future_shifted {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {D : ℕ → Ω → ℤ}
    (hD : ∀ n, Measurable (D n))
    (hshift : ∀ n, D (n + 1) =ᵐ[μ] (D n ∘ T))
    (hhead : IndepFun (D 0) (fun ω (k : ℕ) => D (k + 1) ω) μ)
    (n : ℕ) :
    IndepFun (D n) (fun ω (k : ℕ) => D (n + k + 1) ω) μ := by
  have htailMeas : Measurable (fun ω (k : ℕ) => D (k + 1) ω) :=
    measurable_pi_iff.mpr fun k => hD (k + 1)
  have hcomp := indepFun_comp_measurePreserving (hT.iterate n) hhead (hD 0) htailMeas
  have hfirst : D n =ᵐ[μ] (D 0 ∘ T^[n]) := by
    simpa using (shift_iterate_ae hT hshift n 0)
  have htail : (fun ω (k : ℕ) => D (k + 1) (T^[n] ω)) =ᵐ[μ]
      (fun ω (k : ℕ) => D (n + k + 1) ω) := by
    have hall : ∀ᵐ ω ∂μ, ∀ k, D (k + 1) (T^[n] ω) = D (n + k + 1) ω :=
      ae_all_iff.mpr fun k => by
        have hk := shift_iterate_ae hT hshift n (k + 1)
        filter_upwards [hk] with ω hω
        simpa [Nat.add_assoc] using hω.symm
    filter_upwards [hall] with ω hω
    funext k
    exact hω k
  exact hcomp.congr hfirst.symm htail


/-- Add one variable that is independent of the vector of an already
independent finite family. Generic helper for the item-Busemann-ind reduction -/
theorem iIndepFun_cons_of_indepFun {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {head : Ω → ℤ} {tail : Fin n → Ω → ℤ}
    (hheadM : Measurable head) (htailM : ∀ i, Measurable (tail i))
    (hhead : IndepFun head (fun ω i => tail i ω) μ)
    (htail : iIndepFun tail μ) :
    iIndepFun (Fin.cons (α := fun _ : Fin (n + 1) => Ω → ℤ) head tail) μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℤ) 0
  let y : Ω → (Fin n → ℤ) := fun ω i => tail i ω
  let F : Ω → (Fin (n + 1) → ℤ) := fun ω => e.symm (head ω, y ω)
  have hyM : Measurable y := measurable_pi_iff.mpr htailM
  have hFM : Measurable F := e.symm.measurable.comp (hheadM.prodMk hyM)
  have hXA : ∀ i, AEMeasurable (fun ω => F ω i) μ := fun i =>
    ((measurable_pi_apply i).comp hFM).aemeasurable
  have htailLaw : μ.map y = Measure.pi (fun i => μ.map (tail i)) :=
    htail.map_fun_eq_pi_map fun i => (htailM i).aemeasurable
  have hpair : μ.map (fun ω => (head ω, y ω)) =
      (μ.map head).prod (μ.map y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hheadM.aemeasurable hyM.aemeasurable).mp hhead
  let ν : Fin (n + 1) → Measure ℤ := fun i => μ.map (fun ω => F ω i)
  have hmapF : (μ.map F).map e = (Measure.pi ν).map e := by
    calc
      (μ.map F).map e = μ.map (fun ω => (head ω, y ω)) := by
        rw [Measure.map_map e.measurable hFM]
        apply Measure.map_congr
        filter_upwards with ω
        simp [F, e, y]
      _ = (μ.map head).prod (μ.map y) := hpair
      _ = (Measure.pi ν).map e := by
        symm
        rw [(measurePreserving_piFinSuccAbove ν 0).map_eq]
        congr 1
        exact htailLaw.symm
  have hFInd : iIndepFun (fun i : Fin (n + 1) => fun ω => F ω i) μ := by
    rw [iIndepFun_iff_map_fun_eq_pi_map hXA]
    exact (MeasurableEquiv.map_measurableEquiv_injective e) hmapF
  have heq : (fun i : Fin (n + 1) => fun ω => F ω i) = Fin.cons (α := fun _ : Fin (n + 1) => Ω → ℤ) head tail := by
    funext i ω
    refine Fin.cases ?_ ?_ i
    · simp [F, e, y]
    · intro j
      simp [F, e, y]
  exact hFInd.congr fun i => Filter.EventuallyEq.of_eq (by
    funext ω
    exact congrFun (congrFun heq i) ω)


private theorem prefix_indep {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {D : ℕ → Ω → ℤ}
    (hD : ∀ n, Measurable (D n))
    (hshift : ∀ n, D (n + 1) =ᵐ[μ] (D n ∘ T))
    (hhead : IndepFun (D 0) (fun ω (k : ℕ) => D (k + 1) ω) μ) :
    ∀ (m start : ℕ), iIndepFun (fun i : Fin m => D (start + i.val)) μ := by
  intro m
  induction m with
  | zero =>
      intro start
      exact iIndepFun.of_subsingleton
  | succ m ih =>
      intro start
      let tail : Fin m → Ω → ℤ := fun i => D ((start + 1) + i.val)
      have htail : iIndepFun tail μ := by
        simpa [tail] using ih (start + 1)
      have hfuture := indepFun_increment_future_shifted hT hD hshift hhead start
      have htailProjMeas : Measurable (fun x : ℕ → ℤ => fun i : Fin m => x i.val) :=
        measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
      have hheadTail : IndepFun (D start) (fun ω i => tail i ω) μ := by
        have h := hfuture.comp measurable_id htailProjMeas
        exact h.congr (Filter.EventuallyEq.of_eq rfl)
          (Filter.EventuallyEq.of_eq (by
            funext ω i
            dsimp [tail]
            congr 1
            omega))
      have hcons := iIndepFun_cons_of_indepFun (hD start) (fun i => hD _) hheadTail htail
      have heq : (Fin.cons (D start) tail) =
          (fun i : Fin (m + 1) => fun ω => D (start + i.val) ω) := by
        funext i ω
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j
          simp only [Fin.cons_succ]
          dsimp [tail]
          congr 1
          omega
      exact hcons.congr fun i => Filter.EventuallyEq.of_eq (by
        funext ω
        exact congrFun (congrFun heq i) ω)

/-- Head independence from the entire future, together with measure-preserving
shift identities, implies mutual independence of the increment family. Generic
not counted as a paper theorem. -/
theorem iIndepFun_of_head_indep_tail_of_shift {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {D : ℕ → Ω → ℤ}
    (hD : ∀ n, Measurable (D n))
    (hshift : ∀ n, D (n + 1) =ᵐ[μ] (D n ∘ T))
    (hhead : IndepFun (D 0) (fun ω (n : ℕ) => D (n + 1) ω) μ) :
    iIndepFun D μ := by
  rw [iIndepFun_iff_finset]
  intro s
  let N := s.sup id + 1
  let g : s → Fin N := fun i => ⟨i.val,
    Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  have hprefix := prefix_indep hT hD hshift hhead N 0
  have hinj : Function.Injective g := fun i j hij => Subtype.ext (congrArg Fin.val hij)
  have hrestr := hprefix.precomp hinj
  have heq : (fun i : s => D (0 + (g i).val)) =
      (fun i : s => D i.val) := by
    funext i
    simp [g]
  exact hrestr.congr fun i => Filter.EventuallyEq.of_eq (by
    funext ω
    exact congrFun (congrFun heq i) ω)

/-- Distinct increments are pairwise independent under the shift and
head-tail hypotheses. Generic helper for the item-Busemann-ind reduction -/
theorem indepFun_increments_of_lt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {D : ℕ → Ω → ℤ}
    (hD : ∀ n, Measurable (D n))
    (hshift : ∀ n, D (n + 1) =ᵐ[μ] (D n ∘ T))
    (hhead : IndepFun (D 0) (fun ω (k : ℕ) => D (k + 1) ω) μ)
    {i j : ℕ} (hij : i < j) : IndepFun (D i) (D j) μ := by
  let k := j - i - 1
  have hk : i + k + 1 = j := by dsimp [k]; omega
  have h := indepFun_increment_future_shifted hT hD hshift hhead i
  have hp := h.comp measurable_id (measurable_pi_apply k)
  simpa [Function.comp_def, hk] using hp


end DirectedDistances.Probability
