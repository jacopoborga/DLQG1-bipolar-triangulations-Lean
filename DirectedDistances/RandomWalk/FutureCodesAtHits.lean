module

public import DirectedDistances.RandomWalk.IIDCodeRelabel

/-! # The future codes at an a.s. finite stopping time

Helpers for the first claim of `lem-directed-contain`
`tau_k` that `R = -k` (or `L = k`), the future codes have the law of the whole code sequence and
are independent of the stopped past, by the strong Markov property. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- The code sequence seen from a stopping time, as a function of the sample -/
theorem measurable_codeShift_toNat (tau : (ℕ → Fin 3) → ℕ∞)
    (htau : ∀ k : ℕ, MeasurableSet[codePast k] {ω | tau ω = k}) :
    Measurable (fun ω => codeShift (tau ω).toNat ω) := by
  have hm : ∀ k : ℕ, MeasurableSet {ω | tau ω = k} := fun k => codePast_le k _ (htau k)
  have htop : MeasurableSet {ω | tau ω = ⊤} := by
    have : {ω | tau ω = ⊤} = (⋃ k : ℕ, {ω | tau ω = k})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      constructor
      · intro h k hk; rw [h] at hk; exact ENat.top_ne_natCast k hk
      · intro h
        by_contra hne
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
        exact h k hk.symm
    rw [this]; exact (MeasurableSet.iUnion hm).compl
  have hn : Measurable (fun ω => (tau ω).toNat) := by
    refine measurable_to_countable' fun k => ?_
    by_cases hk : k = 0
    · have : (fun ω => (tau ω).toNat) ⁻¹' {k} = {ω | tau ω = ((0 : ℕ) : ℕ∞)} ∪ {ω | tau ω = ⊤} := by
        ext ω
        subst hk
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_ofPred_eq]
        constructor
        · intro h
          cases htω : tau ω with
          | top => exact Or.inr rfl
          | coe m => left; rw [htω] at h; simpa using h
        · rintro (h | h) <;> simp [h]
      rw [this]; exact (hm 0).union htop
    · have : (fun ω => (tau ω).toNat) ⁻¹' {k} = {ω | tau ω = k} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
        constructor
        · intro h
          cases htω : tau ω with
          | top => rw [htω] at h; simp at h; exact absurd h.symm hk
          | coe m => rw [htω] at h; simpa using h
        · intro h; rw [h]; simp
      rw [this]; exact hm k
  have hf : Measurable (fun p : (ℕ → Fin 3) × ℕ => codeShift p.2 p.1) :=
    measurable_from_prod_countable_left fun k => measurable_codeShift k
  exact hf.comp (measurable_id.prodMk hn)

/-- Independence of the future codes at an a.s. finite stopping time from the stopped past -/
theorem iidCodeMeasure_inter_codeShift_toNat_preimage (tau : (ℕ → Fin 3) → ℕ∞)
    (htau : ∀ k : ℕ, MeasurableSet[codePast k] {ω | tau ω = k})
    (hfin : ∀ᵐ ω ∂iidCodeMeasure, tau ω < ⊤)
    {A : Set (ℕ → Fin 3)} (hA : ∀ k : ℕ, MeasurableSet[codePast k] (A ∩ {ω | tau ω = k}))
    {B : Set (ℕ → Fin 3)} (hB : MeasurableSet B) :
    iidCodeMeasure (A ∩ {ω | codeShift (tau ω).toNat ω ∈ B}) =
      iidCodeMeasure A * iidCodeMeasure B := by
  have h := iidCodeMeasure_strongMarkov tau htau hA hB
  have e1 : A ∩ {ω | tau ω < ⊤} ∩ {ω | codeShift (tau ω).toNat ω ∈ B} =ᵐ[iidCodeMeasure]
      A ∩ {ω | codeShift (tau ω).toNat ω ∈ B} := by
    filter_upwards [hfin] with ω hω
    exact propext ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hω⟩, h.2⟩⟩
  have e2 : A ∩ {ω | tau ω < ⊤} =ᵐ[iidCodeMeasure] A := by
    filter_upwards [hfin] with ω hω
    exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
  rw [← measure_congr e1, ← measure_congr e2]
  exact h

/-- The future codes at an a.s. finite stopping time have the iid code law -/
theorem map_codeShift_toNat (tau : (ℕ → Fin 3) → ℕ∞)
    (htau : ∀ k : ℕ, MeasurableSet[codePast k] {ω | tau ω = k})
    (hfin : ∀ᵐ ω ∂iidCodeMeasure, tau ω < ⊤) :
    iidCodeMeasure.map (fun ω => codeShift (tau ω).toNat ω) = iidCodeMeasure := by
  ext B hB
  rw [Measure.map_apply (measurable_codeShift_toNat tau htau) hB]
  have := iidCodeMeasure_inter_codeShift_toNat_preimage tau htau hfin
    (A := Set.univ) (fun k => by simpa using htau k) hB
  rw [Set.univ_inter, measure_univ, one_mul] at this
  exact this

/-- Law of a measurable functional of the future codes at an a.s. finite stopping time -/
theorem map_comp_codeShift_toNat {β : Type*} [MeasurableSpace β] (tau : (ℕ → Fin 3) → ℕ∞)
    (htau : ∀ k : ℕ, MeasurableSet[codePast k] {ω | tau ω = k})
    (hfin : ∀ᵐ ω ∂iidCodeMeasure, tau ω < ⊤)
    {F : (ℕ → Fin 3) → β} (hF : Measurable F) :
    iidCodeMeasure.map (fun ω => F (codeShift (tau ω).toNat ω)) = iidCodeMeasure.map F := by
  have := Measure.map_map hF (measurable_codeShift_toNat tau htau) (μ := iidCodeMeasure)
  rw [map_codeShift_toNat tau htau hfin] at this
  exact this.symm

/-- Second-coordinate hit: the future codes have the iid code law -/
theorem map_codeShift_codeSndFirstHit (a : ℤ) :
    iidCodeMeasure.map (fun ω => codeShift (codeSndFirstHit a ω).toNat ω) = iidCodeMeasure :=
  map_codeShift_toNat _ (measurableSet_codePast_codeSndFirstHit_eq a)
    (ae_codeSndFirstHit_lt_top_int a)

/-- First-coordinate hit: the future codes have the iid code law -/
theorem map_codeShift_codeFstFirstHit (a : ℤ) :
    iidCodeMeasure.map (fun ω => codeShift (codeFstFirstHit a ω).toNat ω) = iidCodeMeasure :=
  map_codeShift_toNat _ (measurableSet_codePast_codeFstFirstHit_eq a)
    (ae_codeFstFirstHit_lt_top_int a)

/-- Second-coordinate hit: the future codes are independent of the stopped past -/
theorem iidCodeMeasure_inter_codeShift_codeSndFirstHit (a : ℤ) {A : Set (ℕ → Fin 3)}
    (hA : ∀ k : ℕ, MeasurableSet[codePast k] (A ∩ {ω | codeSndFirstHit a ω = k}))
    {B : Set (ℕ → Fin 3)} (hB : MeasurableSet B) :
    iidCodeMeasure (A ∩ {ω | codeShift (codeSndFirstHit a ω).toNat ω ∈ B}) =
      iidCodeMeasure A * iidCodeMeasure B :=
  iidCodeMeasure_inter_codeShift_toNat_preimage _ (measurableSet_codePast_codeSndFirstHit_eq a)
    (ae_codeSndFirstHit_lt_top_int a) hA hB

/-- First-coordinate hit: the future codes are independent of the stopped past -/
theorem iidCodeMeasure_inter_codeShift_codeFstFirstHit (a : ℤ) {A : Set (ℕ → Fin 3)}
    (hA : ∀ k : ℕ, MeasurableSet[codePast k] (A ∩ {ω | codeFstFirstHit a ω = k}))
    {B : Set (ℕ → Fin 3)} (hB : MeasurableSet B) :
    iidCodeMeasure (A ∩ {ω | codeShift (codeFstFirstHit a ω).toNat ω ∈ B}) =
      iidCodeMeasure A * iidCodeMeasure B :=
  iidCodeMeasure_inter_codeShift_toNat_preimage _ (measurableSet_codePast_codeFstFirstHit_eq a)
    (ae_codeFstFirstHit_lt_top_int a) hA hB

/-- Law of any measurable functional of the future codes at the second-coordinate hit -/
theorem map_comp_codeShift_codeSndFirstHit {β : Type*} [MeasurableSpace β] (a : ℤ)
    {F : (ℕ → Fin 3) → β} (hF : Measurable F) :
    iidCodeMeasure.map (fun ω => F (codeShift (codeSndFirstHit a ω).toNat ω)) =
      iidCodeMeasure.map F :=
  map_comp_codeShift_toNat _ (measurableSet_codePast_codeSndFirstHit_eq a)
    (ae_codeSndFirstHit_lt_top_int a) hF

/-- Law of any measurable functional of the future codes at the first-coordinate hit -/
theorem map_comp_codeShift_codeFstFirstHit {β : Type*} [MeasurableSpace β] (a : ℤ)
    {F : (ℕ → Fin 3) → β} (hF : Measurable F) :
    iidCodeMeasure.map (fun ω => F (codeShift (codeFstFirstHit a ω).toNat ω)) =
      iidCodeMeasure.map F :=
  map_comp_codeShift_toNat _ (measurableSet_codePast_codeFstFirstHit_eq a)
    (ae_codeFstFirstHit_lt_top_int a) hF

end DirectedDistances.RandomWalk
