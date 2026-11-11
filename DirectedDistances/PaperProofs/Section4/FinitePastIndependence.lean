module

public import DirectedDistances.PaperProofs.Section4.PastMapFixedLevelFiberLaw
public import DirectedDistances.PlanarMap.LRIndConcreteData

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open Classical MeasureTheory ProbabilityTheory

private theorem indepFun_map_iff_comp {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) {f : β → γ} {g : β → δ} {k : α → β}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    IndepFun f g (μ.map k) ↔ IndepFun (f ∘ k) (g ∘ k) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul,
    indepFun_iff_measure_inter_preimage_eq_mul]
  constructor
  · intro h U V hU hV
    have hUV := h U V hU hV
    rw [Measure.map_apply hk ((hf hU).inter (hg hV)),
      Measure.map_apply hk (hf hU), Measure.map_apply hk (hg hV)] at hUV
    exact hUV
  · intro h U V hU hV
    rw [Measure.map_apply hk ((hf hU).inter (hg hV)),
      Measure.map_apply hk (hf hU), Measure.map_apply hk (hg hV)]
    exact h U V hU hV

/-- code law; uses the compiled Lemma 3.11 and Lemma 3.15 candidates as ordinary lemmas
the σ-algebra F_k are not treated; not the paper result. The conclusion holds for
every default pair. -/
theorem finiteStoppedPastCuts_independent
    (x : XDP) (ℓ r s : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (hF : 0 < boltzmannLaw ℓ r
      (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
      (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2
      (boltzmannFiber (ℓ := ℓ) (r := r) x s)) :
    let Good (ω : ℕ → Fin 3) : Prop :=
      ∃ m : BoltzmannSpace ℓ r,
        stoppedMap r hr ω = some (⟨ℓ, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s
    let E : Set (ℕ → Fin 3) := boltzmannEvent r ∩ {ω | Good ω}
    ∀ default :
      {mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR},
      IndepFun
        (fun ω => if h : Good ω then
          (lrCutLeftClass (lrCutGlueRepData x ℓ s r) default (Classical.choose h)).val
          else default.1.val)
        (fun ω => if h : Good ω then
          (lrCutRightClass (lrCutGlueRepData x ℓ s r) default (Classical.choose h)).val
          else default.2.val)
        (iidCodeMeasure[| E]) := by
  classical
  dsimp only
  intro default
  let d := lrCutGlueRepData x ℓ s r
  let ν := (boltzmannLaw ℓ r
    (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
    (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2)[|
      boltzmannFiber (ℓ := ℓ) (r := r) x s]
  let ι : BoltzmannSpace ℓ r → Option (AllBoltzmannSpace r) :=
    fun m => some (⟨ℓ, m⟩ : AllBoltzmannSpace r)
  have hι : Function.Injective ι := by
    intro m n h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
  let P (o : Option (AllBoltzmannSpace r)) : Prop :=
    ∃ m : BoltzmannSpace ℓ r, o = ι m ∧ xdpLen x m = s
  let L : Option (AllBoltzmannSpace r) → BoltzmannSpace ℓ s := fun o =>
    if h : P o then (lrCutLeftClass d default (Classical.choose h)).val
    else default.1.val
  let R : Option (AllBoltzmannSpace r) → BoltzmannSpace s r := fun o =>
    if h : P o then (lrCutRightClass d default (Classical.choose h)).val
    else default.2.val
  have hchoose (m : BoltzmannSpace ℓ r) (h : P (ι m)) :
      Classical.choose h = m :=
    (hι (Classical.choose_spec h).1).symm
  have hL : L ∘ ι = Subtype.val ∘ lrCutLeftClass d default := by
    funext m
    by_cases hm : xdpLen x m = s
    · have hP : P (ι m) := ⟨m, rfl, hm⟩
      simp only [Function.comp_apply, L, dite_eq_left hP, hchoose m hP]
    · have hP : ¬ P (ι m) := by
        rintro ⟨n, hn, hx⟩
        exact hm ((congrArg (xdpLen x) (hι hn)).trans hx)
      simp only [Function.comp_apply, L, dite_eq_right hP, lrCutLeftClass,
        dite_eq_right hm]
  have hR : R ∘ ι = Subtype.val ∘ lrCutRightClass d default := by
    funext m
    by_cases hm : xdpLen x m = s
    · have hP : P (ι m) := ⟨m, rfl, hm⟩
      simp only [Function.comp_apply, R, dite_eq_left hP, hchoose m hP]
    · have hP : ¬ P (ι m) := by
        rintro ⟨n, hn, hx⟩
        exact hm ((congrArg (xdpLen x) (hι hn)).trans hx)
      simp only [Function.comp_apply, R, dite_eq_right hP, lrCutRightClass,
        dite_eq_right hm]
  have hleft : (Subtype.val ∘ lrCutLeftClass d default) =
      Subtype.val ∘ boltzmannLRLeftCutOutput ℓ s r x (lrClassEquiv d) default := by
    funext m
    by_cases hm : xdpLen x m = s
    · exact congrArg Subtype.val
        (lrCutLeftClass_eq_boltzmannLRLeftCutOutput_on_fiber d default m hm)
    · simp only [Function.comp_apply, lrCutLeftClass, boltzmannLRLeftCutOutput,
        boltzmannLRCutOutputPair, dite_eq_right hm]
  have hright : (Subtype.val ∘ lrCutRightClass d default) =
      Subtype.val ∘ boltzmannLRRightCutOutput ℓ s r x (lrClassEquiv d) default := by
    funext m
    by_cases hm : xdpLen x m = s
    · exact congrArg Subtype.val
        (lrCutRightClass_eq_boltzmannLRRightCutOutput_on_fiber d default m hm)
    · simp only [Function.comp_apply, lrCutRightClass, boltzmannLRRightCutOutput,
        boltzmannLRCutOutputPair, dite_eq_right hm]
  have hred := (lem_lr_ind_reduced d
    (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
    (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2 hF.ne' default).1
  have hvalL : Measurable[⊤] (Subtype.val :
      {mL : BoltzmannSpace ℓ s // IsML x mL} → BoltzmannSpace ℓ s) :=
    measurable_from_top
  have hvalR : Measurable[⊤] (Subtype.val :
      {mR : BoltzmannSpace s r // IsMR x mR} → BoltzmannSpace s r) :=
    measurable_from_top
  have hind : IndepFun (L ∘ ι) (R ∘ ι) ν := by
    rw [hL, hR, hleft, hright]
    exact hred.comp hvalL hvalR
  have hmL : Measurable L := by intro U hU; trivial
  have hmR : Measurable R := by intro U hU; trivial
  have hmι : Measurable ι := by intro U hU; trivial
  have hmap : IndepFun L R (ν.map ι) :=
    (indepFun_map_iff_comp ν hmL hmR hmι).mpr hind
  rw [← stoppedMap_cond_leftLength_xdpFiber_procedureReading x ℓ r s hℓ hr hF]
    at hmap
  exact (indepFun_map_iff_comp _ hmL hmR (measurable_stoppedMap r hr)).mp hmap

end DirectedDistances.PaperProofs.Section4
