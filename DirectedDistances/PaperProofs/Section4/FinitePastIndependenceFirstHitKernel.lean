module

public import DirectedDistances.PaperProofs.Section4.FinitePastIndependenceFirstHit
public import DirectedDistances.PaperProofs.Section4.PastMapFirstHitKernelAS

/-! conditional independence of the past cut outputs at the first hit τ_r given the uncentered
future and the past XDP length; the renewal-time selection T_{m_k}, the T_0 branch and the
infinite-geodesic identification are not treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance {x : XDP} {ell s : ℕ} :
    MeasurableSpace {mL : BoltzmannSpace ell s // IsML x mL} := ⊤
local instance {x : XDP} {s r : ℕ} :
    MeasurableSpace {mR : BoltzmannSpace s r // IsMR x mR} := ⊤

/-- The past map's own XDP length, with value zero at `none`. Helper toward
renewal-time selection T_{m_k}, the T_0 branch and the infinite-geodesic identification
are not treated. -/
@[expose] noncomputable def firstHitPastXdpLength (x : XDP) (r : ℕ) :
    Option (AllBoltzmannSpace r) → ℕ
  | none => 0
  | some m => xdpLen x m.2

/-- Measurability of the past length used toward lem-finite-ind
and the infinite-geodesic identification are not treated. Not the paper result. -/
theorem measurable_firstHitPastXdpLength (x : XDP) (r : ℕ) :
    Measurable (firstHitPastXdpLength x r) := measurable_of_countable _

private theorem firstHitEndpointEvent_measurable (r ell : ℕ) :
    MeasurableSet ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) := by
  have heq : ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) =
      ⋃ k : ℕ, {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hfin, hend⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin.ne
      exact ⟨k, hk.symm, by simpa only [← hk, ENat.toNat_natCast] using hend⟩
    · rintro ⟨k, hk, hend⟩
      exact ⟨hk ▸ ENat.natCast_lt_top k, by simpa only [hk, ENat.toNat_natCast]⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  obtain ⟨S, hS, heq⟩ := MeasurableSpace.measurableSet_comap.mp
    (measurableSet_conditionedVectorPast_firstHit_eq r k)
  rw [← heq]
  exact (hS.preimage (measurable_conditionedVectorPrefix k)).inter
    ((measurable_fst.comp (measurable_pi_apply k)) (measurableSet_singleton _))

private theorem firstHit_map_cond_preimage {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α)
    {f : α → β} (hf : Measurable f) {G : Set β} (hG : MeasurableSet G) :
    (ν[|f ⁻¹' G]).map f = (ν.map f)[|G] := by
  ext T hT
  rw [Measure.map_apply hf hT, cond_apply' (hf hT),
    cond_apply' hT, Measure.map_apply hf hG,
    Measure.map_apply hf (hG.inter hT), Set.preimage_inter]

/-- Product of the normalized ML and MR Boltzmann weights, retaining both map
This formulation also denotes a measure when the selected fiber is null. The renewal-time
selection T_{m_k}, the T_0 branch and the infinite-geodesic identification are not
treated. Not the paper result. -/
@[expose] noncomputable def firstHitPastCutProductLaw (x : XDP) (ell r s : ℕ) :
    Measure (BoltzmannSpace ell s × BoltzmannSpace s r) :=
  ((normalizedWeightLaw (fun a : {mL : BoltzmannSpace ell s // IsML x mL} =>
    boltzmannWeight a.1)).map Subtype.val).prod
  ((normalizedWeightLaw (fun b : {mR : BoltzmannSpace s r // IsMR x mR} =>
    boltzmannWeight b.1)).map Subtype.val)

/-- With positive boundary lengths, the normalized weight product is exactly
the product of the two conditioned Boltzmann laws from lem-lr-ind. Helper toward
renewal-time selection T_{m_k}, the T_0 branch and the infinite-geodesic identification
are not treated. -/
theorem firstHitPastCutProductLaw_eq_boltzmann
    (x : XDP) (ell r s : ℕ) (hell : 1 ≤ ell) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    firstHitPastCutProductLaw x ell r s =
      ((boltzmannLaw ell s
        (boltzmannPartition_ne_zero_and_ne_top ell s hell hs).1
        (boltzmannPartition_ne_zero_and_ne_top ell s hell hs).2)[|{m | IsML x m}]).prod
      ((boltzmannLaw s r
        (boltzmannPartition_ne_zero_and_ne_top s r hs hr).1
        (boltzmannPartition_ne_zero_and_ne_top s r hs hr).2)[|{m | IsMR x m}]) := by
  unfold firstHitPastCutProductLaw
  congr 1
  · exact normalizedWeightLaw_subtype_map_cond {m | IsML x m} boltzmannWeight
      (boltzmannPartition_ne_zero_and_ne_top ell s hell hs).1
      (boltzmannPartition_ne_zero_and_ne_top ell s hell hs).2
  · exact normalizedWeightLaw_subtype_map_cond {m | IsMR x m} boltzmannWeight
      (boltzmannPartition_ne_zero_and_ne_top s r hs hr).1
      (boltzmannPartition_ne_zero_and_ne_top s r hs hr).2

private theorem independent_condDistrib
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (ν : Measure Ω) [IsFiniteMeasure ν] (C : Ω → α) (Y : Ω → β)
    (hC : Measurable C) (hY : Measurable Y) (hI : IndepFun C Y ν) :
    condDistrib C Y ν =ᵐ[ν.map Y] fun _ => ν.map C := by
  exact condDistrib_ae_eq_of_measure_eq_compProd (μ := ν)
    hY.aemeasurable hC.aemeasurable (κ := Kernel.const β (ν.map C)) (by
      rw [Measure.compProd_const]
      exact hI.symm.map_prod_eq_prod_map_map hY.aemeasurable hC.aemeasurable)

private theorem fixedFiber_cut_law
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (default : {mL : BoltzmannSpace ell s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
    0 < μ (E ∩ M ⁻¹' G) →
      (μ[|E ∩ M ⁻¹' G]).map (cuts ∘ M) =
        ((normalizedWeightLaw (fun a : {mL : BoltzmannSpace ell s // IsML x mL} =>
          boltzmannWeight a.1)).map Subtype.val).prod
        ((normalizedWeightLaw (fun b : {mR : BoltzmannSpace s r // IsMR x mR} =>
          boltzmannWeight b.1)).map Subtype.val) := by
  classical
  dsimp only
  intro hGood
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let M : (ℕ → ℤ × ℤ) → Option (AllBoltzmannSpace r) :=
    fun p => stoppedMap r hr (pathCode p)
  let G : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let d := lrCutGlueRepData x ell s r
  let ν := boltzmannLaw ell r
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2
  let σ : BoltzmannSpace ell r → AllBoltzmannSpace r := fun m => ⟨ell, m⟩
  let ι : BoltzmannSpace ell r → Option (AllBoltzmannSpace r) :=
    fun m => some (σ m)
  let fiber := boltzmannFiber (ℓ := ell) (r := r) x s
  let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
  let L : Option (AllBoltzmannSpace r) → BoltzmannSpace ell s :=
    fun o => (cuts o).1
  let R : Option (AllBoltzmannSpace r) → BoltzmannSpace s r :=
    fun o => (cuts o).2
  have hE : MeasurableSet E := firstHitEndpointEvent_measurable r ell
  have hG : MeasurableSet G := trivial
  have hM : Measurable M :=
    (measurable_stoppedMap r hr).comp measurable_pathCode
  have hMpre : MeasurableSet (M ⁻¹' G) := hM hG
  have hEpos : 0 < μ E :=
    lt_of_lt_of_le hGood (measure_mono Set.inter_subset_left)
  have hLaw0 : (μ[|E]).map M = ν.map ι := by
    have hσ : Measurable σ := by intro T hT; trivial
    have hsome : Measurable (some : AllBoltzmannSpace r →
        Option (AllBoltzmannSpace r)) := by intro T hT; trivial
    have hraw : (μ[|E]).map M = (ν.map σ).map some := by
      simpa [μ, τ, E, M, ν, σ] using
        firstHitPastMap_law r ell hr hell hEpos
    rw [Measure.map_map hsome hσ] at hraw
    simpa [Function.comp_def, ι] using hraw
  have hι : Function.Injective ι := by
    intro m n h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
  have hpre : ι ⁻¹' G = fiber := by
    ext m
    change (∃ m' : BoltzmannSpace ell r, ι m = ι m' ∧ xdpLen x m' = s) ↔
      xdpLen x m = s
    constructor
    · rintro ⟨m', hm, hs⟩
      have heq : m = m' := hι hm
      subst m'
      exact hs
    · intro hs
      exact ⟨m, rfl, hs⟩
  have hmapCond : (μ[|E ∩ M ⁻¹' G]).map M = (ν[|fiber]).map ι := by
    rw [← cond_cond_eq_cond_inter hE hMpre μ,
      firstHit_map_cond_preimage _ hM hG, hLaw0]
    have hmapι := firstHit_map_cond_preimage (ν := ν) (f := ι)
      (by intro T hT; trivial) hG
    rw [hpre] at hmapι
    exact hmapι.symm
  have hposCond : 0 < (μ[|E]) (M ⁻¹' G) :=
    cond_pos_of_inter_ne_zero hE hGood.ne'
  have hposFiber : 0 < ν fiber := by
    have h := hposCond
    rw [← Measure.map_apply hM hG, hLaw0,
      Measure.map_apply (by intro T hT; trivial) hG, hpre] at h
    exact h
  let P (o : Option (AllBoltzmannSpace r)) : Prop :=
    ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s
  have hchoose (m : BoltzmannSpace ell r) (h : P (ι m)) :
      Classical.choose h = m := by
    exact (eq_of_heq
      (Sigma.mk.inj_iff.mp (Option.some.inj (Classical.choose_spec h).1)).2).symm
  have hL : (fun m => (cuts (ι m)).1) = Subtype.val ∘ lrCutLeftClass d default := by
    funext m
    by_cases hm : xdpLen x m = s
    · have hp : P (ι m) := ⟨m, rfl, hm⟩
      change (cuts (ι m)).1 =
        (lrCutLeftClass (lrCutGlueRepData x ell s r) default m).val
      simp only [cuts, firstHitFinitePastCutOutputs, ι, P, dite_eq_left hp,
        hchoose m hp]
    · have hp : ¬ P (ι m) := by
        rintro ⟨n, hn, hs⟩
        exact hm ((congrArg (xdpLen x) (hι hn)).trans hs)
      simp only [cuts, firstHitFinitePastCutOutputs, ι, P, dite_eq_right hp]
      simp [d, lrCutLeftClass, hm]
  have hR : (fun m => (cuts (ι m)).2) = Subtype.val ∘ lrCutRightClass d default := by
    funext m
    by_cases hm : xdpLen x m = s
    · have hp : P (ι m) := ⟨m, rfl, hm⟩
      change (cuts (ι m)).2 =
        (lrCutRightClass (lrCutGlueRepData x ell s r) default m).val
      simp only [cuts, firstHitFinitePastCutOutputs, ι, P, dite_eq_left hp,
        hchoose m hp]
    · have hp : ¬ P (ι m) := by
        rintro ⟨n, hn, hs⟩
        exact hm ((congrArg (xdpLen x) (hι hn)).trans hs)
      simp only [cuts, firstHitFinitePastCutOutputs, ι, P, dite_eq_right hp]
      simp [d, lrCutRightClass, hm]
  have hleft : (Subtype.val ∘ lrCutLeftClass d default) =
      Subtype.val ∘ boltzmannLRLeftCutOutput ell s r x (lrClassEquiv d) default := by
    funext m
    by_cases hm : xdpLen x m = s
    · exact congrArg Subtype.val
        (lrCutLeftClass_eq_boltzmannLRLeftCutOutput_on_fiber d default m hm)
    · simp only [Function.comp_apply, lrCutLeftClass, boltzmannLRLeftCutOutput,
        boltzmannLRCutOutputPair, dite_eq_right hm]
  have hright : (Subtype.val ∘ lrCutRightClass d default) =
      Subtype.val ∘ boltzmannLRRightCutOutput ell s r x (lrClassEquiv d) default := by
    funext m
    by_cases hm : xdpLen x m = s
    · exact congrArg Subtype.val
        (lrCutRightClass_eq_boltzmannLRRightCutOutput_on_fiber d default m hm)
    · simp only [Function.comp_apply, lrCutRightClass, boltzmannLRRightCutOutput,
        boltzmannLRCutOutputPair, dite_eq_right hm]
  have hred := lem_lr_ind_reduced d
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2 hposFiber.ne' default
  have hmapL : (μ[|E ∩ M ⁻¹' G]).map (fun p => (cuts (M p)).1) =
      (normalizedWeightLaw (fun a : {mL : BoltzmannSpace ell s // IsML x mL} =>
        boltzmannWeight a.1)).map Subtype.val := by
    change (μ[|E ∩ M ⁻¹' G]).map (L ∘ M) = _
    rw [← Measure.map_map (measurable_of_countable L) hM, hmapCond,
      Measure.map_map (measurable_of_countable L) (measurable_of_countable ι)]
    change (ν[|fiber]).map (fun m => (cuts (ι m)).1) = _
    rw [hL, hleft]
    exact hred.2.1
  have hmapR : (μ[|E ∩ M ⁻¹' G]).map (fun p => (cuts (M p)).2) =
      (normalizedWeightLaw (fun b : {mR : BoltzmannSpace s r // IsMR x mR} =>
        boltzmannWeight b.1)).map Subtype.val := by
    change (μ[|E ∩ M ⁻¹' G]).map (R ∘ M) = _
    rw [← Measure.map_map (measurable_of_countable R) hM, hmapCond,
      Measure.map_map (measurable_of_countable R) (measurable_of_countable ι)]
    change (ν[|fiber]).map (fun m => (cuts (ι m)).2) = _
    rw [hR, hright]
    exact hred.2.2
  have hI := firstHitFinitePastCuts_independent x r ell s hr hell hGood default
  have hCL : Measurable (fun p => (cuts (M p)).1) :=
    (measurable_of_countable L).comp hM
  have hCR : Measurable (fun p => (cuts (M p)).2) :=
    (measurable_of_countable R).comp hM
  have hj := hI.map_prod_eq_prod_map_map hCL.aemeasurable hCR.aemeasurable
  change (μ[|E ∩ M ⁻¹' G]).map (cuts ∘ M) = _ at hj
  rw [hmapL, hmapR] at hj
  exact hj

/-- future/cut law on every fixed endpoint and past-length fiber. Null fibers give zero
on both sides, so no positive-mass premise is imposed. The renewal-time selection
T_{m_k}, the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
theorem firstHitPastCuts_fixedFiber_joint_law
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (default : {mL : BoltzmannSpace ell s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    let ν := μ[|E ∩ M ⁻¹' G]
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let C := firstHitFinitePastCutOutputs x ell r s hell hr default ∘ M
    ν.map (fun p => (Y p, C p)) =
      (ν.map Y).prod (firstHitPastCutProductLaw x ell r s) := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let M := fun p => stoppedMap r hr (pathCode p)
  let G : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let ν := μ[|E ∩ M ⁻¹' G]
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
  let C := cuts ∘ M
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hC : Measurable C := (measurable_of_countable cuts).comp
    ((measurable_stoppedMap r hr).comp measurable_pathCode)
  by_cases hz : μ (E ∩ M ⁻¹' G) = 0
  · have hν : ν = 0 := cond_eq_zero_of_meas_eq_zero hz
    change ν.map (fun p => (Y p, C p)) =
      (ν.map Y).prod (firstHitPastCutProductLaw x ell r s)
    rw [hν]
    simp
  · have hpos : 0 < μ (E ∩ M ⁻¹' G) := bot_lt_iff_ne_bot.mpr hz
    have hI := firstHitFinitePastCuts_independent_future x r ell s hr hell hpos default
    have hLaw : ν.map C = firstHitPastCutProductLaw x ell r s :=
      fixedFiber_cut_law x r ell s hr hell default hpos
    change ν.map (fun p => (Y p, C p)) =
      (ν.map Y).prod (firstHitPastCutProductLaw x ell r s)
    rw [← hLaw]
    exact hI.symm.map_prod_eq_prod_map_map hY.aemeasurable hC.aemeasurable

/-- conditional law of the cut pair given the entire future on each endpoint/length
fiber, including null fibers. The renewal-time selection T_{m_k}, the T_0 branch
and the infinite-geodesic identification are not treated; not the paper result. -/
theorem firstHitPastCuts_fixedFiber_condDistrib
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (default : {mL : BoltzmannSpace ell s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    let : Nonempty (BoltzmannSpace ell s) := ⟨default.1.val⟩
    let : Nonempty (BoltzmannSpace s r) := ⟨default.2.val⟩
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    let ν := μ[|E ∩ M ⁻¹' G]
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let C := firstHitFinitePastCutOutputs x ell r s hell hr default ∘ M
    condDistrib C Y ν =ᵐ[ν.map Y] fun _ => firstHitPastCutProductLaw x ell r s := by
  classical
  dsimp only
  let : Nonempty (BoltzmannSpace ell s) := ⟨default.1.val⟩
  let : Nonempty (BoltzmannSpace s r) := ⟨default.2.val⟩
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let M := fun p => stoppedMap r hr (pathCode p)
  let G : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let ν := μ[|E ∩ M ⁻¹' G]
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
  let C := cuts ∘ M
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hC : Measurable C := (measurable_of_countable cuts).comp
    ((measurable_stoppedMap r hr).comp measurable_pathCode)
  by_cases hz : μ (E ∩ M ⁻¹' G) = 0
  · have hν : ν = 0 := cond_eq_zero_of_meas_eq_zero hz
    change _ =ᵐ[ν.map Y] _
    have hzmap : ν.map Y = 0 := by rw [hν, Measure.map_zero]
    rw [hzmap]
    simp only [ae_zero, Filter.EventuallyEq]
    exact Filter.eventually_bot
  · have hpos : 0 < μ (E ∩ M ⁻¹' G) := bot_lt_iff_ne_bot.mpr hz
    have hI := firstHitFinitePastCuts_independent_future x r ell s hr hell hpos default
    have hk := condDistrib_ae_eq_of_measure_eq_compProd (μ := ν) hY.aemeasurable hC.aemeasurable
      (κ := Kernel.const (ℕ → ℤ × ℤ) (ν.map C)) (by
        rw [Measure.compProd_const]
        exact hI.symm.map_prod_eq_prod_map_map hY.aemeasurable hC.aemeasurable)
    have hLaw : ν.map C = firstHitPastCutProductLaw x ell r s :=
      fixedFiber_cut_law x r ell s hr hell default hpos
    change condDistrib C Y ν =ᵐ[ν.map Y] _
    change condDistrib C Y ν =ᵐ[ν.map Y] fun _ => ν.map C at hk
    rw [hLaw] at hk
    exact hk

/-- independence on every fixed endpoint/length fiber, expressed as equality of whole
conditional measures on one simultaneous a.e. event. Null fibers are included.
The renewal-time selection T_{m_k}, the T_0 branch and the infinite-geodesic
identification are not treated; not the paper result. -/
theorem firstHitPastCuts_fixedFiber_conditionalIndependence
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (default : {mL : BoltzmannSpace ell s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    let : Nonempty (BoltzmannSpace ell s) := ⟨default.1.val⟩
    let : Nonempty (BoltzmannSpace s r) := ⟨default.2.val⟩
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    let ν := μ[|E ∩ M ⁻¹' G]
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let C := firstHitFinitePastCutOutputs x ell r s hell hr default ∘ M
    condDistrib C Y ν =ᵐ[ν.map Y] fun y =>
      (condDistrib (fun p => (C p).1) Y ν y).prod
        (condDistrib (fun p => (C p).2) Y ν y) := by
  classical
  dsimp only
  let : Nonempty (BoltzmannSpace ell s) := ⟨default.1.val⟩
  let : Nonempty (BoltzmannSpace s r) := ⟨default.2.val⟩
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let M := fun p => stoppedMap r hr (pathCode p)
  let G : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let ν := μ[|E ∩ M ⁻¹' G]
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
  let C := cuts ∘ M
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hC : Measurable C := (measurable_of_countable cuts).comp
    ((measurable_stoppedMap r hr).comp measurable_pathCode)
  change condDistrib C Y ν =ᵐ[ν.map Y] fun y =>
    (condDistrib (fun p => (C p).1) Y ν y).prod
      (condDistrib (fun p => (C p).2) Y ν y)
  by_cases hz : μ (E ∩ M ⁻¹' G) = 0
  · have hν : ν = 0 := cond_eq_zero_of_meas_eq_zero hz
    have hzmap : ν.map Y = 0 := by rw [hν, Measure.map_zero]
    rw [hzmap]
    simp only [ae_zero, Filter.EventuallyEq]
    exact Filter.eventually_bot
  · have hpos : 0 < μ (E ∩ M ⁻¹' G) := bot_lt_iff_ne_bot.mpr hz
    have hI : IndepFun C Y ν :=
      firstHitFinitePastCuts_independent_future x r ell s hr hell hpos default
    have hL : IndepFun (fun p => (C p).1) Y ν := by
      simpa only [Function.comp_def, id_eq] using hI.comp measurable_fst measurable_id
    have hR : IndepFun (fun p => (C p).2) Y ν := by
      simpa only [Function.comp_def, id_eq] using hI.comp measurable_snd measurable_id
    have hcuts : IndepFun (fun p => (C p).1) (fun p => (C p).2) ν :=
      firstHitFinitePastCuts_independent x r ell s hr hell hpos default
    have hjoint := hcuts.map_prod_eq_prod_map_map
      hC.fst.aemeasurable hC.snd.aemeasurable
    filter_upwards [independent_condDistrib ν C Y hC hY hI,
      independent_condDistrib ν (fun p => (C p).1) Y hC.fst hY hL,
      independent_condDistrib ν (fun p => (C p).2) Y hC.snd hY hR] with y hy hyl hyr
    rw [hy, hyl, hyr]
    exact hjoint

/-- Discrete measurable structure on the cut-output space used toward lem-finite-ind -/
noncomputable instance firstHitPastLeftCutsMeasurableSpace :
    MeasurableSpace (Option (Σ s : ℕ, AllBoltzmannSpace s)) := ⊤

/-- Actual past cut classes on one common countable carrier, retaining both
boundary lengths in the left output and the shared length in the right output.
selection T_{m_k}, the T_0 branch and the infinite-geodesic identification are not
treated; not the paper result. -/
@[expose] noncomputable def firstHitPastAllCuts (x : XDP) (r : ℕ) :
    Option (AllBoltzmannSpace r) →
      Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r)
  | none => (none, none)
  | some ⟨ell, m⟩ =>
    let s := xdpLen x m
    let c := lrRepresentativeCutPair (lrCutGlueRepData x ell s r) m rfl
    (some ⟨s, ⟨ell, c.1.val⟩⟩, some ⟨s, c.2.val⟩)

/-- Measurability of the common-carrier cuts toward lem-finite-ind
and the infinite-geodesic identification are not treated. Not the paper result. -/
theorem measurable_firstHitPastAllCuts (x : XDP) (r : ℕ) :
    Measurable (firstHitPastAllCuts x r) := measurable_of_countable _

private theorem productLaw_isProbability_of_fiber_pos
    (x : XDP) (ell r s : ℕ) (hell : 1 ≤ ell) (hr : 1 ≤ r)
    (hF : boltzmannLaw ell r
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2
      (boltzmannFiber (ℓ := ell) (r := r) x s) ≠ 0) :
    IsProbabilityMeasure (firstHitPastCutProductLaw x ell r s) := by
  classical
  obtain ⟨m, hm⟩ := nonempty_of_measure_ne_zero hF
  let d := lrCutGlueRepData x ell s r
  let default := lrRepresentativeCutPair d m hm
  have hred := lem_lr_ind_reduced d
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2 hF default
  let ν := (boltzmannLaw ell r
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2)[|
      boltzmannFiber (ℓ := ell) (r := r) x s]
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure hF
  have : IsProbabilityMeasure
      ((normalizedWeightLaw (fun a : {mL : BoltzmannSpace ell s // IsML x mL} =>
        boltzmannWeight a.1)).map Subtype.val) := by
    rw [← hred.2.1]
    change IsProbabilityMeasure (ν.map _)
    infer_instance
  have : IsProbabilityMeasure
      ((normalizedWeightLaw (fun b : {mR : BoltzmannSpace s r // IsMR x mR} =>
        boltzmannWeight b.1)).map Subtype.val) := by
    rw [← hred.2.2]
    change IsProbabilityMeasure (ν.map _)
    infer_instance
  unfold firstHitPastCutProductLaw
  infer_instance

/-- Candidate kernel on the whole `(future, past length)` carrier toward
it is the embedded product of the ML and MR laws. Impossible fibers and nonpositive
left endpoints receive a point mass at the junk pair. The renewal-time selection
T_{m_k}, the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. The global joint-law assembly is a separate obligation. -/
@[expose] noncomputable def firstHitPastCutsKernel (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    Kernel ((ℕ → ℤ × ℤ) × ℕ)
      (Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r)) := by
  classical
  let f : ℤ × ℕ → Measure
      (Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r)) := fun q =>
    if hell : 1 ≤ q.1 then
      if boltzmannLaw q.1.toNat r
          (boltzmannPartition_ne_zero_and_ne_top q.1.toNat r (by omega) hr).1
          (boltzmannPartition_ne_zero_and_ne_top q.1.toNat r (by omega) hr).2
          (boltzmannFiber (ℓ := q.1.toNat) (r := r) x q.2) ≠ 0 then
        (firstHitPastCutProductLaw x q.1.toNat r q.2).map
          (fun c => (some ⟨q.2, ⟨q.1.toNat, c.1⟩⟩, some ⟨q.2, c.2⟩))
      else Measure.dirac (none, none)
    else Measure.dirac (none, none)
  have hobs : Measurable (fun b : (ℕ → ℤ × ℤ) × ℕ => ((b.1 0).1, b.2)) := by
    fun_prop
  exact ⟨fun b => f ((b.1 0).1, b.2), (measurable_of_countable f).comp hobs⟩

instance firstHitPastCutsKernel_isMarkovKernel (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    IsMarkovKernel (firstHitPastCutsKernel x r hr) where
  isProbabilityMeasure b := by
    classical
    dsimp only [firstHitPastCutsKernel, Kernel.coe_mk]
    split
    next hell =>
      split
      next hF =>
        have := productLaw_isProbability_of_fiber_pos x (b.1 0).1.toNat r b.2
          (by omega) hr hF
        infer_instance
      next => infer_instance
    next => infer_instance

private theorem firstHit_cut_fiber_boltz_pos
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    0 < μ (E ∩ M ⁻¹' G) →
      0 < boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2
        (boltzmannFiber (ℓ := ell) (r := r) x s) := by
  classical
  dsimp only
  intro hGood
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let M : (ℕ → ℤ × ℤ) → Option (AllBoltzmannSpace r) :=
    fun p => stoppedMap r hr (pathCode p)
  let G : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let ν := boltzmannLaw ell r
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2
  let σ : BoltzmannSpace ell r → AllBoltzmannSpace r := fun m => ⟨ell, m⟩
  let ι : BoltzmannSpace ell r → Option (AllBoltzmannSpace r) :=
    fun m => some (σ m)
  let fiber := boltzmannFiber (ℓ := ell) (r := r) x s
  have hE : MeasurableSet E := firstHitEndpointEvent_measurable r ell
  have hG : MeasurableSet G := trivial
  have hM : Measurable M :=
    (measurable_stoppedMap r hr).comp measurable_pathCode
  have hMpre : MeasurableSet (M ⁻¹' G) := hM hG
  have hEpos : 0 < μ E :=
    lt_of_lt_of_le hGood (measure_mono Set.inter_subset_left)
  have hLaw0 : (μ[|E]).map M = ν.map ι := by
    have hσ : Measurable σ := by intro T hT; trivial
    have hsome : Measurable (some : AllBoltzmannSpace r →
        Option (AllBoltzmannSpace r)) := by intro T hT; trivial
    have hraw : (μ[|E]).map M = (ν.map σ).map some := by
      simpa [μ, τ, E, M, ν, σ] using
        firstHitPastMap_law r ell hr hell hEpos
    rw [Measure.map_map hsome hσ] at hraw
    simpa [Function.comp_def, ι] using hraw
  have hι : Function.Injective ι := by
    intro m n h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
  have hpre : ι ⁻¹' G = fiber := by
    ext m
    change (∃ m' : BoltzmannSpace ell r, ι m = ι m' ∧ xdpLen x m' = s) ↔
      xdpLen x m = s
    constructor
    · rintro ⟨m', hm, hs⟩
      have heq : m = m' := hι hm
      subst m'
      exact hs
    · intro hs
      exact ⟨m, rfl, hs⟩
  have hposCond : 0 < (μ[|E]) (M ⁻¹' G) :=
    cond_pos_of_inter_ne_zero hE hGood.ne'
  have hposFiber : 0 < ν fiber := by
    have h := hposCond
    rw [← Measure.map_apply hM hG, hLaw0,
      Measure.map_apply (by intro T hT; trivial) hG, hpre] at h
    exact h
  exact hposFiber

private theorem allCuts_eq_fixed_on_fiber
    (x : XDP) (ell r s : ℕ) (hell : 1 ≤ ell) (hr : 1 ≤ r)
    (default : {mL : BoltzmannSpace ell s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR})
    (m : BoltzmannSpace ell r) (hm : xdpLen x m = s) :
    firstHitPastAllCuts x r (some ⟨ell, m⟩) =
      let c := firstHitFinitePastCutOutputs x ell r s hell hr default (some ⟨ell, m⟩)
      (some ⟨s, ⟨ell, c.1⟩⟩, some ⟨s, c.2⟩) := by
  classical
  let P : Prop := ∃ n : BoltzmannSpace ell r,
    (some (⟨ell, m⟩ : AllBoltzmannSpace r)) = some ⟨ell, n⟩ ∧ xdpLen x n = s
  have hp : P := ⟨m, rfl, hm⟩
  have hc : Classical.choose hp = m := by
    exact (eq_of_heq
      (Sigma.mk.inj_iff.mp (Option.some.inj (Classical.choose_spec hp).1)).2).symm
  have he : firstHitFinitePastCutOutputs x ell r s hell hr default
      (some ⟨ell, m⟩) =
      ((lrCutLeftClass (lrCutGlueRepData x ell s r) default m).val,
        (lrCutRightClass (lrCutGlueRepData x ell s r) default m).val) := by
    unfold firstHitFinitePastCutOutputs
    unfold AllBoltzmannSpace at *
    rw [dite_eq_left hp, hc]
  rw [he]
  simp only [lrCutLeftClass, lrCutRightClass, dite_eq_left hm]
  subst s
  rfl

/-- carrier and global product kernel give the joint law on each endpoint/length
fiber, including null fibers. Conditioning uses the future and the past map's
own length. The renewal-time selection T_{m_k}, the T_0 branch and the
infinite-geodesic identification are not treated; not the paper result. -/
theorem firstHitPastAllCuts_fixedFiber_joint_kernel_law
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    let ν := μ[|E ∩ M ⁻¹' G]
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    ν.map (fun p => (B p, C p)) = ν.map B ⊗ₘ firstHitPastCutsKernel x r hr := by
  classical
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let M := fun p => stoppedMap r hr (pathCode p)
  let G : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let ν := μ[|E ∩ M ⁻¹' G]
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let C := firstHitPastAllCuts x r ∘ M
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hB : Measurable B := hY.prodMk ((measurable_firstHitPastXdpLength x r).comp hM)
  have hC : Measurable C := (measurable_firstHitPastAllCuts x r).comp hM
  change ν.map (fun p => (B p, C p)) = ν.map B ⊗ₘ firstHitPastCutsKernel x r hr
  by_cases hz : μ (E ∩ M ⁻¹' G) = 0
  · have hν : ν = 0 := cond_eq_zero_of_meas_eq_zero hz
    rw [hν]
    simp
  · have hpos : 0 < μ (E ∩ M ⁻¹' G) := bot_lt_iff_ne_bot.mpr hz
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hz
    obtain ⟨m, _, hm⟩ := hp.2
    let default := lrRepresentativeCutPair (lrCutGlueRepData x ell s r) m hm
    let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
    let D := cuts ∘ M
    let emb : BoltzmannSpace ell s × BoltzmannSpace s r →
        Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r) :=
      fun c => (some ⟨s, ⟨ell, c.1⟩⟩, some ⟨s, c.2⟩)
    have hEmb : Measurable emb := measurable_of_countable _
    have hD : Measurable D := (measurable_of_countable cuts).comp hM
    have hH : MeasurableSet (E ∩ M ⁻¹' G) :=
      (firstHitEndpointEvent_measurable r ell).inter (hM (show MeasurableSet G from trivial))
    have hSC : ∀ᵐ p ∂ν, firstHitPastXdpLength x r (M p) = s := by
      filter_upwards [ae_cond_mem hH] with p hp
      obtain ⟨m, he, hs⟩ := hp.2
      simp only [he, firstHitPastXdpLength, hs]
    have hBC : B =ᵐ[ν] fun p => (Y p, s) := by
      filter_upwards [hSC] with p hp
      exact Prod.ext rfl hp
    have hCD : C =ᵐ[ν] emb ∘ D := by
      filter_upwards [ae_cond_mem hH] with p hp
      obtain ⟨m, he, hs⟩ := hp.2
      change firstHitPastAllCuts x r (M p) = emb (cuts (M p))
      rw [he]
      exact allCuts_eq_fixed_on_fiber x ell r s hell hr default m hs
    have hI : IndepFun C B ν := by
      have hi : IndepFun D Y ν :=
        firstHitFinitePastCuts_independent_future x r ell s hr hell hpos default
      exact (hi.comp hEmb (show Measurable (fun y : ℕ → ℤ × ℤ => (y, s)) by
        fun_prop)).congr hCD.symm hBC.symm
    have hLaw : ν.map C = (firstHitPastCutProductLaw x ell r s).map emb := by
      rw [Measure.map_congr hCD, ← Measure.map_map hEmb hD]
      rw [show ν.map D = firstHitPastCutProductLaw x ell r s from
        fixedFiber_cut_law x r ell s hr hell default hpos]
    have hF := firstHit_cut_fiber_boltz_pos x r ell s hr hell hpos
    have : IsProbabilityMeasure (firstHitPastCutProductLaw x ell r s) :=
      productLaw_isProbability_of_fiber_pos x ell r s hell hr hF.ne'
    have hindex : ∀ᵐ b ∂ν.map B, (b.1 0).1 = (ell : ℤ) ∧ b.2 = s := by
      apply (ae_map_iff hB.aemeasurable (by measurability)).2
      filter_upwards [ae_cond_mem hH, hSC] with p hp hs
      exact ⟨by simpa only [Y, B, conditionedVectorShift, Nat.add_zero,
        Set.mem_ofPred_eq] using hp.1.2, hs⟩
    have hk : firstHitPastCutsKernel x r hr =ᵐ[ν.map B]
        Kernel.const ((ℕ → ℤ × ℤ) × ℕ) ((firstHitPastCutProductLaw x ell r s).map emb) := by
      filter_upwards [hindex] with b hb
      let f : ℤ × ℕ → Measure
          (Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r)) :=
        fun q => firstHitPastCutsKernel x r hr ((fun _ => (q.1, 0)), q.2)
      change f ((b.1 0).1, b.2) = (firstHitPastCutProductLaw x ell r s).map emb
      rw [show ((b.1 0).1, b.2) = ((ell : ℤ), s) from Prod.ext hb.1 hb.2]
      dsimp only [f, firstHitPastCutsKernel, Kernel.coe_mk]
      rw [dite_eq_left (by exact_mod_cast hell)]
      simp only [Int.toNat_natCast]
      rw [ite_eq_left hF.ne']
    calc
      ν.map (fun p => (B p, C p)) = (ν.map B).prod (ν.map C) :=
        hI.symm.map_prod_eq_prod_map_map hB.aemeasurable hC.aemeasurable
      _ = (ν.map B).prod ((firstHitPastCutProductLaw x ell r s).map emb) := by rw [hLaw]
      _ = ν.map B ⊗ₘ firstHitPastCutsKernel x r hr := by
        rw [Measure.compProd_congr hk, Measure.compProd_const]

/-- assembly of all positive-endpoint and past-length fibers, on their measurable
union. Removal of this restriction requires a full-mass support proof. The
renewal-time selection T_{m_k}, the T_0 branch and the infinite-geodesic
identification are not treated; not the paper result. -/
theorem firstHitPastAllCuts_supported_joint_kernel_law
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let H := fun i : ℕ × ℕ =>
      ({p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = ((i.1 + 1 : ℕ) : ℤ)}) ∩
        M ⁻¹' {o | ∃ m : BoltzmannSpace (i.1 + 1) r,
          o = some (⟨i.1 + 1, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = i.2}
    let ν := μ.restrict (⋃ i, H i)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    ν.map (fun p => (B p, C p)) = ν.map B ⊗ₘ firstHitPastCutsKernel x r hr := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let H := fun i : ℕ × ℕ =>
    ({p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = ((i.1 + 1 : ℕ) : ℤ)}) ∩
      M ⁻¹' {o | ∃ m : BoltzmannSpace (i.1 + 1) r,
        o = some (⟨i.1 + 1, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = i.2}
  let ν := μ.restrict (⋃ i, H i)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let C := firstHitPastAllCuts x r ∘ M
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hB : Measurable B := hY.prodMk ((measurable_firstHitPastXdpLength x r).comp hM)
  have hC : Measurable C := (measurable_firstHitPastAllCuts x r).comp hM
  have hH (i : ℕ × ℕ) : MeasurableSet (H i) :=
    (firstHitEndpointEvent_measurable r (i.1 + 1)).inter
      (hM (show MeasurableSet _ from trivial))
  have hdisj : Pairwise (fun i j => Disjoint (H i) (H j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    have hiS : firstHitPastXdpLength x r (M p) = i.2 := by
      obtain ⟨m, he, hs⟩ := hi.2
      simp only [he, firstHitPastXdpLength, hs]
    have hjS : firstHitPastXdpLength x r (M p) = j.2 := by
      obtain ⟨m, he, hs⟩ := hj.2
      simp only [he, firstHitPastXdpLength, hs]
    have hℓ := hi.1.2.symm.trans hj.1.2
    apply hij
    apply Prod.ext
    · omega
    · exact hiS.symm.trans hjS
  have hsum : ν = Measure.sum (fun i => μ.restrict (H i)) :=
    Measure.restrict_iUnion hdisj hH
  have hfiber (i : ℕ × ℕ) :
      (μ.restrict (H i)).map (fun p => (B p, C p)) =
        (μ.restrict (H i)).map B ⊗ₘ firstHitPastCutsKernel x r hr := by
    by_cases hz : μ (H i) = 0
    · rw [Measure.restrict_eq_zero.mpr hz]
      simp
    · have hpos : 0 < μ (H i) := bot_lt_iff_ne_bot.mpr hz
      have he : μ.restrict (H i) = μ (H i) • μ[|H i] := by
        rw [ProbabilityTheory.cond, smul_smul,
          ENNReal.mul_inv_cancel hz (measure_ne_top _ _), one_smul]
      rw [he, Measure.map_smul _ (hB.prodMk hC).aemeasurable,
        Measure.map_smul _ hB.aemeasurable, Measure.compProd_smul_left]
      exact congrArg (fun ρ => μ (H i) • ρ)
        (firstHitPastAllCuts_fixedFiber_joint_kernel_law x r (i.1 + 1) i.2 hr (by omega))
  change ν.map (fun p => (B p, C p)) = ν.map B ⊗ₘ firstHitPastCutsKernel x r hr
  calc
    ν.map (fun p => (B p, C p)) =
        Measure.sum (fun i => (μ.restrict (H i)).map (fun p => (B p, C p))) := by
      conv_lhs => rw [hsum]
      exact Measure.map_sum (hB.prodMk hC).aemeasurable
    _ = Measure.sum (fun i => (μ.restrict (H i)).map B ⊗ₘ
        firstHitPastCutsKernel x r hr) := congrArg Measure.sum (funext hfiber)
    _ = ν.map B ⊗ₘ firstHitPastCutsKernel x r hr := by
      rw [← Measure.compProd_sum_left, ← Measure.map_sum hB.aemeasurable, ← hsum]





theorem firstHitPastAllCuts_supported_condDistrib
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let H := fun i : ℕ × ℕ =>
      ({p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = ((i.1 + 1 : ℕ) : ℤ)}) ∩
        M ⁻¹' {o | ∃ m : BoltzmannSpace (i.1 + 1) r,
          o = some (⟨i.1 + 1, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = i.2}
    let ν := μ.restrict (⋃ i, H i)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    condDistrib C B ν =ᵐ[ν.map B] firstHitPastCutsKernel x r hr := by
  dsimp only
  apply condDistrib_ae_eq_of_measure_eq_compProd
    ((measurable_conditionedFirstHit_future r).prodMk
      ((measurable_firstHitPastXdpLength x r).comp
        ((measurable_stoppedMap r hr).comp measurable_pathCode))).aemeasurable
    (((measurable_firstHitPastAllCuts x r).comp
      ((measurable_stoppedMap r hr).comp measurable_pathCode)).aemeasurable)
  exact firstHitPastAllCuts_supported_joint_kernel_law x r hr

/-- of the conditional independence of the past cut outputs at the first hit τ_r given
the uncentered future and the past XDP length; the renewal-time selection T_{m_k},
the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
private theorem stoppedMap_endpoint_of_legal (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) (h0 : p 0 = (0, 0))
    (hstep : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hnonneg : ∀ n, 0 ≤ (p n).1)
    (hfin : conditionedSecondCoordinateFirstHit r p < ⊤) :
    ∃ m : BoltzmannSpace (p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat r,
      stoppedMap r hr (pathCode p) = some ⟨_, m⟩ := by
  classical
  have hw : codeWalk (pathCode p) = p := by
    funext n
    rw [codeWalk_pathCode p hstep n, h0]
    exact sub_zero _
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hn
    simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hn] at hfin
    exact (lt_irrefl _ hfin)
  have ht : boltzmannTau r (pathCode p) =
      (conditionedSecondCoordinateFirstHit r p).toNat := by
    simp only [boltzmannTau, hw, conditionedSecondCoordinateFirstHit,
      dite_eq_left hh, ENat.toNat_natCast]
  have hE : pathCode p ∈ boltzmannEvent r := by
    refine ⟨Nat.find hh, ?_, fun n _ => ?_⟩
    · rw [hw]
      exact Nat.find_spec hh
    · rw [hw]
      exact hnonneg n
  have hL : L (boltzmannKMSWStream (pathCode p)) (boltzmannTau r (pathCode p)) =
      (p (conditionedSecondCoordinateFirstHit r p).toNat).1 := by
    calc
      _ = (codeWalk (pathCode p) (boltzmannTau r (pathCode p))).1 := by
        rw [kmsw_L_eq, codeWalk_eq_integrateCodes]
        rfl
      _ = _ := by rw [hw, ht]
  let j : StoppedWalkIndex r := ⟨boltzmannTau r (pathCode p),
    ⟨(L (boltzmannKMSWStream (pathCode p)) (boltzmannTau r (pathCode p))).toNat,
      ⟨stoppedWord r (pathCode p), (stoppedWord_admissible r hr _ hE).1⟩⟩⟩
  have hj : 1 ≤ j.1 := (boltzmann_boundary_observable r hr _ hE).1
  have hi : stoppedIndex r hr (pathCode p) = some j := by
    simp only [stoppedIndex, dite_eq_left hE, j]
  have hm : stoppedMap r hr (pathCode p) = some (stoppedWalkMap ⟨j, hj⟩) := by
    rw [stoppedMap, hi]
    change stoppedWalkMapOption r j = _
    simp only [stoppedWalkMapOption, dite_eq_left hj]
  have hell : (stoppedWalkMap ⟨j, hj⟩).1 =
      (p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat := by
    change (L _ _).toNat = _
    rw [hL]
  generalize hq : stoppedWalkMap ⟨j, hj⟩ = q at hell hm
  rcases q with ⟨ell, m⟩
  change ell = _ at hell
  subst ell
  exact ⟨m, hm⟩

/-- of the conditional independence of the past cut outputs at the first hit τ_r given
the uncentered future and the past XDP length; the renewal-time selection T_{m_k},
the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
theorem firstHitPastAllCuts_restrict_support (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let H := fun i : ℕ × ℕ =>
      ({p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = ((i.1 + 1 : ℕ) : ℤ)}) ∩
        M ⁻¹' {o | ∃ m : BoltzmannSpace (i.1 + 1) r,
          o = some (⟨i.1 + 1, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = i.2}
    μ.restrict (⋃ i, H i) = μ := by
  dsimp only
  apply Measure.restrict_eq_self_of_ae_mem
  have hpos := firstHitPastMap_left_pos_ae r hr
  dsimp only at hpos
  rw [firstHitPastMap_cond_finite_hit_eq r hr] at hpos
  have hnonneg : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∀ n, 0 ≤ (p n).1 := by
    unfold conditionedVectorPathLaw
    apply ae_map_iff (by fun_prop) (by measurability) |>.2
    exact Filter.Eventually.of_forall fun p n => Int.natCast_nonneg _
  filter_upwards [firstHitPastMap_finite_hit_ae r hr, hpos,
    conditionedVectorPathLaw_ae_legal, hnonneg] with p hfin hp hlegal hn
  obtain ⟨m, hm⟩ := stoppedMap_endpoint_of_legal r hr p hlegal.1 hlegal.2 hn hfin
  let ell := (p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat
  have hell : ell - 1 + 1 = ell := by dsimp only [ell]; omega
  apply Set.mem_iUnion.mpr
  refine ⟨(ell - 1, xdpLen x m), ?_⟩
  change (_ ∧ _) ∧ ∃ m' : BoltzmannSpace (ell - 1 + 1) r,
    stoppedMap r hr (pathCode p) = some ⟨ell - 1 + 1, m'⟩ ∧ _
  rw [hell]
  refine ⟨⟨hfin, ?_⟩, m, hm, rfl⟩
  dsimp only [ell]
  exact (Int.toNat_of_nonneg (by omega)).symm

/-- of the conditional independence of the past cut outputs at the first hit τ_r given
the uncentered future and the past XDP length; the renewal-time selection T_{m_k},
the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
theorem firstHitPastAllCuts_joint_kernel_law (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    μ.map (fun p => (B p, C p)) = μ.map B ⊗ₘ firstHitPastCutsKernel x r hr := by
  have h := firstHitPastAllCuts_supported_joint_kernel_law x r hr
  dsimp only at h ⊢
  rwa [firstHitPastAllCuts_restrict_support x r hr] at h

/-- of the conditional independence of the past cut outputs at the first hit τ_r given
the uncentered future and the past XDP length; the renewal-time selection T_{m_k},
the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
theorem firstHitPastAllCuts_condDistrib (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    condDistrib C B μ =ᵐ[μ.map B] firstHitPastCutsKernel x r hr := by
  apply condDistrib_ae_eq_of_measure_eq_compProd
    ((measurable_conditionedFirstHit_future r).prodMk
      ((measurable_firstHitPastXdpLength x r).comp
        ((measurable_stoppedMap r hr).comp measurable_pathCode))).aemeasurable
    (((measurable_firstHitPastAllCuts x r).comp
      ((measurable_stoppedMap r hr).comp measurable_pathCode)).aemeasurable)
  exact firstHitPastAllCuts_joint_kernel_law x r hr

/-- of the conditional independence of the past cut outputs at the first hit τ_r given
the uncentered future and the past XDP length; the renewal-time selection T_{m_k},
the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
private theorem cutProductLaw_map_eq_prod_marginals
    (x : XDP) (ell r s : ℕ) (hell : 1 ≤ ell) (hr : 1 ≤ r)
    (hF : boltzmannLaw ell r
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2
      (boltzmannFiber (ℓ := ell) (r := r) x s) ≠ 0) :
    let emb : BoltzmannSpace ell s × BoltzmannSpace s r →
        Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r) :=
      fun c => (some ⟨s, ⟨ell, c.1⟩⟩, some ⟨s, c.2⟩)
    let ν := (firstHitPastCutProductLaw x ell r s).map emb
    ν = (ν.map Prod.fst).prod (ν.map Prod.snd) := by
  classical
  obtain ⟨m, hm⟩ := nonempty_of_measure_ne_zero hF
  let d := lrCutGlueRepData x ell s r
  let default := lrRepresentativeCutPair d m hm
  have hred := lem_lr_ind_reduced d
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2 hF default
  let ρ := (boltzmannLaw ell r
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2)[|
      boltzmannFiber (ℓ := ell) (r := r) x s]
  have : IsProbabilityMeasure ρ := cond_isProbabilityMeasure hF
  let μL := (normalizedWeightLaw
    (fun a : {mL : BoltzmannSpace ell s // IsML x mL} => boltzmannWeight a.1)).map
      Subtype.val
  let μR := (normalizedWeightLaw
    (fun b : {mR : BoltzmannSpace s r // IsMR x mR} => boltzmannWeight b.1)).map
      Subtype.val
  have : IsProbabilityMeasure μL := by
    dsimp only [μL]
    rw [← hred.2.1]
    change IsProbabilityMeasure (ρ.map _)
    infer_instance
  have : IsProbabilityMeasure μR := by
    dsimp only [μR]
    rw [← hred.2.2]
    change IsProbabilityMeasure (ρ.map _)
    infer_instance
  let f : BoltzmannSpace ell s → Option (Σ s : ℕ, AllBoltzmannSpace s) :=
    fun a => some ⟨s, ⟨ell, a⟩⟩
  let g : BoltzmannSpace s r → Option (AllBoltzmannSpace r) :=
    fun b => some ⟨s, b⟩
  let emb := Prod.map f g
  have hf : Measurable f := measurable_of_countable _
  have hg : Measurable g := measurable_of_countable _
  have hemb : Measurable emb := hf.prodMap hg
  change (μL.prod μR).map emb =
    (((μL.prod μR).map emb).map Prod.fst).prod
      (((μL.prod μR).map emb).map Prod.snd)
  rw [Measure.map_map measurable_fst hemb, Measure.map_map measurable_snd hemb]
  exact (indepFun_prod (μ := μL) (ν := μR) hf hg).map_prod_eq_prod_map_map
    (hf.comp measurable_fst).aemeasurable (hg.comp measurable_snd).aemeasurable

/-- of the conditional independence of the past cut outputs at the first hit τ_r given
the uncentered future and the past XDP length; the renewal-time selection T_{m_k},
the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
private theorem firstHitPastCutsKernel_eq_prod_marginals
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) (b : (ℕ → ℤ × ℤ) × ℕ) :
    firstHitPastCutsKernel x r hr b =
      ((firstHitPastCutsKernel x r hr b).map Prod.fst).prod
        ((firstHitPastCutsKernel x r hr b).map Prod.snd) := by
  classical
  dsimp only [firstHitPastCutsKernel, Kernel.coe_mk]
  split
  next hell =>
    split
    next hF =>
      exact cutProductLaw_map_eq_prod_marginals x (b.1 0).1.toNat r b.2
        (by omega) hr hF
    next =>
      simp only [Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_snd,
        Measure.dirac_prod_dirac]
  next =>
    simp only [Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_snd,
      Measure.dirac_prod_dirac]

/-- of the conditional independence of the past cut outputs at the first hit τ_r given
the uncentered future and the past XDP length; the renewal-time selection T_{m_k},
the T_0 branch and the infinite-geodesic identification are not treated;
not the paper result. -/
theorem firstHitPastAllCuts_conditionalIndependence (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    condDistrib C B μ =ᵐ[μ.map B] fun b =>
      (condDistrib (fun p => (C p).1) B μ b).prod
        (condDistrib (fun p => (C p).2) B μ b) := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let C := firstHitPastAllCuts x r ∘ M
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hB : Measurable B := (measurable_conditionedFirstHit_future r).prodMk
    ((measurable_firstHitPastXdpLength x r).comp hM)
  have hC : Measurable C := (measurable_firstHitPastAllCuts x r).comp hM
  have hK : condDistrib C B μ =ᵐ[μ.map B] firstHitPastCutsKernel x r hr :=
    firstHitPastAllCuts_condDistrib x r hr
  have hL := condDistrib_comp (μ := μ) hB.aemeasurable hC.aemeasurable measurable_fst
  have hR := condDistrib_comp (μ := μ) hB.aemeasurable hC.aemeasurable measurable_snd
  change condDistrib C B μ =ᵐ[μ.map B] fun b =>
    (condDistrib (fun p => (C p).1) B μ b).prod
      (condDistrib (fun p => (C p).2) B μ b)
  filter_upwards [hK, hL, hR] with b hk hl hright
  simp only [Function.comp_def] at hl hright
  rw [hl, hright, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd, hk]
  exact firstHitPastCutsKernel_eq_prod_marginals x r hr b

end DirectedDistances.PaperProofs.Section4
