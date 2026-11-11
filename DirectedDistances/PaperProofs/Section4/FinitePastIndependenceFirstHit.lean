/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.FinitePastIndependence
public import DirectedDistances.RandomWalk.ConditionedFirstHitPastCodeLaw
public import DirectedDistances.RandomWalk.ConditionedFirstHitEndpointIndependence
public import DirectedDistances.PaperProofs.Section4.PastMapPathDecoding
public import DirectedDistances.PaperProofs.Section4.PastMapFirstHitLaw

/-! independence of the finite past cut outputs at the first hit τ_r given the endpoint
and the XDP length, and their independence from the uncentered future; the renewal-time
selection T_{m_k}, the T_0 branch and the infinite-geodesic identification are not
treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Classical MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open scoped ENNReal

/-- The path restriction used for finite past cuts toward lem-finite-ind -/
@[expose]
def firstHitPrefixLegal (r : ℕ) (p : ℕ → ℤ × ℤ) : Prop :=
  p 0 = (0, 0) ∧ ∀ n < (conditionedSecondCoordinateFirstHit r p).toNat,
    p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep

/-- Cut outputs extracted from the first-hit stopped map toward lem-finite-ind -/
@[expose]
noncomputable def firstHitFinitePastCutOutputs
    (x : XDP) (ell r s : ℕ) (_hℓ : 1 ≤ ell) (_hr : 1 ≤ r)
    (default : {mL : BoltzmannSpace ell s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR})
    (o : Option (AllBoltzmannSpace r)) : BoltzmannSpace ell s × BoltzmannSpace s r := by
  classical
  exact if h : ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s then
    ((lrCutLeftClass (lrCutGlueRepData x ell s r) default (Classical.choose h)).val,
      (lrCutRightClass (lrCutGlueRepData x ell s r) default (Classical.choose h)).val)
  else (default.1.val, default.2.val)

private theorem measurableSet_firstHit_cut_slice
    (r : ℕ) (hr : 1 ≤ r) (ell k : ℕ)
    {β : Type*} (f : Option (AllBoltzmannSpace r) → β)
    (d : β) (g : (ℕ → ℤ × ℤ) → β)
    (hg : ∀ p, g p = if _h : firstHitPrefixLegal r p then
      f (stoppedMap r hr (pathCode p)) else d) :
    (T : Set β) → MeasurableSet[conditionedVectorPast k]
      (g ⁻¹' T ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  intro T
  classical
  let Hit : Set (ℕ → ℤ × ℤ) :=
    {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}
  let End : Set (ℕ → ℤ × ℤ) := {p | (p k).1 = (ell : ℤ)}
  let Slice := Hit ∩ End
  let Legal : Set (ℕ → ℤ × ℤ) := {p | firstHitPrefixLegal r p}
  let CutLegal : Set (ℕ → ℤ × ℤ) :=
    {p | f (stoppedMap r hr (pathCode p)) ∈ T ∧ firstHitPrefixLegal r p} ∩ Slice
  let LegalSlice := Legal ∩ Slice
  have hhit : MeasurableSet[conditionedVectorPast k] Hit :=
    measurableSet_conditionedVectorPast_firstHit_eq r k
  have hend : MeasurableSet[conditionedVectorPast k] End := by
    refine ⟨{q : Fin (k + 1) → ℤ × ℤ | (q (Fin.last k)).1 = (ell : ℤ)},
      (Set.to_countable _).measurableSet, ?_⟩
    rfl
  have hslice : MeasurableSet[conditionedVectorPast k] Slice := hhit.inter hend
  have hcut : MeasurableSet[conditionedVectorPast k] CutLegal := by
    have h := measurableSet_stoppedMap_pathCode_firstHit_legal r hr
      (f ⁻¹' T) k ell
    convert h using 1
    ext p
    simp only [CutLegal, Slice, Hit, End, firstHitPrefixLegal,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    tauto
  have hlegal : MeasurableSet[conditionedVectorPast k] LegalSlice := by
    have h := measurableSet_stoppedMap_pathCode_firstHit_legal r hr Set.univ k ell
    convert h using 1
    ext p
    simp only [LegalSlice, Legal, Slice, Hit, End, firstHitPrefixLegal,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ]
    tauto
  have heq : g ⁻¹' T ∩ Hit ∩ End =
      if d ∈ T then (Slice \ LegalSlice) ∪ CutLegal else CutLegal := by
    classical
    ext p
    by_cases hp : firstHitPrefixLegal r p
    · by_cases hd : d ∈ T
      · simp_all [CutLegal, Legal, Slice, Hit, End, LegalSlice, and_assoc]
      · simp_all [CutLegal, Legal, Slice, Hit, End, LegalSlice, and_assoc]
    · by_cases hd : d ∈ T
      · simp_all [CutLegal, Legal, Slice, Hit, End, LegalSlice]
      · simp_all [CutLegal, Legal, Slice, Hit, End, LegalSlice]
  rw [heq]
  by_cases hd : d ∈ T
  · simpa [hd] using (hslice.diff hlegal).union hcut
  · simpa [hd] using hcut

private theorem firstHit_past_slice_prefix
    (r k : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[conditionedVectorPast k]
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)})) :
    ∃ S : Set (Fin (k + 1) → ℤ × ℤ), MeasurableSet S ∧
      A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
        conditionedVectorPrefix k ⁻¹' S := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  exact ⟨S, hS, hpre.symm⟩

/-- The endpoint fiber mass bridge used to turn positive conditioned path mass -/
theorem firstHitEndpointCodeMass (r ell : ℕ) :
    conditionedVectorPathLaw 0 0
        ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
          {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) =
      (ell + 1 : ℝ≥0∞) * iidCodeMeasure
        (boltzmannEvent r ∩
          {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}) := by
  classical
  have hA (k : ℕ) : MeasurableSet[conditionedVectorPast k]
      (Set.univ ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}) := by
    simpa only [Set.univ_inter] using
      (measurableSet_conditionedVectorPast_firstHit_eq r k)
  let S : ∀ k : ℕ, Set (Fin (k + 1) → ℤ × ℤ) := fun k =>
    Classical.choose (firstHit_past_slice_prefix r k Set.univ (hA k))
  have hS (k : ℕ) : MeasurableSet (S k) ∧
      Set.univ ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
        conditionedVectorPrefix k ⁻¹' S k :=
    Classical.choose_spec (firstHit_past_slice_prefix r k Set.univ (hA k))
  simpa [Set.univ_inter] using
    conditionedVectorPathLaw_zero_zero_firstHit_bridge r ell Set.univ S
      (fun k => (hS k).2)

/-- Positive mass of the path endpoint event implies positive mass of its -/
theorem firstHitEndpointCodeMass_pos (r ell : ℕ)
    (hE : 0 < conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)})) :
    0 < iidCodeMeasure
      (boltzmannEvent r ∩
        {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}) := by
  have hm := firstHitEndpointCodeMass r ell
  by_contra hpos
  have hz : iidCodeMeasure
      (boltzmannEvent r ∩
        {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}) = 0 :=
    le_antisymm (not_lt.mp hpos) bot_le
  have hzero : conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) = 0 := by
    rw [hm, hz]
    simp
  exact (ne_of_gt hE) hzero

/-- First-hit event bridge for a stopped-past event measurable on every finite -/
theorem firstHitConditionedCodeEventBridge
    (r ell : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}))
    (hE : 0 < conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)})) :
    (conditionedVectorPathLaw 0 0)[A |
      {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}] =
      iidCodeMeasure[(fun ω n => codeWalk ω n) ⁻¹' A |
        boltzmannEvent r ∩
          {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}] := by
  classical
  let S : ∀ k : ℕ, Set (Fin (k + 1) → ℤ × ℤ) := fun k =>
    Classical.choose (firstHit_past_slice_prefix r k A (hA k))
  have hS (k : ℕ) : MeasurableSet (S k) ∧
      A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
        conditionedVectorPrefix k ⁻¹' S k :=
    Classical.choose_spec (firstHit_past_slice_prefix r k A (hA k))
  have hpos := firstHitEndpointCodeMass_pos r ell hE
  exact conditionedVectorPathLaw_zero_zero_firstHit_conditional
    r ell A S (fun k => (hS k).2) hpos

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

private theorem firstHit_indepFun_map_iff_comp {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (ν : Measure α) {f : β → γ} {g : β → δ} {k : α → β}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    IndepFun f g (ν.map k) ↔ IndepFun (f ∘ k) (g ∘ k) ν := by
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

private theorem firstHit_indepFun_comp_cond_preimage
    {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure Ω)
    (X : Ω → α) (Y : Ω → β) (f : α → γ) (G : Set α)
    (hX : Measurable X) (hf : Measurable f)
    (hI : IndepFun X Y ν) (hG : MeasurableSet G)
    (hpos : 0 < ν (X ⁻¹' G)) (hStop : ν (X ⁻¹' G) ≠ ⊤) :
    IndepFun (f ∘ X) Y (ν[|X ⁻¹' G]) := by
  have hS : MeasurableSet (X ⁻¹' G) := hX hG
  have hS0 : ν (X ⁻¹' G) ≠ 0 := hpos.ne'
  let d := ν (X ⁻¹' G)
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro U V hU hV
  have hjoint := hI.measure_inter_preimage_eq_mul
    (G ∩ f ⁻¹' U) V (hG.inter (hf hU)) hV
  have hright := hI.measure_inter_preimage_eq_mul G V hG hV
  have hsetJoint : X ⁻¹' G ∩ ((f ∘ X) ⁻¹' U ∩ Y ⁻¹' V) =
      (X ⁻¹' (G ∩ f ⁻¹' U)) ∩ Y ⁻¹' V := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
    tauto
  have hsetLeft : X ⁻¹' G ∩ (f ∘ X) ⁻¹' U = X ⁻¹' (G ∩ f ⁻¹' U) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
  rw [cond_apply hS, cond_apply hS, cond_apply hS,
    hsetJoint, hsetLeft, hjoint, hright]
  have halg (a b : ℝ≥0∞) :
      d⁻¹ * (a * b) = (d⁻¹ * a) * (d⁻¹ * (d * b)) := by
    calc
      d⁻¹ * (a * b) = (d⁻¹ * a) * b := by rw [← mul_assoc]
      _ = (d⁻¹ * a) * (d⁻¹ * (d * b)) := by
        congr 1
        calc
          b = (d⁻¹ * d) * b := by
            rw [ENNReal.inv_mul_cancel hS0 hStop, one_mul]
          _ = d⁻¹ * (d * b) := by rw [mul_assoc]
  rw [halg]

/-- conditional independence of the finite first-hit past cut outputs given the endpoint
and XDP length. This does not treat the renewal-time selection, the T_0 branch, or
the infinite-geodesic identification; not the paper result. -/
theorem firstHitFinitePastCuts_independent
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    0 < μ (E ∩ M ⁻¹' G) →
      ∀ default : {mL : BoltzmannSpace ell s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR},
        let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
        IndepFun (fun p => (cuts (M p)).1) (fun p => (cuts (M p)).2)
          (μ[|E ∩ M ⁻¹' G]) := by
  dsimp only
  intro hGood default
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
  have hred := (lem_lr_ind_reduced d
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2 hposFiber.ne' default).1
  have hvalL : Measurable[⊤] (Subtype.val :
      {mL : BoltzmannSpace ell s // IsML x mL} → BoltzmannSpace ell s) :=
    measurable_from_top
  have hvalR : Measurable[⊤] (Subtype.val :
      {mR : BoltzmannSpace s r // IsMR x mR} → BoltzmannSpace s r) :=
    measurable_from_top
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
  have hind : IndepFun (fun m => (cuts (ι m)).1) (fun m => (cuts (ι m)).2)
      (ν[|fiber]) := by
    rw [hL, hR, hleft, hright]
    exact hred.comp hvalL hvalR
  have hmL : Measurable L := by intro U hU; trivial
  have hmR : Measurable R := by intro U hU; trivial
  have hmι : Measurable ι := by intro U hU; trivial
  have hmap : IndepFun L R ((ν[|fiber]).map ι) :=
    (firstHit_indepFun_map_iff_comp (ν[|fiber]) hmL hmR hmι).mpr hind
  have hpath : IndepFun L R ((μ[|E ∩ M ⁻¹' G]).map M) := by
    rwa [hmapCond]
  exact (firstHit_indepFun_map_iff_comp (μ[|E ∩ M ⁻¹' G]) hmL hmR hM).mp hpath

private noncomputable def firstHitLegalMap (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) : Option (AllBoltzmannSpace r) := by
  classical
  exact if firstHitPrefixLegal r p then stoppedMap r hr (pathCode p) else none

private theorem firstHitLegalMap_ae (r : ℕ) (hr : 1 ≤ r) :
    firstHitLegalMap r hr =ᵐ[conditionedVectorPathLaw 0 0]
      fun p => stoppedMap r hr (pathCode p) := by
  filter_upwards [conditionedVectorPathLaw_ae_legal] with p hp
  have hl : firstHitPrefixLegal r p := ⟨hp.1, fun n hn => hp.2 n⟩
  simp [firstHitLegalMap, hl]

private theorem firstHitLegalMap_past (r : ℕ) (hr : 1 ≤ r) (ell : ℕ)
    (T : Set (Option (AllBoltzmannSpace r))) (_hT : MeasurableSet T)
    (k : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      (firstHitLegalMap r hr ⁻¹' T ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) :=
  measurableSet_firstHit_cut_slice r hr ell k id none (firstHitLegalMap r hr)
    (by intro p; simp [firstHitLegalMap]) T

/-- the finite first-hit past cut pair is independent of the uncentered future when
conditioned on the endpoint and XDP length. The renewal-time selection, T_0 branch,
and infinite-geodesic identification are not treated; not the paper result. -/
theorem firstHitFinitePastCuts_independent_future
    (x : XDP) (r ell s : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let M := fun p => stoppedMap r hr (pathCode p)
    let G : Set (Option (AllBoltzmannSpace r)) :=
      {o | ∃ m : BoltzmannSpace ell r,
        o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ (E ∩ M ⁻¹' G) →
      ∀ default : {mL : BoltzmannSpace ell s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR},
        let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
        IndepFun (cuts ∘ M) Y (μ[|E ∩ M ⁻¹' G]) := by
  dsimp only
  intro hGood default
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let M : (ℕ → ℤ × ℤ) → Option (AllBoltzmannSpace r) :=
    fun p => stoppedMap r hr (pathCode p)
  let G : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r,
      o = some (⟨ell, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let cuts := firstHitFinitePastCutOutputs x ell r s hell hr default
  have hE : MeasurableSet E := firstHitEndpointEvent_measurable r ell
  have hG : MeasurableSet G := trivial
  have hM : Measurable M :=
    (measurable_stoppedMap r hr).comp measurable_pathCode
  have hMpre : MeasurableSet (M ⁻¹' G) := hM hG
  have hEpos : 0 < μ E :=
    lt_of_lt_of_le hGood (measure_mono Set.inter_subset_left)
  have hI : IndepFun M Y (μ[|E]) := by
    have hI' := conditionedFirstHit_endpoint_indepFun r ell hr hell
      (firstHitLegalMap r hr)
      (fun T hT k => firstHitLegalMap_past r hr ell T hT k) hEpos
    have hae : firstHitLegalMap r hr =ᵐ[μ] M := by
      simpa [M] using firstHitLegalMap_ae r hr
    exact hI'.congr (cond_absolutelyContinuous.ae_le hae) (by rfl)
  have hposCond : 0 < (μ[|E]) (M ⁻¹' G) :=
    cond_pos_of_inter_ne_zero hE hGood.ne'
  have hprob : IsProbabilityMeasure (μ[|E]) := cond_isProbabilityMeasure hEpos.ne'
  have hstop : (μ[|E]) (M ⁻¹' G) ≠ ⊤ := by
    have hle : (μ[|E]) (M ⁻¹' G) ≤ 1 := by
      calc
        (μ[|E]) (M ⁻¹' G) ≤ (μ[|E]) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := hprob.measure_univ
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  rw [← cond_cond_eq_cond_inter hE hMpre μ]
  exact firstHit_indepFun_comp_cond_preimage (μ[|E]) M Y cuts G hM
    (by intro T hT; trivial) hI hG hposCond hstop

end DirectedDistances.PaperProofs.Section4
