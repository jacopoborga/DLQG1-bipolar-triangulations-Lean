module

public import DirectedDistances.PaperProofs.Section4.SelectedCutGoodEvent
public import DirectedDistances.PaperProofs.Section4.SelectedCutAmbientFactorization
public import DirectedDistances.PaperProofs.Section4.SelectedCutFiltrationCore
public import DirectedDistances.PaperProofs.Section4.SelectedCutBlockInvariance
public import DirectedDistances.Probability.ThinIndependenceSkeleton

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal Topology

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0

private theorem coherent_measurePreserving
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    MeasurePreserving (Subtype.val : selectedCutCoherentDomain x T hT → Ω)
      ((μ).comap Subtype.val) μ := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe (selectedCutCoherentDomain_measurable_conull x T hT).1]
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_iff.mpr (selectedCutCoherentDomain_measurable_conull x T hT).2)






theorem selectedCutCoherent_probability
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    IsProbabilityMeasure ((μ).comap
      (Subtype.val : selectedCutCoherentDomain x T hT → Ω)) := by
  have : IsProbabilityMeasure μ :=
    (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).1
  have hp := coherent_measurePreserving x T hT
  have : IsProbabilityMeasure (((μ).comap
      (Subtype.val : selectedCutCoherentDomain x T hT → Ω)).map Subtype.val) := by
    rw [hp.map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable

private theorem condExp_pullback
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {ν : Measure α} {ρ : Measure β} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    {e : α → β} (he : MeasurePreserving e ν ρ) (hemb : MeasurableEmbedding e)
    (m : MeasurableSpace β) (hm : m ≤ mβ) (f : β → ℝ) (hf : Integrable f ρ) :
    (fun a => ρ[f | m] (e a)) =ᵐ[ν] ν[fun a => f (e a) | m.comap e] := by
  let : MeasurableSpace β := mβ
  have hle : m.comap e ≤ mα := (MeasurableSpace.comap_mono hm).trans he.measurable.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq hle
    (he.integrable_comp_of_integrable hf)
  · intro s _ _
    exact (he.integrable_comp_of_integrable integrable_condExp).integrableOn
  · intro s hs _
    obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    change (∫ a in e ⁻¹' u, ρ[f | m] (e a) ∂ν) =
      ∫ a in e ⁻¹' u, f (e a) ∂ν
    rw [he.setIntegral_preimage_emb hemb, he.setIntegral_preimage_emb hemb]
    exact setIntegral_condExp hm hf hu
  · exact (stronglyMeasurable_condExp.comp_measurable
      (comap_measurable e)).aestronglyMeasurable






theorem measurableSet_selectedCutCoherent_good_event
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s k : ℕ) :
    MeasurableSet[selectedCutConditioningSigma x T hT k]
      {q : selectedCutCoherentDomain x T hT | (s : ℤ) + 1 ≤
        min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
          (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)} := by
  rw [(selectedCutConditioningSigma_eq x T hT k).1]
  have hc : Measurable (fun b : Ω × ℕ => min (b.1 0).1 (-(b.1 0).2)) :=
    (((measurable_pi_apply 0).comp measurable_fst).fst).min
      (((measurable_pi_apply 0).comp measurable_fst).snd.neg)
  exact ⟨{b | (s : ℤ) + 1 ≤ min (b.1 0).1 (-(b.1 0).2)},
    measurableSet_le measurable_const hc, rfl⟩






theorem selectedCutCoherent_good_event_probability_tendsto_one
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) (s : ℕ) :
    Tendsto (fun k => ((μ).comap
      (Subtype.val : selectedCutCoherentDomain x T hT → Ω))
      {q | (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)}) atTop (𝓝 1) := by
  have ht := (selectedCutTime_good_event_probability_tendsto_one T hT s).comp
    (tendsto_add_atTop_nat 1)
  have hp := coherent_measurePreserving x T hT
  convert ht using 1
  funext k
  exact hp.measure_preimage
    (measurableSet_selectedCutTime_good_event T hT s (k + 1)).nullMeasurableSet

/-- Helper toward Proposition 4.7 (prop-thin-ind): transport of slice 2 to the coherent
carrier, on the explicit good event. This is not the paper result and requires no decoders. -/
theorem selectedCutCoherent_indicator_factorization
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s k : ℕ) (A B : Set (Option (Σ n : ℕ, KMSW.AllBoltzmannSpace n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let Q := selectedCutCoherentDomain x T hT
    let ν := (μ).comap (Subtype.val : Q → Ω)
    let F := selectedCutConditioningSigma x T hT k
    let AL := {q : Q | (selectedCutPastCuts x T (k + 1) q.1).1 ∈ A}
    let BR := {q : Q | (selectedCutPastCuts x T (k + 1) q.1).2 ∈ B}
    let E := {q : Q | (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)}
    ν[(AL ∩ BR).indicator (1 : Q → ℝ) | F] * E.indicator 1 =ᵐ[ν]
      ν[AL.indicator (1 : Q → ℝ) | F] *
        ν[BR.indicator (1 : Q → ℝ) | F] * E.indicator 1 := by
  classical
  let Q := selectedCutCoherentDomain x T hT
  let ν := (μ).comap (Subtype.val : Q → Ω)
  let m0 : MeasurableSpace Ω := inferInstance
  let Bv := selectedCutConditioningVersion x T hT k
  let F := MeasurableSpace.comap Bv inferInstance
  let : MeasurableSpace Ω := m0
  let C := selectedCutPastCuts x T (k + 1)
  let AL := {p : Ω | (C p).1 ∈ A}
  let BR := {p : Ω | (C p).2 ∈ B}
  let E := {p : Ω | (s : ℤ) + 1 ≤ min ((Bv p).1 0).1 (-((Bv p).1 0).2)}
  let EQ := {q : Q | (s : ℤ) + 1 ≤
    min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)}
  have : IsProbabilityMeasure μ :=
    (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).1
  have : IsProbabilityMeasure ν := selectedCutCoherent_probability x T hT
  have hp := coherent_measurePreserving x T hT
  have hvm := (selectedCutConditioningVersion_measurable_ae_eq x T hT k).1
  have hv := (selectedCutConditioningVersion_measurable_ae_eq x T hT k).2
  have hE : MeasurableSet[F] E := by
    have hc : Measurable (fun b : Ω × ℕ => min (b.1 0).1 (-(b.1 0).2)) :=
      (((measurable_pi_apply 0).comp measurable_fst).fst).min
        (((measurable_pi_apply 0).comp measurable_fst).snd.neg)
    exact ⟨{b | (s : ℤ) + 1 ≤ min (b.1 0).1 (-(b.1 0).2)},
      measurableSet_le measurable_const hc, rfl⟩
  have hES : E ⊆ {p | ((Bv p).1 0).2 < 0} := by
    intro p hp
    change (s : ℤ) + 1 ≤ min _ _ at hp
    have hh := hp.trans (min_le_right _ _)
    change ((Bv p).1 0).2 < 0
    omega
  have hfac := selectedCutCodeDistance_ambient_indicator_factorization x T (k + 1)
    (by omega) hT Bv hvm hv A B hA hB E hE hES
  have hCm := measurable_selectedCutPastCuts x T (k + 1) hT
  have hAm : MeasurableSet AL := hCm.fst hA
  have hBm : MeasurableSet BR := hCm.snd hB
  have hemb :=
    MeasurableEmbedding.subtype_coe
      (selectedCutCoherentDomain_measurable_conull x T hT).1
  have hF : F.comap (Subtype.val : Q → Ω) = selectedCutConditioningSigma x T hT k := by
    rw [MeasurableSpace.comap_comp]
    rfl
  have hL := condExp_pullback hp hemb F hvm.comap_le
    (AL.indicator (1 : Ω → ℝ)) ((integrable_const (1 : ℝ)).indicator hAm)
  have hR := condExp_pullback hp hemb F hvm.comap_le
    (BR.indicator (1 : Ω → ℝ)) ((integrable_const (1 : ℝ)).indicator hBm)
  have hLR := condExp_pullback hp hemb F hvm.comap_le
    ((AL ∩ BR).indicator (1 : Ω → ℝ))
    ((integrable_const (1 : ℝ)).indicator (hAm.inter hBm))
  rw [hF] at hL hR hLR
  have hfacQ := hp.quasiMeasurePreserving.ae hfac
  have hI : (fun q : Q => E.indicator (1 : Ω → ℝ) q.1) = EQ.indicator 1 := by
    funext q
    have hEq : q.1 ∈ E ↔ q ∈ EQ := by
      change (s : ℤ) + 1 ≤ min ((Bv q.1).1 0).1 (-((Bv q.1).1 0).2) ↔ _
      change (s : ℤ) + 1 ≤
        min ((selectedCutConditioningVersion x T hT k q.1).1 0).1
          (-((selectedCutConditioningVersion x T hT k q.1).1 0).2) ↔ _
      rw [(selectedCutCoherentDomain_spec x T hT q).1 k]
      rfl
    by_cases hh : q.1 ∈ E
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (hEq.mp hh)]
      rfl
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (fun h => hh (hEq.mpr h))]
  filter_upwards [hfacQ, hL, hR, hLR] with q hq hl hr hlr
  have hi := congrFun hI q
  change μ[(AL ∩ BR).indicator (1 : Ω → ℝ) | F] q.1 *
    E.indicator 1 q.1 = μ[AL.indicator (1 : Ω → ℝ) | F] q.1 *
      μ[BR.indicator (1 : Ω → ℝ) | F] q.1 * E.indicator 1 q.1 at hq
  rw [hi, hl, hr, hlr] at hq
  exact hq

private theorem condExp_eq_on_event
    {Q : Type*} [m0 : MeasurableSpace Q] (ν : Measure Q)
    (F : MeasurableSpace Q) (E : Set Q) (hE : MeasurableSet[F] E)
    (f g : Q → ℝ) (hf : Integrable f ν) (hg : Integrable g ν)
    (hfg : ∀ q ∈ E, f q = g q) :
    ∀ᵐ q ∂ν, q ∈ E → ν[f | F] q = ν[g | F] q := by
  have hI : E.indicator f = E.indicator g := by
    funext q
    by_cases hq : q ∈ E
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      exact hfg q hq
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
  have hCE : E.indicator (ν[f | F]) =ᵐ[ν] E.indicator (ν[g | F]) :=
    (condExp_indicator hf hE).symm.trans
      ((condExp_congr_ae (Filter.Eventually.of_forall (congrFun hI))).trans
        (condExp_indicator hg hE))
  filter_upwards [hCE] with q hq hmem
  simpa only [Set.indicator_of_mem hmem] using hq






theorem thinIndependence_of_cutDecoders
    {L R L' R' : Type*} [mL : MeasurableSpace L] [mR : MeasurableSpace R]
    [MeasurableSpace L'] [MeasurableSpace R']
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (XL : ℕ → selectedCutCoherentDomain x T hT → L)
    (XR : ℕ → selectedCutCoherentDomain x T hT → R)
    (hXL : ∀ s, Measurable (XL s)) (hXR : ∀ s, Measurable (XR s))
    (hmonoL : Monotone (fun s => mL.comap (XL s)))
    (hmonoR : Monotone (fun s => mR.comap (XR s)))
    (gL : ℕ → ℕ → Option (Σ n : ℕ, KMSW.AllBoltzmannSpace n) → L)
    (gR : ℕ → ℕ → Option (Σ n : ℕ, KMSW.AllBoltzmannSpace n) → R)
    (hgL : ∀ s k, Measurable (gL s k)) (hgR : ∀ s k, Measurable (gR s k))
    (hdecodeL : ∀ (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
      (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
      XL s q = gL s k (selectedCutPastCuts x T (k + 1) q.1).1)
    (hdecodeR : ∀ (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
      (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
      XR s q = gR s k (selectedCutPastCuts x T (k + 1) q.1).2)
    (XLlim : selectedCutCoherentDomain x T hT → L')
    (XRlim : selectedCutCoherentDomain x T hT → R')
    (hXLlim : Measurable[⨆ s, mL.comap (XL s)] XLlim)
    (hXRlim : Measurable[⨆ s, mR.comap (XR s)] XRlim) :
    IndepFun XLlim XRlim ((μ).comap
      (Subtype.val : selectedCutCoherentDomain x T hT → Ω)) := by
  classical
  let Q := selectedCutCoherentDomain x T hT
  let ν := (μ).comap (Subtype.val : Q → Ω)
  let F := selectedCutConditioningSigma x T hT
  let E : ℕ → ℕ → Set Q := fun s k =>
    {q | (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)}
  have : IsProbabilityMeasure ν := selectedCutCoherent_probability x T hT
  have hF : ∀ k, F k ≤ (inferInstance : MeasurableSpace Q) := fun k =>
    ((selectedCutConditioningVersion_measurable_ae_eq x T hT k).1.comp
      measurable_subtype_coe).comap_le
  have hE : ∀ s k, MeasurableSet[F k] (E s k) :=
    measurableSet_selectedCutCoherent_good_event x T hT
  apply DirectedDistances.Probability.indepFun_of_backward_indicator_factorization
    ν F hF (selectedCutConditioningSigma_antitone x T hT)
    (selectedCutConditioningSigma_iInf_trivial x T hT) XL XR hXL hXR hmonoL hmonoR
    E hE (selectedCutCoherent_good_event_probability_tendsto_one x T hT)
    ?_ XLlim XRlim hXLlim hXRlim
  intro s k A hA B hB
  obtain ⟨A0, hA0, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  obtain ⟨B0, hB0, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
  let AL := XL s ⁻¹' A0
  let BR := XR s ⁻¹' B0
  let DL := {q : Q | gL s k (selectedCutPastCuts x T (k + 1) q.1).1 ∈ A0}
  let DR := {q : Q | gR s k (selectedCutPastCuts x T (k + 1) q.1).2 ∈ B0}
  have hAL : MeasurableSet AL := hXL s hA0
  have hBR : MeasurableSet BR := hXR s hB0
  have hC : Measurable (fun q : Q => selectedCutPastCuts x T (k + 1) q.1) :=
    (measurable_selectedCutPastCuts x T (k + 1) hT).comp measurable_subtype_coe
  have hDL : MeasurableSet DL := hC.fst (hgL s k hA0)
  have hDR : MeasurableSet DR := hC.snd (hgR s k hB0)
  have heqL : ∀ q ∈ E s k, AL.indicator (1 : Q → ℝ) q = DL.indicator 1 q := by
    intro q hq
    have hx := hdecodeL s k q hq
    change (XL s ⁻¹' A0).indicator (1 : Q → ℝ) q = _
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, DL, Set.mem_ofPred_eq, hx]
  have heqR : ∀ q ∈ E s k, BR.indicator (1 : Q → ℝ) q = DR.indicator 1 q := by
    intro q hq
    have hx := hdecodeR s k q hq
    change (XR s ⁻¹' B0).indicator (1 : Q → ℝ) q = _
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, DR, Set.mem_ofPred_eq, hx]
  have heqLR : ∀ q ∈ E s k,
      (AL ∩ BR).indicator (1 : Q → ℝ) q = (DL ∩ DR).indicator 1 q := by
    intro q hq
    simp only [Set.inter_indicator_one, Pi.mul_apply, heqL q hq, heqR q hq]
  have hL := condExp_eq_on_event ν (F k) (E s k) (hE s k)
    (AL.indicator 1) (DL.indicator 1)
    ((integrable_const (1 : ℝ)).indicator hAL)
    ((integrable_const (1 : ℝ)).indicator hDL) heqL
  have hR := condExp_eq_on_event ν (F k) (E s k) (hE s k)
    (BR.indicator 1) (DR.indicator 1)
    ((integrable_const (1 : ℝ)).indicator hBR)
    ((integrable_const (1 : ℝ)).indicator hDR) heqR
  have hLR := condExp_eq_on_event ν (F k) (E s k) (hE s k)
    ((AL ∩ BR).indicator 1) ((DL ∩ DR).indicator 1)
    ((integrable_const (1 : ℝ)).indicator (hAL.inter hBR))
    ((integrable_const (1 : ℝ)).indicator (hDL.inter hDR)) heqLR
  have hcut := selectedCutCoherent_indicator_factorization x T hT s k
    (gL s k ⁻¹' A0) (gR s k ⁻¹' B0) (hgL s k hA0) (hgR s k hB0)
  filter_upwards [hL, hR, hLR, hcut] with q hl hr hlr hc
  by_cases hq : q ∈ E s k
  · change ν[(AL ∩ BR).indicator (1 : Q → ℝ) | F k] q *
      (E s k).indicator 1 q = ν[AL.indicator (1 : Q → ℝ) | F k] q *
        ν[BR.indicator (1 : Q → ℝ) | F k] q * (E s k).indicator 1 q
    rw [hl hq, hr hq, hlr hq]
    exact hc
  · simp only [Pi.mul_apply, Set.indicator_of_notMem hq, mul_zero]

end DirectedDistances.PaperProofs.Section4
