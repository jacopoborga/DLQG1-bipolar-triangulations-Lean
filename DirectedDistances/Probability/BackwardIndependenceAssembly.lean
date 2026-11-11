module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Abstract backward-martingale independence assembly

backward-martingale independence assembly; the concrete filtration F_k (renewal times, -/

public section

namespace DirectedDistances.Probability

open MeasureTheory Filter
open scoped Topology ENNReal

/-- expectation onto a measure-trivial sigma-algebra is the constant mean. The concrete -/
theorem condExp_ae_eq_mean_of_trivial {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (htriv : ∀ s, MeasurableSet[m] s → μ s = 0 ∨ μ s = 1)
    (Z : Ω → ℝ) (hZ : Integrable Z μ) :
    μ[Z | m] =ᵐ[μ] fun _ => ∫ ω, Z ω ∂μ := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hZ
  · intro s _ _
    exact (integrable_const _).integrableOn
  · intro s hs _
    rcases htriv s hs with hzero | hone
    · simp [Measure.restrict_eq_zero.mpr hzero]
    · have hae : ∀ᵐ ω ∂μ, ω ∈ s := by
        rw [ae_iff]
        exact (prob_compl_eq_zero_iff (hm s hs)).mpr hone
      rw [← integral_eq_setIntegral hae, ← integral_eq_setIntegral hae]
      simp
  · exact stronglyMeasurable_const.aestronglyMeasurable

private theorem aestronglyMeasurable_iInf_of_antitone
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (F : ℕ → MeasurableSpace Ω) (hanti : Antitone F) (f : Ω → ℝ)
    (hf : ∀ k, AEStronglyMeasurable[F k] f μ) :
    AEStronglyMeasurable[⨅ k, F k] f μ := by
  let g : ℕ → Ω → ℝ := fun k => (hf k).mk f
  have hg (k : ℕ) : Measurable[F k] (g k) := (hf k).measurable_mk
  have hm : Measurable[⨅ k, F k] (fun ω => liminf (fun k => g k ω) atTop) := by
    rw [measurable_iff_comap_le]
    apply le_iInf
    intro k
    apply Measurable.comap_le
    have ht : Measurable[F k] (fun ω => liminf (fun n => g (n + k) ω) atTop) :=
      Measurable.liminf (fun n => (hg (n + k)).mono (hanti (Nat.le_add_left k n)) le_rfl)
    have he : (fun ω => liminf (fun n => g (n + k) ω) atTop) =
        (fun ω => liminf (fun n => g n ω) atTop) := by
      funext ω
      exact liminf_nat_add (fun n => g n ω) k
    exact he ▸ ht
  refine ⟨_, hm.stronglyMeasurable, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun k => (hf k).ae_eq_mk)] with ω hω
  have heq : (fun k => g k ω) = fun _ => f ω := by
    funext k
    exact (hω k).symm
  rw [heq]
  exact tendsto_const_nhds.liminf_eq.symm

private theorem starProjection_tendsto_iInf
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : ℕ → Submodule ℝ H) [∀ k, (U k).HasOrthogonalProjection]
    [(⨅ k, U k).HasOrthogonalProjection] (hanti : Antitone U) (x : H) :
    Tendsto (fun k => (U k).starProjection x) atTop
      (𝓝 ((⨅ k, U k).starProjection x)) := by
  have hmono : Monotone (fun k => (U k)ᗮ) :=
    fun _ _ h => Submodule.orthogonal_le (hanti h)
  have ht := Submodule.starProjection_tendsto_closure_iSup (fun k => (U k)ᗮ) hmono x
  have heq : (⨆ k, (U k)ᗮ).topologicalClosureᗮ = ⨅ k, U k := by
    rw [Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal]
    simp only [Submodule.orthogonal_orthogonal]
  have hs (k : ℕ) : x - (U k)ᗮ.starProjection x = (U k).starProjection x := by
    rw [Submodule.starProjection_orthogonal]
    simp only [sub_apply, ContinuousLinearMap.id_apply, sub_sub_cancel]
  have hl : x - (⨆ k, (U k)ᗮ).topologicalClosure.starProjection x =
      (⨅ k, U k).starProjection x := by
    simp only [← heq, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply]
  simpa only [hs, hl] using (tendsto_const_nhds (x := x)).sub ht

/-- conditional-expectation convergence for an abstract decreasing sequence of sigma-algebras.
not the paper result. -/
theorem tendsto_eLpNorm_condExp_iInf
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ k, F k ≤ m0) (hanti : Antitone F)
    (Z : Ω → ℝ) (hZ : MemLp Z 2 μ) :
    Tendsto (fun k => eLpNorm (μ[Z | F k] - μ[Z | ⨅ n, F n]) 2 μ)
      atTop (𝓝 0) := by
  let U : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun k => lpMeas ℝ ℝ (F k) 2 μ
  have hInf : (⨅ k, F k) ≤ m0 := (iInf_le F 0).trans (hF 0)
  let : ∀ k, Fact (F k ≤ m0) := fun k => ⟨hF k⟩
  let : Fact ((⨅ k, F k) ≤ m0) := ⟨hInf⟩
  have hUeq : (⨅ k, U k) = lpMeas ℝ ℝ (⨅ k, F k) 2 μ := by
    ext f
    simp only [Submodule.mem_iInf, mem_lpMeas_iff_aestronglyMeasurable, U]
    constructor
    · exact aestronglyMeasurable_iInf_of_antitone F hanti f
    · intro hf k
      exact AEStronglyMeasurable.mono (iInf_le F k) hf
  let : (⨅ k, U k).HasOrthogonalProjection := by
    rw [hUeq]
    infer_instance
  have hUanti : Antitone U := by
    intro i j hij f hf
    exact AEStronglyMeasurable.mono (hanti hij) hf
  have ht := starProjection_tendsto_iInf U hUanti (hZ.toLp Z)
  simp only [hUeq] at ht
  change Tendsto (fun k => (condExpL2 ℝ ℝ (hF k) (hZ.toLp Z) : Lp ℝ 2 μ)) atTop
    (𝓝 (condExpL2 ℝ ℝ hInf (hZ.toLp Z) : Lp ℝ 2 μ)) at ht
  have hn := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp ht
  have heq (k : ℕ) :
      eLpNorm (μ[Z | F k] - μ[Z | ⨅ n, F n]) 2 μ =
        eLpNorm ((condExpL2 ℝ ℝ (hF k) (hZ.toLp Z) : Ω → ℝ) -
          (condExpL2 ℝ ℝ hInf (hZ.toLp Z) : Ω → ℝ)) 2 μ := by
    apply eLpNorm_congr_ae
    exact (hZ.condExpL2_ae_eq_condExp (hF k)).symm.sub
      (hZ.condExpL2_ae_eq_condExp hInf).symm
  simpa only [heq] using hn

private theorem tendsto_eLpNorm_condExp_mean_of_trivial_iInf
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ k, F k ≤ m0) (hanti : Antitone F)
    (htriv : ∀ s, MeasurableSet[⨅ k, F k] s → μ s = 0 ∨ μ s = 1)
    (Z : Ω → ℝ) (hZ : MemLp Z 2 μ) :
    Tendsto (fun k => eLpNorm (μ[Z | F k] - fun _ => ∫ ω, Z ω ∂μ) 2 μ)
      atTop (𝓝 0) := by
  have hc := condExp_ae_eq_mean_of_trivial μ (⨅ k, F k)
    ((iInf_le F 0).trans (hF 0)) htriv Z
    (memLp_one_iff_integrable.mp (hZ.mono_exponent one_le_two))
  have heq (k : ℕ) :
      eLpNorm (μ[Z | F k] - fun _ => ∫ ω, Z ω ∂μ) 2 μ =
        eLpNorm (μ[Z | F k] - μ[Z | ⨅ n, F n]) 2 μ :=
    eLpNorm_congr_ae (ae_eq_rfl.sub hc.symm)
  simpa only [heq] using tendsto_eLpNorm_condExp_iInf μ F hF hanti Z hZ

private theorem indicator_tendstoInMeasure_one {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet (E k))
    (hEto : Tendsto (fun k => μ (E k)) atTop (𝓝 1)) :
    TendstoInMeasure μ (fun k => (E k).indicator (fun _ => (1 : ℝ))) atTop
      (fun _ => 1) := by
  have hc : Tendsto (fun k => μ (E k)ᶜ) atTop (𝓝 0) := by
    have ht := ((ENNReal.continuous_sub_left (a := 1) ENNReal.one_ne_top).tendsto 1).comp
      hEto
    simpa only [Function.comp_def, prob_compl_eq_one_sub (hE _), tsub_self] using ht
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
  · intro k
    positivity
  · intro k
    apply measure_mono
    intro ω hω
    by_contra hmem
    have hm : ω ∈ E k := by simpa using hmem
    change ε ≤ ‖(E k).indicator (fun _ => (1 : ℝ)) ω - 1‖ at hω
    simp only [Set.indicator_of_mem hm, sub_self, norm_zero] at hω
    exact (not_le_of_gt hε) hω

private theorem eq_mul_of_masked_tendstoInMeasure {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C D : ℕ → Ω → ℝ) (a b c : ℝ)
    (hA : TendstoInMeasure μ A atTop (fun _ => a))
    (hB : TendstoInMeasure μ B atTop (fun _ => b))
    (hC : TendstoInMeasure μ C atTop (fun _ => c))
    (hD : TendstoInMeasure μ D atTop (fun _ => 1))
    (heq : ∀ k, A k * D k =ᵐ[μ] B k * C k * D k) : a = b * c := by
  obtain ⟨n₁, hn₁, h₁⟩ := hA.exists_seq_tendsto_ae
  obtain ⟨n₂, hn₂, h₂⟩ := (hB.comp hn₁.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨n₃, hn₃, h₃⟩ :=
    (hC.comp (hn₁.comp hn₂).tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨n₄, hn₄, h₄⟩ :=
    (hD.comp (hn₁.comp (hn₂.comp hn₃)).tendsto_atTop).exists_seq_tendsto_ae
  have hlim : ∀ᵐ ω ∂μ, a = b * c := by
    filter_upwards [h₁, h₂, h₃, h₄, ae_all_iff.mpr heq] with ω h₁ h₂ h₃ h₄ heq
    have hleft := (h₁.comp (hn₂.comp (hn₃.comp hn₄)).tendsto_atTop).mul h₄
    have hright := ((h₂.comp (hn₃.comp hn₄).tendsto_atTop).mul
      (h₃.comp hn₄.tendsto_atTop)).mul h₄
    have he : (fun k => A (n₁ (n₂ (n₃ (n₄ k)))) ω * D (n₁ (n₂ (n₃ (n₄ k)))) ω) =
        (fun k => B (n₁ (n₂ (n₃ (n₄ k)))) ω * C (n₁ (n₂ (n₃ (n₄ k)))) ω *
          D (n₁ (n₂ (n₃ (n₄ k)))) ω) := by
      funext k
      exact heq _
    dsimp only [Function.comp_def] at hleft hright
    rw [he] at hleft
    simpa only [mul_one] using tendsto_nhds_unique hleft hright
  exact hlim.exists.choose_spec

/-- backward-martingale independence assembly, assuming explicit Lp convergence of the three
is not used; not the paper result. The final assembly discharges the convergence assumptions. -/
private theorem integral_mul_eq_mul_integral_of_tendsto_condExp
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet (E k))
    (hEto : Tendsto (fun k => μ (E k)) atTop (𝓝 1))
    (X Y : Ω → ℝ) (p : ℝ≥0∞) (hp : p ≠ 0)
    (hX : Tendsto (fun k => eLpNorm (μ[X | F k] - fun _ => ∫ ω, X ω ∂μ) p μ)
      atTop (𝓝 0))
    (hY : Tendsto (fun k => eLpNorm (μ[Y | F k] - fun _ => ∫ ω, Y ω ∂μ) p μ)
      atTop (𝓝 0))
    (hXY : Tendsto (fun k => eLpNorm
      (μ[X * Y | F k] - fun _ => ∫ ω, X ω * Y ω ∂μ) p μ) atTop (𝓝 0))
    (hfac : ∀ k, μ[X * Y | F k] * (E k).indicator 1 =ᵐ[μ]
      μ[X | F k] * μ[Y | F k] * (E k).indicator 1) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) := by
  exact eq_mul_of_masked_tendstoInMeasure μ _ _ _ _ _ _ _
    (tendstoInMeasure_of_tendsto_eLpNorm hp hXY)
    (tendstoInMeasure_of_tendsto_eLpNorm hp hX)
    (tendstoInMeasure_of_tendsto_eLpNorm hp hY)
    (indicator_tendstoInMeasure_one μ E hE hEto) hfac

/-- backward-martingale independence assembly for bounded real random variables. The concrete -/
theorem integral_mul_eq_mul_integral_of_backward_factorization
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ k, F k ≤ m0) (hanti : Antitone F)
    (htriv : ∀ s, MeasurableSet[⨅ k, F k] s → μ s = 0 ∨ μ s = 1)
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet[F k] (E k))
    (hEto : Tendsto (fun k => μ (E k)) atTop (𝓝 1))
    (X Y : Ω → ℝ) (hX : MemLp X ∞ μ) (hY : MemLp Y ∞ μ)
    (hfac : ∀ k, μ[X * Y | F k] * (E k).indicator 1 =ᵐ[μ]
      μ[X | F k] * μ[Y | F k] * (E k).indicator 1) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) := by
  apply integral_mul_eq_mul_integral_of_tendsto_condExp μ F E
    (fun k => hF k _ (hE k)) hEto X Y 2 (by norm_num)
  · exact tendsto_eLpNorm_condExp_mean_of_trivial_iInf μ F hF hanti htriv X
      (hX.mono_exponent le_top)
  · exact tendsto_eLpNorm_condExp_mean_of_trivial_iInf μ F hF hanti htriv Y
      (hY.mono_exponent le_top)
  · exact tendsto_eLpNorm_condExp_mean_of_trivial_iInf μ F hF hanti htriv (X * Y)
      ((hX.mul hY).mono_exponent le_top)
  · exact hfac

end DirectedDistances.Probability
