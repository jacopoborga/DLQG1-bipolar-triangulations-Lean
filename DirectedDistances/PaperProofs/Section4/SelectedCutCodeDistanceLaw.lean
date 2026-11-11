module

public import DirectedDistances.PaperProofs.Section4.SelectedCutPastMapLaw
public import DirectedDistances.PaperProofs.Section4.FirstHitPositiveBranchCodeDistance

/-! positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
The natural distance uses the imported almost surely finite decoder; zero at a
nonpositive recovered level is only a totalization outside the positive branches. -/
@[expose] noncomputable def selectedCutCodeDistanceConditioning
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (p : ℕ → ℤ × ℤ) : (ℕ → ℤ × ℤ) × ℕ :=
  let r := (-(selectedCutFuture T k p 0).2).toNat
  (selectedCutFuture T k p,
    if hr : 1 ≤ r then (firstHitCodeDistanceConditioning x r hr p).2 else 0)

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
The output retains the right boundary length in the common cut carrier. -/
@[expose] noncomputable def selectedCutPastCuts
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (p : ℕ → ℤ × ℤ) : PositiveCutOutput :=
  let r := (-(selectedCutFuture T k p 0).2).toNat
  if hr : 1 ≤ r then
    firstHitPositiveCutEmbedding r (firstHitPastAllCuts x r (stoppedMap r hr (pathCode p)))
  else (none, none)

private theorem measurable_selectedCutLevel
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (fun p => (-(selectedCutFuture T k p 0).2).toNat) :=
  (measurable_of_countable (fun q : ℤ × ℤ => (-q.2).toNat)).comp
    ((measurable_pi_apply 0).comp (measurable_selectedCutFuture T k hT))

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
Measurability of the selected cut outputs requires no extra premise on T. -/
theorem measurable_selectedCutPastCuts
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectedCutPastCuts x T k) := by
  let F : (ℕ → ℤ × ℤ) × ℕ → PositiveCutOutput := fun z =>
    if hr : 1 ≤ z.2 then
      firstHitPositiveCutEmbedding z.2
        (firstHitPastAllCuts x z.2 (stoppedMap z.2 hr (pathCode z.1)))
    else (none, none)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro r
    by_cases hr : 1 ≤ r
    · simpa only [F, dite_eq_left hr, Function.comp_def] using
        (measurable_of_countable (firstHitPositiveCutEmbedding r)).comp
          ((measurable_firstHitPastAllCuts x r).comp
            ((measurable_stoppedMap r hr).comp measurable_pathCode))
    · simpa only [F, dite_eq_right hr] using
        (measurable_const : Measurable (fun _ : ℕ → ℤ × ℤ =>
          ((none, none) : PositiveCutOutput)))
  exact hF.comp (measurable_id.prodMk (measurable_selectedCutLevel T k hT))

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
The code-distance datum is almost everywhere measurable under the original law. -/
theorem aemeasurable_selectedCutCodeDistanceConditioning
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    AEMeasurable (selectedCutCodeDistanceConditioning x T k)
      (conditionedVectorPathLaw 0 0) := by
  let R := fun p => (-(selectedCutFuture T k p 0).2).toNat
  let D : (ℕ → ℤ × ℤ) × ℕ → ℕ := fun z =>
    if hr : 1 ≤ z.2 then
      firstHitPastXdpLength x z.2 (stoppedMap z.2 hr (pathCode z.1))
    else 0
  have hD : Measurable D := by
    apply measurable_from_prod_countable_left
    intro r
    by_cases hr : 1 ≤ r
    · simpa only [D, dite_eq_left hr, Function.comp_def] using
        (measurable_firstHitPastXdpLength x r).comp
          ((measurable_stoppedMap r hr).comp measurable_pathCode)
    · simpa only [D, dite_eq_right hr] using
        (measurable_const : Measurable (fun _ : ℕ → ℤ × ℤ => (0 : ℕ)))
  have hPast : Measurable (fun p => (selectedCutFuture T k p, D (p, R p))) :=
    (measurable_selectedCutFuture T k hT).prodMk
      (hD.comp (measurable_id.prodMk (measurable_selectedCutLevel T k hT)))
  have hall : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∀ r (hr : 1 ≤ r),
      firstHitCodeXdpDistance x r p =
        firstHitPastXdpLength x r (stoppedMap r hr (pathCode p)) :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun hr =>
      firstHitCodeXdpDistance_ae_eq_pastLength x r hr
  apply hPast.aemeasurable.congr
  filter_upwards [hall] with p hp
  apply Prod.ext
  · rfl
  · dsimp only [selectedCutCodeDistanceConditioning, firstHitCodeDistanceConditioning, D]
    by_cases hr : 1 ≤ R p
    · simp only [R] at hr
      rw [dite_eq_left hr, dite_eq_left hr]
      exact (hp _ hr).symm
    · simp only [R] at hr
      rw [dite_eq_right hr, dite_eq_right hr]

private theorem selectedCutCodeDistance_positive_maps
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let μ := conditionedVectorPathLaw 0 0
    let S := {p | 0 < selectedCutTime T k p}
    let B := selectedCutCodeDistanceConditioning x T k
    let C := selectedCutPastCuts x T k
    let E := fun i : PositiveBranchIx k =>
      (fun p => conditionedVectorShift
        (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
        firstHitPositiveBranchFuture i.1.1 i.1.2 k
    let Bc := fun i : PositiveBranchIx k =>
      firstHitCodeDistanceConditioning x i.1.2 i.2.1
    let Cp := fun i : PositiveBranchIx k => fun p =>
      firstHitPositiveCutEmbedding i.1.2
        (firstHitPastAllCuts x i.1.2 (stoppedMap i.1.2 i.2.1 (pathCode p)))
    (μ.restrict S).map B = Measure.sum (fun i => (μ.restrict (E i)).map (Bc i)) ∧
      (μ.restrict S).map (fun p => (B p, C p)) =
        Measure.sum (fun i => (μ.restrict (E i)).map (fun p => (Bc i p, Cp i p))) := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let E := fun i : PositiveBranchIx k =>
    (fun p => conditionedVectorShift
      (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
      firstHitPositiveBranchFuture i.1.1 i.1.2 k
  let Y := fun r p =>
    conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
  let B := selectedCutCodeDistanceConditioning x T k
  let C := selectedCutPastCuts x T k
  let Bc := fun i : PositiveBranchIx k =>
    firstHitCodeDistanceConditioning x i.1.2 i.2.1
  let Cp := fun i : PositiveBranchIx k => fun p =>
    firstHitPositiveCutEmbedding i.1.2
      (firstHitPastAllCuts x i.1.2 (stoppedMap i.1.2 i.2.1 (pathCode p)))
  have hrestrict : μ.restrict {p | 0 < selectedCutTime T k p} =
      Measure.sum (fun i => μ.restrict (E i)) :=
    selectedCutTime_positive_restrict_eq_sum T k hk hT
  have hB : AEMeasurable B (Measure.sum (fun i => μ.restrict (E i))) := by
    rw [← hrestrict]
    exact (aemeasurable_selectedCutCodeDistanceConditioning x T k hT).restrict
  have hC : Measurable C := measurable_selectedCutPastCuts x T k hT
  have hagree (i : PositiveBranchIx k) :
      (fun p => (B p, C p)) =ᵐ[μ.restrict (E i)]
        fun p => (Bc i p, Cp i p) := by
    have hE : MeasurableSet (E i) :=
      (measurable_conditionedFirstHit_future i.1.2)
        (measurableSet_firstHitPositiveBranchFuture i.1.1 i.1.2 k)
    filter_upwards [ae_restrict_of_ae
      (selectedCutTime_positiveBranch_event_ae T k i.1.2 i.1.1 i.2.1 i.2.2 hT),
      ae_restrict_of_ae (firstHitPastMap_finite_hit_ae i.1.2 i.2.1),
      ae_restrict_mem hE] with p hb hf hp
    have hsel : selectedCutTime T k p = conditionedSecondCoordinateFirstHit i.1.2 p :=
      ((Iff.of_eq hb).mpr ⟨hf, hp⟩).1
    have hY : selectedCutFuture T k p = Y i.1.2 p := by
      change conditionedVectorShift (selectedCutTime T k p).toNat p = _
      rw [hsel]
    have hpoint : Y i.1.2 p 0 = ((i.1.1 : ℤ), -(i.1.2 : ℤ)) := hp.2
    have hR : (-(selectedCutFuture T k p 0).2).toNat = i.1.2 := by
      rw [hY, hpoint]
      simp only [neg_neg, Int.toNat_natCast]
    apply Prod.ext
    · dsimp only [B, selectedCutCodeDistanceConditioning]
      rw [hR, dite_eq_left i.2.1]
      change (selectedCutFuture T k p, firstHitCodeXdpDistance x i.1.2 p) =
        (Y i.1.2 p, firstHitCodeXdpDistance x i.1.2 p)
      rw [hY]
    · dsimp only [C, selectedCutPastCuts]
      rw [hR, dite_eq_left i.2.1]
  constructor
  · rw [hrestrict, Measure.map_sum hB]
    apply congrArg Measure.sum
    funext i
    apply Measure.map_congr
    filter_upwards [hagree i] with p hp
    exact congrArg Prod.fst hp
  · rw [hrestrict, Measure.map_sum (hB.prodMk hC.aemeasurable)]
    apply congrArg Measure.sum
    funext i
    exact Measure.map_congr (hagree i)

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
Restrictions are unnormalized and include null branches. -/
theorem selectedCutCodeDistance_positive_joint_kernel_law
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let μ := conditionedVectorPathLaw 0 0
    let S := {p | 0 < selectedCutTime T k p}
    let B := selectedCutCodeDistanceConditioning x T k
    let C := selectedCutPastCuts x T k
    (μ.restrict S).map (fun p => (B p, C p)) =
      (μ.restrict S).map B ⊗ₘ firstHitPastCutsPositiveKernel x := by
  have hmaps := selectedCutCodeDistance_positive_maps x T k hk hT
  dsimp only at hmaps ⊢
  rw [hmaps.2, hmaps.1]
  exact firstHitPositiveBranchesCodeDistance_joint_kernel_law x k

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
This is the product-kernel joint law for the two common-carrier cut outputs. -/
theorem selectedCutCodeDistance_positive_joint_product_kernel_law
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let μ := conditionedVectorPathLaw 0 0
    let S := {p | 0 < selectedCutTime T k p}
    let B := selectedCutCodeDistanceConditioning x T k
    let C := selectedCutPastCuts x T k
    (μ.restrict S).map (fun p => (B p, C p)) =
      (μ.restrict S).map B ⊗ₘ
        ((firstHitPastCutsPositiveKernel x).map Prod.fst ×ₖ
          (firstHitPastCutsPositiveKernel x).map Prod.snd) := by
  have hmaps := selectedCutCodeDistance_positive_maps x T k hk hT
  dsimp only at hmaps ⊢
  rw [hmaps.2, hmaps.1]
  exact firstHitPositiveBranchesCodeDistance_joint_product_kernel_law x k

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
This is the conditional-distribution form on the positive restriction. -/
theorem selectedCutCodeDistance_positive_condDistrib
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let ν := (conditionedVectorPathLaw 0 0).restrict {p | 0 < selectedCutTime T k p}
    let B := selectedCutCodeDistanceConditioning x T k
    let C := selectedCutPastCuts x T k
    condDistrib C B ν =ᵐ[ν.map B] firstHitPastCutsPositiveKernel x := by
  dsimp only
  apply condDistrib_ae_eq_of_measure_eq_compProd
    (aemeasurable_selectedCutCodeDistanceConditioning x T k hT).restrict
    (measurable_selectedCutPastCuts x T k hT).aemeasurable
  exact selectedCutCodeDistance_positive_joint_kernel_law x T k hk hT

/-- positive branch of the cut independence at the source last cut T_{m_k} with the
code-graph XDP distance in the conditioning, for any selector T satisfying the
the source-map distance F_k, the T_0 branch, the grouped 4.13/4.14 source questions
and the one-sided carrier binding are not treated; not the paper result.
This conditional-distribution factorization has the same form as the τ_r helper. -/
theorem selectedCutCodeDistance_positive_conditionalIndependence
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let ν := (conditionedVectorPathLaw 0 0).restrict {p | 0 < selectedCutTime T k p}
    let B := selectedCutCodeDistanceConditioning x T k
    let C := selectedCutPastCuts x T k
    condDistrib C B ν =ᵐ[ν.map B] fun b =>
      (condDistrib (fun p => (C p).1) B ν b).prod
        (condDistrib (fun p => (C p).2) B ν b) := by
  dsimp only
  let ν := (conditionedVectorPathLaw 0 0).restrict {p | 0 < selectedCutTime T k p}
  let B := selectedCutCodeDistanceConditioning x T k
  let C := selectedCutPastCuts x T k
  have hB : AEMeasurable B ν :=
    (aemeasurable_selectedCutCodeDistanceConditioning x T k hT).restrict
  have hC : AEMeasurable C ν := (measurable_selectedCutPastCuts x T k hT).aemeasurable
  have hK : condDistrib C B ν =ᵐ[ν.map B] firstHitPastCutsPositiveKernel x :=
    selectedCutCodeDistance_positive_condDistrib x T k hk hT
  have hP : condDistrib C B ν =ᵐ[ν.map B]
      ((firstHitPastCutsPositiveKernel x).map Prod.fst ×ₖ
        (firstHitPastCutsPositiveKernel x).map Prod.snd) :=
    condDistrib_ae_eq_of_measure_eq_compProd hB hC
      (selectedCutCodeDistance_positive_joint_product_kernel_law x T k hk hT)
  have hL := condDistrib_comp (μ := ν) hB hC measurable_fst
  have hR := condDistrib_comp (μ := ν) hB hC measurable_snd
  filter_upwards [hK, hP, hL, hR] with b hkern hprod hleft hright
  simp only [Function.comp_def] at hleft hright
  rw [hleft, hright, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd, hkern]
  rw [hkern, Kernel.prod_apply, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd] at hprod
  exact hprod

end DirectedDistances.PaperProofs.Section4
