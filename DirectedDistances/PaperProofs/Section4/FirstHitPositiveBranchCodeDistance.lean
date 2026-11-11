module

public import DirectedDistances.PaperProofs.Section4.FirstHitPositiveBranchGluing
public import DirectedDistances.PaperProofs.Section4.FirstHitCodeDistanceIndependence






public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal





theorem firstHitPositiveBranchCodeDistance_joint_kernel_law
    (x : XDP) (ell r k : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let Bc := firstHitCodeDistanceConditioning x r hr
    let C := firstHitPositiveCutEmbedding r ∘ firstHitPastAllCuts x r ∘ M
    let H := firstHitPositiveBranchFuture ell r k
    (μ.restrict (Y ⁻¹' H)).map (fun p => (Bc p, C p)) =
      ((μ.restrict (Y ⁻¹' H)).map Bc) ⊗ₘ firstHitPastCutsPositiveKernel x := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let Bc := firstHitCodeDistanceConditioning x r hr
  let C := firstHitPositiveCutEmbedding r ∘ firstHitPastAllCuts x r ∘ M
  let H := firstHitPositiveBranchFuture ell r k
  let ν := μ.restrict (Y ⁻¹' H)
  have hEq : Bc =ᵐ[μ] B := by
    simpa only [Bc, B, Y, M, μ] using
      firstHitCodeDistanceConditioning_ae_eq_pastConditioning x r hr
  have hEqν : Bc =ᵐ[ν] B := ae_restrict_of_ae hEq
  have hpair : (fun p => (Bc p, C p)) =ᵐ[ν] fun p => (B p, C p) := by
    filter_upwards [hEqν] with p hp
    exact congrArg (fun b => (b, C p)) hp
  have hbase := firstHitPositiveBranch_joint_kernel_law x ell r k hr
  dsimp only at hbase
  calc
    ν.map (fun p => (Bc p, C p)) = ν.map (fun p => (B p, C p)) :=
      Measure.map_congr hpair
    _ = (ν.map B) ⊗ₘ firstHitPastCutsPositiveKernel x := hbase
    _ = (ν.map Bc) ⊗ₘ firstHitPastCutsPositiveKernel x := by
      rw [← Measure.map_congr hEqν]





theorem firstHitPositiveBranchesCodeDistance_joint_kernel_law (x : XDP) (k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := fun r => conditionedSecondCoordinateFirstHit r
    let M := fun i : PositiveBranchIx k =>
      fun p => stoppedMap i.1.2 i.2.1 (pathCode p)
    let Y := fun r p => conditionedVectorShift (τ r p).toNat p
    let Bc := fun i : PositiveBranchIx k =>
      firstHitCodeDistanceConditioning x i.1.2 i.2.1
    let C := fun i : PositiveBranchIx k =>
      firstHitPositiveCutEmbedding i.1.2 ∘ firstHitPastAllCuts x i.1.2 ∘ M i
    let E := fun i : PositiveBranchIx k =>
      Y i.1.2 ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
    Measure.sum (fun i => (μ.restrict (E i)).map (fun p => (Bc i p, C i p))) =
      (Measure.sum (fun i => (μ.restrict (E i)).map (Bc i))) ⊗ₘ
        firstHitPastCutsPositiveKernel x := by
  dsimp only
  rw [Measure.compProd_sum_left]
  apply congrArg Measure.sum
  funext i
  exact firstHitPositiveBranchCodeDistance_joint_kernel_law x i.1.1 i.1.2 k i.2.1

private theorem fixedCutKernel_product_ae (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    ∀ᵐ b ∂μ.map B, firstHitPastCutsKernel x r hr b =
      ((firstHitPastCutsKernel x r hr b).map Prod.fst).prod
        ((firstHitPastCutsKernel x r hr b).map Prod.snd) := by
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
  have hI := firstHitPastAllCuts_conditionalIndependence x r hr
  have hL := condDistrib_comp (μ := μ) hB.aemeasurable hC.aemeasurable measurable_fst
  have hR := condDistrib_comp (μ := μ) hB.aemeasurable hC.aemeasurable measurable_snd
  change ∀ᵐ b ∂μ.map B, _
  filter_upwards [hK, hI, hL, hR] with b hk hi hl hright
  simp only [Function.comp_def] at hl hright
  rw [hl, hright, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd, hk] at hi
  exact hi

private theorem embeddedCutKernel_product
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) (b : (ℕ → ℤ × ℤ) × ℕ)
    (h : firstHitPastCutsKernel x r hr b =
      ((firstHitPastCutsKernel x r hr b).map Prod.fst).prod
        ((firstHitPastCutsKernel x r hr b).map Prod.snd)) :
    firstHitPastCutsEmbeddedKernel x r hr b =
      ((firstHitPastCutsEmbeddedKernel x r hr b).map Prod.fst).prod
        ((firstHitPastCutsEmbeddedKernel x r hr b).map Prod.snd) := by
  let ν := firstHitPastCutsKernel x r hr b
  let g : Option (AllBoltzmannSpace r) → Option (Σ t : ℕ, AllBoltzmannSpace t) :=
    fun o => o.map (fun m => ⟨r, m⟩)
  have hg : Measurable g := measurable_of_countable _
  have he : Measurable (firstHitPositiveCutEmbedding r) := measurable_of_countable _
  have hI : IndepFun Prod.fst Prod.snd ν := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable).2
    change ν.map id = _
    rw [Measure.map_id]
    exact h
  have hi := (hI.comp measurable_id hg).map_prod_eq_prod_map_map
    measurable_fst.aemeasurable (hg.comp measurable_snd).aemeasurable
  rw [firstHitPastCutsEmbeddedKernel, Kernel.map_apply _ he,
    Measure.map_map measurable_fst he, Measure.map_map measurable_snd he]
  exact hi

private theorem positiveBranchKernel_product_ae
    (x : XDP) (ell r k : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let H := firstHitPositiveBranchFuture ell r k
    ∀ᵐ b ∂(μ.restrict (Y ⁻¹' H)).map B,
      firstHitPastCutsPositiveKernel x b =
        ((firstHitPastCutsPositiveKernel x b).map Prod.fst).prod
          ((firstHitPastCutsPositiveKernel x b).map Prod.snd) := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let H := firstHitPositiveBranchFuture ell r k
  let ν := μ.restrict (Y ⁻¹' H)
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hB : Measurable B := hY.prodMk
    ((measurable_firstHitPastXdpLength x r).comp hM)
  have hH := measurableSet_firstHitPositiveBranchFuture ell r k
  have hindex : ∀ᵐ b ∂ν.map B, b.1 0 = ((ell : ℤ), -(r : ℤ)) := by
    apply (ae_map_iff hB.aemeasurable (by measurability)).2
    filter_upwards [ae_restrict_mem (hY hH)] with p hp
    exact hp.2
  have hprod := (Measure.absolutelyContinuous_of_le
    (Measure.map_mono (show ν ≤ μ from Measure.restrict_le_self) hB)).ae_le
      (fixedCutKernel_product_ae x r hr)
  change ∀ᵐ b ∂ν.map B, _
  filter_upwards [hindex, hprod] with b hb hp
  rw [firstHitPastCutsPositiveKernel_apply x ell r hr b hb]
  have he : Measurable (firstHitPositiveCutEmbedding r) := measurable_of_countable _
  simpa only [firstHitPastCutsEmbeddedKernel, Kernel.map_apply _ he] using
    embeddedCutKernel_product x r hr b hp





theorem firstHitPositiveBranchesCodeDistance_joint_product_kernel_law
    (x : XDP) (k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := fun r => conditionedSecondCoordinateFirstHit r
    let M := fun i : PositiveBranchIx k =>
      fun p => stoppedMap i.1.2 i.2.1 (pathCode p)
    let Y := fun r p => conditionedVectorShift (τ r p).toNat p
    let Bc := fun i : PositiveBranchIx k =>
      firstHitCodeDistanceConditioning x i.1.2 i.2.1
    let C := fun i : PositiveBranchIx k =>
      firstHitPositiveCutEmbedding i.1.2 ∘ firstHitPastAllCuts x i.1.2 ∘ M i
    let E := fun i : PositiveBranchIx k =>
      Y i.1.2 ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
    Measure.sum (fun i => (μ.restrict (E i)).map (fun p => (Bc i p, C i p))) =
      (Measure.sum (fun i => (μ.restrict (E i)).map (Bc i)) ⊗ₘ
        ((firstHitPastCutsPositiveKernel x).map Prod.fst ×ₖ
          (firstHitPastCutsPositiveKernel x).map Prod.snd)) := by
  dsimp only
  rw [firstHitPositiveBranchesCodeDistance_joint_kernel_law x k]
  apply Measure.compProd_congr
  apply Measure.ae_sum_iff.mpr
  intro i
  let μ := conditionedVectorPathLaw 0 0
  let M := fun p => stoppedMap i.1.2 i.2.1 (pathCode p)
  let Y := fun p =>
    conditionedVectorShift (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p
  let B := fun p =>
    (Y p, firstHitPastXdpLength x i.1.2 (M p))
  let Bc := firstHitCodeDistanceConditioning x i.1.2 i.2.1
  let H := firstHitPositiveBranchFuture i.1.1 i.1.2 k
  let ν := μ.restrict (Y ⁻¹' H)
  have hEq : Bc =ᵐ[μ] B := by
    simpa only [Bc, B, Y, M, μ] using
      firstHitCodeDistanceConditioning_ae_eq_pastConditioning x i.1.2 i.2.1
  have hEqν : Bc =ᵐ[ν] B := ae_restrict_of_ae hEq
  have hMap : ν.map Bc = ν.map B := Measure.map_congr hEqν
  have hprod := positiveBranchKernel_product_ae x i.1.1 i.1.2 k i.2.1
  have hprodCode : ∀ᵐ b ∂ν.map Bc,
    firstHitPastCutsPositiveKernel x b =
      ((firstHitPastCutsPositiveKernel x b).map Prod.fst).prod
        ((firstHitPastCutsPositiveKernel x b).map Prod.snd) := by
    rw [hMap]
    exact hprod
  filter_upwards [hprodCode] with b hb
  rw [Kernel.prod_apply, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd]
  exact hb

end DirectedDistances.PaperProofs.Section4
