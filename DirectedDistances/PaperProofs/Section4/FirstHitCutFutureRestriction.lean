module

public import DirectedDistances.PaperProofs.Section4.FinitePastIndependenceFirstHitKernel
public import DirectedDistances.RandomWalk.FirstHitBarrierDecomposition

/-! kernel law restricted to a measurable event of the uncentered future (positive last-cut
branch selection); the random-index gluing, the T_0 branch and the source carrier binding
are not treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem measure_compProd_restrict_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [SFinite ν] (κ : Kernel α β) [IsSFiniteKernel κ]
    {s : Set α} (hs : MeasurableSet s) :
    (ν.restrict s) ⊗ₘ κ = (ν ⊗ₘ κ).restrict (s ×ˢ Set.univ) := by
  change (Kernel.const Unit (ν.restrict s) ⊗ₖ Kernel.prodMkLeft Unit κ) () =
    ((Kernel.const Unit ν ⊗ₖ Kernel.prodMkLeft Unit κ) ()).restrict
      (s ×ˢ Set.univ)
  rw [← Kernel.restrict_apply (Kernel.const Unit ν ⊗ₖ Kernel.prodMkLeft Unit κ)
    (hs.prod MeasurableSet.univ) ()]
  rw [← Kernel.compProd_restrict_left hs, Kernel.restrict_const hs]

/-- kernel law restricted to a measurable event of the uncentered future (positive last-cut
branch selection); the random-index gluing, the T_0 branch and the source carrier binding
are not treated; not the paper result. -/
theorem firstHitPastAllCuts_joint_kernel_law_restrict
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) {H : Set (ℕ → ℤ × ℤ)}
    (hH : MeasurableSet H) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    (μ.restrict (Y ⁻¹' H)).map (fun p => (B p, C p)) =
      ((μ.restrict (Y ⁻¹' H)).map B) ⊗ₘ firstHitPastCutsKernel x r hr := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let C := firstHitPastAllCuts x r ∘ M
  let Z := fun p => (B p, C p)
  let S : Set (((ℕ → ℤ × ℤ) × ℕ) ×
      (Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r))) :=
    (H ×ˢ (Set.univ : Set ℕ)) ×ˢ Set.univ
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hB : Measurable B := hY.prodMk
    ((measurable_firstHitPastXdpLength x r).comp hM)
  have hC : Measurable C := (measurable_firstHitPastAllCuts x r).comp hM
  have hZ : Measurable Z := hB.prodMk hC
  have hS : MeasurableSet S := (hH.prod MeasurableSet.univ).prod
    MeasurableSet.univ
  have hBset : B ⁻¹' (H ×ˢ Set.univ) = Y ⁻¹' H := by
    ext p
    simp [B]
  have hZset : Z ⁻¹' S = Y ⁻¹' H := by
    ext p
    simp [Z, S, B]
  have hbase := firstHitPastAllCuts_joint_kernel_law x r hr
  dsimp only at hbase
  have hleft := Measure.restrict_map (μ := μ) hZ hS
  have hfirst := Measure.restrict_map (μ := μ) hB (hH.prod MeasurableSet.univ)
  change μ.map Z = μ.map B ⊗ₘ firstHitPastCutsKernel x r hr at hbase
  change (μ.restrict (Y ⁻¹' H)).map Z =
    ((μ.restrict (Y ⁻¹' H)).map B) ⊗ₘ firstHitPastCutsKernel x r hr
  calc
    _ = (μ.map Z).restrict S := by rw [← hZset, ← hleft]
    _ = (μ.map B ⊗ₘ firstHitPastCutsKernel x r hr).restrict S := by rw [hbase]
    _ = ((μ.map B).restrict (H ×ˢ Set.univ)) ⊗ₘ
        firstHitPastCutsKernel x r hr := by
      exact (measure_compProd_restrict_left (ν := μ.map B)
        (firstHitPastCutsKernel x r hr) (hH.prod MeasurableSet.univ)).symm
    _ = ((μ.restrict (Y ⁻¹' H)).map B) ⊗ₘ
        firstHitPastCutsKernel x r hr := by rw [← hBset, ← hfirst]

/-- kernel law restricted to a measurable event of the uncentered future (positive last-cut
branch selection); the random-index gluing, the T_0 branch and the source carrier binding
are not treated; not the paper result. -/
theorem firstHitPastAllCuts_joint_kernel_law_barrier
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) (ell k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPastAllCuts x r ∘ M
    let H := barrierFutureEvent ell r k
    (μ.restrict (Y ⁻¹' H)).map (fun p => (B p, C p)) =
      ((μ.restrict (Y ⁻¹' H)).map B) ⊗ₘ firstHitPastCutsKernel x r hr := by
  dsimp only
  exact firstHitPastAllCuts_joint_kernel_law_restrict x r hr
    (measurableSet_barrierFutureEvent ell r k)

end DirectedDistances.PaperProofs.Section4
