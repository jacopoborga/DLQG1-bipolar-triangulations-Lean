module

public import DirectedDistances.PaperProofs.Section4.PastMapFirstHitKernel
public import DirectedDistances.PaperProofs.Section4.FirstHitPositiveBranchGluing
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! joint kernel law restricted to events of the uncentered future and glued over positive
barrier branches, with the branch index read from the conditioning variable; the
T_{m_k} selector bridge, the T_0 branch and the grouped 4.13 source questions are not
treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem pastMap_compProd_restrict_left
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

/-- past-map joint kernel law restricted to events of the uncentered future and glued over
positive barrier branches, with the branch index read from the conditioning variable;
the T_{m_k} selector bridge, the T_0 branch and the grouped 4.13 source questions are
not treated; not the paper result. This restriction is unnormalized and allows null events. -/
theorem firstHitPastMap_joint_kernel_law_restrict
    (r : ℕ) (hr : 1 ≤ r) {H : Set (ℕ → ℤ × ℤ)} (hH : MeasurableSet H) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let ν := μ[|{p | τ p < ⊤}]
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    (ν.restrict (Y ⁻¹' H)).map (fun p => (Y p, stoppedMap r hr (pathCode p))) =
      (ν.restrict (Y ⁻¹' H)).map Y ⊗ₘ firstHitPastMapKernel r hr := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let ν := μ[|{p | τ p < ⊤}]
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let M := fun p => stoppedMap r hr (pathCode p)
  let Z := fun p => (Y p, M p)
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hZ : Measurable Z := hY.prodMk hM
  have hZset : Z ⁻¹' (H ×ˢ Set.univ) = Y ⁻¹' H := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Z]
  have hbase : ν.map Z = ν.map Y ⊗ₘ firstHitPastMapKernel r hr :=
    firstHitPastMap_joint_kernel_law r hr
  change (ν.restrict (Y ⁻¹' H)).map Z = _
  calc
    _ = (ν.map Z).restrict (H ×ˢ Set.univ) := by
      rw [Measure.restrict_map hZ (hH.prod MeasurableSet.univ), hZset]
    _ = (ν.map Y ⊗ₘ firstHitPastMapKernel r hr).restrict (H ×ˢ Set.univ) := by
      rw [hbase]
    _ = ((ν.map Y).restrict H) ⊗ₘ firstHitPastMapKernel r hr :=
      (pastMap_compProd_restrict_left (ν.map Y) (firstHitPastMapKernel r hr) hH).symm
    _ = (ν.restrict (Y ⁻¹' H)).map Y ⊗ₘ firstHitPastMapKernel r hr := by
      rw [Measure.restrict_map hY hH]

/-- Common discrete helper carrier toward lem-past-map
This is not a source definition or the paper result. -/
abbrev PositivePastMapOutput := Option (Σ r : ℕ, AllBoltzmannSpace r)

/-- Common-carrier embedding for the helper toward lem-past-map -/
@[expose] def firstHitPositivePastMapEmbedding (r : ℕ) :
    Option (AllBoltzmannSpace r) → PositivePastMapOutput :=
  fun o => o.map (fun m => ⟨r, m⟩)

/-- Transported fixed-level helper kernel toward lem-past-map -/
@[expose] noncomputable def firstHitPastMapEmbeddedKernel (r : ℕ) (hr : 1 ≤ r) :
    Kernel (ℕ → ℤ × ℤ) PositivePastMapOutput :=
  (firstHitPastMapKernel r hr).map (firstHitPositivePastMapEmbedding r)

/-- The transported helper kernel toward lem-past-map -/
instance firstHitPastMapEmbeddedKernel_isMarkovKernel (r : ℕ) (hr : 1 ≤ r) :
    IsMarkovKernel (firstHitPastMapEmbeddedKernel r hr) :=
  Kernel.IsMarkovKernel.map _ (measurable_of_countable _)

/-- past-map joint kernel law restricted to events of the uncentered future and glued over
positive barrier branches, with the branch index read from the conditioning variable;
the T_{m_k} selector bridge, the T_0 branch and the grouped 4.13 source questions are
not treated; not the paper result. Invalid endpoints receive the junk Dirac law.
This kernel is a helper object, not a source definition. -/
@[expose] noncomputable def firstHitPastMapPositiveKernel :
    Kernel (ℕ → ℤ × ℤ) PositivePastMapOutput := by
  classical
  let f : ℤ × ℤ → Measure PositivePastMapOutput := fun q =>
    if h : 0 ≤ q.1 ∧ 1 ≤ (-q.2).toNat then
      firstHitPastMapEmbeddedKernel (-q.2).toNat h.2 (fun _ => q)
    else Measure.dirac none
  exact ⟨fun y => f (y 0), (measurable_of_countable f).comp (measurable_pi_apply 0)⟩

/-- The glued helper kernel toward lem-past-map -/
instance firstHitPastMapPositiveKernel_isMarkovKernel :
    IsMarkovKernel firstHitPastMapPositiveKernel where
  isProbabilityMeasure y := by
    classical
    dsimp only [firstHitPastMapPositiveKernel, Kernel.coe_mk]
    split <;> infer_instance

/-- Agreement on each positive helper branch toward lem-past-map -/
theorem firstHitPastMapPositiveKernel_apply
    (ell r : ℕ) (hr : 1 ≤ r) (y : ℕ → ℤ × ℤ)
    (hy : y 0 = ((ell : ℤ), -(r : ℤ))) :
    firstHitPastMapPositiveKernel y =
      (firstHitPastMapKernel r hr y).map (firstHitPositivePastMapEmbedding r) := by
  classical
  let f : ℤ × ℤ → Measure PositivePastMapOutput := fun q =>
    if h : 0 ≤ q.1 ∧ 1 ≤ (-q.2).toNat then
      firstHitPastMapEmbeddedKernel (-q.2).toNat h.2 (fun _ => q)
    else Measure.dirac none
  change f (y 0) = _
  rw [hy]
  dsimp only [f]
  have hn : (-(-(r : ℤ))).toNat = r := by simp only [neg_neg, Int.toNat_natCast]
  simp only [hn, Nat.cast_nonneg, true_and, dite_eq_left hr]
  rw [firstHitPastMapEmbeddedKernel, Kernel.map_apply _ (measurable_of_countable _)]
  congr 1
  dsimp only [firstHitPastMapKernel, Kernel.coe_mk]
  simp only [hy]

/-- past-map joint kernel law restricted to events of the uncentered future and glued over
positive barrier branches, with the branch index read from the conditioning variable;
the T_{m_k} selector bridge, the T_0 branch and the grouped 4.13 source questions are
not treated; not the paper result. This is the transported law on one helper branch. -/
theorem firstHitPastMapPositiveBranch_joint_kernel_law
    (ell r k : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let H := firstHitPositiveBranchFuture ell r k
    (μ.restrict (Y ⁻¹' H)).map
        (fun p => (Y p, firstHitPositivePastMapEmbedding r (M p))) =
      (μ.restrict (Y ⁻¹' H)).map Y ⊗ₘ firstHitPastMapPositiveKernel := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let H := firstHitPositiveBranchFuture ell r k
  let ν := μ.restrict (Y ⁻¹' H)
  let e := firstHitPositivePastMapEmbedding r
  have he : Measurable e := measurable_of_countable _
  have hH : MeasurableSet H := measurableSet_firstHitPositiveBranchFuture ell r k
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hbase : ν.map (fun p => (Y p, M p)) =
      (ν.map Y) ⊗ₘ firstHitPastMapKernel r hr := by
    have h := firstHitPastMap_joint_kernel_law_restrict r hr hH
    dsimp only at h
    rwa [firstHitPastMap_cond_finite_hit_eq r hr] at h
  have hindex : ∀ᵐ y ∂ν.map Y, y 0 = ((ell : ℤ), -(r : ℤ)) := by
    apply (ae_map_iff hY.aemeasurable (by measurability)).2
    filter_upwards [ae_restrict_mem (hY hH)] with p hp
    exact hp.2
  have hk : (firstHitPastMapKernel r hr).map e =ᵐ[ν.map Y]
      firstHitPastMapPositiveKernel := by
    filter_upwards [hindex] with y hy
    rw [Kernel.map_apply _ he]
    exact (firstHitPastMapPositiveKernel_apply ell r hr y hy).symm
  let _ := Kernel.IsMarkovKernel.map (firstHitPastMapKernel r hr) he
  change ν.map (fun p => (Y p, e (M p))) = _
  calc
    _ = (ν.map (fun p => (Y p, M p))).map (Prod.map id e) := by
      rw [Measure.map_map (measurable_id.prodMap he) (hY.prodMk hM)]
      rfl
    _ = ((ν.map Y) ⊗ₘ firstHitPastMapKernel r hr).map (Prod.map id e) := by
      rw [hbase]
    _ = (ν.map Y) ⊗ₘ (firstHitPastMapKernel r hr).map e :=
      (Measure.compProd_map he).symm
    _ = (ν.map Y) ⊗ₘ firstHitPastMapPositiveKernel := Measure.compProd_congr hk

/-- past-map joint kernel law restricted to events of the uncentered future and glued over
positive barrier branches, with the branch index read from the conditioning variable;
the T_{m_k} selector bridge, the T_0 branch and the grouped 4.13 source questions are
not treated; not the paper result. The imported helper index includes `ell = 0`.
No positive-mass premise or identification with a source renewal event is used. -/
theorem firstHitPastMapPositiveBranches_joint_kernel_law (k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := fun r => conditionedSecondCoordinateFirstHit r
    let M := fun i : PositiveBranchIx k => fun p => stoppedMap i.1.2 i.2.1 (pathCode p)
    let Y := fun r p => conditionedVectorShift (τ r p).toNat p
    let C := fun i : PositiveBranchIx k => firstHitPositivePastMapEmbedding i.1.2 ∘ M i
    let E := fun i : PositiveBranchIx k =>
      Y i.1.2 ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
    Measure.sum (fun i => (μ.restrict (E i)).map (fun p => (Y i.1.2 p, C i p))) =
      (Measure.sum (fun i => (μ.restrict (E i)).map (Y i.1.2))) ⊗ₘ
        firstHitPastMapPositiveKernel := by
  dsimp only
  rw [Measure.compProd_sum_left]
  apply congrArg Measure.sum
  funext i
  exact firstHitPastMapPositiveBranch_joint_kernel_law i.1.1 i.1.2 k i.2.1

end DirectedDistances.PaperProofs.Section4
