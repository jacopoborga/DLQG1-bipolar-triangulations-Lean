module

public import DirectedDistances.PaperProofs.Section4.FirstHitCutFutureRestriction
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Supporting lemmas for paper labels `lem-finite-ind` (see CORRESPONDENCE.md). -/

/-! the first-hit future-restricted joint kernel laws over positive barrier branches, with
the branch index read from the conditioning variable; the T_{m_k} selector bridge,
the T_0 branch, the source-map distance F_k and the one-sided carrier binding are not
treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Common output carrier for the helper toward lem-finite-ind
This is a helper carrier, not a source definition. -/
abbrev PositiveCutOutput :=
  Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (Σ r : ℕ, AllBoltzmannSpace r)

/-- Common-carrier embedding for the helper toward lem-finite-ind -/
@[expose] def firstHitPositiveCutEmbedding (r : ℕ) :
    (Option (Σ s : ℕ, AllBoltzmannSpace s) × Option (AllBoltzmannSpace r)) →
      PositiveCutOutput :=
  fun c => (c.1, c.2.map (fun m => ⟨r, m⟩))

/-- Fixed-r kernel embedded in the common helper carrier toward lem-finite-ind -/
@[expose] noncomputable def firstHitPastCutsEmbeddedKernel
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    Kernel ((ℕ → ℤ × ℤ) × ℕ) PositiveCutOutput :=
  (firstHitPastCutsKernel x r hr).map (firstHitPositiveCutEmbedding r)

/-- The fixed-r embedded helper kernel toward lem-finite-ind -/
instance firstHitPastCutsEmbeddedKernel_isMarkovKernel
    (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    IsMarkovKernel (firstHitPastCutsEmbeddedKernel x r hr) :=
  Kernel.IsMarkovKernel.map _ (measurable_of_countable _)

/-- Future branch set for the helper toward lem-finite-ind
the T_{m_k} selector bridge and zero branch are not treated. -/
@[expose] def firstHitPositiveBranchFuture (ell r k : ℕ) : Set (ℕ → ℤ × ℤ) :=
  barrierFutureEvent ell r k ∩ {q | q 0 = ((ell : ℤ), -(r : ℤ))}

/-- Measurability of the helper branch set toward lem-finite-ind -/
theorem measurableSet_firstHitPositiveBranchFuture (ell r k : ℕ) :
    MeasurableSet (firstHitPositiveBranchFuture ell r k) :=
  (measurableSet_barrierFutureEvent ell r k).inter
    ((measurable_pi_apply 0) (measurableSet_singleton _))

/-- of the first-hit future-restricted joint kernel laws over positive barrier branches,
with the branch index read from the conditioning variable; the T_{m_k} selector bridge,
the T_0 branch, the source-map distance F_k and the one-sided carrier binding are not
treated; not the paper result. Invalid endpoints receive the fixed junk Dirac law. -/
@[expose] noncomputable def firstHitPastCutsPositiveKernel (x : XDP) :
    Kernel ((ℕ → ℤ × ℤ) × ℕ) PositiveCutOutput := by
  classical
  let f : (ℤ × ℤ) × ℕ → Measure PositiveCutOutput := fun q =>
    if h : 0 ≤ q.1.1 ∧ 1 ≤ (-q.1.2).toNat then
      firstHitPastCutsEmbeddedKernel x (-q.1.2).toNat h.2 ((fun _ => q.1), q.2)
    else Measure.dirac (none, none)
  exact ⟨fun b => f (b.1 0, b.2), (measurable_of_countable f).comp (by fun_prop)⟩

/-- The glued helper kernel toward lem-finite-ind -/
instance firstHitPastCutsPositiveKernel_isMarkovKernel (x : XDP) :
    IsMarkovKernel (firstHitPastCutsPositiveKernel x) where
  isProbabilityMeasure b := by
    classical
    dsimp only [firstHitPastCutsPositiveKernel, Kernel.coe_mk]
    split
    · infer_instance
    · infer_instance

/-- Agreement on a positive branch for the helper toward lem-finite-ind -/
theorem firstHitPastCutsPositiveKernel_apply
    (x : XDP) (ell r : ℕ) (hr : 1 ≤ r) (b : (ℕ → ℤ × ℤ) × ℕ)
    (hb : b.1 0 = ((ell : ℤ), -(r : ℤ))) :
    firstHitPastCutsPositiveKernel x b =
      (firstHitPastCutsKernel x r hr b).map (firstHitPositiveCutEmbedding r) := by
  classical
  let f : (ℤ × ℤ) × ℕ → Measure PositiveCutOutput := fun q =>
    if h : 0 ≤ q.1.1 ∧ 1 ≤ (-q.1.2).toNat then
      firstHitPastCutsEmbeddedKernel x (-q.1.2).toNat h.2 ((fun _ => q.1), q.2)
    else Measure.dirac (none, none)
  change f (b.1 0, b.2) = _
  rw [hb]
  dsimp only [f]
  have hn : (-(-(r : ℤ))).toNat = r := by simp only [neg_neg, Int.toNat_natCast]
  simp only [hn, Nat.cast_nonneg, true_and, dite_eq_left hr]
  rw [firstHitPastCutsEmbeddedKernel, Kernel.map_apply _ (measurable_of_countable _)]
  congr 1
  dsimp only [firstHitPastCutsKernel, Kernel.coe_mk]
  rw [hb]

/-- future-restricted law transported to the common carrier and replaced by the glued
kernel on its branch. The selector, zero branch, source F_k and source carrier
binding are not treated; not the paper result. -/
theorem firstHitPositiveBranch_joint_kernel_law
    (x : XDP) (ell r k : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let M := fun p => stoppedMap r hr (pathCode p)
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
    let C := firstHitPositiveCutEmbedding r ∘ firstHitPastAllCuts x r ∘ M
    let H := firstHitPositiveBranchFuture ell r k
    (μ.restrict (Y ⁻¹' H)).map (fun p => (B p, C p)) =
      ((μ.restrict (Y ⁻¹' H)).map B) ⊗ₘ firstHitPastCutsPositiveKernel x := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let M := fun p => stoppedMap r hr (pathCode p)
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := fun p => (Y p, firstHitPastXdpLength x r (M p))
  let C := firstHitPastAllCuts x r ∘ M
  let H := firstHitPositiveBranchFuture ell r k
  let ν := μ.restrict (Y ⁻¹' H)
  let e := firstHitPositiveCutEmbedding r
  have he : Measurable e := measurable_of_countable _
  have hH : MeasurableSet H := measurableSet_firstHitPositiveBranchFuture ell r k
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hB : Measurable B := hY.prodMk
    ((measurable_firstHitPastXdpLength x r).comp hM)
  have hC : Measurable C := (measurable_firstHitPastAllCuts x r).comp hM
  have hbase : ν.map (fun p => (B p, C p)) =
      (ν.map B) ⊗ₘ firstHitPastCutsKernel x r hr :=
    firstHitPastAllCuts_joint_kernel_law_restrict x r hr hH
  have hindex : ∀ᵐ b ∂ν.map B, b.1 0 = ((ell : ℤ), -(r : ℤ)) := by
    apply (ae_map_iff hB.aemeasurable (by measurability)).2
    filter_upwards [ae_restrict_mem (hY hH)] with p hp
    exact hp.2
  have hk : (firstHitPastCutsKernel x r hr).map e =ᵐ[ν.map B]
      firstHitPastCutsPositiveKernel x := by
    filter_upwards [hindex] with b hb
    rw [Kernel.map_apply _ he]
    exact (firstHitPastCutsPositiveKernel_apply x ell r hr b hb).symm
  let _ := Kernel.IsMarkovKernel.map (firstHitPastCutsKernel x r hr) he
  change ν.map (fun p => (B p, e (C p))) = _
  calc
    _ = (ν.map (fun p => (B p, C p))).map (Prod.map id e) := by
      rw [Measure.map_map (measurable_id.prodMap he) (hB.prodMk hC)]
      rfl
    _ = ((ν.map B) ⊗ₘ firstHitPastCutsKernel x r hr).map (Prod.map id e) := by
      rw [hbase]
    _ = (ν.map B) ⊗ₘ (firstHitPastCutsKernel x r hr).map e :=
      (Measure.compProd_map he).symm
    _ = (ν.map B) ⊗ₘ firstHitPastCutsPositiveKernel x := Measure.compProd_congr hk






abbrev PositiveBranchIx (k : ℕ) := {i : ℕ × ℕ // 1 ≤ i.2 ∧ i.2 ≤ k}

/-- of the first-hit future-restricted joint kernel laws over positive barrier branches,
with the branch index read from the conditioning variable; the T_{m_k} selector bridge,
the T_0 branch, the source-map distance F_k and the one-sided carrier binding are not
treated; not the paper result. -/
theorem firstHitPositiveBranches_joint_kernel_law (x : XDP) (k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := fun r => conditionedSecondCoordinateFirstHit r
    let M := fun i : PositiveBranchIx k => fun p => stoppedMap i.1.2 i.2.1 (pathCode p)
    let Y := fun r p => conditionedVectorShift (τ r p).toNat p
    let B := fun i : PositiveBranchIx k => fun p =>
      (Y i.1.2 p, firstHitPastXdpLength x i.1.2 (M i p))
    let C := fun i : PositiveBranchIx k =>
      firstHitPositiveCutEmbedding i.1.2 ∘ firstHitPastAllCuts x i.1.2 ∘ M i
    let E := fun i : PositiveBranchIx k =>
      Y i.1.2 ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
    Measure.sum (fun i => (μ.restrict (E i)).map (fun p => (B i p, C i p))) =
      (Measure.sum (fun i => (μ.restrict (E i)).map (B i))) ⊗ₘ
        firstHitPastCutsPositiveKernel x := by
  dsimp only
  rw [Measure.compProd_sum_left]
  apply congrArg Measure.sum
  funext i
  exact firstHitPositiveBranch_joint_kernel_law x i.1.1 i.1.2 k i.2.1

private theorem positiveBranch_barriers
    (p : ℕ → ℤ × ℤ) (ell r k : ℕ) (hr : 1 ≤ r)
    (h0 : p 0 = (0, 0))
    (hstep : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hfin : conditionedSecondCoordinateFirstHit r p < ⊤)
    (hp : conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p ∈
      firstHitPositiveBranchFuture ell r k) :
    firstHitBarrier r p ∧ ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s p := by
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  have hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞) := ht.symm
  have hend : (p t).1 = (ell : ℤ) := by
    simpa only [hτ, ENat.toNat_natCast, conditionedVectorShift, Nat.add_zero] using
      congrArg Prod.fst hp.2
  have hdown (n : ℕ) : (p n).2 - 1 ≤ (p (n + 1)).2 := by
    obtain ⟨c, hc⟩ := hstep n
    have hs := congrArg Prod.snd hc
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  apply (firstHitBarrier_positive_decomposition p ell r k t hdown
    (congrArg Prod.snd h0) hr hτ hend).2
  simpa only [hτ, ENat.toNat_natCast] using hp.1

/-- Positive helper branch events toward lem-finite-ind
conditioned path law. Exact disjointness on arbitrary paths is not asserted.
The source selector and zero branch are not treated; not the paper result. -/
theorem firstHitPositiveBranches_pairwise_aedisjoint (k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let Y := fun r p =>
      conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
    let E := fun i : PositiveBranchIx k =>
      Y i.1.2 ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
    Pairwise (fun i j => AEDisjoint μ (E i) (E j)) := by
  dsimp only
  intro i j hij
  rw [AEDisjoint, measure_eq_zero_iff_ae_notMem]
  filter_upwards [conditionedVectorPathLaw_ae_legal,
    firstHitPastMap_finite_hit_ae i.1.2 i.2.1,
    firstHitPastMap_finite_hit_ae j.1.2 j.2.1] with p hlegal hfi hfj
  rintro ⟨hi, hj⟩
  by_cases hr : i.1.2 = j.1.2
  · have hei := congrArg Prod.fst hi.2
    have hej := congrArg Prod.fst hj.2
    dsimp only at hei hej
    rw [hr] at hei
    apply hij
    apply Subtype.ext
    exact Prod.ext (by exact_mod_cast hei.symm.trans hej) hr
  · have hbi := positiveBranch_barriers p i.1.1 i.1.2 k i.2.1
      hlegal.1 hlegal.2 hfi hi
    have hbj := positiveBranch_barriers p j.1.1 j.1.2 k j.2.1
      hlegal.1 hlegal.2 hfj hj
    rcases lt_or_gt_of_ne hr with hlt | hgt
    · exact hbi.2 j.1.2 hlt j.2.2 hbj.1
    · exact hbj.2 i.1.2 hgt i.2.2 hbi.1

/-- The sum of branch restrictions is exactly restriction to their union for the
identify that union with a source renewal event; not the paper result. -/
theorem firstHitPositiveBranches_restrict_union (k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let Y := fun r p =>
      conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
    let E := fun i : PositiveBranchIx k =>
      Y i.1.2 ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
    μ.restrict (⋃ i, E i) = Measure.sum (fun i => μ.restrict (E i)) := by
  dsimp only
  apply Measure.restrict_iUnion_ae (firstHitPositiveBranches_pairwise_aedisjoint k)
  intro i
  exact ((measurable_conditionedFirstHit_future i.1.2)
    (measurableSet_firstHitPositiveBranchFuture i.1.1 i.1.2 k)).nullMeasurableSet

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

/-- assembled on the positive branch union has a product kernel for the two cut outputs
given the future and past length. The branch restrictions are disjoint up to null
sets by `firstHitPositiveBranches_pairwise_aedisjoint`. The T_{m_k} selector bridge,
the T_0 branch, the source-map distance F_k and the one-sided carrier binding are
not treated; not the paper result. -/
theorem firstHitPositiveBranches_joint_product_kernel_law (x : XDP) (k : ℕ) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := fun r => conditionedSecondCoordinateFirstHit r
    let M := fun i : PositiveBranchIx k => fun p => stoppedMap i.1.2 i.2.1 (pathCode p)
    let Y := fun r p => conditionedVectorShift (τ r p).toNat p
    let B := fun i : PositiveBranchIx k => fun p =>
      (Y i.1.2 p, firstHitPastXdpLength x i.1.2 (M i p))
    let C := fun i : PositiveBranchIx k =>
      firstHitPositiveCutEmbedding i.1.2 ∘ firstHitPastAllCuts x i.1.2 ∘ M i
    let E := fun i : PositiveBranchIx k =>
      Y i.1.2 ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
    Measure.sum (fun i => (μ.restrict (E i)).map (fun p => (B i p, C i p))) =
      (Measure.sum (fun i => (μ.restrict (E i)).map (B i))) ⊗ₘ
        ((firstHitPastCutsPositiveKernel x).map Prod.fst ×ₖ
          (firstHitPastCutsPositiveKernel x).map Prod.snd) := by
  dsimp only
  rw [firstHitPositiveBranches_joint_kernel_law x k]
  apply Measure.compProd_congr
  apply Measure.ae_sum_iff.mpr
  intro i
  filter_upwards [positiveBranchKernel_product_ae x i.1.1 i.1.2 k i.2.1] with b hb
  rw [Kernel.prod_apply, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd]
  exact hb

end DirectedDistances.PaperProofs.Section4
