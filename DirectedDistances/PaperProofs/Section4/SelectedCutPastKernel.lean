/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ZeroEdgeMarkedPast
public import DirectedDistances.PaperProofs.Section4.SelectedCutWalkPrefix
public import DirectedDistances.PaperProofs.Section4.SelectedCutTimePartition
public import DirectedDistances.PaperProofs.Section4.FirstHitPastMapBranchGluing
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Full-scope selected-cut past kernel helpers toward Lemma 4.13. These are not a -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
Embed the stopped-map output in the ruling's zero-or-positive carrier. -/
@[expose] noncomputable def selectedCutPastOutputToCarrier :
    PositivePastMapOutput → SelectedCutPastMap := fun o =>
  match o with
  | none => Sum.inl zeroEdgeMarkedPast
  | some ⟨r, ⟨ell, m⟩⟩ =>
      if hr : 1 ≤ r then
        if hell : 1 ≤ ell then
          Sum.inr ⟨⟨ell, hell⟩, ⟨⟨r, hr⟩, m⟩⟩
        else Sum.inl zeroEdgeMarkedPast
      else Sum.inl zeroEdgeMarkedPast

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The full stopped-past map, including the one-vertex zero past. -/
@[expose] noncomputable def selectedCutPastMapFull
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (p : ℕ → ℤ × ℤ) : SelectedCutPastMap :=
  selectedCutPastOutputToCarrier (selectedCutPastMap T k p)

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The past-map kernel on the ruling's zero-or-positive carrier.
The zero output of the existing positive-branch kernel is sent to the -/
@[expose] noncomputable def selectedCutMapKernel :
    Kernel (ℕ → ℤ × ℤ) SelectedCutPastMap :=
  firstHitPastMapPositiveKernel.map selectedCutPastOutputToCarrier

instance selectedCutMapKernel_isSFinite : IsSFiniteKernel selectedCutMapKernel := by
  dsimp [selectedCutMapKernel]
  infer_instance

instance selectedCutMapKernel_isMarkov : IsMarkovKernel selectedCutMapKernel := by
  dsimp [selectedCutMapKernel]
  exact Kernel.IsMarkovKernel.map _ (measurable_of_countable _)

instance : Countable ZeroEdgeMarkedPast :=
  (⟨fun _ => PUnit.unit, by
    intro a b
    cases a
    cases b
    intro _
    rfl⟩ : ZeroEdgeMarkedPast ↪ PUnit.{0}).countable

noncomputable instance selectedCutPastMap_countable : Countable SelectedCutPastMap := by
  dsimp [SelectedCutPastMap, PositiveSelectedCutPastMap]
  infer_instance

instance selectedCutPastMap_nonempty : Nonempty SelectedCutPastMap :=
  ⟨Sum.inl zeroEdgeMarkedPast⟩

noncomputable instance selectedCutPastMap_standardBorel :
    StandardBorelSpace SelectedCutPastMap := by
  exact standardBorelSpace_of_discreteMeasurableSpace

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
At the zero selected future, the past-map kernel is the point mass at the -/
theorem selectedCutMapKernel_zero (y : ℕ → ℤ × ℤ)
    (hy : y 0 = (0, 0)) :
    selectedCutMapKernel y = Measure.dirac
      (Sum.inl zeroEdgeMarkedPast : SelectedCutPastMap) := by
  classical
  rw [selectedCutMapKernel, Kernel.map_apply _ (measurable_of_countable _)]
  rw [firstHitPastMapPositiveKernel]
  simp [hy, selectedCutPastOutputToCarrier]

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
Under the actual selected-cut law, the kernel is evaluated only at the origin -/
theorem selectedCutMapKernel_valid_endpoint_ae (k : ℕ) (hk : 1 ≤ k) :
    let μ := conditionedVectorPathLaw 0 0
    let Y := selectedCutFuture Paper.Section4.renewalTime k
    ∀ᵐ y ∂μ.map Y,
      y 0 = (0, 0) ∨
        (1 ≤ (y 0).1 ∧ 1 ≤ (-(y 0).2).toNat) := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let T := Paper.Section4.renewalTime
  let Y := selectedCutFuture T k
  have hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p) :=
    fun p m => (renewalTime_characterization m p).1
  have hbranches := selectedCutTime_positive_event_ae T k hk hT
  have hfinite : ∀ᵐ p ∂μ, ∀ i : PositiveBranchIx k,
      conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ := by
    apply ae_all_iff.mpr
    intro i
    exact firstHitPastMap_finite_hit_ae i.1.2 i.2.1
  have hleft : ∀ᵐ p ∂μ, ∀ i : PositiveBranchIx k,
      1 ≤ (p (conditionedSecondCoordinateFirstHit i.1.2 p).toNat).1 := by
    apply ae_all_iff.mpr
    intro i
    have h := firstHitPastMap_left_pos_ae i.1.2 i.2.1
    dsimp only at h
    rw [firstHitPastMap_cond_finite_hit_eq i.1.2 i.2.1] at h
    exact h
  have hbranchEq : ∀ᵐ p ∂μ, ∀ i : PositiveBranchIx k,
      (selectedCutTime T k p = conditionedSecondCoordinateFirstHit i.1.2 p ∧
        conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit i.1.2 p).toNat).1 =
          (i.1.1 : ℤ)) ↔
      (conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ ∧
        conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p ∈
          firstHitPositiveBranchFuture i.1.1 i.1.2 k) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [selectedCutTime_positiveBranch_event_ae T k i.1.2 i.1.1
      i.2.1 i.2.2 hT] with p hp
    exact Iff.of_eq hp
  have hlegal := conditionedVectorPathLaw_ae_legal
  apply (ae_map_iff (measurable_selectedCutFuture T k hT).aemeasurable
    (by measurability)).2
  filter_upwards [hbranches, hfinite, hleft, hbranchEq, hlegal]
    with p hp hfiniteP hleftP hbranchP hlegalP
  by_cases hpos : 0 < selectedCutTime T k p
  · have hpUnion : p ∈ ⋃ i : PositiveBranchIx k,
        (fun q => conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 q).toNat q) ⁻¹'
          firstHitPositiveBranchFuture i.1.1 i.1.2 k := by
      exact (Iff.of_eq hp).mp hpos
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpUnion
    have hpoint : conditionedVectorShift
        (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p 0 =
          ((i.1.1 : ℤ), -(i.1.2 : ℤ)) := hi.2
    have hbranch := (hbranchP i).mpr ⟨hfiniteP i, hi⟩
    have htime := hbranch.1
    have hfuture : Y p = conditionedVectorShift
        (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p := by
      change conditionedVectorShift (selectedCutTime T k p).toNat p = _
      rw [htime]
    have hleftEndpoint : (1 : ℤ) ≤
        (conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p 0).1 := by
      simpa [conditionedVectorShift] using (hleftP i)
    have hleftEq := congrArg Prod.fst hpoint
    rw [hleftEq] at hleftEndpoint
    change Y p 0 = (0, 0) ∨
      (1 ≤ (Y p 0).1 ∧ 1 ≤ (-(Y p 0).2).toNat)
    rw [hfuture, hpoint]
    exact Or.inr ⟨hleftEndpoint,
      by simp only [neg_neg, Int.toNat_natCast]; exact i.2.1⟩
  · have hzero : selectedCutTime T k p = 0 := by
      exact le_antisymm (le_of_not_gt hpos) bot_le
    have hfuture : Y p 0 = (0, 0) := by
      simp [Y, selectedCutFuture, hzero, conditionedVectorShift, hlegalP.1]
    exact Or.inl hfuture

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
Transport one fixed right-boundary map carrier to the full selected-past -/
@[expose] noncomputable def selectedCutFixedLevelToCarrier
    (r : ℕ) (hr : 1 ≤ r) :
    Option (AllBoltzmannSpace r) → SelectedCutPastMap := fun o =>
  match o with
  | none => Sum.inl zeroEdgeMarkedPast
  | some ⟨ell, m⟩ =>
      if hell : 1 ≤ ell then
        Sum.inr ⟨⟨ell, hell⟩, ⟨⟨r, hr⟩, m⟩⟩
      else Sum.inl zeroEdgeMarkedPast

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
At future initial coordinate `(ell,-r)`, the full map kernel is the fixed
first-hit map kernel
transported to the ruling's zero-or-positive carrier. Source: -/
theorem selectedCutMapKernel_positive
    (ell r : ℕ) (hr : 1 ≤ r)
    (y : ℕ → ℤ × ℤ)
    (hy : y 0 = ((ell : ℤ), -(r : ℤ))) :
    selectedCutMapKernel y =
      (firstHitPastMapKernel r hr y).map
        (selectedCutFixedLevelToCarrier r hr) := by
  classical
  rw [selectedCutMapKernel, Kernel.map_apply _ (measurable_of_countable _)]
  rw [firstHitPastMapPositiveKernel_apply ell r hr y hy]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext o
  change selectedCutPastOutputToCarrier
    (firstHitPositivePastMapEmbedding r o) =
      selectedCutFixedLevelToCarrier r hr o
  cases o with
  | none => rfl
  | some q =>
      rcases q with ⟨ell', m⟩
      by_cases h : 1 ≤ ell'
      · change selectedCutPastOutputToCarrier
          (some ⟨r, ⟨ell', m⟩⟩) =
            selectedCutFixedLevelToCarrier r hr (some ⟨ell', m⟩)
        simp [selectedCutPastOutputToCarrier,
          selectedCutFixedLevelToCarrier, hr, h]
      · change selectedCutPastOutputToCarrier
          (some ⟨r, ⟨ell', m⟩⟩) =
            selectedCutFixedLevelToCarrier r hr (some ⟨ell', m⟩)
        simp [selectedCutPastOutputToCarrier,
          selectedCutFixedLevelToCarrier, hr, h]

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
When the selected cut time is zero, the selected past is the point object. -/
theorem selectedCutPastMapFull_zero_ae
    (k : ℕ) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      selectedCutTime Paper.Section4.renewalTime k p = 0 →
        selectedCutPastMapFull Paper.Section4.renewalTime k p =
          Sum.inl zeroEdgeMarkedPast := by
  filter_upwards [conditionedVectorPathLaw_ae_legal] with p hp
  intro htime
  have hfuture : selectedCutFuture Paper.Section4.renewalTime k p 0 =
      (0, 0) := by
    simp [selectedCutFuture, conditionedVectorShift, htime, hp.1]
  simp [selectedCutPastMapFull, selectedCutPastOutputToCarrier,
    selectedCutPastMap, hfuture]

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The joint law of the selected future and full past map factors on the positive -/
theorem selectedCutPastMapFull_positive_joint_kernel_law
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let μ := conditionedVectorPathLaw 0 0
    let S := {p | 0 < selectedCutTime T k p}
    let Y := selectedCutFuture T k
    (μ.restrict S).map (fun p => (Y p, selectedCutPastMapFull T k p)) =
      (μ.restrict S).map Y ⊗ₘ selectedCutMapKernel := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let S := {p | 0 < selectedCutTime T k p}
  let Y := selectedCutFuture T k
  let C := selectedCutPastMap T k
  have hbase := selectedCutPastMap_positive_joint_kernel_law T k hk hT
  have hY : Measurable Y := measurable_selectedCutFuture T k hT
  have hC : Measurable C := measurable_selectedCutPastMap T k hT
  have he : Measurable selectedCutPastOutputToCarrier :=
    measurable_of_countable _
  calc
    (μ.restrict S).map (fun p => (Y p, selectedCutPastMapFull T k p)) =
        ((μ.restrict S).map (fun p => (Y p, C p))).map
          (Prod.map id selectedCutPastOutputToCarrier) := by
      rw [Measure.map_map (measurable_id.prodMap he) (hY.prodMk hC)]
      rfl
    _ = ((μ.restrict S).map Y ⊗ₘ firstHitPastMapPositiveKernel).map
        (Prod.map id selectedCutPastOutputToCarrier) := by
      rw [hbase]
    _ = (μ.restrict S).map Y ⊗ₘ selectedCutMapKernel := by
      exact (Measure.compProd_map he).symm

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The full selected-past joint law, including the zero-time point branch. -/
theorem selectedCutPastMapFull_joint_kernel_law
    (k : ℕ) (hk : 1 ≤ k) :
    let μ := conditionedVectorPathLaw 0 0
    let Y := selectedCutFuture Paper.Section4.renewalTime k
    let P := selectedCutPastMapFull Paper.Section4.renewalTime k
    μ.map (fun p => (Y p, P p)) = μ.map Y ⊗ₘ selectedCutMapKernel := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let T := Paper.Section4.renewalTime
  let Y := selectedCutFuture T k
  let P := selectedCutPastMapFull T k
  let Z := {p | selectedCutTime T k p = (0 : ℕ∞)}
  let S := {p | 0 < selectedCutTime T k p}
  let z₀ : SelectedCutPastMap := Sum.inl zeroEdgeMarkedPast
  have hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p) :=
    fun p m => (renewalTime_characterization m p).1
  have hY : Measurable Y := measurable_selectedCutFuture T k hT
  have hP : Measurable P :=
    (measurable_of_countable selectedCutPastOutputToCarrier).comp
      (measurable_selectedCutPastMap T k hT)
  have hPair : Measurable (fun p => (Y p, P p)) := hY.prodMk hP
  have hZ : MeasurableSet Z := (selectedCutTime_partition k hk).1
  have hcomp : Zᶜ = S := by
    ext p
    simp only [Z, S, Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact (pos_iff_ne_zero :
      0 < selectedCutTime T k p ↔ selectedCutTime T k p ≠ 0).symm
  have hdecomp : μ = μ.restrict Z + μ.restrict S := by
    calc
      μ = μ.restrict Z + μ.restrict Zᶜ :=
        (Measure.restrict_add_restrict_compl (μ := μ) hZ).symm
      _ = μ.restrict Z + μ.restrict S := by rw [hcomp]
  have hinit : ∀ᵐ y ∂(μ.restrict Z).map Y, y 0 = (0, 0) := by
    apply (ae_map_iff hY.aemeasurable (by measurability)).2
    filter_upwards [ae_restrict_mem hZ,
      ae_restrict_of_ae conditionedVectorPathLaw_ae_legal] with p hp hlegal
    have htime : selectedCutTime T k p = 0 := hp
    simp [Y, selectedCutFuture, htime, conditionedVectorShift, hlegal.1]
  have hkernelZero : selectedCutMapKernel =ᵐ[(μ.restrict Z).map Y]
      fun _ => Measure.dirac z₀ := by
    filter_upwards [hinit] with y hy
    exact selectedCutMapKernel_zero y hy
  have hzero : (μ.restrict Z).map (fun p => (Y p, P p)) =
      (μ.restrict Z).map Y ⊗ₘ selectedCutMapKernel := by
    calc
      _ = (μ.restrict Z).map (fun p => (Y p, z₀)) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hZ,
          ae_restrict_of_ae (selectedCutPastMapFull_zero_ae k)] with p hp hzero
        exact congrArg (fun q => (Y p, q)) (hzero hp)
      _ = ((μ.restrict Z).map Y).prod (Measure.dirac z₀) :=
        by
          rw [Measure.prod_dirac,
            Measure.map_map measurable_prodMk_right hY]
          rfl
      _ = (μ.restrict Z).map Y ⊗ₘ selectedCutMapKernel := by
        symm
        calc
          _ = (μ.restrict Z).map Y ⊗ₘ
              Kernel.const (ℕ → ℤ × ℤ) (Measure.dirac z₀) :=
            Measure.compProd_congr hkernelZero
          _ = _ := by rw [Measure.compProd_const]
  have hpositive :=
    selectedCutPastMapFull_positive_joint_kernel_law T k hk hT
  dsimp only [μ, S, Y, P, T] at hpositive
  have hmapY : (μ.restrict Z).map Y + (μ.restrict S).map Y = μ.map Y := by
    calc
      (μ.restrict Z).map Y + (μ.restrict S).map Y =
          (μ.restrict Z + μ.restrict S).map Y :=
        (Measure.map_add _ _ hY).symm
      _ = μ.map Y :=
        congrArg (fun ν : Measure (ℕ → ℤ × ℤ) => ν.map Y) hdecomp.symm
  calc
    μ.map (fun p => (Y p, P p)) =
        (μ.restrict Z + μ.restrict S).map (fun p => (Y p, P p)) := by
      exact congrArg (fun ν : Measure (ℕ → ℤ × ℤ) =>
        ν.map (fun p => (Y p, P p))) hdecomp
    _ = (μ.restrict Z).map (fun p => (Y p, P p)) +
        (μ.restrict S).map (fun p => (Y p, P p)) := by
      rw [Measure.map_add _ _ hPair]
    _ = (μ.restrict Z).map Y ⊗ₘ selectedCutMapKernel +
        (μ.restrict S).map Y ⊗ₘ selectedCutMapKernel := by
      rw [hzero, hpositive]
    _ = ((μ.restrict Z).map Y + (μ.restrict S).map Y) ⊗ₘ
        selectedCutMapKernel := by
      rw [Measure.compProd_add_left]
    _ = μ.map Y ⊗ₘ selectedCutMapKernel := by
      exact congrArg (fun ν : Measure (ℕ → ℤ × ℤ) =>
        ν ⊗ₘ selectedCutMapKernel) hmapY

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The conditional law of the full selected past given the uncentered future. -/
theorem selectedCutPastMapFull_condDistrib (k : ℕ) (hk : 1 ≤ k) :
    let μ := conditionedVectorPathLaw 0 0
    let Y := selectedCutFuture Paper.Section4.renewalTime k
    let P := selectedCutPastMapFull Paper.Section4.renewalTime k
    condDistrib P Y μ =ᵐ[μ.map Y] selectedCutMapKernel := by
  dsimp only
  let T := Paper.Section4.renewalTime
  have hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p) :=
    fun p m => (renewalTime_characterization m p).1
  apply condDistrib_ae_eq_of_measure_eq_compProd
    (measurable_selectedCutFuture T k hT).aemeasurable
    ((measurable_of_countable selectedCutPastOutputToCarrier).comp
      (measurable_selectedCutPastMap T k hT)).aemeasurable
  exact selectedCutPastMapFull_joint_kernel_law k hk

end DirectedDistances.PaperProofs.Section4
