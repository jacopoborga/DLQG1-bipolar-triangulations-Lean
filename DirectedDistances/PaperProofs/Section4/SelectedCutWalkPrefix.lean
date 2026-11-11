/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.SelectedCutPastMapLaw
public import Mathlib.Probability.Kernel.Basic

/-! Finite path prefix retained at the selected cut time for the full-scope
Lemma 4.13 ruling. This file constructs the path-valued object and its
measurability; it does not prove the conditional law of the prefix. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The countable dependent type of finite paths, including the zero-step path. -/
abbrev SelectedCutWalkPrefix :=
  Σ t : ℕ, Fin (t + 1) → ℤ × ℤ

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The first-hit prefix at level `R = -r`, with its endpoint retained. -/
@[expose] noncomputable def selectedCutFirstHitWalkPrefix
    (r : ℕ) (p : ℕ → ℤ × ℤ) : SelectedCutWalkPrefix :=
  ⟨(conditionedSecondCoordinateFirstHit r p).toNat,
    conditionedVectorPrefix (conditionedSecondCoordinateFirstHit r p).toNat p⟩

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The first-hit prefix law at endpoint `(ell, -r)`, under the original conditioned
walk law given the finite first hit and its left endpoint. -/
@[expose] noncomputable def selectedCutFirstHitWalkLaw (ell r : ℕ) :
    Measure SelectedCutWalkPrefix := by
  let E := {p : ℕ → ℤ × ℤ |
    conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
        (ell : ℤ)}
  exact ((conditionedVectorPathLaw 0 0)[|E]).map
    (selectedCutFirstHitWalkPrefix r)

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
Singletons are measurable in the dependent sigma measurable space. -/
instance selectedCutWalkPrefix_measurableSingletonClass :
    MeasurableSingletonClass SelectedCutWalkPrefix := by
  constructor
  intro x
  rcases x with ⟨t, q⟩
  change MeasurableSet[
    ⨅ s : ℕ,
      (inferInstance : MeasurableSpace (Fin (s + 1) → ℤ × ℤ)).map
        (Sigma.mk (β := fun s : ℕ => Fin (s + 1) → ℤ × ℤ) s :
          (Fin (s + 1) → ℤ × ℤ) → SelectedCutWalkPrefix)]
    ({⟨t, q⟩} : Set SelectedCutWalkPrefix)
  rw [MeasurableSpace.measurableSet_iInf]
  intro s
  rw [MeasurableSpace.map_def]
  by_cases hs : s = t
  · subst s
    have hpre :
        (Sigma.mk (β := fun s : ℕ => Fin (s + 1) → ℤ × ℤ) t) ⁻¹'
          ({⟨t, q⟩} : Set SelectedCutWalkPrefix) =
        ({q} : Set (Fin (t + 1) → ℤ × ℤ)) := by
      ext v
      simp
    rw [hpre]
    exact measurableSet_singleton q
  · have hpre :
        (Sigma.mk (β := fun s : ℕ => Fin (s + 1) → ℤ × ℤ) s) ⁻¹'
          ({⟨t, q⟩} : Set SelectedCutWalkPrefix) = ∅ := by
      ext v
      simp [hs]
    rw [hpre]
    exact MeasurableSet.empty

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The sigma type carries the discrete measurable space on this countable path
carrier. -/
theorem selectedCutWalkPrefix_measurableSpace_discrete :
    DiscreteMeasurableSpace SelectedCutWalkPrefix := by
  infer_instance





@[expose] noncomputable def selectedCutWalkKernel :
    Kernel (ℕ → ℤ × ℤ) SelectedCutWalkPrefix := by
  classical
  let f : ℤ × ℤ → Measure SelectedCutWalkPrefix := fun q =>
    if hzero : q = (0, 0) then
      Measure.dirac (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix)
    else if hpos : 1 ≤ q.1 ∧ 1 ≤ (-q.2).toNat then
      let ell := q.1.toNat
      let r := (-q.2).toNat
      if hmass : 0 < (conditionedVectorPathLaw 0 0) ({p |
          conditionedSecondCoordinateFirstHit r p < ⊤} ∩
            {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
              (ell : ℤ)}) then
        selectedCutFirstHitWalkLaw ell r
      else Measure.dirac (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix)
    else Measure.dirac (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix)
  exact ⟨fun y => f (y 0), (measurable_of_countable f).comp
    (measurable_pi_apply 0)⟩

private theorem measurable_conditionedSecondCoordinateFirstHit_rw (r : ℕ) :
    Measurable (conditionedSecondCoordinateFirstHit r) := by
  apply ENat.measurable_iff.mpr
  intro n
  change MeasurableSet {p | conditionedSecondCoordinateFirstHit r p =
    (n : ℕ∞)}
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp
    (measurableSet_conditionedVectorPast_firstHit_eq r n)
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix n)

/-- Measurability of the finite first-hit prefix into the countable path carrier. -/
private theorem measurable_selectedCutFirstHitWalkPrefix (r : ℕ) :
    Measurable (selectedCutFirstHitWalkPrefix r) := by
  let t := fun p => (conditionedSecondCoordinateFirstHit r p).toNat
  have ht : Measurable t :=
    (measurable_of_countable ENat.toNat).comp
      (measurable_conditionedSecondCoordinateFirstHit_rw r)
  apply measurable_to_countable'
  rintro ⟨n, q⟩
  have heq : {p | selectedCutFirstHitWalkPrefix r p = ⟨n, q⟩} =
      {p | t p = n} ∩ {p | conditionedVectorPrefix n p = q} := by
    ext p
    constructor
    · intro hp
      rcases Sigma.mk.inj hp with ⟨htn, hpq⟩
      refine ⟨htn, ?_⟩
      subst n
      exact eq_of_heq hpq
    · rintro ⟨htn, hq⟩
      subst n
      exact congrArg (Sigma.mk (t p)) hq
  change MeasurableSet {p | selectedCutFirstHitWalkPrefix r p =
    (⟨n, q⟩ : SelectedCutWalkPrefix)}
  rw [heq]
  exact (ht (measurableSet_singleton n)).inter
    ((measurable_conditionedVectorPrefix n) (measurableSet_singleton q))

private theorem selectedCutFirstHitWalkPrefix_past_measurable
    (r ell k : ℕ) (A : Set SelectedCutWalkPrefix) (_hA : MeasurableSet A) :
    MeasurableSet[conditionedVectorPast k]
      (selectedCutFirstHitWalkPrefix r ⁻¹' A ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  let S : Set (Fin (k + 1) → ℤ × ℤ) :=
    {q | (⟨k, q⟩ : SelectedCutWalkPrefix) ∈ A ∧
      (q (Fin.last k)).1 = (ell : ℤ)}
  have hS : MeasurableSet S := (Set.to_countable _).measurableSet
  have hpre :
      selectedCutFirstHitWalkPrefix r ⁻¹' A ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)} =
        (conditionedVectorPrefix k ⁻¹' S) ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
    ext p
    constructor
    · rintro ⟨⟨hp, hk⟩, hend⟩
      refine ⟨?_, hk⟩
      change (⟨k, conditionedVectorPrefix k p⟩ : SelectedCutWalkPrefix) ∈ A ∧ _
      constructor
      · have hx : selectedCutFirstHitWalkPrefix r p =
            ⟨k, conditionedVectorPrefix k p⟩ := by
          rw [selectedCutFirstHitWalkPrefix, hk]
          simp
        rw [← hx]
        exact hp
      · change (p k).1 = (ell : ℤ) at hend
        exact hend
    · rintro ⟨⟨hp, hend⟩, hk⟩
      refine ⟨⟨?_, hk⟩, ?_⟩
      · have hx : selectedCutFirstHitWalkPrefix r p =
            ⟨k, conditionedVectorPrefix k p⟩ := by
          rw [selectedCutFirstHitWalkPrefix, hk]
          simp
        change selectedCutFirstHitWalkPrefix r p ∈ A
        rw [hx]
        exact hp
      · change (p k).1 = (ell : ℤ) at hend
        exact hend
  rw [hpre]
  exact (show MeasurableSet[conditionedVectorPast k]
      (conditionedVectorPrefix k ⁻¹' S) from ⟨S, hS, rfl⟩).inter
    (measurableSet_conditionedVectorPast_firstHit_eq r k)

private theorem selectedCutFirstHitWalkPrefix_endpoint_indepFun
    (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (hpos : 0 < (conditionedVectorPathLaw 0 0)
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
          (ell : ℤ)})) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    IndepFun (selectedCutFirstHitWalkPrefix r) Y (μ[|E]) := by
  dsimp only
  exact conditionedFirstHit_endpoint_indepFun r ell hr hell
    (selectedCutFirstHitWalkPrefix r)
    (fun A hA k => selectedCutFirstHitWalkPrefix_past_measurable r ell k A hA)
    hpos

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The selected-cut walk kernel is Markov. -/
instance selectedCutWalkKernel_isMarkov : IsMarkovKernel selectedCutWalkKernel := by
  classical
  refine ⟨fun y => ?_⟩
  dsimp only [selectedCutWalkKernel, Kernel.coe_mk]
  split
  · infer_instance
  · split
    · split
      · dsimp only [selectedCutFirstHitWalkLaw]
        apply (Measure.isProbabilityMeasure_map_iff
          (measurable_selectedCutFirstHitWalkPrefix _).aemeasurable).2
        exact cond_isProbabilityMeasure (ne_of_gt (by assumption))
      · infer_instance
    · infer_instance

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The zero endpoint branch of the stopped-walk prefix kernel is a point mass. -/
theorem selectedCutWalkKernel_zero (y : ℕ → ℤ × ℤ)
    (hy : y 0 = (0, 0)) :
    selectedCutWalkKernel y = Measure.dirac
      (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix) := by
  classical
  dsimp [selectedCutWalkKernel]
  simp [hy]

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
On a positive endpoint, the kernel is the fixed-endpoint stopped-walk law. -/
theorem selectedCutWalkKernel_positive (ell r : ℕ) (hell : 1 ≤ ell)
    (hr : 1 ≤ r) (y : ℕ → ℤ × ℤ)
    (hy : y 0 = ((ell : ℤ), -(r : ℤ))) :
    selectedCutWalkKernel y =
      if _hmass : 0 < (conditionedVectorPathLaw 0 0) ({p |
        conditionedSecondCoordinateFirstHit r p < ⊤} ∩
          {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
            (ell : ℤ)}) then
        selectedCutFirstHitWalkLaw ell r
      else Measure.dirac (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix) := by
  classical
  dsimp [selectedCutWalkKernel]
  have hzero : y 0 ≠ (0, 0) := by
    rw [hy]
    intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  have hpos : 1 ≤ (y 0).1 ∧ 1 ≤ (-(y 0).2).toNat := by
    rw [hy]
    simp only [neg_neg, Int.toNat_natCast]
    exact ⟨by exact_mod_cast hell, hr⟩
  simp only [hzero, hpos, true_and, ite_false, ite_true]
  simp only [hy, neg_neg, Int.toNat_natCast, selectedCutFirstHitWalkLaw]

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The zero-left-coordinate positive first-hit branch is null: at a finite first hit
of `R = -r`, a legal path from the origin has left coordinate at least one. -/
theorem selectedCutWalkPrefix_zero_ell_branch_ae
    (k r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p ∉
        firstHitPositiveBranchFuture 0 r k := by
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  have hleft : ∀ᵐ p ∂μ, 1 ≤ (p (τ p).toNat).1 := by
    have h := firstHitPastMap_left_pos_ae r hr
    dsimp only at h
    rw [firstHitPastMap_cond_finite_hit_eq r hr] at h
    exact h
  filter_upwards [hleft] with p hpLeft
  intro hp
  have hbad : (p (τ p).toNat).1 = 0 := by
    have h := congrArg Prod.fst hp.2
    simpa [τ, conditionedVectorShift] using h
  rw [hbad] at hpLeft
  norm_num at hpLeft


/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The path through the selected cut time, with its endpoint retained. -/
@[expose] noncomputable def selectedCutWalkPrefix
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (p : ℕ → ℤ × ℤ) :
    SelectedCutWalkPrefix :=
  ⟨(selectedCutTime T k p).toNat,
    conditionedVectorPrefix (selectedCutTime T k p).toNat p⟩

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The selected finite prefix is a measurable map into its countable sigma type. -/
theorem measurable_selectedCutWalkPrefix
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectedCutWalkPrefix T k) := by
  let t := fun p => (selectedCutTime T k p).toNat
  have ht : Measurable t :=
    (measurable_of_countable ENat.toNat).comp
      (measurable_selectedCutTime T k hT)
  apply measurable_to_countable'
  rintro ⟨n, q⟩
  have heq : {p | selectedCutWalkPrefix T k p = ⟨n, q⟩} =
      {p | t p = n} ∩ {p | conditionedVectorPrefix n p = q} := by
    ext p
    constructor
    · intro hp
      rcases Sigma.mk.inj hp with ⟨htn, hpq⟩
      refine ⟨htn, ?_⟩
      subst n
      exact eq_of_heq hpq
    · rintro ⟨htn, hq⟩
      subst n
      exact congrArg (Sigma.mk (t p)) hq
  change MeasurableSet {p | selectedCutWalkPrefix T k p =
    (⟨n, q⟩ : SelectedCutWalkPrefix)}
  rw [heq]
  exact (ht (measurableSet_singleton n)).inter
    ((measurable_conditionedVectorPrefix n) (measurableSet_singleton q))

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
At selected time zero, the prefix is the one-point origin path almost surely
under the conditioned path law. -/
theorem selectedCutWalkPrefix_zero_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      selectedCutTime T k p = 0 →
        selectedCutWalkPrefix T k p = ⟨0, fun _ => (0, 0)⟩ := by
  filter_upwards [conditionedVectorPathLaw_ae_legal] with p hp
  intro htime
  have hstart : p 0 = (0, 0) := hp.1
  have htimeNat : (selectedCutTime T k p).toNat = 0 := by
    simp [htime]
  change (⟨(selectedCutTime T k p).toNat,
      conditionedVectorPrefix (selectedCutTime T k p).toNat p⟩ :
        SelectedCutWalkPrefix) =
    (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix)
  rw [htimeNat]
  apply congrArg (Sigma.mk 0)
  funext i
  have hi : i.val = 0 := by omega
  simpa [conditionedVectorPrefix, hi] using hstart

private theorem conditionedSecondCoordinateFirstHit_eq_nat_iff
    (r t : ℕ) (p : ℕ → ℤ × ℤ) :
    conditionedSecondCoordinateFirstHit r p = (t : ℕ∞) ↔
      (p t).2 = -(r : ℤ) ∧ ∀ j < t, (p j).2 ≠ -(r : ℤ) := by
  unfold conditionedSecondCoordinateFirstHit
  by_cases h : ∃ n, (p n).2 = -(r : ℤ)
  · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dite_eq_right h]
    constructor
    · intro he
      exact (ENat.top_ne_natCast t he).elim
    · rintro ⟨ht, _⟩
      exact (h ⟨t, ht⟩).elim

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
On a legal supported path, a finite first-hit time, possibly zero, gives the
prefix through that first hit and the lower-half-plane stay conditions. -/
theorem selectedCutWalkPrefix_firstHit_characterization
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k r : ℕ) (p : ℕ → ℤ × ℤ)
    (hselected : selectedCutTime T k p =
      conditionedSecondCoordinateFirstHit r p)
    (hfinite : conditionedSecondCoordinateFirstHit r p < ⊤)
    (h0 : (p 0).2 = 0)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (hnonnegative : ∀ j, 0 ≤ (p j).1) :
    ∃ t : ℕ,
      selectedCutTime T k p = (t : ℕ∞) ∧
      selectedCutWalkPrefix T k p = ⟨t, conditionedVectorPrefix t p⟩ ∧
      (p t).2 = -(r : ℤ) ∧
      (∀ j < t, (p j).2 ≠ -(r : ℤ)) ∧
      ∀ j ≤ t, 0 ≤ (p j).1 ∧ -(r : ℤ) ≤ (p j).2 := by
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfinite.ne
  have hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞) := ht.symm
  have htime : selectedCutTime T k p = (t : ℕ∞) := hselected.trans hτ
  have htimeNat : (selectedCutTime T k p).toNat = t := by
    rw [htime]
    simp
  have hfirst :=
    (conditionedSecondCoordinateFirstHit_eq_nat_iff r t p).mp hτ
  have hprefix : selectedCutWalkPrefix T k p =
      ⟨t, conditionedVectorPrefix t p⟩ := by
    change (⟨(selectedCutTime T k p).toNat,
      conditionedVectorPrefix (selectedCutTime T k p).toNat p⟩ :
        SelectedCutWalkPrefix) = _
    rw [htimeNat]
  have hsecond : ∀ j ≤ t, -(r : ℤ) ≤ (p j).2 := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [h0]
        omega
    | succ j ih =>
        intro hj
        by_contra hbad
        have hjt : j ≤ t := by omega
        have hprev := ih hjt
        have hnot := hfirst.2 j (by omega)
        have hstepj := hstep j
        omega
  refine ⟨t, htime, hprefix, hfirst.1, hfirst.2, ?_⟩
  intro j hj
  exact ⟨hnonnegative j, hsecond j hj⟩

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The joint-law characterization of the conditional law of the selected prefix given
the selected future: it suffices to identify the joint law with the composition
product of the future law and the kernel. -/
theorem selectedCutWalkPrefix_condDistrib_of_joint_law
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (h : (conditionedVectorPathLaw 0 0).map
        (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) =
      ((conditionedVectorPathLaw 0 0).map (selectedCutFuture T k)) ⊗ₘ
        selectedCutWalkKernel) :
    condDistrib (selectedCutWalkPrefix T k) (selectedCutFuture T k)
        (conditionedVectorPathLaw 0 0)
      =ᵐ[(conditionedVectorPathLaw 0 0).map (selectedCutFuture T k)]
      selectedCutWalkKernel :=
  condDistrib_ae_eq_of_measure_eq_compProd
    (measurable_selectedCutFuture T k hT).aemeasurable
    (measurable_selectedCutWalkPrefix T k hT).aemeasurable h

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
Zero branch: on the event that the selected time is zero, the joint law of the
selected future and the prefix is the future law composed with the kernel, which is
the point mass at the single-origin path there. -/
theorem selectedCutWalkPrefix_zero_branch_joint_law
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ((conditionedVectorPathLaw 0 0).restrict {p | selectedCutTime T k p = 0}).map
        (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) =
      (((conditionedVectorPathLaw 0 0).restrict
        {p | selectedCutTime T k p = 0}).map (selectedCutFuture T k)) ⊗ₘ
        selectedCutWalkKernel := by
  classical
  set μ' := (conditionedVectorPathLaw 0 0).restrict {p | selectedCutTime T k p = 0}
    with hμ'
  have hY := measurable_selectedCutFuture T k hT
  have hZ : MeasurableSet {p | selectedCutTime T k p = 0} :=
    measurable_selectedCutTime T k hT (measurableSet_singleton 0)
  have hae : ∀ᵐ p ∂μ', selectedCutFuture T k p 0 = (0, 0) ∧
      selectedCutWalkPrefix T k p = ⟨0, fun _ => (0, 0)⟩ := by
    filter_upwards [ae_restrict_of_ae (conditionedVectorPathLaw_ae_legal),
      ae_restrict_of_ae (selectedCutWalkPrefix_zero_ae T k),
      ae_restrict_mem hZ] with p hl hp hz
    have hz' : selectedCutTime T k p = 0 := hz
    refine ⟨?_, hp hz'⟩
    simp only [selectedCutFuture, hz', ENat.toNat_zero, conditionedVectorShift,
      Nat.add_zero]
    exact hl.1
  have hker : selectedCutWalkKernel =ᵐ[μ'.map (selectedCutFuture T k)]
      Kernel.const _ (Measure.dirac (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix)) := by
    have hmeas : MeasurableSet {y : ℕ → ℤ × ℤ | y 0 = (0, 0)} :=
      (measurable_pi_apply 0) (measurableSet_singleton _)
    have hy : ∀ᵐ y ∂μ'.map (selectedCutFuture T k), y 0 = (0, 0) :=
      (ae_map_iff hY.aemeasurable hmeas).2 (hae.mono fun p hp => hp.1)
    filter_upwards [hy] with y hy0
    rw [selectedCutWalkKernel_zero y hy0]
    rfl
  have hmeasX := measurable_selectedCutWalkPrefix T k hT
  calc μ'.map (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p))
      = μ'.map (fun p => (selectedCutFuture T k p,
          (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix))) :=
        Measure.map_congr (hae.mono fun p hp => by dsimp only; rw [hp.2])
    _ = (μ'.map (selectedCutFuture T k)).map (fun y =>
          (y, (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix))) := by
        rw [Measure.map_map (by fun_prop) hY]
        rfl
    _ = (μ'.map (selectedCutFuture T k)).prod
          (Measure.dirac (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix)) := by
        rw [Measure.prod_dirac]
    _ = _ := by
        rw [Measure.compProd_congr hker, Measure.compProd_const]

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The joint law of the selected future and prefix, assuming the positive-branch joint
law on each almost-sure positive first-hit branch (the remaining fixed-endpoint
past/future independence goal), together with the proved zero branch. -/
theorem selectedCutWalkPrefix_joint_law_of_positive_branches
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hpos : ∀ i : PositiveBranchIx k,
      ((conditionedVectorPathLaw 0 0).restrict
        ((fun p => conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
          firstHitPositiveBranchFuture i.1.1 i.1.2 k)).map
          (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) =
        (((conditionedVectorPathLaw 0 0).restrict
          ((fun p => conditionedVectorShift
            (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
            firstHitPositiveBranchFuture i.1.1 i.1.2 k)).map
              (selectedCutFuture T k)) ⊗ₘ selectedCutWalkKernel) :
    (conditionedVectorPathLaw 0 0).map
        (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) =
      ((conditionedVectorPathLaw 0 0).map (selectedCutFuture T k)) ⊗ₘ
        selectedCutWalkKernel := by
  classical
  set μ := conditionedVectorPathLaw 0 0 with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have : Countable (PositiveBranchIx k) := inferInstance
  have hY := measurable_selectedCutFuture T k hT
  have hX := measurable_selectedCutWalkPrefix T k hT
  have hZ : MeasurableSet {p | selectedCutTime T k p = 0} :=
    measurable_selectedCutTime T k hT (measurableSet_singleton 0)
  have hsplit : μ.restrict {p | selectedCutTime T k p = 0} +
      μ.restrict {p | 0 < selectedCutTime T k p} = μ := by
    have hc : {p | selectedCutTime T k p = 0}ᶜ = {p | 0 < selectedCutTime T k p} := by
      ext p
      simp [pos_iff_ne_zero]
    rw [← hc]
    exact Measure.restrict_add_restrict_compl hZ
  have hsum := selectedCutTime_positive_restrict_eq_sum T k hk hT
  have hzero := selectedCutWalkPrefix_zero_branch_joint_law T k hT
  have hjoint : μ.map (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) =
      (μ.restrict {p | selectedCutTime T k p = 0}).map
        (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) +
      Measure.sum (fun i : PositiveBranchIx k => (μ.restrict
        ((fun p => conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
          firstHitPositiveBranchFuture i.1.1 i.1.2 k)).map
          (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p))) := by
    rw [← Measure.map_sum (hY.prodMk hX).aemeasurable, ← hsum,
      ← Measure.map_add _ _ (hY.prodMk hX)]
    rw [hsplit]
  have hfut : μ.map (selectedCutFuture T k) =
      (μ.restrict {p | selectedCutTime T k p = 0}).map (selectedCutFuture T k) +
      Measure.sum (fun i : PositiveBranchIx k => (μ.restrict
        ((fun p => conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
          firstHitPositiveBranchFuture i.1.1 i.1.2 k)).map
          (selectedCutFuture T k)) := by
    rw [← Measure.map_sum hY.aemeasurable, ← hsum, ← Measure.map_add _ _ hY]
    rw [hsplit]
  rw [hjoint, hfut, Measure.compProd_add_left, Measure.compProd_sum_left, hzero]
  congr 1
  exact congrArg Measure.sum (funext hpos)

/- Remaining work toward Lemma 4.13: prove the positive-branch hypothesis `hpos` of
`selectedCutWalkPrefix_joint_law_of_positive_branches` (fixed-endpoint past/future
independence for the first-hit prefix), then apply
`selectedCutWalkPrefix_condDistrib_of_joint_law` for `T := renewalTime`. -/

end DirectedDistances.PaperProofs.Section4
