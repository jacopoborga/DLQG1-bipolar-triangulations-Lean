/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LastCutSelector
public import DirectedDistances.PaperProofs.Section4.FirstHitPastMapBranchGluing

/-! Supporting lemmas for paper labels `lem-past-map` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- The greatest selector rank whose graph time is not after `τ_k`.
This definition is a generic selector helper, not the source renewal rank. -/
@[expose] noncomputable def selectedCutRank
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (p : ℕ → ℤ × ℤ) : ℕ :=
  Nat.findGreatest (fun m => T m p ≤ conditionedSecondCoordinateFirstHit k p)
    (conditionedSecondCoordinateFirstHit k p).toNat

/-- The finite last selector time through `τ_k`, with value `⊤` when `τ_k=⊤`.
For finite `τ_k`, this is the graph value at `selectedCutRank`; the generic
last-cut theorem identifies it with the largest source barrier branch. -/
@[expose] noncomputable def selectedCutTime
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (p : ℕ → ℤ × ℤ) : ℕ∞ :=
  if _hτ : conditionedSecondCoordinateFirstHit k p < ⊤ then
    T (selectedCutRank T k p) p
  else ⊤

/-- The future after the selected cut time, using `toNat` at the cemetery value. -/
@[expose] noncomputable def selectedCutFuture
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (p : ℕ → ℤ × ℤ) :=
  conditionedVectorShift (selectedCutTime T k p).toNat p

private theorem measurableSet_of_conditionedVectorPast (n : ℕ)
    (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[conditionedVectorPast n] A) : MeasurableSet A := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix n)

private theorem measurable_conditionedHitTime (r : ℕ) :
    Measurable (conditionedSecondCoordinateFirstHit r) := by
  apply ENat.measurable_iff.mpr
  intro n
  exact measurableSet_of_conditionedVectorPast n _
    (measurableSet_conditionedVectorPast_firstHit_eq r n)

@[expose] def literalSuccessGraph (p : ℕ → ℤ × ℤ) : ℕ → Prop := fun j =>
  (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
    ∀ i, j ≤ i → (p j).1 ≤ (p i).1

private theorem selectedCutGraph_fiber
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (m : ℕ) (t : ℕ∞) :
    {p | T m p = t} = {p | IsPositiveSuccessTime (literalSuccessGraph p) m t} := by
  ext p
  constructor
  · intro h
    rw [← h]
    exact hT p m
  · intro ht
    obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (literalSuccessGraph p) m
    exact (hu (T m p) (hT p m)).trans (hu t ht).symm

private theorem measurable_selector_component
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (m : ℕ) : Measurable (T m) := by
  have hFiber (t : ℕ∞) : MeasurableSet {p | T m p = t} := by
    rw [selectedCutGraph_fiber T hT m t]
    induction t using ENat.recTopCoe with
    | top =>
        exact measurableSet_isPositiveSuccessTime_top _
          (fun j _ => measurableSet_renewal_success j) m
    | coe n =>
        exact measurableSet_isPositiveSuccessTime_natCast _
          (fun j _ => measurableSet_renewal_success j) m n
  intro s hs
  have hpre : (T m) ⁻¹' s = ⋃ t : s, {p | T m p = t.val} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hp
      exact ⟨⟨T m p, hp⟩, rfl⟩
    · rintro ⟨t, ht⟩
      exact ht ▸ t.property
  rw [hpre]
  exact MeasurableSet.iUnion fun t => hFiber t.val

private theorem measurable_selectedCutRank
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectedCutRank T k) := by
  classical
  let τ := conditionedSecondCoordinateFirstHit k
  let V := fun p => (τ p).toNat
  let U := fun j p => T j p ≤ τ p
  have hτ : Measurable τ := measurable_conditionedHitTime k
  have hV : Measurable V := (measurable_of_countable ENat.toNat).comp hτ
  have hOrder : MeasurableSet {q : ℕ∞ × ℕ∞ | q.1 ≤ q.2} :=
    (Set.to_countable _).measurableSet
  have hU (j : ℕ) : MeasurableSet {p | U j p} :=
    hOrder.preimage ((measurable_selector_component T hT j).prodMk hτ)
  have hFiber (m : ℕ) : MeasurableSet {p | selectedCutRank T k p = m} := by
    have hEq : {p | selectedCutRank T k p = m} =
        ⋃ n : ℕ, {p | V p = n} ∩
          {p | m ≤ n ∧ (m ≠ 0 → U m p) ∧
            ∀ j, m < j → j ≤ n → ¬ U j p} := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hp
        refine ⟨V p, rfl, ?_⟩
        change Nat.findGreatest (fun j => U j p) (V p) = m at hp
        rw [Nat.findGreatest_eq_iff] at hp
        exact hp
      · rintro ⟨n, hn, hmax⟩
        change Nat.findGreatest (fun j => U j p) (V p) = m
        rw [hn, Nat.findGreatest_eq_iff]
        exact hmax
    rw [hEq]
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.inter
    · exact hV (measurableSet_singleton n)
    · have hmax : MeasurableSet
          {p | m ≤ n ∧ (m ≠ 0 → U m p) ∧
            ∀ j, m < j → j ≤ n → ¬ U j p} := by
        by_cases hmn : m ≤ n
        · have hcond : MeasurableSet {p | (m ≠ 0 → U m p) ∧
              ∀ j, m < j → j ≤ n → ¬ U j p} := by
            have hset :
                {p | (m ≠ 0 → U m p) ∧
                  ∀ j, m < j → j ≤ n → ¬ U j p} =
                {p | m ≠ 0 → U m p} ∩
                  {p | ∀ j, m < j → j ≤ n → ¬ U j p} := by
              ext p
              rfl
            rw [hset]
            apply MeasurableSet.inter
            · exact (MeasurableSet.const (m ≠ 0)).imp (hU m)
            · rw [Set.ofPred_forall]
              apply MeasurableSet.iInter
              intro j
              apply (MeasurableSet.const (m < j)).imp
              apply (MeasurableSet.const (j ≤ n)).imp
              exact (hU j).compl
          simpa [hmn] using hcond
        · simp [hmn]
      exact hmax
  intro s hs
  have hpre : (selectedCutRank T k) ⁻¹' s =
      ⋃ m : s, {p | selectedCutRank T k p = m.val} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hp
      exact ⟨⟨selectedCutRank T k p, hp⟩, rfl⟩
    · rintro ⟨m, hm⟩
      exact hm ▸ m.property
  rw [hpre]
  exact MeasurableSet.iUnion fun m => hFiber m.val

/-- Measurability of each supplied graph time follows from its literal graph;
no measurability premise is added to the generic selector. -/
theorem measurable_selector_component_of_graph
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (m : ℕ) : Measurable (T m) :=
  measurable_selector_component T hT m

/-- The selected last-cut time is measurable for every selector satisfying the
literal `A_n ∩ B_n` graph. -/
theorem measurable_selectedCutTime
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectedCutTime T k) := by
  classical
  let τ := conditionedSecondCoordinateFirstHit k
  have hτ : Measurable τ := measurable_conditionedHitTime k
  have hRank : Measurable (selectedCutRank T k) := measurable_selectedCutRank T k hT
  have hComp (m : ℕ) : Measurable (fun p => T m p) :=
    measurable_selector_component T hT m
  apply ENat.measurable_iff.mpr
  intro n
  have hFinite : MeasurableSet {p | τ p < ⊤} := by
    rw [show {p | τ p < ⊤} = ⋃ j : ℕ, {p | τ p = (j : ℕ∞)} by
      ext p
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp h.ne
        exact ⟨j, hj.symm⟩
      · rintro ⟨j, hj⟩
        rw [hj]
        exact ENat.natCast_lt_top _]
    exact MeasurableSet.iUnion fun j =>
      hτ (measurableSet_singleton (j : ℕ∞))
  have hEq : {p | selectedCutTime T k p = (n : ℕ∞)} =
      ⋃ m : ℕ, {p | τ p < ⊤} ∩ {p | selectedCutRank T k p = m} ∩
        {p | T m p = (n : ℕ∞)} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hp
      by_cases hfinite : τ p < ⊤
      · refine ⟨selectedCutRank T k p, ⟨hfinite, rfl⟩, ?_⟩
        simpa [selectedCutTime, τ, hfinite] using hp
      · have htime : selectedCutTime T k p = ⊤ := by
          simp [selectedCutTime, τ, hfinite]
        exact (ENat.top_ne_natCast n (htime.symm.trans hp)).elim
    · rintro ⟨m, ⟨hfinite, hrank⟩, heq⟩
      have htime : selectedCutTime T k p = T m p := by
        simp [selectedCutTime, τ, hfinite, hrank]
      exact htime.trans heq
  change MeasurableSet {p | selectedCutTime T k p = (n : ℕ∞)}
  rw [hEq]
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · exact hFinite
    · exact hRank (measurableSet_singleton m)
  · exact (hComp m) (measurableSet_singleton (n : ℕ∞))

/-- The selected-cut future is measurable by countable evaluation of the
integer-valued selected time. -/
theorem measurable_selectedCutFuture
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectedCutFuture T k) := by
  have htime := measurable_selectedCutTime T k hT
  have hnat : Measurable (fun p => (selectedCutTime T k p).toNat) :=
    (measurable_of_countable ENat.toNat).comp htime
  have heval : Measurable
      (fun z : (ℕ → ℤ × ℤ) × ℕ => conditionedVectorShift z.2 z.1) :=
    measurable_from_prod_countable_left fun n => measurable_conditionedVectorShift n
  exact heval.comp (measurable_id.prodMk hnat)

/-- On a finite `τ_k`, the chosen rank is exactly the largest graph rank from
`exists_last_successTime_before_firstHit`; hence `selectedCutTime` equals its
graph time and inherits the last-barrier characterization. -/
theorem selectedCutTime_lastSuccessTime
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ) (k : ℕ)
    (hk : 1 ≤ k)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2)
    (h0 : (p 0).2 = 0)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hτ : conditionedSecondCoordinateFirstHit k p < ⊤) :
    ∃ mk,
      selectedCutTime T k p = T mk p ∧
      (∀ m, T m p ≤ conditionedSecondCoordinateFirstHit k p → m ≤ mk) ∧
      (∀ r, 1 ≤ r → r ≤ k →
        (selectedCutTime T k p = conditionedSecondCoordinateFirstHit r p ↔
          firstHitBarrier r p ∧
            ∀ s, r < s → s ≤ k → ¬ firstHitBarrier s p)) ∧
      (selectedCutTime T k p = 0 ↔
        ∀ s, 1 ≤ s → s ≤ k → ¬ firstHitBarrier s p) := by
  obtain ⟨mk, hle, hmax, hbranch, hzero⟩ :=
    exists_last_successTime_before_firstHit T p k hk hstep h0 hT hτ
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp hτ.ne
  have hτK : conditionedSecondCoordinateFirstHit k p = (K : ℕ∞) := hK.symm
  have htoNat : (conditionedSecondCoordinateFirstHit k p).toNat = K := by
    rw [hτK]
    simp
  have hTzero : T 0 p = 0 :=
    (isPositiveSuccessTime_zero_iff _ _).mp (hT 0)
  have hzeroRank : T 0 p ≤ conditionedSecondCoordinateFirstHit k p := by
    rw [hTzero]
    exact bot_le
  have hmkK : mk ≤ K := by
    apply positiveSuccessTime_le_index T p hT mk K
    simpa [hτK] using hle
  have hmkRank : mk ≤ selectedCutRank T k p := by
    rw [selectedCutRank, htoNat]
    apply Nat.le_findGreatest hmkK
    simpa [hτK] using hle
  have hrankK : selectedCutRank T k p ≤ K := by
    rw [selectedCutRank, htoNat]
    exact Nat.findGreatest_le K
  have hrankOK : T (selectedCutRank T k p) p ≤
      conditionedSecondCoordinateFirstHit k p := by
    rw [selectedCutRank, htoNat]
    apply Nat.findGreatest_spec (m := 0) (n := K)
      (P := fun m => T m p ≤ conditionedSecondCoordinateFirstHit k p)
    · exact Nat.zero_le K
    · exact hzeroRank
  have hrankMax : selectedCutRank T k p ≤ mk := hmax _ hrankOK
  have hrankEq : selectedCutRank T k p = mk := Nat.le_antisymm hrankMax hmkRank
  have hselected : selectedCutTime T k p = T mk p := by
    rw [selectedCutTime, dite_eq_left hτ, hrankEq]
  refine ⟨mk, hselected, hmax, ?_, ?_⟩
  · intro r hr hrk
    simpa [hselected] using hbranch r hr hrk
  · simpa [hselected] using hzero

private theorem secondCoordinate_at_finite_firstHit
    (r t : ℕ) (p : ℕ → ℤ × ℤ)
    (hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞)) :
    (p t).2 = -(r : ℤ) := by
  classical
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hnone
    have htop : conditionedSecondCoordinateFirstHit r p = ⊤ := by
      simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hnone]
    rw [htop] at hτ
    exact (ENat.top_ne_natCast t hτ).elim
  have hfind : ((Nat.find hh : ℕ) : ℕ∞) = (t : ℕ∞) := by
    simpa only [conditionedSecondCoordinateFirstHit, dite_eq_left hh] using hτ
  have hfindNat : Nat.find hh = t := by
    exact_mod_cast hfind
  rw [← hfindNat]
  exact Nat.find_spec hh

/-- positive branch of the past-map law at the source last cut T_{m_k}, for any
selector T satisfying the literal A_n ∩ B_n graph (T_m is not defined here; the
the grouped 4.13 source questions are not treated; not the paper result. -/
theorem selectedCutTime_positiveBranch_event_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k r ell : ℕ)
    (hr : 1 ≤ r) (hrk : r ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    {p | selectedCutTime T k p = conditionedSecondCoordinateFirstHit r p ∧
      conditionedSecondCoordinateFirstHit r p < ⊤ ∧
      (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)} =ᵐ[
        conditionedVectorPathLaw 0 0]
      {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        (fun p => conditionedVectorShift
          (conditionedSecondCoordinateFirstHit r p).toNat p) ⁻¹'
          firstHitPositiveBranchFuture ell r k := by
  let τ := conditionedSecondCoordinateFirstHit r
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  filter_upwards [conditionedVectorPathLaw_ae_legal,
    firstHitPastMap_finite_hit_ae r hr,
    firstHitPastMap_finite_hit_ae k (by omega)] with p hlegal hfinite hfiniteK
  apply propext
  change (selectedCutTime T k p = τ p ∧ τ p < ⊤ ∧
      (p (τ p).toNat).1 = (ell : ℤ)) ↔
    (τ p < ⊤ ∧ Y p ∈ firstHitPositiveBranchFuture ell r k)
  have h0 : (p 0).2 = 0 := by
    have h := congrArg Prod.snd hlegal.1
    simpa using h
  have hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2 := by
    intro j
    obtain ⟨c, hc⟩ := hlegal.2 j
    have hs := congrArg Prod.snd hc
    fin_cases c <;>
      norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfinite.ne
  have hτt : τ p = (t : ℕ∞) := ht.symm
  have hlast := selectedCutTime_lastSuccessTime T p k (by omega)
    hstep h0 (fun m => hT p m) hfiniteK
  obtain ⟨mk, _, _, hchar, _⟩ := hlast
  have hdecomp (hend : (p t).1 = (ell : ℤ)) :=
    firstHitBarrier_positive_decomposition p ell r k t hstep h0 hr hτt hend
  constructor
  · rintro ⟨hsel, hlt, hell⟩
    have hbar := (hchar r hr hrk).mp hsel
    have hend : (p t).1 = (ell : ℤ) := by
      simpa [hτt] using hell
    have hfuture := (hdecomp hend).mp hbar
    refine ⟨hlt, ?_⟩
    change Y p ∈ barrierFutureEvent ell r k ∧
      Y p 0 = ((ell : ℤ), -(r : ℤ))
    constructor
    · simpa [Y, hτt, conditionedVectorShift] using hfuture
    · apply Prod.ext
      · simpa [Y, hτt, conditionedVectorShift] using hell
      · simpa [Y, hτt, conditionedVectorShift] using
          secondCoordinate_at_finite_firstHit r t p hτt
  · rintro ⟨hlt, hbranch⟩
    have hbranch' : Y p ∈ barrierFutureEvent ell r k ∧
        Y p 0 = ((ell : ℤ), -(r : ℤ)) := by
      simpa [firstHitPositiveBranchFuture] using hbranch
    have hend : (p t).1 = (ell : ℤ) := by
      have h := congrArg Prod.fst hbranch'.2
      simpa [Y, hτt, conditionedVectorShift] using h
    have hbar := (hdecomp hend).mpr (by simpa [Y, hτt] using hbranch'.1)
    have hsel := (hchar r hr hrk).mpr hbar
    refine ⟨hsel, hlt, ?_⟩
    have h := congrArg Prod.fst hbranch'.2
    simpa [Y, hτt, conditionedVectorShift] using h


private theorem selectedCut_branch_iff_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k r ell : ℕ)
    (hr : 1 ≤ r) (hrk : r ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (selectedCutTime T k p = conditionedSecondCoordinateFirstHit r p ∧
        conditionedSecondCoordinateFirstHit r p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)) ↔
      conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p ∈
        firstHitPositiveBranchFuture ell r k := by
  filter_upwards [selectedCutTime_positiveBranch_event_ae T k r ell hr hrk hT,
    firstHitPastMap_finite_hit_ae r hr] with p he hf
  exact ⟨fun hs => ((Iff.of_eq he).mp hs).2,
    fun hp => (Iff.of_eq he).mpr ⟨hf, hp⟩⟩

/-- positive branch of the past-map law at the source last cut T_{m_k}, for any
selector T satisfying the literal A_n ∩ B_n graph (T_m is not defined here; the
the grouped 4.13 source questions are not treated; not the paper result. -/
theorem selectedCutTime_positive_event_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    {p | 0 < selectedCutTime T k p} =ᵐ[conditionedVectorPathLaw 0 0]
      ⋃ i : PositiveBranchIx k,
        (fun p => conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
          firstHitPositiveBranchFuture i.1.1 i.1.2 k := by
  classical
  let E := fun i : PositiveBranchIx k =>
    (fun p => conditionedVectorShift
      (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
      firstHitPositiveBranchFuture i.1.1 i.1.2 k
  have hbranches : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∀ i : PositiveBranchIx k,
      (selectedCutTime T k p = conditionedSecondCoordinateFirstHit i.1.2 p ∧
        conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit i.1.2 p).toNat).1 = (i.1.1 : ℤ)) ↔
      p ∈ E i := by
    exact ae_all_iff.mpr fun i =>
      selectedCut_branch_iff_ae T k i.1.2 i.1.1 i.2.1 i.2.2 hT
  have hnonneg : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∀ n, 0 ≤ (p n).1 := by
    unfold conditionedVectorPathLaw
    apply ae_map_iff (by fun_prop) (by measurability) |>.2
    exact Filter.Eventually.of_forall fun p n => Int.natCast_nonneg _
  filter_upwards [hbranches, conditionedVectorPathLaw_ae_legal, hnonneg,
    firstHitPastMap_finite_hit_ae k hk] with p hbranches hlegal hnonneg hfinite
  apply propext
  change 0 < selectedCutTime T k p ↔ p ∈ ⋃ i, E i
  rw [Set.mem_iUnion]
  have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
  have hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2 := by
    intro j
    obtain ⟨c, hc⟩ := hlegal.2 j
    have hs := congrArg Prod.snd hc
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega
  obtain ⟨mk, _, _, hchar, hzero⟩ :=
    selectedCutTime_lastSuccessTime T p k hk hstep h0 (fun m => hT p m) hfinite
  constructor
  · intro hpos
    have hex : ∃ r, 1 ≤ r ∧ r ≤ k ∧ firstHitBarrier r p := by
      by_contra hnone
      have hz : selectedCutTime T k p = 0 := hzero.mpr (by
        intro s hs hsk hb
        exact hnone ⟨s, hs, hsk, hb⟩)
      rw [hz] at hpos
      exact (lt_irrefl _ hpos)
    obtain ⟨s, hs, hsk, hb⟩ := hex
    let r := Nat.findGreatest (fun j => firstHitBarrier j p) k
    have hsr : s ≤ r := Nat.le_findGreatest hsk hb
    have hr : 1 ≤ r := hs.trans hsr
    have hrk : r ≤ k := Nat.findGreatest_le k
    have hbar : firstHitBarrier r p :=
      Nat.findGreatest_spec (P := fun j => firstHitBarrier j p) hsk hb
    have hlater : ∀ j, r < j → j ≤ k → ¬ firstHitBarrier j p := by
      intro j hj hjk
      exact Nat.findGreatest_is_greatest hj hjk
    have hsel := (hchar r hr hrk).mpr ⟨hbar, hlater⟩
    obtain ⟨t, ht, _⟩ := hbar
    have hfin : conditionedSecondCoordinateFirstHit r p < ⊤ := by
      rw [ht]
      exact ENat.natCast_lt_top _
    let ell := (p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat
    have hell : (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
        (ell : ℤ) := (Int.toNat_of_nonneg (hnonneg _)).symm
    exact ⟨⟨(ell, r), hr, hrk⟩, (hbranches ⟨(ell, r), hr, hrk⟩).mp
      ⟨hsel, hfin, hell⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨hsel, hfin, _⟩ := (hbranches i).mpr hi
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfin.ne
    have hτ : conditionedSecondCoordinateFirstHit i.1.2 p = (t : ℕ∞) := ht.symm
    have htpos : 0 < t := by
      have hlevel := secondCoordinate_at_finite_firstHit i.1.2 t p hτ
      have hr := i.2.1
      by_contra hnot
      have htzero : t = 0 := by omega
      rw [htzero, h0] at hlevel
      omega
    rw [hsel, hτ]
    exact ENat.natCast_lt_natCast.mpr htpos

/-- positive branch of the past-map law at the source last cut T_{m_k}, for any
selector T satisfying the literal A_n ∩ B_n graph (T_m is not defined here; the
the grouped 4.13 source questions are not treated; not the paper result.
The branch restrictions are pairwise almost surely disjoint by the imported
firstHitPositiveBranches_pairwise_aedisjoint. -/
theorem selectedCutTime_positive_restrict_eq_sum
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    (conditionedVectorPathLaw 0 0).restrict {p | 0 < selectedCutTime T k p} =
      Measure.sum (fun i : PositiveBranchIx k =>
        (conditionedVectorPathLaw 0 0).restrict
          ((fun p => conditionedVectorShift
            (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
            firstHitPositiveBranchFuture i.1.1 i.1.2 k)) := by
  rw [Measure.restrict_congr_set (selectedCutTime_positive_event_ae T k hk hT)]
  exact firstHitPositiveBranches_restrict_union k

/-- positive branch of the past-map law at the source last cut T_{m_k}, for any
selector T satisfying the literal A_n ∩ B_n graph (T_m is not defined here; the
the grouped 4.13 source questions are not treated; not the paper result.
The finite selector branch events are exactly pairwise disjoint on all paths. -/
theorem selectedCutTime_positiveBranches_pairwise_disjoint
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) :
    Pairwise (fun i j : PositiveBranchIx k =>
      Disjoint
        {p | selectedCutTime T k p = conditionedSecondCoordinateFirstHit i.1.2 p ∧
          conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ ∧
          (p (conditionedSecondCoordinateFirstHit i.1.2 p).toNat).1 = (i.1.1 : ℤ)}
        {p | selectedCutTime T k p = conditionedSecondCoordinateFirstHit j.1.2 p ∧
          conditionedSecondCoordinateFirstHit j.1.2 p < ⊤ ∧
          (p (conditionedSecondCoordinateFirstHit j.1.2 p).toNat).1 = (j.1.1 : ℤ)}) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hτeq : conditionedSecondCoordinateFirstHit i.1.2 p =
      conditionedSecondCoordinateFirstHit j.1.2 p := hi.1.symm.trans hj.1
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hi.2.1.ne
  have hτi : conditionedSecondCoordinateFirstHit i.1.2 p = (t : ℕ∞) := ht.symm
  have hτj : conditionedSecondCoordinateFirstHit j.1.2 p = (t : ℕ∞) :=
    hτeq.symm.trans hτi
  have hiR := secondCoordinate_at_finite_firstHit i.1.2 t p hτi
  have hjR := secondCoordinate_at_finite_firstHit j.1.2 t p hτj
  have hlevels : i.1.2 = j.1.2 := by omega
  have hends : i.1.1 = j.1.1 := by
    have hei := hi.2.2
    have hej := hj.2.2
    rw [hτeq] at hei
    exact_mod_cast hei.symm.trans hej
  exact hij (Subtype.ext (Prod.ext hends hlevels))

/-- positive branch of the past-map law at the source last cut T_{m_k}, for any
selector T satisfying the literal A_n ∩ B_n graph (T_m is not defined here; the
the grouped 4.13 source questions are not treated; not the paper result.
This helper output uses the endpoint's right level and the proved stopped map;
it is none when that level is not positive. -/
@[expose] noncomputable def selectedCutPastMap
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (p : ℕ → ℤ × ℤ) :
    PositivePastMapOutput :=
  let r := (-(selectedCutFuture T k p 0).2).toNat
  if hr : 1 ≤ r then
    firstHitPositivePastMapEmbedding r (stoppedMap r hr (pathCode p))
  else none

/-- Measurability of the selected helper map toward lem-past-map
not the paper result. -/
theorem measurable_selectedCutPastMap
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectedCutPastMap T k) := by
  classical
  let F : (ℕ → ℤ × ℤ) × ℕ → PositivePastMapOutput := fun z =>
    if hr : 1 ≤ z.2 then
      firstHitPositivePastMapEmbedding z.2 (stoppedMap z.2 hr (pathCode z.1))
    else none
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro r
    by_cases hr : 1 ≤ r
    · simpa only [F, dite_eq_left hr, Function.comp_def] using
        (measurable_of_countable (firstHitPositivePastMapEmbedding r)).comp
          ((measurable_stoppedMap r hr).comp measurable_pathCode)
    · simpa only [F, dite_eq_right hr] using
        (measurable_const : Measurable (fun _ : ℕ → ℤ × ℤ =>
          (none : PositivePastMapOutput)))
  have hR : Measurable (fun p => (-(selectedCutFuture T k p 0).2).toNat) :=
    (measurable_of_countable (fun q : ℤ × ℤ => (-q.2).toNat)).comp
      ((measurable_pi_apply 0).comp (measurable_selectedCutFuture T k hT))
  exact hF.comp (measurable_id.prodMk hR)

private theorem selectedCutPastMap_eq_of_firstHit
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ)
    (hsel : selectedCutTime T k p = conditionedSecondCoordinateFirstHit r p)
    (hfin : conditionedSecondCoordinateFirstHit r p < ⊤) :
    selectedCutPastMap T k p =
      firstHitPositivePastMapEmbedding r (stoppedMap r hr (pathCode p)) := by
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  have hτ : conditionedSecondCoordinateFirstHit r p = (t : ℕ∞) := ht.symm
  have hlevel := secondCoordinate_at_finite_firstHit r t p hτ
  have hY : selectedCutFuture T k p 0 = p t := by
    simp only [selectedCutFuture, hsel, hτ, ENat.toNat_natCast,
      conditionedVectorShift, Nat.add_zero]
  have hR : (-(selectedCutFuture T k p 0).2).toNat = r := by
    rw [hY, hlevel]
    simp only [neg_neg, Int.toNat_natCast]
  dsimp only [selectedCutPastMap]
  rw [hR, dite_eq_left hr]

/-- positive branch of the past-map law at the source last cut T_{m_k}, for any
selector T satisfying the literal A_n ∩ B_n graph (T_m is not defined here; the
the grouped 4.13 source questions are not treated; not the paper result.
The restriction is unnormalized, so null branches are included. -/
theorem selectedCutPastMap_positive_joint_kernel_law
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let μ := conditionedVectorPathLaw 0 0
    let S := {p | 0 < selectedCutTime T k p}
    let Y := selectedCutFuture T k
    let C := selectedCutPastMap T k
    (μ.restrict S).map (fun p => (Y p, C p)) =
      (μ.restrict S).map Y ⊗ₘ firstHitPastMapPositiveKernel := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let E := fun i : PositiveBranchIx k =>
    (fun p => conditionedVectorShift
      (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
      firstHitPositiveBranchFuture i.1.1 i.1.2 k
  let Y := fun r p =>
    conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
  let C := fun i : PositiveBranchIx k => fun p =>
    firstHitPositivePastMapEmbedding i.1.2 (stoppedMap i.1.2 i.2.1 (pathCode p))
  have hYsel := measurable_selectedCutFuture T k hT
  have hCsel := measurable_selectedCutPastMap T k hT
  have hrestrict : μ.restrict {p | 0 < selectedCutTime T k p} =
      Measure.sum (fun i => μ.restrict (E i)) :=
    selectedCutTime_positive_restrict_eq_sum T k hk hT
  have hagree (i : PositiveBranchIx k) :
      (fun p => (selectedCutFuture T k p, selectedCutPastMap T k p)) =ᵐ[
        μ.restrict (E i)] fun p => (Y i.1.2 p, C i p) := by
    have hE : MeasurableSet (E i) :=
      (measurable_conditionedFirstHit_future i.1.2)
        (measurableSet_firstHitPositiveBranchFuture i.1.1 i.1.2 k)
    filter_upwards [ae_restrict_of_ae
      (selectedCut_branch_iff_ae T k i.1.2 i.1.1 i.2.1 i.2.2 hT),
      ae_restrict_mem hE] with p hb hp
    obtain ⟨hsel, hfin, _⟩ := hb.mpr hp
    apply Prod.ext
    · change conditionedVectorShift (selectedCutTime T k p).toNat p = _
      rw [hsel]
    · exact selectedCutPastMap_eq_of_firstHit T k i.1.2 i.2.1 p hsel hfin
  have hsumY : (μ.restrict {p | 0 < selectedCutTime T k p}).map
      (selectedCutFuture T k) =
      Measure.sum (fun i => (μ.restrict (E i)).map (Y i.1.2)) := by
    rw [hrestrict, Measure.map_sum hYsel.aemeasurable]
    apply congrArg Measure.sum
    funext i
    apply Measure.map_congr
    filter_upwards [hagree i] with p hp
    exact congrArg Prod.fst hp
  calc
    _ = Measure.sum (fun i => (μ.restrict (E i)).map
        (fun p => (Y i.1.2 p, C i p))) := by
      rw [hrestrict, Measure.map_sum (hYsel.prodMk hCsel).aemeasurable]
      apply congrArg Measure.sum
      funext i
      exact Measure.map_congr (hagree i)
    _ = (Measure.sum (fun i => (μ.restrict (E i)).map (Y i.1.2))) ⊗ₘ
        firstHitPastMapPositiveKernel :=
      firstHitPastMapPositiveBranches_joint_kernel_law k
    _ = _ := by rw [hsumY]

end DirectedDistances.PaperProofs.Section4
