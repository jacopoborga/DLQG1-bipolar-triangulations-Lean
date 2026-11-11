module

public import DirectedDistances.RandomWalk.ConditionedStrongMarkov
public import DirectedDistances.RandomWalk.RenewalStoppedHistory
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import DirectedDistances.Paper.Section4.WalkPosProb

/-! Helper toward lem-uiqbot-boltzmann / Lemma 7.9
of −r, the post-hit minimum of L is uniform on {0,…,L(τ_r)} (strong Markov +
Lemma 4.10). This is the POST-hit minimum, not the earlier minimum displayed in
eqn-left-bdy-time (candidate issue D15); the marked-law assembly is not treated;
not the paper result. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
conditional infimum defaults to zero if the future range is unbounded below;
this branch is null for the conditioned law. It is not the earlier minimum in
eqn-left-bdy-time (candidate issue D15). The marked-law assembly is not treated;
not the paper result. -/
@[expose] noncomputable def postHitMinimum (r : ℕ) (p : ℕ → ℤ × ℤ) : ℤ :=
  ⨅ n : ℕ, (p ((conditionedSecondCoordinateFirstHit r p).toNat + n)).1

private theorem measurable_past_event (k : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[conditionedVectorPast k] A) : MeasurableSet A := by
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix k)

private theorem measurable_hit_nat (r : ℕ) :
    Measurable (fun p => (conditionedSecondCoordinateFirstHit r p).toNat) := by
  apply (measurable_of_countable ENat.toNat).comp
  apply ENat.measurable_iff.mpr
  intro k
  exact measurable_past_event k _ (measurableSet_conditionedVectorPast_firstHit_eq r k)

private theorem measurable_hit_eval (r n : ℕ) :
    Measurable (fun p : ℕ → ℤ × ℤ =>
      p ((conditionedSecondCoordinateFirstHit r p).toNat + n)) := by
  have he : Measurable (fun z : (ℕ → ℤ × ℤ) × ℕ => z.1 (z.2 + n)) :=
    measurable_from_prod_countable_left fun k => measurable_pi_apply (k + n)
  exact he.comp (measurable_id.prodMk (measurable_hit_nat r))

/-- Measurability of the POST-hit minimum helper for Lemma 7.9 -/
theorem measurable_postHitMinimum (r : ℕ) : Measurable (postHitMinimum r) := by
  exact Measurable.iInf fun n => (measurable_hit_eval r n).fst

private theorem nonneg_ae (x : ℕ) (y : ℤ) :
    ∀ᵐ p ∂conditionedVectorPathLaw x y, ∀ n, 0 ≤ (p n).1 := by
  unfold conditionedVectorPathLaw
  apply (ae_map_iff (by fun_prop) ?_).mpr
  · exact Eventually.of_forall fun p n => Int.natCast_nonneg _
  · change MeasurableSet {p : ℕ → ℤ × ℤ | ∀ n, 0 ≤ (p n).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_le measurable_const (measurable_pi_apply n).fst

private theorem start_ae (x : ℕ) (y : ℤ) :
    ∀ᵐ p ∂conditionedVectorPathLaw x y, p 0 = ((x : ℤ), y) := by
  unfold conditionedVectorPathLaw conditionedVectorTrajectory
  apply (ae_map_iff (by fun_prop)
    ((measurableSet_singleton _).preimage (measurable_pi_apply 0))).mpr
  filter_upwards [DirectedDistances.Probability.markovTrajectory_ae_start
    conditionedVectorKernel (x, y)] with p hp
  simp only [Set.mem_singleton_iff, hp]

private theorem minimum_spec (r : ℕ) (p : ℕ → ℤ × ℤ)
    (hp : ∀ n, 0 ≤ (p n).1) :
    (∃ n, (p ((conditionedSecondCoordinateFirstHit r p).toNat + n)).1 =
      postHitMinimum r p) ∧
    ∀ n, postHitMinimum r p ≤
      (p ((conditionedSecondCoordinateFirstHit r p).toNat + n)).1 := by
  have hb : BddBelow (Set.range (fun n : ℕ =>
      (p ((conditionedSecondCoordinateFirstHit r p).toNat + n)).1)) :=
    ⟨0, by rintro z ⟨n, rfl⟩; exact hp _⟩
  exact ⟨Int.csInf_mem (Set.range_nonempty _) hb, fun n => ciInf_le hb n⟩

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
bounds every value after the hit, almost surely. Candidate issue D15's earlier
minimum and the marked-law assembly are not treated; not the paper result. -/
theorem postHitMinimum_attained_ae (r : ℕ) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (∃ s, (conditionedSecondCoordinateFirstHit r p).toNat ≤ s ∧
        (p s).1 = postHitMinimum r p) ∧
      (∀ s, (conditionedSecondCoordinateFirstHit r p).toNat ≤ s →
        postHitMinimum r p ≤ (p s).1) ∧ 0 ≤ postHitMinimum r p := by
  filter_upwards [nonneg_ae 0 0] with p hp
  obtain ⟨⟨n, hn⟩, hmin⟩ := minimum_spec r p hp
  refine ⟨⟨_, Nat.le_add_right _ _, hn⟩, ?_, ?_⟩
  · intro s hs
    simpa only [Nat.add_sub_of_le hs] using hmin
      (s - (conditionedSecondCoordinateFirstHit r p).toNat)
  · rw [← hn]
    exact hp _

private theorem barrier_law (x j : ℕ) (y : ℤ) :
    conditionedVectorPathLaw x y {p | ∀ n, (j : ℤ) ≤ (p n).1} =
      if j ≤ x then ENNReal.ofReal
        ((((x - j : ℕ) : ℝ) + 1) / ((x : ℝ) + 1)) else 0 := by
  by_cases hj : j ≤ x
  · rw [ite_eq_left hj]
    have h := DirectedDistances.Paper.Section4.conditioned_walk_barrier_probability
      x y (conditionedVectorPathLaw x y) (conditionedVectorPathLaw_map_prefix x y)
      (x - j) (Nat.sub_le _ _)
    have he : (x : ℤ) - ((x - j : ℕ) : ℤ) = (j : ℤ) := by omega
    rw [he] at h
    rw [← ofReal_measureReal, h]
  · rw [ite_eq_right hj]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [start_ae x y] with p hp hbar
    have hh := hbar 0
    rw [hp] at hh
    simp only at hh
    omega

private theorem future_minimum_tail (x j : ℕ) (y : ℤ) :
    conditionedVectorPathLaw x y {q | (j : ℤ) ≤ ⨅ n : ℕ, (q n).1} =
      if j ≤ x then ENNReal.ofReal
        ((((x - j : ℕ) : ℝ) + 1) / ((x : ℝ) + 1)) else 0 := by
  rw [← barrier_law x j y]
  apply measure_congr
  filter_upwards [nonneg_ae x y] with q hq
  have hb : BddBelow (Set.range (fun n : ℕ => (q n).1)) :=
    ⟨0, by rintro z ⟨n, rfl⟩; exact hq n⟩
  exact propext (le_ciInf_iff hb)

private theorem future_minimum_atom (x j : ℕ) (y : ℤ) :
    conditionedVectorPathLaw x y {q | (⨅ n : ℕ, (q n).1) = (j : ℤ)} =
      if j ≤ x then ENNReal.ofReal (1 / ((x : ℝ) + 1)) else 0 := by
  let ν := conditionedVectorPathLaw x y
  let E : ℕ → Set (ℕ → ℤ × ℤ) := fun k => {q | (k : ℤ) ≤ ⨅ n : ℕ, (q n).1}
  have hm : ∀ k, MeasurableSet (E k) := fun k =>
    measurableSet_le measurable_const (Measurable.iInf fun n =>
      (measurable_pi_apply n).fst)
  have hs : E (j + 1) ⊆ E j := by
    intro q hq
    change (j : ℤ) ≤ ⨅ n : ℕ, (q n).1
    change ((j + 1 : ℕ) : ℤ) ≤ ⨅ n : ℕ, (q n).1 at hq
    omega
  have he : {q : ℕ → ℤ × ℤ | (⨅ n : ℕ, (q n).1) = (j : ℤ)} =
      E j \ E (j + 1) := by
    ext q
    simp only [E, Set.mem_sdiff, Set.mem_ofPred_eq]
    omega
  rw [he, measure_sdiff hs (hm _).nullMeasurableSet (measure_ne_top ν _)]
  change ν (E j) - ν (E (j + 1)) = _
  rw [future_minimum_tail x j y, future_minimum_tail x (j + 1) y]
  by_cases hj : j ≤ x
  · simp only [hj, ↓reduceIte]
    by_cases hj' : j + 1 ≤ x
    · rw [ite_eq_left hj', ← ENNReal.ofReal_sub _ (by positivity)]
      congr 1
      have hc : ((x - j : ℕ) : ℝ) = ((x - (j + 1) : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show x - j = x - (j + 1) + 1 by omega)
      rw [hc]
      ring
    · rw [ite_eq_right hj', tsub_zero]
      have hx : x = j := by omega
      simp only [hx, Nat.sub_self, Nat.cast_zero, zero_add]
  · simp only [hj, show ¬j + 1 ≤ x by omega, ↓reduceIte, zero_tsub]

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
against every stopped-past event, by strong Markov and Lemma 4.10. The endpoint
is nonnegative almost surely, so its `toNat` is exact. The earlier minimum in
eqn-left-bdy-time (candidate issue D15) and marked-law assembly are not treated;
not the paper result. -/
theorem postHitMinimum_tail (r j : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : ∀ k : ℕ, MeasurableSet[conditionedVectorPast k]
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)})) :
    conditionedVectorPathLaw 0 0
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (j : ℤ) ≤ postHitMinimum r p}) =
      ∫⁻ p in A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤},
        if j ≤ (p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat then
          ENNReal.ofReal
            (((((p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat - j : ℕ) :
              ℝ) + 1) /
              (((p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat : ℝ) + 1))
        else 0 ∂conditionedVectorPathLaw 0 0 := by
  let B : Set (ℕ → ℤ × ℤ) := {q | ∀ n, (j : ℤ) ≤ (q n).1}
  have hB : MeasurableSet B := by
    change MeasurableSet {q : ℕ → ℤ × ℤ | ∀ n, (j : ℤ) ≤ (q n).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_le measurable_const (measurable_pi_apply n).fst
  have h := conditionedVectorPathLaw_strongMarkov 0 0
    (conditionedSecondCoordinateFirstHit r)
    (measurableSet_conditionedVectorPast_firstHit_eq r) A hA B hB
  have he :
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (j : ℤ) ≤ postHitMinimum r p}) =ᵐ[conditionedVectorPathLaw 0 0]
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | conditionedVectorShift
          (conditionedSecondCoordinateFirstHit r p).toNat p ∈ B}) := by
    filter_upwards [nonneg_ae 0 0] with p hp
    obtain ⟨_, hmin⟩ := minimum_spec r p hp
    have hi : (j : ℤ) ≤ postHitMinimum r p ↔
        ∀ n, (j : ℤ) ≤
          (p ((conditionedSecondCoordinateFirstHit r p).toNat + n)).1 := by
      constructor
      · intro hj n
        exact hj.trans (hmin n)
      · exact fun hh => le_ciInf hh
    exact propext (and_congr Iff.rfl hi)
  rw [measure_congr he, h]
  apply lintegral_congr
  intro p
  exact barrier_law _ j _

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
R-hit of −r, the POST-hit minimum of L is uniform on {0,…,L(τ_r)}, by strong
Markov and Lemma 4.10. The earlier minimum in eqn-left-bdy-time (candidate issue
D15) and the marked-law assembly are not treated; not the paper result. -/
theorem postHitMinimum_uniform (r j : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : ∀ k : ℕ, MeasurableSet[conditionedVectorPast k]
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)})) :
    conditionedVectorPathLaw 0 0
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | postHitMinimum r p = (j : ℤ)}) =
      ∫⁻ p in A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤},
        if j ≤ (p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat then
          ENNReal.ofReal
            (1 / (((p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat : ℝ) + 1))
        else 0 ∂conditionedVectorPathLaw 0 0 := by
  let B : Set (ℕ → ℤ × ℤ) := {q | (⨅ n : ℕ, (q n).1) = (j : ℤ)}
  have hB : MeasurableSet B :=
    (measurableSet_singleton _).preimage
      (Measurable.iInf fun n => (measurable_pi_apply n).fst)
  have h := conditionedVectorPathLaw_strongMarkov 0 0
    (conditionedSecondCoordinateFirstHit r)
    (measurableSet_conditionedVectorPast_firstHit_eq r) A hA B hB
  change conditionedVectorPathLaw 0 0
      (A ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | postHitMinimum r p = (j : ℤ)}) = _ at h
  rw [h]
  apply lintegral_congr
  intro p
  exact future_minimum_atom _ j _

/-- The full stopped prefix, including its terminal point, used by the POST-hit
infinite hit the `toNat` convention gives the time-zero prefix; the kernel law
below restricts to finite hits. Not the marked-law assembly or paper result. -/
@[expose] noncomputable def postHitMinimumPast (r : ℕ) (p : ℕ → ℤ × ℤ) :
    Σ n : ℕ, Fin (n + 1) → ℤ × ℤ :=
  stoppedVectorHistory (fun q => (conditionedSecondCoordinateFirstHit r q).toNat) id p

private theorem measurable_minimum_past (r : ℕ) :
    Measurable (postHitMinimumPast r) :=
  measurable_stoppedVectorHistory _ _ (measurable_hit_nat r) measurable_id

private theorem minimum_past_event (r : ℕ)
    (H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) (hH : MeasurableSet H) (k : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      (postHitMinimumPast r ⁻¹' H ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}) := by
  have he : postHitMinimumPast r ⁻¹' H ∩
      {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
      (fun p => (⟨k, conditionedVectorPrefix k p⟩ :
        Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) ⁻¹' H ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
    ext p
    by_cases hp : conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)
    · simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hp, and_true]
      have ht : (conditionedSecondCoordinateFirstHit r p).toNat = k := by
        rw [hp]
        rfl
      change (⟨(conditionedSecondCoordinateFirstHit r p).toNat, fun j => p j.val⟩ :
        Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ∈ H ↔ _
      rw [ht]
      rfl
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hp, and_false]
  rw [he]
  apply MeasurableSet.inter _ (measurableSet_conditionedVectorPast_firstHit_eq r k)
  refine ⟨(Sigma.mk (β := fun n : ℕ => Fin (n + 1) → ℤ × ℤ) k) ⁻¹' H, ?_, rfl⟩
  exact hH.preimage (Measurable.of_le_map (iInf_le _ k))

private instance minimum_history_singletons :
    MeasurableSingletonClass (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) where
  measurableSet_singleton h := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro n
    change MeasurableSet (Sigma.mk n ⁻¹' {h})
    exact (Set.to_countable _).measurableSet

/-- Uniform law on {0,…,a} for the endpoint height a of a stopped prefix.
Helper toward lem-uiqbot-boltzmann / Lemma 7.9
not the paper result. -/
@[expose] noncomputable def postHitMinimumKernel :
    Kernel (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ℕ where
  toFun h := Measure.uniformOfFinset (Finset.range ((h.2 (Fin.last h.1)).1.toNat + 1))
  measurable' := by
    let _ := minimum_history_singletons
    exact measurable_of_countable _

/-- The POST-hit minimum kernel is normalized, for the helper toward Lemma 7.9 -/
instance postHitMinimumKernel_isMarkovKernel : IsMarkovKernel postHitMinimumKernel where
  isProbabilityMeasure h := by
    constructor
    change Measure.uniformOfFinset
      (Finset.range ((h.2 (Fin.last h.1)).1.toNat + 1)) Set.univ = 1
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true, Finset.card_range,
      Nat.cast_add, Nat.cast_one]
    exact ENNReal.div_self (by positivity) (by finiteness)

private theorem minimum_kernel_atom (h : Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) (j : ℕ) :
    postHitMinimumKernel h {j} =
      if j ≤ (h.2 (Fin.last h.1)).1.toNat then
        ENNReal.ofReal (1 / (((h.2 (Fin.last h.1)).1.toNat : ℝ) + 1)) else 0 := by
  change Measure.uniformOfFinset
    (Finset.range ((h.2 (Fin.last h.1)).1.toNat + 1)) {j} = _
  rw [Measure.uniformOfFinset_apply_singleton]
  simp only [Finset.mem_range, Nat.lt_succ_iff, Finset.card_range]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
  simp

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
R-hit of −r, the POST-hit minimum is uniform on {0,…,L(τ_r)} (strong Markov +
Lemma 4.10), as a joint kernel law. This is not the earlier minimum displayed
in eqn-left-bdy-time (candidate issue D15); the marked-law assembly is not
treated; not the paper result. -/
theorem postHitMinimum_kernel (r : ℕ) :
    ((conditionedVectorPathLaw 0 0).restrict
      {p | conditionedSecondCoordinateFirstHit r p < ⊤}).map
        (fun p => (postHitMinimumPast r p, (postHitMinimum r p).toNat)) =
      (((conditionedVectorPathLaw 0 0).restrict
        {p | conditionedSecondCoordinateFirstHit r p < ⊤}).map
          (postHitMinimumPast r)) ⊗ₘ postHitMinimumKernel := by
  let μ := conditionedVectorPathLaw 0 0
  let F : Set (ℕ → ℤ × ℤ) := {p | conditionedSecondCoordinateFirstHit r p < ⊤}
  apply Measure.ext_of_singleton
  rintro ⟨h, j⟩
  have hA := minimum_past_event r {h} (measurableSet_singleton h)
  have hu := postHitMinimum_uniform r j (postHitMinimumPast r ⁻¹' {h}) hA
  have hm : Measurable (fun p => (postHitMinimumPast r p, (postHitMinimum r p).toNat)) :=
    (measurable_minimum_past r).prodMk
      ((measurable_of_countable Int.toNat).comp (measurable_postHitMinimum r))
  rw [Measure.map_apply hm (measurableSet_singleton _),
    Measure.restrict_apply ((measurableSet_singleton _).preimage hm)]
  have he :
      ((fun p => (postHitMinimumPast r p, (postHitMinimum r p).toNat)) ⁻¹' {(h, j)} ∩ F)
        =ᵐ[μ]
      (postHitMinimumPast r ⁻¹' {h} ∩ F ∩ {p | postHitMinimum r p = (j : ℤ)}) := by
    filter_upwards [postHitMinimum_attained_ae r] with p hp
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, Set.mem_ofPred_eq]
    have hn := hp.2.2
    have hj : (postHitMinimum r p).toNat = j ↔ postHitMinimum r p = (j : ℤ) := by
      omega
    rw [hj]
    apply propext
    tauto
  rw [measure_congr he, hu]
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod
    (measurableSet_singleton h) (measurableSet_singleton j)]
  rw [setLIntegral_map (measurableSet_singleton h)
    (Kernel.measurable_coe postHitMinimumKernel (measurableSet_singleton j))
    (measurable_minimum_past r), Measure.restrict_restrict
      ((measurableSet_singleton h).preimage (measurable_minimum_past r))]
  apply lintegral_congr
  intro p
  exact (minimum_kernel_atom (postHitMinimumPast r p) j).symm

end DirectedDistances.RandomWalk
