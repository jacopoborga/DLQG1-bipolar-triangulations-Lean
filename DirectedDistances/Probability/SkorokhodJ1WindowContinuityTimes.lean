module

public import DirectedDistances.Probability.SkorokhodJ1WindowBorel
import DirectedDistances.Probability.SkorokhodJ1WindowDEvalInterior
import DirectedDistances.Probability.SkorokhodModulus
import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section
namespace DirectedDistances.Probability

open Filter MeasureTheory Set
open scoped Topology ENNReal



def continuityTimes {T : ℝ} {hT : 0 < T}
    (μ : Measure (J1WindowD T hT)) : Set (J1Window T) :=
  {t | ∀ᵐ x ∂μ, ContinuousAt x.path.1 t}

private theorem cadlag_continuousAt_zero {T : ℝ} (hT : 0 < T)
    (f : CadlagWindow T) :
    ContinuousAt f.1 (⟨0, le_rfl, hT.le⟩ : J1Window T) := by
  let t : J1Window T := ⟨0, le_rfl, hT.le⟩
  have hright : ContinuousWithinAt f.1 (Ioi t) t := f.2.isRightContinuous t
  have hIci : (Ici t : Set (J1Window T)) = univ := by
    ext y
    simp only [mem_Ici, mem_univ, iff_true]
    change (0 : ℝ) ≤ (y : ℝ)
    exact y.property.1
  change Tendsto f.1 (𝓝 t) (𝓝 (f.1 t))
  rw [← nhdsWithin_univ t, ← hIci,
    ← nhdsGT_sup_nhdsWithin_singleton t, tendsto_sup]
  exact ⟨hright, by simpa only [nhdsWithin_singleton] using
    (tendsto_pure_nhds f.1 t)⟩




theorem zero_mem_continuityTimes {T : ℝ} {hT : 0 < T}
    (μ : Measure (J1WindowD T hT)) :
    (⟨0, le_rfl, hT.le⟩ : J1Window T) ∈ continuityTimes μ := by
  change ∀ᵐ x ∂μ, ContinuousAt x.path.1 _
  filter_upwards [] with x
  exact cadlag_continuousAt_zero hT x.path




theorem cadlag_continuousAt_endpoint_iff_leftLim_eq {T : ℝ} (hT : 0 < T)
    (f : CadlagWindow T) :
    ContinuousAt f.1 (⟨T, hT.le, le_rfl⟩ : J1Window T) ↔
      f.1.leftLim ⟨T, hT.le, le_rfl⟩ = f.1 ⟨T, hT.le, le_rfl⟩ := by
  let t : J1Window T := ⟨T, hT.le, le_rfl⟩
  have htTop (s : J1Window T) : s ≤ t := s.property.2
  have hset : (Iio t ∪ {t} : Set (J1Window T)) = univ := by
    ext s
    simp only [mem_union, mem_Iio, mem_singleton_iff, mem_univ, iff_true]
    rcases eq_or_lt_of_le (htTop s) with h | h
    · exact Or.inr h
    · exact Or.inl h
  constructor
  · intro hcont
    have hIic : ContinuousWithinAt f.1 (Iic t) t :=
      hcont.continuousWithinAt.mono (Set.subset_univ _)
    exact hIic.leftLim_eq
  · intro heq
    have hleft := f.2.tendsto_nhdsLT_leftLim t
    rw [heq] at hleft
    change Tendsto f.1 (𝓝 t) (𝓝 (f.1 t))
    rw [← nhdsWithin_univ t, ← hset, nhdsWithin_union, tendsto_sup]
    exact ⟨hleft, by simpa only [nhdsWithin_singleton] using
      (tendsto_pure_nhds f.1 t)⟩




theorem endpoint_mem_continuityTimes_iff_leftLim_eq {T : ℝ} {hT : 0 < T}
    (μ : Measure (J1WindowD T hT)) :
    (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ continuityTimes μ ↔
      ∀ᵐ x ∂μ,
        x.path.1.leftLim ⟨T, hT.le, le_rfl⟩ = x.path.1 ⟨T, hT.le, le_rfl⟩ := by
  change (∀ᵐ x ∂μ, ContinuousAt x.path.1
      (⟨T, hT.le, le_rfl⟩ : J1Window T)) ↔
    ∀ᵐ x ∂μ,
      x.path.1.leftLim ⟨T, hT.le, le_rfl⟩ = x.path.1 ⟨T, hT.le, le_rfl⟩
  exact eventually_congr (Filter.Eventually.of_forall fun
    (x : J1WindowD T hT) =>
      cadlag_continuousAt_endpoint_iff_leftLim_eq hT x.path)

end DirectedDistances.Probability

namespace DirectedDistances.Probability

open Filter MeasureTheory Set
open scoped Topology ENNReal

private noncomputable def leftLimApproxTime {T : ℝ} (t : J1Window T)
    (ht : 0 < (t : ℝ)) (n : ℕ) : J1Window T := by
  let s := (t : ℝ) - (t : ℝ) / ((n : ℝ) + 2)
  have hden : 1 < (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdenpos : 0 < (n : ℝ) + 2 := by linarith
  have hquotpos : 0 < (t : ℝ) / ((n : ℝ) + 2) := div_pos ht hdenpos
  have hquotlt : (t : ℝ) / ((n : ℝ) + 2) < t := div_lt_self ht hden
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hsle : s ≤ t := by
    dsimp [s]
    linarith
  exact ⟨s, ⟨hs.le, hsle.trans t.property.2⟩⟩

private theorem leftLimApproxTime_lt {T : ℝ} (t : J1Window T)
    (ht : 0 < (t : ℝ)) (n : ℕ) : (leftLimApproxTime t ht n : ℝ) < t := by
  change (t : ℝ) - (t : ℝ) / ((n : ℝ) + 2) < t
  have hden : 0 < (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hquot : 0 < (t : ℝ) / ((n : ℝ) + 2) := div_pos ht hden
  linarith

private theorem tendsto_leftLimApproxTime {T : ℝ} (t : J1Window T)
    (ht : 0 < (t : ℝ)) :
    Tendsto (leftLimApproxTime t ht) atTop (𝓝[<] t) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (leftLimApproxTime t ht)
  · apply tendsto_subtype_rng.2
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
      exact (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    have hconv := (tendsto_const_nhds (x := (t : ℝ))).sub
      ((tendsto_const_nhds (x := (t : ℝ))).mul hinv)
    simpa [leftLimApproxTime, div_eq_mul_inv] using hconv
  · filter_upwards [] with n
    exact leftLimApproxTime_lt t ht n




theorem measurable_j1WindowD_leftLim {T : ℝ} (hT : 0 < T)
    (t : J1Window T) (ht : 0 < (t : ℝ)) :
    Measurable (fun x : J1WindowD T hT => x.path.1.leftLim t) := by
  apply measurable_of_tendsto_metrizable (f := fun n x => x.path.1
    (leftLimApproxTime t ht n))
  · intro n
    exact measurable_j1WindowD_eval hT (leftLimApproxTime t ht n)
  · rw [tendsto_pi_nhds]
    intro x
    exact (x.path.2.tendsto_nhdsLT_leftLim t).comp
      (tendsto_leftLimApproxTime t ht)




noncomputable def j1WindowJump {T : ℝ} {hT : 0 < T}
    (x : J1WindowD T hT) (t : J1Window T) : ℝ :=
  if (t : ℝ) = 0 then 0 else |x.path.1 t - x.path.1.leftLim t|




theorem measurableSet_j1WindowJump_gt {T : ℝ} (hT : 0 < T)
    (t : J1Window T) (ε : ℝ) :
    MeasurableSet {x : J1WindowD T hT | ε < j1WindowJump x t} := by
  by_cases ht : (t : ℝ) = 0
  · simp [j1WindowJump, ht]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hleft := measurable_j1WindowD_leftLim hT t htpos
    have heval := measurable_j1WindowD_eval hT t
    simp only [j1WindowJump, ite_eq_right ht]
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (heval.sub hleft))




theorem cadlag_continuousAt_iff_j1WindowJump_eq_zero {T : ℝ} {hT : 0 < T}
    (x : J1WindowD T hT) (t : J1Window T) :
    ContinuousAt x.path.1 t ↔ j1WindowJump x t = 0 := by
  by_cases ht : (t : ℝ) = 0
  · have heq : t = ⟨0, le_rfl, hT.le⟩ := Subtype.ext ht
    subst t
    have hcont := cadlag_continuousAt_zero hT x.path
    simp [j1WindowJump, hcont]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hbelow : ∃ s : J1Window T, s < t := by
      refine ⟨⟨0, le_rfl, hT.le⟩, ?_⟩
      change (0 : ℝ) < (t : ℝ)
      exact htpos
    let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt hbelow
    have hleft : ContinuousWithinAt x.path.1 (Iio t) t ↔
        x.path.1.leftLim t = x.path.1 t := by
      constructor
      · intro h
        exact tendsto_nhds_unique
          (x.path.2.tendsto_nhdsLT_leftLim t) h.tendsto
      · intro heq
        have hlim := x.path.2.tendsto_nhdsLT_leftLim t
        rw [heq] at hlim
        exact hlim
    have hright : ContinuousWithinAt x.path.1 (Ioi t) t :=
      x.path.2.isRightContinuous t
    constructor
    · intro hcont
      have hpair := (continuousAt_iff_continuous_left'_right').mp hcont
      have heq := hleft.mp hpair.1
      simp only [j1WindowJump, ite_eq_right ht]
      rw [heq]
      simp
    · intro hjump
      have heq : x.path.1.leftLim t = x.path.1 t := by
        simp only [j1WindowJump, ite_eq_right ht] at hjump
        exact (sub_eq_zero.mp (abs_eq_zero.mp hjump)).symm
      exact (continuousAt_iff_continuous_left'_right').mpr
        ⟨hleft.mpr heq, hright⟩

private theorem continuityTimes_exists_block
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (s : J1Window T) (hsT : (s : ℝ) < T) :
    ∃ i : Fin p.n, p.time i.castSucc ≤ s ∧ s < p.time i.succ := by
  classical
  let q : Finset (Fin (p.n + 1)) :=
    Finset.univ.filter fun j => (s : ℝ) < (p.time j : ℝ)
  have hq : q.Nonempty := by
    refine ⟨Fin.last p.n, ?_⟩
    simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [p.last]
    exact hsT
  let j := q.min' hq
  have hjq : j ∈ q := Finset.min'_mem q hq
  have hjs : (s : ℝ) < (p.time j : ℝ) := by
    simpa only [q, Finset.mem_filter, Finset.mem_univ, true_and] using hjq
  have hjpos : 0 < j.val := by
    by_contra hj
    have hjzero : j.val = 0 := by omega
    have htime : p.time j = p.time 0 := by
      apply congrArg p.time
      apply Fin.ext
      exact hjzero
    rw [htime, p.first] at hjs
    exact (not_lt_of_ge s.property.1) hjs
  let i : Fin p.n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have hji : i.succ = j := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp [i]
    omega
  have hleft : p.time i.castSucc ≤ s := by
    by_contra hnot
    have hprev : (s : ℝ) < (p.time i.castSucc : ℝ) := by
      exact_mod_cast (lt_of_not_ge hnot)
    have hprev_mem : i.castSucc ∈ q := by
      simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hprev
    have hmin := Finset.min'_le q i.castSucc hprev_mem
    have hmin' : i.succ ≤ i.castSucc := by simpa [hji] using hmin
    have hvals : (i.succ).val ≤ (i.castSucc).val := by exact_mod_cast hmin'
    simp only [Fin.val_succ, Fin.val_castSucc] at hvals
    omega
  refine ⟨i, hleft, ?_⟩
  rw [hji]
  exact_mod_cast hjs



theorem finite_setOf_j1WindowJump_gt {T : ℝ} {hT : 0 < T}
    (x : J1WindowD T hT) (ε : ℝ) (hε : 0 < ε) :
    {t : J1Window T | ε < j1WindowJump x t}.Finite := by
  classical
  obtain ⟨p, hp⟩ := exists_partition_oscillation_lt hT x.path hε
  apply (Set.finite_range p.time).subset
  intro t ht
  by_contra hnot
  have htT : (t : ℝ) < T := by
    apply lt_of_le_of_ne t.property.2
    intro heq
    apply hnot
    refine ⟨Fin.last p.n, ?_⟩
    rw [p.last]
    exact Subtype.ext heq.symm
  obtain ⟨i, hle, hright⟩ := continuityTimes_exists_block p t htT
  have hleft : p.time i.castSucc < t := lt_of_le_of_ne hle (by
    intro heq
    exact hnot ⟨i.castSucc, heq⟩)
  have htpos : 0 < (t : ℝ) := lt_of_le_of_lt (p.time i.castSucc).property.1 hleft
  have htzero : (t : ℝ) ≠ 0 := ne_of_gt htpos
  have hconv : Tendsto (leftLimApproxTime t htpos) atTop (𝓝 t) :=
    (tendsto_leftLimApproxTime t htpos).mono_right nhdsWithin_le_nhds
  have hbound : ∀ᶠ n : ℕ in atTop,
      |x.path.1 t - x.path.1 (leftLimApproxTime t htpos n)| ≤
        blockOscillation x.path (p.time i.castSucc) (p.time i.succ) := by
    filter_upwards [(tendsto_order.mp hconv).1 _ hleft] with n hn
    apply le_csSup (blockOscillation_values_bddAbove x.path _ _)
    exact ⟨t, leftLimApproxTime t htpos n, hle, hright, hn.le,
      (leftLimApproxTime_lt t htpos n).trans hright, rfl⟩
  have hlim := (tendsto_const_nhds (x := x.path.1 t)).sub
    ((x.path.2.tendsto_nhdsLT_leftLim t).comp
      (tendsto_leftLimApproxTime t htpos))
  have hlejump := le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hlim) hbound
  have hjump : j1WindowJump x t < ε := by
    simp only [j1WindowJump, ite_eq_right htzero]
    exact hlejump.trans_lt (hp i)
  exact (not_lt_of_ge hjump.le) ht

private theorem finite_jump_measure_ge {T : ℝ} {hT : 0 < T}
    (μ : Measure (J1WindowD T hT)) [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    {t : J1Window T | δ ≤ μ {x | ε < j1WindowJump x t}}.Finite := by
  classical
  by_contra hinf
  let B := {t : J1Window T | δ ≤ μ {x | ε < j1WindowJump x t}}
  have hB : B.Infinite := hinf
  let e : ℕ ↪ B := Set.Infinite.natEmbedding B hB
  let t : ℕ → J1Window T := fun n => (e n).val
  have ht : Function.Injective t := Subtype.val_injective.comp e.injective
  let J : ℕ → Set (J1WindowD T hT) := fun n => {x | ε < j1WindowJump x (t n)}
  let A : ℕ → Set (J1WindowD T hT) := fun N => ⋃ n, ⋃ (_ : N ≤ n), J n
  have hA (N : ℕ) : MeasurableSet (A N) :=
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      measurableSet_j1WindowJump_gt hT (t n) ε
  have hanti : Antitone A := by
    intro N M hNM x hx
    rcases mem_iUnion.mp hx with ⟨n, hn⟩
    rcases mem_iUnion.mp hn with ⟨hMn, hxn⟩
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hNM.trans hMn, hxn⟩⟩
  have hempty : (⋂ N, A N) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hfin : {n : ℕ | ε < j1WindowJump x (t n)}.Finite :=
      (finite_setOf_j1WindowJump_gt x ε hε).preimage ht.injOn
    obtain ⟨k, hk⟩ := hfin.bddAbove
    obtain ⟨n, hn⟩ := mem_iUnion.mp (mem_iInter.mp hx (k + 1))
    obtain ⟨hkn, hxn⟩ := mem_iUnion.mp hn
    have hnk : n ≤ k := hk hxn
    omega
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun N => (hA N).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hempty, measure_empty] at hlim
  have hbound (N : ℕ) : δ ≤ μ (A N) := by
    apply (e N).property.trans
    apply measure_mono
    intro x hx
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨le_rfl, hx⟩⟩
  exact (not_le_of_gt hδ) (ge_of_tendsto hlim (Eventually.of_forall hbound))




theorem countable_compl_continuityTimes {T : ℝ} {hT : 0 < T}
    (μ : Measure (J1WindowD T hT)) [IsFiniteMeasure μ] :
    (continuityTimes μ)ᶜ.Countable := by
  classical
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  let B : ℕ → ℕ → Set (J1Window T) := fun m j =>
    {t | ENNReal.ofReal (c j) ≤ μ {x | c m < j1WindowJump x t}}
  have hcount : (⋃ m, ⋃ j, B m j).Countable :=
    Set.countable_iUnion fun m => Set.countable_iUnion fun j =>
      (finite_jump_measure_ge μ (c m) (hc m) (ENNReal.ofReal (c j))
        (ENNReal.ofReal_pos.mpr (hc j))).countable
  apply hcount.mono
  intro t ht
  have hex : ∃ m : ℕ, μ {x | c m < j1WindowJump x t} ≠ 0 := by
    by_contra! hall
    apply ht
    change ∀ᵐ x ∂μ, ContinuousAt x.path.1 t
    have hunion : μ (⋃ m : ℕ, {x | c m < j1WindowJump x t}) = 0 :=
      measure_iUnion_null hall
    have hnull : μ {x | 0 < j1WindowJump x t} = 0 := by
      apply measure_mono_null _ hunion
      intro x hx
      change 0 < j1WindowJump x t at hx
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hx
      exact mem_iUnion.mpr ⟨m, hm⟩
    have hae : ∀ᵐ x ∂μ, ¬0 < j1WindowJump x t := by
      rw [ae_iff]
      simpa only [not_not] using hnull
    filter_upwards [hae] with x hx
    apply (cadlag_continuousAt_iff_j1WindowJump_eq_zero x t).mpr
    have hnonneg : 0 ≤ j1WindowJump x t := by
      unfold j1WindowJump
      split <;> positivity
    exact le_antisymm (not_lt.mp hx) hnonneg
  obtain ⟨m, hm⟩ := hex
  have hreal : 0 < (μ {x | c m < j1WindowJump x t}).toReal :=
    ENNReal.toReal_pos hm (measure_ne_top μ _)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hreal
  refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨j, ?_⟩⟩
  exact (ENNReal.ofReal_le_ofReal hj.le).trans ENNReal.ofReal_toReal_le

end DirectedDistances.Probability
