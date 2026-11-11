module

public import DirectedDistances.PaperProofs.Section4.SelectedCutBlockSums
public import DirectedDistances.PaperProofs.Section4.SelectedCutFiltrationCore
public import DirectedDistances.PaperProofs.Section4.RenewalIIDBlockProducts
public import DirectedDistances.Probability.IIDHewittSavage

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open MeasureTheory
open scoped Classical ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0
local notation "Block" => (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)
local notation "endpoint" => (fun b : Block => Sigma.snd b (Fin.last (Sigma.fst b)))
local notation "cumR" =>
  (fun (z : ℕ → Block) (m : ℕ) => ∑ i ∈ Finset.range m, Prod.snd (endpoint (z i)))

private instance blockMeasurableSingleton : MeasurableSingletonClass Block := ⟨fun z => by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet (Sigma.mk n ⁻¹' {z})
  exact (Set.to_countable _).measurableSet⟩




@[expose] noncomputable def blockRank (k : ℕ) (z : ℕ → Block) : ℕ :=
  Nat.findGreatest (fun m => -((k + 1 : ℕ) : ℤ) ≤ cumR z m) (k + 1)

private theorem cumR_le_neg (z : ℕ → Block)
    (hz : ∀ i, (endpoint (z i)).2 ≤ -1) (m : ℕ) : cumR z m ≤ -(m : ℤ) := by
  induction m with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, neg_zero, le_refl]
  | succ m ih =>
      change (∑ i ∈ Finset.range (m + 1), (endpoint (z i)).2) ≤ -((m + 1 : ℕ) : ℤ)
      change (∑ i ∈ Finset.range m, (endpoint (z i)).2) ≤ -(m : ℤ) at ih
      rw [Finset.sum_range_succ]
      have hi := hz m
      dsimp only at ih hi ⊢
      push_cast
      omega





theorem blockRank_spec (k : ℕ) (z : ℕ → Block)
    (hz : ∀ i, (endpoint (z i)).2 ≤ -1) :
    -((k + 1 : ℕ) : ℤ) ≤ cumR z (blockRank k z) ∧
      ∀ m, -((k + 1 : ℕ) : ℤ) ≤ cumR z m → m ≤ blockRank k z := by
  constructor
  · exact Nat.findGreatest_spec
      (P := fun m => -((k + 1 : ℕ) : ℤ) ≤ cumR z m) (m := 0) (Nat.zero_le _) (by
      change -((k + 1 : ℕ) : ℤ) ≤ 0
      omega)
  · intro m hm
    have hb := cumR_le_neg z hz m
    exact Nat.le_findGreatest (by omega) hm

private theorem measurable_endpoint_prefix (m : ℕ) :
    Measurable (fun z : ℕ → Block => ∑ i ∈ Finset.range m, endpoint (z i)) := by
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_of_countable endpoint).comp (measurable_pi_apply i)

private theorem measurable_cumR (m : ℕ) : Measurable (fun z : ℕ → Block => cumR z m) := by
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_of_countable (fun b : Block => (endpoint b).2)).comp
      (measurable_pi_apply i)




theorem measurable_blockRank (k : ℕ) : Measurable (blockRank k) := by
  apply measurable_findGreatest
  intro m _
  exact measurableSet_le measurable_const (measurable_cumR m)

private theorem measurable_block_eval :
    Measurable (fun q : (ℕ → Block) × ℕ => q.1 q.2) :=
  measurable_from_prod_countable_left fun n => measurable_pi_apply n

private theorem measurable_concatenateRenewalBlocks (n : ℕ) :
    Measurable (fun z : ℕ → Block => concatenateRenewalBlocks z n) := by
  let len : (ℕ → Block) → ℕ → ℕ := fun z m => ∑ i ∈ Finset.range m, (z i).1
  have hlen (m : ℕ) : Measurable (fun z => len z m) :=
    Finset.measurable_sum _ fun i _ =>
      (measurable_of_countable Sigma.fst).comp (measurable_pi_apply i)
  let j : (ℕ → Block) → ℕ := fun z => Nat.findGreatest (fun m => len z m ≤ n) n
  have hj : Measurable j := measurable_findGreatest fun m _ =>
    measurableSet_le (hlen m) measurable_const
  have he : Measurable (fun q : (ℕ → Block) × ℕ =>
      ∑ i ∈ Finset.range q.2, endpoint (q.1 i)) :=
    measurable_from_prod_countable_left measurable_endpoint_prefix
  have hl : Measurable (fun q : (ℕ → Block) × ℕ => len q.1 q.2) :=
    measurable_from_prod_countable_left hlen
  have hclip : Measurable (fun q : Block × ℕ =>
      q.1.2 ⟨min q.2 q.1.1, by omega⟩) := measurable_of_countable _
  exact (he.comp (measurable_id.prodMk hj)).add
    (hclip.comp ((measurable_block_eval.comp (measurable_id.prodMk hj)).prodMk
      (measurable_const.sub (hl.comp (measurable_id.prodMk hj)))))




@[expose] noncomputable def blockConditioning (x : XDP) (k : ℕ)
    (z : ℕ → Block) : Ω × ℕ :=
  (fun n => (∑ i ∈ Finset.range (blockRank k z), endpoint (z i)) +
    concatenateRenewalBlocks (fun j => z (blockRank k z + j)) n,
    ∑ i ∈ Finset.range (blockRank k z), blockDist x (z i))

private theorem measurable_block_distance_prefix (x : XDP) :
    Measurable (fun q : (ℕ → Block) × ℕ =>
      ∑ i ∈ Finset.range q.2, blockDist x (q.1 i)) := by
  apply measurable_from_prod_countable_left
  intro m
  change Measurable (fun z : ℕ → Block => ∑ i ∈ Finset.range m, blockDist x (z i))
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_blockDist x).comp (measurable_pi_apply i)

private theorem measurable_block_tail (k : ℕ) :
    Measurable (fun z : ℕ → Block => fun j => z (blockRank k z + j)) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_block_eval.comp
    (measurable_id.prodMk ((measurable_blockRank k).add_const j))

private theorem measurable_block_future (k : ℕ) :
    Measurable (fun z : ℕ → Block => fun n =>
      (∑ i ∈ Finset.range (blockRank k z), endpoint (z i)) +
        concatenateRenewalBlocks (fun j => z (blockRank k z + j)) n) := by
  have he : Measurable (fun q : (ℕ → Block) × ℕ =>
      ∑ i ∈ Finset.range q.2, endpoint (q.1 i)) :=
    measurable_from_prod_countable_left measurable_endpoint_prefix
  apply measurable_pi_iff.mpr
  intro n
  exact (he.comp (measurable_id.prodMk (measurable_blockRank k))).add
    ((measurable_concatenateRenewalBlocks n).comp (measurable_block_tail k))




theorem measurable_blockConditioning (x : XDP) (k : ℕ) :
    Measurable (blockConditioning x k) := by
  unfold blockConditioning
  apply Measurable.prodMk
  · exact measurable_block_future k
  · exact Measurable.comp
      (g := fun q : (ℕ → Block) × ℕ => ∑ i ∈ Finset.range q.2, blockDist x (q.1 i))
      (f := fun z : ℕ → Block => (z, blockRank k z))
      (measurable_block_distance_prefix x)
      (measurable_id.prodMk (measurable_blockRank k))




theorem selectedCutConditioning_eq_blockConditioning_ae
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂μ, ∀ k,
      selectedCutCodeDistanceConditioning x T (k + 1) p =
        blockConditioning x k
          (fun i => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)) := by
  filter_upwards [selectedCutBlock_time_endpoint_rank_ae T hT,
    selectedCutBlock_distance_sum_ae x T hT, selectedCutFuture_block_tail_ae T hT,
    selectorRenewalBlock_prefix_sums_ae T hT] with p htime hdist htail hprefix
  intro k
  let Z := fun i => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)
  have hs := blockRank_spec k Z hprefix.2.2
  have hc := htime k
  have hr : blockRank k Z = selectedCutRank T (k + 1) p :=
    le_antisymm (hc.2.2.2.2 _ hs.1) (hs.2 _ hc.2.2.2.1)
  change selectedCutCodeDistanceConditioning x T (k + 1) p = blockConditioning x k Z
  apply Prod.ext
  · change selectedCutFuture T (k + 1) p = fun n =>
      (∑ i ∈ Finset.range (blockRank k Z), endpoint (Z i)) +
        concatenateRenewalBlocks (fun j => Z (blockRank k Z + j)) n
    rw [hr]
    exact htail k
  · change (selectedCutCodeDistanceConditioning x T (k + 1) p).2 =
      ∑ i ∈ Finset.range (blockRank k Z), blockDist x (Z i)
    rw [hr]
    exact hdist k

private theorem sum_range_perm {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (m n : ℕ) (hmn : m ≤ n) (σ : Equiv.Perm ℕ)
    (hσ : ∀ i, σ i ≠ i → i < m) :
    ∑ i ∈ Finset.range n, f (σ i) = ∑ i ∈ Finset.range n, f i := by
  have hfix (i : ℕ) (hi : m ≤ i) : σ i = i := by
    by_contra h
    have := hσ i h
    omega
  have hmap (i : ℕ) (hi : i < n) : σ i < n := by
    by_contra h
    have he := hfix (σ i) (by omega)
    have he' : σ i = i := σ.injective he
    omega
  refine Finset.sum_bij (fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_range.mpr (hmap i (Finset.mem_range.mp hi))
  · intro i _ j _ hij
    exact σ.injective hij
  · intro i hi
    refine ⟨σ.symm i, ?_, σ.apply_symm_apply i⟩
    apply Finset.mem_range.mpr
    by_contra h
    have he := hfix (σ.symm i) (by omega)
    have he' : i = σ.symm i := (σ.apply_symm_apply i).symm.trans he
    have hi' := Finset.mem_range.mp hi
    omega
  · intro i _
    rfl




theorem blockConditioning_perm_invariant (x : XDP) (k : ℕ) (z : ℕ → Block)
    (hz : ∀ i, (endpoint (z i)).2 ≤ -1) (σ : Equiv.Perm ℕ)
    (hσ : ∀ i, σ i ≠ i → i < blockRank k z) :
    blockRank k (fun i => z (σ i)) = blockRank k z ∧
      blockConditioning x k (fun i => z (σ i)) = blockConditioning x k z := by
  let m := blockRank k z
  let z' := fun i => z (σ i)
  have hs := blockRank_spec k z hz
  have hs' := blockRank_spec k z' (fun i => hz (σ i))
  have hsum (n : ℕ) (hn : m ≤ n) : cumR z' n = cumR z n :=
    sum_range_perm (fun i => (endpoint (z i)).2) m n hn σ hσ
  have hmr : m ≤ blockRank k z' := hs'.2 m (by rw [hsum m le_rfl]; exact hs.1)
  have hr : blockRank k z' = m := le_antisymm
    (hs.2 _ (by rw [← hsum _ hmr]; exact hs'.1)) hmr
  refine ⟨hr, ?_⟩
  have ht : (fun j => z' (m + j)) = (fun j => z (m + j)) := by
    funext j
    change z (σ (m + j)) = z (m + j)
    have he : σ (m + j) = m + j := by
      by_contra h
      have := hσ (m + j) h
      change m + j < m at this
      omega
    rw [he]
  change blockConditioning x k z' = _
  simp only [blockConditioning, hr]
  rw [show (∑ i ∈ Finset.range m, endpoint (z' i)) =
    ∑ i ∈ Finset.range m, endpoint (z i) from
      sum_range_perm (fun i => endpoint (z i)) m m le_rfl σ hσ,
    show (∑ i ∈ Finset.range m, blockDist x (z' i)) =
    ∑ i ∈ Finset.range m, blockDist x (z i) from
      sum_range_perm (fun i => blockDist x (z i)) m m le_rfl σ hσ, ht]

private theorem blockRank_tendsto (z : ℕ → Block)
    (hz : ∀ i, (endpoint (z i)).2 ≤ -1) :
    Filter.Tendsto (fun k => blockRank k z) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨(-cumR z b).toNat, fun k hk => (blockRank_spec k z hz).2 b ?_⟩
  omega

private def blockHSRepresentative (x : XDP) (U : ℕ → Set (Ω × ℕ)) :
    Set (ℕ → Block) :=
  {z | (∀ i, (endpoint (z i)).2 ≤ -1) ∧
    Filter.Tendsto (fun k => blockRank k z) Filter.atTop Filter.atTop ∧
    ∃ K, ∀ k ≥ K, blockConditioning x k z ∈ U k}

private theorem measurableSet_blockHSRepresentative (x : XDP) (U : ℕ → Set (Ω × ℕ))
    (hU : ∀ k, MeasurableSet (U k)) : MeasurableSet (blockHSRepresentative x U) := by
  have hneg : MeasurableSet {z : ℕ → Block | ∀ i, (endpoint (z i)).2 ≤ -1} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      ((measurable_of_countable (fun b : Block => (endpoint b).2)).comp
        (measurable_pi_apply i)) measurable_const
  have hevent : MeasurableSet
      {z : ℕ → Block | ∃ K, ∀ k ≥ K, blockConditioning x k z ∈ U k} := by
    simp only [Set.ofPred_exists, Set.ofPred_forall]
    exact MeasurableSet.iUnion fun K => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => (hU k).preimage (measurable_blockConditioning x k)
  have heq : blockHSRepresentative x U =
      {z : ℕ → Block | ∀ i, (endpoint (z i)).2 ≤ -1} ∩
        {z : ℕ → Block | ∃ K, ∀ k ≥ K, blockConditioning x k z ∈ U k} := by
    ext z
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, blockRank_tendsto z h.1, h.2⟩
  rw [heq]
  exact hneg.inter hevent

private theorem blockHSRepresentative_perm_forward (x : XDP) (U : ℕ → Set (Ω × ℕ))
    (σ : Equiv.Perm ℕ) (hσ : {i | σ i ≠ i}.Finite) (z : ℕ → Block)
    (hz : z ∈ blockHSRepresentative x U) :
    (fun i => z (σ i)) ∈ blockHSRepresentative x U := by
  obtain ⟨N, hN⟩ := hσ.bddAbove
  obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp hz.2.1 (N + 1)
  obtain ⟨J, hJ⟩ := hz.2.2
  have hneg : ∀ i, (endpoint (z (σ i))).2 ≤ -1 := fun i => hz.1 (σ i)
  refine ⟨hneg, blockRank_tendsto _ hneg, max K J, ?_⟩
  intro k hk
  have hkK : K ≤ k := (le_max_left K J).trans hk
  have hkJ : J ≤ k := (le_max_right K J).trans hk
  have hbound : ∀ i, σ i ≠ i → i < blockRank k z := by
    intro i hi
    have hiN : i ≤ N := hN hi
    have hm := hK k hkK
    omega
  rw [(blockConditioning_perm_invariant x k z hz.1 σ hbound).2]
  exact hJ k hkJ

private theorem blockHSRepresentative_perm (x : XDP) (U : ℕ → Set (Ω × ℕ))
    (σ : Equiv.Perm ℕ) (hσ : {i | σ i ≠ i}.Finite) :
    (fun z i => z (σ i)) ⁻¹' blockHSRepresentative x U = blockHSRepresentative x U := by
  have hinv : {i | σ.symm i ≠ i}.Finite := hσ.subset fun i hi => by
    intro he
    apply hi
    have hh := congrArg σ.symm he
    simpa only [σ.symm_apply_apply] using hh.symm
  ext z
  constructor
  · intro h
    have hh := blockHSRepresentative_perm_forward x U σ.symm hinv (fun i => z (σ i)) h
    simpa only [σ.apply_symm_apply] using hh
  · exact blockHSRepresentative_perm_forward x U σ hσ z





theorem selectedCutConditioningSigma_iInf_trivial
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (A : Set (selectedCutCoherentDomain x T hT))
    (hA : MeasurableSet[⨅ j, selectedCutConditioningSigma x T hT j] A) :
    ((μ).comap (Subtype.val : selectedCutCoherentDomain x T hT → Ω)) A = 0 ∨
      ((μ).comap (Subtype.val : selectedCutCoherentDomain x T hT → Ω)) A = 1 := by
  have hAk (k : ℕ) : ∃ U : Set (Ω × ℕ), MeasurableSet U ∧
      (fun q : selectedCutCoherentDomain x T hT =>
        selectedCutConditioningVersion x T hT k q.1) ⁻¹' U = A :=
    MeasurableSpace.measurableSet_comap.mp (MeasurableSpace.measurableSet_iInf.mp hA k)
  choose U hU hAU using hAk
  let Z : Ω → ℕ → Block := fun p i =>
    selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p)
  let V := blockHSRepresentative x U
  have hQ := selectedCutCoherentDomain_measurable_conull x T hT
  have hQa : ∀ᵐ p ∂μ, p ∈ selectedCutCoherentDomain x T hT := ae_iff.mpr hQ.2
  have hae : (Subtype.val : selectedCutCoherentDomain x T hT → Ω) '' A =ᵐ[μ]
      Z ⁻¹' V := by
    filter_upwards [hQa, selectedCutConditioning_eq_blockConditioning_ae x T hT,
      selectorRenewalBlock_prefix_sums_ae T hT] with p hp hrep hprefix
    let q : selectedCutCoherentDomain x T hT := ⟨p, hp⟩
    have him : p ∈ (Subtype.val : selectedCutCoherentDomain x T hT → Ω) '' A ↔ q ∈ A := by
      constructor
      · rintro ⟨r, hr, he⟩
        have heq : r = q := Subtype.ext he
        exact heq ▸ hr
      · exact fun ha => ⟨q, ha, rfl⟩
    have hmem (k : ℕ) : q ∈ A ↔ blockConditioning x k (Z p) ∈ U k := by
      rw [← hAU k]
      change selectedCutConditioningVersion x T hT k p ∈ U k ↔ _
      rw [(selectedCutCoherentDomain_spec x T hT q).1 k, hrep k]
    apply propext
    change (p ∈ (Subtype.val : selectedCutCoherentDomain x T hT → Ω) '' A ↔ Z p ∈ V)
    rw [him]
    constructor
    · intro ha
      exact ⟨hprefix.2.2, blockRank_tendsto (Z p) hprefix.2.2,
        0, fun k _ => (hmem k).mp ha⟩
    · rintro ⟨_, _, K, hK⟩
      exact (hmem K).mpr (hK K le_rfl)
  have hmeasure : ((μ).comap (Subtype.val : selectedCutCoherentDomain x T hT → Ω)) A =
      μ (Z ⁻¹' V) :=
    (comap_subtype_coe_apply hQ.1 μ A).trans (measure_congr hae)
  rw [hmeasure]
  have : IsProbabilityMeasure μ :=
    (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).1
  have hR := (selectorRenewal_oneStep_product T hT).1
  have hB := selectorRenewalBlock_measurable T hT
  have hiid := selectorRenewal_iterates_iid T hT
  exact DirectedDistances.Probability.iid_sequence_hs_zero_one μ
    ((μ).map (selectorRenewalBlock T))
    (fun i p => selectorRenewalBlock T ((selectorRenewalFuture T)^[i] p))
    (fun i => hB.comp (hR.iterate i).measurable) hiid.2 hiid.1
    (measurableSet_blockHSRepresentative x U hU) (blockHSRepresentative_perm x U)

end DirectedDistances.PaperProofs.Section4
