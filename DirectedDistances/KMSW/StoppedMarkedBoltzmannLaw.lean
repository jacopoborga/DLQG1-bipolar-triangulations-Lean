module

public import DirectedDistances.RandomWalk.PostHitMinimumLaw
public import DirectedDistances.PaperProofs.Section4.PastMapFirstHitKernelAS
public import DirectedDistances.KMSW.BoltzmannMarkedRightLawProcedure

/-! Supporting lemmas for paper labels `lem-uiqbot-boltzmann` (see CORRESPONDENCE.md). -/
















public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- A fixed fallback class for the null undefined-map branch of the Lemma 7.9 -/
@[expose] noncomputable def stoppedMarkedDefault (r : ℕ) (hr : 1 ≤ r) :
    AllBoltzmannSpace r := by
  letI := rightVertexMarkedBoltzmannLaw_isProbabilityMeasure_procedureReading r hr
  exact (Classical.choice
    (nonempty_of_isProbabilityMeasure (rightVertexMarkedBoltzmannLaw r))).1

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
total left-boundary-vertex index, clamped to the last allowed index. The
geometric mark identification is StoppedLeftBoundaryMarkAE. Definition 1.10
edge-count clause and the source-map binding are not treated; not the paper result. -/
@[expose] noncomputable def stoppedMarked (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) : RightVertexMarkedBoltzmannSpace r :=
  let q := (stoppedMap r hr (pathCode p)).getD (stoppedMarkedDefault r hr)
  ⟨q, ⟨min (postHitMinimum r p).toNat q.1,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

/-- Measurability of the marked stopped-map helper toward Lemma 7.9 -/
theorem measurable_stoppedMarked (r : ℕ) (hr : 1 ≤ r) :
    Measurable (stoppedMarked r hr) := by
  let g : Option (AllBoltzmannSpace r) × ℕ → RightVertexMarkedBoltzmannSpace r :=
    fun z => let q := z.1.getD (stoppedMarkedDefault r hr)
      ⟨q, ⟨min z.2 q.1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩
  exact (measurable_of_countable g).comp
    (((measurable_stoppedMap r hr).comp measurable_pathCode).prodMk
      ((measurable_of_countable Int.toNat).comp (measurable_postHitMinimum r)))

private theorem endpoint_measurable (r ell : ℕ) :
    MeasurableSet ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) := by
  have ht : Measurable (conditionedSecondCoordinateFirstHit r) := by
    apply ENat.measurable_iff.mpr
    intro k
    obtain ⟨S, hS, he⟩ := MeasurableSpace.measurableSet_comap.mp
      (measurableSet_conditionedVectorPast_firstHit_eq r k)
    change MeasurableSet {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}
    rw [← he]
    exact hS.preimage (measurable_conditionedVectorPrefix k)
  have hF : MeasurableSet {t : ℕ∞ | t < ⊤} := (Set.to_countable _).measurableSet
  refine (hF.preimage ht).inter ?_
  have he := ((measurable_fst.comp (measurable_pi_apply 0)).comp
    (measurable_conditionedFirstHit_future r)) (measurableSet_singleton (ell : ℤ))
  simpa only [Function.comp_def, conditionedVectorShift, Nat.add_zero,
    Set.preimage, Set.mem_singleton_iff] using he

private instance history_singletons :
    MeasurableSingletonClass (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) where
  measurableSet_singleton h := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro n
    change MeasurableSet (Sigma.mk n ⁻¹' {h})
    exact (Set.to_countable _).measurableSet

private theorem stopped_class_support (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃ q : AllBoltzmannSpace r, stoppedMap r hr (pathCode p) = some q ∧
        q.1 = (p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat := by
  let μ := conditionedVectorPathLaw 0 0
  let Y := fun p => conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
  let X := fun p => stoppedMap r hr (pathCode p)
  let P : (ℕ → ℤ × ℤ) × Option (AllBoltzmannSpace r) → Prop :=
    fun z => ∃ q : AllBoltzmannSpace r, z.2 = some q ∧ q.1 = (z.1 0).1.toNat
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hX : Measurable X := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hP : MeasurableSet {z | P z} := by
    let S : Set (ℤ × Option (AllBoltzmannSpace r)) :=
      {z | ∃ q : AllBoltzmannSpace r, z.2 = some q ∧ q.1 = z.1.toNat}
    have he : Measurable (fun z : (ℕ → ℤ × ℤ) × Option (AllBoltzmannSpace r) =>
        (z.1 0).1) :=
      measurable_fst.comp ((measurable_pi_apply 0).comp measurable_fst)
    exact (Set.to_countable S).measurableSet.preimage (he.prodMk measurable_snd)
  have hpos : ∀ᵐ p ∂μ, 1 ≤ (p (conditionedSecondCoordinateFirstHit r p).toNat).1 := by
    have h := firstHitPastMap_left_pos_ae r hr
    dsimp only at h
    rwa [firstHitPastMap_cond_finite_hit_eq r hr] at h
  have hposY : ∀ᵐ y ∂μ.map Y, 1 ≤ (y 0).1 := by
    apply (ae_map_iff hY.aemeasurable
      (measurableSet_le measurable_const
        (measurable_fst.comp (measurable_pi_apply 0)))).mpr
    exact hpos
  have ha : ∀ᵐ z ∂μ.map (fun p => (Y p, X p)), P z := by
    rw [firstHitPastMap_joint_kernel_law_unconditioned r hr]
    apply (Measure.ae_compProd_iff hP).mpr
    filter_upwards [hposY] with y hy
    change ∀ᵐ o ∂(if h : 1 ≤ (y 0).1 then
      firstHitBoltzmannMapLaw r (y 0).1.toNat hr (by omega)
      else Measure.dirac none), P (y, o)
    rw [dite_eq_left hy]
    unfold firstHitBoltzmannMapLaw
    apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
    apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
    exact Eventually.of_forall fun m => ⟨⟨(y 0).1.toNat, m⟩, rfl, rfl⟩
  exact (ae_map_iff (hY.prodMk hX).aemeasurable hP).mp ha

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
minimum index almost surely, so the clamp is inactive. The geometric mark
identification is StoppedLeftBoundaryMarkAE; Definition 1.10
edge-count clause and the source-map binding are not treated; not the paper result. -/
theorem stoppedMarked_clamp_inactive_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (stoppedMarked r hr p).2.val = (postHitMinimum r p).toNat ∧
        stoppedMap r hr (pathCode p) = some (stoppedMarked r hr p).1 := by
  filter_upwards [stopped_class_support r hr, postHitMinimum_attained_ae r] with p hq hm
  obtain ⟨q, hq, hlen⟩ := hq
  have hb := hm.2.1 (conditionedSecondCoordinateFirstHit r p).toNat le_rfl
  have hbn : (postHitMinimum r p).toNat ≤ q.1 := by
    rw [hlen]
    omega
  simp only [stoppedMarked, hq, Option.getD_some]
  exact ⟨Nat.min_eq_left hbn, trivial⟩

private theorem endpoint_minimum_law (r ell : ℕ)
    (hpos : 0 < conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)})) :
    ((conditionedVectorPathLaw 0 0)[|
      {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}]).map
      (fun p => (postHitMinimum r p).toNat) =
        Measure.uniformOfFinset (Finset.range (ell + 1)) := by
  let μ := conditionedVectorPathLaw 0 0
  let F := {p | conditionedSecondCoordinateFirstHit r p < ⊤}
  let E := F ∩
    {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}
  let H : Set (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) :=
    {h | (h.2 (Fin.last h.1)).1 = (ell : ℤ)}
  have hH : MeasurableSet H := (Set.to_countable _).measurableSet
  have ht : Measurable (fun p => (conditionedSecondCoordinateFirstHit r p).toNat) := by
    apply (measurable_of_countable ENat.toNat).comp
    apply ENat.measurable_iff.mpr
    intro k
    obtain ⟨S, hS, he⟩ := MeasurableSpace.measurableSet_comap.mp
      (measurableSet_conditionedVectorPast_firstHit_eq r k)
    change MeasurableSet {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}
    rw [← he]
    exact hS.preimage (measurable_conditionedVectorPrefix k)
  have hh : Measurable (postHitMinimumPast r) :=
    measurable_stoppedVectorHistory _ _ ht measurable_id
  have hm : Measurable (fun p => (postHitMinimum r p).toNat) :=
    (measurable_of_countable Int.toNat).comp (measurable_postHitMinimum r)
  apply Measure.ext_of_singleton
  intro j
  have hk := congrArg (fun ν => ν (H ×ˢ {j})) (postHitMinimum_kernel r)
  rw [Measure.map_apply (hh.prodMk hm) (hH.prod (measurableSet_singleton j)),
    Measure.restrict_apply ((hH.prod (measurableSet_singleton j)).preimage
      (hh.prodMk hm)), Measure.compProd_apply_prod hH (measurableSet_singleton j),
    setLIntegral_map hH
      (Kernel.measurable_coe postHitMinimumKernel (measurableSet_singleton j)) hh] at hk
  have he : (fun p => (postHitMinimumPast r p, (postHitMinimum r p).toNat)) ⁻¹'
      (H ×ˢ {j}) ∩ F = E ∩ {p | (postHitMinimum r p).toNat = j} := by
    ext p
    simp only [H, E, F, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
    tauto
  rw [he, Measure.restrict_restrict (hH.preimage hh)] at hk
  have hp : postHitMinimumPast r ⁻¹' H ∩ F = E := by
    ext p
    change ((_ = (ell : ℤ)) ∧ _) ↔ (_ ∧ _ = (ell : ℤ))
    tauto
  rw [hp] at hk
  have hv : ∫⁻ p in E, postHitMinimumKernel (postHitMinimumPast r p) {j} ∂μ =
      (if j < ell + 1 then ((ell + 1 : ℕ) : ℝ≥0∞)⁻¹ else 0) * μ E := by
    rw [← setLIntegral_const]
    apply setLIntegral_congr_fun (endpoint_measurable r ell)
    intro p hp
    change Measure.uniformOfFinset
      (Finset.range ((p (conditionedSecondCoordinateFirstHit r p).toNat).1.toNat + 1))
        {j} = _
    rw [hp.2, Int.toNat_natCast, Measure.uniformOfFinset_apply_singleton]
    simp only [Finset.mem_range, Finset.card_range]
  rw [hv] at hk
  rw [Measure.map_apply hm (measurableSet_singleton j),
    cond_apply (endpoint_measurable r ell)]
  change (μ E)⁻¹ * μ (E ∩ {p | (postHitMinimum r p).toNat = j}) = _
  rw [hk, Measure.uniformOfFinset_apply_singleton]
  simp only [Finset.mem_range, Finset.card_range]
  rw [mul_left_comm,
    ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top μ E), mul_one]

private theorem endpoint_joint_nat (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (hpos : 0 < conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)})) :
    ((conditionedVectorPathLaw 0 0)[|
      {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}]).map
      (fun p => (stoppedMap r hr (pathCode p), (postHitMinimum r p).toNat)) =
        (firstHitBoltzmannMapLaw r ell hr hell).prod
          (Measure.uniformOfFinset (Finset.range (ell + 1))) := by
  let μ := conditionedVectorPathLaw 0 0
  let E := {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
    {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}
  let ν := μ[|E]
  let Y := fun p => conditionedVectorShift (conditionedSecondCoordinateFirstHit r p).toNat p
  let X := fun p => stoppedMap r hr (pathCode p)
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure hpos.ne'
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hX : Measurable X := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hc := firstHitPastMap_condDistrib r ell hr hell hpos
  have hj := (condDistrib_ae_eq_iff_measure_eq_compProd hY.aemeasurable hX.aemeasurable
    (Kernel.const _ (firstHitBoltzmannMapLaw r ell hr hell))).mp hc
  rw [Measure.compProd_const] at hj
  have hmap : ν.map X = firstHitBoltzmannMapLaw r ell hr hell :=
    firstHitPastMap_law r ell hr hell hpos
  rw [← hmap] at hj
  have hi := (indepFun_iff_map_prod_eq_prod_map_map
    hY.aemeasurable hX.aemeasurable).mpr hj
  let f : (ℕ → ℤ × ℤ) → ℕ := fun q => (⨅ n : ℕ, (q n).1).toNat
  have hf : Measurable f := (measurable_of_countable Int.toNat).comp
    (Measurable.iInf fun n => (measurable_pi_apply n).fst)
  have hn := (hi.symm.comp measurable_id hf).map_prod_eq_prod_map_map
    hX.aemeasurable (hf.comp hY).aemeasurable
  change ν.map (fun p => (X p, (postHitMinimum r p).toNat)) =
    (ν.map X).prod (ν.map (fun p => (postHitMinimum r p).toNat)) at hn
  rw [hmap, endpoint_minimum_law r ell hpos] at hn
  exact hn

private theorem uniform_fin_val (ell : ℕ) :
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell + 1)))).map Fin.val =
      Measure.uniformOfFinset (Finset.range (ell + 1)) := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton j)]
  by_cases hj : j < ell + 1
  · have he : (Fin.val : Fin (ell + 1) → ℕ) ⁻¹' {j} = {⟨j, hj⟩} := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
    rw [he, Measure.uniformOfFinset_apply_singleton,
      Measure.uniformOfFinset_apply_singleton]
    simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ, Fintype.card_fin,
      Finset.mem_range, hj, Finset.card_range]
  · have he : (Fin.val : Fin (ell + 1) → ℕ) ⁻¹' {j} = ∅ := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro hk
      exact hj (hk ▸ k.isLt)
    rw [he, measure_empty, Measure.uniformOfFinset_apply_singleton]
    simp only [Finset.mem_range, hj, ↓reduceIte]

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
slice, the joint law is Boltzmann(ell,r) times the uniform left-boundary vertex
mark, embedded in the existing marked carrier (Definition 1.10,
StoppedLeftBoundaryMarkAE; the edge-count clause and the source-map binding are
not treated; not the paper result. -/
theorem stoppedMarked_endpoint_law (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    0 < μ E → (μ[|E]).map (stoppedMarked r hr) =
      ((boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).prod
          (Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell + 1))))).map
            (β := RightVertexMarkedBoltzmannSpace r)
            (fun z => (⟨⟨ell, z.1⟩, z.2⟩ : RightVertexMarkedBoltzmannSpace r)) := by
  dsimp only
  intro hpos
  let ν := (conditionedVectorPathLaw 0 0)[|
    {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}]
  let B := boltzmannLaw ell r
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2
  let U := Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell + 1)))
  let g : Option (AllBoltzmannSpace r) × ℕ → RightVertexMarkedBoltzmannSpace r :=
    fun z => let q := z.1.getD (stoppedMarkedDefault r hr)
      ⟨q, ⟨min z.2 q.1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩
  let i : BoltzmannSpace ell r → Option (AllBoltzmannSpace r) :=
    fun m => some ⟨ell, m⟩
  have hi : Measurable i := measurable_of_countable _
  have hB : firstHitBoltzmannMapLaw r ell hr hell = B.map i := by
    change (B.map (β := AllBoltzmannSpace r) (fun m => ⟨ell, m⟩)).map some = B.map i
    let f : BoltzmannSpace ell r → AllBoltzmannSpace r := fun m => ⟨ell, m⟩
    exact Measure.map_map (μ := B) (f := f) (g := some)
      (measurable_of_countable _) (measurable_of_countable _)
  have hm : Measurable (fun p =>
      (stoppedMap r hr (pathCode p), (postHitMinimum r p).toNat)) :=
    ((measurable_stoppedMap r hr).comp measurable_pathCode).prodMk
      ((measurable_of_countable Int.toNat).comp (measurable_postHitMinimum r))
  change ν.map (stoppedMarked r hr) = _
  change ν.map (g ∘ fun p =>
    (stoppedMap r hr (pathCode p), (postHitMinimum r p).toNat)) = _
  rw [← Measure.map_map (measurable_of_countable g) hm,
    endpoint_joint_nat r ell hr hell hpos, hB, ← uniform_fin_val ell,
    Measure.map_prod_map B U hi (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext z
  change (⟨⟨ell, z.1⟩, ⟨min z.2.val ell, _⟩⟩ :
    RightVertexMarkedBoltzmannSpace r) = ⟨⟨ell, z.1⟩, z.2⟩
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ z.2.isLt)


end DirectedDistances.KMSW
