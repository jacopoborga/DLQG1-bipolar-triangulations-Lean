module

public import DirectedDistances.PaperProofs.Section4.FirstHitCondIndepSigma
public import DirectedDistances.KMSW.KMSWMeasurability

/-! of the first-hit code-graph XDP distance and literal σ-algebra conditional independence
at τ_r; the renewal-time selection T_{m_k}, the T_0 branch and the one-sided source
carrier binding are not treated; not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory Quiver

private theorem path_in_late_stages {w : ℕ → Fin 3} {a b : PresentVertex w}
    (p : Path a b) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ q : Path (⟨a.id⟩ : StagePresentVertex w n) ⟨b.id⟩,
        q.length = p.length := by
  induction p with
  | nil => exact ⟨0, fun _ _ => ⟨Path.nil, rfl⟩⟩
  | @cons b c p e ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := e.property.1.eventually_present
    refine ⟨max N M, fun n hn => ?_⟩
    obtain ⟨q, hq⟩ := hN n ((Nat.le_max_left _ _).trans hn)
    obtain ⟨he, hp⟩ := hM n ((Nat.le_max_right _ _).trans hn)
    let en : (⟨b.id⟩ : StagePresentVertex w n) ⟶ ⟨c.id⟩ :=
      ⟨e.val, he, hp,
        (edge_endpoints_eq w he).1.trans e.property.2.1,
        (edge_endpoints_eq w he).2.trans e.property.2.2⟩
    exact ⟨q.cons en, by simp only [Path.length_cons, hq]⟩

private theorem mem_present_pathLengths_iff (w : ℕ → Fin 3) (a b k : ℕ) :
    k ∈ pathLengths (⟨a⟩ : PresentVertex w) ⟨b⟩ ↔
      ∃ n, k ∈ pathLengths (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨N, hN⟩ := path_in_late_stages p
    obtain ⟨q, hq⟩ := hN N le_rfl
    exact ⟨N, q, hq⟩
  · rintro ⟨n, hk⟩
    exact pathLengths_stage_subset w n ⟨a⟩ ⟨b⟩ hk

private theorem measurableSet_present_pathLengths (a b k : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 |
      k ∈ pathLengths (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} := by
  have he : {ω : ℕ → Fin 3 |
      k ∈ pathLengths (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} =
      ⋃ n : ℕ, {ω : ℕ → Fin 3 |
        k ∈ pathLengths (⟨a⟩ : StagePresentVertex (boltzmannKMSWStream ω) n) ⟨b⟩} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_present_pathLengths_iff]
  rw [he]
  exact MeasurableSet.iUnion fun n => measurableSet_stage_pathLengths n a b (fun s => k ∈ s)

private theorem measurable_of_countable_le {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [Countable α] [LinearOrder α] (f : Ω → α)
    (hf : ∀ z, MeasurableSet {ω | f ω ≤ z}) : Measurable f := by
  refine measurable_to_countable' fun z => ?_
  have he : f ⁻¹' {z} = {ω | f ω ≤ z} \
      ⋃ y : α, ⋃ (_ : y < z), {ω | f ω ≤ y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
      Set.mem_ofPred_eq, Set.mem_iUnion, not_exists]
    constructor
    · rintro rfl
      exact ⟨le_rfl, fun y hy hzy => (not_le_of_gt hy) hzy⟩
    · rintro ⟨h, hn⟩
      exact le_antisymm h (le_of_not_gt fun hlt => hn (f ω) hlt le_rfl)
  rw [he]
  exact (hf z).diff (MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun _ => hf y)

private theorem measurable_presentLdp_comp {β : Type*} [MeasurableSpace β]
    (a b : ℕ) (F : WithBot ℕ∞ → β) :
    Measurable (fun ω : ℕ → Fin 3 =>
      F (presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩)) := by
  let : MeasurableSpace (WithBot ℕ∞) := ⊤
  have hm : Measurable (fun ω : ℕ → Fin 3 =>
      presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩) := by
    apply measurable_of_countable_le
    intro z
    have he : {ω : ℕ → Fin 3 |
        presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩ ≤ z} =
        ⋂ k : ℕ, {ω : ℕ → Fin 3 |
          k ∉ pathLengths (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} ∪
          {ω : ℕ → Fin 3 | ((k : ℕ∞) : WithBot ℕ∞) ≤ z} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, presentLdp, iSup_le_iff]
      constructor
      · intro h k
        by_cases hk : k ∈ pathLengths
            (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩
        · obtain ⟨p, rfl⟩ := hk
          exact Or.inr (h p)
        · exact Or.inl hk
      · intro h p
        exact (h p.length).resolve_left (not_not.mpr ⟨p, rfl⟩)
    rw [he]
    refine MeasurableSet.iInter fun k =>
      (measurableSet_present_pathLengths a b k).compl.union ?_
    by_cases h : ((k : ℕ∞) : WithBot ℕ∞) ≤ z <;> simp only [h,
      Set.ofPred_true, Set.ofPred_false, MeasurableSet.univ, MeasurableSet.empty]
  exact (measurable_of_countable F).comp hm

private theorem measurable_presentSdp (a b : ℕ) :
    Measurable (fun ω : ℕ → Fin 3 =>
      sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩) := by
  let : Countable (OrderDual ℕ∞) := inferInstanceAs (Countable ℕ∞)
  apply measurable_of_countable_le (α := OrderDual ℕ∞)
    (fun ω => OrderDual.toDual
      (sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩))
  intro z
  change MeasurableSet {ω : ℕ → Fin 3 |
    OrderDual.ofDual z ≤ sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩}
  have he : {ω : ℕ → Fin 3 |
      OrderDual.ofDual z ≤ sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} =
      ⋂ k : ℕ, {ω : ℕ → Fin 3 |
        k ∉ pathLengths (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} ∪
        {ω : ℕ → Fin 3 | OrderDual.ofDual z ≤ (k : ℕ∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, sdp, le_iInf_iff]
    constructor
    · intro h k
      by_cases hk : k ∈ pathLengths
          (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩
      · obtain ⟨p, rfl⟩ := hk
        exact Or.inr (h p)
      · exact Or.inl hk
    · intro h p
      exact (h p.length).resolve_left (not_not.mpr ⟨p, rfl⟩)
  rw [he]
  refine MeasurableSet.iInter fun k =>
    (measurableSet_present_pathLengths a b k).compl.union ?_
  by_cases h : OrderDual.ofDual z ≤ (k : ℕ∞) <;> simp only [h,
    Set.ofPred_true, Set.ofPred_false, MeasurableSet.univ, MeasurableSet.empty]

private theorem measurable_select {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] (f : ι → Ω → β) (hf : ∀ i, Measurable (f i))
    (g : Ω → ι) (hg : Measurable g) : Measurable (fun ω => f (g ω) ω) := by
  have h : Measurable (fun p : Ω × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

private theorem measurable_firstHit_nat (r : ℕ) :
    Measurable (fun p => (conditionedSecondCoordinateFirstHit r p).toNat) := by
  have ht : Measurable (conditionedSecondCoordinateFirstHit r) := by
    apply ENat.measurable_iff.mpr
    intro k
    obtain ⟨T, hT, hpre⟩ := MeasurableSpace.measurableSet_comap.mp
      (measurableSet_conditionedVectorPast_firstHit_eq r k)
    change MeasurableSet {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}
    rw [← hpre]
    exact hT.preimage (measurable_conditionedVectorPrefix k)
  exact (measurable_of_countable ENat.toNat).comp ht

private theorem measurable_decoded_presentXdp (x : XDP) (a b : ℕ) :
    Measurable (fun ω : ℕ → Fin 3 =>
      match x with
      | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
          (presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩)
      | .sdp => (sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩).toNat) := by
  cases x with
  | ldp => exact measurable_presentLdp_comp a b _
  | sdp => exact (measurable_of_countable ENat.toNat).comp (measurable_presentSdp a b)

/-- of the first-hit code-graph XDP distance and literal σ-algebra conditional independence
at τ_r; the renewal-time selection T_{m_k}, the T_0 branch and the one-sided source
carrier binding are not treated; not the paper result. -/
theorem measurable_firstHitCodeXdpDistance (x : XDP) (r : ℕ) :
    Measurable (firstHitCodeXdpDistance x r) := by
  have hv : Measurable (fun p : ℕ → ℤ × ℤ =>
      (recordVertex (boltzmannKMSWStream (pathCode p))
        (conditionedSecondCoordinateFirstHit r p).toNat).id) := by
    exact measurable_select
      (fun t p => (recordVertex (boltzmannKMSWStream (pathCode p)) t).id)
      (fun t => (measurable_kmswStage_shift_comp t (fun s => s.west s.active)).comp
        measurable_pathCode)
      (fun p => (conditionedSecondCoordinateFirstHit r p).toNat)
      (measurable_firstHit_nat r)
  exact measurable_select
    (fun b p => match x with
      | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
          (presentLdp (⟨0⟩ : PresentVertex (boltzmannKMSWStream (pathCode p))) ⟨b⟩)
      | .sdp => (sdp (⟨0⟩ : PresentVertex (boltzmannKMSWStream (pathCode p))) ⟨b⟩).toNat)
    (fun b => (measurable_decoded_presentXdp x 0 b).comp measurable_pathCode)
    (fun p => (recordVertex (boltzmannKMSWStream (pathCode p))
      (conditionedSecondCoordinateFirstHit r p).toNat).id) hv

/-- of the first-hit code-graph XDP distance and literal σ-algebra conditional independence
at τ_r; the renewal-time selection T_{m_k}, the T_0 branch and the one-sided source
carrier binding are not treated; not the paper result. -/
theorem measurable_firstHitCodeDistanceConditioning (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    Measurable (firstHitCodeDistanceConditioning x r hr) :=
  (measurable_conditionedFirstHit_future r).prodMk (measurable_firstHitCodeXdpDistance x r)

/-- of the first-hit code-graph XDP distance and literal σ-algebra conditional independence
at τ_r; the renewal-time selection T_{m_k}, the T_0 branch and the one-sided source
carrier binding are not treated; not the paper result. -/
theorem firstHitCodeDistance_condIndepFun_comap (x : XDP) (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let M := fun p => stoppedMap r hr (pathCode p)
    let C := firstHitPastAllCuts x r ∘ M
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (firstHitCodeDistanceConditioning x r hr) inferInstance)
      (Measurable.comap_le (measurable_firstHitCodeDistanceConditioning x r hr))
      (fun p => (C p).1) (fun p => (C p).2) μ := by
  classical
  let μ := conditionedVectorPathLaw 0 0
  let M := fun p : ℕ → ℤ × ℤ => stoppedMap r hr (pathCode p)
  let C := firstHitPastAllCuts x r ∘ M
  let B := firstHitCodeDistanceConditioning x r hr
  have hB : Measurable B := measurable_firstHitCodeDistanceConditioning x r hr
  have hM : Measurable M := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hC : Measurable C := (measurable_firstHitPastAllCuts x r).comp hM
  let κ := condDistrib (fun p => (C p).1) B μ ×ₖ
    condDistrib (fun p => (C p).2) B μ
  have hFactor : condDistrib C B μ =ᵐ[μ.map B] κ := by
    have hOld : condDistrib C B μ =ᵐ[μ.map B] fun b =>
        (condDistrib (fun p => (C p).1) B μ b).prod
          (condDistrib (fun p => (C p).2) B μ b) :=
      firstHitCodeDistance_conditionalIndependence x r hr
    filter_upwards [hOld] with b hb
    change condDistrib C B μ b =
      (condDistrib (fun p => (C p).1) B μ ×ₖ
        condDistrib (fun p => (C p).2) B μ) b
    rw [Kernel.prod_apply]
    exact hb
  have hPair := (condDistrib_ae_eq_iff_measure_eq_compProd
    hB.aemeasurable hC.aemeasurable κ).mp hFactor
  have hJoint : μ.map (fun p => (B p, C p)) =
      (Kernel.id ×ₖ
        (condDistrib (fun p => (C p).1) B μ ×ₖ
          condDistrib (fun p => (C p).2) B μ)) ∘ₘ μ.map B := by
    rw [← Measure.compProd_eq_comp_prod]
    exact hPair
  exact (ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    (μ := μ) (f := fun p => (C p).1) (g := fun p => (C p).2)
    hC.fst hC.snd hB).2 hJoint

end DirectedDistances.PaperProofs.Section4
