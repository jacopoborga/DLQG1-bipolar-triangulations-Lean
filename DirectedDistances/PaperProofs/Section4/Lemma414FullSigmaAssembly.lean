module

public import DirectedDistances.PaperProofs.Section4.Lemma414FullSigma
public import DirectedDistances.PaperProofs.Section4.Lemma414PositiveSigma
public import DirectedDistances.PaperProofs.Section4.Lemma414FiltrationBridge
public import DirectedDistances.PaperProofs.Section4.Lemma414SideCarrier

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.KMSW DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open Quiver
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "T" => (fun m p => DirectedDistances.Paper.Section4.renewalTime m p)
local notation "hT" => renewalTime_positiveSuccessTime

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_path_in_late_stages {w : ℕ → Fin 3} {a b : PresentVertex w}
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

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_mem_present_pathLengths_iff (w : ℕ → Fin 3) (a b k : ℕ) :
    k ∈ pathLengths (⟨a⟩ : PresentVertex w) ⟨b⟩ ↔
      ∃ n, k ∈ pathLengths (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨N, hN⟩ := assembly_path_in_late_stages p
    obtain ⟨q, hq⟩ := hN N le_rfl
    exact ⟨N, q, hq⟩
  · rintro ⟨n, hk⟩
    exact pathLengths_stage_subset w n ⟨a⟩ ⟨b⟩ hk

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurableSet_present_pathLengths (a b k : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 |
      k ∈ pathLengths (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} := by
  have he : {ω : ℕ → Fin 3 |
      k ∈ pathLengths (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} =
      ⋃ n : ℕ, {ω : ℕ → Fin 3 |
        k ∈ pathLengths
          (⟨a⟩ : StagePresentVertex (boltzmannKMSWStream ω) n) ⟨b⟩} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, assembly_mem_present_pathLengths_iff]
  rw [he]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_stage_pathLengths n a b (fun s => k ∈ s)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurable_of_countable_le
    {S α : Type*} [MeasurableSpace S] [MeasurableSpace α]
    [Countable α] [LinearOrder α] (f : S → α)
    (hf : ∀ z, MeasurableSet {p | f p ≤ z}) : Measurable f := by
  refine measurable_to_countable' fun z => ?_
  have he : f ⁻¹' {z} = {p | f p ≤ z} \
      ⋃ y : α, ⋃ (_ : y < z), {p | f p ≤ y} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
      Set.mem_ofPred_eq, Set.mem_iUnion, not_exists]
    constructor
    · rintro rfl
      exact ⟨le_rfl, fun y hy hzy => (not_le_of_gt hy) hzy⟩
    · rintro ⟨h, hn⟩
      exact le_antisymm h (le_of_not_gt fun hlt => hn (f p) hlt le_rfl)
  rw [he]
  exact (hf z).diff (MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun _ => hf y)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurable_presentLdp_comp (a b : ℕ) :
    Measurable (fun ω : ℕ → Fin 3 =>
      WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
        (presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩)) := by
  let : MeasurableSpace (WithBot ℕ∞) := ⊤
  have hm : Measurable (fun ω : ℕ → Fin 3 =>
      presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩) := by
    apply assembly_measurable_of_countable_le
    intro z
    have he : {ω : ℕ → Fin 3 |
        presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩ ≤ z} =
        ⋂ k : ℕ, {ω : ℕ → Fin 3 |
          k ∉ pathLengths
            (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} ∪
          {ω : ℕ → Fin 3 | ((k : ℕ∞) : WithBot ℕ∞) ≤ z} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union,
        presentLdp, iSup_le_iff]
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
      (assembly_measurableSet_present_pathLengths a b k).compl.union ?_
    by_cases h : ((k : ℕ∞) : WithBot ℕ∞) ≤ z <;>
      simp only [h, Set.ofPred_true, Set.ofPred_false,
        MeasurableSet.univ, MeasurableSet.empty]
  exact (measurable_of_countable
    (WithBot.recBotCoe (C := fun _ => ℕ) 0 fun d : ℕ∞ => d.toNat)).comp hm

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurable_presentSdp (a b : ℕ) :
    Measurable (fun ω : ℕ → Fin 3 =>
      sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩) := by
  let : Countable (OrderDual ℕ∞) := inferInstanceAs (Countable ℕ∞)
  apply assembly_measurable_of_countable_le (α := OrderDual ℕ∞)
    (fun ω => OrderDual.toDual
      (sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩))
  intro z
  change MeasurableSet {ω : ℕ → Fin 3 |
    OrderDual.ofDual z ≤ sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩}
  have he : {ω : ℕ → Fin 3 |
      OrderDual.ofDual z ≤ sdp
        (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} =
      ⋂ k : ℕ, {ω : ℕ → Fin 3 |
        k ∉ pathLengths
          (⟨a⟩ : PresentVertex (boltzmannKMSWStream ω)) ⟨b⟩} ∪
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
    (assembly_measurableSet_present_pathLengths a b k).compl.union ?_
  by_cases h : OrderDual.ofDual z ≤ (k : ℕ∞) <;>
    simp only [h, Set.ofPred_true, Set.ofPred_false,
      MeasurableSet.univ, MeasurableSet.empty]

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurable_fixed_distance (x : XDP) (a b : ℕ) :
    Measurable (fun p : Ω =>
      match x with
      | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
          (presentLdp (⟨a⟩ : PresentVertex
            (boltzmannKMSWStream (pathCode p))) ⟨b⟩)
      | .sdp => (sdp (⟨a⟩ : PresentVertex
          (boltzmannKMSWStream (pathCode p))) ⟨b⟩).toNat) := by
  cases x with
  | ldp => exact (assembly_measurable_presentLdp_comp a b).comp measurable_pathCode
  | sdp =>
    exact (measurable_of_countable ENat.toNat).comp
      ((assembly_measurable_presentSdp a b).comp measurable_pathCode)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurable_activeInitial (n : ℕ) :
    Measurable (fun p : Ω =>
      activeInitial (boltzmannKMSWStream (pathCode p)) n) := by
  have h := (measurable_kmswStage_shift_comp n (fun s => s.west s.active)).comp
    measurable_pathCode
  have heq : (fun p : Ω => activeInitial (boltzmannKMSWStream (pathCode p)) n) =
      fun p => (kmswStage (boltzmannKMSWStream (pathCode p)) n).west
        (act (boltzmannKMSWStream (pathCode p)) n) := by
    funext p
    exact CutConverse.activeInitial_eq _ _
  rw [heq]
  exact h

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurable_activeInitial_at
    (t : Ω → ℕ) (ht : Measurable t) :
    Measurable (fun p : Ω =>
      activeInitial (boltzmannKMSWStream (pathCode p)) (t p)) := by
  have h : Measurable (fun z : Ω × ℕ =>
      activeInitial (boltzmannKMSWStream (pathCode z.1)) z.2) :=
    measurable_from_prod_countable_left assembly_measurable_activeInitial
  exact h.comp (measurable_id.prodMk ht)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem assembly_measurable_selected_distance
    (x : XDP) (k : ℕ) :
    Measurable (fun p : Ω =>
      match x with
      | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
          (presentLdp
            (⟨activeInitial (boltzmannKMSWStream (pathCode p)) 0⟩ :
              PresentVertex (boltzmannKMSWStream (pathCode p)))
            ⟨activeInitial (boltzmannKMSWStream (pathCode p))
              (selectedCutTime T k p).toNat⟩)
      | .sdp => (sdp
          (⟨activeInitial (boltzmannKMSWStream (pathCode p)) 0⟩ :
            PresentVertex (boltzmannKMSWStream (pathCode p)))
          ⟨activeInitial (boltzmannKMSWStream (pathCode p))
            (selectedCutTime T k p).toNat⟩).toNat) := by
  let t := fun p : Ω => (selectedCutTime T k p).toNat
  have ht : Measurable t := by
    exact (measurable_of_countable ENat.toNat).comp
      (measurable_selectedCutTime T k hT)
  have ha := assembly_measurable_activeInitial 0
  have hb := assembly_measurable_activeInitial_at t ht
  have hab : Measurable (fun p : Ω =>
      (activeInitial (boltzmannKMSWStream (pathCode p)) 0,
        activeInitial (boltzmannKMSWStream (pathCode p)) (t p))) := ha.prodMk hb
  cases x with
  | ldp =>
    have hfixed : ∀ a b : ℕ, Measurable (fun p : Ω =>
        WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
          (presentLdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream (pathCode p))) ⟨b⟩)) := by
      intro a b
      exact assembly_measurable_fixed_distance .ldp a b
    have hsel : Measurable (fun z : Ω × (ℕ × ℕ) =>
        WithBot.recBotCoe (C := fun _ => ℕ) 0 (fun d : ℕ∞ => d.toNat)
          (presentLdp (⟨z.2.1⟩ : PresentVertex (boltzmannKMSWStream
            (pathCode z.1))) ⟨z.2.2⟩)) :=
      measurable_from_prod_countable_left fun ab => hfixed ab.1 ab.2
    simpa only [Function.comp_def, t] using hsel.comp
      (measurable_id.prodMk hab)
  | sdp =>
    have hfixed : ∀ a b : ℕ, Measurable (fun p : Ω =>
        (sdp (⟨a⟩ : PresentVertex (boltzmannKMSWStream (pathCode p))) ⟨b⟩).toNat) := by
      intro a b
      exact assembly_measurable_fixed_distance .sdp a b
    have hsel : Measurable (fun z : Ω × (ℕ × ℕ) =>
        (sdp (⟨z.2.1⟩ : PresentVertex (boltzmannKMSWStream (pathCode z.1)))
          ⟨z.2.2⟩).toNat) :=
      measurable_from_prod_countable_left fun ab => hfixed ab.1 ab.2
    simpa only [Function.comp_def, t] using hsel.comp
      (measurable_id.prodMk hab)

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
theorem assembly_measurable_sourceCutObservation (x : XDP) (k : ℕ) :
    Measurable (sourceCutObservation x k) := by
  have hfuture : Measurable (selectedCutFuture T k) :=
    measurable_selectedCutFuture T k hT
  have hdistance := assembly_measurable_selected_distance x k
  change Measurable (fun p : Ω =>
    (conditionedVectorShift (selectedCutTime T k p).toNat p,
      match x with
      | .ldp => WithBot.recBotCoe (C := fun _ => ℕ) 0
          (fun d : ℕ∞ => d.toNat)
          (presentLdp (⟨activeInitial (boltzmannKMSWStream
            (pathCode p)) 0⟩ : PresentVertex
              (boltzmannKMSWStream (pathCode p)))
            ⟨activeInitial (boltzmannKMSWStream (pathCode p))
              (selectedCutTime T k p).toNat⟩)
      | .sdp => (sdp (⟨activeInitial (boltzmannKMSWStream
          (pathCode p)) 0⟩ : PresentVertex
            (boltzmannKMSWStream (pathCode p)))
          ⟨activeInitial (boltzmannKMSWStream (pathCode p))
            (selectedCutTime T k p).toNat⟩).toNat))
  exact hfuture.prodMk hdistance

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
theorem sourceCutFiltration_le_ambient (x : XDP) (k : ℕ) :
    sourceCutFiltration x k ≤ (inferInstance : MeasurableSpace Ω) := by
  change MeasurableSpace.comap (sourceCutObservation x k) inferInstance ≤ _
  exact (assembly_measurable_sourceCutObservation x k).comap_le

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
def lemma414_full_sigma_assembly_obligation : Prop :=
  ∀ (x : XDP) (k : ℕ), 1 ≤ k →
    ProbabilityTheory.CondIndepFun (sourceCutFiltration x k)
      (sourceCutFiltration_le_ambient x k)
      (fun p => (selectedCutPastSides x DirectedDistances.Paper.Section4.renewalTime
        DirectedDistances.PaperProofs.Section4.renewalTime_positiveSuccessTime k p).1)
      (fun p => (selectedCutPastSides x DirectedDistances.Paper.Section4.renewalTime
        DirectedDistances.PaperProofs.Section4.renewalTime_positiveSuccessTime k p).2)
      (conditionedVectorPathLaw 0 0)

end DirectedDistances.PaperProofs.Section4
