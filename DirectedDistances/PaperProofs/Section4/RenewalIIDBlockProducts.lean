module

public import DirectedDistances.PaperProofs.Section4.RenewalIIDBlocks
import DirectedDistances.Probability.ShiftIndependenceInduction

/-! product laws for a supplied literal success graph T (NOT the admitted source T_m or
Lemma 4.9); not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk
open scoped ENNReal Classical




theorem selectorRenewal_oneStep_product
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    MeasurePreserving (selectorRenewalFuture T)
        (conditionedVectorPathLaw 0 0) (conditionedVectorPathLaw 0 0) ∧
      (conditionedVectorPathLaw 0 0).map
          (fun p => (selectorRenewalBlock T p, selectorRenewalFuture T p)) =
        ((conditionedVectorPathLaw 0 0).map (selectorRenewalBlock T)).prod
          (conditionedVectorPathLaw 0 0) := by
  let μ := conditionedVectorPathLaw 0 0
  have : IsProbabilityMeasure μ :=
    (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).1
  let U : (ℕ → ℤ × ℤ) → WithTop ℕ := fun p => T 1 p
  let E := {p : ℕ → ℤ × ℤ | U p < ⊤}
  let μf : Measure E := μ.comap Subtype.val
  let history := stoppedVectorHistory (finiteTimeIndex U) (fun ω => ω.val)
  let future := stoppedVectorFuture (finiteTimeIndex U) (fun ω => ω.val)
  have ht := selectorRenewalTime_measurable T hT 1
  have hu : Measurable U := by
    intro s _
    exact ht (@Set.Countable.measurableSet ℕ∞ ENat.instMeasurableSpace
      inferInstance s (Set.to_countable s))
  have hE : MeasurableSet E := hu measurableSet_Iio
  have hval : μf.map (Subtype.val : E → (ℕ → ℤ × ℤ)) = μ := by
    change (μ.comap (Subtype.val : E → _)).map Subtype.val = μ
    rw [map_comap_subtype_coe hE]
    exact Measure.restrict_eq_self_of_ae_mem (selectorRenewalTime_finite_ae T hT 1)
  have hn (ω : E) : finiteTimeIndex U ω = (T 1 ω.val).toNat := by
    have h := coe_finiteTimeIndex U ω
    have h' : (finiteTimeIndex U ω : ℕ∞) = T 1 ω.val := h
    simpa only [ENat.toNat_natCast] using congrArg ENat.toNat h'
  have hh : history = selectorRenewalBlock T ∘ (Subtype.val : E → _) := by
    funext ω
    dsimp [history, selectorRenewalBlock, Function.comp_def, stoppedVectorHistory]
    rw [hn]
  have hf : future = selectorRenewalFuture T ∘ (Subtype.val : E → _) := by
    funext ω
    dsimp only [future, selectorRenewalFuture, Function.comp_def]
    rw [stoppedVectorFuture_eq_of_time _ _ ω _ (hn ω),
      stoppedVectorFuture_eq_of_time _ _ ω.val _ rfl]
    rfl
  have hhistory : Measurable history :=
    measurable_finiteTime_vectorHistory U id hu measurable_id
  have hfuture : Measurable future :=
    measurable_finiteTime_vectorFuture U id hu measurable_id
  have hB := selectorRenewalBlock_measurable T hT
  have hR := selectorRenewalFuture_measurable T hT
  have hhistoryLaw : μf.map history = μ.map (selectorRenewalBlock T) := by
    rw [hh, ← Measure.map_map hB measurable_subtype_coe, hval]
  have hjointLaw : μf.map (fun ω => (history ω, future ω)) =
      μ.map (fun p => (selectorRenewalBlock T p, selectorRenewalFuture T p)) := by
    rw [hh, hf]
    change μf.map ((fun p => (selectorRenewalBlock T p, selectorRenewalFuture T p)) ∘
      Subtype.val) = _
    rw [← Measure.map_map (hB.prodMk hR) measurable_subtype_coe, hval]
  have hcond := conditionedVectorPathLaw_selector_regeneration 1 U (fun p => by
    exact hT p 1)
  have hjoint : μ.map (fun p => (selectorRenewalBlock T p, selectorRenewalFuture T p)) =
      (μ.map (selectorRenewalBlock T)).prod μ := by
    rw [← hjointLaw, ← hhistoryLaw, ← Measure.compProd_const]
    apply (condDistrib_ae_eq_iff_measure_eq_compProd
      hhistory.aemeasurable hfuture.aemeasurable _).mp
    exact hcond
  have hRlaw : μ.map (selectorRenewalFuture T) = μ := by
    calc
      μ.map (selectorRenewalFuture T) =
          (μ.map (fun p => (selectorRenewalBlock T p, selectorRenewalFuture T p))).map
            Prod.snd := by
        rw [Measure.map_map measurable_snd (hB.prodMk hR)]
        rfl
      _ = ((μ.map (selectorRenewalBlock T)).prod μ).map Prod.snd := by rw [hjoint]
      _ = (μ.map (selectorRenewalBlock T)) Set.univ • μ := Measure.map_snd_prod
      _ = μ := by simp
  exact ⟨⟨hR, hRlaw⟩, hjoint⟩

private theorem block_iIndepFun_cons {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {head : Ω → α} {tail : Fin n → Ω → α}
    (hheadM : Measurable head) (htailM : ∀ i, Measurable (tail i))
    (hhead : IndepFun head (fun ω i => tail i ω) μ)
    (htail : iIndepFun tail μ) :
    iIndepFun (Fin.cons (α := fun _ : Fin (n + 1) => Ω → α) head tail) μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
  let y : Ω → (Fin n → α) := fun ω i => tail i ω
  let F : Ω → (Fin (n + 1) → α) := fun ω => e.symm (head ω, y ω)
  have hyM : Measurable y := measurable_pi_iff.mpr htailM
  have hFM : Measurable F := e.symm.measurable.comp (hheadM.prodMk hyM)
  have hXA : ∀ i, AEMeasurable (fun ω => F ω i) μ := fun i =>
    ((measurable_pi_apply i).comp hFM).aemeasurable
  have htailLaw : μ.map y = Measure.pi (fun i => μ.map (tail i)) :=
    htail.map_fun_eq_pi_map fun i => (htailM i).aemeasurable
  have hpair : μ.map (fun ω => (head ω, y ω)) =
      (μ.map head).prod (μ.map y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hheadM.aemeasurable hyM.aemeasurable).mp hhead
  let ν : Fin (n + 1) → Measure α := fun i => μ.map (fun ω => F ω i)
  have hmapF : (μ.map F).map e = (Measure.pi ν).map e := by
    calc
      (μ.map F).map e = μ.map (fun ω => (head ω, y ω)) := by
        rw [Measure.map_map e.measurable hFM]
        apply Measure.map_congr
        filter_upwards with ω
        simp [F, e, y]
      _ = (μ.map head).prod (μ.map y) := hpair
      _ = (Measure.pi ν).map e := by
        symm
        rw [(measurePreserving_piFinSuccAbove ν 0).map_eq]
        congr 1
        exact htailLaw.symm
  have hFInd : iIndepFun (fun i : Fin (n + 1) => fun ω => F ω i) μ := by
    rw [iIndepFun_iff_map_fun_eq_pi_map hXA]
    exact (MeasurableEquiv.map_measurableEquiv_injective e) hmapF
  have heq : (fun i : Fin (n + 1) => fun ω => F ω i) =
      Fin.cons (α := fun _ : Fin (n + 1) => Ω → α) head tail := by
    funext i ω
    refine Fin.cases ?_ ?_ i
    · simp [F, e, y]
    · intro j
      simp [F, e, y]
  exact hFInd.congr fun i => Filter.EventuallyEq.of_eq (by
    funext ω
    exact congrFun (congrFun heq i) ω)

private theorem block_prefix_indep {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Ω → Ω} {B : Ω → α}
    (hR : MeasurePreserving R μ μ) (hB : Measurable B) (hBR : IndepFun B R μ) :
    ∀ (m start : ℕ), iIndepFun (fun i : Fin m => fun p => B (R^[start + i.val] p)) μ := by
  intro m
  induction m with
  | zero =>
      intro start
      exact iIndepFun.of_subsingleton
  | succ m ih =>
      intro start
      let tail : Fin m → Ω → α := fun i p => B (R^[(start + 1) + i.val] p)
      let q : Ω → Fin m → α := fun p i => B (R^[i.val] p)
      have hq : Measurable q := measurable_pi_iff.mpr fun i =>
        hB.comp (hR.iterate i.val).measurable
      have hbase := hBR.comp measurable_id hq
      have hcomp := DirectedDistances.Probability.indepFun_comp_measurePreserving
        (hR.iterate start) hbase hB (hq.comp hR.measurable)
      have hheadTail : IndepFun (fun p => B (R^[start] p)) (fun p i => tail i p) μ := by
        apply hcomp.congr (Filter.EventuallyEq.of_eq rfl)
        apply Filter.EventuallyEq.of_eq
        funext p i
        dsimp [Function.comp_def, q, tail]
        congr 1
        rw [← Function.iterate_succ_apply' R start p,
          ← Function.iterate_add_apply R i.val (start + 1) p,
          Nat.add_comm i.val (start + 1)]
      have htail : iIndepFun tail μ := ih (start + 1)
      have hcons := block_iIndepFun_cons (hB.comp (hR.iterate start).measurable)
        (fun i => hB.comp (hR.iterate _).measurable) hheadTail htail
      have heq : Fin.cons (fun p => B (R^[start] p)) tail =
          (fun i : Fin (m + 1) => fun p => B (R^[start + i.val] p)) := by
        funext i p
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j
          simp only [Fin.cons_succ]
          dsimp [tail]
          rw [Nat.add_assoc, Nat.add_comm 1 j.val]
      exact hcons.congr fun i => Filter.EventuallyEq.of_eq (by
        funext p
        exact congrFun (congrFun heq i) p)




theorem selectorRenewal_iterates_iid
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    (∀ j : ℕ, (conditionedVectorPathLaw 0 0).map
        (fun p => selectorRenewalBlock T ((selectorRenewalFuture T)^[j] p)) =
      (conditionedVectorPathLaw 0 0).map (selectorRenewalBlock T)) ∧
    iIndepFun (fun j : ℕ => fun p =>
      selectorRenewalBlock T ((selectorRenewalFuture T)^[j] p))
      (conditionedVectorPathLaw 0 0) := by
  let μ := conditionedVectorPathLaw 0 0
  have : IsProbabilityMeasure μ :=
    (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).1
  obtain ⟨hR, hprod⟩ := selectorRenewal_oneStep_product T hT
  have hB := selectorRenewalBlock_measurable T hT
  have hBR : IndepFun (selectorRenewalBlock T) (selectorRenewalFuture T) μ := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hB.aemeasurable
      hR.measurable.aemeasurable).mpr
    rw [hR.map_eq]
    exact hprod
  constructor
  · intro j
    change μ.map (selectorRenewalBlock T ∘ (selectorRenewalFuture T)^[j]) = _
    rw [← Measure.map_map hB (hR.iterate j).measurable, (hR.iterate j).map_eq]
  · rw [iIndepFun_iff_finset]
    intro s
    let N := s.sup id + 1
    let g : s → Fin N := fun i => ⟨i.val,
      Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
    have hprefix := block_prefix_indep hR hB hBR N 0
    have hinj : Function.Injective g := fun i j hij => Subtype.ext (congrArg Fin.val hij)
    have hrestr := hprefix.precomp hinj
    exact hrestr.congr fun i => Filter.EventuallyEq.of_eq (by
      funext p
      simp only [g, Nat.zero_add, Finset.restrict_def])

end DirectedDistances.PaperProofs.Section4
