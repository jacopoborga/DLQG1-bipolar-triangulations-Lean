module

public import DirectedDistances.Probability.SkorokhodJ1LocalPositive
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.CondDistrib

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Finset MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder





theorem condDistrib_bonding_map_eq_id
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (π : Y → X) (hπ : Measurable π) (ν : ProbabilityMeasure Y) :
    (condDistrib (fun y : Y => y) π (ν : Measure Y)).map π
      =ᵐ[(ν : Measure Y).map π] Kernel.id := by
  have hcomp := condDistrib_comp (X := π) (Y := fun y : Y => y)
    (μ := (ν : Measure Y)) (f := π) hπ.aemeasurable measurable_id.aemeasurable hπ
  have hself := condDistrib_self (Y := π) (μ := (ν : Measure Y)) hπ.aemeasurable
  have hself' : condDistrib (π ∘ fun y : Y => y) π (ν : Measure Y)
      =ᵐ[(ν : Measure Y).map π] Kernel.id := by
    simpa only [Function.comp_def, id_eq] using hself
  filter_upwards [hcomp, hself'] with x hc hs
  rw [← hc, hs]




theorem condDistrib_bonding_comp_map
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (π : Y → X) (hπ : Measurable π) (ν : ProbabilityMeasure Y) :
    condDistrib (fun y : Y => y) π (ν : Measure Y) ∘ₘ
      ((ν : Measure Y).map π) = (ν : Measure Y) := by
  simpa using
    (condDistrib_comp_map (X := π) (Y := fun y : Y => y)
      (μ := (ν : Measure Y)) hπ.aemeasurable measurable_id.aemeasurable)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
For a measurable bonding map, the conditional transition from coordinate `m`
to coordinate `m + 1`. -/
noncomputable def projectiveTransition
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m)
    (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m)) (m : ℕ) :
    Kernel (X m) (X (m + 1)) := by
  let _hπm := hπ m
  letI : Nonempty (X (m + 1)) :=
    nonempty_of_isProbabilityMeasure (ν (m + 1) : Measure (X (m + 1)))
  exact condDistrib (fun y : X (m + 1) => y) (π m) (ν (m + 1) : Measure (X (m + 1)))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Each conditional transition is a Markov kernel. -/
instance projectiveTransition_isMarkovKernel
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m)) (m : ℕ) :
    IsMarkovKernel (projectiveTransition π hπ ν m) := by
  rw [projectiveTransition]
  infer_instance

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The transition kernel recovers the next-coordinate law after averaging. -/
theorem projectiveTransition_comp
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (hν : ∀ m,
      (ν (m + 1) : Measure (X (m + 1))).map (π m) =
        (ν m : Measure (X m))) (m : ℕ) :
    projectiveTransition π hπ ν m ∘ₘ (ν m : Measure (X m)) =
      (ν (m + 1) : Measure (X (m + 1))) := by
  have hn₀ : Nonempty (X m) := nonempty_of_isProbabilityMeasure (ν m : Measure (X m))
  have hn₁ : Nonempty (X (m + 1)) :=
    nonempty_of_isProbabilityMeasure (ν (m + 1) : Measure (X (m + 1)))
  rw [projectiveTransition]
  rw [show (ν m : Measure (X m)) =
    (ν (m + 1) : Measure (X (m + 1))).map (π m) by exact (hν m).symm]
  exact @condDistrib_bonding_comp_map (X m) (X (m + 1)) _ _ hn₀ _ _ hn₁
    (π m) (hπ m) (ν (m + 1))

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The transition is supported on pairs related by the bonding map, almost everywhere. -/
theorem projectiveTransition_map_eq_id
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (hν : ∀ m,
      (ν (m + 1) : Measure (X (m + 1))).map (π m) =
        (ν m : Measure (X m))) (m : ℕ) :
    (projectiveTransition π hπ ν m).map (π m)
      =ᵐ[(ν m : Measure (X m))] Kernel.id := by
  have hn₀ : Nonempty (X m) := nonempty_of_isProbabilityMeasure (ν m : Measure (X m))
  have hn₁ : Nonempty (X (m + 1)) :=
    nonempty_of_isProbabilityMeasure (ν (m + 1) : Measure (X (m + 1)))
  have h := @condDistrib_bonding_map_eq_id (X m) (X (m + 1)) _ _ hn₀ _ _ hn₁
    (π m) (hπ m) (ν (m + 1))
  simpa [projectiveTransition, hν m] using h



theorem projectiveTransition_ae_bonding
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (hν : ∀ m,
      (ν (m + 1) : Measure (X (m + 1))).map (π m) =
        (ν m : Measure (X m))) (m : ℕ) :
    ∀ᵐ x ∂(ν m : Measure (X m)),
      ∀ᵐ y ∂projectiveTransition π hπ ν m x, π m y = x := by
  have h := projectiveTransition_map_eq_id π hπ ν hν m
  filter_upwards [h] with x hx
  rw [Kernel.map_apply _ (hπ m)] at hx
  have hmap : (projectiveTransition π hπ ν m x).map (π m) = Measure.dirac x := by
    simpa only [Kernel.id_apply] using hx
  have hdirac :
      ∀ᵐ z ∂(projectiveTransition π hπ ν m x).map (π m), z = x := by
    rw [hmap]
    exact (ae_dirac_iff measurableSet_eq).2 rfl
  exact (ae_map_iff (hπ m).aemeasurable measurableSet_eq).1 hdirac

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The next-coordinate kernel depends on the history through its last coordinate. -/
noncomputable def projectiveHistoryKernel
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (m : ℕ) : Kernel (Π i : Iic m, X i) (X (m + 1)) :=
  projectiveTransition π hπ ν m ∘ₖ Kernel.deterministic
    (fun x : Π i : Iic m, X i => x ⟨m, mem_Iic.2 le_rfl⟩) (by fun_prop)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Each history-dependent transition is a Markov kernel. -/
instance projectiveHistoryKernel_isMarkovKernel
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m)) (m : ℕ) :
    IsMarkovKernel (projectiveHistoryKernel π hπ ν m) := by
  rw [projectiveHistoryKernel]
  infer_instance

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The trajectory law obtained by iterating the conditional transition kernels. -/
noncomputable def projectiveTrajectoryLaw
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m)) :
    Measure (Π m, X m) :=
  Kernel.trajMeasure (ν 0 : Measure (X 0)) (projectiveHistoryKernel π hπ ν)



instance projectiveTrajectoryLaw_isProbabilityMeasure
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m)) :
    IsProbabilityMeasure (projectiveTrajectoryLaw π hπ ν) := by
  rw [projectiveTrajectoryLaw]
  infer_instance



theorem projectiveTrajectoryLaw_eval_succ
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (m : ℕ) :
    (projectiveTrajectoryLaw π hπ ν).map (fun x : Π n, X n => x (m + 1)) =
      projectiveTransition π hπ ν m ∘ₘ
        ((projectiveTrajectoryLaw π hπ ν).map (fun x : Π n, X n => x m)) := by
  let μ := projectiveTrajectoryLaw π hπ ν
  have hpair :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (μ₀ := (ν 0 : Measure (X 0)))
      (κ := projectiveHistoryKernel π hπ ν) (a := m)
  have hpair' :
      (μ.map (frestrictLe m)) ⊗ₘ projectiveHistoryKernel π hπ ν m =
        μ.map (fun x : Π n, X n => (frestrictLe m x, x (m + 1))) := by
    simpa [μ, projectiveTrajectoryLaw] using hpair
  have hlast :
      (μ.map (frestrictLe m)).map
          (fun x : Π i : Iic m, X i => x ⟨m, mem_Iic.2 le_rfl⟩) =
        μ.map (fun x : Π n, X n => x m) := by
    rw [Measure.map_map (measurable_pi_apply _) (by fun_prop)]
    exact congrArg (fun f : (Π n, X n) → X m => μ.map f) (by
      funext x
      rfl)
  calc
    μ.map (fun x : Π n, X n => x (m + 1)) =
        ((μ.map (frestrictLe m)) ⊗ₘ projectiveHistoryKernel π hπ ν m).snd := by
      rw [hpair', Measure.snd_map_prodMk (by fun_prop) (by fun_prop)]
    _ = projectiveHistoryKernel π hπ ν m ∘ₘ (μ.map (frestrictLe m)) :=
      Measure.snd_compProd _ _
    _ = projectiveTransition π hπ ν m ∘ₘ
          ((μ.map (frestrictLe m)).map
            (fun x : Π i : Iic m, X i => x ⟨m, mem_Iic.2 le_rfl⟩)) := by
      rw [projectiveHistoryKernel, ← Measure.comp_assoc,
        Measure.deterministic_comp_eq_map (by fun_prop)]
    _ = projectiveTransition π hπ ν m ∘ₘ (μ.map (fun x : Π n, X n => x m)) := by
      rw [hlast]
    _ = projectiveTransition π hπ ν m ∘ₘ
          ((projectiveTrajectoryLaw π hπ ν).map (fun x : Π n, X n => x m)) := by
      rfl



theorem projectiveTrajectoryLaw_map_eval
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (hν : ∀ m,
      (ν (m + 1) : Measure (X (m + 1))).map (π m) =
        (ν m : Measure (X m))) :
    ∀ m, (projectiveTrajectoryLaw π hπ ν).map (fun x : Π n, X n => x m) =
      (ν m : Measure (X m)) := by
  intro m
  induction m with
  | zero =>
      rw [projectiveTrajectoryLaw, Kernel.trajMeasure]
      let e := MeasurableEquiv.piUnique (fun i : Iic 0 => X i)
      have heval : (fun x : Π n, X n => x 0) = e ∘ frestrictLe 0 := by
        funext x
        rfl
      have htraj :
          (Kernel.traj (projectiveHistoryKernel π hπ ν) 0).map
              (fun x : Π n, X n => x 0) = Kernel.deterministic e e.measurable := by
        rw [heval, Kernel.map_comp_right _ (measurable_frestrictLe 0) e.measurable,
          Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map]
      rw [Measure.map_comp _ _ (by fun_prop), htraj,
        Measure.deterministic_comp_eq_map e.measurable,
        Measure.map_map e.measurable e.symm.measurable]
      have he : (e : (Π i : Iic 0, X i) → X 0) ∘ e.symm = id := by
        funext x
        exact e.apply_symm_apply x
      rw [he, Measure.map_id]
  | succ m ih =>
      rw [projectiveTrajectoryLaw_eval_succ]
      rw [ih, projectiveTransition_comp π hπ ν hν]



theorem projectiveTrajectoryLaw_ae_bonding
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (hν : ∀ m,
      (ν (m + 1) : Measure (X (m + 1))).map (π m) =
        (ν m : Measure (X m))) :
    ∀ᵐ x ∂(projectiveTrajectoryLaw π hπ ν),
      ∀ m, π m (x (m + 1)) = x m := by
  rw [ae_all_iff]
  intro m
  let μ := projectiveTrajectoryLaw π hπ ν
  let last : (Π i : Iic m, X i) → X m := fun h => h ⟨m, mem_Iic.2 le_rfl⟩
  let pair : (Π i : Iic m, X i) × X (m + 1) → Prop :=
    fun z => π m z.2 = last z.1
  have hlast : (μ.map (frestrictLe m)).map last = (ν m : Measure (X m)) := by
    rw [Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe m)]
    have heval : last ∘ frestrictLe m = fun x : Π n, X n => x m := by
      funext x
      rfl
    rw [heval]
    exact projectiveTrajectoryLaw_map_eval π hπ ν hν m
  have hgood := projectiveTransition_ae_bonding π hπ ν hν m
  rw [← hlast] at hgood
  have hgood' :
      ∀ᵐ h ∂μ.map (frestrictLe m),
        ∀ᵐ y ∂projectiveHistoryKernel π hπ ν m h, π m y = last h := by
    have hlastMeas : Measurable last := measurable_pi_apply _
    have htendsto := Measure.tendsto_ae_map (μ := μ.map (frestrictLe m))
      (f := last) hlastMeas.aemeasurable
    filter_upwards [htendsto hgood] with h hh
    have hk : projectiveHistoryKernel π hπ ν m h =
        projectiveTransition π hπ ν m (last h) := by
      change (projectiveTransition π hπ ν m ∘ₖ
        Kernel.deterministic (fun x : Π i : Iic m, X i => last x) (by fun_prop)) h = _
      rw [Kernel.comp_apply, Kernel.deterministic_apply,
        Measure.dirac_bind (Kernel.measurable _)]
    simpa [hk] using hh
  have hset : MeasurableSet {z | pair z} := by
    apply measurableSet_eq_fun
    · exact (hπ m).comp measurable_snd
    · exact (measurable_pi_apply _).comp measurable_fst
  have hcomp :
      ∀ᵐ z ∂((μ.map (frestrictLe m)) ⊗ₘ projectiveHistoryKernel π hπ ν m), pair z := by
    apply (Measure.ae_compProd_iff hset).2
    exact hgood'
  have hpair :
      (μ.map (frestrictLe m)) ⊗ₘ projectiveHistoryKernel π hπ ν m =
        μ.map (fun x : Π n, X n => (frestrictLe m x, x (m + 1))) := by
    simpa [μ, projectiveTrajectoryLaw] using
      (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (μ₀ := (ν 0 : Measure (X 0)))
        (κ := projectiveHistoryKernel π hπ ν) (a := m))
  have hpairAE :
      ∀ᵐ z ∂μ.map (fun x : Π n, X n => (frestrictLe m x, x (m + 1))), pair z := by
    rw [← hpair]
    exact hcomp
  have hmeas : Measurable (fun x : Π n, X n => (frestrictLe m x, x (m + 1))) := by
    fun_prop
  have hpath := (ae_map_iff hmeas.aemeasurable hset).1 hpairAE
  simpa [pair, last] using hpath



theorem projectiveProbabilityOnInverseLimit_map
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (hν : ∀ m,
      (ν (m + 1) : Measure (X (m + 1))).map (π m) =
        (ν m : Measure (X m))) :
    ∃ P : ProbabilityMeasure
      {x : (m : ℕ) → X m // ∀ m, π m (x (m + 1)) = x m},
      (P : Measure
        {x : (m : ℕ) → X m // ∀ m, π m (x (m + 1)) = x m}).map
          (Subtype.val :
            {x : (m : ℕ) → X m // ∀ m, π m (x (m + 1)) = x m} → (m : ℕ) → X m) =
        projectiveTrajectoryLaw π hπ ν := by
  let μ := projectiveTrajectoryLaw π hπ ν
  let S : Set (Π m, X m) := {x | ∀ m, π m (x (m + 1)) = x m}
  have hSmeas : MeasurableSet S := by
    rw [show S = ⋂ m : ℕ, {x | π m (x (m + 1)) = x m} by
      ext x
      simp [S]]
    exact MeasurableSet.iInter fun m =>
      measurableSet_eq_fun ((hπ m).comp (measurable_pi_apply _))
        (measurable_pi_apply _)
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    simpa [μ, S] using projectiveTrajectoryLaw_ae_bonding π hπ ν hν
  have hmass : μ S = 1 := by
    calc
      μ S = (μ.restrict S) Set.univ := by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp
      _ = μ Set.univ := by rw [Measure.restrict_eq_self_of_ae_mem hSae]
      _ = 1 := measure_univ
  let P : ProbabilityMeasure
      {x : Π m, X m // ∀ m, π m (x (m + 1)) = x m} :=
    ⟨μ.comap (Subtype.val :
      {x : Π m, X m // ∀ m, π m (x (m + 1)) = x m} → Π m, X m), by
      rw [isProbabilityMeasure_iff]
      change (μ.comap (Subtype.val : S → Π m, X m)) Set.univ = 1
      rw [comap_subtype_coe_apply hSmeas μ Set.univ]
      rw [Set.image_univ, Subtype.range_coe]
      simpa [S] using hmass⟩
  refine ⟨P, ?_⟩
  change (P : Measure
    {x : Π m, X m // ∀ m, π m (x (m + 1)) = x m}).map Subtype.val = μ
  dsimp [P]
  change (μ.comap (Subtype.val : S → Π m, X m)).map
      (Subtype.val : S → Π m, X m) = μ
  rw [map_comap_subtype_coe hSmeas]
  exact Measure.restrict_eq_self_of_ae_mem hSae



theorem projectiveProbabilityOnInverseLimit
    {X : ℕ → Type*} [∀ m, MeasurableSpace (X m)]
    [∀ m, StandardBorelSpace (X m)]
    (π : ∀ m, X (m + 1) → X m) (hπ : ∀ m, Measurable (π m))
    (ν : ∀ m, ProbabilityMeasure (X m))
    (hν : ∀ m,
      (ν (m + 1) : Measure (X (m + 1))).map (π m) =
        (ν m : Measure (X m))) :
    ∃ P : ProbabilityMeasure
      {x : (m : ℕ) → X m // ∀ m, π m (x (m + 1)) = x m},
      ∀ m, (P : Measure
        {x : (m : ℕ) → X m // ∀ m, π m (x (m + 1)) = x m}).map
          (fun x => x.1 m) = (ν m : Measure (X m)) := by
  obtain ⟨P, hP⟩ := projectiveProbabilityOnInverseLimit_map π hπ ν hν
  refine ⟨P, ?_⟩
  intro m
  rw [show (fun x : {x : (n : ℕ) → X n //
      ∀ n, π n (x (n + 1)) = x n} => x.1 m) =
        (fun x : (n : ℕ) → X n => x m) ∘ Subtype.val by rfl]
  rw [← Measure.map_map (measurable_pi_apply _) measurable_subtype_coe, hP]
  exact projectiveTrajectoryLaw_map_eval π hπ ν hν m

end DirectedDistances.Probability
