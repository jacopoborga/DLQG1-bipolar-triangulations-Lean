module

public import DirectedDistances.Probability.SkorokhodJ1WindowBorel
public import DirectedDistances.Probability.SkorokhodJ1WindowDEvalInterior
public import DirectedDistances.Probability.SkorokhodJ1WindowSeparableSpace
public import Mathlib.MeasureTheory.Constructions.Cylinders

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section
namespace DirectedDistances.Probability

open Filter MeasureTheory
open scoped Topology

private theorem exists_dense_right_sequence {T : ℝ}
    (D : Set (J1Window T)) (hD : Dense D) (t : J1Window T)
    (ht : (t : ℝ) < T) :
    ∃ u : ℕ → J1Window T, (∀ n, u n ∈ D) ∧ (∀ n, t < u n) ∧
      Tendsto u atTop (𝓝 t) := by
  classical
  let ε (n : ℕ) := min (T - (t : ℝ)) (1 / (n + 1 : ℝ))
  have hε (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    exact lt_min (sub_pos.mpr ht) (by positivity)
  let c (n : ℕ) : J1Window T :=
    ⟨(t : ℝ) + ε n / 2, add_nonneg t.property.1 (by positivity), by
      have hn : ε n ≤ T - (t : ℝ) := min_le_left _ _
      linarith [t.property.2]⟩
  have hchoose (n : ℕ) : ∃ s ∈ D, dist (c n) s < ε n / 4 :=
    hD.exists_dist_lt (c n) (by positivity)
  choose u huD hudist using hchoose
  have hclose (n : ℕ) : |(u n : ℝ) - (c n : ℝ)| < ε n / 4 := by
    have h := hudist n
    rw [Subtype.dist_eq, Real.dist_eq] at h
    rw [abs_sub_comm] at h
    exact h
  have hright (n : ℕ) : t < u n := by
    have hlow := (abs_lt.mp (hclose n)).1
    change (t : ℝ) < (u n : ℝ)
    have hc : (c n : ℝ) = (t : ℝ) + ε n / 2 := rfl
    rw [hc] at hlow
    linarith [hε n]
  have hsmall (n : ℕ) : dist (u n) t < 1 / (n + 1 : ℝ) := by
    have hu := (abs_lt.mp (hclose n)).2
    change |(u n : ℝ) - (t : ℝ)| < 1 / (n + 1 : ℝ)
    rw [abs_of_pos (sub_pos.mpr (show (t : ℝ) < (u n : ℝ) from hright n))]
    have hc : (c n : ℝ) = (t : ℝ) + ε n / 2 := rfl
    rw [hc] at hu
    have hn : ε n ≤ 1 / (n + 1 : ℝ) := min_le_right _ _
    calc
      (u n : ℝ) - (t : ℝ) < ε n := by nlinarith [hu, hε n]
      _ ≤ 1 / (n + 1 : ℝ) := hn
  have htendsto : Tendsto u atTop (𝓝 t) := by
    apply (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).2
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, trivial, ?_⟩
    intro n hn
    have hn' : N ≤ n := le_of_lt hn
    have hNn : (N + 1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ hn'
    have hrecip : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hNn
    exact (hsmall n).trans_le (hrecip.trans hN.le)
  exact ⟨u, huD, hright, htendsto⟩




theorem iSup_comap_eval_le_borel {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) :
    (⨆ t ∈ D, MeasurableSpace.comap
      (fun x : J1WindowD T hT => x.path.1 t) (borel ℝ)) ≤
      borel (J1WindowD T hT) := by
  refine iSup_le fun t => iSup_le fun _ => ?_
  exact (measurable_j1WindowD_eval hT t).comap_le




theorem measurable_j1WindowD_eval_cylinder {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) (hD : Dense D)
    (hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ D)
    (t : J1Window T) :
    Measurable[⨆ s ∈ D, MeasurableSpace.comap
      (fun x : J1WindowD T hT => x.path.1 s) (borel ℝ)]
      (fun x : J1WindowD T hT => x.path.1 t) := by
  let cylinder : MeasurableSpace (J1WindowD T hT) :=
    ⨆ s ∈ D, MeasurableSpace.comap
      (fun x : J1WindowD T hT => x.path.1 s) (borel ℝ)
  by_cases ht : (t : ℝ) = T
  · have heq : t = (⟨T, hT.le, le_rfl⟩ : J1Window T) := Subtype.ext ht
    subst t
    apply Measurable.of_comap_le
    exact le_iSup_of_le _ (le_iSup_of_le hEndpoint le_rfl)
  · have htT : (t : ℝ) < T := lt_of_le_of_ne t.property.2 ht
    obtain ⟨u, huD, hright, hutendsto⟩ :=
      exists_dense_right_sequence D hD t htT
    have hmeas (n : ℕ) : Measurable[cylinder]
        (fun x : J1WindowD T hT => x.path.1 (u n)) := by
      apply Measurable.of_comap_le
      exact le_iSup_of_le (u n) (le_iSup_of_le (huD n) le_rfl)
    have hlim : Tendsto
        (fun n (x : J1WindowD T hT) => x.path.1 (u n)) atTop
        (𝓝 (fun x : J1WindowD T hT => x.path.1 t)) := by
      rw [tendsto_pi_nhds]
      intro x
      have huwithin : Tendsto u atTop (𝓝[Set.Ioi t] t) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutendsto
          (Eventually.of_forall fun n => hright n)
      have hcont : ContinuousWithinAt (fun s => x.path.1 s) (Set.Ioi t) t :=
        x.path.2.isRightContinuous t
      have hpath := hcont.tendsto_nhdsWithin (fun _ _ => Set.mem_univ _)
      have hpath' : Tendsto ((fun s => x.path.1 s) ∘ u) atTop
          (𝓝 (x.path.1 t)) := by
        simpa only [nhdsWithin_univ] using hpath.comp huwithin
      have heq : (fun i => x.path.1 (u i)) = (fun s => x.path.1 s) ∘ u := by
        funext i
        rfl
      rw [heq]
      exact hpath'
    exact @measurable_of_tendsto_metrizable (J1WindowD T hT) ℝ cylinder
      _ _ _ _ (fun n x => x.path.1 (u n)) (fun x => x.path.1 t) hmeas hlim

private theorem isRightContinuous_comp_orderIso {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {f : α → ℝ}
    (hf : IsRightContinuous f) (φ : α ≃o α) :
    IsRightContinuous (fun t => f (φ t)) := by
  intro t
  have himage : φ '' Set.Ioi t = Set.Ioi (φ t) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact φ.strictMono hs
    · intro hy
      refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
      simpa using φ.symm.strictMono hy
  have himage' : φ.toHomeomorph '' Set.Ioi t = Set.Ioi (φ t) := by
    exact himage
  have hmap := φ.toHomeomorph.isEmbedding.map_nhdsWithin_eq (Set.Ioi t) t
  rw [himage'] at hmap
  have hφ : Tendsto φ.toHomeomorph (𝓝[Set.Ioi t] t)
      (𝓝[Set.Ioi (φ t)] (φ t)) := by
    change map φ.toHomeomorph (𝓝[Set.Ioi t] t) ≤ _
    rw [hmap]
    exact le_rfl
  exact (hf (φ t)).tendsto.comp hφ

private theorem j1WindowValueError_isRightContinuous {T : ℝ}
    (f g : CadlagWindow T) (φ : J1TimeChange T) :
    IsRightContinuous (fun t => f.1 (φ t) - g.1 t) := by
  have hf := isRightContinuous_comp_orderIso f.2.isRightContinuous φ
  have hcont : Continuous (Function.uncurry (fun a b : ℝ => a - b)) :=
    continuous_fst.sub continuous_snd
  change IsRightContinuous
    (fun t => (fun a b : ℝ => a - b) (f.1 (φ t)) (g.1 t))
  exact hf.continuous_comp₂ g.2.isRightContinuous hcont





theorem iSup_abs_eq_iSup_dense_right {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) (hD : Dense D)
    (hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ D)
    (f : J1Window T → ℝ) (hf : IsRightContinuous f)
    (hbdd : BddAbove (Set.range fun t : J1Window T => |f t|)) :
    (⨆ t : J1Window T, |f t|) = ⨆ t : D, |f t.val| := by
  let : Nonempty (J1Window T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  let : Nonempty D := ⟨⟨⟨T, hT.le, le_rfl⟩, hEndpoint⟩⟩
  have hbddD : BddAbove (Set.range fun t : D => |f t.val|) := by
    apply hbdd.mono
    rintro _ ⟨t, rfl⟩
    exact ⟨t.val, rfl⟩
  apply le_antisymm
  · apply ciSup_le
    intro t
    by_cases ht : (t : ℝ) = T
    · have heq : t = (⟨T, hT.le, le_rfl⟩ : J1Window T) := Subtype.ext ht
      rw [heq]
      exact le_ciSup_of_le hbddD
        ⟨⟨T, hT.le, le_rfl⟩, hEndpoint⟩ le_rfl
    · have htT : (t : ℝ) < T := lt_of_le_of_ne t.property.2 ht
      obtain ⟨u, huD, hright, hutendsto⟩ :=
        exists_dense_right_sequence D hD t htT
      have huwithin : Tendsto u atTop (𝓝[Set.Ioi t] t) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutendsto
          (Eventually.of_forall fun n => hright n)
      have hlim := (hf t).tendsto_nhdsWithin (fun _ _ => Set.mem_univ _)
      have hlim' : Tendsto (fun n => |f (u n)|) atTop (𝓝 |f t|) := by
        have hval : Tendsto (fun n => f (u n)) atTop (𝓝 (f t)) := by
          change Tendsto (f ∘ u) atTop (𝓝 (f t))
          simpa only [nhdsWithin_univ] using hlim.comp huwithin
        exact (continuous_abs.tendsto (f t)).comp hval
      apply le_of_tendsto' hlim'
      intro n
      exact le_ciSup_of_le hbddD ⟨u n, huD n⟩ le_rfl
  · apply ciSup_le
    intro t
    exact le_ciSup_of_le hbdd t.val le_rfl




theorem measurable_j1WindowValueErrorSup_cylinder {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) (hD : Dense D) (hDcount : D.Countable)
    (hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ D)
    (φ : J1TimeChange T) (y : CadlagWindow T) :
    Measurable[⨆ s ∈ D, MeasurableSpace.comap
      (fun x : J1WindowD T hT => x.path.1 s) (borel ℝ)]
      (fun x : J1WindowD T hT =>
        ⨆ t : J1Window T, |x.path.1 (φ t) - y.1 t|) := by
  let cylinder : MeasurableSpace (J1WindowD T hT) :=
    ⨆ s ∈ D, MeasurableSpace.comap
      (fun x : J1WindowD T hT => x.path.1 s) (borel ℝ)
  have heq : (fun x : J1WindowD T hT =>
      ⨆ t : J1Window T, |x.path.1 (φ t) - y.1 t|) =
      fun x => ⨆ t : D, |x.path.1 (φ t.val) - y.1 t.val| := by
    funext x
    exact iSup_abs_eq_iSup_dense_right hT D hD hEndpoint
      (fun t => x.path.1 (φ t) - y.1 t)
      (j1WindowValueError_isRightContinuous x.path y φ)
      (j1WindowValueError_bddAbove x.path y φ)
  rw [heq]
  let _ : Countable D := hDcount.to_subtype
  apply Measurable.iSup
  intro t
  have heval : Measurable[cylinder] (fun x : J1WindowD T hT =>
      x.path.1 (φ t.val)) :=
    measurable_j1WindowD_eval_cylinder hT D hD hEndpoint (φ t.val)
  have hdiff : Measurable[cylinder] (fun x : J1WindowD T hT =>
      x.path.1 (φ t.val) - y.1 t.val) := heval.sub measurable_const
  simpa only [Real.norm_eq_abs] using hdiff.norm




theorem measurable_j1WindowCost_cylinder {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) (hD : Dense D) (hDcount : D.Countable)
    (hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ D)
    (φ : J1TimeChange T) (g : CadlagWindow T) :
    Measurable[⨆ s ∈ D, MeasurableSpace.comap
      (fun x : J1WindowD T hT => x.path.1 s) (borel ℝ)]
      (fun x : J1WindowD T hT =>
        max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
          (⨆ t : J1Window T, |x.path.1 (φ t) - g.1 t|)) := by
  let cylinder : MeasurableSpace (J1WindowD T hT) :=
    ⨆ s ∈ D, MeasurableSpace.comap
      (fun x : J1WindowD T hT => x.path.1 s) (borel ℝ)
  have hvalue := measurable_j1WindowValueErrorSup_cylinder hT D hD hDcount
    hEndpoint φ g
  have hdist : Measurable[cylinder] (fun _ : J1WindowD T hT =>
      ⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|) := measurable_const
  exact hdist.max hvalue





theorem measure_ext_of_fdd {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) (_hD : Dense D)
    (_hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ D)
    (μ ν : Measure (J1WindowD T hT)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hBorelCylinder : borel (J1WindowD T hT) =
      (MeasurableSpace.pi : MeasurableSpace (D → ℝ)).comap
        (fun x : J1WindowD T hT => fun t : D => x.path.1 t.val))
    (hFDD : ∀ (I : Finset D) (A : Set (∀ _ : I, ℝ)), MeasurableSet A →
      μ ((fun x : J1WindowD T hT => fun t : D => x.path.1 t.val) ⁻¹'
        MeasureTheory.cylinder I A) =
      ν ((fun x : J1WindowD T hT => fun t : D => x.path.1 t.val) ⁻¹'
        MeasureTheory.cylinder I A)) :
    μ = ν := by
  classical
  let eval : J1WindowD T hT → D → ℝ := fun x t => x.path.1 t.val
  let baseCyl := MeasureTheory.measurableCylinders (fun _ : D => ℝ)
  let C : Set (Set (J1WindowD T hT)) :=
    {s | ∃ A ∈ baseCyl, eval ⁻¹' A = s}
  have hpi : IsPiSystem C := by
    exact MeasureTheory.isPiSystem_measurableCylinders.comap eval
  have hC : C = Set.preimage eval '' baseCyl := by
    ext s
    simp [C]
  have hgen : MeasurableSpace.generateFrom C =
      (MeasurableSpace.pi : MeasurableSpace (D → ℝ)).comap eval := by
    rw [hC, ← MeasurableSpace.comap_generateFrom,
      MeasureTheory.generateFrom_measurableCylinders]
  have hsets : ∀ s ∈ C, μ s = ν s := by
    intro s hs
    obtain ⟨A, hA, hEq⟩ := hs
    rw [← hEq]
    obtain ⟨I, B, hB, rfl⟩ :=
      (MeasureTheory.mem_measurableCylinders A).mp hA
    exact hFDD I B hB
  have huniv : μ Set.univ = ν Set.univ := by
    simpa using hFDD (∅ : Finset D) Set.univ MeasurableSet.univ
  exact MeasureTheory.ext_of_generate_finite C
    (hBorelCylinder.trans hgen.symm) hpi hsets huniv




theorem borel_eq_comap_pi_eval {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) (hD : Dense D) (hDcount : D.Countable)
    (hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ D) :
    borel (J1WindowD T hT) =
      (MeasurableSpace.pi : MeasurableSpace (D → ℝ)).comap
        (fun x : J1WindowD T hT => fun t : D => x.path.1 t.val) := by
  classical
  let : Countable D := hDcount.to_subtype
  let eval : J1WindowD T hT → D → ℝ := fun x t => x.path.1 t.val
  have heval_measurable : Measurable eval := by
    apply measurable_pi_iff.mpr
    intro t
    exact measurable_j1WindowD_eval hT t.val
  have heval_injective : Function.Injective eval := by
    intro x y hxy
    let : Nonempty (J1Window T) := ⟨⟨0, le_rfl, hT.le⟩⟩
    let : Nonempty D := ⟨⟨⟨T, hT.le, le_rfl⟩, hEndpoint⟩⟩
    have hbdd := j1WindowValueError_bddAbove x.path y.path (OrderIso.refl _)
    have hbddD : BddAbove (Set.range fun t : D =>
        |x.path.1 t.val - y.path.1 t.val|) := by
      apply hbdd.mono
      rintro _ ⟨t, rfl⟩
      exact ⟨t.val, rfl⟩
    have hsup : (⨆ t : J1Window T, |x.path.1 t - y.path.1 t|) = 0 := by
      rw [iSup_abs_eq_iSup_dense_right hT D hD hEndpoint
        (fun t => x.path.1 t - y.path.1 t)
        (j1WindowValueError_isRightContinuous x.path y.path (OrderIso.refl _))
        hbdd]
      apply le_antisymm
      · apply ciSup_le
        intro t
        have ht := congrFun hxy t
        change x.path.1 t.val = y.path.1 t.val at ht
        simp [ht]
      · let top : J1Window T := ⟨T, hT.le, le_rfl⟩
        have ht := congrFun hxy ⟨top, hEndpoint⟩
        change x.path.1 top = y.path.1 top at ht
        simpa only [ht, sub_self, abs_zero] using
          (le_ciSup_of_le hbddD ⟨top, hEndpoint⟩ (by simp [ht]))
    have hpoint (t : J1Window T) : x.path.1 t = y.path.1 t := by
      have hle : |x.path.1 t - y.path.1 t| ≤ 0 := by
        calc
          |x.path.1 t - y.path.1 t| ≤
              ⨆ s : J1Window T, |x.path.1 s - y.path.1 s| :=
            le_ciSup_of_le hbdd t le_rfl
          _ = 0 := hsup
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
    have hpaths : x.path.1 = y.path.1 := funext hpoint
    have hcadlag : x.path = y.path := Subtype.ext hpaths
    cases x
    cases y
    cases hcadlag
    rfl
  have hembedding : MeasurableEmbedding eval :=
    heval_measurable.measurableEmbedding heval_injective
  exact hembedding.comap_eq.symm




theorem measure_ext_of_fdd' {T : ℝ} (hT : 0 < T)
    (D : Set (J1Window T)) (hD : Dense D) (hDcount : D.Countable)
    (hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ D)
    (μ ν : Measure (J1WindowD T hT)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hFDD : ∀ (I : Finset D) (A : Set (∀ _ : I, ℝ)), MeasurableSet A →
      μ ((fun x : J1WindowD T hT => fun t : D => x.path.1 t.val) ⁻¹'
        MeasureTheory.cylinder I A) =
      ν ((fun x : J1WindowD T hT => fun t : D => x.path.1 t.val) ⁻¹'
        MeasureTheory.cylinder I A)) :
    μ = ν := by
  exact measure_ext_of_fdd hT D hD hEndpoint μ ν
    (borel_eq_comap_pi_eval hT D hD hDcount hEndpoint) hFDD

end DirectedDistances.Probability
