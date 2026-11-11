module

public import DirectedDistances.Probability.SkorokhodJ1WindowCylinder
public import DirectedDistances.Probability.SkorokhodJ1WindowContinuityTimes
public import Mathlib.MeasureTheory.Measure.Prokhorov
import DirectedDistances.Probability.SkorokhodJ1WindowDEval
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Sequences

@[expose] public section
namespace DirectedDistances.Probability

open Filter MeasureTheory Set
open scoped Topology




theorem tendsto_map_of_ae_continuousAt {X Y : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace Y] [TopologicalSpace Y]
    [BorelSpace Y] (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hμ : Tendsto μ atTop (𝓝 ν)) (f : X → Y) (hf : Measurable f)
    (hcont : ∀ᵐ x ∂(ν : Measure X), ContinuousAt f x) :
    Tendsto (fun n => (μ n).map f) atTop (𝓝 (ν.map f)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have heq : (ν : Measure X) (closure (f ⁻¹' F)) = (ν : Measure X) (f ⁻¹' F) := by
    apply measure_congr
    filter_upwards [hcont] with x hx
    apply propext
    constructor
    · intro hcl
      have himage := mem_closure_image hx hcl
      have hsub : f '' (f ⁻¹' F) ⊆ F := image_preimage_subset f F
      exact hF.closure_eq ▸ closure_mono hsub himage
    · intro hx
      exact subset_closure hx
  have hle : (atTop.limsup fun n =>
      ((μ n).map f : Measure Y) F) ≤
      atTop.limsup fun n => (μ n : Measure X) (closure (f ⁻¹' F)) := by
    refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [] with n
    rw [ProbabilityMeasure.map_apply' _ hf.aemeasurable hF.measurableSet]
    exact measure_mono subset_closure
  calc
    _ ≤ _ := hle
    _ ≤ (ν : Measure X) (closure (f ⁻¹' F)) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure
    _ = (ν.map f : Measure Y) F := by
      rw [ProbabilityMeasure.map_apply' _ hf.aemeasurable hF.measurableSet]
      exact heq




def windowEvalVec {T : ℝ} {hT : 0 < T} {ι : Type*}
    (t : ι → J1Window T) (x : J1WindowD T hT) : ι → ℝ :=
  fun i => x.path.1 (t i)




theorem measurable_windowEvalVec {T : ℝ} {hT : 0 < T} {ι : Type*}
    (t : ι → J1Window T) : Measurable (windowEvalVec (hT := hT) t) := by
  exact measurable_pi_iff.mpr fun i => measurable_j1WindowD_eval hT (t i)





theorem tendsto_map_windowEvalVec {T : ℝ} {hT : 0 < T} {ι : Type*}
    [Finite ι] (μ : ℕ → ProbabilityMeasure (J1WindowD T hT))
    (ν : ProbabilityMeasure (J1WindowD T hT)) (hμ : Tendsto μ atTop (𝓝 ν))
    (t : ι → J1Window T)
    (ht : ∀ i, (t i : ℝ) < T → t i ∈ continuityTimes (ν : Measure (J1WindowD T hT))) :
    Tendsto (fun n => (μ n).map (windowEvalVec t)) atTop
      (𝓝 (ν.map (windowEvalVec t))) := by
  apply tendsto_map_of_ae_continuousAt μ ν hμ _ (measurable_windowEvalVec t)
  have hi (i : ι) : ∀ᵐ x ∂(ν : Measure (J1WindowD T hT)),
      ContinuousAt (fun y : J1WindowD T hT => y.path.1 (t i)) x := by
    by_cases h : (t i : ℝ) < T
    · filter_upwards [ht i h] with x hx
      exact j1WindowD_eval_continuousAt hT x (t i) hx
    · have heq : t i = (⟨T, hT.le, le_rfl⟩ : J1Window T) :=
        Subtype.ext (le_antisymm (t i).property.2 (not_lt.mp h))
      filter_upwards [] with x
      rw [heq]
      exact j1WindowD_eval_endpoint_continuousAt hT x
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact continuousAt_pi.mpr hx

private theorem dense_of_countable_compl {T : ℝ} (hT : 0 < T)
    (E : Set (J1Window T)) (hE : Eᶜ.Countable) : Dense E := by
  rw [Metric.dense_iff]
  intro x r hr
  let a : ℝ := max 0 ((x : ℝ) - r / 2)
  let b : ℝ := min T ((x : ℝ) + r / 2)
  have hab : a < b := by
    dsimp [a, b]
    exact max_lt (lt_min hT (by linarith [x.property.1]))
      (lt_min (by linarith [x.property.2]) (by linarith))
  let B : Set ℝ := Subtype.val '' Eᶜ
  have hB : B.Countable := hE.image Subtype.val
  have hnot : ¬ Ioo a b ⊆ B := by
    intro hsub
    exact (not_le_of_gt hab) (Cardinal.Real.Ioo_countable_iff.mp (hB.mono hsub))
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hnot
  have hy0 : 0 ≤ y := (le_max_left _ _).trans hy.1.le
  have hyT : y ≤ T := hy.2.le.trans (min_le_left _ _)
  let z : J1Window T := ⟨y, hy0, hyT⟩
  refine ⟨z, ?_, ?_⟩
  · change |y - (x : ℝ)| < r
    have hlo := (le_max_right 0 ((x : ℝ) - r / 2)).trans_lt hy.1
    have hhi := hy.2.trans_le (min_le_right T ((x : ℝ) + r / 2))
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · by_contra hz
    exact hyB ⟨z, hz, rfl⟩




theorem map_windowEvalVec_eq_of_subseq {T : ℝ} {hT : 0 < T}
    (μ : ℕ → ProbabilityMeasure (J1WindowD T hT))
    (μLimit ν : ProbabilityMeasure (J1WindowD T hT))
    (S : Set (J1Window T))
    (hfdd : ∀ (k : ℕ) (t : Fin k → S),
      Tendsto (fun n => (μ n).map (windowEvalVec (fun i => (t i).val))) atTop
        (𝓝 (μLimit.map (windowEvalVec (fun i => (t i).val)))))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (hν : Tendsto (μ ∘ φ) atTop (𝓝 ν)) (k : ℕ) (t : Fin k → S)
    (ht : ∀ i, ((t i).val : ℝ) < T →
      (t i).val ∈ continuityTimes (ν : Measure (J1WindowD T hT))) :
    ν.map (windowEvalVec (fun i => (t i).val)) =
      μLimit.map (windowEvalVec (fun i => (t i).val)) := by
  exact tendsto_nhds_unique
    (tendsto_map_windowEvalVec (μ ∘ φ) ν hν (fun i => (t i).val) ht)
    ((hfdd k t).comp hφ)

private theorem probabilityMeasure_map_map {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : ProbabilityMeasure X) {f : X → Y} {g : Y → Z}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_map hg hf







theorem tendsto_of_tight_of_fdd {T : ℝ} {hT : 0 < T}
    (μ : ℕ → ProbabilityMeasure (J1WindowD T hT))
    (μLimit : ProbabilityMeasure (J1WindowD T hT))
    (htight : IsTightMeasureSet (Set.range fun n => (μ n : Measure (J1WindowD T hT))))
    (S : Set (J1Window T)) (hS : Sᶜ.Countable)
    (hEndpoint : (⟨T, hT.le, le_rfl⟩ : J1Window T) ∈ S)
    (hfdd : ∀ (k : ℕ) (t : Fin k → S),
      Tendsto (fun n => (μ n).map (windowEvalVec (fun i => (t i).val))) atTop
        (𝓝 (μLimit.map (windowEvalVec (fun i => (t i).val))))) :
    Tendsto μ atTop (𝓝 μLimit) := by
  classical
  have htight' : IsTightMeasureSet
      {((p : ProbabilityMeasure (J1WindowD T hT)) : Measure (J1WindowD T hT)) | p ∈ range μ} := by
    convert htight using 1
    ext m
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
  have hcompact := isCompact_closure_of_isTightMeasureSet htight'
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν, _, φ, hφ, hν⟩ := hcompact.tendsto_subseq
    (x := μ ∘ ns) (fun n => subset_closure ⟨ns n, rfl⟩)
  refine ⟨φ, ?_⟩
  suffices hEq : ν = μLimit by
    simpa only [hEq, Function.comp_def] using hν
  let E : Set (J1Window T) := S ∩ continuityTimes (ν : Measure (J1WindowD T hT))
  have hEc : Eᶜ.Countable := by
    rw [show Eᶜ = Sᶜ ∪ (continuityTimes (ν : Measure (J1WindowD T hT)))ᶜ from compl_inter _ _]
    exact hS.union (countable_compl_continuityTimes (ν : Measure (J1WindowD T hT)))
  obtain ⟨D₀, hD₀E, hD₀c, hD₀⟩ :=
    (dense_of_countable_compl hT E hEc).exists_countable_dense_subset
  let endpoint : J1Window T := ⟨T, hT.le, le_rfl⟩
  let D : Set (J1Window T) := insert endpoint D₀
  have hDc : D.Countable := hD₀c.insert endpoint
  have hDd : Dense D := hD₀.mono (subset_insert endpoint D₀)
  have hDe : endpoint ∈ D := mem_insert _ _
  have hDS : D ⊆ S := by
    intro t ht
    rcases ht with rfl | ht
    · exact hEndpoint
    · exact (hD₀E ht).1
  have hDν : ∀ t ∈ D, (t : ℝ) < T → t ∈ continuityTimes (ν : Measure (J1WindowD T hT)) := by
    intro t ht hlt
    rcases ht with rfl | ht
    · exact False.elim ((lt_irrefl T) hlt)
    · exact (hD₀E ht).2
  have hFDD (I : Finset D) :
      ν.map (windowEvalVec (fun i : I => i.val.val)) =
        μLimit.map (windowEvalVec (fun i : I => i.val.val)) := by
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let t : Fin (Fintype.card I) → S := fun j =>
      ⟨(e.symm j).val.val, hDS (e.symm j).val.property⟩
    have hbase := map_windowEvalVec_eq_of_subseq μ μLimit ν S hfdd
      (ns ∘ φ) (hns.comp hφ.tendsto_atTop) hν (Fintype.card I) t
      (fun j hj => hDν _ (e.symm j).val.property hj)
    let r : (Fin (Fintype.card I) → ℝ) → I → ℝ := fun v i => v (e i)
    have hr : Measurable r := measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
    have hh := congrArg (fun p : ProbabilityMeasure (Fin (Fintype.card I) → ℝ) =>
      p.map r) hbase
    rw [probabilityMeasure_map_map _ (measurable_windowEvalVec _) hr,
      probabilityMeasure_map_map _ (measurable_windowEvalVec _) hr] at hh
    have hfun : (r ∘ windowEvalVec (hT := hT) (fun i => (t i).val)) =
        windowEvalVec (hT := hT) (fun i : I => i.val.val) := by
      funext x i
      change x.path.1 ((e.symm (e i)).val.val) = x.path.1 i.val.val
      rw [e.symm_apply_apply]
    rw [hfun] at hh
    exact hh
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_ext_of_fdd' hT D hDd hDc hDe
    (ν : Measure (J1WindowD T hT)) (μLimit : Measure (J1WindowD T hT))
  intro I A hA
  have hh := congrArg (fun p : ProbabilityMeasure (I → ℝ) => (p : Measure (I → ℝ)) A) (hFDD I)
  rw [ProbabilityMeasure.map_apply' _ (measurable_windowEvalVec _).aemeasurable hA,
    ProbabilityMeasure.map_apply' _ (measurable_windowEvalVec _).aemeasurable hA] at hh
  exact hh

end DirectedDistances.Probability
