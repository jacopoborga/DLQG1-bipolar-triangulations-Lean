/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The local second-countability argument is adapted from Mathlib,
Copyright (c) 2024 Yury Kudryashov, under Apache 2.0.
-/
module

public import DirectedDistances.Probability.PitmanBessel3
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-! Helpers toward Lemma 4.11: continuous-path law determination and the
compact-interval tightness/FDD criterion. These are generic probability lemmas;
no tightness or convergence premise is added to the manuscript result. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Filter Set Function TopologicalSpace
open scoped Topology NNReal

section PathTopology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
open ContinuousMap

private theorem pathCompactOpen_eq_generateFrom {S : Set (Set X)} {T : Set (Set Y)}
    (hS₁ : ∀ K ∈ S, IsCompact K) (hT : IsTopologicalBasis T)
    (hS₂ : ∀ f : C(X, Y), ∀ x, ∀ V ∈ T, f x ∈ V → ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V) :
    compactOpen = .generateFrom (.image2 (fun K t ↦
      {f : C(X, Y) | MapsTo f K (⋃₀ t)}) S {t : Set (Set Y) | t.Finite ∧ t ⊆ T}) := by
  apply le_antisymm
  · apply_rules [generateFrom_anti, image2_subset_iff.mpr]
    intro K hK t ht
    exact mem_image2_of_mem (hS₁ K hK) (isOpen_sUnion fun _ h ↦ hT.isOpen <| ht.2 h)
  · refine le_of_nhds_le_nhds fun f ↦ ?_
    simp only [nhds_compactOpen, le_iInf_iff, le_principal_iff]
    intro K (hK : IsCompact K) U (hU : IsOpen U) hfKU
    simp only [TopologicalSpace.nhds_generateFrom]
    obtain ⟨t, htT, htf, hTU, hKT⟩ : ∃ t ⊆ T, t.Finite ∧ (∀ V ∈ t, V ⊆ U) ∧ f '' K ⊆ ⋃₀ t := by
      rw [hT.open_eq_sUnion' hU, mapsTo_iff_image_subset, sUnion_eq_biUnion] at hfKU
      obtain ⟨t, ht, hfin, htK⟩ :=
        (hK.image (map_continuous f)).elim_finite_subcover_image
          (b := {V | V ∈ T ∧ V ⊆ U}) (fun V hV ↦ hT.isOpen hV.1) hfKU
      replace ht : ∀ V ∈ t, V ∈ T ∧ V ⊆ U := ht
      refine ⟨t, fun _ h ↦ (ht _ h).1, hfin, fun _ h ↦ (ht _ h).2, ?_⟩
      rwa [sUnion_eq_biUnion]
    rw [image_subset_iff] at hKT
    obtain ⟨s, hsS, hsf, hKs, hst⟩ : ∃ s ⊆ S, s.Finite ∧ K ⊆ ⋃₀ s ∧ MapsTo f (⋃₀ s) (⋃₀ t) := by
      have : ∀ x ∈ K, ∃ L ∈ S, L ∈ 𝓝 x ∧ MapsTo f L (⋃₀ t) := by
        intro x hx
        rcases hKT hx with ⟨V, hVt, hxV⟩
        rcases hS₂ f x V (htT hVt) hxV with ⟨L, hLS, hLx, hLV⟩
        exact ⟨L, hLS, hLx, hLV.mono_right <| subset_sUnion_of_mem hVt⟩
      choose! L hLS hLmem hLt using this
      rcases hK.elim_nhds_subcover L hLmem with ⟨s, hsK, hs⟩
      refine ⟨L '' s, image_subset_iff.2 fun x hx ↦ hLS x <| hsK x hx, s.finite_toSet.image _,
        by rwa [sUnion_image], ?_⟩
      rw [mapsTo_sUnion, forall_mem_image]
      exact fun x hx ↦ hLt x <| hsK x hx
    have hsub : (⋂ L ∈ s, {g : C(X, Y) | MapsTo g L (⋃₀ t)}) ⊆ {g | MapsTo g K U} := by
      simp only [← ofPred_forall, ← mapsTo_iUnion, ← sUnion_eq_biUnion]
      exact fun g hg ↦ hg.mono hKs (sUnion_subset hTU)
    refine mem_of_superset ((biInter_mem hsf).2 fun L hL ↦ ?_) hsub
    refine mem_iInf_of_mem _ <| mem_iInf_of_mem ?_ <| mem_principal_self _
    exact ⟨hst.mono_left (subset_sUnion_of_mem hL), mem_image2_of_mem (hsS hL) ⟨htf, htT⟩⟩

private theorem pathSecondCountableTopology [SecondCountableTopology Y]
    (hX : ∃ S : Set (Set X), S.Countable ∧ (∀ K ∈ S, IsCompact K) ∧
      ∀ f : C(X, Y), ∀ V, IsOpen V → ∀ x ∈ f ⁻¹' V, ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V) :
    SecondCountableTopology C(X, Y) where
  is_open_generated_countable := by
    rcases hX with ⟨S, hScount, hScomp, hS⟩
    refine ⟨_, ?_, pathCompactOpen_eq_generateFrom (S := S) hScomp (isBasis_countableBasis _) ?_⟩
    · exact .image2 hScount (countable_ofPred_finite_subset (countable_countableBasis Y)) _
    · intro f x V hV hx
      apply hS
      exacts [isOpen_of_mem_countableBasis hV, hx]

/-- Helper toward Lemma 4.11: continuous paths on a locally compact second-countable
domain have second-countable compact-open topology. This is the pinned Mathlib proof
from `Topology/ContinuousMap/SecondCountableSpace`, whose compiled artifact is absent. -/
theorem continuousPath_secondCountable [SecondCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopology Y] : SecondCountableTopology C(X, Y) := by
  apply pathSecondCountableTopology
  have (U : countableBasis X) : LocallyCompactSpace U.1 :=
    (isOpen_of_mem_countableBasis U.2).locallyCompactSpace
  set K := fun U : countableBasis X ↦ CompactExhaustion.choice U.1
  use ⋃ U : countableBasis X, Set.range fun n ↦ K U n
  refine ⟨countable_iUnion fun _ ↦ countable_range _, ?_, ?_⟩
  · simp only [mem_iUnion, mem_range]
    rintro K ⟨U, n, rfl⟩
    exact ((K U).isCompact _).image continuous_subtype_val
  · intro f V hVo x hxV
    obtain ⟨U, hU, hxU, hUV⟩ : ∃ U ∈ countableBasis X, x ∈ U ∧ U ⊆ f ⁻¹' V := by
      rw [← (isBasis_countableBasis _).mem_nhds_iff]
      exact (hVo.preimage (map_continuous f)).mem_nhds hxV
    lift x to U using hxU
    lift U to countableBasis X using hU
    rcases (K U).exists_mem_nhds x with ⟨n, hn⟩
    refine ⟨K U n, mem_iUnion.2 ⟨U, mem_range_self _⟩, ?_, ?_⟩
    · rw [← map_nhds_subtype_coe_eq_nhds x.2]
      exacts [image_mem_map hn, (isOpen_of_mem_countableBasis U.2).mem_nhds x.2]
    · rw [mapsTo_image_iff]
      exact fun y _ ↦ hUV y.2


end PathTopology

section ContinuousPaths
variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X] [T2Space X]

local instance : MeasurableSpace C(X, ℝ × ℝ) := borel _
local instance : BorelSpace C(X, ℝ × ℝ) := ⟨rfl⟩
local instance : SecondCountableTopology C(X, ℝ × ℝ) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: finite evaluation laws determine a finite measure
on continuous paths over a locally compact, sigma-compact, second-countable
Hausdorff time domain. -/
theorem continuousPath_measure_ext_of_fdd
    (μ ν : Measure C(X, ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfdd : ∀ (k : ℕ) (t : Fin k → X),
      μ.map (fun f i => f (t i)) = ν.map (fun f i => f (t i))) : μ = ν := by
  classical
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  let : Countable D := hDc.to_subtype
  let ev : C(X, ℝ × ℝ) → D → ℝ × ℝ := fun f t => f t
  have hevc : Continuous ev := continuous_pi (fun t => continuous_eval_const t.val)
  have hev : MeasurableEmbedding ev := hevc.measurableEmbedding (by
    intro f g h
    apply DFunLike.ext'
    apply f.continuous.ext_on hDd g.continuous
    intro t ht
    exact congrFun h ⟨t, ht⟩)
  apply hev.map_injective
  have hproj (I : Finset D) :
      (μ.map ev).map I.restrict = (ν.map ev).map I.restrict := by
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let t : Fin (Fintype.card I) → X := fun j => (e.symm j).val.val
    let r : (Fin (Fintype.card I) → ℝ × ℝ) → I → ℝ × ℝ := fun v i => v (e i)
    have hr : Measurable r := measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))
    have h := congrArg (Measure.map r) (hfdd (Fintype.card I) t)
    have hm : Measurable (fun f : C(X, ℝ × ℝ) => fun i => f (t i)) :=
      (continuous_pi (fun i => continuous_eval_const (t i))).measurable
    rw [Measure.map_map hr hm, Measure.map_map hr hm] at h
    have hI : Measurable (I.restrict : (D → ℝ × ℝ) → I → ℝ × ℝ) :=
      measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)
    rw [Measure.map_map hI hev.measurable, Measure.map_map hI hev.measurable]
    have heq : r ∘ (fun f : C(X, ℝ × ℝ) => fun i => f (t i)) = I.restrict ∘ ev := by
      funext f i
      change f (e.symm (e i)).val.val = f i.val.val
      rw [e.symm_apply_apply]
    rw [heq] at h
    exact h
  exact IsProjectiveLimit.unique (P := fun I => (μ.map ev).map I.restrict)
    (fun I => rfl) (fun I => (hproj I).symm)

/-- Helper toward Lemma 4.11: tightness plus all finite-dimensional evaluation
limits implies weak convergence in the compact-open continuous-path space.
This is a generic assembly criterion, not an assertion of walk tightness. -/
theorem continuousPath_tendsto_of_tight_of_fdd
    (μ : ℕ → ProbabilityMeasure C(X, ℝ × ℝ))
    (ν : ProbabilityMeasure C(X, ℝ × ℝ))
    (htight : IsTightMeasureSet (Set.range (fun n => (μ n : Measure C(X, ℝ × ℝ)))))
    (hfdd : ∀ (k : ℕ) (t : Fin k → X),
      Tendsto (fun n => (μ n).map (fun f i => f (t i))) atTop
        (𝓝 (ν.map (fun f i => f (t i))))) :
    Tendsto μ atTop (𝓝 ν) := by
  have htight' : IsTightMeasureSet
      {((p : ProbabilityMeasure C(X, ℝ × ℝ)) : Measure C(X, ℝ × ℝ)) | p ∈ range μ} := by
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
  obtain ⟨ν', _, φ, hφ, hν'⟩ := hcompact.tendsto_subseq
    (x := μ ∘ ns) (fun n => subset_closure ⟨ns n, rfl⟩)
  refine ⟨φ, ?_⟩
  have heq : ν' = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    apply continuousPath_measure_ext_of_fdd
    intro k t
    have hcont : Continuous (fun f : C(X, ℝ × ℝ) => fun i => f (t i)) :=
      continuous_pi (fun i => continuous_eval_const (t i))
    have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      ((μ ∘ ns) ∘ φ) ν' hν' hcont
    have hlimit := (hfdd k t).comp (hns.comp hφ.tendsto_atTop)
    exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hmap hlimit)
  simpa only [heq, Function.comp_def] using hν'

end ContinuousPaths

end DirectedDistances.Probability
