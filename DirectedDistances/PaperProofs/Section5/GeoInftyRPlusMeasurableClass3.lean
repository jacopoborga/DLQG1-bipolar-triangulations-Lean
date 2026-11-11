/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusMeasurableClass
public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusSideMeasurable3
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-! # Descent of the coherent right-side class

Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

Route A uses the countable ranges of the existing finite-half truncations.
The body of the upstream `FiniteThinMap` definition is not exposed, so no
countability instance for that entire abstract type is asserted here. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical ENNReal

local notation "Code" => (ℕ → Option FiniteThinMap)
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The countable values actually produced by the
finite-half truncation at one right-boundary index. -/
noncomputable abbrev RightThinValue (s : ℕ) := Set.range (halfTruncate .right s)

/-- Helper toward Lemma 5.5. Each truncation value has a countable input space. -/
instance (s : ℕ) : Countable (RightThinValue s) :=
  (Set.countable_range (halfTruncate .right s)).to_subtype

/-- Helper toward Lemma 5.5. Absence is an actual finite-half truncation value. -/
def rightThinValueNone (s : ℕ) : RightThinValue s :=
  ⟨none, ⟨none, halfTruncate_none .right s⟩⟩

/-- Helper toward Lemma 5.5. The product of the countable coordinate ranges. -/
noncomputable abbrev RightThinCode := (s : ℕ) → RightThinValue s

/-- Helper toward Lemma 5.5. Forget the range certificates of a truncation code. -/
@[expose] def rightThinCodeVal (c : RightThinCode) : Code := fun s => (c s).1

/-- Helper toward Lemma 5.5. Forgetting the certificates is measurable. -/
theorem measurable_rightThinCodeVal : Measurable rightThinCodeVal :=
  measurable_pi_iff.mpr fun s =>
    measurable_subtype_coe.comp (measurable_pi_apply s)

/-- Helper toward Lemma 5.5. A total coordinate retraction, using only actual
finite-half values and returning the absent value on other coordinates. -/
@[expose] noncomputable def rightThinCodeRetract (c : Code) : RightThinCode :=
  fun s => if h : c s ∈ Set.range (halfTruncate .right s) then ⟨c s, h⟩
    else rightThinValueNone s

/-- Helper toward Lemma 5.5. The coordinate retraction is measurable because
the original coordinate sigma algebra is discrete. -/
theorem measurable_rightThinCodeRetract : Measurable rightThinCodeRetract := by
  apply measurable_pi_iff.mpr
  intro s
  let f (v : Option FiniteThinMap) : RightThinValue s :=
    if h : v ∈ Set.range (halfTruncate .right s) then ⟨v, h⟩ else rightThinValueNone s
  have hf : Measurable f := fun _ _ => trivial
  exact hf.comp (measurable_pi_apply s)

/-- Helper toward Lemma 5.5. Every coordinate certificate survives retraction. -/
theorem rightThinCodeRetract_val (c : RightThinCode) :
    rightThinCodeRetract (rightThinCodeVal c) = c := by
  funext s
  exact dite_eq_left (c s).2

/-- Helper toward Lemma 5.5. Valid coordinate ranges define a measurable
subset of the original code space. -/
theorem measurableSet_range_rightThinCodeVal :
    MeasurableSet (Set.range rightThinCodeVal) := by
  have he : Set.range rightThinCodeVal =
      ⋂ s : ℕ, {c : Code | c s ∈ Set.range (halfTruncate .right s)} := by
    ext c
    constructor
    · rintro ⟨d, rfl⟩
      exact Set.mem_iInter.mpr fun s => (d s).2
    · intro h
      exact ⟨fun s => ⟨c s, Set.mem_iInter.mp h s⟩, rfl⟩
  rw [he]
  exact MeasurableSet.iInter fun s =>
    (show MeasurableSet (Set.range (halfTruncate .right s)) from trivial).preimage
      (measurable_pi_apply s)

/-- Helper toward Lemma 5.5. The product of actual coordinate ranges embeds
measurably in the original code space, including measurable images. -/
theorem measurableEmbedding_rightThinCodeVal : MeasurableEmbedding rightThinCodeVal :=
  MeasurableEmbedding.of_measurable_inverse measurable_rightThinCodeVal
    measurableSet_range_rightThinCodeVal measurable_rightThinCodeRetract
    rightThinCodeRetract_val

/-- Helper toward Lemma 5.5. The actual coordinate product is standard Borel. -/
instance : StandardBorelSpace RightThinCode := by
  infer_instance

/-- Helper toward Lemma 5.5. Each coherent code uses only actual finite-half
truncation values, with the existing least-good-cut realization. -/
@[expose] noncomputable def coherentRightThinCode (x : XDP) (q : Coherent x) :
    RightThinCode := fun s =>
  ⟨thinTruncationAt x renewalTime renewalTime_positiveSuccessTime .right s q,
    ⟨selectedCutSide x renewalTime .right
      (leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q) q.1, rfl⟩⟩

/-- Helper toward Lemma 5.5. Forgetting a coherent coordinate certificate
recovers exactly the existing thin-side code. -/
theorem coherentRightThinCode_val (x : XDP) (q : Coherent x) :
    rightThinCodeVal (coherentRightThinCode x q) =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 := by
  exact (thinSideCode_coe x renewalTime renewalTime_positiveSuccessTime .right q).symm

/-- Helper toward Lemma 5.5. The coherent code in its countable-coordinate
product is measurable. -/
theorem measurable_coherentRightThinCode (x : XDP) :
    Measurable (coherentRightThinCode x) := by
  apply measurable_pi_iff.mpr
  intro s
  exact (measurable_thinTruncationAt x renewalTime
    renewalTime_positiveSuccessTime .right s).subtype_mk

/-- Helper toward Lemma 5.5. The coherent path subtype is standard Borel. -/
instance (x : XDP) : StandardBorelSpace (Coherent x) :=
  (selectedCutCoherentDomain_measurable_conull x renewalTime
    renewalTime_positiveSuccessTime).1.standardBorel

/-- Helper toward Lemma 5.5. The optional class reader is measurable on the
coherent-code range with its inherited sigma algebra. -/
theorem measurable_Psi_restrict_coherentRightThinCode (x : XDP) :
    Measurable ((Set.range (coherentRightThinCode x)).domRestrict
      (fun c => Psi x (rightThinCodeVal c))) := by
  apply (measurable_coherentRightThinCode x).measurable_comp_iff_restrict.mp
  have he : (fun c => Psi x (rightThinCodeVal c)) ∘ coherentRightThinCode x =
      fun q : Coherent x => some (geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) := by
    funext q
    rw [Function.comp_apply, coherentRightThinCode_val, psi_thinSideCode]
  rw [he]
  exact measurable_some_geometricSideClass.comp (measurable_geometricRightSide_class x)

/-- Helper toward Lemma 5.5. A measurable subset of the coherent-code range
has full code law. This uses compact images after a compatible Polish
refinement; it does not assert that the entire range is Borel. -/
theorem exists_measurableSet_coherentRightThinCode_conull (x : XDP) :
    ∃ S : Set RightThinCode, MeasurableSet S ∧
      S ⊆ Set.range (coherentRightThinCode x) ∧
      (((conditionedVectorPathLaw 0 0).comap
        (Subtype.val : (Coherent x) → (ℕ → ℤ × ℤ))).map
          (coherentRightThinCode x)) Sᶜ = 0 := by
  let ν := (conditionedVectorPathLaw 0 0).comap
    (Subtype.val : (Coherent x) → (ℕ → ℤ × ℤ))
  let codePolish := upgradeStandardBorel RightThinCode
  let : TopologicalSpace RightThinCode := codePolish.toTopologicalSpace
  let : BorelSpace RightThinCode := codePolish.toBorelSpace
  let : PolishSpace RightThinCode := codePolish.toPolishSpace
  let pathPolish := upgradeStandardBorel (Coherent x)
  let : TopologicalSpace (Coherent x) := pathPolish.toTopologicalSpace
  let : BorelSpace (Coherent x) := pathPolish.toBorelSpace
  let : PolishSpace (Coherent x) := pathPolish.toPolishSpace
  obtain ⟨t, hle, hcont, hpol⟩ := (measurable_coherentRightThinCode x).exists_continuous
  have hb : (inferInstance : MeasurableSpace (Coherent x)) = @borel _ t := by
    exact pathPolish.toBorelSpace.measurable_eq.trans
      (borel_eq_borel_of_le hpol pathPolish.toPolishSpace hle).symm
  let : TopologicalSpace (Coherent x) := t
  let : PolishSpace (Coherent x) := hpol
  let : BorelSpace (Coherent x) := ⟨hb⟩
  have hcompact (n : ℕ) : ∃ K : Set (Coherent x), IsCompact K ∧ ν Kᶜ < (n : ℝ≥0∞)⁻¹ := by
    obtain ⟨K, hK, hc, hm⟩ :=
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Coherent x))).exists_isCompact_sdiff_lt
        (μ := ν) (ε := (n : ℝ≥0∞)⁻¹) (measure_ne_top ν _) (by simp)
    exact ⟨K, hc, by simpa only [← Set.compl_eq_univ_sdiff] using hm⟩
  choose K hK hνK using hcompact
  let S : Set RightThinCode := ⋃ n : ℕ, coherentRightThinCode x '' K n
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion fun n => ((hK n).image hcont).measurableSet
  refine ⟨S, hS, ?_, ?_⟩
  · exact Set.iUnion_subset fun n => Set.image_subset_range _ _
  · change (ν.map (coherentRightThinCode x)) Sᶜ = 0
    rw [Measure.map_apply (measurable_coherentRightThinCode x) hS.compl]
    by_contra hn
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hn
    have hsub : coherentRightThinCode x ⁻¹' Sᶜ ⊆ (K n)ᶜ := by
      intro q hq hqK
      exact hq (Set.mem_iUnion.mpr ⟨n, ⟨q, hqK, rfl⟩⟩)
    exact (not_lt_of_ge (measure_mono hsub)) ((hνK n).trans hn)

/-- Helper toward Lemma 5.5. The exact optional class reader is almost
everywhere measurable for the conditioned right-side code law. No global
measurability or measurable-range premise is needed. -/
theorem aemeasurable_Psi_thinSideCode_law (x : XDP) :
    AEMeasurable (Psi x) ((conditionedVectorPathLaw 0 0).map
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right)) := by
  obtain ⟨S, hS, hsub, hnull⟩ := exists_measurableSet_coherentRightThinCode_conull x
  let ν := (conditionedVectorPathLaw 0 0).comap
    (Subtype.val : (Coherent x) → (ℕ → ℤ × ℤ))
  have hD := selectedCutCoherentDomain_measurable_conull x renewalTime
    renewalTime_positiveSuccessTime
  have hmap : (ν.map (coherentRightThinCode x)).map rightThinCodeVal =
      (conditionedVectorPathLaw 0 0).map
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right) := by
    rw [Measure.map_map measurable_rightThinCodeVal (measurable_coherentRightThinCode x)]
    have he : rightThinCodeVal ∘ coherentRightThinCode x =
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right ∘
          (Subtype.val : (Coherent x) → (ℕ → ℤ × ℤ)) := by
      funext q
      exact coherentRightThinCode_val x q
    rw [he, ← Measure.map_map
      (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right)
      measurable_subtype_coe]
    have hν : ν.map Subtype.val = conditionedVectorPathLaw 0 0 := by
      rw [map_comap_subtype_coe hD.1]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hD.2)
    rw [hν]
  let g (c : S) : Option GeometricSideClass := Psi x (rightThinCodeVal c.1)
  have hg : Measurable g :=
    (measurable_Psi_restrict_coherentRightThinCode x).comp
      (measurable_subtype_coe.subtype_mk (h := fun c : S => hsub c.2))
  let G (c : RightThinCode) : Option GeometricSideClass :=
    if hc : c ∈ S then g ⟨c, hc⟩ else none
  have hG : Measurable G := hg.dite measurable_const hS
  have himage : MeasurableSet (rightThinCodeVal '' S) :=
    measurableEmbedding_rightThinCodeVal.measurableSet_image' hS
  have hfull : ((conditionedVectorPathLaw 0 0).map
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right))
        (rightThinCodeVal '' S)ᶜ = 0 := by
    rw [← hmap, Measure.map_apply measurable_rightThinCodeVal himage.compl,
      Set.preimage_compl,
      Set.preimage_image_eq S measurableEmbedding_rightThinCodeVal.injective]
    exact hnull
  refine ⟨G ∘ rightThinCodeRetract, hG.comp measurable_rightThinCodeRetract, ?_⟩
  filter_upwards [ae_iff.mpr hfull] with c hc
  obtain ⟨d, hd, rfl⟩ := hc
  change Psi x (rightThinCodeVal d) = G (rightThinCodeRetract (rightThinCodeVal d))
  rw [rightThinCodeRetract_val]
  change g ⟨d, hd⟩ = (if hc : d ∈ S then g ⟨d, hc⟩ else none)
  rw [dite_eq_left hd]

/-- Helper toward Lemma 5.5. The exact optional class reader is almost
everywhere measurable for the law of every nonnegative-layout right-code
observation, at any boundary index. -/
theorem aemeasurable_Psi_rightSideObsNonneg_law (x : XDP) (k : ℤ) :
    AEMeasurable (Psi x)
      (wholePlaneIIDCodeMeasure.map (rightSideObsNonneg x k)) := by
  have he : rightSideObsNonneg x k =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right ∘
        boundaryFutureHattedPath k := by
    funext W
    exact rightSideObsNonneg_eq_thinSideCode x k W
  rw [he, ← AEMeasurable.map_map_of_aemeasurable
    (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right).aemeasurable
    (aemeasurable_boundaryFutureHattedPath k), boundaryFutureHattedPath_map_law k]
  exact aemeasurable_Psi_thinSideCode_law x
































end DirectedDistances.PaperProofs.Section5
