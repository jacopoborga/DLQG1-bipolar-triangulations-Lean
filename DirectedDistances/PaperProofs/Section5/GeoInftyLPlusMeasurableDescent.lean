/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusMeasurableDescent
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly8

/-! Certified countable-coordinate presentations and descent for the corrected -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Retain both complete code blocks and the
actual countable ranges of the hatted left truncations. -/
noncomputable abbrev LPlusThinPresentation :=
  (ℕ → Fin 3) × LeftThinCode × (ℕ → Fin 3)

/-- Helper toward Lemma 5.5. The certified product is standard Borel. -/
instance : StandardBorelSpace LPlusThinPresentation := by infer_instance

/-- Helper toward Lemma 5.5. Forget only the hatted range certificates. -/
@[expose] def lPlusThinPresentationVal (x : XDP)
    (c : LPlusThinPresentation) : LPlusSidePresentation x :=
  decodeLPlus x 0 (c.1, leftThinCodeVal c.2.1, c.2.2)

/-- Helper toward Lemma 5.5. The complete presentation embedding is measurable. -/
theorem measurable_lPlusThinPresentationVal (x : XDP) :
    Measurable (lPlusThinPresentationVal x) :=
  (measurable_decodeLPlus x 0).comp
    (measurable_fst.prodMk
      ((measurable_leftThinCodeVal.comp measurable_snd.fst).prodMk measurable_snd.snd))

/-- Helper toward Lemma 5.5. Retract only the hatted coordinates, preserving
the entire stopped prefix and primed block. -/
@[expose] noncomputable def lPlusThinPresentationRetract (x : XDP)
    (r : LPlusSidePresentation x) : LPlusThinPresentation :=
  (r.code.1, leftThinCodeRetract r.code.2.1, r.code.2.2)

/-- Helper toward Lemma 5.5. The complete retraction is measurable. -/
theorem measurable_lPlusThinPresentationRetract (x : XDP) :
    Measurable (lPlusThinPresentationRetract x) :=
  (measurable_lPlusSidePresentation_code x).fst.prodMk
    ((measurable_leftThinCodeRetract.comp
      (measurable_lPlusSidePresentation_code x).snd.fst).prodMk
      (measurable_lPlusSidePresentation_code x).snd.snd)

/-- Helper toward Lemma 5.5. Retraction is inverse on certified presentations. -/
theorem lPlusThinPresentationRetract_val (x : XDP) (c : LPlusThinPresentation) :
    lPlusThinPresentationRetract x (lPlusThinPresentationVal x c) = c :=
  Prod.ext rfl (Prod.ext (leftThinCodeRetract_val c.2.1) rfl)

/-- Helper toward Lemma 5.5. Certify all hatted coordinate ranges simultaneously. -/
@[expose] def lPlusCertifiedPresentationDomain (x : XDP) :
    Set (LPlusSidePresentation x) :=
  {r | ∀ i : ℕ, r.code.2.1 i ∈ Set.range (halfTruncate .left i)}

/-- Helper toward Lemma 5.5. The simultaneous range domain is measurable. -/
theorem measurableSet_lPlusCertifiedPresentationDomain (x : XDP) :
    MeasurableSet (lPlusCertifiedPresentationDomain x) := by
  unfold lPlusCertifiedPresentationDomain
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (show MeasurableSet (Set.range (halfTruncate .left i)) from trivial).preimage
      ((measurable_pi_apply i).comp (measurable_lPlusSidePresentation_code x).snd.fst))

/-- Helper toward Lemma 5.5. The embedding range is exactly the certified domain. -/
theorem range_lPlusThinPresentationVal (x : XDP) :
    Set.range (lPlusThinPresentationVal x) = lPlusCertifiedPresentationDomain x := by
  ext r
  constructor
  · rintro ⟨c, rfl⟩
    exact fun i => (c.2.1 i).property
  · intro h
    refine ⟨(r.code.1, (fun i => ⟨r.code.2.1 i, h i⟩), r.code.2.2), ?_⟩
    exact LPlusSidePresentation.decode_code r 0

/-- Helper toward Lemma 5.5. The embedding has measurable range. -/
theorem measurableSet_range_lPlusThinPresentationVal (x : XDP) :
    MeasurableSet (Set.range (lPlusThinPresentationVal x)) := by
  rw [range_lPlusThinPresentationVal]
  exact measurableSet_lPlusCertifiedPresentationDomain x

/-- Helper toward Lemma 5.5. Certified complete presentations embed measurably. -/
theorem measurableEmbedding_lPlusThinPresentationVal (x : XDP) :
    MeasurableEmbedding (lPlusThinPresentationVal x) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_lPlusThinPresentationVal x)
    (measurableSet_range_lPlusThinPresentationVal x)
    (measurable_lPlusThinPresentationRetract x) (lPlusThinPresentationRetract_val x)

/-- Helper toward Lemma 5.5. The retraction also recovers every presentation
in its certified domain. -/
theorem lPlusThinPresentationVal_retract (x : XDP) (r : LPlusSidePresentation x)
    (hr : r ∈ lPlusCertifiedPresentationDomain x) :
    lPlusThinPresentationVal x (lPlusThinPresentationRetract x r) = r := by
  obtain ⟨c, rfl⟩ := (range_lPlusThinPresentationVal x).symm ▸ hr
  rw [lPlusThinPresentationRetract_val]

/-- Helper toward Lemma 5.5. Every observed hatted coordinate belongs to
its actual truncation range, on one common probability-one event. -/
theorem ae_decodeLPlus_leftSideObsNonneg_hatted_mem_range (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ i : ℕ,
      (decodeLPlus x k (leftSideObsNonneg x k W)).code.2.1 i ∈
        Set.range (halfTruncate .left i) := by
  filter_upwards [(boundaryFutureThinSides_package x k).2.2.2.2.2] with W hW
  intro i
  change thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
    (boundaryFutureHattedPath k W) i ∈ Set.range (halfTruncate .left i)
  rw [thinSideCode_coe x renewalTime renewalTime_positiveSuccessTime .left
    ⟨boundaryFutureHattedPath k W, hW⟩]
  exact ⟨selectedCutSide x renewalTime .left
    (leastGoodCut x renewalTime renewalTime_positiveSuccessTime i
      ⟨boundaryFutureHattedPath k W, hW⟩) (boundaryFutureHattedPath k W), rfl⟩

/-- Helper toward Lemma 5.5. The decoded observation belongs almost surely
to the measurable embedding range; no range hypothesis is assumed. -/
theorem ae_decodeLPlus_leftSideObsNonneg_mem_range (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      decodeLPlus x k (leftSideObsNonneg x k W) ∈
        Set.range (lPlusThinPresentationVal x) := by
  rw [range_lPlusThinPresentationVal]
  exact ae_decodeLPlus_leftSideObsNonneg_hatted_mem_range x k

/-- Helper toward Lemma 5.5. The presentation law is concentrated on the
measurable embedding range of the standard Borel product. -/
theorem ae_lPlusSidePresentation_mem_range (x : XDP) (k : ℤ) :
    ∀ᵐ r ∂(wholePlaneIIDCodeMeasure.map
      (fun W => decodeLPlus x k (leftSideObsNonneg x k W))),
      r ∈ Set.range (lPlusThinPresentationVal x) :=
  (ae_map_iff (aemeasurable_decodeLPlus_leftSideObsNonneg x k)
    (measurableSet_range_lPlusThinPresentationVal x)).mpr
      (ae_decodeLPlus_leftSideObsNonneg_mem_range x k)

/-- Helper toward Lemma 5.5. Almost-everywhere measurability of the exact
corrected reader composed with the observation descends to its observation
law. The only measurability premise concerns the source composition. -/
theorem aemeasurable_LPlusSidePresentation_classOptionAt4_of_comp
    (x : XDP) (k : ℤ) (_hk : 0 ≤ k)
    (hcomp : AEMeasurable
      ((LPlusSidePresentation.classOptionAt4 x k) ∘
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W)))
      wholePlaneIIDCodeMeasure) :
    AEMeasurable (LPlusSidePresentation.classOptionAt4 x k)
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W))) := by
  let obs (W : ℤ → Fin 3) := decodeLPlus x k (leftSideObsNonneg x k W)
  let f := lPlusThinPresentationRetract x ∘ obs
  let g := (LPlusSidePresentation.classOptionAt4 x k) ∘ lPlusThinPresentationVal x
  have hf : AEMeasurable f wholePlaneIIDCodeMeasure :=
    (measurable_lPlusThinPresentationRetract x).comp_aemeasurable
      (aemeasurable_decodeLPlus_leftSideObsNonneg x k)
  have he : lPlusThinPresentationVal x ∘ f =ᵐ[wholePlaneIIDCodeMeasure] obs := by
    filter_upwards [ae_decodeLPlus_leftSideObsNonneg_hatted_mem_range x k] with W hW
    exact lPlusThinPresentationVal_retract x (obs W) hW
  have hgf : AEMeasurable (g ∘ f) wholePlaneIIDCodeMeasure :=
    hcomp.congr (he.symm.fun_comp (LPlusSidePresentation.classOptionAt4 x k))
  have hdesc : AEMeasurable g (wholePlaneIIDCodeMeasure.map f) :=
    aemeasurable_map_of_aemeasurable_comp wholePlaneIIDCodeMeasure hf hgf
  have hreader : AEMeasurable (LPlusSidePresentation.classOptionAt4 x k)
      ((wholePlaneIIDCodeMeasure.map f).map (lPlusThinPresentationVal x)) :=
    (measurableEmbedding_lPlusThinPresentationVal x).aemeasurable_map_iff.mpr hdesc
  have hmap : (wholePlaneIIDCodeMeasure.map f).map (lPlusThinPresentationVal x) =
      wholePlaneIIDCodeMeasure.map obs := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_lPlusThinPresentationVal x).aemeasurable hf]
    exact Measure.map_congr he
  rwa [hmap] at hreader

/-- Helper toward Lemma 5.5. The exact fixed-index actual-side identity,
together with measurability of that actual side, discharges the fixed-index
`hLplusMeas4` obligation of Assembly 7. -/
theorem aemeasurable_LPlusSidePresentation_classOptionAt4_of_actual
    (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (hLplusEq4 : lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      (LPlusSidePresentation.classOptionAt4 x k) ∘
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W)))
    (hactual : AEMeasurable (lemma55LeftSideClassOption x k)
      wholePlaneIIDCodeMeasure) :
    AEMeasurable (LPlusSidePresentation.classOptionAt4 x k)
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W))) :=
  aemeasurable_LPlusSidePresentation_classOptionAt4_of_comp x k hk
    (hactual.congr hLplusEq4)

/-- Helper toward Lemma 5.5. The endpoint of the nonnegative actual-side
measurability target follows unconditionally from the proved L-minus model. -/
theorem aemeasurable_lemma55LeftSideClassOption_zero (x : XDP) :
    AEMeasurable (lemma55LeftSideClassOption x 0) wholePlaneIIDCodeMeasure := by
  have hm := (aemeasurable_LMinusSidePresentation_classOption4 x 0 (le_refl 0)).comp_aemeasurable
    (aemeasurable_decodeLMinus_leftSideObsNonpos x 0)
  exact hm.congr
    (lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4
      x 0 (le_refl 0)).symm




































































end DirectedDistances.PaperProofs.Section5

/- eighteen named definitions and theorems above compiled with exit 0. Every
probe reported exactly [propext, Classical.choice, Quot.sound]; no custom
axiom or sorryAx occurred. Temporary #check probes elaborated both exact
conditional descent statements and the unconditional zero endpoint.
Development compile exits: 0, 0, 0, 1, 0. The single failure was a newline
after a field-notation dot in the zero-endpoint proof; it was repaired.
All probes were removed before the final production compile. Only the -/
