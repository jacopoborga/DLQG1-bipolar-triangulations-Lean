/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusMeasurableDescent
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE3
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55RightObservable

/-! Measurable descent for the nonpositive R-minus presentation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical ENNReal

/-- Helper toward Lemma 5.5. Retain the complete finite prefix and certify
that each hatted coordinate is an actual right half-truncation value. -/
noncomputable abbrev RMinusThinPresentation := (ℕ → Fin 3) × RightThinCode

/-- Helper toward Lemma 5.5. Embed a certified R-minus code at its fixed
boundary index into the original presentation. -/
@[expose] def rMinusThinPresentationVal (x : XDP) (k : ℤ)
    (c : RMinusThinPresentation) : RMinusSidePresentation x :=
  decodeRMinus x k (c.1, rightThinCodeVal c.2)

/-- Helper toward Lemma 5.5. The certified R-minus presentation is standard
Borel. -/
instance : StandardBorelSpace RMinusThinPresentation := by
  infer_instance

/-- Helper toward Lemma 5.5. The R-minus presentation embedding is measurable. -/
theorem measurable_rMinusThinPresentationVal (x : XDP) (k : ℤ) :
    Measurable (rMinusThinPresentationVal x k) :=
  (measurable_decodeRMinus x k).comp
    (measurable_fst.prodMk
      (measurable_rightThinCodeVal.comp measurable_snd))

/-- Helper toward Lemma 5.5. Retract arbitrary hatted coordinates to their
actual truncation ranges, retaining the full prefix. -/
@[expose] noncomputable def rMinusThinPresentationRetract (x : XDP)
    (r : RMinusSidePresentation x) : RMinusThinPresentation :=
  (r.code.1, rightThinCodeRetract r.code.2)

/-- Helper toward Lemma 5.5. The R-minus presentation retraction is measurable. -/
theorem measurable_rMinusThinPresentationRetract (x : XDP) :
    Measurable (rMinusThinPresentationRetract x) := by
  let hcoords := measurable_rMinusSidePresentation_coordinates x
  have hcode : Measurable (fun r : RMinusSidePresentation x => r.code) :=
    measurable_snd.comp hcoords
  exact (measurable_fst.comp hcode).prodMk
    (measurable_rightThinCodeRetract.comp (measurable_snd.comp hcode))

/-- Helper toward Lemma 5.5. Retraction is inverse on every certified
R-minus presentation. -/
theorem rMinusThinPresentationRetract_val (x : XDP) (k : ℤ)
    (c : RMinusThinPresentation) :
    rMinusThinPresentationRetract x (rMinusThinPresentationVal x k c) = c := by
  exact Prod.ext rfl (rightThinCodeRetract_val c.2)

/-- Helper toward Lemma 5.5. The embedding range consists exactly of
presentations at index `k` with certified hatted coordinates. -/
theorem range_rMinusThinPresentationVal (x : XDP) (k : ℤ) :
    Set.range (rMinusThinPresentationVal x k) =
      {r : RMinusSidePresentation x | r.boundaryIndex = k ∧
        ∀ i, r.code.2 i ∈ Set.range (halfTruncate .right i)} := by
  ext r
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨rfl, fun i => (c.2 i).property⟩
  · intro h
    rcases r with ⟨b, p, c⟩
    change b = k ∧ ∀ i, c i ∈ Set.range (halfTruncate .right i) at h
    rcases h with ⟨hb, hc⟩
    refine ⟨(p, fun i => ⟨c i, hc i⟩), ?_⟩
    change decodeRMinus x k (p, c) = ⟨b, (p, c)⟩
    simp only [decodeRMinus]
    cases hb
    rfl

/-- Helper toward Lemma 5.5. The range of the certified R-minus
presentation embedding is measurable. -/
theorem measurableSet_range_rMinusThinPresentationVal (x : XDP) (k : ℤ) :
    MeasurableSet (Set.range (rMinusThinPresentationVal x k)) := by
  rw [range_rMinusThinPresentationVal]
  let hcoords := measurable_rMinusSidePresentation_coordinates x
  have hb : Measurable (fun r : RMinusSidePresentation x => r.boundaryIndex) :=
    measurable_fst.comp hcoords
  have hcode : Measurable (fun r : RMinusSidePresentation x => r.code) :=
    measurable_snd.comp hcoords
  have hhat : Measurable (fun r : RMinusSidePresentation x => r.code.2) :=
    measurable_snd.comp hcode
  have h1 : MeasurableSet {r : RMinusSidePresentation x | r.boundaryIndex = k} :=
    (MeasurableSet.singleton k).preimage hb
  have h2 : MeasurableSet {r : RMinusSidePresentation x |
      ∀ i, r.code.2 i ∈ Set.range (halfTruncate .right i)} := by
    have he : {r : RMinusSidePresentation x |
        ∀ i, r.code.2 i ∈ Set.range (halfTruncate .right i)} =
        ⋂ i : ℕ, {r : RMinusSidePresentation x |
          r.code.2 i ∈ Set.range (halfTruncate .right i)} := by
      ext r
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [he]
    exact MeasurableSet.iInter fun i =>
      (show MeasurableSet (Set.range (halfTruncate .right i)) from trivial).preimage
        ((measurable_pi_apply i).comp hhat)
  simpa only [Set.ofPred_and] using h1.inter h2

/-- Helper toward Lemma 5.5. The certified R-minus presentation embeds
measurably, with its complete coordinate-range domain. -/
theorem measurableEmbedding_rMinusThinPresentationVal (x : XDP) (k : ℤ) :
    MeasurableEmbedding (rMinusThinPresentationVal x k) :=
  MeasurableEmbedding.of_measurable_inverse
    (measurable_rMinusThinPresentationVal x k)
    (measurableSet_range_rMinusThinPresentationVal x k)
    (measurable_rMinusThinPresentationRetract x)
    (rMinusThinPresentationRetract_val x k)

/-- Helper toward Lemma 5.5. A.e. measurability of the decoded R-minus
class reader on the source implies a.e. measurability under its observation
law. The coordinate-range condition is supplied by the existing a.s.
hatted-realization theorem. -/
theorem aemeasurable_RMinusSidePresentation_classOption_of_source
    (x : XDP) (k : ℤ)
    (hsrc : AEMeasurable
      (fun W => (decodeRMinus x k (rightSideObsNonpos x k W)).classOption)
      wholePlaneIIDCodeMeasure)
    (hk : k ≤ 0) :
    AEMeasurable (RMinusSidePresentation.classOption (x := x))
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeRMinus x k (rightSideObsNonpos x k W))) := by
  let obs : (ℤ → Fin 3) → RMinusSidePresentation x :=
    fun W => decodeRMinus x k (rightSideObsNonpos x k W)
  let thinObs : (ℤ → Fin 3) → RMinusThinPresentation :=
    rMinusThinPresentationRetract x ∘ obs
  let g : RMinusSidePresentation x → Option GeometricSideClass :=
    RMinusSidePresentation.classOption
  have hobs : AEMeasurable obs wholePlaneIIDCodeMeasure := by
    exact aemeasurable_decodeRMinus_rightSideObsNonpos x k
  have hthin : AEMeasurable thinObs wholePlaneIIDCodeMeasure := by
    exact (measurable_rMinusThinPresentationRetract x).comp_aemeasurable hobs
  have hrange : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      obs W ∈ Set.range (rMinusThinPresentationVal x k) := by
    filter_upwards [ae_decodeRMinus_rightSideObsNonpos_hattedRealization_isSome x k]
      with W hW
    let r := obs W
    obtain ⟨q, hcode, _⟩ := r.hattedRealization_eq_some_spec
      (r.hattedRealization.get hW) (Option.some_get hW).symm
    have hcoord (i : ℕ) : r.code.2 i ∈ Set.range (halfTruncate .right i) := by
      have hi : (coherentRightThinCode x q i).val = r.code.2 i := by
        change rightThinCodeVal (coherentRightThinCode x q) i = _
        rw [coherentRightThinCode_val x q, hcode]
      rw [← hi]
      exact (coherentRightThinCode x q i).property
    rw [range_rMinusThinPresentationVal]
    refine ⟨?_, hcoord⟩
    simp [obs, decodeRMinus]
  have hval : (fun W => rMinusThinPresentationVal x k (thinObs W)) =ᵐ[
      wholePlaneIIDCodeMeasure] obs := by
    filter_upwards [hrange] with W hW
    change rMinusThinPresentationVal x k
        (rMinusThinPresentationRetract x (obs W)) = obs W
    rcases hW with ⟨c, hc⟩
    rw [← hc, rMinusThinPresentationRetract_val]
  have hgf : AEMeasurable
      (fun W => g (rMinusThinPresentationVal x k (thinObs W)))
      wholePlaneIIDCodeMeasure := by
    have heq : (fun W => g (obs W)) =ᵐ[wholePlaneIIDCodeMeasure]
        (fun W => g (rMinusThinPresentationVal x k (thinObs W))) := by
      exact (hval.fun_comp g).symm
    exact hsrc.congr heq
  have hdesc : AEMeasurable (fun c => g (rMinusThinPresentationVal x k c))
      (wholePlaneIIDCodeMeasure.map thinObs) :=
    aemeasurable_map_of_aemeasurable_comp wholePlaneIIDCodeMeasure hthin hgf
  have hreader : AEMeasurable g
      ((wholePlaneIIDCodeMeasure.map thinObs).map (rMinusThinPresentationVal x k)) :=
    (measurableEmbedding_rMinusThinPresentationVal x k).aemeasurable_map_iff.mpr hdesc
  have hmap : (wholePlaneIIDCodeMeasure.map thinObs).map
        (rMinusThinPresentationVal x k) =
      wholePlaneIIDCodeMeasure.map obs := by
    calc
      (wholePlaneIIDCodeMeasure.map thinObs).map (rMinusThinPresentationVal x k) =
          wholePlaneIIDCodeMeasure.map (rMinusThinPresentationVal x k ∘ thinObs) :=
        AEMeasurable.map_map_of_aemeasurable
          (measurable_rMinusThinPresentationVal x k).aemeasurable hthin
      _ = wholePlaneIIDCodeMeasure.map obs := Measure.map_congr hval
  rw [hmap] at hreader
  exact hreader

/-- Helper toward Lemma 5.5. A.e. measurability of the source observable
transfers through the proved a.e. identity with the R-minus presentation
reader. -/
theorem aemeasurable_RMinusSidePresentation_classOption_of_lemma55RightSideClassOption2
    (x : XDP) (k : ℤ)
    (hsrc : AEMeasurable (lemma55RightSideClassOption2 x k)
      wholePlaneIIDCodeMeasure)
    (hk : k ≤ 0) :
    AEMeasurable (RMinusSidePresentation.classOption (x := x))
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeRMinus x k (rightSideObsNonpos x k W))) := by
  have hcomp : AEMeasurable
      (fun W => (decodeRMinus x k (rightSideObsNonpos x k W)).classOption)
      wholePlaneIIDCodeMeasure :=
    hsrc.congr
      (lemma55RightSideClassOption2_ae_eq_RMinusSidePresentation_classOption x k hk)
  exact aemeasurable_RMinusSidePresentation_classOption_of_source x k hcomp hk

end DirectedDistances.PaperProofs.Section5
