/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusMeasurableClass3
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55NonnegPresentationIndependence
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55NonposPresentationIndependence
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable6
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable6
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusSideMeasurable5

/-! These optional class readers use the existing presentation realizations.
This file does not claim the geometric-side class maps are a.e. measurable. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Read the class of an existing optional
geometric-side realization, preserving absence. -/
@[expose] def optionalGeometricSideClass
    (M : Option GeometricSideSubmap) : Option GeometricSideClass :=
  M.map geometricSideClass

/-- Helper toward Lemma 5.5. Passing to a marked-isomorphism class preserves
exactly the domain of an optional realization. -/
theorem optionalGeometricSideClass_eq_none_iff
    (M : Option GeometricSideSubmap) :
    optionalGeometricSideClass M = none ↔ M = none := by
  simp [optionalGeometricSideClass]

/-- Helper toward Lemma 5.5. The nonpositive right presentation's optional
class reader uses its existing whole-side realization. -/
@[expose] noncomputable def RMinusSidePresentation.classOption
    {x : DirectedDistances.PlanarMap.XDP} (r : RMinusSidePresentation x) :
    Option GeometricSideClass :=
  optionalGeometricSideClass r.wholeRealization

/-- Helper toward Lemma 5.5. The R-minus class reader returns the class of
the existing decoded side under its realization guards. -/
theorem RMinusSidePresentation.classOption_eq_some
    {x : DirectedDistances.PlanarMap.XDP} (r : RMinusSidePresentation x)
    (hk : r.boundaryIndex ≤ 0) (hp : r.prefixValid)
    (hq : ∃ q : selectedCutCoherentDomain x renewalTime
      renewalTime_positiveSuccessTime,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
        r.code.2) :
    r.classOption = some (geometricSideClass
      (rMinusDecodedSide r.code.1 hp.choose hq.choose)) := by
  simp only [RMinusSidePresentation.classOption, optionalGeometricSideClass]
  rw [RMinusSidePresentation.wholeRealization_eq_some_rMinusDecodedSide r hk hp hq]
  rfl

/-- Helper toward Lemma 5.5. The R-minus class reader is absent exactly when
the existing whole-side realization is absent. -/
theorem RMinusSidePresentation.classOption_eq_none_iff
    {x : DirectedDistances.PlanarMap.XDP} (r : RMinusSidePresentation x) :
    r.classOption = none ↔ r.wholeRealization = none := by
  exact optionalGeometricSideClass_eq_none_iff r.wholeRealization

/-- Helper toward Lemma 5.5. A realized pair of R-minus blocks gives the
existing complete glued-side realization whenever the stored index is
nonpositive. -/
theorem RMinusSidePresentation.wholeRealization_isSome_of_blocks
    {x : DirectedDistances.PlanarMap.XDP} (r : RMinusSidePresentation x)
    (hk : r.boundaryIndex ≤ 0) (hb : r.blocksRealization.isSome) :
    r.wholeRealization.isSome := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hb
  cases b with
  | mk F M =>
    have hb := (r.blocksRealization_eq_some_iff F M).mp hb
    obtain ⟨n, hn, hpad, hF⟩ := r.prefixRealization_eq_some_spec F hb.1
    have hp : r.prefixValid := ⟨n, hn, hpad⟩
    obtain ⟨q, hcode, hside⟩ := r.hattedRealization_eq_some_spec M hb.2
    unfold RMinusSidePresentation.wholeRealization
    rw [dite_eq_left hk, dite_eq_left hp, dite_eq_left ⟨q, hcode⟩]
    exact Option.isSome_some

/-- Helper toward Lemma 5.5. The observed complete R-minus realization
exists almost surely at every nonpositive index, using the existing theorem
that both code blocks are realized almost surely. -/
theorem ae_decodeRMinus_rightSideObsNonpos_wholeRealization_isSome
    (x : DirectedDistances.PlanarMap.XDP) (k : ℤ) (hk : k ≤ 0) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (decodeRMinus x k (rightSideObsNonpos x k W)).wholeRealization.isSome := by
  filter_upwards [ae_decodeRMinus_rightSideObsNonpos_blocksRealization_isSome x k]
    with W hb
  exact RMinusSidePresentation.wholeRealization_isSome_of_blocks
    (decodeRMinus x k (rightSideObsNonpos x k W))
    (by rw [decodeRMinus_boundaryIndex]; exact hk) hb

/-- Helper toward Lemma 5.5. The nonpositive R-minus class reader is present
almost surely under every observed presentation law. -/
theorem ae_decodeRMinus_rightSideObsNonpos_classOption_isSome
    (x : DirectedDistances.PlanarMap.XDP) (k : ℤ) (hk : k ≤ 0) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (RMinusSidePresentation.classOption (x := x)
        (decodeRMinus x k (rightSideObsNonpos x k W))).isSome := by
  filter_upwards [ae_decodeRMinus_rightSideObsNonpos_wholeRealization_isSome x k hk]
    with W h
  simpa [RMinusSidePresentation.classOption, optionalGeometricSideClass] using h

/-- Helper toward Lemma 5.5. Presence is a measurable event in the optional
geometric-side class sigma algebra. -/
theorem measurableSet_optionGeometricSideClass_isSome :
    MeasurableSet {c : Option GeometricSideClass | c.isSome} := by
  have hset : {c : Option GeometricSideClass | c.isSome} = ({none} : Set _)ᶜ := by
    ext c
    cases c <;> simp
  rw [hset]
  exact measurableSet_optionGeometricSideClass_none.compl

/-- Helper toward Lemma 5.5. The nonnegative left presentation's optional
class reader uses its existing whole-side realization. The boundary index is
an explicit argument because the current presentation type does not store it. -/
@[expose] noncomputable def LPlusSidePresentation.classOptionAt
    (x : DirectedDistances.PlanarMap.XDP) (k : ℤ)
    (r : LPlusSidePresentation x) : Option GeometricSideClass :=
  optionalGeometricSideClass (lPlusSidePresentationRealization x k r)

/-- Helper toward Lemma 5.5. The L-plus class reader returns the class of
the existing decoded side under its source-witness and index guards. -/
theorem LPlusSidePresentation.classOptionAt_eq_some
    (x : DirectedDistances.PlanarMap.XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (hk : 0 ≤ k)
    (hw : Nonempty (LPlusSidePresentationSourceWitness x k r)) :
    LPlusSidePresentation.classOptionAt x k r = some (geometricSideClass
      (lPlusCodeBlockSide (W := (Classical.choice hw).W)
        (h := (Classical.choice hw).h) (k := k)
        (H := (Classical.choice hw).H) (hLL := (Classical.choice hw).hLL)
        (longest := (Classical.choice hw).longest) (Classical.choice hw).hτ
        (Classical.choice hw).hp (Classical.choice hw).P
        (Classical.choice hw).hqMode (Classical.choice hw).Tpath
        (Classical.choice hw).hfin (Classical.choice hw).hleft hk)) := by
  simp only [LPlusSidePresentation.classOptionAt, optionalGeometricSideClass]
  rw [lPlusSidePresentationRealization_eq_some_lPlusCodeBlockSide x k r hk hw]
  rfl

/-- Helper toward Lemma 5.5. The index-specific L-plus class reader is absent
exactly outside its existing index and source-witness realization guards. -/
theorem LPlusSidePresentation.classOptionAt_eq_none_iff
    (x : DirectedDistances.PlanarMap.XDP) (k : ℤ)
    (r : LPlusSidePresentation x) :
    LPlusSidePresentation.classOptionAt x k r = none ↔
      ¬ 0 ≤ k ∨ ¬ Nonempty (LPlusSidePresentationSourceWitness x k r) := by
  classical
  by_cases hk : 0 ≤ k
  · by_cases hw : Nonempty (LPlusSidePresentationSourceWitness x k r)
    · simp [LPlusSidePresentation.classOptionAt, optionalGeometricSideClass,
        lPlusSidePresentationRealization, hk, hw]
    · simp [LPlusSidePresentation.classOptionAt, optionalGeometricSideClass,
        lPlusSidePresentationRealization, hk, hw]
  · simp [LPlusSidePresentation.classOptionAt, optionalGeometricSideClass,
      lPlusSidePresentationRealization, hk]

/-- Helper toward Lemma 5.5. The nonpositive left presentation's optional
class reader uses its existing whole-side realization. -/
@[expose] noncomputable def LMinusSidePresentation.classOption
    {x : DirectedDistances.PlanarMap.XDP} (r : LMinusSidePresentation x) :
    Option GeometricSideClass :=
  optionalGeometricSideClass r.wholeRealization

/-- Helper toward Lemma 5.5. The L-minus class reader returns the class of
the existing decoded side whenever a source-valid preimage exists. -/
theorem LMinusSidePresentation.classOption_eq_some
    {x : DirectedDistances.PlanarMap.XDP} (r : LMinusSidePresentation x)
    (hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code) :
    r.classOption = some (geometricSideClass
      (lMinusDecodedSide (W := hq.choose.W) (h := hq.choose.h)
        (k := hq.choose.k) (longest := hq.choose.longest)
        hq.choose.hτ hq.choose.hqMode hq.choose.hfin)) := by
  simp only [LMinusSidePresentation.classOption, optionalGeometricSideClass]
  rw [LMinusSidePresentation.wholeRealization_eq_some_lMinusDecodedSide r hq]
  rfl

/-- Helper toward Lemma 5.5. The L-minus class reader is absent exactly when
the presentation has no source-valid preimage. -/
theorem LMinusSidePresentation.classOption_eq_none_iff
    {x : DirectedDistances.PlanarMap.XDP} (r : LMinusSidePresentation x) :
    r.classOption = none ↔ ¬ ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code := by
  classical
  simp [LMinusSidePresentation.classOption, optionalGeometricSideClass,
    LMinusSidePresentation.wholeRealization]

/-- Helper toward Lemma 5.5. An option-valued reader is a.e. measurable when
it is measurable on a measurable subset of full measure. This generic form
lets a presentation reader be replaced by any corrected fixed function on
the presentation without changing the measure argument. -/
theorem aemeasurable_of_measurable_on_conull
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S : Set α} (hS : MeasurableSet S) (hfull : μ Sᶜ = 0)
    (f : α → Option GeometricSideClass)
    (hf : Measurable ((S.domRestrict f))) :
    AEMeasurable f μ := by
  let F (a : α) : Option GeometricSideClass :=
    if ha : a ∈ S then f a else none
  have hF : Measurable F := hf.dite measurable_const hS
  refine ⟨F, hF, ?_⟩
  filter_upwards [ae_iff.mpr hfull] with a ha
  simp only [F, dite_eq_left ha]

/-- Helper toward Lemma 5.5. Apply the conull-restriction extension directly
to a presentation law that is the pushforward of the source measure. This
lemma depends only on the fixed presentation reader and a measurable conull
restriction, so it also applies to a corrected L-minus decoded side. -/
theorem aemeasurable_of_measurable_on_conull_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (obs : α → β) (S : Set β)
    (hS : MeasurableSet S) (hfull : (μ.map obs) Sᶜ = 0)
    (f : β → Option GeometricSideClass)
    (hf : Measurable (S.domRestrict f)) :
    AEMeasurable f (μ.map obs) :=
  aemeasurable_of_measurable_on_conull hS hfull f hf























































end DirectedDistances.PaperProofs.Section5
