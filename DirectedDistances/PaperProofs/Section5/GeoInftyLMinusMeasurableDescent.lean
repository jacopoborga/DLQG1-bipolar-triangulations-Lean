/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusCanonicalCodingMeasurable3
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-! Descent of measurable readers to finite observation laws and its application
to the complete nonpositive left-side presentation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical ENNReal

/-- Helper toward Lemma 5.5. A measurable map between standard Borel spaces
has a measurable subset of its range of full pushforward finite measure. -/
theorem exists_measurableSet_conull_subset_range
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [StandardBorelSpace Z]
    (ν : Measure X) [IsFiniteMeasure ν] {f : X → Z} (hf : Measurable f) :
    ∃ S : Set Z, MeasurableSet S ∧ S ⊆ Set.range f ∧ (ν.map f) Sᶜ = 0 := by
  let zPolish := upgradeStandardBorel Z
  let : TopologicalSpace Z := zPolish.toTopologicalSpace
  let : BorelSpace Z := zPolish.toBorelSpace
  let : PolishSpace Z := zPolish.toPolishSpace
  let xPolish := upgradeStandardBorel X
  let : TopologicalSpace X := xPolish.toTopologicalSpace
  let : BorelSpace X := xPolish.toBorelSpace
  let : PolishSpace X := xPolish.toPolishSpace
  obtain ⟨t, hle, hcont, hpol⟩ := hf.exists_continuous
  have hb : (inferInstance : MeasurableSpace X) = @borel _ t :=
    xPolish.toBorelSpace.measurable_eq.trans
      (borel_eq_borel_of_le hpol xPolish.toPolishSpace hle).symm
  let : TopologicalSpace X := t
  let : PolishSpace X := hpol
  let : BorelSpace X := ⟨hb⟩
  have hcompact (n : ℕ) : ∃ K : Set X, IsCompact K ∧ ν Kᶜ < (n : ℝ≥0∞)⁻¹ := by
    obtain ⟨K, _, hc, hm⟩ :=
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set X)).exists_isCompact_sdiff_lt
        (μ := ν) (ε := (n : ℝ≥0∞)⁻¹) (measure_ne_top ν _) (by simp)
    exact ⟨K, hc, by simpa only [← Set.compl_eq_univ_sdiff] using hm⟩
  choose K hK hνK using hcompact
  let S : Set Z := ⋃ n : ℕ, f '' K n
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion fun n => ((hK n).image hcont).measurableSet
  refine ⟨S, hS, Set.iUnion_subset (fun n => Set.image_subset_range _ _), ?_⟩
  rw [Measure.map_apply hf hS.compl]
  by_contra hn
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hn
  have hsub : f ⁻¹' Sᶜ ⊆ (K n)ᶜ := by
    intro q hq hqK
    exact hq (Set.mem_iUnion.mpr ⟨n, ⟨q, hqK, rfl⟩⟩)
  exact (not_lt_of_ge (measure_mono hsub)) ((hνK n).trans hn)

/-- Helper toward Lemma 5.5. Measurability of a reader composed with a
measurable observation descends to almost everywhere measurability for its law. -/
theorem aemeasurable_map_of_measurable_comp
    {X Z β : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [StandardBorelSpace Z] [MeasurableSpace β]
    (ν : Measure X) [IsFiniteMeasure ν] {f : X → Z} {g : Z → β}
    (hf : Measurable f) (hgf : Measurable (g ∘ f)) :
    AEMeasurable g (ν.map f) := by
  cases isEmpty_or_nonempty β with
  | inl h => exact (measurable_of_empty_codomain g).aemeasurable
  | inr h =>
    obtain ⟨S, hS, hsub, hnull⟩ := exists_measurableSet_conull_subset_range ν hf
    let gS (z : S) := g z.val
    have hgS : Measurable gS :=
      (hf.measurable_comp_iff_restrict.mp hgf).comp
        (measurable_subtype_coe.subtype_mk (h := fun z : S => hsub z.property))
    let G (z : Z) := if hz : z ∈ S then gS ⟨z, hz⟩ else Classical.choice h
    refine ⟨G, hgS.dite measurable_const hS, ?_⟩
    filter_upwards [ae_iff.mpr hnull] with z hz
    change g z = if hz : z ∈ S then gS ⟨z, hz⟩ else Classical.choice h
    rw [dite_eq_left hz]

/-- Helper toward Lemma 5.5. The same descent holds when the observation
and the composed reader are only almost everywhere measurable. -/
theorem aemeasurable_map_of_aemeasurable_comp
    {X Z β : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [StandardBorelSpace Z] [MeasurableSpace β]
    (ν : Measure X) [IsFiniteMeasure ν] {f : X → Z} {g : Z → β}
    (hf : AEMeasurable f ν) (hgf : AEMeasurable (g ∘ f) ν) :
    AEMeasurable g (ν.map f) := by
  obtain ⟨S, hfull, hS, hgood⟩ :=
    (hf.ae_eq_mk.and hgf.ae_eq_mk).exists_measurable_mem
  let : StandardBorelSpace S := hS.standardBorel
  let νS := ν.comap (Subtype.val : S → X)
  have hfS : Measurable (fun z : S => f z.val) := by
    have he : (fun z : S => f z.val) = fun z : S => hf.mk f z.val :=
      funext fun z => (hgood z.val z.property).1
    rw [he]
    exact hf.measurable_mk.comp measurable_subtype_coe
  have hgfS : Measurable (g ∘ (fun z : S => f z.val)) := by
    have he : (g ∘ (fun z : S => f z.val)) =
        fun z : S => hgf.mk (g ∘ f) z.val :=
      funext fun z => (hgood z.val z.property).2
    rw [he]
    exact hgf.measurable_mk.comp measurable_subtype_coe
  have hdesc := aemeasurable_map_of_measurable_comp νS hfS hgfS
  have hmap : νS.map (fun z : S => f z.val) = ν.map f := by
    change νS.map (f ∘ Subtype.val) = ν.map f
    have hν : νS.map (Subtype.val : S → X) = ν := by
      rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hfull]
    have hf' : AEMeasurable f (νS.map (Subtype.val : S → X)) := by rwa [hν]
    rw [← AEMeasurable.map_map_of_aemeasurable hf'
      measurable_subtype_coe.aemeasurable, hν]
  rwa [hmap] at hdesc

/-- Helper toward Lemma 5.5. The actual values of one left truncation coordinate. -/
noncomputable abbrev LeftThinValue (i : ℕ) := Set.range (halfTruncate .left i)

/-- Helper toward Lemma 5.5. Left coordinate ranges are countable. -/
instance (i : ℕ) : Countable (LeftThinValue i) :=
  (Set.countable_range (halfTruncate .left i)).to_subtype

/-- Helper toward Lemma 5.5. The absent value belongs to every left coordinate range. -/
def leftThinValueNone (i : ℕ) : LeftThinValue i :=
  ⟨none, ⟨none, halfTruncate_none .left i⟩⟩

/-- Helper toward Lemma 5.5. The product of actual left truncation ranges. -/
noncomputable abbrev LeftThinCode := (i : ℕ) → LeftThinValue i

/-- Helper toward Lemma 5.5. Forget the left coordinate certificates. -/
@[expose] def leftThinCodeVal (c : LeftThinCode) : ℕ → Option FiniteThinMap :=
  fun i => (c i).val

/-- Helper toward Lemma 5.5. Forgetting the coordinate certificates is measurable. -/
theorem measurable_leftThinCodeVal : Measurable leftThinCodeVal :=
  measurable_pi_iff.mpr fun i =>
    measurable_subtype_coe.comp (measurable_pi_apply i)

/-- Helper toward Lemma 5.5. Retract arbitrary coordinates to their actual ranges. -/
@[expose] noncomputable def leftThinCodeRetract
    (c : ℕ → Option FiniteThinMap) : LeftThinCode :=
  fun i => if h : c i ∈ Set.range (halfTruncate .left i) then ⟨c i, h⟩
    else leftThinValueNone i

/-- Helper toward Lemma 5.5. The coordinate retraction is measurable for the
discrete coordinate sigma algebras. -/
theorem measurable_leftThinCodeRetract : Measurable leftThinCodeRetract := by
  apply measurable_pi_iff.mpr
  intro i
  let f (v : Option FiniteThinMap) : LeftThinValue i :=
    if h : v ∈ Set.range (halfTruncate .left i) then ⟨v, h⟩ else leftThinValueNone i
  have hf : Measurable f := fun _ _ => trivial
  exact hf.comp (measurable_pi_apply i)

/-- Helper toward Lemma 5.5. Retraction preserves every certified coordinate. -/
theorem leftThinCodeRetract_val (c : LeftThinCode) :
    leftThinCodeRetract (leftThinCodeVal c) = c := by
  funext i
  exact dite_eq_left (c i).property

/-- Helper toward Lemma 5.5. Retain the complete primed block and the
countable ranges of all hatted left coordinates. -/
noncomputable abbrev LMinusThinPresentation := (ℕ → Fin 3) × LeftThinCode

/-- Helper toward Lemma 5.5. The complete certified presentation is standard Borel. -/
instance : StandardBorelSpace LMinusThinPresentation := by infer_instance

/-- Helper toward Lemma 5.5. Embed the certified presentation in the original space. -/
@[expose] def lMinusThinPresentationVal (x : XDP)
    (c : LMinusThinPresentation) : LMinusSidePresentation x :=
  decodeLMinus x 0 (c.1, leftThinCodeVal c.2)

/-- Helper toward Lemma 5.5. The complete presentation embedding is measurable. -/
theorem measurable_lMinusThinPresentationVal (x : XDP) :
    Measurable (lMinusThinPresentationVal x) :=
  (measurable_decodeLMinus x 0).comp
    (measurable_fst.prodMk (measurable_leftThinCodeVal.comp measurable_snd))

/-- Helper toward Lemma 5.5. A measurable retraction retains the entire
primed block and retracts only the hatted coordinate ranges. -/
@[expose] noncomputable def lMinusThinPresentationRetract (x : XDP)
    (r : LMinusSidePresentation x) : LMinusThinPresentation :=
  (r.code.1, leftThinCodeRetract r.code.2)

/-- Helper toward Lemma 5.5. The complete presentation retraction is measurable. -/
theorem measurable_lMinusThinPresentationRetract (x : XDP) :
    Measurable (lMinusThinPresentationRetract x) :=
  (measurable_lMinusSidePresentation_code x).fst.prodMk
    (measurable_leftThinCodeRetract.comp (measurable_lMinusSidePresentation_code x).snd)

/-- Helper toward Lemma 5.5. Retraction is inverse on certified presentations. -/
theorem lMinusThinPresentationRetract_val (x : XDP) (c : LMinusThinPresentation) :
    lMinusThinPresentationRetract x (lMinusThinPresentationVal x c) = c := by
  exact Prod.ext rfl (leftThinCodeRetract_val c.2)

/-- Helper toward Lemma 5.5. The embedding range is exactly the existing
simultaneously certified coordinate domain. -/
theorem range_lMinusThinPresentationVal (x : XDP) :
    Set.range (lMinusThinPresentationVal x) = lMinusCertifiedPresentationDomain x := by
  ext r
  constructor
  · rintro ⟨c, rfl⟩
    exact fun i => (c.2 i).property
  · intro h
    refine ⟨(r.code.1, fun i => ⟨r.code.2 i, h i⟩), ?_⟩
    exact LMinusSidePresentation.decode_code r 0

/-- Helper toward Lemma 5.5. The complete embedding has a measurable range. -/
theorem measurableSet_range_lMinusThinPresentationVal (x : XDP) :
    MeasurableSet (Set.range (lMinusThinPresentationVal x)) := by
  rw [range_lMinusThinPresentationVal]
  exact measurableSet_lMinusCertifiedPresentationDomain x

/-- Helper toward Lemma 5.5. Certified complete presentations embed measurably,
including measurable images, in the original presentation space. -/
theorem measurableEmbedding_lMinusThinPresentationVal (x : XDP) :
    MeasurableEmbedding (lMinusThinPresentationVal x) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_lMinusThinPresentationVal x)
    (measurableSet_range_lMinusThinPresentationVal x)
    (measurable_lMinusThinPresentationRetract x) (lMinusThinPresentationRetract_val x)

/-- Helper toward Lemma 5.5. The exact complete nonpositive left-side class
reader is almost everywhere measurable for the decoded observation law. -/
theorem aemeasurable_LMinusSidePresentation_classOption4
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeLMinus x k (leftSideObsNonpos x k W))) := by
  obtain ⟨S, hS, hfull, hrange, hobs, hclass⟩ :=
    exists_measurable_lMinusSourceDomain x k hk
  let : StandardBorelSpace S := hS.standardBorel
  let obs (W : ℤ → Fin 3) := decodeLMinus x k (leftSideObsNonpos x k W)
  let νS := wholePlaneIIDCodeMeasure.comap
    (Subtype.val : S → (ℤ → Fin 3))
  let f (W : S) : LMinusThinPresentation :=
    ((obs W.val).code.1,
      fun i => ⟨(obs W.val).code.2 i, hrange W.val W.property i⟩)
  have hf : Measurable f := by
    apply Measurable.prodMk
    · exact (measurable_lMinusSidePresentation_code x).fst.comp hobs
    · apply measurable_pi_iff.mpr
      intro i
      exact (((measurable_pi_apply i).comp
        (measurable_lMinusSidePresentation_code x).snd).comp hobs).subtype_mk
  have hval (W : S) : lMinusThinPresentationVal x (f W) = obs W.val :=
    LMinusSidePresentation.decode_code (obs W.val) 0
  let g (c : LMinusThinPresentation) :=
    (lMinusThinPresentationVal x c).classOption4
  have hgf : Measurable (g ∘ f) := by
    have he : g ∘ f = fun W : S => (obs W.val).classOption4 :=
      funext fun W => congrArg LMinusSidePresentation.classOption4 (hval W)
    rw [he]
    exact hclass
  have hdesc : AEMeasurable g (νS.map f) :=
    aemeasurable_map_of_measurable_comp νS hf hgf
  have hreader : AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
      ((νS.map f).map (lMinusThinPresentationVal x)) :=
    (measurableEmbedding_lMinusThinPresentationVal x).aemeasurable_map_iff.mpr hdesc
  have hν : νS.map (Subtype.val : S → (ℤ → Fin 3)) = wholePlaneIIDCodeMeasure := by
    rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hfull]
  have hobs' : AEMeasurable obs (νS.map (Subtype.val : S → (ℤ → Fin 3))) := by
    rw [hν]
    exact aemeasurable_decodeLMinus_leftSideObsNonpos x k
  have hmap : (νS.map f).map (lMinusThinPresentationVal x) =
      wholePlaneIIDCodeMeasure.map obs := by
    rw [Measure.map_map (measurable_lMinusThinPresentationVal x) hf]
    have he : lMinusThinPresentationVal x ∘ f =
        obs ∘ (Subtype.val : S → (ℤ → Fin 3)) := funext hval
    rw [he, ← AEMeasurable.map_map_of_aemeasurable hobs'
      measurable_subtype_coe.aemeasurable, hν]
  rw [hmap] at hreader
  exact hreader

end DirectedDistances.PaperProofs.Section5

