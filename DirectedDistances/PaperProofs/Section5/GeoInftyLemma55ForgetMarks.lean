/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeometricSideClass
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly6
import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassValued

/-! # Forgetting marks from geometric side classes

Forgetting formalization-internal marks to match the source's submap laws.
unmarked class retains the side's vertices, edges, directed planar structure,
and root, while forgetting only the indexed boundary and seam marks used by
the formalization. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The structural relations retained by an
unmarked side-submap isomorphism; unlike the marked relation, this has no
indexed boundary or seam relations. -/
inductive SideSubmapRelation where
  | vertex
  | root
  | incident
  | opposite
  | oriented
  | rotation
  | faceNext

/-- Helper toward Lemma 5.5. Identify each retained unmarked relation with
its structural tag in the marked geometric-side relation. -/
def SideSubmapRelation.toMarkedTag : SideSubmapRelation → TruncationRelation
  | .vertex => .vertex
  | .root => .root
  | .incident => .incident
  | .opposite => .opposite
  | .oriented => .oriented
  | .rotation => .rotation
  | .faceNext => .faceNext

/-- Helper toward Lemma 5.5. The directed planar submap relations after
forgetting the formalization-internal indexed boundary and seam marks. -/
@[expose] def sideSubmapRelation (M : GeometricSideSubmap) :
    SideSubmapRelation → GeometricSideCell M → GeometricSideCell M → Prop :=
  fun t u v => geometricSideRelation M t.toMarkedTag u v

/-- Helper toward Lemma 5.5. Isomorphism of directed planar side submaps
preserving the source root and every structural relation, with no indexed
boundary or seam marks. -/
structure GeometricSideUnmarkedIso (M N : GeometricSideSubmap) where
  equiv : GeometricSideCell M ≃ GeometricSideCell N
  relation_iff : ∀ t u v,
    sideSubmapRelation M t u v ↔ sideSubmapRelation N t (equiv u) (equiv v)

/-- Helper toward Lemma 5.5. A marked side isomorphism induces an unmarked
isomorphism by retaining its root and structural relation clauses. -/
@[expose] def geometricSideMarkedIsoToUnmarked {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) : GeometricSideUnmarkedIso M N where
  equiv := I.equiv
  relation_iff := by
    intro t u v
    simpa [sideSubmapRelation] using (I.relation_iff t.toMarkedTag u v)

/-- Helper toward Lemma 5.5. Reverse an unmarked side-submap isomorphism. -/
@[expose] def GeometricSideUnmarkedIso.symm {M N : GeometricSideSubmap}
    (I : GeometricSideUnmarkedIso M N) : GeometricSideUnmarkedIso N M where
  equiv := I.equiv.symm
  relation_iff := by
    intro t u v
    simpa using (I.relation_iff t (I.equiv.symm u) (I.equiv.symm v)).symm

/-- Helper toward Lemma 5.5. Compose unmarked side-submap isomorphisms. -/
@[expose] def GeometricSideUnmarkedIso.trans {M N P : GeometricSideSubmap}
    (I : GeometricSideUnmarkedIso M N) (J : GeometricSideUnmarkedIso N P) :
    GeometricSideUnmarkedIso M P where
  equiv := I.equiv.trans J.equiv
  relation_iff := by
    intro t u v
    exact (I.relation_iff t u v).trans (J.relation_iff t (I.equiv u) (I.equiv v))

/-- Helper toward Lemma 5.5. Reflexive unmarked side-submap isomorphism. -/
@[expose] def GeometricSideUnmarkedIso.refl (M : GeometricSideSubmap) :
    GeometricSideUnmarkedIso M M where
  equiv := Equiv.refl _
  relation_iff := by intro t u v; rfl

/-- Helper toward Lemma 5.5. The unmarked side-submap isomorphism relation. -/
@[expose] def sideSubmapSetoid : Setoid GeometricSideSubmap where
  r M N := Nonempty (GeometricSideUnmarkedIso M N)
  iseqv := ⟨
    fun M => ⟨GeometricSideUnmarkedIso.refl M⟩,
    fun h => h.elim fun I => ⟨GeometricSideUnmarkedIso.symm I⟩,
    fun h₁ h₂ => h₁.elim fun I => h₂.elim fun J =>
      ⟨GeometricSideUnmarkedIso.trans I J⟩⟩

/-- Helper toward Lemma 5.5. Classes of directed planar side submaps with
their source root, modulo unmarked isomorphism. -/
@[expose] def SideSubmapClass := Quotient sideSubmapSetoid

/-- Helper toward Lemma 5.5. The unmarked-isomorphism class of a side submap. -/
@[expose] def sideSubmapClass (M : GeometricSideSubmap) : SideSubmapClass :=
  Quotient.mk sideSubmapSetoid M

/-- Helper toward Lemma 5.5. Equality of unmarked classes is exactly existence
of an unmarked directed planar isomorphism preserving the root. -/
theorem sideSubmapClass_eq_iff (M N : GeometricSideSubmap) :
    sideSubmapClass M = sideSubmapClass N ↔
      Nonempty (GeometricSideUnmarkedIso M N) := by
  constructor
  · exact Quotient.exact
  · intro h
    change Quotient.mk sideSubmapSetoid M = Quotient.mk sideSubmapSetoid N
    exact Quotient.sound h

/-- Helper toward Lemma 5.5. The unmarked code records precisely the
structural fields and root, omitting only indexed boundary and seam marks. -/
abbrev SideSubmapCode :=
  (ℕ → Bool) × (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → Bool) ×
    ((ℕ × Bool) → (ℕ × Bool) → Bool) × ((ℕ × Bool) → (ℕ × Bool) → Bool) × ℕ

/-- Helper toward Lemma 5.5. Encode an unmarked side using exactly its
vertices, edges, endpoint maps, present-edge set, rotation, face succession,
and root. -/
@[expose] noncomputable def sideSubmapCode (M : GeometricSideSubmap) : SideSubmapCode :=
  (fun n => decide (n ∈ M.vertices),
   fun n => decide (n ∈ M.edges),
   M.west,
   M.east,
   fun n => decide (n ∈ M.present),
   fun d e => decide (M.rotation d e),
   fun d e => decide (M.faceNext d e),
   M.root)

/-- Helper toward Lemma 5.5. Project the marked code onto the structural
fields and root retained by an unmarked submap. -/
noncomputable def forgetSideCodeMarks (c : GeometricSideCode) : SideSubmapCode :=
  (c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1,
   c.2.2.2.2.2.1, c.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.1)

/-- Helper toward Lemma 5.5. The unmarked code is a measurable projection
of the existing complete geometric-side code. -/
theorem measurable_forgetSideCodeMarks : Measurable forgetSideCodeMarks := by
  unfold forgetSideCodeMarks
  fun_prop

/-- Helper toward Lemma 5.5. The complete side code is measurable by the
comap sigma-algebra on geometric submaps. -/
theorem measurable_geometricSideCode : Measurable geometricSideCode := by
  rw [measurable_iff_comap_le]
  exact le_rfl

/-- Helper toward Lemma 5.5. The unmarked code map is measurable for the
existing geometric-side sigma-algebra. -/
theorem measurable_sideSubmapCode : Measurable sideSubmapCode := by
  have hcode : sideSubmapCode = forgetSideCodeMarks ∘ geometricSideCode := by
    funext M
    rfl
  rw [hcode]
  exact measurable_forgetSideCodeMarks.comp measurable_geometricSideCode

/-- Helper toward Lemma 5.5. The measurable space on unmarked classes is the
quotient sigma-algebra induced by the comap code containing just unmarked
fields. -/
noncomputable instance : MeasurableSpace SideSubmapClass :=
  MeasurableSpace.map sideSubmapClass
    (MeasurableSpace.comap sideSubmapCode
      (inferInstance : MeasurableSpace SideSubmapCode))

/-- Helper toward Lemma 5.5. Forget the internal boundary/seam indexing on a
marked geometric-side class. The source root and planar submap are retained. -/
@[expose] noncomputable def forgetMarks : GeometricSideClass → SideSubmapClass :=
  Quotient.lift sideSubmapClass (by
    intro M N h
    exact h.elim fun I => Quotient.sound ⟨geometricSideMarkedIsoToUnmarked I⟩)

/-- Helper toward Lemma 5.5. Forgetting marks commutes with the quotient class
maps on representatives. -/
theorem forgetMarks_geometricSideClass (M : GeometricSideSubmap) :
    forgetMarks (geometricSideClass M) = sideSubmapClass M := rfl

/-- Helper toward Lemma 5.5. Forgetting marks is measurable between the
quotient sigma-algebras. Its proof uses the two code maps and the marked
class-map measurability theorem. -/
theorem measurable_forgetMarks : Measurable forgetMarks := by
  rw [measurable_iff_le_map]
  change MeasurableSpace.map sideSubmapClass
      (MeasurableSpace.comap sideSubmapCode
        (inferInstance : MeasurableSpace SideSubmapCode)) ≤
    (MeasurableSpace.map geometricSideClass
      (inferInstance : MeasurableSpace GeometricSideSubmap)).map forgetMarks
  rw [MeasurableSpace.map_comp]
  rw [show forgetMarks ∘ geometricSideClass = sideSubmapClass from by
    funext M
    rfl]
  exact MeasurableSpace.map_mono
    (measurable_iff_comap_le.mp measurable_sideSubmapCode)

/-- Helper toward Lemma 5.5. Independence of two marked side classes passes
to their unmarked side-submap classes. -/
theorem indepFun_forgetMarks {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → GeometricSideClass} (h : IndepFun f g μ) :
    IndepFun (forgetMarks ∘ f) (forgetMarks ∘ g) μ :=
  h.comp measurable_forgetMarks measurable_forgetMarks

/-- Helper toward Lemma 5.5. Equality of laws of almost everywhere measurable
marked side classes passes through the measurable forgetful map. -/
theorem map_forgetMarks_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → GeometricSideClass} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (h : μ.map f = μ.map g) :
    μ.map (forgetMarks ∘ f) = μ.map (forgetMarks ∘ g) := by
  calc
    μ.map (forgetMarks ∘ f) = (μ.map f).map forgetMarks :=
      (measurable_forgetMarks.aemeasurable (μ := μ.map f)).map_map_of_aemeasurable hf |>.symm
    _ = (μ.map g).map forgetMarks := congrArg (fun ν : Measure GeometricSideClass =>
      ν.map forgetMarks) h
    _ = μ.map (forgetMarks ∘ g) :=
      (measurable_forgetMarks.aemeasurable (μ := μ.map g)).map_map_of_aemeasurable hg

/-- Helper toward Lemma 5.5. Apply the fixed-default Option class reader and
then forget the internal boundary/seam marks. -/
@[expose] noncomputable def forgetMarksOptionClassValue
    (default : GeometricSideClass) : Option GeometricSideClass → SideSubmapClass :=
  forgetMarks ∘ lemma55OptionClassValue default

/-- Helper toward Lemma 5.5. The Option/default unmarked class reader is
measurable as a composition of the two class readers. -/
theorem measurable_forgetMarksOptionClassValue (default : GeometricSideClass) :
    Measurable (forgetMarksOptionClassValue default) :=
  measurable_forgetMarks.comp (measurable_lemma55OptionClassValue default)

/-- Helper toward Lemma 5.5. Embedding a class-valued observable as `some`,
reading it with the fixed default, and forgetting marks preserves its law. -/
theorem map_some_forgetMarksOptionClassValue {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (default : GeometricSideClass)
    (X : Ω → GeometricSideClass) (hX : AEMeasurable X μ) :
    (μ.map (fun ω => some (X ω))).map (forgetMarksOptionClassValue default) =
      μ.map (forgetMarks ∘ X) := by
  have hsome : AEMeasurable (fun ω => some (X ω)) μ :=
    measurable_some_geometricSideClass.comp_aemeasurable hX
  calc
    (μ.map (fun ω => some (X ω))).map (forgetMarksOptionClassValue default) =
        μ.map (forgetMarksOptionClassValue default ∘ (fun ω => some (X ω))) :=
      (measurable_forgetMarksOptionClassValue default).aemeasurable
        |>.map_map_of_aemeasurable hsome
    _ = μ.map (forgetMarks ∘ X) := by
      apply Measure.map_congr
      filter_upwards [] with ω
      simp [forgetMarksOptionClassValue, lemma55OptionClassValue]

/-- Helper toward Lemma 5.5. The class-valued independence and both
rooted side-submap classes, under exactly Assembly6's four hypotheses. -/
theorem lemma55_unmarked_of_exposedObservables
    (default : GeometricSideClass)
    (hLplusMeas : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      AEMeasurable (LPlusSidePresentation.classOptionAt x k)
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLPlus x k (leftSideObsNonneg x k W))))
    (hLplusEq : ∀ (x : XDP) (k : ℤ) (hk : 0 ≤ k),
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        (LPlusIndexedSidePresentation.classOption x) ∘ (fun W =>
          decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)))
    (hLminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W))))
    (hRminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (RMinusSidePresentation.classOption (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W)))) :
    ∀ (x : XDP) (k : ℤ),
      IndepFun
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k)
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x 0)) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x 0)) := by
  intro x k
  have hassembly := lemma55_classValued_of_exposedObservables default
    hLplusMeas hLplusEq hLminusMeas hRminusMeas x k
  have hLoption : AEMeasurable (lemma55LeftSideClassOption x k)
      wholePlaneIIDCodeMeasure := by
    by_cases hk : 0 ≤ k
    · let obs := fun W => decodeLPlusWithIndex x k hk
        (leftSideObsNonneg x k W)
      have hObs : AEMeasurable obs wholePlaneIIDCodeMeasure :=
        (measurable_decodeLPlusWithIndex x k hk).comp_aemeasurable
          (aemeasurable_leftSideObsNonneg x k)
      have hIndexed := aemeasurable_LPlusIndexedSidePresentation_classOption_of_classOptionAt
        x k hk (hLplusMeas x k hk)
      have hcomp : AEMeasurable
          ((LPlusIndexedSidePresentation.classOption x) ∘ obs)
          wholePlaneIIDCodeMeasure := hIndexed.comp_aemeasurable hObs
      exact hcomp.congr (hLplusEq x k hk).symm
    · have hk' : k ≤ 0 := by omega
      let obs := fun W => decodeLMinus x k (leftSideObsNonpos x k W)
      have hcomp : AEMeasurable
          ((LMinusSidePresentation.classOption4 (x := x)) ∘ obs)
          wholePlaneIIDCodeMeasure :=
        (hLminusMeas x k hk').comp_aemeasurable
          (aemeasurable_decodeLMinus_leftSideObsNonpos x k)
      exact hcomp.congr
        (lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4
          x k hk').symm
  have hRoption : AEMeasurable (lemma55RightSideClassOption2 x k)
      wholePlaneIIDCodeMeasure := by
    by_cases hk : 0 ≤ k
    · exact (aemeasurable_lemma55RightSideClassOption_nonnegative x k hk).congr
        (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption x k hk).symm
    · have hk' : k ≤ 0 := by omega
      let obs := fun W => decodeRMinus x k (rightSideObsNonpos x k W)
      have hcomp : AEMeasurable
          ((RMinusSidePresentation.classOption (x := x)) ∘ obs)
          wholePlaneIIDCodeMeasure :=
        (hRminusMeas x k hk').comp_aemeasurable
          (aemeasurable_decodeRMinus_rightSideObsNonpos x k)
      exact hcomp.congr
        (lemma55RightSideClassOption2_ae_eq_RMinusSidePresentation_classOption
          x k hk').symm
  have hLvalue : AEMeasurable
      (fun W => lemma55OptionClassValue default (lemma55LeftSideClassOption x k W))
      wholePlaneIIDCodeMeasure :=
    (measurable_lemma55OptionClassValue default).comp_aemeasurable hLoption
  have hRvalue : AEMeasurable
      (fun W => lemma55OptionClassValue default
        (lemma55RightSideClassOption2 x k W)) wholePlaneIIDCodeMeasure :=
    (measurable_lemma55OptionClassValue default).comp_aemeasurable hRoption
  refine ⟨?_, ?_, ?_⟩
  · simpa [forgetMarksOptionClassValue, Function.comp_def] using
      indepFun_forgetMarks hassembly.2.2.1
  · intro hk
    have hRzeroOption : AEMeasurable (lemma55RightSideClassOption2 x 0)
        wholePlaneIIDCodeMeasure :=
      (aemeasurable_lemma55RightSideClassOption_nonnegative x 0 (by omega)).congr
        (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption
          x 0 (by omega)).symm
    have hRzero : AEMeasurable
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x 0 W)) wholePlaneIIDCodeMeasure := by
      exact (measurable_lemma55OptionClassValue default).comp_aemeasurable
        hRzeroOption
    simpa [forgetMarksOptionClassValue, Function.comp_def] using
      map_forgetMarks_eq hRvalue hRzero (hassembly.2.2.2.1 hk)
  · intro hk
    have hLzeroOption : AEMeasurable (lemma55LeftSideClassOption x 0)
        wholePlaneIIDCodeMeasure := by
      have hObs : AEMeasurable
          (fun W => decodeLPlusWithIndex x 0 (by omega)
            (leftSideObsNonneg x 0 W)) wholePlaneIIDCodeMeasure :=
        (measurable_decodeLPlusWithIndex x 0 (by omega)).comp_aemeasurable
          (aemeasurable_leftSideObsNonneg x 0)
      have hIndexed := aemeasurable_LPlusIndexedSidePresentation_classOption_of_classOptionAt
        x 0 (by omega) (hLplusMeas x 0 (by omega))
      have hcomp : AEMeasurable
          ((LPlusIndexedSidePresentation.classOption x) ∘
            (fun W => decodeLPlusWithIndex x 0 (by omega)
              (leftSideObsNonneg x 0 W))) wholePlaneIIDCodeMeasure :=
        hIndexed.comp_aemeasurable hObs
      exact hcomp.congr (hLplusEq x 0 (by omega)).symm
    have hLzero : AEMeasurable
        (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x 0 W)) wholePlaneIIDCodeMeasure :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable hLzeroOption
    simpa [forgetMarksOptionClassValue, Function.comp_def] using
      map_forgetMarks_eq hLvalue hLzero (hassembly.2.2.2.2 hk)

end DirectedDistances.PaperProofs.Section5
