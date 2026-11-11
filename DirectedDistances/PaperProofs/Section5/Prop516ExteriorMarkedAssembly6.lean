/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedAssembly5

/-! Helper toward Proposition 5.16. Convergence of the actual finite geometric
sample laws to the canonical code pushforward. Identifying that pushforward
with Definition 5.8 is the explicit, unadopted F3 boundary. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly6

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.Probability
open Prop516RootExteriorEncoding Prop516ExteriorAssembly4 Prop516ExteriorAssembly5
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Helper toward Proposition 5.16: a total canonical realization in the
common subspace, selected from the already proved measurable existence theorem. -/
@[expose] def canonicalSubspaceClass : (ℤ → Fin 3) → subspace :=
  Classical.choose exists_canonicalClass

/-- Helper toward Proposition 5.16: the selected canonical subspace map
is measurable for the marked local observation topology. -/
theorem measurable_canonicalSubspaceClass :
    letI : TopologicalSpace subspace := localClassTopology observation
    letI : MeasurableSpace subspace := borel subspace
    Measurable canonicalSubspaceClass :=
  (Classical.choose_spec exists_canonicalClass).1

/-- Helper toward Proposition 5.16: exact canonical-class realization and
all marked cylinder identities hold on one common probability-one event. -/
theorem canonicalSubspaceClass_spec :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      (∃ hW : (uibhbotD39CanonicalClass W).isSome,
        (canonicalSubspaceClass W).val = (uibhbotD39CanonicalClass W).get hW) ∧
      ∀ r, observation r (canonicalSubspaceClass W) = rootLift (d39BallClass
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
        (r + 1) (Nat.succ_pos r)) :=
  (Classical.choose_spec exists_canonicalClass).2

/-- Helper toward Proposition 5.16: the total canonical representative as
a geometric class map; this does not name or define the source law. -/
@[expose] def canonicalGeometricClass (W : ℤ → Fin 3) : D39GeomRootedMapClass.{0} :=
  (canonicalSubspaceClass W).val

/-- Helper toward Proposition 5.16: the selected total canonical geometric
class representative is Borel measurable. -/
theorem measurable_canonicalGeometricClass :
    letI : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
    Measurable canonicalGeometricClass := by
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  let : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
  exact measurable_subspace_val.comp measurable_canonicalSubspaceClass

/-- Helper toward Proposition 5.16: the selected total map agrees almost
surely with the exact canonical option class. -/
theorem canonicalGeometricClass_spec :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hW : (uibhbotD39CanonicalClass W).isSome,
        canonicalGeometricClass W = (uibhbotD39CanonicalClass W).get hW :=
  canonicalSubspaceClass_spec.mono fun _ h => h.1

/-- Helper toward Proposition 5.16: every total representative of the
same almost-sure canonical class has the identical code pushforward law. -/
theorem canonicalGeometricClass_map_eq
    (F : (ℤ → Fin 3) → D39GeomRootedMapClass.{0})
    (hF : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hW : (uibhbotD39CanonicalClass W).isSome,
        F W = (uibhbotD39CanonicalClass W).get hW) :
    letI : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
    uibhbotCodeLawRel.map canonicalGeometricClass = uibhbotCodeLawRel.map F := by
  let : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
  apply ProbabilityMeasure.toMeasure_injective
  exact uibhbotCanonical_realization_map_unique _ _ canonicalGeometricClass_spec hF

/-- Helper toward Proposition 5.16: the actual uniform finite exterior
sample laws converge to the explicit canonical code pushforward. All common
subspace, measurability, and cylinder inputs have been discharged. -/
theorem finiteGeometricLaw_tendsto_canonicalCodePushforward
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
    letI : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
    Tendsto (fun k => finiteGeometricLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop
      (𝓝 (uibhbotCodeLawRel.map canonicalGeometricClass)) := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
  let : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  let : BorelSpace subspace := ⟨rfl⟩
  obtain ⟨f, g, hf, hg, hfc, hgc, ht⟩ :=
    exists_geometric_pushforward_convergence A hA ell hadm hlo hhi
  have he (k : ℕ) := finiteGeometricLaw_eq_map (k + 1) (ell k)
    (hadm k).1 (hadm k).2.1 (hadm k).2.2 (f k) (hf k) (hfc k)
  have hlim : (uibhbotCodeLawRel.map g).map Subtype.val =
      uibhbotCodeLawRel.map canonicalGeometricClass := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_subspace_val hg]
    exact uibhbotCanonical_realization_map_unique _ _
      (hgc.mono fun _ h => h.1) canonicalGeometricClass_spec
  simp_rw [← he] at ht
  rwa [hlim] at ht

/-- Helper toward Proposition 5.16: the convergence limit can be expressed
using any measurable total canonical-class representative chosen by ROOT. -/
theorem finiteGeometricLaw_tendsto_realization
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
    letI : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
    ∀ (F : (ℤ → Fin 3) → D39GeomRootedMapClass.{0}) (_hFmeas : Measurable F)
      (_hFcanon : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        ∃ hW : (uibhbotD39CanonicalClass W).isSome,
          F W = (uibhbotD39CanonicalClass W).get hW),
      Tendsto (fun k => finiteGeometricLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop
        (𝓝 (uibhbotCodeLawRel.map F)) := by
  let : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
  let : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
  intro F _ hFcanon
  rw [← canonicalGeometricClass_map_eq F hFcanon]
  exact finiteGeometricLaw_tendsto_canonicalCodePushforward A hA ell hadm hlo hhi

/-- Helper toward Proposition 5.16: the final geometric assembly has only
the Definition 5.8 law identification left explicit. F3 is not adopted by
this conditional transport theorem. -/
theorem finiteGeometricLaw_tendsto_of_definition58_identification
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
    letI : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
    ∀ (definition58GeometricClassLaw : ProbabilityMeasure D39GeomRootedMapClass.{0})
      (_hlaw : definition58GeometricClassLaw = uibhbotCodeLawRel.map canonicalGeometricClass),
      Tendsto (fun k => finiteGeometricLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop
        (𝓝 definition58GeometricClassLaw) := by
  let : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
  let : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
  intro μ hlaw
  rw [hlaw]
  exact finiteGeometricLaw_tendsto_canonicalCodePushforward A hA ell hadm hlo hhi

/- REMAINDER (ROOT decision F3, not asserted or adopted here).
The common subspace and observations are Assembly4.subspace and
Assembly4.observation with Assembly4.hball. The named finite maps above are
actual finite exterior samples, and Assembly5.finiteGeometricLaw_eq_map
identifies their laws with the intermediate assembly. The named canonical
map has the exact option-class realization and simultaneous cylinder laws.

The only source-law identification still required has these full binders:

letI : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
letI : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
(F : (ℤ → Fin 3) → D39GeomRootedMapClass.{0})
(hFmeas : Measurable F)
(hFcanon : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
  ∃ hW : (uibhbotD39CanonicalClass W).isSome,
    F W = (uibhbotD39CanonicalClass W).get hW)
(definition58GeometricClassLaw : ProbabilityMeasure D39GeomRootedMapClass.{0})
⊢ definition58GeometricClassLaw = uibhbotCodeLawRel.map F

ROOT must first give the left side its source interpretation; this is not
true for an arbitrary measure. canonicalGeometricClass_map_eq proves that
the right side is independent of the total representative. No source-law
kernel validation remain with the coordinator; no paper completion claimed. -/

end DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly6
end
