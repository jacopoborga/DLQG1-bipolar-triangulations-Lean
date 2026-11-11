/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516Definition58ClassWellDefined
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedAssembly6

/-! Supporting lemmas for paper labels `def-uihbot`, `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/

/-! Helper toward Proposition 5.16. The source law is the law of the geometric
class of the Definition 5.8 assembly, defined only almost surely. A measurable
total representative is chosen after proving existence; its off-event values -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open Prop516ExteriorAssembly5 Prop516ExteriorAssembly6
open MeasureTheory Set Filter
open scoped Classical Topology

/-- Helper toward Proposition 5.16: use the geometric Borel sigma algebra. -/
local instance prop516SourceGeometricLawBorel :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}

/-- Helper toward Proposition 5.16: the geometric sigma algebra is Borel. -/
local instance prop516SourceGeometricLawBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 5.16: there exists a Borel measurable class
map agreeing, on one conull event, with every Definition 5.8 witness assembly.
We quantify over all compatible assembly data, hence in particular over every
full witness set of `def_uihbot`; the additional boundary enumeration and face
conclusions do not change the assembly or its ordered missing root. -/
theorem exists_measurable_uibhbotSourceGeometricClass_realization :
    ∃ f : (ℤ → Fin 3) → D39GeomRootedMapClass.{0}, Measurable f ∧
      ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        ∀ (H : WholePlaneRotationHypothesis W)
          (h0 : BoundaryHitWitnesses (shiftedStream W 0))
          (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
          (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
          (hfin : KMSWFiniteIncidence (kmswPastCode W))
          (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
            (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
          (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
            (uibhbotPastMonotoneDrawing W hfin).pos)
          (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
            ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
          (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
            (kmswInfRot (shiftedStream W 0) (H.1 0))
            (kmswLimitDartVertex (shiftedStream W 0)))
          (hf : F.pos = uibhbotSeparationFuturePos W H h0)
          (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
          (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
            h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all _)).arc d).image)
          (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n),
        let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
        let M := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let rho := uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa
        ∃ hd : D39GeomDomain M rho,
          f W = Quotient.mk d39DomainSetoid
            (⟨WholePlaneVertex W, G.GeometricEdge, M, rho, hd⟩ : D39DomainRootedMap) := by
  obtain ⟨f, hfmeas, hfcanon⟩ := exists_measurable_uibhbotD39CanonicalClass_realization
  refine ⟨f, hfmeas, ?_⟩
  filter_upwards [hfcanon, uibhbotCodeLawRel_ae_d39CanonicalDomainEvent] with W hw hW
  obtain ⟨hs, he⟩ := hw
  intro H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hd := uibhbotAssembly_domain_of_canonicalDomainEvent W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos hW
  exact ⟨hd, he.trans (uibhbotAssembly_class_eq_canonical_get W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos hW hd hs).symm⟩

/-- Helper toward Proposition 5.16: a measurable total representative of
the almost-sure source geometric class, chosen only after existence is proved. -/
@[expose] def uibhbotSourceGeometricClass : (ℤ → Fin 3) → D39GeomRootedMapClass.{0} :=
  Classical.choose exists_measurable_uibhbotSourceGeometricClass_realization

/-- Helper toward Proposition 5.16: the selected source-class representative
is Borel measurable. -/
theorem measurable_uibhbotSourceGeometricClass : Measurable uibhbotSourceGeometricClass :=
  (Classical.choose_spec exists_measurable_uibhbotSourceGeometricClass_realization).1

/-- Helper toward Proposition 5.16: on one conull event the selected map
is the geometric class of every compatible Definition 5.8 assembly witness. -/
theorem uibhbotSourceGeometricClass_spec :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
        (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
          (uibhbotPastMonotoneDrawing W hfin).pos)
        (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
          ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
        (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (shiftedStream W 0) (H.1 0))
          (kmswLimitDartVertex (shiftedStream W 0)))
        (hf : F.pos = uibhbotSeparationFuturePos W H h0)
        (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
          h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
            (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n),
      let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
      let M := uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      let rho := uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa
      ∃ hd : D39GeomDomain M rho,
        uibhbotSourceGeometricClass W = Quotient.mk d39DomainSetoid
          (⟨WholePlaneVertex W, G.GeometricEdge, M, rho, hd⟩ : D39DomainRootedMap) :=
  (Classical.choose_spec exists_measurable_uibhbotSourceGeometricClass_realization).2




@[expose] def uibhbotSourceGeometricClassLaw : ProbabilityMeasure D39GeomRootedMapClass.{0} :=
  uibhbotCodeLawRel.map uibhbotSourceGeometricClass

/-- Helper toward Proposition 5.16: every measurable realization of every
Definition 5.8 witness assembly has the source geometric class law. Thus choice
of representative and all off-event values are immaterial. -/
theorem uibhbotSourceGeometricClassLaw_eq_map
    (f : (ℤ → Fin 3) → D39GeomRootedMapClass.{0}) (_hfmeas : Measurable f)
    (hfsource : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
        (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
          (uibhbotPastMonotoneDrawing W hfin).pos)
        (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
          ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
        (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (shiftedStream W 0) (H.1 0))
          (kmswLimitDartVertex (shiftedStream W 0)))
        (hf : F.pos = uibhbotSeparationFuturePos W H h0)
        (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
          h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
            (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n),
      let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
      let M := uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      let rho := uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa
      ∃ hd : D39GeomDomain M rho,
        f W = Quotient.mk d39DomainSetoid
          (⟨WholePlaneVertex W, G.GeometricEdge, M, rho, hd⟩ : D39DomainRootedMap)) :
    uibhbotCodeLawRel.map f = uibhbotSourceGeometricClassLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [hfsource, uibhbotSourceGeometricClass_spec,
    uibhbotCodeLawRel_ae_definition58_class_eq_canonical] with W hw hc hex
  obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, hd, hs, he⟩ := hex
  obtain ⟨hd', he'⟩ := hw H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  obtain ⟨hd'', he''⟩ := hc H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  exact he'.trans he''.symm

/-- Helper toward Proposition 5.16: the source law equals the canonical
code pushforward used in the geometric convergence theorem; this is proved
from the Definition 5.8 witnesses rather than assumed as a law premise. -/
theorem uibhbotSourceGeometricClassLaw_eq_canonicalCodePushforward :
    uibhbotSourceGeometricClassLaw = uibhbotCodeLawRel.map canonicalGeometricClass := by
  apply ProbabilityMeasure.toMeasure_injective
  apply uibhbotCanonical_realization_map_unique
  · filter_upwards [uibhbotSourceGeometricClass_spec,
      uibhbotCodeLawRel_ae_definition58_class_eq_canonical] with W hc hex
    obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, hd, hs, he⟩ := hex
    obtain ⟨hd', he'⟩ := hc H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
    exact ⟨hs, he'.trans he⟩
  · exact canonicalGeometricClass_spec

/-- Helper toward Proposition 5.16: even agreement with one compatible
Definition 5.8 assembly almost surely determines the source law. In particular
this applies to any measurable map agreeing with every full witness set of
`def_uihbot`, without requiring its values on other walks or other data. -/
theorem uibhbotSourceGeometricClassLaw_eq_map_of_ae_assembly
    (f : (ℤ → Fin 3) → D39GeomRootedMapClass.{0}) (_hfmeas : Measurable f)
    (hfsource : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
        (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
          (uibhbotPastMonotoneDrawing W hfin).pos)
        (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
          ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
        (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (shiftedStream W 0) (H.1 0))
          (kmswLimitDartVertex (shiftedStream W 0)))
        (hf : F.pos = uibhbotSeparationFuturePos W H h0)
        (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
          h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
            (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n),
      let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
      let M := uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      let rho := uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa
      ∃ hd : D39GeomDomain M rho,
        f W = Quotient.mk d39DomainSetoid
          (⟨WholePlaneVertex W, G.GeometricEdge, M, rho, hd⟩ : D39DomainRootedMap)) :
    uibhbotCodeLawRel.map f = uibhbotSourceGeometricClassLaw := by
  rw [uibhbotSourceGeometricClassLaw_eq_canonicalCodePushforward]
  apply ProbabilityMeasure.toMeasure_injective
  apply uibhbotCanonical_realization_map_unique
  · filter_upwards [hfsource, uibhbotCodeLawRel_ae_d39CanonicalDomainEvent,
      uibhbotCodeLawRel_ae_uibhbotD39CanonicalClass_isSome] with W hw hW hs
    obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, hd, he⟩ := hw
    exact ⟨hs, he.trans (uibhbotAssembly_class_eq_canonical_get W H h0 hL hR hfin
      P hp ha F hf hFim hFa hRpos hW hd hs)⟩
  · exact canonicalGeometricClass_spec

/-- Helper toward Proposition 5.16: the finite geometric laws converge to
the actual Definition 5.8 geometric class law under exactly Assembly6's
admissibility and square-root hypotheses, without a law-identification premise. -/
theorem finiteGeometricLaw_tendsto_uibhbotSourceGeometricClassLaw
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    Tendsto (fun k => finiteGeometricLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop
      (𝓝 uibhbotSourceGeometricClassLaw) :=
  finiteGeometricLaw_tendsto_of_definition58_identification A hA ell hadm hlo hhi
    uibhbotSourceGeometricClassLaw
    uibhbotSourceGeometricClassLaw_eq_canonicalCodePushforward
































end DirectedDistances.PaperProofs.Section5
end
