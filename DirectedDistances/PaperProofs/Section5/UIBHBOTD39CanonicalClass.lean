/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalDomain3
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassSpace
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39RandomClass

/-! # The canonical UIBHBOT geometric rooted-map class

Helpers toward Definition 3.8 consumers. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory

noncomputable section

/-- Helper toward Definition 3.8 consumers: the directed map of the canonical
past and future drawing assembly, for the witnesses needed to construct its
two canonical drawings. -/
@[expose] noncomputable def uibhbotD39CanonicalAssemblyMap
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) :=
  uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin
    (uibhbotD39PastCanonicalDrawing W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
    (uibhbotD39FutureCanonicalDrawing W H h0)
    (uibhbotD39FutureCanonicalDrawing_pos W H h0)
    (uibhbotD39FutureCanonicalDrawing_image W H h0)
    (uibhbotD39FutureCanonicalDrawing_arcImage W H h0) hRpos

/-- Helper toward Definition 3.8 consumers: the ordered root mark of the
canonical past and future drawing assembly. -/
@[expose] noncomputable def uibhbotD39CanonicalAssemblyRoot
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W)) :=
  uibhbotAssemblyD39RootMark W H h0 hL hR hfin
    (uibhbotD39PastCanonicalDrawing W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
    (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
    (uibhbotD39FutureCanonicalDrawing W H h0)
    (uibhbotD39FutureCanonicalDrawing_pos W H h0)
    (uibhbotD39FutureCanonicalDrawing_image W H h0)
    (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)

/-- Helper toward Definition 3.8 consumers: witnesses that the canonical
drawing assembly belongs to the complete geometric domain. The structure
contains only the hypotheses and domain proof; its drawings are the fixed
canonical constructors, not selected values. -/
structure UIBHBOTD39CanonicalDomainWitness (W : ℤ → Fin 3) where
  rotation : WholePlaneRotationHypothesis W
  boundary : BoundaryHitWitnesses (shiftedStream W 0)
  pastLeftUnbounded :
    ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a
  pastRightNonnegative : ∀ n, 0 ≤ R (kmswPastCode W) n
  pastFiniteIncidence : KMSWFiniteIncidence (kmswPastCode W)
  pastRightPositive : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n
  domain : D39GeomDomain
    (uibhbotD39CanonicalAssemblyMap W rotation boundary pastLeftUnbounded
      pastRightNonnegative pastFiniteIncidence pastRightPositive)
    (uibhbotD39CanonicalAssemblyRoot W rotation boundary pastLeftUnbounded
      pastRightNonnegative pastFiniteIncidence)

/-- Helper toward Definition 3.8 consumers: the predicate that the canonical
drawing assembly has a complete Definition 3.8 geometric domain. -/
def uibhbotD39CanonicalDomainEvent (W : ℤ → Fin 3) : Prop :=
  Nonempty (UIBHBOTD39CanonicalDomainWitness W)

/-- Helper toward Definition 3.8 consumers: select the rooted geometric
class of the canonical drawing assembly when its geometric domain holds, and
return `none` otherwise. The classical case split is on the domain event; the
selected witness has no drawing fields. -/
noncomputable def uibhbotD39CanonicalClass (W : ℤ → Fin 3) :
    Option D39GeomRootedMapClass.{0} := by
  classical
  refine dite (uibhbotD39CanonicalDomainEvent W) ?_ ?_
  · intro hW
    let D := Classical.choice hW
    let A : D39DomainRootedMap.{0} :=
      ⟨WholePlaneVertex W,
        (uibhbotCcw_assemblyDrawing W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
          (uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
            D.pastRightNonnegative D.pastFiniteIncidence)
          (uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
            D.pastRightNonnegative D.pastFiniteIncidence)
          (uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
            D.pastRightNonnegative D.pastFiniteIncidence)
          (uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary)
          (uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary)
          (uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary)
          (uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary)).GeometricEdge,
        uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
          D.pastRightPositive,
        uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence,
        D.domain⟩
    exact some (Quotient.mk d39DomainSetoid A)
  · intro _
    exact none

/-- Helper toward Definition 3.8 consumers: the canonical geometric domain
event follows almost surely from the canonical assembly domain theorem. -/
theorem uibhbotCodeLawRel_ae_d39CanonicalDomainEvent :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      uibhbotD39CanonicalDomainEvent W := by
  filter_upwards [uibhbotCodeLawRel_ae_d39CanonicalGeomDomain] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, hRpos, e, he, hdomain⟩
  exact ⟨⟨H, h0, hL, hR, hfin, hRpos, hdomain⟩⟩

/-- Helper toward Definition 3.8 consumers: almost surely the canonical
UIBHBOT geometric rooted-map class is defined. -/
theorem uibhbotCodeLawRel_ae_uibhbotD39CanonicalClass_isSome :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      (uibhbotD39CanonicalClass W).isSome := by
  filter_upwards [uibhbotCodeLawRel_ae_d39CanonicalDomainEvent] with W hW
  simp [uibhbotD39CanonicalClass, hW]

/-- Helper toward Definition 3.8 consumers: the canonical drawing assembly
has the almost-sure geometric domain recorded as the `Pcan`/`Fcan` target in
`UIBHBOTD39RandomClass2`. -/
theorem uibhbotCodeLawRel_ae_d39CanonicalMapDomain :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W),
      e 0 = uibhbotRootEdge W ∧
        D39GeomDomain
          (uibhbotAssemblyDirectedPlaneMapWithMissing W H h0 hL hR hfin
            (uibhbotD39PastCanonicalDrawing W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
            (uibhbotD39FutureCanonicalDrawing W H h0)
            (uibhbotD39FutureCanonicalDrawing_pos W H h0)
            (uibhbotD39FutureCanonicalDrawing_image W H h0)
            (uibhbotD39FutureCanonicalDrawing_arcImage W H h0) hRpos)
          (uibhbotAssemblyD39RootMark W H h0 hL hR hfin
            (uibhbotD39PastCanonicalDrawing W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_pos W hL hR hfin)
            (uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin)
            (uibhbotD39FutureCanonicalDrawing W H h0)
            (uibhbotD39FutureCanonicalDrawing_pos W H h0)
            (uibhbotD39FutureCanonicalDrawing_image W H h0)
            (uibhbotD39FutureCanonicalDrawing_arcImage W H h0)) := by
  exact uibhbotCodeLawRel_ae_d39CanonicalGeomDomain

end

end DirectedDistances.PaperProofs.Section5
