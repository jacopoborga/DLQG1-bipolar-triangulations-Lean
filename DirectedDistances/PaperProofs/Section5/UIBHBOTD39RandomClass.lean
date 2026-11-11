/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39Domain
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassSpace

/-! # The UIBHBOT geometric rooted-map class

Helpers toward Definition 3.8 applications (Propositions 5.9 and 5.16). -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open MeasureTheory

/-- The witness event used to select the UIBHBOT assembly as a rooted-map
class. Its witnesses include the source root edge, the compensated ordered
root mark, and the complete Definition 3.8 domain proof. -/
def uibhbotD39WitnessEvent (W : ℤ → Fin 3) : Prop :=
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
    (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
      (shiftedStream W 0) h0 (H.1 0) ''
        ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
          (monotone_family_all _)).arc d).image)
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (e : ℤ → WholePlaneEdge W),
    e 0 = uibhbotRootEdge W ∧
      D39GeomDomain (uibhbotAssemblyDirectedPlaneMapWithMissing
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)
        (uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa)

/-- Helper toward Definition 3.8 applications (Propositions 5.9 and 5.16):
the provider witness event supplies a domain rooted map. -/
theorem uibhbotD39WitnessEvent_nonempty (W : ℤ → Fin 3)
    (hW : uibhbotD39WitnessEvent W) :
    ∃ A : D39DomainRootedMap.{0}, D39GeomDomain A.map A.root := by
  classical
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, he, hdomain⟩
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let rho := uibhbotAssemblyD39RootMark W H h0 hL hR hfin P hp ha F hf hFim hFa
  let A : D39DomainRootedMap.{0} :=
    ⟨WholePlaneVertex W, (G).GeometricEdge, M, rho, hdomain⟩
  exact ⟨A, hdomain⟩

/-- Helper toward Definition 3.8 applications (Propositions 5.9 and 5.16):
select the rooted geometric class of a provider witness tuple, with `none`
exactly when the provider domain-witness event does not hold. -/
noncomputable def uibhbotD39Class (W : ℤ → Fin 3) : Option D39GeomRootedMapClass.{0} := by
  classical
  exact if hW : uibhbotD39WitnessEvent W then
    some (Quotient.mk d39DomainSetoid
      (Classical.choose (uibhbotD39WitnessEvent_nonempty W hW)))
  else none

/-- Helper toward Definition 3.8 applications (Propositions 5.9 and 5.16):
the selected UIBHBOT geometric rooted-map class is defined almost surely. -/
theorem uibhbotCodeLawRel_ae_uibhbotD39Class_isSome :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      (uibhbotD39Class W).isSome := by
  filter_upwards [uibhbotCodeLawRel_ae_d39GeomDomain] with W hW
  have hW' : uibhbotD39WitnessEvent W := hW
  simp [uibhbotD39Class, hW']


























































end DirectedDistances.PaperProofs.Section5

