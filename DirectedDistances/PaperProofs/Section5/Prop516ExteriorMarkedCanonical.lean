/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516RootExteriorEncoding
public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat8
public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect8

/-! Helper toward Proposition 5.16: the canonical UIBHBOT assembly drawing's
restricted exterior marking is the reversed-root lift of its unmarked ball
class, once the source root edge is absent. The almost-sure statement uses
the root-edge absence result under the canonical representation binders.
This helper makes no paper-completion claim. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.KMSW
open MeasureTheory

/-- Helper toward Proposition 5.16. Under explicit absence of the canonical
root edge, the canonical assembly drawing's exterior-marked ball class is
the reversed-root lift of its unmarked ball class at every positive radius. -/
theorem prop516_canonicalExteriorMarkedBallClass_eq_rootLift
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hrootAbsent : ¬ wholePlaneEdgePresent W (uibhbotRootEdge W))
    (r : ℕ) (hr : 0 < r) :
    let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
    let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
    Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal M P r hr) =
      Prop516RootExteriorEncoding.rootLift (d39BallClass M r hr) := by
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
  have hcanonical := prop59_canonicalAssembly_missingRootSide_mem_restrictedExternalOrbit
    W D hhit C₀ hrootAbsent r hr
  change M.core.missing M.rootMark.dart ∧ _ ∧
    (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart ∈
      (d39FacedBallPLWithExternal M P r hr).externalOrbit.val at hcanonical
  obtain ⟨_, _, hside⟩ := hcanonical
  let d := (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart
  have horbit :
      (d39FacedBallPLWithExternal M P r hr).externalOrbit =
        (Prop516RootExteriorEncoding.rootBall (d39FacedBall M r hr)).externalOrbit :=
    plBallFaceCycleOrbit_eq_of_mem _ _ d hside Equiv.Perm.SameCycle.rfl
  have heq : d39FacedBallPLWithExternal M P r hr =
      Prop516RootExteriorEncoding.rootBall (d39FacedBall M r hr) := by
    exact congrArg (fun O : D39BallFaceCycleOrbit (d39FacedBall M r hr) =>
      D39FiniteBallWithExternal.mk (d39FacedBall M r hr) O) horbit
  exact congrArg (Quotient.mk exteriorMarkedBallSetoid) heq

/-- Helper toward Proposition 5.16. Almost surely under the canonical UIBHBOT
code law, every choice of canonical domain, boundary-hit witnesses and root
capture gives the exterior-marked class equality at every positive radius. -/
theorem prop516_canonicalExteriorMarkedBallClass_eq_rootLift_ae
    (r : ℕ) (hr : 0 < r) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (D : UIBHBOTD39CanonicalDomainWitness W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C₀ : UIBHBOTCertifiedRootCapture W 0),
        let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
        let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
        Quotient.mk exteriorMarkedBallSetoid
            (d39FacedBallPLWithExternal M P r hr) =
          Prop516RootExteriorEncoding.rootLift (d39BallClass M r hr) := by
  filter_upwards [prop59_uibhbotRootEdge_absent_ae_for_mirror_compat] with W hrootAbsent
  intro D hhit C₀
  exact prop516_canonicalExteriorMarkedBallClass_eq_rootLift
    W D hhit C₀ hrootAbsent r hr

end DirectedDistances.PaperProofs.Section5

end
