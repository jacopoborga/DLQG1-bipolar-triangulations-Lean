/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat6
public import DirectedDistances.PaperProofs.Section5.Prop59RootAbsentAE
import DirectedDistances.PaperProofs.Section5.Prop516BallMarkerPreservation

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). This file identifies the
canonical assembly's restricted external orbit with its missing-root side and
transports that identification across represented faced-ball isomorphisms.
It makes no paper-completion claim. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory

/-- Helper toward Proposition 5.9. For every positive-radius ball of the
canonical UIBHBOT assembly representation, the reverse of its missing root
dart lies in the selected restricted external orbit. The root mark is the
missing frame edge, and the outer-dart comparison identifies its reverse
with the canonical outer dart. -/
theorem prop59_canonicalAssembly_missingRootSide_mem_restrictedExternalOrbit
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hrootAbsent : ¬ wholePlaneEdgePresent W (uibhbotRootEdge W))
    (r : ℕ) (hr : 0 < r) :
    let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
    let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
    M.core.missing M.rootMark.dart ∧
      (uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        D.pastRightPositive).toPlaneMapWithMissing.missing
        (uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence).1 ∧
      (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart ∈
        (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
  have hmark : ∃ d, ∃ hm : M.core.missing d,
      M.rootMark = D39RootMark.missing d hm := by
    exact ⟨M.rootMark.dart, by
      change (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).missing
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).frameEdgeDart
      exact (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).frameEdge_missing,
      by rfl⟩
  obtain ⟨root, hrootMissing, hrootMark⟩ := hmark
  have hrootDart : M.rootMark.dart = root := by
    rw [hrootMark]
    rfl
  have hballRoot : (d39FacedBall M r hr).rootDart =
      ⟨root, by rw [← hrootDart]; exact (d39BallDarts_root_mem M hr).1⟩ := by
    apply Subtype.ext
    exact hrootDart
  have hmissing : M.core.missing M.rootMark.dart := by
    rw [hrootMark]
    exact hrootMissing
  have hassemblyRootMissing :=
    (prop59_canonicalAssembly_rootMissing_iff_rootAbsent W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      D.pastRightPositive).mpr hrootAbsent
  obtain ⟨d, hdOuter, hmem⟩ :=
    prop59_canonicalAssembly_outerDart_mem_restrictedExternalOrbit W D hhit C₀ r hr
  have houter : M.core.outer = uibhbotWholePlaneOuterDart W := by
    change (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).outer = _
    rfl
  have houterRoot : M.core.outer = M.core.edgeInv M.rootMark.dart := by rfl
  have hside : (d39FacedBall M r hr).map.edgeInv
      (d39FacedBall M r hr).rootDart = d := by
    have hval : ((d39FacedBall M r hr).map.edgeInv
        (d39FacedBall M r hr).rootDart).1 = d.1 := by
      rw [hballRoot]
      change M.core.edgeInv root = d.1
      rw [← hrootDart, ← houterRoot, houter]
      exact hdOuter.symm
    apply Subtype.ext
    exact hval
  exact ⟨hmissing, hassemblyRootMissing, hside ▸ hmem⟩

/-- Helper toward Proposition 5.9. For two represented faced balls, if the
reverse-root side belongs to each selected restricted external orbit, then a
full faced-ball isomorphism transports the selected external orbit exactly.
The isomorphism's root and missing-tag fields identify the marked side; its
root and edge-reversal fields carry that side to the target ball. -/
theorem prop59_representedExternalOrbit_eq_of_missingRootSide_mem
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (_x : PLCylinderBall.Representation M B)
    (_y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (_hrootM : M.core.missing M.rootMark.dart)
    (_hrootN : N.core.missing N.rootMark.dart)
    (hsideM : (d39FacedBall M r hr).map.edgeInv
        (d39FacedBall M r hr).rootDart ∈
      (d39FacedBallPLWithExternal M _x.drawing r hr).externalOrbit.val)
    (hsideN : (d39FacedBall N r hr).map.edgeInv
        (d39FacedBall N r hr).rootDart ∈
      (d39FacedBallPLWithExternal N _y.drawing r hr).externalOrbit.val) :
    plBallFaceOrbitMap I
        (d39FacedBallPLWithExternal M _x.drawing r hr).externalOrbit =
      (d39FacedBallPLWithExternal N _y.drawing r hr).externalOrbit := by
  have hsideMap : I.toEquiv
      ((d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart) =
        (d39FacedBall N r hr).map.edgeInv (d39FacedBall N r hr).rootDart := by
    calc
      I.toEquiv ((d39FacedBall M r hr).map.edgeInv
          (d39FacedBall M r hr).rootDart) =
          (d39FacedBall N r hr).map.edgeInv
            (I.toEquiv (d39FacedBall M r hr).rootDart) := I.edgeInv_comm _
      _ = (d39FacedBall N r hr).map.edgeInv
          (d39FacedBall N r hr).rootDart := congrArg _ I.root_comm
  have _hrootTagN : (d39FacedBall N r hr).missing
      (d39FacedBall N r hr).rootDart := by
    rw [← I.root_comm]
    exact (I.missing_iff (d39FacedBall M r hr).rootDart).mpr (by
      change M.core.missing M.rootMark.dart
      exact _hrootM)
  exact (plBallFaceOrbitMap_eq_iff_exists_common_dart I
    (d39FacedBallPLWithExternal M _x.drawing r hr).externalOrbit
    (d39FacedBallPLWithExternal N _y.drawing r hr).externalOrbit).2
      ⟨(d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart,
        hsideM, by rw [hsideMap]; exact hsideN⟩

/-- Helper toward Proposition 5.9. The canonical assembly's side of the
missing root is carried to the selected exterior of any second drawing whose
reverse-root side is also selected. This is the canonical-assembly instance
of the generic represented-ball comparison; the second drawing and its
root-side fact remain explicit. -/
theorem prop59_canonicalAssembly_externalOrbit_eq_of_rootSide_mem
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hrootAbsent : ¬ wholePlaneEdgePresent W (uibhbotRootEdge W))
    {N : D39RootedMap}
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso
      (d39FacedBall
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
        r hr)
      (d39FacedBall N r hr))
    (_hrootN : N.core.missing N.rootMark.dart)
    (hsideN : (d39FacedBall N r hr).map.edgeInv
        (d39FacedBall N r hr).rootDart ∈
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit.val) :
    plBallFaceOrbitMap I
        (d39FacedBallPLWithExternal
          ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
          (prop59_canonicalAssembly_reindexedDrawing W D hhit C₀) r hr).externalOrbit =
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit := by
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
  have hA := prop59_canonicalAssembly_missingRootSide_mem_restrictedExternalOrbit
    W D hhit C₀ hrootAbsent r hr
  change M.core.missing M.rootMark.dart ∧
    (uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      D.pastRightPositive).toPlaneMapWithMissing.missing
      (uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence).1 ∧
    (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart ∈
      (d39FacedBallPLWithExternal M P r hr).externalOrbit.val at hA
  have hsideMap : I.toEquiv
      ((d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart) =
        (d39FacedBall N r hr).map.edgeInv (d39FacedBall N r hr).rootDart := by
    calc
      I.toEquiv ((d39FacedBall M r hr).map.edgeInv
          (d39FacedBall M r hr).rootDart) =
          (d39FacedBall N r hr).map.edgeInv
            (I.toEquiv (d39FacedBall M r hr).rootDart) := I.edgeInv_comm _
      _ = (d39FacedBall N r hr).map.edgeInv
          (d39FacedBall N r hr).rootDart := congrArg _ I.root_comm
  exact (plBallFaceOrbitMap_eq_iff_exists_common_dart I
    (d39FacedBallPLWithExternal M P r hr).externalOrbit
    (d39FacedBallPLWithExternal N Q r hr).externalOrbit).2
      ⟨(d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart,
        hA.2.2, by rw [hsideMap]; exact hsideN⟩

/-- Helper toward Proposition 5.9. The almost-sure canonical root-edge
absence supplies the missing-root condition used by the represented
comparison above. -/
theorem prop59_uibhbotRootEdge_absent_ae_for_mirror_compat :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ¬ wholePlaneEdgePresent W (uibhbotRootEdge W) :=
  prop59_uibhbotRootEdge_absent_ae

end DirectedDistances.PaperProofs.Section5

end
