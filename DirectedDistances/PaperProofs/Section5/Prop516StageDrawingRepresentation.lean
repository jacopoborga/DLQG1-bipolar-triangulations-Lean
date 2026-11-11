/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2
public import DirectedDistances.PlanarMap.D39DrawingRepresentation3
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.KMSW.KMSWStageDrawing

/-! # Finite stage drawing representation bridge

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16. A PL drawing with finitely many darts has
finitely many geometric edge identities after quotienting by dart reversal. -/
theorem plDrawing_geometricEdge_finite
    {D V : Type*} [Finite D] {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) :
    Finite P.GeometricEdge := by
  classical
  exact Finite.of_surjective (Quotient.mk P.edgeSetoid) Quotient.mk_surjective

/-- Helper toward Proposition 5.16. A finite geometric edge carrier is
locally finite at every vertex in the local topology sense, which counts edge identities
including missing edges and parallel edges. -/
theorem d39GeomDomain_of_finite_edgeCarrier
    {V E : Type*} [Finite E] (M : DirectedPlaneMapWithMissing V E)
    (rho : E × Bool)
    (hconn : ∀ v w : V, (d39GeomGraph M).Reachable v w)
    (hroot : M.toPlaneMapWithMissing.missing rho.1 ∨
      ∃ h : ¬ M.toPlaneMapWithMissing.missing rho.1,
        M.forward ⟨rho.1, h⟩ = rho.2) :
    D39GeomDomain M rho := by
  classical
  exact ⟨hconn, fun _ => Set.toFinite _, hroot⟩

/-- Helper toward Proposition 5.16. Build the directed plane map carried by a
PL drawing, retaining its geometric edge identities, missing tags and the
directions of present edges. The external-face witnesses are explicit input
because they are required by `PlaneMapWithMissing`. -/
@[expose] def finitePLDrawingDirectedMap
    {D V : Type u} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (missing : P.GeometricEdge → Prop)
    (forward : {e : P.GeometricEdge // ¬ missing e} → Bool)
    (hmissingExternal : ∀ e, missing e →
      ∃ F : P.toPlaneGraphDrawing.Face,
        PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧
          Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val) :
    DirectedPlaneMapWithMissing V P.GeometricEdge :=
  { toPlaneMapWithMissing :=
      { toPlaneGraphDrawing := P.toPlaneGraphDrawing
        missing := missing
        missing_on_external := hmissingExternal }
    forward := forward }

/-- Helper toward Proposition 5.16. Package a connected finite geometric map
and a valid ordered root mark as a local topology v2 domain object. -/
@[expose] noncomputable def d39FiniteDomainRootedMapV2
    {V E : Type u} [Finite E] (M : DirectedPlaneMapWithMissing V E)
    (rho : E × Bool)
    (hconn : ∀ v w : V, (d39GeomGraph M).Reachable v w)
    (hroot : M.toPlaneMapWithMissing.missing rho.1 ∨
      ∃ h : ¬ M.toPlaneMapWithMissing.missing rho.1,
        M.forward ⟨rho.1, h⟩ = rho.2) :
    D39DomainRootedMapV2 :=
  ⟨V, E, M, rho, d39GeomDomain_of_finite_edgeCarrier M rho hconn hroot⟩

/-- Helper toward Proposition 5.16. A finite PL drawing gives a finite local topology
domain object once its missing-edge exterior witnesses, geometric connectedness
and ordered root validity have been established. -/
@[expose] noncomputable def finitePLDrawingD39DomainRootedMapV2
    {D V : Type u} [Finite D]
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (missing : P.GeometricEdge → Prop)
    (forward : {e : P.GeometricEdge // ¬ missing e} → Bool)
    (hmissingExternal : ∀ e, missing e →
      ∃ F : P.toPlaneGraphDrawing.Face,
        PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧
          Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val)
    (root : P.GeometricEdge × Bool)
    (hconn : ∀ v w : V,
      (d39GeomGraph (finitePLDrawingDirectedMap P missing forward
        hmissingExternal)).Reachable v w)
    (hroot : (finitePLDrawingDirectedMap P missing forward hmissingExternal).toPlaneMapWithMissing.missing root.1 ∨
      ∃ h : ¬ (finitePLDrawingDirectedMap P missing forward hmissingExternal).toPlaneMapWithMissing.missing root.1,
        (finitePLDrawingDirectedMap P missing forward hmissingExternal).forward
          ⟨root.1, h⟩ = root.2) :
    D39DomainRootedMapV2 := by
  letI : Finite P.GeometricEdge := plDrawing_geometricEdge_finite P
  exact d39FiniteDomainRootedMapV2
    (finitePLDrawingDirectedMap P missing forward hmissingExternal)
    root hconn hroot


















































































end DirectedDistances.PaperProofs.Section5

end
