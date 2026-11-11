/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation11
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation12









public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.SourceResults
open unitInterval

/-- Helper toward Proposition 5.16. The canonical assembly domain used by
the constructed representation in Rep12. -/
@[expose] noncomputable def uibhbotD39CanonicalRepresentation13Domain
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W) :
    D39DomainRootedMapV2 := by
  let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  exact ⟨WholePlaneVertex W, G.GeometricEdge,
    uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      D.pastRightPositive,
    uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence,
    D.domain⟩

/-- Helper toward Proposition 5.16. A public selected name for the
constructed code-map drawing-representation record of Rep12. -/
@[expose] noncomputable def uibhbotD39CanonicalRepresentation13Base
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W) :
    D39DrawingRepresentationData
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
      (uibhbotD39CanonicalRepresentation13Domain W D) := by
  classical
  let h := uibhbotD39CanonicalAssembly_rotation_topological_successor W hW D
  let h₁ := Classical.choose_spec h
  let h₂ := Classical.choose_spec h₁
  let h₃ := Classical.choose_spec h₂
  exact Classical.choose h₃

/-- Helper toward Proposition 5.16. The selected Rep12 record retains the
prescribed dart equivalence and its proved topological successor field. -/
theorem uibhbotD39CanonicalRepresentation13Base_spec
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W) :
    let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
    let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
    let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
    let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
    let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let B : D39DomainRootedMapV2 :=
      ⟨WholePlaneVertex W, G.GeometricEdge,
        uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
          D.pastRightPositive,
        uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence,
        D.domain⟩
    let M :=
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0)
      (iso : D39RootedMapIso
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)),
      (uibhbotD39CanonicalRepresentation13Base W hW D).dartEquiv =
        iso.toEquiv.symm.trans
          (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
            D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
            P hp ha F hf hFim hFa) ∧
      ∀ d, D39TopologicalCcwSuccessor
        {e | rootedLocallyFiniteVertexClass M.core.rot e =
          rootedLocallyFiniteVertexClass M.core.rot d}
        (d39DrawingDartArc B (uibhbotD39CanonicalRepresentation13Base W hW D))
        d (M.core.rot d) := by
  classical
  let h := uibhbotD39CanonicalAssembly_rotation_topological_successor W hW D
  let hhit := Classical.choose h
  let h₁ := Classical.choose_spec h
  let C₀ := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let iso := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  refine ⟨hhit, C₀, iso, ?_⟩
  exact Classical.choose_spec h₃





theorem uibhbotD39CanonicalRepresentation13Base_faceOrbit
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W)
    (d e : ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D) :
    (uibhbotD39CanonicalRepresentation13Base W hW D).faceOfDart d =
        (uibhbotD39CanonicalRepresentation13Base W hW D).faceOfDart e ↔
      Equiv.Perm.SameCycle
        (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot.symm *
          ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.edgeInv)
        d e := by
  exact (uibhbotD39CanonicalRepresentation13Base W hW D).faceOrbit_iff d e

/-- Helper toward Proposition 5.16. The selected record's vertex map sends
the initial vertex of each dart to the endpoint prescribed by its direction
bit. -/
theorem uibhbotD39CanonicalRepresentation13Base_tailVertex
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W)
    (d : ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D) :
    (uibhbotD39CanonicalRepresentation13Base W hW D).vertexEquiv
        (rootedLocallyFiniteVertexClass
          ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d) =
      if ((uibhbotD39CanonicalRepresentation13Base W hW D).dartEquiv d).2 then
        (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.src
          ((uibhbotD39CanonicalRepresentation13Base W hW D).dartEquiv d).1
      else
        (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.tgt
          ((uibhbotD39CanonicalRepresentation13Base W hW D).dartEquiv d).1 := by
  exact (uibhbotD39CanonicalRepresentation13Base W hW D).dart_tail_vertex d



































































end DirectedDistances.PaperProofs.Section5

end
