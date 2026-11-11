module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso6








public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

attribute [local instance] Classical.propDecidable

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. The target dart arc obtained by applying
the geometric ball map to a source dart and accounting for its edge flip. -/
def d39GeomBallIsoV2TargetDartArc
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r})
    (forward : Bool) : I → ℂ :=
  if Bool.xor forward (e.edgeFlip a) then
    C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1
  else
    (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).symm

/-- Helper toward Proposition 5.16. If every dart at a source vertex belongs
to the geometric ball, its represented cyclic-successor witness transports
to the corresponding target dart arcs. -/
theorem d39GeomBallIsoV2_topological_successor_transport
    {M : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : M.core.D)
    (hball : ∀ q : M.core.D,
      rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d →
      (x.dartEquiv q).1 ∈ d39GeomBallEdges B.map B.root r) :
    D39TopologicalCcwSuccessor
      {q | rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d}
      (fun q => d39GeomBallIsoV2TargetDartArc e
        (if hq : rootedLocallyFiniteVertexClass M.core.rot q =
            rootedLocallyFiniteVertexClass M.core.rot d then
          ⟨(x.dartEquiv q).1, hball q hq⟩
        else ⟨B.root.1, d39GeomRootEdge_mem B.map B.root e.radius_pos⟩)
        (x.dartEquiv q).2)
      d (M.core.rot d) := by
  classical
  let star : Set M.core.D :=
    {q | rootedLocallyFiniteVertexClass M.core.rot q =
      rootedLocallyFiniteVertexClass M.core.rot d}
  let edgeOf (q : M.core.D) :
      {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
    if hq : q ∈ star then
      ⟨(x.dartEquiv q).1, hball q hq⟩
    else ⟨B.root.1, d39GeomRootEdge_mem B.map B.root e.radius_pos⟩
  let param (q : M.core.D) : I ≃ₜ I :=
    d39GeomBallIsoV2DartParam e (edgeOf q) (x.dartEquiv q).2
  let targetArc (q : M.core.D) : I → ℂ :=
    d39GeomBallIsoV2TargetDartArc e (edgeOf q) (x.dartEquiv q).2
  have hparam : ∀ q ∈ star, StrictMono (param q) := by
    intro q hq
    exact d39GeomBallIsoV2DartParam_strictMono e (edgeOf q)
      (x.dartEquiv q).2
  have hmap : ∀ q ∈ star, ∀ t,
      e.h (d39DrawingDartArc B x.toD39DrawingRepresentationData q t) =
        targetArc q (param q t) := by
    intro q hq t
    change rootedLocallyFiniteVertexClass M.core.rot q =
      rootedLocallyFiniteVertexClass M.core.rot d at hq
    have hval : (edgeOf q).1 = (x.dartEquiv q).1 := by
      dsimp [edgeOf, star]
      rw [dite_eq_left hq]
    have h := d39GeomBallIsoV2_arc_map_dart e (edgeOf q)
      (x.dartEquiv q).2 t
    rw [hval] at h
    cases hb : (x.dartEquiv q).2 <;>
      cases hf : e.edgeFlip (edgeOf q) <;>
      simpa [d39DrawingDartArc, targetArc, param,
        d39GeomBallIsoV2TargetDartArc, hval, hb, hf] using h
  exact d39TopologicalCcwSuccessor_map_orientedHomeomorph star
    (d39DrawingDartArc B x.toD39DrawingRepresentationData) targetArc param
    d (M.core.rot d) e.h e.orientationPreserving hparam hmap
    (x.rotation_topological_successor d)














































































end DirectedDistances.PaperProofs.Section5

end
