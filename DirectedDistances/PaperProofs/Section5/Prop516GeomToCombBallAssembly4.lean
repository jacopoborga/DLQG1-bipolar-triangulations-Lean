/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly2
public import DirectedDistances.PaperProofs.Section5.Prop516StarRotationCommutation












public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

attribute [local instance] Classical.propDecidable

private theorem d39DrawingRepresentationData3_geomBallIso_rotation_comm_on_retained_star
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
        ((d39BallMap M r).rot d) =
      (d39BallMap N r).rot
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d) := by
  classical
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  let star : Set {q : M.core.D // q ∈ d39BallDarts M r} :=
    {q | rootedLocallyFiniteVertexClass M.core.rot q.1 =
      rootedLocallyFiniteVertexClass M.core.rot d.1}
  have hsource := d39DrawingRepresentationData3_ball_rotation_topological_successor
    r x d
  let param (q : {q : M.core.D // q ∈ d39BallDarts M r}) : I ≃ₜ I :=
    d39GeomBallIsoV2DartParam e
      ⟨(x.dartEquiv q.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x r q.1).mp q.2⟩
      (x.dartEquiv q.1).2
  have htransport := d39TopologicalCcwSuccessor_map_orientedHomeomorph
    star
    (fun q => d39DrawingDartArc B x.toD39DrawingRepresentationData q.1)
    (fun q => d39DrawingDartArc C y.toD39DrawingRepresentationData (E q).1)
    param d ((d39BallMap M r).rot d) e.h e.orientationPreserving
    (fun q _ => d39GeomBallIsoV2DartParam_strictMono e _ _)
    (fun q _ t => d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_arc_map
      x y e q t) hsource
  have hindexed :=
    (d39TopologicalCcwSuccessor_map_equiv_iff E _ _ _ _).mpr htransport
  have himage : E '' star =
      {q : {q : N.core.D // q ∈ d39BallDarts N r} |
        rootedLocallyFiniteVertexClass N.core.rot q.1 =
          rootedLocallyFiniteVertexClass N.core.rot (E d).1} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_iff
        x y e p d).mpr hp
    · intro hq
      refine ⟨E.symm q, ?_, E.apply_symm_apply q⟩
      apply (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_iff
        x y e (E.symm q) d).mp
      change rootedLocallyFiniteVertexClass N.core.rot (E (E.symm q)).1 = _
      rw [E.apply_symm_apply]
      exact hq
  rw [himage] at hindexed
  have htransported : D39TopologicalCcwSuccessor
      {q : {q : N.core.D // q ∈ d39BallDarts N r} |
        rootedLocallyFiniteVertexClass N.core.rot q.1 =
          rootedLocallyFiniteVertexClass N.core.rot (E d).1}
      (fun q => d39DrawingDartArc C y.toD39DrawingRepresentationData q.1)
      (E d) (E ((d39BallMap M r).rot d)) := by
    simpa only [E.apply_symm_apply] using hindexed
  exact d39TopologicalCcwSuccessor_unique htransported
    (d39DrawingRepresentationData3_ball_rotation_topological_successor r y (E d))

/-- Helper toward Proposition 5.16: the geometric ball dart equivalence
commutes with the first-return rotations at every retained dart. Interior
stars use the full-star commutation theorem; boundary stars use the retained
star first-return successor and its transport under the oriented homeomorphism. -/
theorem d39DrawingRepresentationData3_geomBallIso_rotation_comm
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (hr : 0 < r) (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
        ((d39BallMap M r).rot d) =
      (d39BallMap N r).rot
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d) := by
  classical
  let star : Set M.core.D :=
    {q | rootedLocallyFiniteVertexClass M.core.rot q =
      rootedLocallyFiniteVertexClass M.core.rot d.1}
  by_cases hstar : star ⊆ d39BallDarts M r
  · have hball : ∀ q : M.core.D,
        rootedLocallyFiniteVertexClass M.core.rot q =
          rootedLocallyFiniteVertexClass M.core.rot d.1 →
        (x.dartEquiv q).1 ∈ d39GeomBallEdges B.map B.root r :=
      (d39DrawingRepresentationData3_star_subset_ballDarts_iff_geomBall
        x d.1).mp hstar
    exact d39DrawingRepresentationData3_geomBallIso_rotation_comm_when_star_in_ball
      hr x y e d hball
  · exact d39DrawingRepresentationData3_geomBallIso_rotation_comm_on_retained_star
      x y e d

/-- Helper toward Proposition 5.16: the geometric ball dart equivalence
assembles the faced-ball isomorphism once its original-face field is supplied. -/
theorem d39BallIso_of_geomBallIsoV2_of_original_iff
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (r : ℕ) (hr : 0 < r)
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (horiginal : ∀ d : {d : M.core.D // d ∈ d39BallDarts M r},
      d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d ∈
          (d39FacedBall N r hr).original ↔
        d ∈ (d39FacedBall M r hr).original) :
    Nonempty (D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) := by
  classical
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  refine ⟨{
    toEquiv := E
    rot_comm := ?_
    edgeInv_comm := ?_
    missing_iff := ?_
    tail_iff := ?_
    root_comm := ?_
    original_iff := horiginal
  }⟩
  · intro d
    exact d39DrawingRepresentationData3_geomBallIso_rotation_comm hr x y e d
  · intro d
    exact d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_edgeInv x y e d
  · intro d
    exact d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_missing_iff x y e d
  · intro d
    exact d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_tail_iff x y e d
  · exact d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_root x y e













































end DirectedDistances.PaperProofs.Section5

end
