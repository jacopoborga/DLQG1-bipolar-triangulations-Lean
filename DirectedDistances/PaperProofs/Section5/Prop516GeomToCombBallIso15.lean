/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso14

/-! Helper toward Proposition 5.16. This file records the restriction of a full
vertex star to the combinatorial ball and the remaining star-map and rotation
obligations for the geometric-to-combinatorial ball equivalence. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16. The entire combinatorial dart star at a
vertex lies in the combinatorial ball exactly when every represented dart at
that vertex belongs to the geometric radius ball. -/
theorem d39DrawingRepresentationData3_star_subset_ballDarts_iff_geomBall
    {M : D39RootedMap} {B : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B) (d : M.core.D) :
    {q : M.core.D | rootedLocallyFiniteVertexClass M.core.rot q =
      rootedLocallyFiniteVertexClass M.core.rot d} ⊆ d39BallDarts M r ↔
    ∀ q : M.core.D,
      rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d →
      (x.dartEquiv q).1 ∈ d39GeomBallEdges B.map B.root r := by
  constructor
  · intro hball q hq
    exact (d39DrawingRepresentationData3_ballDarts_iff x r q).mp
      (hball hq)
  · intro hball q hq
    exact (d39DrawingRepresentationData3_ballDarts_iff x r q).mpr
      (hball q hq)

/-- Helper toward Proposition 5.16. The ball-dart equivalence transports the
initial vertex class through the geometric ball vertex equivalence. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_map
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (q : {q : M.core.D // q ∈ d39BallDarts M r}) :
    y.vertexEquiv
        (rootedLocallyFiniteVertexClass N.core.rot
          (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e q).1) =
      (e.vertexEquiv
        ⟨x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot q.1),
          (d39DrawingRepresentationData3_ballVertices_iff x r
            (rootedLocallyFiniteVertexClass M.core.rot q.1)).mp
              (by simpa only [d39VertexClass] using
                ((mem_d39BallDarts M r q.1).mp q.2).1)⟩).1 := by
  classical
  let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
    ⟨(x.dartEquiv q.1).1,
      (d39DrawingRepresentationData3_ballDarts_iff x r q.1).mp q.2⟩
  let p := d39GeomBallIsoV2DirectedEdgeEquiv e (a, (x.dartEquiv q.1).2)
  let q' := y.dartEquiv.symm (p.1.1, p.2)
  have hpair : y.dartEquiv q' = (p.1.1, p.2) := by
    simp [q']
  change y.vertexEquiv
      (rootedLocallyFiniteVertexClass N.core.rot q') = _
  rw [y.dart_tail_vertex q', hpair]
  simp only [x.dart_tail_vertex q.1]
  have hsrc := e.src_map a
  have htgt := e.tgt_map a
  by_cases hb : (x.dartEquiv q.1).2 = true <;>
    by_cases hf : e.edgeFlip a = true <;>
    simp [a, p, d39GeomBallIsoV2DirectedEdgeEquiv, hb, hf, hsrc, htgt]

/-- Helper toward Proposition 5.16. When the source vertex star lies in the
geometric ball, the ball-dart equivalence bijects it with the target star
among target ball darts. -/
def d39DrawingRepresentationData3_geomBallIso_starBallDartEquiv
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hball : ∀ q : M.core.D,
      rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d.1 →
      (x.dartEquiv q).1 ∈ d39GeomBallEdges B.map B.root r) :
    {q : M.core.D // rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d.1} ≃
      {q : N.core.D // q ∈ d39BallDarts N r ∧
        rootedLocallyFiniteVertexClass N.core.rot q =
          rootedLocallyFiniteVertexClass N.core.rot
            (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1} := by
  classical
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  let f : {q : M.core.D //
      rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d.1} →
      {q : N.core.D // q ∈ d39BallDarts N r ∧
        rootedLocallyFiniteVertexClass N.core.rot q =
          rootedLocallyFiniteVertexClass N.core.rot (E d).1} := fun q =>
    have hqball : q.1 ∈ d39BallDarts M r := by
      apply (d39DrawingRepresentationData3_star_subset_ballDarts_iff_geomBall
        x d.1).mpr hball
      exact q.2
    let q' := E ⟨q.1, hqball⟩
    ⟨q'.1, q'.2, by
      have hq := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_map
        x y e ⟨q.1, hqball⟩
      have hd := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_map
        x y e d
      have hx : x.vertexEquiv
          (rootedLocallyFiniteVertexClass M.core.rot q.1) =
          x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d.1) :=
        congrArg x.vertexEquiv q.2
      have hvq := (d39DrawingRepresentationData3_ballVertices_iff x r
        (rootedLocallyFiniteVertexClass M.core.rot q.1)).mp
          (by simpa only [d39VertexClass] using
            ((mem_d39BallDarts M r q.1).mp hqball).1)
      have hvd := (d39DrawingRepresentationData3_ballVertices_iff x r
        (rootedLocallyFiniteVertexClass M.core.rot d.1)).mp
          (by simpa only [d39VertexClass] using
            ((mem_d39BallDarts M r d.1).mp d.2).1)
      have hsub :
          (⟨x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot q.1), hvq⟩ :
            {v : B.V // v ∈ d39GeomBallVertices B.map B.root r}) =
          ⟨x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d.1), hvd⟩ :=
        Subtype.ext hx
      have hmapped := congrArg (fun v => v.1) (congrArg e.vertexEquiv hsub)
      apply y.vertexEquiv.injective
      calc
        y.vertexEquiv (rootedLocallyFiniteVertexClass N.core.rot q'.1) =
            (e.vertexEquiv ⟨x.vertexEquiv
              (rootedLocallyFiniteVertexClass M.core.rot q.1), hvq⟩).1 := hq
        _ = (e.vertexEquiv ⟨x.vertexEquiv
              (rootedLocallyFiniteVertexClass M.core.rot d.1), hvd⟩).1 := hmapped
        _ = y.vertexEquiv
            (rootedLocallyFiniteVertexClass N.core.rot (E d).1) := hd.symm⟩
  let g : {q : N.core.D // q ∈ d39BallDarts N r ∧
      rootedLocallyFiniteVertexClass N.core.rot q =
        rootedLocallyFiniteVertexClass N.core.rot (E d).1} →
      {q : M.core.D // rootedLocallyFiniteVertexClass M.core.rot q =
        rootedLocallyFiniteVertexClass M.core.rot d.1} := fun q =>
    let q' := E.symm ⟨q.1, q.2.1⟩
    ⟨q'.1, by
      have hvq := (d39DrawingRepresentationData3_ballVertices_iff x r
        (rootedLocallyFiniteVertexClass M.core.rot q'.1)).mp
          (by simpa only [d39VertexClass] using
            ((mem_d39BallDarts M r q'.1).mp q'.2).1)
      have hvd := (d39DrawingRepresentationData3_ballVertices_iff x r
        (rootedLocallyFiniteVertexClass M.core.rot d.1)).mp
          (by simpa only [d39VertexClass] using
            ((mem_d39BallDarts M r d.1).mp d.2).1)
      let vq : {v : B.V // v ∈ d39GeomBallVertices B.map B.root r} :=
        ⟨x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot q'.1), hvq⟩
      let vd : {v : B.V // v ∈ d39GeomBallVertices B.map B.root r} :=
        ⟨x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d.1), hvd⟩
      have hqmap : y.vertexEquiv
          (rootedLocallyFiniteVertexClass N.core.rot q.1) =
          (e.vertexEquiv vq).1 := by
        simpa [E, q'] using
          (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_map
            x y e q')
      have hd : y.vertexEquiv
          (rootedLocallyFiniteVertexClass N.core.rot (E d).1) =
          (e.vertexEquiv vd).1 := by
        simpa [E] using
          (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_vertex_map
            x y e d)
      have hy := congrArg y.vertexEquiv q.2.2
      rw [hqmap, hd] at hy
      have hmapped := e.vertexEquiv.injective (Subtype.ext hy)
      exact x.vertexEquiv.injective (congrArg Subtype.val hmapped)⟩
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro q
    apply Subtype.ext
    simp [f, g, E]
  · intro q
    apply Subtype.ext
    simp [f, g, E]
















































end DirectedDistances.PaperProofs.Section5

end
