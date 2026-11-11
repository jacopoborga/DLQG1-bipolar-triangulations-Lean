module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso2

/-! # Geometric-to-combinatorial ball isomorphism helpers

Helpers toward Proposition 5.16. This file identifies the metric graph
underlying the represented combinatorial map with the geometric graph. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16. The simple graph on rotation-orbit
vertices, with adjacency given by one all-geometric dart step. -/
@[expose] def d39RepresentationVertexGraph (M : D39RootedMap) :
    SimpleGraph (RootedLocallyFiniteVertex M.core.D M.core.rot) where
  Adj v w := v ≠ w ∧ rootedLocallyFiniteGeometricStep M.core.rot M.core.edgeInv v w
  symm.symm v w h := by
    rcases h with ⟨hne, d, hdv, hdw⟩
    refine ⟨hne.symm, M.core.edgeInv d, hdw, ?_⟩
    simpa [M.core.edgeInv_invol d] using hdv
  loopless.irrefl v h := by
    exact h.1 rfl

/-- Helper toward Proposition 5.16. A drawing representation induces an
isomorphism from the combinatorial vertex graph to the geometric graph. -/
@[expose] def d39DrawingRepresentationData3_vertexGraphIso
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) :
    d39RepresentationVertexGraph M ≃g d39GeomGraph B.map where
  toEquiv := x.vertexEquiv
  map_rel_iff' := by
    intro v w
    simp only [d39GeomGraph, d39RepresentationVertexGraph]
    change d39GeomAdj B.map (x.vertexEquiv v) (x.vertexEquiv w) ↔
      (v ≠ w ∧ rootedLocallyFiniteGeometricStep M.core.rot M.core.edgeInv v w)
    constructor
    · rintro ⟨hne, e, he | he⟩
      · obtain ⟨d, hd⟩ := x.dartEquiv.surjective (e, true)
        have htail : x.vertexEquiv (d39VertexClass M d) = x.vertexEquiv v := by
          change x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) = _
          rw [x.dart_tail_vertex d, hd]
          exact he.1
        have hhead :
            x.vertexEquiv (d39VertexClass M (M.core.edgeInv d)) =
              x.vertexEquiv w := by
          change x.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) = _
          rw [x.dart_head_vertex d, hd]
          exact he.2
        exact ⟨fun h => hne (congrArg x.vertexEquiv h), d,
          x.vertexEquiv.injective htail, x.vertexEquiv.injective hhead⟩
      · obtain ⟨d, hd⟩ := x.dartEquiv.surjective (e, false)
        have htail : x.vertexEquiv (d39VertexClass M d) = x.vertexEquiv v := by
          change x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) = _
          rw [x.dart_tail_vertex d, hd]
          exact he.2
        have hhead :
            x.vertexEquiv (d39VertexClass M (M.core.edgeInv d)) =
              x.vertexEquiv w := by
          change x.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) = _
          rw [x.dart_head_vertex d, hd]
          exact he.1
        exact ⟨fun h => hne (congrArg x.vertexEquiv h), d,
          x.vertexEquiv.injective htail, x.vertexEquiv.injective hhead⟩
    · rintro ⟨hne, d, hdv, hdw⟩
      let p := x.dartEquiv d
      have htail : x.vertexEquiv v =
          if p.2 then B.map.toPlaneMapWithMissing.src p.1
          else B.map.toPlaneMapWithMissing.tgt p.1 := by
        calc
          x.vertexEquiv v =
              x.vertexEquiv (d39VertexClass M d) := congrArg x.vertexEquiv hdv.symm
          _ = if p.2 then B.map.toPlaneMapWithMissing.src p.1
              else B.map.toPlaneMapWithMissing.tgt p.1 := x.dart_tail_vertex d
      have hhead : x.vertexEquiv w =
          if p.2 then B.map.toPlaneMapWithMissing.tgt p.1
          else B.map.toPlaneMapWithMissing.src p.1 := by
        calc
          x.vertexEquiv w = x.vertexEquiv
              (d39VertexClass M (M.core.edgeInv d)) := congrArg x.vertexEquiv hdw.symm
          _ = if p.2 then B.map.toPlaneMapWithMissing.tgt p.1
              else B.map.toPlaneMapWithMissing.src p.1 := by
            change x.vertexEquiv
              (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) = _
            simpa [p] using x.dart_head_vertex d
      have hne' : x.vertexEquiv v ≠ x.vertexEquiv w :=
        fun h => hne (x.vertexEquiv.injective h)
      cases hb : p.2
      · exact ⟨hne', p.1, Or.inr ⟨by simpa [hb] using hhead.symm,
          by simpa [hb] using htail.symm⟩⟩
      · exact ⟨hne', p.1, Or.inl ⟨by simpa [hb] using htail.symm,
          by simpa [hb] using hhead.symm⟩⟩

/-- Helper toward Proposition 5.16. The representation vertex equivalence
preserves all-geometric extended graph distance, including missing edges. -/
theorem d39DrawingRepresentationData3_graphDistance_map
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (v w : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    d39GeomGraphDistance B.map (x.vertexEquiv v) (x.vertexEquiv w) =
      (d39RepresentationVertexGraph M).edist v w := by
  change (d39GeomGraph B.map).edist (x.vertexEquiv v) (x.vertexEquiv w) = _
  exact (d39DrawingRepresentationData3_vertexGraphIso x).edist_eq v w

/-- Helper toward Proposition 5.16. The represented combinatorial root
vertex is the first endpoint selected by the ordered geometric root dart. -/
theorem d39DrawingRepresentationData3_root_vertex
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) :
    x.vertexEquiv (d39VertexClass M M.rootMark.dart) =
      d39GeomRootVertex B.map B.root := by
  change x.vertexEquiv
      (rootedLocallyFiniteVertexClass M.core.rot M.rootMark.dart) = _
  rw [x.dart_tail_vertex, x.root_mark]
  rfl

/-- Helper toward Proposition 5.16. The inductive combinatorial radius
predicate is exactly the closed ball in the representation vertex graph. -/
theorem d39WithinRadius_iff_representationVertexGraph_edist_le
    (M : D39RootedMap) (r : ℕ)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    D39WithinRadius M r v ↔
      (d39RepresentationVertexGraph M).edist
        (d39VertexClass M M.rootMark.dart) v ≤ (r : ℕ∞) := by
  let G := d39RepresentationVertexGraph M
  constructor
  · intro h
    induction h with
    | root => simp [G, d39RepresentationVertexGraph]
    | @stay r v h ih =>
        exact le_trans ih (by exact_mod_cast (Nat.le_succ r))
    | @edge r v w hv hstep ih =>
        by_cases hvw : v = w
        · subst w
          exact le_trans ih (by exact_mod_cast (Nat.le_succ r))
        · have hadj : G.Adj v w := ⟨hvw, hstep⟩
          have hdist : G.edist v w ≤ (1 : ℕ∞) :=
            le_of_eq (G.edist_eq_one_iff_adj.mpr hadj)
          calc
            G.edist (d39VertexClass M M.rootMark.dart) w ≤
                G.edist (d39VertexClass M M.rootMark.dart) v + G.edist v w :=
              G.edist_triangle
            _ ≤ (r : ℕ∞) + 1 := add_le_add ih hdist
            _ = ((r + 1 : ℕ) : ℕ∞) := by simp
  · intro h
    induction r generalizing v with
    | zero =>
        have hzero : G.edist (d39VertexClass M M.rootMark.dart) v = 0 :=
          le_antisymm h bot_le
        have hv := G.edist_eq_zero_iff.mp hzero
        subst v
        exact .root
    | succ r ih =>
        have hne : G.edist (d39VertexClass M M.rootMark.dart) v ≠ ⊤ := by
          apply ne_of_lt
          exact lt_of_le_of_lt h (by simp)
        obtain ⟨p, hp⟩ :=
          (G.edist_ne_top_iff_reachable.mp hne).exists_walk_length_eq_edist
        have hplen : p.length ≤ r + 1 := by
          have hcast : (p.length : ℕ∞) ≤ ((r + 1 : ℕ) : ℕ∞) := by
            rw [hp]
            exact h
          exact_mod_cast hcast
        cases hrev : p.reverse with
        | nil =>
            exact D39WithinRadius.stay (ih _ (by simp [G]))
        | @cons a b c hab q =>
            have hlen : q.length + 1 = p.length := by
              have h := congrArg SimpleGraph.Walk.length hrev
              simpa [SimpleGraph.Walk.length_reverse,
                SimpleGraph.Walk.length_cons] using h.symm
            have hq : q.length ≤ r := by omega
            have hdb : G.edist (d39VertexClass M M.rootMark.dart) b ≤ (r : ℕ∞) := by
              calc
                G.edist (d39VertexClass M M.rootMark.dart) b ≤
                    (q.reverse.length : ℕ∞) := G.edist_le _
                _ = (q.length : ℕ∞) := by exact_mod_cast SimpleGraph.Walk.length_reverse q
                _ ≤ (r : ℕ∞) := by exact_mod_cast hq
            have hb := ih b hdb
            have hba : G.Adj b v := by
              have hab' : G.Adj v b := by simpa using hab
              change v ≠ b ∧ rootedLocallyFiniteGeometricStep
                M.core.rot M.core.edgeInv v b at hab'
              rcases hab' with ⟨hne, hstep⟩
              refine ⟨hne.symm, ?_⟩
              rcases hstep with ⟨d, hdv, hdb⟩
              refine ⟨M.core.edgeInv d, hdb, ?_⟩
              simpa [d39VertexClass, M.core.edgeInv_invol d] using hdv
            exact D39WithinRadius.edge hb hba.2

/-- Helper toward Proposition 5.16. Combinatorial and geometric radius-r
vertex balls agree under the representation vertex equivalence. -/
theorem d39DrawingRepresentationData3_ballVertices_iff
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (r : ℕ)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    v ∈ d39BallVertices M r ↔
      x.vertexEquiv v ∈ d39GeomBallVertices B.map B.root r := by
  rw [mem_d39BallVertices, d39WithinRadius_iff_representationVertexGraph_edist_le]
  change (d39RepresentationVertexGraph M).edist
      (d39VertexClass M M.rootMark.dart) v ≤ (r : ℕ∞) ↔
    d39GeomGraphDistance B.map (d39GeomRootVertex B.map B.root)
      (x.vertexEquiv v) ≤ (r : ℕ∞)
  rw [← d39DrawingRepresentationData3_graphDistance_map x,
    d39DrawingRepresentationData3_root_vertex]

/-- Helper toward Proposition 5.16. A dart lies in the combinatorial ball
exactly when its geometric edge identity has both endpoints in the geometric
ball; missing edge identities are included on both sides. -/
theorem d39DrawingRepresentationData3_ballDarts_iff
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (r : ℕ) (d : M.core.D) :
    d ∈ d39BallDarts M r ↔
      (x.dartEquiv d).1 ∈ d39GeomBallEdges B.map B.root r := by
  rw [mem_d39BallDarts,
    d39DrawingRepresentationData3_ballVertices_iff x r (d39VertexClass M d),
    d39DrawingRepresentationData3_ballVertices_iff x r
      (d39VertexClass M (M.core.edgeInv d))]
  change
    (x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) ∈
        d39GeomBallVertices B.map B.root r ∧
      x.vertexEquiv
        (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) ∈
        d39GeomBallVertices B.map B.root r) ↔
    (B.map.toPlaneMapWithMissing.src (x.dartEquiv d).1 ∈
        d39GeomBallVertices B.map B.root r ∧
      B.map.toPlaneMapWithMissing.tgt (x.dartEquiv d).1 ∈
        d39GeomBallVertices B.map B.root r)
  rw [x.dart_tail_vertex d, x.dart_head_vertex d]
  cases hb : (x.dartEquiv d).2 <;> simp [hb, and_comm]

/-- Helper toward Proposition 5.16. A geometric ball isomorphism and two
representations induce an equivalence of the actual combinatorial ball darts. -/
@[expose] def d39DrawingRepresentationData3_geomBallIso_ballDartEquiv
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    {d : M.core.D // d ∈ d39BallDarts M r} ≃
      {d : N.core.D // d ∈ d39BallDarts N r} := by
  let i := d39GeomBallIsoV2RepresentationDartEquiv x y e
  refine
    { toFun := fun d =>
        let q := i ⟨d.1, (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩
        ⟨q.1, (d39DrawingRepresentationData3_ballDarts_iff y r q.1).mpr q.2⟩
      invFun := fun d =>
        let q := i.symm
          ⟨d.1, (d39DrawingRepresentationData3_ballDarts_iff y r d.1).mp d.2⟩
        ⟨q.1, (d39DrawingRepresentationData3_ballDarts_iff x r q.1).mpr q.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro d
    apply Subtype.ext
    dsimp
    exact congrArg Subtype.val (i.left_inv
      ⟨d.1, (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩)
  · intro d
    apply Subtype.ext
    dsimp
    exact congrArg Subtype.val (i.right_inv
      ⟨d.1, (d39DrawingRepresentationData3_ballDarts_iff y r d.1).mp d.2⟩)

















































end DirectedDistances.PaperProofs.Section5

end
