/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedComparison

/-! Discrete geometric ball correspondences retain edge identities, missing tags, -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

namespace ExteriorMarkedComparison2

/-- Helper toward Proposition 5.16: a represented ball dart is exactly a
geometric ball edge together with its stored traversal direction. -/
@[expose] def ballDartEquiv {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (r : ℕ) (hr : 0 < r) :
    (d39FacedBall M r hr).D ≃
      ({e // e ∈ d39GeomBallEdges B.map B.root r} × Bool) where
  toFun d := (⟨(x.dartEquiv d.1).1,
    (d39DrawingRepresentationData_ballDarts_iff x r d.1).mp d.2⟩,
      (x.dartEquiv d.1).2)
  invFun e := ⟨x.dartEquiv.symm (e.1.1, e.2),
    (d39DrawingRepresentationData_ballDarts_iff x r _).mpr (by
      rw [x.dartEquiv.apply_symm_apply]; exact e.1.2)⟩
  left_inv := by intro d; apply Subtype.ext; exact x.dartEquiv.symm_apply_apply d.1
  right_inv := by
    rintro ⟨⟨e, he⟩, b⟩
    simp only [Equiv.apply_symm_apply]

/-- Helper toward Proposition 5.16: the dart identification commutes with
edge reversal even for missing geometric edges. -/
theorem ballDartEquiv_flip {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D) :
    ballDartEquiv x r hr ((d39FacedBall M r hr).map.edgeInv d) =
      ((ballDartEquiv x r hr d).1, !(ballDartEquiv x r hr d).2) := by
  apply Prod.ext
  · apply Subtype.ext
    have h := congrArg (fun z : B.E × Bool => z.1) (x.dart_edgeInv d.1)
    exact h
  · exact congrArg (fun z : B.E × Bool => z.2) (x.dart_edgeInv d.1)

/-- Helper toward Proposition 5.16: a reversal-compatible bijection of
ordered edges has a uniquely determined edge map and flip bit. -/
theorem orderedEdgeEquiv_apply {E F : Type*} (f : E × Bool ≃ F × Bool)
    (hf : ∀ e b, f (e, !b) = ((f (e, b)).1, !(f (e, b)).2))
    (e : E) (b : Bool) :
    f (e, b) = ((f (e, true)).1, Bool.xor b (!(f (e, true)).2)) := by
  cases b
  · simpa only [Bool.not_true, Bool.false_xor] using hf e true
  · simp only [Bool.true_xor, Bool.not_not, Prod.mk.eta]

/-- Helper toward Proposition 5.16: descend a reversal-compatible ordered
edge bijection to the actual edge identities, without collapsing multiedges. -/
@[expose] def orderedEdgeEquiv {E F : Type*} (f : E × Bool ≃ F × Bool)
    (hf : ∀ e b, f (e, !b) = ((f (e, b)).1, !(f (e, b)).2)) : E ≃ F :=
  Equiv.ofBijective (fun e => (f (e, true)).1) (by
    constructor
    · intro e k he
      by_cases hb : (f (e, true)).2 = (f (k, true)).2
      · exact congrArg Prod.fst (f.injective (Prod.ext he hb))
      · have hb' : (f (e, true)).2 = !(f (k, true)).2 := by
          cases h₁ : (f (e, true)).2 <;> cases h₂ : (f (k, true)).2 <;>
            simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
              Bool.true_eq_false, not_false_eq_true, not_true_eq_false]
        have h : f (e, true) = f (k, false) := by
          rw [orderedEdgeEquiv_apply f hf k false]
          exact Prod.ext he (by simpa only [Bool.false_xor] using hb')
        exact congrArg Prod.fst (f.injective h)
    · intro k
      obtain ⟨⟨e, b⟩, he⟩ := f.surjective (k, true)
      refine ⟨e, ?_⟩
      rw [orderedEdgeEquiv_apply f hf e b] at he
      exact congrArg Prod.fst he)

/-- Helper toward Proposition 5.16: a combinatorial ball isomorphism acts
on the geometric ordered edges through the two representations. -/
@[expose] def dartMap {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (y : D39DrawingRepresentationData N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) :
    ({e // e ∈ d39GeomBallEdges B.map B.root r} × Bool) ≃
      ({e // e ∈ d39GeomBallEdges C.map C.root r} × Bool) :=
  (ballDartEquiv x r hr).symm.trans (I.toEquiv.trans (ballDartEquiv y r hr))

/-- Helper toward Proposition 5.16: conjugating a ball isomorphism by
representation bijections preserves ordered-edge reversal. -/
theorem dartMap_flip {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (y : D39DrawingRepresentationData N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (e : {e // e ∈ d39GeomBallEdges B.map B.root r}) (b : Bool) :
    dartMap x y r hr I (e, !b) =
      ((dartMap x y r hr I (e, b)).1, !(dartMap x y r hr I (e, b)).2) := by
  let d := (ballDartEquiv x r hr).symm (e, b)
  have hd : ballDartEquiv x r hr d = (e, b) := Equiv.apply_symm_apply _ _
  have hf := ballDartEquiv_flip x r hr d
  rw [hd] at hf
  change ballDartEquiv y r hr (I.toEquiv ((ballDartEquiv x r hr).symm (e, !b))) = _
  rw [← hf, Equiv.symm_apply_apply, I.edgeInv_comm, ballDartEquiv_flip]
  rfl

/-- Helper toward Proposition 5.16: the incident vertices of the restricted
PL drawing are precisely the represented geometric ball vertices. -/
@[expose] def ballVertexEquiv {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M)) (r : ℕ) (hr : 0 < r) :
    RestrictedVertex P (d39BallDarts M r : Set M.core.D) ≃
      {v // v ∈ d39GeomBallVertices B.map B.root r} where
  toFun v := ⟨x.vertexEquiv v.1,
    (D39DrawingRepresentationData.ballVertices_iff x r v.1).mpr
      ((d39FacedBallPLDrawing_vertex_mem_iff M r hr v.1).mp v.2)⟩
  invFun v := ⟨x.vertexEquiv.symm v.1,
    (d39FacedBallPLDrawing_vertex_mem_iff M r hr _).mpr
      ((D39DrawingRepresentationData.ballVertices_iff x r _).mp (by rw [Equiv.apply_symm_apply]; exact v.2))⟩
  left_inv := by intro v; apply Subtype.ext; exact x.vertexEquiv.symm_apply_apply v.1
  right_inv := by intro v; apply Subtype.ext; exact x.vertexEquiv.apply_symm_apply v.1

/-- Helper toward Proposition 5.16: a faced ball isomorphism induces the
geometric vertex bijection through the restricted drawings. -/
@[expose] def vertexMap {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (y : D39DrawingRepresentationData N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N)) (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) :
    {v // v ∈ d39GeomBallVertices B.map B.root r} ≃
      {v // v ∈ d39GeomBallVertices C.map C.root r} :=
  (ballVertexEquiv x P r hr).symm.trans
    ((plBallVertexEquiv I _ _ (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing N Q r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective N Q r hr)).trans
        (ballVertexEquiv y Q r hr))

/-- Helper toward Proposition 5.16: the vertex map preserves the initial
vertex of each retained dart. -/
theorem vertexMap_dart {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (y : D39DrawingRepresentationData N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N)) (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (d : (d39FacedBall M r hr).D) :
    (vertexMap x y P Q r hr I
      (ballVertexEquiv x P r hr (restrictedVertex P (d39BallDarts M r) d))).1 =
        y.vertexEquiv (d39VertexClass N (I.toEquiv d).1) := by
  change (ballVertexEquiv y Q r hr
    (plBallVertexEquiv I _ _ _ _ _ _
      ((ballVertexEquiv x P r hr).symm
        (ballVertexEquiv x P r hr (restrictedVertex P (d39BallDarts M r) d))))).1 = _
  rw [Equiv.symm_apply_apply]
  rw [plBallVertexEquiv_apply I _ _ (d39FacedBallPLDrawing M P r hr)
    (d39FacedBallPLDrawing N Q r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective N Q r hr) d]
  rfl


section Correspondence
variable {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
  (x : D39DrawingRepresentationData M B) (y : D39DrawingRepresentationData N C)
  (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
    M.core.edgeInv M.core.rot (d39VertexClass M))
  (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
    N.core.edgeInv N.core.rot (d39VertexClass N)) (r : ℕ) (hr : 0 < r)
  (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))

/-- Helper toward Proposition 5.16: the vertex correspondence respects both
stored endpoints of every geometric edge. -/
theorem vertexMap_endpoint
    (e : {e // e ∈ d39GeomBallEdges B.map B.root r}) (b : Bool) :
    (vertexMap x y P Q r hr I
      (if b then ⟨B.map.toPlaneMapWithMissing.src e.1, e.2.1⟩
        else ⟨B.map.toPlaneMapWithMissing.tgt e.1, e.2.2⟩)).1 =
      if (dartMap x y r hr I (e, b)).2 then
        C.map.toPlaneMapWithMissing.src (dartMap x y r hr I (e, b)).1.1
      else C.map.toPlaneMapWithMissing.tgt (dartMap x y r hr I (e, b)).1.1 := by
  let d := (ballDartEquiv x r hr).symm (e, b)
  have hx : x.dartEquiv d.1 = (e.1, b) := x.dartEquiv.apply_symm_apply _
  have hv : ballVertexEquiv x P r hr
      (restrictedVertex P (d39BallDarts M r) d) =
      if b then ⟨B.map.toPlaneMapWithMissing.src e.1, e.2.1⟩
        else ⟨B.map.toPlaneMapWithMissing.tgt e.1, e.2.2⟩ := by
    apply Subtype.ext
    have ht := x.dart_tail_vertex d.1
    rw [hx] at ht
    cases b <;> exact ht
  rw [← hv, vertexMap_dart]
  exact y.dart_tail_vertex (I.toEquiv d).1

/-- Helper toward Proposition 5.16: construct all discrete geometric ball
fields from the represented faced ball isomorphism and a retained-face
bijection. The face-image equation is supplied separately by plane transport. -/
@[expose] def correspondence
    (E : {F // F ∈ d39GeomRetainedFaces B.map B.root r} ≃
      {F // F ∈ d39GeomRetainedFaces C.map C.root r}) :
    D39GeomBallCorrespondenceV2 r B C := by
  let f := dartMap x y r hr I
  have hf := dartMap_flip x y r hr I
  let g := orderedEdgeEquiv f hf
  have happ (e) (b) : f (e, b) = (g e, Bool.xor b (!(f (e, true)).2)) :=
    orderedEdgeEquiv_apply f hf e b
  have hmissing (e) :
      C.map.toPlaneMapWithMissing.missing (g e).1 ↔
        B.map.toPlaneMapWithMissing.missing e.1 := by
    let d := (ballDartEquiv x r hr).symm (e, true)
    have hx : x.dartEquiv d.1 = (e.1, true) := x.dartEquiv.apply_symm_apply _
    have hy := y.dart_missing (I.toEquiv d).1
    have hi := I.missing_iff d
    have hm := x.dart_missing d.1
    rw [hx] at hm
    exact hy.trans (hi.trans hm.symm)
  have hroot : f (⟨B.root.1, d39GeomRootEdge_mem B.map B.root hr⟩, B.root.2) =
      (⟨C.root.1, d39GeomRootEdge_mem C.map C.root hr⟩, C.root.2) := by
    have hx : ballDartEquiv x r hr (d39FacedBall M r hr).rootDart =
        (⟨B.root.1, d39GeomRootEdge_mem B.map B.root hr⟩, B.root.2) := by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst x.root_mark
      · exact congrArg (fun z : B.E × Bool => z.2) x.root_mark
    rw [← hx]
    change ballDartEquiv y r hr
      (I.toEquiv ((ballDartEquiv x r hr).symm
        (ballDartEquiv x r hr (d39FacedBall M r hr).rootDart))) = _
    rw [Equiv.symm_apply_apply, I.root_comm]
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst y.root_mark
    · exact congrArg (fun z : C.E × Bool => z.2) y.root_mark
  refine {
    radius_pos := hr
    vertexEquiv := vertexMap x y P Q r hr I
    edgeEquiv := g
    faceEquiv := E
    edgeFlip := fun e => !(f (e, true)).2
    src_map := ?_
    tgt_map := ?_
    missing_map := hmissing
    orientation_map := ?_
    root_edge_map := ?_
    root_bool_map := ?_ }
  · intro e
    have hv := vertexMap_endpoint x y P Q r hr I e true
    change _ = if (f (e, true)).2 then C.map.toPlaneMapWithMissing.src (g e).1
      else C.map.toPlaneMapWithMissing.tgt (g e).1 at hv
    cases hb : (f (e, true)).2 <;>
      simpa only [hb, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true] using hv
  · intro e
    have hv := vertexMap_endpoint x y P Q r hr I e false
    change _ = if (f (e, false)).2 then _ else _ at hv
    rw [happ e false] at hv
    cases hb : (f (e, true)).2 <;>
      simpa only [hb, Bool.not_false, Bool.not_true, Bool.false_xor,
        Bool.false_eq_true, ite_false, ite_true] using hv
  · intro e he
    let d := (ballDartEquiv x r hr).symm (e, true)
    have hx : x.dartEquiv d.1 = (e.1, true) := x.dartEquiv.apply_symm_apply _
    have hd : ¬ M.core.missing d.1 := by
      have hm := x.dart_missing d.1
      rw [hx] at hm
      exact hm.not.mp he
    have hId : ¬ N.core.missing (I.toEquiv d).1 := (I.missing_iff d).not.mpr hd
    have ht := (y.dart_orientation (I.toEquiv d).1 hId).symm.trans
      ((I.tail_iff d).trans (x.dart_orientation d.1 hd))
    have hxe : (x.dartEquiv d.1).1 = e.1 := congrArg Prod.fst hx
    have hxb : (x.dartEquiv d.1).2 = true := congrArg Prod.snd hx
    simp only [hxe, hxb] at ht
    change (C.map.forward ⟨(g e).1, _⟩ = (f (e, true)).2 ↔
      B.map.forward ⟨e.1, he⟩ = true) at ht
    cases hB : B.map.forward ⟨e.1, he⟩ <;>
      cases hC : C.map.forward ⟨(g e).1, _⟩ <;>
      cases hb : (f (e, true)).2 <;>
      simp only [hB, hC, hb, Bool.not_false, Bool.not_true, Bool.xor_false,
        Bool.xor_true, Bool.false_eq_true, Bool.true_eq_false, iff_true, iff_false,
        not_true_eq_false] at ht ⊢
  · have h := congrArg (fun z => z.1.1) hroot
    rw [happ] at h
    exact h
  · have h := congrArg Prod.snd hroot
    rw [happ] at h
    exact h.symm

end Correspondence


/-- Helper toward Proposition 5.16: a reparameterized PL representation
preserves each complete edge range, independently of its stored direction. -/
theorem reparam_arc_range {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (harc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval,
      ∀ t, d39DrawingDartArc B x d t = (P.arc d).toPath (φ t))
    (d : M.core.D) :
    Set.range (P.arc d).toPath =
      Set.range (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1) := by
  obtain ⟨φ, hφ⟩ := harc d
  have heq : Set.range (P.arc d).toPath = Set.range (d39DrawingDartArc B x d) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨φ.symm t, by rw [hφ, φ.apply_symm_apply]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨φ t, (hφ t).symm⟩
  rw [heq]
  unfold d39DrawingDartArc
  split
  · rfl
  · exact Path.symm_range _

/-- Helper toward Proposition 5.16: endpoint-preserving reparameterizations
of the simple PL dart arcs exclude geometric loops as a proved consequence. -/
theorem reparam_src_ne_tgt {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (harc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x d t = (P.arc d).toPath (φ t))
    (e : B.E) :
    B.map.toPlaneMapWithMissing.src e ≠ B.map.toPlaneMapWithMissing.tgt e := by
  intro he
  let d := x.dartEquiv.symm (e, true)
  have hd : x.dartEquiv d = (e, true) := x.dartEquiv.apply_symm_apply _
  obtain ⟨φ, h0, h1, hφ⟩ := harc d
  have hs := hφ 0
  have ht := hφ 1
  simp only [d39DrawingDartArc, hd, ite_true, Path.source, h0] at hs
  simp only [d39DrawingDartArc, hd, ite_true, Path.target, h1] at ht
  exact zero_ne_one ((P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d)
    (by simpa only [Path.source, Path.target] using
      (hs.symm.trans ((congrArg B.map.toPlaneMapWithMissing.pos he).trans ht))))


/-- Helper toward Proposition 5.16: initial-point equality of the represented
PL paths already forces the full vertex-position compatibility. -/
theorem pos_eq_of_reparam {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (harc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x d t = (P.arc d).toPath (φ t))
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v) := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep v
  obtain ⟨φ, h0, _, hφ⟩ := harc d
  have h := hφ 0
  rw [h0, Path.source, P.arc_start] at h
  have ht := x.dart_tail_vertex d
  cases hb : (x.dartEquiv d).2 <;>
    simp only [d39DrawingDartArc, hb, Bool.false_eq_true, ite_false, ite_true,
      Path.source] at h ht
  · exact h.symm.trans (congrArg B.map.toPlaneMapWithMissing.pos ht.symm)
  · exact h.symm.trans (congrArg B.map.toPlaneMapWithMissing.pos ht.symm)

end ExteriorMarkedComparison2

/-- Helper toward Proposition 5.16: equality of the exterior-marked balls
of two reparameterized PL representations gives the full geometric ball
isomorphism, including every retained ambient face and missing-edge tag. -/
theorem exteriorMarkedComparison_reparam_geomBallIso
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (hPpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (hQpos : ∀ v, Q.pos v = C.map.toPlaneMapWithMissing.pos (y.vertexEquiv v))
    (hParc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
        (P.arc d).toPath (φ t))
    (hQarc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc C y.toD39DrawingRepresentationData d t =
        (Q.arc d).toPath (φ t))
    (r : ℕ) (hr : 0 < r)
    (hxy : Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q r hr)) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) := by
  obtain ⟨I, H, E, hH, hp, ha, hf⟩ :=
    exteriorMarkedComparison_reparam_retainedFaceEquiv
      x y P Q hPpos hQpos hParc hQarc r hr hxy
  let c := ExteriorMarkedComparison2.correspondence
    x.toD39DrawingRepresentationData y.toD39DrawingRepresentationData P Q r hr
    I.toD39BallIso E
  refine ⟨c.toGeomBallIsoOfNoLoops
    (fun e => ExteriorMarkedComparison2.reparam_src_ne_tgt
      x.toD39DrawingRepresentationData P hParc e.1)
    (fun e => ExteriorMarkedComparison2.reparam_src_ne_tgt
      y.toD39DrawingRepresentationData Q hQarc e.1) H hH ?_ ?_ hf⟩
  · intro v
    obtain ⟨w, rfl⟩ := (ExteriorMarkedComparison2.ballVertexEquiv
      x.toD39DrawingRepresentationData P r hr).surjective v
    obtain ⟨d, rfl⟩ := d39FacedBallPLDrawing_vertex_surjective M P r hr w
    change H (B.map.toPlaneMapWithMissing.pos
      (x.vertexEquiv (d39VertexClass M d.1))) =
        C.map.toPlaneMapWithMissing.pos
          (ExteriorMarkedComparison2.vertexMap
            x.toD39DrawingRepresentationData y.toD39DrawingRepresentationData
            P Q r hr I.toD39BallIso
            (ExteriorMarkedComparison2.ballVertexEquiv x.toD39DrawingRepresentationData
              P r hr (restrictedVertex P (d39BallDarts M r) d))).1
    rw [ExteriorMarkedComparison2.vertexMap_dart x.toD39DrawingRepresentationData
      y.toD39DrawingRepresentationData P Q r hr I.toD39BallIso d]
    have h := hp d
    rw [hPpos, hQpos] at h
    exact h
  · intro e
    let d := (ExteriorMarkedComparison2.ballDartEquiv
      x.toD39DrawingRepresentationData r hr).symm (e, true)
    have hx : x.dartEquiv d.1 = (e.1, true) := x.dartEquiv.apply_symm_apply _
    have hpRange := ExteriorMarkedComparison2.reparam_arc_range
      x.toD39DrawingRepresentationData P
      (fun d => by obtain ⟨φ, _, _, hφ⟩ := hParc d; exact ⟨φ, hφ⟩) d.1
    have hqRange := ExteriorMarkedComparison2.reparam_arc_range
      y.toD39DrawingRepresentationData Q
      (fun d => by obtain ⟨φ, _, _, hφ⟩ := hQarc d; exact ⟨φ, hφ⟩)
      (I.toD39BallIso.toEquiv d).1
    rw [hx] at hpRange
    change H '' Set.range (B.map.toPlaneMapWithMissing.arc e.1) =
      Set.range (C.map.toPlaneMapWithMissing.arc
        (y.dartEquiv (I.toD39BallIso.toEquiv d).1).1)
    rw [← hpRange, ← hqRange]
    obtain ⟨φ, _, hφ⟩ := ha d
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨φ t, (hφ t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(P.arc d.1).toPath (φ.symm t), ⟨φ.symm t, rfl⟩,
        by rw [hφ, φ.apply_symm_apply]⟩


open DirectedDistances.KMSW unitInterval

/-- Helper toward Proposition 5.16: retain the canonical Data3 construction's
exact dart identification, needed to match its source assembly drawing. -/
theorem exteriorMarkedComparison_canonical_data3_with_dartEquiv
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
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0)
      (iso : D39RootedMapIso
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap M)
      (data : D39DrawingRepresentationData3 M B),
      data.dartEquiv = iso.toEquiv.symm.trans
        (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
          P hp ha F hf hFim hFa) := by
  classical
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
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  obtain ⟨hhit, C₀, iso, base, hbase, hface, hsuccessor⟩ :=
    uibhbotD39CanonicalAssembly_rotation_topological_successor_with_face W hW D
  let faceEquiv := uibhbotD39CanonicalAssembly_faceOrbitEquiv' W D hhit C₀ iso
  let E := iso.toEquiv.symm.trans
    (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa)
  have hvertex (d : M.core.D) :
      base.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) =
        wholePlaneDartVertex W (iso.toEquiv.symm d) := by
    have htail := base.dart_tail_vertex d
    rw [congrArg (fun f => f d) hbase] at htail
    calc
      base.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) =
          if (E d).2 then B.map.toPlaneMapWithMissing.src (E d).1
          else B.map.toPlaneMapWithMissing.tgt (E d).1 := htail
      _ = boundaryDartInitial B.map (E d) :=
        (boundaryDartInitial_eq (M := B.map) (E d)).symm
      _ = wholePlaneDartVertex W (iso.toEquiv.symm d) := by
        change boundaryDartInitial
            (uibhbotAssemblyDirectedPlaneMapWithMissing W D.rotation D.boundary
              D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
              P hp ha F hf hFim hFa D.pastRightPositive)
            (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
              D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
              P hp ha F hf hFim hFa (iso.toEquiv.symm d)) = _
        exact uibhbotAssemblyBoundaryDartEquiv3_initialVertex
          W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
          D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive
          (iso.toEquiv.symm d)
  have hcycles (d : M.core.D)
      (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
      (∃ e : M.core.D,
        Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
          rootedLocallyFiniteVertexClass M.core.rot e = v) ↔
      (∃ e : WholePlaneDart W,
        (wholePlaneFaceSucc W D.rotation).SameCycle (iso.toEquiv.symm d) e ∧
          wholePlaneDartVertex W e = base.vertexEquiv v) := by
    constructor
    · rintro ⟨e, hcycle, hvertex'⟩
      refine ⟨iso.toEquiv.symm e, ?_, ?_⟩
      · have hcode : Equiv.Perm.SameCycle
            (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot.symm *
              ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.edgeInv)
            (iso.toEquiv (iso.toEquiv.symm d)) (iso.toEquiv (iso.toEquiv.symm e)) := by
          simpa [M] using hcycle
        have hwhole := (iso.faceSameCycle_iff (iso.toEquiv.symm d)
          (iso.toEquiv.symm e)).mpr hcode
        change (wholePlaneFaceSucc W D.rotation).SameCycle
          (iso.toEquiv.symm d) (iso.toEquiv.symm e) at hwhole
        exact hwhole
      · calc
          wholePlaneDartVertex W (iso.toEquiv.symm e) =
              base.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot e) :=
                (hvertex e).symm
          _ = base.vertexEquiv v := congrArg base.vertexEquiv hvertex'
    · rintro ⟨e, hcycle, hvertex'⟩
      refine ⟨iso.toEquiv e, ?_, ?_⟩
      · have hwhole : Equiv.Perm.SameCycle
            (((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.rot.symm *
              ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.edgeInv)
            (iso.toEquiv.symm d) e := by
          change (wholePlaneFaceSucc W D.rotation).SameCycle
            (iso.toEquiv.symm d) e
          exact hcycle
        have hcode := (iso.faceSameCycle_iff (iso.toEquiv.symm d) e).mp hwhole
        simpa only [Equiv.apply_symm_apply, M] using hcode
      · apply base.vertexEquiv.injective
        calc
          base.vertexEquiv
              (rootedLocallyFiniteVertexClass M.core.rot (iso.toEquiv e)) =
              wholePlaneDartVertex W e := by
                have hv := hvertex (iso.toEquiv e)
                exact hv.trans (congrArg (wholePlaneDartVertex W)
                  (Equiv.symm_apply_apply iso.toEquiv e))
          _ = base.vertexEquiv v := hvertex'
  have hfrontier : ∀ (d : M.core.D)
      (v : RootedLocallyFiniteVertex M.core.D M.core.rot),
      B.map.toPlaneMapWithMissing.pos (base.vertexEquiv v) ∈
          frontier (base.faceOfDart d).val ↔
        ∃ e : M.core.D,
          Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
            rootedLocallyFiniteVertexClass M.core.rot e = v := by
    intro d v
    have hassembly := uibhbotD39Assembly_vertex_frontier_iff_faceCycle W D
      (iso.toEquiv.symm d) (base.vertexEquiv v)
    have hfrontier' : B.map.toPlaneMapWithMissing.pos (base.vertexEquiv v) ∈
        frontier (base.faceOfDart d).val ↔
      ∃ e : WholePlaneDart W,
        (wholePlaneFaceSucc W D.rotation).SameCycle (iso.toEquiv.symm d) e ∧
          wholePlaneDartVertex W e = base.vertexEquiv v := by
      change G.pos (base.vertexEquiv v) ∈
        frontier (base.faceOfDart d).val ↔ _
      rw [hface d, uibhbotD39CanonicalAssembly_faceOrbitEquiv'_mk
        W D hhit C₀ iso d]
      exact hassembly
    exact hfrontier'.trans (hcycles d v).symm
  let data : D39DrawingRepresentationData3 M B :=
    { toD39DrawingRepresentationData := base
      rotation_topological_successor := hsuccessor
      vertex_frontier_incidence := hfrontier }
  exact ⟨hhit, C₀, iso, data, hbase⟩


/-- Helper toward Proposition 5.16: canonical vertex rotation classes are
exactly the whole-plane vertices. -/
theorem exteriorMarkedComparison_wholePlaneVertexClass_eq_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d e : WholePlaneDart W) :
    rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d =
        rootedLocallyFiniteVertexClass (wholePlaneRotation W H) e ↔
      wholePlaneDartVertex W d = wholePlaneDartVertex W e := by
  constructor
  · intro h
    exact (wholePlaneRotation_sameCycle_dartVertex W H d e
      (Quotient.exact h)).symm
  · intro h
    exact Quotient.sound
      (wholePlaneRotation_sameVertex_sameCycle_proof W H d e h)


/-- Helper toward Proposition 5.16: expose the canonical assembly drawing
reindexed on its own rotation-class vertices, preserving all polylines. -/
@[expose] def exteriorMarkedComparison_canonicalDrawing
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) :
    PLDrawing
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.D
      (RootedLocallyFiniteVertex
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.D
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.rot)
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.edgeInv
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.rot
      (d39VertexClass
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)) := by
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P0 := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F0 := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P0 hp ha F0 hf hFim hFa
  have hrep (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
      d39VertexClass M (Quotient.out v) = v := Quotient.out_eq' v
  have hvertex (d : M.core.D) :
      wholePlaneDartVertex W (Quotient.out (d39VertexClass M d)) =
        wholePlaneDartVertex W d :=
    (exteriorMarkedComparison_wholePlaneVertexClass_eq_iff W D.rotation _ _).mp (hrep _)
  have hclass {v w : RootedLocallyFiniteVertex M.core.D M.core.rot}
      (hv : wholePlaneDartVertex W (Quotient.out v) =
        wholePlaneDartVertex W (Quotient.out w)) : v = w := by
    calc
      v = d39VertexClass M (Quotient.out v) := (hrep v).symm
      _ = d39VertexClass M (Quotient.out w) :=
        (exteriorMarkedComparison_wholePlaneVertexClass_eq_iff W D.rotation _ _).mpr hv
      _ = w := hrep w
  refine
    { flip_involutive := M.core.edgeInv_invol
      flip_ne := M.core.edgeInv_ne
      vert_rotation := by
        intro d
        change rootedLocallyFiniteVertexClass M.core.rot (M.core.rot d) = _
        exact Quotient.sound ⟨-1, by simp⟩
      pos := fun v => G.pos (wholePlaneDartVertex W (Quotient.out v))
      pos_injective := by
        intro v w hvw
        apply hclass
        exact G.pos_injective hvw
      arc := G.arc
      arc_simple := G.arc_simple
      arc_length := G.arc_length
      arc_start := by
        intro d
        change (G.arc d).start =
          G.pos (wholePlaneDartVertex W (Quotient.out (d39VertexClass M d)))
        rw [hvertex d]
        exact G.arc_start d
      arc_finish := by
        intro d
        change (G.arc d).finish =
          G.pos (wholePlaneDartVertex W
            (Quotient.out (d39VertexClass M (M.core.edgeInv d))))
        rw [hvertex (M.core.edgeInv d)]
        exact G.arc_finish d
      arc_flip := by
        intro d
        change G.arc (wholePlaneDartFlip W d) = (G.arc d).reverse
        exact G.arc_flip d
      interior_disjoint := G.interior_disjoint
      interior_avoids_vertices := by
        intro d v
        exact G.interior_avoids_vertices d (wholePlaneDartVertex W (Quotient.out v))
      locally_finite := G.locally_finite
      initial_nonzero := G.initial_nonzero
      initial_arg_injective := by
        intro d e hv harg
        apply G.initial_arg_injective d e ?_ harg
        exact (exteriorMarkedComparison_wholePlaneVertexClass_eq_iff W D.rotation d e).mp hv
      rotation_agreement := by
        intro d
        have hstar :
            {e : M.core.D | d39VertexClass M e = d39VertexClass M d} =
            {e | wholePlaneDartVertex W e = wholePlaneDartVertex W d} := by
          ext e
          constructor
          · intro h
            change d39VertexClass M e = d39VertexClass M d at h
            exact (exteriorMarkedComparison_wholePlaneVertexClass_eq_iff W D.rotation e d).mp h
          · intro h
            change wholePlaneDartVertex W e = wholePlaneDartVertex W d at h
            exact (exteriorMarkedComparison_wholePlaneVertexClass_eq_iff W D.rotation e d).mpr h
        change CcwSuccessor
          {e | d39VertexClass M e = d39VertexClass M d}
          (fun e => (G.arc e).initialDirection) d
          (wholePlaneRotation W D.rotation d)
        rw [hstar]
        exact G.rotation_agreement d }


/-- Helper toward Proposition 5.16: the canonical reversed-root outer dart
lies in the exterior of every restricted ball of this same drawing. -/
theorem exteriorMarkedComparison_canonicalDrawing_outerDart
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (r : ℕ) (hr : 0 < r) :
    let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
    let P := exteriorMarkedComparison_canonicalDrawing W D hhit C₀
    ∃ d : (d39FacedBall M r hr).D,
      d.1 = uibhbotWholePlaneOuterDart W ∧
      d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  let P0 := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F0 := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P0 hp ha F0 hf hFim hFa
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P := exteriorMarkedComparison_canonicalDrawing W D hhit C₀
  have hD : WholePlaneDart W = M.core.D := by
    dsimp [M, RootedLocallyFiniteMap.toD39RootedMap,
      uibhbotWholePlaneRootedLocallyFiniteMap]
  let eD : WholePlaneDart W ≃ M.core.D := Equiv.cast hD
  have harc (d : WholePlaneDart W) : P.arc (eD d) = G.arc d := by
    rfl
  have hPsurj : Function.Surjective (d39VertexClass M) := by
    intro v
    exact ⟨Quotient.out v, Quotient.out_eq' v⟩
  have hGsurj : Function.Surjective (wholePlaneDartVertex W) := by
    intro v
    obtain ⟨d, hd⟩ := WholePlanePastGlueData.vertex_incident W v
    exact ⟨d, hd⟩
  have himage : P.image = G.image := by
    rw [P.image_eq_union_arcs hPsurj, G.image_eq_union_arcs hGsurj]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨d', hz⟩
      obtain ⟨d, rfl⟩ := eD.surjective d'
      exact ⟨d, harc d ▸ hz⟩
    · rintro ⟨d, hz⟩
      exact ⟨eD d, (harc d).symm ▸ hz⟩
  have htransport := prop59_PLDrawing_transport_faces_of_image_eq
    G P eD harc himage.symm
  let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P0 hp ha F0 hf hFim hFa D.pastRightPositive
  let F := A (Quotient.mk _ (uibhbotWholePlaneOuterDart W))
  obtain ⟨F', hFval, hFbounded⟩ := htransport.1 F
  have hambient := prop59_canonicalAssembly_outerDart_borders_ambientUnboundedFace
    W D hhit C₀
  have hGborder : G.dartBorders (uibhbotWholePlaneOuterDart W) F := by
    exact hambient.1
  have hGunbounded : G.IsUnbounded F := hambient.2
  have hPborder : P.dartBorders (uibhbotWholePlaneOuterDart W) F' :=
    (htransport.2.2 _ F F' hFval).2 hGborder
  have houter : M.core.outer = uibhbotWholePlaneOuterDart W := by
    change (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).outer = _
    rfl
  have hPborder' : P.dartBorders M.core.outer F' := by
    rw [houter]
    exact hPborder
  have hPunbounded : P.IsUnbounded F' := hFbounded.mpr hGunbounded
  have houterRoot : M.core.outer = M.core.edgeInv M.rootMark.dart := by rfl
  have houterBall : M.core.outer ∈ d39BallDarts M r := by
    rw [houterRoot]
    exact (d39BallDarts_root_mem M hr).2
  let d : (d39FacedBall M r hr).D := ⟨M.core.outer, houterBall⟩
  have hmem := prop59_ambientUnboundedDartSide_mem_restrictedExternalOrbit
    M P r hr d F' hPunbounded (by simpa [d] using hPborder')
  exact ⟨d, by simp [d, M, uibhbotWholePlaneRootedLocallyFiniteMap,
      RootedLocallyFiniteMap.toD39RootedMap], hmem⟩


/-- Helper toward Proposition 5.16: the canonical source domain admits Data3
on the very same reindexed assembly drawing used by its exterior producer,
with endpoint-preserving path reparameterizations and exact positions. -/
theorem exteriorMarkedComparison_canonical_reparam_data
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W) :
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0)
      (_iso : D39RootedMapIso
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
      (x : D39DrawingRepresentationData3
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
        (uibhbotD39CanonicalRepresentation13Domain W D)),
      (∀ v, (exteriorMarkedComparison_canonicalDrawing W D hhit C₀).pos v =
        (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.pos
          (x.vertexEquiv v)) ∧
      ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, d39DrawingDartArc (uibhbotD39CanonicalRepresentation13Domain W D)
          x.toD39DrawingRepresentationData d t =
            ((exteriorMarkedComparison_canonicalDrawing W D hhit C₀).arc d).toPath (φ t) := by
  classical
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
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  obtain ⟨hhit, C₀, iso, data, hdata⟩ :=
    exteriorMarkedComparison_canonical_data3_with_dartEquiv W hW D
  let E := iso.toEquiv.symm.trans
    (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa)
  have hparams (x : M.core.D) :
      ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, d39DrawingDartArc B data.toD39DrawingRepresentationData x t =
          (G.arc (iso.toEquiv.symm x)).toPath (φ t) := by
    have hdraw := uibhbotD39CanonicalAssembly_drawingDartArc_eq W D data.toD39DrawingRepresentationData x
    have hdart : data.dartEquiv x = E x := congrArg (fun f => f x) hdata
    change d39DrawingDartArc B data.toD39DrawingRepresentationData x =
      (if (data.dartEquiv x).2 then
        (fun t => (G.arc (data.dartEquiv x).1.out).toPath t)
      else (fun t => (G.arc (data.dartEquiv x).1.out).toPath.symm t)) at hdraw
    rw [hdart] at hdraw
    have hpoly := uibhbotD39CanonicalAssembly_arcIdentification W D hhit C₀ iso x
    change (if (E x).2 then G.arc (E x).1.out
      else (G.arc (E x).1.out).reverse) = G.arc (iso.toEquiv.symm x) at hpoly
    cases hb : (E x).2
    · have hp : (G.arc (E x).1.out).reverse = G.arc (iso.toEquiv.symm x) := by
        simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hpoly
      obtain ⟨φ, h0, h1, hφ⟩ := polyline_reverse_toPath_exists_reparam
        (G.arc (E x).1.out) (G.arc_length _) (G.arc_simple _)
      refine ⟨φ, h0, h1, ?_⟩
      intro t
      have ht := congrFun hdraw t
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at ht
      exact ht.trans ((hφ t).trans (congrArg (fun p : Polyline => p.toPath (φ t)) hp))
    · have hp : G.arc (E x).1.out = G.arc (iso.toEquiv.symm x) := by
        simpa only [hb, ↓reduceIte] using hpoly
      refine ⟨Homeomorph.refl I, rfl, rfl, ?_⟩
      intro t
      have ht := congrFun hdraw t
      simp only [hb, ↓reduceIte] at ht
      exact ht.trans (congrArg (fun p : Polyline => p.toPath t) hp)
  let x := D39DrawingRepresentationData3.transportCombinatorialData iso.symm data
  have hx : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc (uibhbotD39CanonicalRepresentation13Domain W D)
        x.toD39DrawingRepresentationData d t =
          ((exteriorMarkedComparison_canonicalDrawing W D hhit C₀).arc d).toPath (φ t) := by
    intro d
    obtain ⟨φ, h0, h1, hφ⟩ := hparams (iso.toEquiv d)
    refine ⟨φ, h0, h1, ?_⟩
    intro t
    have h := hφ t
    rw [Equiv.symm_apply_apply] at h
    exact h
  exact ⟨hhit, C₀, iso, x,
    ExteriorMarkedComparison2.pos_eq_of_reparam x.toD39DrawingRepresentationData
      (exteriorMarkedComparison_canonicalDrawing W D hhit C₀) hx, hx⟩



/-- Helper toward Proposition 5.16: the exposed canonical assembly drawing's
actual exterior-marked ball is precisely its reversed-root lift. -/
theorem exteriorMarkedComparison_canonicalDrawing_rootLift
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) (r : ℕ) (hr : 0 < r) :
    Quotient.mk exteriorMarkedBallSetoid
      (d39FacedBallPLWithExternal
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
        (exteriorMarkedComparison_canonicalDrawing W D hhit C₀) r hr) =
      Prop516RootExteriorEncoding.rootLift (d39BallClass
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap r hr) := by
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P := exteriorMarkedComparison_canonicalDrawing W D hhit C₀
  obtain ⟨d, hd, hmem⟩ := exteriorMarkedComparison_canonicalDrawing_outerDart
    W D hhit C₀ r hr
  have hd' : d = (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart := by
    apply Subtype.ext
    exact hd
  rw [hd'] at hmem
  have horbit : (d39FacedBallPLWithExternal M P r hr).externalOrbit =
      (Prop516RootExteriorEncoding.rootBall (d39FacedBall M r hr)).externalOrbit :=
    plBallFaceCycleOrbit_eq_of_mem _ _ _ hmem Equiv.Perm.SameCycle.rfl
  have heq : d39FacedBallPLWithExternal M P r hr =
      Prop516RootExteriorEncoding.rootBall (d39FacedBall M r hr) :=
    congrArg (fun O => D39FiniteBallWithExternal.mk (d39FacedBall M r hr) O) horbit
  exact congrArg (Quotient.mk exteriorMarkedBallSetoid) heq

open MeasureTheory
open scoped ENNReal

/-- Helper toward Proposition 5.16: on one conull code event, agreement of
reversed-root marked balls bounds the geometric distance between every
finite exterior sample and every canonical UIBHBOT domain witness. -/
theorem exteriorMarkedComparison_sample_canonical_distance :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (D : UIBHBOTD39CanonicalDomainWitness W)
        (ell n : ℕ) (hell : 0 < ell)
        (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
        (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
        (U : P.Face) (hU : P.IsUnbounded U)
        (hborder : ∀ d, P.dartBorders d U ↔
          (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d)
        (r : ℕ) (hr : 0 < r),
        Prop516RootExteriorEncoding.rootLift
            (d39BallClass (diskRootedD39MapOfSample n ell hell p) r hr) =
          Prop516RootExteriorEncoding.rootLift (d39BallClass
            (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr) →
        edist (PLCylinderBall.geometricClass
          (diskSampleExteriorDomain ell n hell p P U hU hborder))
          (PLCylinderBall.geometricClass (uibhbotD39CanonicalRepresentation13Domain W D)) ≤
            (1 / 2 : ENNReal) ^ r := by
  filter_upwards [uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hW
  intro D ell n hell p P U hU hborder r hr hxy
  obtain ⟨hhit, C₀, iso, y, hypos, hyarc⟩ :=
    exteriorMarkedComparison_canonical_reparam_data W hW D
  have hcode : d39BallClass
      (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap r hr =
      d39BallClass
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr :=
    Quotient.sound ⟨iso.ballIso r hr⟩
  have hmarked := (diskSampleExteriorMarkedBallClass_eq_rootLift
    ell n hell p P U hU hborder r hr).trans
      (hxy.trans ((congrArg Prop516RootExteriorEncoding.rootLift hcode).symm.trans
        (exteriorMarkedComparison_canonicalDrawing_rootLift
          W D hhit C₀ r hr).symm))
  have hg := exteriorMarkedComparison_reparam_geomBallIso
    (diskSampleExteriorData3 ell n hell p P U hU hborder) y
    (diskSampleRootedStagePLDrawing ell n hell p P)
    (exteriorMarkedComparison_canonicalDrawing W D hhit C₀)
    (fun _ => rfl) hypos
    (diskSampleExteriorBase_dartArc_reparam ell n hell p P U hU hborder)
    hyarc r hr hmarked
  exact (d39ClassDistance_le_pow_iff_nonempty hr
    (PLCylinderBall.domainMap (diskSampleExteriorDomain ell n hell p P U hU hborder))
    (PLCylinderBall.domainMap (uibhbotD39CanonicalRepresentation13Domain W D))).mpr hg


/-- Helper toward Proposition 5.16: marked equality and the Definition 3.8
distance bound are equivalent on the actual finite and canonical carriers,
simultaneously for all source witnesses on a single conull event. -/
theorem exteriorMarkedComparison_sample_canonical_distance_iff :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (D : UIBHBOTD39CanonicalDomainWitness W)
        (ell n : ℕ) (hell : 0 < ell)
        (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
        (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
        (U : P.Face) (hU : P.IsUnbounded U)
        (hborder : ∀ d, P.dartBorders d U ↔
          (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d)
        (r : ℕ) (hr : 0 < r),
        Prop516RootExteriorEncoding.rootLift
            (d39BallClass (diskRootedD39MapOfSample n ell hell p) r hr) =
          Prop516RootExteriorEncoding.rootLift (d39BallClass
            (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr) ↔
        edist (PLCylinderBall.geometricClass
          (diskSampleExteriorDomain ell n hell p P U hU hborder))
          (PLCylinderBall.geometricClass (uibhbotD39CanonicalRepresentation13Domain W D)) ≤
            (1 / 2 : ENNReal) ^ r := by
  filter_upwards [exteriorMarkedComparison_sample_canonical_distance,
    uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hreverse hW
  intro D ell n hell p P U hU hborder r hr
  constructor
  · exact hreverse D ell n hell p P U hU hborder r hr
  · intro hd
    obtain ⟨e⟩ := (d39ClassDistance_le_pow_iff_nonempty hr
      (PLCylinderBall.domainMap (diskSampleExteriorDomain ell n hell p P U hU hborder))
      (PLCylinderBall.domainMap (uibhbotD39CanonicalRepresentation13Domain W D))).mp hd
    obtain ⟨J⟩ := diskSampleExteriorDomain_uibhbot_facedBallIso
      ell n hell p P U hU hborder W hW D r hr e
    exact congrArg Prop516RootExteriorEncoding.rootLift (Quotient.sound ⟨J⟩)

end DirectedDistances.PaperProofs.Section5
end
