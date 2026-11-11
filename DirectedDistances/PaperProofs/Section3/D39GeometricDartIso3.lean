/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso2

/-! # Restricted edge data for geometric dart isomorphisms -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open unitInterval
open scoped ENNReal Topology

universe uV uE uV' uE'

namespace D39GeomBallIsoV2

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {r s : ℕ} {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: a smaller geometric edge ball lies in its
enclosing ball. -/
theorem edgeBall_mono (hsr : s ≤ r) {a : E}
    (ha : a ∈ d39GeomBallEdges M rho s) :
    a ∈ d39GeomBallEdges M rho r := by
  change M.toPlaneMapWithMissing.src a ∈ d39GeomBallVertices M rho s ∧
    M.toPlaneMapWithMissing.tgt a ∈ d39GeomBallVertices M rho s at ha
  change M.toPlaneMapWithMissing.src a ∈ d39GeomBallVertices M rho r ∧
    M.toPlaneMapWithMissing.tgt a ∈ d39GeomBallVertices M rho r
  exact ⟨vertexBall_mono hsr ha.1, vertexBall_mono hsr ha.2⟩

/-- Helper toward Definition 3.8: an edge is in the smaller ball exactly when
its image under the larger-ball edge equivalence is in the corresponding
smaller ball. The endpoint conditions use the edge flip recorded by the
isomorphism. -/
theorem edgeBall_map_iff (e : D39GeomBallIsoV2 r M rho M' rho')
    (a : {a // a ∈ d39GeomBallEdges M rho r}) :
    a.1 ∈ d39GeomBallEdges M rho s ↔
      (e.edgeEquiv a).1 ∈ d39GeomBallEdges M' rho' s := by
  change (M.toPlaneMapWithMissing.src a.1 ∈ d39GeomBallVertices M rho s ∧
      M.toPlaneMapWithMissing.tgt a.1 ∈ d39GeomBallVertices M rho s) ↔
    (M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1 ∈
        d39GeomBallVertices M' rho' s ∧
      M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1 ∈
        d39GeomBallVertices M' rho' s)
  have hsrc : M.toPlaneMapWithMissing.src a.1 ∈
      d39GeomBallVertices M rho s ↔
      (e.vertexEquiv ⟨M.toPlaneMapWithMissing.src a.1, a.2.1⟩).1 ∈
        d39GeomBallVertices M' rho' s := by
    change d39GeomGraphDistance M (d39GeomRootVertex M rho)
        (M.toPlaneMapWithMissing.src a.1) ≤ (s : ℕ∞) ↔
      d39GeomGraphDistance M' (d39GeomRootVertex M' rho')
        (e.vertexEquiv ⟨M.toPlaneMapWithMissing.src a.1, a.2.1⟩).1 ≤
          (s : ℕ∞)
    rw [e.distance_preserving _ a.2.1]
  have htgt : M.toPlaneMapWithMissing.tgt a.1 ∈
      d39GeomBallVertices M rho s ↔
      (e.vertexEquiv ⟨M.toPlaneMapWithMissing.tgt a.1, a.2.2⟩).1 ∈
        d39GeomBallVertices M' rho' s := by
    change d39GeomGraphDistance M (d39GeomRootVertex M rho)
        (M.toPlaneMapWithMissing.tgt a.1) ≤ (s : ℕ∞) ↔
      d39GeomGraphDistance M' (d39GeomRootVertex M' rho')
        (e.vertexEquiv ⟨M.toPlaneMapWithMissing.tgt a.1, a.2.2⟩).1 ≤
          (s : ℕ∞)
    rw [e.distance_preserving _ a.2.2]
  have hsrc' : M.toPlaneMapWithMissing.src a.1 ∈
      d39GeomBallVertices M rho s ↔
      (if e.edgeFlip a then M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1
       else M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1) ∈
        d39GeomBallVertices M' rho' s := by
    rw [← e.src_map a]
    exact hsrc
  have htgt' : M.toPlaneMapWithMissing.tgt a.1 ∈
      d39GeomBallVertices M rho s ↔
      (if e.edgeFlip a then M'.toPlaneMapWithMissing.src (e.edgeEquiv a).1
       else M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a).1) ∈
        d39GeomBallVertices M' rho' s := by
    rw [← e.tgt_map a]
    exact htgt
  cases hf : e.edgeFlip a
  · simpa [hf] using and_congr hsrc' htgt'
  · simpa [hf, and_comm] using and_congr hsrc' htgt'

/-- Helper toward Definition 3.8: membership is reflected through the inverse
edge equivalence on the smaller balls. -/
theorem edgeBall_map_symm_iff (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r) (b : {b // b ∈ d39GeomBallEdges M' rho' s}) :
    (e.edgeEquiv.symm ⟨b.1, edgeBall_mono (M := M') (rho := rho') hsr b.2⟩).1 ∈
        d39GeomBallEdges M rho s ↔ b.1 ∈ d39GeomBallEdges M' rho' s := by
  let bR : {b // b ∈ d39GeomBallEdges M' rho' r} :=
    ⟨b.1, edgeBall_mono (M := M') (rho := rho') hsr b.2⟩
  have h := edgeBall_map_iff (e := e) (s := s) (e.edgeEquiv.symm bR)
  simpa [bR] using h

/-- Helper toward Definition 3.8: restrict the edge equivalence to smaller
geometric balls, retaining each original edge identity. -/
@[expose]
def restrictEdges (e : D39GeomBallIsoV2 r M rho M' rho') (hsr : s ≤ r) :
    {a // a ∈ d39GeomBallEdges M rho s} ≃
      {a // a ∈ d39GeomBallEdges M' rho' s} := by
  let L := Equiv.subtypeSubtypeEquivSubtype
    (p := fun a : E => a ∈ d39GeomBallEdges M rho r)
    (q := fun a : E => a ∈ d39GeomBallEdges M rho s)
    (fun {_} h => edgeBall_mono (M := M) (rho := rho) hsr h)
  let R := Equiv.subtypeSubtypeEquivSubtype
    (p := fun a : E' => a ∈ d39GeomBallEdges M' rho' r)
    (q := fun a : E' => a ∈ d39GeomBallEdges M' rho' s)
    (fun {_} h => edgeBall_mono (M := M') (rho := rho') hsr h)
  let mid := e.edgeEquiv.subtypeEquiv
    (p := fun a : {a // a ∈ d39GeomBallEdges M rho r} =>
      a.1 ∈ d39GeomBallEdges M rho s)
    (q := fun a : {a // a ∈ d39GeomBallEdges M' rho' r} =>
      a.1 ∈ d39GeomBallEdges M' rho' s)
    (fun a => edgeBall_map_iff (e := e) (s := s) a)
  exact L.symm.trans (mid.trans R)

/-- Helper toward Definition 3.8: the restricted edge equivalence has the same
underlying edge map as the enclosing-ball equivalence. -/
theorem restrictEdges_val (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r) (a : {a // a ∈ d39GeomBallEdges M rho s}) :
    (restrictEdges e hsr a).1 =
      (e.edgeEquiv ⟨a.1, edgeBall_mono (M := M) (rho := rho) hsr a.2⟩).1 := by
  rfl

end D39GeomBallIsoV2

/-- Helper toward Definition 3.8: the edge data of a geometric dart ball
isomorphism at a smaller positive radius, before the retained-face fields are
assembled. -/
structure D39GeomBallIsoV2EdgePart {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'} (s : ℕ)
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) where
  radius_pos : 0 < s
  h : ℂ ≃ₜ ℂ
  orientationPreserving : OrientationPreserving h
  vertexEquiv : {v // v ∈ d39GeomBallVertices M rho s} ≃
    {v // v ∈ d39GeomBallVertices M' rho' s}
  edgeEquiv : {a // a ∈ d39GeomBallEdges M rho s} ≃
    {a // a ∈ d39GeomBallEdges M' rho' s}
  edgeFlip : {a // a ∈ d39GeomBallEdges M rho s} → Bool
  pos_map : ∀ v, h (M.toPlaneMapWithMissing.pos v.1) =
    M'.toPlaneMapWithMissing.pos (vertexEquiv v).1
  edgeParam : ∀ _a : {a // a ∈ d39GeomBallEdges M rho s},
    Homeomorph unitInterval unitInterval
  edgeParam_mono : ∀ a, edgeFlip a = false → StrictMono (edgeParam a)
  edgeParam_anti : ∀ a, edgeFlip a = true → StrictAnti (edgeParam a)
  arc_map : ∀ a t, h (M.toPlaneMapWithMissing.arc a.1 t) =
    M'.toPlaneMapWithMissing.arc (edgeEquiv a).1 (edgeParam a t)
  src_map : ∀ a,
    (vertexEquiv ⟨M.toPlaneMapWithMissing.src a.1, a.2.1⟩).1 =
      if edgeFlip a then M'.toPlaneMapWithMissing.tgt (edgeEquiv a).1
      else M'.toPlaneMapWithMissing.src (edgeEquiv a).1
  tgt_map : ∀ a,
    (vertexEquiv ⟨M.toPlaneMapWithMissing.tgt a.1, a.2.2⟩).1 =
      if edgeFlip a then M'.toPlaneMapWithMissing.src (edgeEquiv a).1
      else M'.toPlaneMapWithMissing.tgt (edgeEquiv a).1
  missing_map : ∀ a,
    M'.toPlaneMapWithMissing.missing (edgeEquiv a).1 ↔
      M.toPlaneMapWithMissing.missing a.1
  orientation_map : ∀ a (ha : ¬ M.toPlaneMapWithMissing.missing a.1),
    M'.forward ⟨(edgeEquiv a).1, by simpa [missing_map a] using ha⟩ =
      Bool.xor (M.forward ⟨a.1, ha⟩) (edgeFlip a)
  root_edge_map :
    (edgeEquiv ⟨rho.1, d39GeomRootEdge_mem M rho radius_pos⟩).1 = rho'.1
  root_bool_map : rho'.2 = Bool.xor rho.2
    (edgeFlip ⟨rho.1, d39GeomRootEdge_mem M rho radius_pos⟩)

namespace D39GeomBallIsoV2EdgePart

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {r s : ℕ} {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: restrict every edge field of a geometric dart
ball isomorphism. -/
@[expose]
def restrict (e : D39GeomBallIsoV2 r M rho M' rho') (hs : 0 < s)
    (hsr : s ≤ r) : D39GeomBallIsoV2EdgePart s M rho M' rho' where
  radius_pos := hs
  h := e.h
  orientationPreserving := e.orientationPreserving
  vertexEquiv := D39GeomBallIsoV2.restrictVertices e hsr
  edgeEquiv := D39GeomBallIsoV2.restrictEdges e hsr
  edgeFlip := fun a => e.edgeFlip
    ⟨a.1, D39GeomBallIsoV2.edgeBall_mono hsr a.2⟩
  pos_map := by
    intro v
    rw [D39GeomBallIsoV2.restrictVertices_val]
    exact e.pos_map ⟨v.1, D39GeomBallIsoV2.vertexBall_mono hsr v.2⟩
  edgeParam := fun a => e.edgeParam
    ⟨a.1, D39GeomBallIsoV2.edgeBall_mono hsr a.2⟩
  edgeParam_mono := by
    intro _a ha
    exact e.edgeParam_mono _ ha
  edgeParam_anti := by
    intro _a ha
    exact e.edgeParam_anti _ ha
  arc_map := by
    intro a t
    rw [D39GeomBallIsoV2.restrictEdges_val]
    exact e.arc_map ⟨a.1, D39GeomBallIsoV2.edgeBall_mono hsr a.2⟩ t
  src_map := by
    intro a
    rw [D39GeomBallIsoV2.restrictVertices_val,
      D39GeomBallIsoV2.restrictEdges_val]
    exact e.src_map ⟨a.1, D39GeomBallIsoV2.edgeBall_mono hsr a.2⟩
  tgt_map := by
    intro a
    rw [D39GeomBallIsoV2.restrictVertices_val,
      D39GeomBallIsoV2.restrictEdges_val]
    exact e.tgt_map ⟨a.1, D39GeomBallIsoV2.edgeBall_mono hsr a.2⟩
  missing_map := by
    intro a
    rw [D39GeomBallIsoV2.restrictEdges_val]
    exact e.missing_map ⟨a.1, D39GeomBallIsoV2.edgeBall_mono hsr a.2⟩
  orientation_map := by
    intro a ha
    have h := e.orientation_map
      ⟨a.1, D39GeomBallIsoV2.edgeBall_mono hsr a.2⟩ ha
    simpa [D39GeomBallIsoV2.restrictEdges_val] using h
  root_edge_map := by
    rw [D39GeomBallIsoV2.restrictEdges_val]
    exact e.root_edge_map
  root_bool_map := by
    change rho'.2 = Bool.xor rho.2
      (e.edgeFlip ⟨rho.1, D39GeomBallIsoV2.edgeBall_mono hsr
        (d39GeomRootEdge_mem M rho hs)⟩)
    have h := e.root_bool_map
    simpa using h

end D39GeomBallIsoV2EdgePart











end DirectedDistances.PaperProofs.Section3

end
