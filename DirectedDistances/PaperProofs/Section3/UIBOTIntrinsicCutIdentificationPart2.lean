/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart1

/-! # Actual edge-list paths under the geometric cut isomorphism

Consumer helpers for Definition 1.3 and Theorem 1.4
retained, including parallel edges. The empty-path convention and ambient
vertex indexing agree exactly with `M0CutData.sdp` and `M0CutData.ldp`.
No recurrence, face-equality or source-object identification assumption is
below take an actual geometric isomorphism and derive earlier-run recurrence. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1
open scoped Classical

/-- Consumer helper for Definition 1.3: a finite directed path stores the
actual ordered list of geometric edge identities. Each appended edge is in
the cut and has a cut tail, so missing edges cannot occur in the list.
The nil constructor matches the existing distance convention. -/
inductive UIBOTCutEdgeListPath (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) :
    WholePlaneVertex W → WholePlaneVertex W → List (WholePlaneEdge W) → Prop
  | nil (u : WholePlaneVertex W) : UIBOTCutEdgeListPath W H u u []
  | snoc {u v : WholePlaneVertex W} {es : List (WholePlaneEdge W)}
      (p : UIBOTCutEdgeListPath W H u v es) (e : WholePlaneEdge W)
      (retained : e ∈ m0CutLeftEdges W H (m0CutSeamEdge W H))
      (present : m0CutTail W H (e, false))
      (incident : wholePlaneEdgeWest W e = v) :
      UIBOTCutEdgeListPath W H u (wholePlaneEdgeEast W e) (es ++ [e])

/-- Consumer helper for Definition 1.3: edge-list paths realize exactly the
lengths used by both installed extended cut distances, including length zero. -/
theorem uibotIntrinsicCut_edgeList_length_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (u v : WholePlaneVertex W) (n : ℕ) :
    (∃ es : List (WholePlaneEdge W), UIBOTCutEdgeListPath W H u v es ∧ es.length = n) ↔
      m0CutReachableLength (m0CutDirectedStep W H (m0CutSeamEdge W H)) n u v := by
  constructor
  · rintro ⟨es, p, rfl⟩
    induction p with
    | nil => rfl
    | @snoc v es p e he ht hv ih =>
      simp only [List.length_append, List.length_singleton]
      exact ⟨v, ih, (show m0CutDirectedStep W H (m0CutSeamEdge W H) v
        (wholePlaneEdgeEast W e) from ⟨(e, false), ht, he, hv, rfl⟩)⟩
  · induction n generalizing v with
    | zero =>
      intro huv
      change u = v at huv
      subst v
      exact ⟨[], .nil u, rfl⟩
    | succ n ih =>
      rintro ⟨x, hx, d, ht, he, hwest, heast⟩
      obtain ⟨es, p, hlen⟩ := ih x hx
      rcases d with ⟨e, b⟩
      cases b with
      | false =>
        rw [← heast]
        exact ⟨es ++ [e], p.snoc e he ht hwest, by
          simp only [List.length_append, List.length_singleton, hlen]⟩
      | true => exact (ht.1.1 rfl).elim

section GeometricTransport

variable {W W' : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} {H' : WholePlaneRotationHypothesis W'}
    {G : WholePlaneDrawing W H} {G' : WholePlaneDrawing W' H'}
    {hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e}
    {hp' : ∀ e : WholePlaneEdge W', wholePlaneEdgePresent W' e}
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0))
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))

include h h'

/-- Consumer helper for Definition 1.3: restrict the actual geometric
vertex bijection to the retained cut vertices, including every seam vertex. -/
@[expose] def uibotIntrinsicCut_vertexEquiv (D : M0CutData W H) (D' : M0CutData W' H') :
    {v : WholePlaneVertex W // v ∈ m0CutLeftVertices W H D.seam} ≃
      {v : WholePlaneVertex W' // v ∈ m0CutLeftVertices W' H' D'.seam} :=
  I.vertexEquiv.subtypeEquiv
    (uibotCut_geometric_iso_marks
      (fun N => boundaryHitWitnesses_of_le W (Nat.zero_le N) h)
      (fun N => boundaryHitWitnesses_of_le W' (Nat.zero_le N) h')
      I D D').2.2.2.1

/-- Consumer helper for Definition 1.3: restrict the actual geometric edge
bijection to all retained cut edges, including the missing lower-left edges. -/
@[expose] def uibotIntrinsicCut_edgeEquiv (D : M0CutData W H) (D' : M0CutData W' H') :
    {e : WholePlaneEdge W // e ∈ D.edges} ≃
      {e : WholePlaneEdge W' // e ∈ D'.edges} :=
  I.edgeEquiv.subtypeEquiv (fun e =>
    ((uibotCut_geometric_iso_marks
      (fun N => boundaryHitWitnesses_of_le W (Nat.zero_le N) h)
      (fun N => boundaryHitWitnesses_of_le W' (Nat.zero_le N) h')
      I D D').2.2.2.2.1 e).1)

/-- Consumer helper for Definition 1.3: the geometric edge map sends every
individual directed cut path to a directed cut path, and reflects that
property. The same ordered edge list, rather than just its vertices, is mapped. -/
theorem uibotIntrinsicCut_edgeList_transport
    (u v : WholePlaneVertex W) (es : List (WholePlaneEdge W)) :
    UIBOTCutEdgeListPath W H u v es ↔
      UIBOTCutEdgeListPath W' H' (I.vertexEquiv u) (I.vertexEquiv v)
        (es.map I.edgeEquiv) := by
  have hh (N : ℕ) := boundaryHitWitnesses_of_le W (Nat.zero_le N) h
  have hh' (N : ℕ) := boundaryHitWitnesses_of_le W' (Nat.zero_le N) h'
  have hW := uibotCut_code_eq_of_geometric_iso hh hh' I
  subst W'
  obtain ⟨he, hv⟩ := uibotCut_geometric_iso_fixes_ids hh I
  have heq : (I.edgeEquiv : WholePlaneEdge W → WholePlaneEdge W) = id := funext he
  rw [heq, List.map_id, hv, hv]

/-- Consumer helper for Definition 1.3: an actual equivalence of edge-list
path carriers. The inverse maps each edge by the inverse ambient edge
bijection; both maps preserve the exact finite length. -/
@[expose] def uibotIntrinsicCut_pathEquiv (u v : WholePlaneVertex W) :
    {es : List (WholePlaneEdge W) // UIBOTCutEdgeListPath W H u v es} ≃
      {es : List (WholePlaneEdge W') //
        UIBOTCutEdgeListPath W' H' (I.vertexEquiv u) (I.vertexEquiv v) es} := by
  let e : List (WholePlaneEdge W) ≃ List (WholePlaneEdge W') := {
    toFun := List.map I.edgeEquiv
    invFun := List.map I.edgeEquiv.symm
    left_inv := by
      intro es
      induction es with
      | nil => rfl
      | cons a es ih => simp only [List.map_cons, Equiv.symm_apply_apply, ih]
    right_inv := by
      intro es
      induction es with
      | nil => rfl
      | cons a es ih => simp only [List.map_cons, Equiv.apply_symm_apply, ih] }
  exact e.subtypeEquiv (uibotIntrinsicCut_edgeList_transport h h' I u v)

/-- Consumer helper for Definition 1.3: the actual path equivalence on
the cut vertex subtypes. Thus even the empty path has its vertex in the cut;
nonempty paths retain their complete ordered list of individual edges. -/
@[expose] def uibotIntrinsicCut_directedPathEquiv
    (D : M0CutData W H) (D' : M0CutData W' H')
    (u v : {v : WholePlaneVertex W // v ∈ m0CutLeftVertices W H D.seam}) :
    {es : List (WholePlaneEdge W) // UIBOTCutEdgeListPath W H u.val v.val es} ≃
      {es : List (WholePlaneEdge W') // UIBOTCutEdgeListPath W' H'
        (uibotIntrinsicCut_vertexEquiv h h' I D D' u).val
        (uibotIntrinsicCut_vertexEquiv h h' I D D' v).val es} :=
  uibotIntrinsicCut_pathEquiv h h' I u.val v.val

/-- Consumer helper for Definition 1.3: the forward path equivalence retains
every edge identity through I.edgeEquiv and has exactly the original length. -/
theorem uibotIntrinsicCut_pathEquiv_spec (u v : WholePlaneVertex W)
    (p : {es : List (WholePlaneEdge W) // UIBOTCutEdgeListPath W H u v es}) :
    (uibotIntrinsicCut_pathEquiv h h' I u v p).val = p.val.map I.edgeEquiv ∧
      (uibotIntrinsicCut_pathEquiv h h' I u v p).val.length = p.val.length :=
  ⟨rfl, List.length_map _⟩

/-- Consumer helper for Definition 1.3: the inverse path equivalence retains
every edge identity through I.edgeEquiv.symm and preserves the exact length. -/
theorem uibotIntrinsicCut_pathEquiv_symm_spec (u v : WholePlaneVertex W)
    (p : {es : List (WholePlaneEdge W') //
      UIBOTCutEdgeListPath W' H' (I.vertexEquiv u) (I.vertexEquiv v) es}) :
    ((uibotIntrinsicCut_pathEquiv h h' I u v).symm p).val =
        p.val.map I.edgeEquiv.symm ∧
      ((uibotIntrinsicCut_pathEquiv h h' I u v).symm p).val.length = p.val.length :=
  ⟨rfl, List.length_map _⟩

/-- Consumer helper for Theorem 1.4: both extended cut distances are preserved
simultaneously for every pair of vertices. This includes all extrema, top
SDP for unreachable pairs, bottom LDP for unreachable pairs, and unbounded
LDP; it makes no unjustified finite-distance assertion. -/
theorem uibotIntrinsicCut_distances
    (D : M0CutData W H) (D' : M0CutData W' H') (u v : WholePlaneVertex W) :
    D'.sdp (I.vertexEquiv u) (I.vertexEquiv v) = D.sdp u v ∧
      D'.ldp (I.vertexEquiv u) (I.vertexEquiv v) = D.ldp u v := by
  have hh (N : ℕ) := boundaryHitWitnesses_of_le W (Nat.zero_le N) h
  have hh' (N : ℕ) := boundaryHitWitnesses_of_le W' (Nat.zero_le N) h'
  have hW := uibotCut_code_eq_of_geometric_iso hh hh' I
  subst W'
  obtain ⟨_, hv⟩ := uibotCut_geometric_iso_fixes_ids hh I
  rw [hv, hv]
  exact ⟨rfl, rfl⟩

/-- Consumer helper for Theorem 1.4: the two unreachable-value conventions
survive geometric transport without replacing either value by zero. -/
theorem uibotIntrinsicCut_unreachable_values
    (D : M0CutData W H) (D' : M0CutData W' H') (u v : WholePlaneVertex W) :
    (D'.sdp (I.vertexEquiv u) (I.vertexEquiv v) = ⊤ ↔ D.sdp u v = ⊤) ∧
      (D'.ldp (I.vertexEquiv u) (I.vertexEquiv v) = ⊥ ↔ D.ldp u v = ⊥) := by
  obtain ⟨hs, hl⟩ := uibotIntrinsicCut_distances h h' I D D' u v
  rw [hs, hl]
  exact ⟨Iff.rfl, Iff.rfl⟩

end GeometricTransport
end DirectedDistances.PaperProofs.Section3
end
