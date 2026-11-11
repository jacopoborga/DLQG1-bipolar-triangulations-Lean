/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination15

/-! # Coherent ambient lifting of a prescribed intrinsic candidate

The realized side retains the actual ambient edge IDs and endpoints. Thus
concatenating its prescribed darts constructs coherent finite prefixes directly;
no compactness, local finiteness, or compatibility premise is needed. Ambient
optimality comes from the finite excursion replacement in Determination15.
This does not prove the angular comparison or intrinsic leftmost selector. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4 Quiver

private theorem ray_vertices {M : GeometricSideSubmap}
    {v d : ℕ → GeometricSideCell M} (hr : geometricSideDirectedRay M v d) :
    ∃ u : ℕ → M.vertices, ∀ n, v n = .inl (u n) := by
  classical
  have hv (n : ℕ) : ∃ u : M.vertices, v n = .inl u := by
    have hi := (hr n).2.1
    cases hd : d n with
    | inl z => simp only [hd, geometricSideRelation] at hi
    | inr e =>
      cases hn : v n with
      | inl u => exact ⟨u, rfl⟩
      | inr f => simp only [hd, hn, geometricSideRelation] at hi
  exact ⟨fun n => (hv n).choose, fun n => (hv n).choose_spec⟩

private theorem ray_darts {M : GeometricSideSubmap}
    {v d : ℕ → GeometricSideCell M} (hr : geometricSideDirectedRay M v d)
    (u : ℕ → M.vertices) (hu : ∀ n, v n = .inl (u n)) :
    ∃ e : ℕ → M.edges, ∀ n,
      d n = .inr ⟨((e n).val, false), (e n).property⟩ ∧
      (e n).val ∈ M.present ∧ M.west (e n).val = (u n).val ∧
      M.east (e n).val = (u (n + 1)).val := by
  classical
  have he (n : ℕ) : ∃ e : M.edges,
      d n = .inr ⟨(e.val, false), e.property⟩ ∧
      e.val ∈ M.present ∧ M.west e.val = (u n).val ∧
      M.east e.val = (u (n + 1)).val := by
    obtain ⟨ho, hi, f, hf, ht⟩ := hr n
    rw [hu n] at hi
    rw [hu (n + 1)] at ht
    cases hd : d n with
    | inl z => simp only [hd, geometricSideRelation] at ho
    | inr a =>
      rw [hd] at ho hi hf
      have hp : a.val.1 ∈ M.present ∧ a.val.2 = false := ho
      cases f with
      | inl z => exact False.elim hf
      | inr b =>
        have hb : (a.val.1, !a.val.2) = b.val := hf
        have hw : (if a.val.2 then M.east a.val.1 else M.west a.val.1) =
            (u n).val := hi
        have ht' : (if b.val.2 then M.east b.val.1 else M.west b.val.1) =
            (u (n + 1)).val := ht
        rw [← hb, hp.2] at ht'
        rw [hp.2] at hw
        refine ⟨⟨a.val.1, a.property⟩, ?_, hp.1, hw, ht'⟩
        congr 1
        exact Subtype.ext (Prod.ext rfl hp.2)
  exact ⟨fun n => (he n).choose, fun n => (he n).choose_spec⟩

private def dartPrefix {w : ℕ → Fin 3}
    (u : ℕ → PresentVertex w) (a : ∀ n, u n ⟶ u (n + 1)) :
    (n : ℕ) → Path (u 0) (u n)
  | 0 => .nil
  | n + 1 => (dartPrefix u a n).cons (a n)

private theorem dartPrefix_length {w : ℕ → Fin 3}
    (u : ℕ → PresentVertex w) (a : ∀ n, u n ⟶ u (n + 1)) (n : ℕ) :
    (dartPrefix u a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

private theorem dartPrefix_edges {w : ℕ → Fin 3}
    (u : ℕ → PresentVertex w) (a : ∀ n, u n ⟶ u (n + 1)) (n : ℕ) :
    pathEdgeList (dartPrefix u a n) = List.ofFn (fun i : Fin n => (a i.val).val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [dartPrefix, pathEdgeList, List.ofFn_succ', List.concat_eq_append,
      Fin.val_castSucc, Fin.val_last] using congrArg (fun l => l ++ [(a n).val]) ih

private theorem segments_of_optimal_prefixes {w : ℕ → Fin 3}
    {start : PresentVertex w} (R : InfinitePresentPath w start) (longest : Bool)
    (hopt : ∀ n, if longest then IsLongest (R.initial n).2
      else IsShortest (R.initial n).2) :
    if longest then R.HasLongestSegments else R.HasShortestSegments := by
  have hs : ∀ a b : ℕ, 1 ≤ a → a ≤ b →
      ∃ z, ∃ q : Path z (R.initial b).1,
        q.length = b + 1 - a ∧
        pathEdgeList q = (List.ofFn (fun i : Fin b => R.edge i.val)).drop (a - 1) ∧
        (if longest then IsLongest q else IsShortest q) := by
    intro a b ha hab
    obtain ⟨z, p, q, hpq, hp⟩ := (R.initial b).2.exists_eq_comp_of_le_length
      (show a - 1 ≤ (R.initial b).2.length by rw [R.prefix_length]; omega)
    refine ⟨z, q, ?_, ?_, ?_⟩
    · have hlen := R.prefix_length b
      rw [hpq, Path.length_comp, hp] at hlen
      omega
    · rw [← R.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
      exact List.drop_left.symm
    · have ho := hopt b
      rw [hpq] at ho
      cases longest with
      | false => exact IsShortest.of_comp_right ho
      | true => exact IsLongest.of_comp_right ho
  cases longest <;> exact hs

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: every intrinsic adjacent candidate in the
actual left side lifts to one infinite ambient cut geodesic from x_(k-1).
The equalities retain every vertex and individual directed dart, including
parallel-edge identity. No leftmost or angular comparison is asserted. -/
theorem m0GeodesicLeftSide_adjacentCandidate_coherentAmbientLift
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp P .left)}
    (hc : geometricSideAdjacentGeodesicCandidate (m0GeodesicSide hp P .left)
      longest v d) :
    ∃ (Q : M0CutInfiniteGeodesic W H h hLL (k - 1) longest)
      (u : ℕ → (m0GeodesicSide hp P .left).vertices)
      (e : ℕ → (m0GeodesicSide hp P .left).edges),
      (∀ n, v n = .inl (u n)) ∧
      (∀ n, d n = .inr ⟨((e n).val, false), (e n).property⟩) ∧
      (∀ n, (Q.codePath.initial n).1.id = (u n).val) ∧
      (∀ n, Q.codePath.edge n = (e n).val) := by
  classical
  let M := m0GeodesicSide hp P .left
  obtain ⟨u, hu⟩ := ray_vertices hc.1
  obtain ⟨e, he⟩ := ray_darts hc.1 u hu
  let U : ℕ → PresentVertex (shiftedStream W 0) := fun n => ⟨(u n).val⟩
  let A : ∀ n, U n ⟶ U (n + 1) := fun n =>
    ⟨(e n).val, (he n).2.1, (he n).2.2.1, (he n).2.2.2⟩
  let R : InfinitePresentPath (shiftedStream W 0) (U 0) :=
    ⟨fun n => (e n).val, fun n => ⟨U n, dartPrefix U A n⟩,
      dartPrefix_length U A, dartPrefix_edges U A⟩
  have hopt (n : ℕ) : if longest then IsLongest (R.initial n).2
      else IsShortest (R.initial n).2 := by
    have hn := hc.2.2 0 n
    rw [Nat.zero_add, hu 0, hu n] at hn
    obtain ⟨p, hlen, ho⟩ := m0GeodesicLeftSide_optimalLength_ambient hp P n
      (u 0) (u n) hn
    have hlen' : (R.initial n).2.length = p.length := (R.prefix_length n).trans hlen.symm
    cases longest with
    | false => exact IsShortest.of_length_eq ho hlen'
    | true => exact IsLongest.of_length_eq ho hlen'
  have hseg := segments_of_optimal_prefixes R longest hopt
  have hstart : U 0 = boundaryPresentVertex (shiftedStream W 0) h (k - 1) := by
    obtain ⟨b, hb, hi⟩ := hc.2.1
    rw [hu 0] at hi
    have hid : (u 0).val = boundaryVertex (shiftedStream W 0) h (k - 1) := by
      cases b with
      | inl z => exact False.elim hb
      | inr b =>
        have hb' : M.boundary 1 = b.val := hb
        have hi' : geometricSideDartInitial M b.val = (u 0).val := hi
        rw [← hb'] at hi'
        exact hi'.symm.trans (m0GeodesicLeftSide_adjacent_start hp P)
    exact congrArg PresentVertex.mk hid
  have hex : ∃ S : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h (k - 1)),
      (if longest then S.HasLongestSegments else S.HasShortestSegments) ∧
      (∀ n, (S.initial n).1.id = (u n).val) ∧
      (∀ n, S.edge n = (e n).val) := by
    rw [← hstart]
    exact ⟨R, hseg, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨S, hS, hSu, hSe⟩ := hex
  have hSstart : (S.initial 0).1.id =
      boundaryVertex (shiftedStream W 0) h (k - 1) := by
    have hz := (S.initial 0).2.eq_of_length_zero (S.prefix_length 0)
    exact congrArg PresentVertex.id hz.symm
  let Q : M0CutInfiniteGeodesic W H h hLL (k - 1) longest := {
    codePath := S
    segments := hS
    startsAtCutBoundary := (m0CutData W H h hLL).x_eq h hLL (k - 1) |>.trans
      (congrArg (wholePlaneVertexι W 0) hSstart.symm)
    cutStep := by
      intro n
      apply (m0Cut_identification_directedStep W H h hLL
        ((S.initial n).1.id) ((S.initial (n + 1)).1.id)).2
      obtain ⟨hpresent, hwest⟩ := S.edge_outgoing_at_initial (shiftedStream W 0) n
      obtain ⟨_, heast⟩ := S.edge_incoming_at_succ (shiftedStream W 0) n
      exact ⟨S.edge n, hpresent, congrArg (wholePlaneVertexι W 0) hwest,
        congrArg (wholePlaneVertexι W 0) heast⟩ }
  exact ⟨Q, u, e, hu, fun n => (he n).1, hSu, hSe⟩

end DirectedDistances.PaperProofs.Section5
