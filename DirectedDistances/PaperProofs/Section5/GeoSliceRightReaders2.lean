/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRightReaders

/-! Right-side ambient path replacement, coherent candidate lifting and intrinsic
clockwise selector uniqueness. No numbered paper result is claimed. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4 Quiver
open scoped Classical

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: an ambient directed path crossing from the
closed left side to the closed right side visits a vertex of the seam. -/
theorem m0GeodesicRightSide_path_hits_seam
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {u v : PresentVertex (shiftedStream W 0)} (p : Path u v)
    (hu : u.id ∈ m0GeodesicSideVertices hp P .left)
    (hv : v.id ∈ m0GeodesicSideVertices hp P .right) :
    ∃ j : ℕ, (P.codePath.initial j).1 ∈ p.vertices := by
  have atSeam {z : PresentVertex (shiftedStream W 0)}
      (hl : z.id ∈ m0GeodesicSideVertices hp P .left)
      (hr : z.id ∈ m0GeodesicSideVertices hp P .right) :
      ∃ j : ℕ, (P.codePath.initial j).1 = z := by
    have hz : z.id ∈ m0GeodesicVertices P := by
      rw [← m0GeodesicSideVertices_inter hp P]
      exact ⟨hl, hr⟩
    obtain ⟨j, hj⟩ := hz
    exact ⟨j, congrArg PresentVertex.mk hj⟩
  have aux : ∀ {z : PresentVertex (shiftedStream W 0)} (q : Path u z),
      z.id ∈ m0GeodesicSideVertices hp P .right →
        ∃ j : ℕ, (P.codePath.initial j).1 ∈ q.vertices := by
    intro z q
    induction q with
    | nil =>
      intro hr
      obtain ⟨j, hj⟩ := atSeam hu hr
      exact ⟨j, hj ▸ Path.end_mem_vertices Path.nil⟩
    | @cons y z q e ih =>
      intro hz
      by_cases hy : y.id ∈ m0GeodesicSideVertices hp P .right
      · obtain ⟨j, hj⟩ := ih hy
        exact ⟨j, (Path.mem_vertices_cons q e).mpr (Or.inl hj)⟩
      · rcases m0GeodesicSideEdges_cover hp P e.val with he | he
        · have hzl : z.id ∈ m0GeodesicSideVertices hp P .left :=
            e.property.2.2 ▸ (m0GeodesicSide_endpoints hp P .left e.val he).2
          obtain ⟨j, hj⟩ := atSeam hzl hz
          exact ⟨j, hj ▸ Path.end_mem_vertices (q.cons e)⟩
        · exact (hy (e.property.2.1 ▸
            (m0GeodesicSide_endpoints hp P .right e.val he).1)).elim
  exact aux p hv

/-- Helper toward Lemma 5.6: every ambient path between right-side vertices
has a right-side competitor at least as good in the chosen metric mode. -/
theorem m0GeodesicRightSide_path_dominance
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {u v : PresentVertex (shiftedStream W 0)} (p : Path u v)
    (hu : u.id ∈ (m0GeodesicSide hp P .right).vertices)
    (hv : v.id ∈ (m0GeodesicSide hp P .right).vertices) :
    ∃ r : Path u v,
      (if longest then p.length ≤ r.length else r.length ≤ p.length) ∧
      ∀ e ∈ pathEdgeList r, e ∈ (m0GeodesicSide hp P .right).edges := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    by_cases hz : p.length = 0
    · obtain rfl := p.eq_of_length_zero hz
      obtain rfl := p.eq_nil_of_length_zero hz
      exact ⟨.nil, by cases longest <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          simp only [Path.length_nil] at hn ⊢ <;> omega,
        fun _ he => False.elim (List.not_mem_nil he)⟩
    · obtain ⟨b, e, t, hp', hlen⟩ := p.length_ne_zero_iff_eq_comp.mp hz
      by_cases he : e.val ∈ (m0GeodesicSide hp P .right).edges
      · have hbl : b.id ∈ (m0GeodesicSide hp P .right).vertices :=
          e.property.2.2 ▸ (m0GeodesicSide_endpoints hp P .right e.val he).2
        obtain ⟨r, hrlen, hr⟩ := ih t.length (by omega) t hbl hv rfl
        refine ⟨e.toPath.comp r, ?_, ?_⟩
        · rw [← hn, hp', Path.length_comp, Path.length_comp]
          cases longest <;> exact Nat.add_le_add_left hrlen _
        · intro f hf
          rw [pathEdgeList_comp] at hf
          rcases List.mem_append.mp hf with hf | hf
          · have hfe : f = e.val := by
              change f ∈ ([] ++ [e.val]) at hf
              exact List.mem_singleton.mp hf
            exact hfe ▸ he
          · exact hr f hf
      · have her := (m0GeodesicSideEdges_cover hp P e.val).resolve_right he
        have hur : u.id ∈ m0GeodesicSideVertices hp P .left :=
          e.property.2.1 ▸ (m0GeodesicSide_endpoints hp P .left e.val her).1
        have hus : u.id ∈ m0GeodesicVertices P := by
          rw [← m0GeodesicSideVertices_inter hp P]
          exact ⟨hur, hu⟩
        obtain ⟨i, hi⟩ := hus
        have hi' : (P.codePath.initial i).1 = u := congrArg PresentVertex.mk hi
        have hbr : b.id ∈ m0GeodesicSideVertices hp P .left :=
          e.property.2.2 ▸ (m0GeodesicSide_endpoints hp P .left e.val her).2
        obtain ⟨j, hj⟩ := m0GeodesicRightSide_path_hits_seam hp P t hbr hv
        obtain ⟨s, t', ht⟩ := t.exists_eq_comp_of_mem_vertices hj
        have hex : ∃ r : Path u (P.codePath.initial j).1,
            (if longest then (e.toPath.comp s).length ≤ r.length
              else r.length ≤ (e.toPath.comp s).length) ∧
            ∀ f ∈ pathEdgeList r, f ∈ (m0GeodesicSide hp P .right).edges := by
          subst u
          exact m0GeodesicSide_seamSegment_dominates hp P .right i j (e.toPath.comp s)
        obtain ⟨r, hrlen, hr⟩ := hex
        have hjl : (P.codePath.initial j).1.id ∈
            (m0GeodesicSide hp P .right).vertices := by
          have hm := m0Geodesic_initial_mem_vertices P j
          rw [← m0GeodesicSideVertices_inter hp P] at hm
          exact hm.2
        have hsplit : p.length = 1 + s.length + t'.length := by
          rw [hp', ht, Path.length_comp, Path.length_comp, Path.length_toPath]
          omega
        obtain ⟨r', hr'len, hr'⟩ := ih t'.length (by omega) t' hjl hv rfl
        refine ⟨r.comp r', ?_, ?_⟩
        · simp only [Path.length_comp, Path.length_toPath] at hrlen ⊢
          cases longest <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrlen hr'len ⊢ <;>
            omega
        · intro f hf
          rw [pathEdgeList_comp] at hf
          exact (List.mem_append.mp hf).elim (hr f) (hr' f)

/-- Helper toward Lemma 5.6: attained intrinsic optimal lengths in the
realized right side are attained ambient optimal lengths, in both modes.
The excursion-replacement theorem discharges the ambient comparisons. -/
theorem m0GeodesicRightSide_optimalLength_ambient
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ)
    (u v : (m0GeodesicSide hp P .right).vertices)
    (hopt : geometricSideOptimalLength (m0GeodesicSide hp P .right) longest n
      (.inl u) (.inl v)) :
    ∃ p : Path (⟨u.val⟩ : PresentVertex (shiftedStream W 0)) ⟨v.val⟩,
      p.length = n ∧ (if longest then IsLongest p else IsShortest p) := by
  obtain ⟨p, hpLen⟩ := m0GeodesicSide_walk_lifts hp P .right n u v hopt.1
  refine ⟨p, hpLen, ?_⟩
  cases longest with
  | false =>
    intro q
    obtain ⟨r, hr, he⟩ := m0GeodesicRightSide_path_dominance hp P q u.property v.property
    have hw := m0GeodesicSide_walk_of_path hp P .right r u.property v.property he
    have ho : n ≤ r.length := hopt.2 r.length hw
    rw [hpLen]
    exact ho.trans hr
  | true =>
    intro q
    obtain ⟨r, hr, he⟩ := m0GeodesicRightSide_path_dominance hp P q u.property v.property
    have hw := m0GeodesicSide_walk_of_path hp P .right r u.property v.property he
    have ho : r.length ≤ n := hopt.2 r.length hw
    rw [hpLen]
    exact hr.trans ho


private theorem right_reader_ray_vertices {M : GeometricSideSubmap}
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

private theorem right_reader_ray_darts {M : GeometricSideSubmap}
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

private def rightReaderDartPrefix {w : ℕ → Fin 3}
    (u : ℕ → PresentVertex w) (a : ∀ n, u n ⟶ u (n + 1)) :
    (n : ℕ) → Path (u 0) (u n)
  | 0 => .nil
  | n + 1 => (rightReaderDartPrefix u a n).cons (a n)

private theorem rightReaderDartPrefix_length {w : ℕ → Fin 3}
    (u : ℕ → PresentVertex w) (a : ∀ n, u n ⟶ u (n + 1)) (n : ℕ) :
    (rightReaderDartPrefix u a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

private theorem rightReaderDartPrefix_edges {w : ℕ → Fin 3}
    (u : ℕ → PresentVertex w) (a : ∀ n, u n ⟶ u (n + 1)) (n : ℕ) :
    pathEdgeList (rightReaderDartPrefix u a n) = List.ofFn (fun i : Fin n => (a i.val).val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [rightReaderDartPrefix, pathEdgeList, List.ofFn_succ', List.concat_eq_append,
      Fin.val_castSucc, Fin.val_last] using congrArg (fun l => l ++ [(a n).val]) ih

private theorem right_reader_segments_of_optimal_prefixes {w : ℕ → Fin 3}
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

/-- Helper toward Lemma 5.6: every intrinsic adjacent candidate in the
actual right side lifts to one infinite ambient cut geodesic from x_(k+1).
The equalities retain every vertex and individual directed dart, including
parallel-edge identity. No leftmost or angular comparison is asserted. -/
theorem m0GeodesicRightSide_adjacentCandidate_coherentAmbientLift
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp P .right)}
    (hc : geometricSideAdjacentGeodesicCandidate (m0GeodesicSide hp P .right)
      longest v d) :
    ∃ (Q : M0CutInfiniteGeodesic W H h hLL (k + 1) longest)
      (u : ℕ → (m0GeodesicSide hp P .right).vertices)
      (e : ℕ → (m0GeodesicSide hp P .right).edges),
      (∀ n, v n = .inl (u n)) ∧
      (∀ n, d n = .inr ⟨((e n).val, false), (e n).property⟩) ∧
      (∀ n, (Q.codePath.initial n).1.id = (u n).val) ∧
      (∀ n, Q.codePath.edge n = (e n).val) := by
  classical
  let M := m0GeodesicSide hp P .right
  obtain ⟨u, hu⟩ := right_reader_ray_vertices hc.1
  obtain ⟨e, he⟩ := right_reader_ray_darts hc.1 u hu
  let U : ℕ → PresentVertex (shiftedStream W 0) := fun n => ⟨(u n).val⟩
  let A : ∀ n, U n ⟶ U (n + 1) := fun n =>
    ⟨(e n).val, (he n).2.1, (he n).2.2.1, (he n).2.2.2⟩
  let R : InfinitePresentPath (shiftedStream W 0) (U 0) :=
    ⟨fun n => (e n).val, fun n => ⟨U n, rightReaderDartPrefix U A n⟩,
      rightReaderDartPrefix_length U A, rightReaderDartPrefix_edges U A⟩
  have hopt (n : ℕ) : if longest then IsLongest (R.initial n).2
      else IsShortest (R.initial n).2 := by
    have hn := hc.2.2 0 n
    rw [Nat.zero_add, hu 0, hu n] at hn
    obtain ⟨p, hlen, ho⟩ := m0GeodesicRightSide_optimalLength_ambient hp P n
      (u 0) (u n) hn
    have hlen' : (R.initial n).2.length = p.length := (R.prefix_length n).trans hlen.symm
    cases longest with
    | false => exact IsShortest.of_length_eq ho hlen'
    | true => exact IsLongest.of_length_eq ho hlen'
  have hseg := right_reader_segments_of_optimal_prefixes R longest hopt
  have hstart : U 0 = boundaryPresentVertex (shiftedStream W 0) h (k + 1) := by
    obtain ⟨b, hb, hi⟩ := hc.2.1
    rw [hu 0] at hi
    have hid : (u 0).val = boundaryVertex (shiftedStream W 0) h (k + 1) := by
      cases b with
      | inl z => exact False.elim hb
      | inr b =>
        have hb' : M.boundary 1 = b.val := hb
        have hi' : geometricSideDartInitial M b.val = (u 0).val := hi
        rw [← hb'] at hi'
        exact hi'.symm.trans (m0GeodesicRightSide_adjacent_start hp P)
    exact congrArg PresentVertex.mk hid
  have hex : ∃ S : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h (k + 1)),
      (if longest then S.HasLongestSegments else S.HasShortestSegments) ∧
      (∀ n, (S.initial n).1.id = (u n).val) ∧
      (∀ n, S.edge n = (e n).val) := by
    rw [← hstart]
    exact ⟨R, hseg, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨S, hS, hSu, hSe⟩ := hex
  have hSstart : (S.initial 0).1.id =
      boundaryVertex (shiftedStream W 0) h (k + 1) := by
    have hz := (S.initial 0).2.eq_of_length_zero (S.prefix_length 0)
    exact congrArg PresentVertex.id hz.symm
  let Q : M0CutInfiniteGeodesic W H h hLL (k + 1) longest := {
    codePath := S
    segments := hS
    startsAtCutBoundary := (m0CutData W H h hLL).x_eq h hLL (k + 1) |>.trans
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



/-- Helper toward Lemma 5.6: clockwise intrinsic selectors in a realized
right side have identical vertex and individual-dart streams. -/
theorem m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRay_unique
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {v d v' d' : ℕ → GeometricSideCell (m0GeodesicSide hp P .right)}
    (hl : IntrinsicallyLeftmostAdjacentRay (m0GeodesicSide hp P .right) longest v d)
    (hl' : IntrinsicallyLeftmostAdjacentRay (m0GeodesicSide hp P .right) longest v' d') :
    v = v' ∧ d = d' :=
  m0GeodesicSide_intrinsicallyLeftmostAdjacentRay_unique hp P .right hl hl'

/-- Helper toward Lemma 5.6: clockwise intrinsic uniqueness persists
on every complete marked representative of a realized right side. -/
theorem m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRay_unique_of_markedIso
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso (m0GeodesicSide hp P .right) N)
    {v d v' d' : ℕ → GeometricSideCell N}
    (hl : IntrinsicallyLeftmostAdjacentRay N longest v d)
    (hl' : IntrinsicallyLeftmostAdjacentRay N longest v' d') :
    v = v' ∧ d = d' := by
  have he := m0GeodesicRightSide_intrinsicallyLeftmostAdjacentRay_unique hp P
    (intrinsicallyLeftmostAdjacentRay_map (GeometricSideMarkedIso.symm I) longest hl)
    (intrinsicallyLeftmostAdjacentRay_map (GeometricSideMarkedIso.symm I) longest hl')
  exact ⟨funext fun i => I.equiv.symm.injective (congrFun he.1 i),
    funext fun i => I.equiv.symm.injective (congrFun he.2 i)⟩

/-- Helper toward Lemma 5.6: vertices of the realized adjacent ray,
retained as cells of the actual right side. -/
@[expose] def m0GeodesicRightSideAdjacentVertices
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
      ((P k).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P (k - 1)) .right).vertices) :
    ℕ → GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right) :=
  fun n => .inl ⟨((P k).codePath.initial n).1.id, (hcontain n).2⟩

/-- Helper toward Lemma 5.6: directed darts of the realized adjacent ray,
with geometric edge identity retained. -/
@[expose] def m0GeodesicRightSideAdjacentDarts
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
      ((P k).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P (k - 1)) .right).vertices) :
    ℕ → GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right) :=
  fun n => .inr ⟨((P k).codePath.edge n, false), (hcontain n).1⟩

/-- Helper toward Lemma 5.6: the candidate is the realized adjacent ray
itself, rather than an unspecified existential witness. -/
theorem m0GeodesicRightSide_realized_adjacentCandidate
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P k).codePath.edge n ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges ∧
      ((P k).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P (k - 1)) .right).vertices) :
    geometricSideAdjacentGeodesicCandidate (m0GeodesicSide hp (P (k - 1)) .right) longest
      (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) := by
  let M := m0GeodesicSide hp (P (k - 1)) .right
  have hr : geometricSideDirectedRay M
      (m0GeodesicRightSideAdjacentVertices hp P k hcontain)
      (m0GeodesicRightSideAdjacentDarts hp P k hcontain) := by
    intro n
    have hout := (P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) n
    have hin := (P k).codePath.edge_incoming_at_succ (shiftedStream W 0) n
    exact ⟨⟨hout.1, rfl⟩, hout.2,
      .inr ⟨((P k).codePath.edge n, true), (hcontain n).1⟩, rfl, hin.2⟩
  refine ⟨hr, ?_, ?_⟩
  · refine ⟨.inr ⟨M.boundary 1,
      m0GeodesicRightSide_boundary_mem_edges hp (P (k - 1)) 1⟩, rfl, ?_⟩
    change geometricSideDartInitial M (M.boundary 1) =
      ((P k).codePath.initial 0).1.id
    have hs := m0GeodesicRightSide_adjacent_start hp (P (k - 1))
    rw [sub_add_cancel] at hs
    exact hs.trans (m0Geodesic_initial_zero (P k)).symm
  · intro i n
    refine ⟨geometricSideDirectedRay_walk hr i n, ?_⟩
    intro m hm
    obtain ⟨r, hrlen⟩ := m0GeodesicSide_walk_lifts hp (P (k - 1)) .right m _ _ hm
    obtain ⟨p, q, hpq, _, hq, _⟩ := (P k).codePath.exists_shift_split i n
    cases longest with
    | false =>
      have hopt := (P k).codePath.initial_isShortest
        (shiftedStream W 0) (P k).segments (i + n)
      rw [hpq] at hopt
      have hle := hopt.of_comp_right r
      change n ≤ m
      simpa only [hq, hrlen] using hle
    | true =>
      have hopt := (P k).codePath.initial_isLongest
        (shiftedStream W 0) (P k).segments (i + n)
      rw [hpq] at hopt
      have hle := hopt.of_comp_right r
      change m ≤ n
      simpa only [hq, hrlen] using hle


section SourceFamily

variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hc : ∀ m : ℤ, ∃ a b : ℕ,
    M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
  (k : ℤ)

/-- Helper toward Lemma 5.6: the next source ray's vertex cells, with
right-side membership derived from leftmostness and adjacent coalescence. -/
@[expose] def m0GeodesicRightSideNextVertices :
    ℕ → GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right) :=
  m0GeodesicRightSideAdjacentVertices hp P k
    (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k)

/-- Helper toward Lemma 5.6: the next source ray's directed dart cells,
retaining every edge identity and deriving right-side membership. -/
@[expose] def m0GeodesicRightSideNextDarts :
    ℕ → GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right) :=
  m0GeodesicRightSideAdjacentDarts hp P k
    (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k)

/-- Helper toward Lemma 5.6: the actual next ray is an adjacent intrinsic
metric candidate, without a containment or identification premise. -/
theorem m0GeodesicRightSide_nextRay_candidate :
    geometricSideAdjacentGeodesicCandidate
      (m0GeodesicSide hp (P (k - 1)) .right) longest
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) :=
  m0GeodesicRightSide_realized_adjacentCandidate hp P k
    (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k)

/-- Helper toward Lemma 5.6: after the first dart, the actual next source
ray is first admissible in the clockwise scan from its incoming corner.
The step-zero boundary corner is a separate obligation. -/
theorem m0GeodesicRightSide_nextRay_firstAdmissible_succ (l : ℕ) :
    let M := m0GeodesicSide hp (P (k - 1)) .right
    let d := m0GeodesicRightSideNextDarts hp P T hleft hc k
    ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
      geometricSideRayIncomingCorner M d (l + 1) a ∧
      geometricSideClockwiseScan M a f n ∧ f n = d (l + 1) ∧
      ∀ (v' d' : ℕ → GeometricSideCell M),
        geometricSideAdjacentGeodesicCandidate M longest v' d' →
        (∀ j, j < l + 1 → d' j = d j) →
        ∀ j, j < n → f j ≠ d' (l + 1) := by
  let M := m0GeodesicSide hp (P (k - 1)) .right
  let w := shiftedStream W 0
  let d := m0GeodesicRightSideNextDarts hp P T hleft hc k
  let hcontain := m0GeodesicRightSide_nextRay_contained hp P T hleft hc k
  let i := l + 1
  let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
    ⟨((P k).codePath.edge l, true), (hcontain l).1⟩
  let e := (P k).codePath.edge l
  have ha : a.val = (e, true) := rfl
  have hcorner : geometricSideRayIncomingCorner M d i (.inr a) := rfl
  have hav : geometricSideDartInitial M a.val = ((P k).codePath.initial i).1.id :=
    ((P k).codePath.edge_incoming_at_succ w l).2
  let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
    ⟨((P k).codePath.edge i, false), (hcontain i).1⟩
  have hv : wholePlaneDartVertex W (wholePlaneDartι W 0 b.val) =
      wholePlaneDartVertex W (wholePlaneDartι W 0 a.val) := by
    rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι]
    apply congrArg (wholePlaneVertexι W 0)
    exact ((P k).codePath.edge_outgoing_at_initial w i).2.trans hav.symm
  have hba : wholePlaneDartι W 0 b.val ≠ wholePlaneDartι W 0 a.val := by
    intro he
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) he
    change false = true at hbit
    cases hbit
  obtain ⟨r, _, _, hfirst, hindices⟩ :=
    m0WholePlane_clockwiseFirstReturn_indices (H := H) (wholePlaneDartι W 0 a.val)
  obtain ⟨n, _, hnr, hnb⟩ := hindices (wholePlaneDartι W 0 b.val) hv hba
  obtain ⟨f, m, hscan, hend, hearlier⟩ :=
    m0GeodesicSide_clockwiseScan_before_ambientEndpoint hp (P (k - 1)) .right a b n hnb
  refine ⟨.inr a, f, m, hcorner, hscan, hend, ?_⟩
  intro v' d' hcandidate hpref j hj heq
  have hlift := m0GeodesicRightSide_adjacentCandidate_coherentAmbientLift
    hp (P (k - 1)) hcandidate
  rw [show k - 1 + 1 = k by omega] at hlift
  obtain ⟨Q, _, q, _, hdq, _, hQq⟩ := hlift
  have hprefEdge (t : ℕ) (ht : t < i) :
      Q.codePath.edge t = (P k).codePath.edge t := by
    have he := (hdq t).symm.trans ((hpref t ht).trans rfl)
    have he' := congrArg Subtype.val (Sum.inr.inj he)
    exact (hQq t).trans (congrArg Prod.fst he')
  have hvertex : ((P k).codePath.initial i).1 = (Q.codePath.initial i).1 := by
    apply InfinitePresentPath.initial_vertex_eq_of_prefix_eq
    apply congrArg List.ofFn
    funext t
    exact (hprefEdge t.val t.isLt).symm
  have harg := m0CutLeftmostXdp_raw_departureArg_le hp (P k) Q
    (T k) (hleft k) i i hvertex
  obtain ⟨c, t, hfc, htn, htc⟩ := hearlier j hj
  have hcq : c.val = ((q i).val, false) := by
    exact congrArg Subtype.val (Sum.inr.inj (hfc.symm.trans (heq.trans (hdq i))))
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    have htc0 : (wholePlaneDartι W 0 a.val : WholePlaneDart W) =
        wholePlaneDartι W 0 c.val := by
      subst t
      exact htc
    have hbit := congrArg (fun x : WholePlaneDart W => x.2) htc0
    change a.val.2 = c.val.2 at hbit
    rw [ha, hcq] at hbit
    cases hbit
  have hang := m0WholePlane_clockwiseIterate_departureAngle_lt
    (W := W) (H := H) (h := h) (hp := hp) (wholePlaneDartι W 0 a.val) r
    hfirst htpos htn hnr
  rw [htc, hnb, ha, hcq, ← hQq i] at hang
  have hraw := (m0WholePlane_incomingCorner_ccwTurn_lt_iff_rawArg_lt
    (W := W) (H := H) (h := h) (hp := hp) e (Q.codePath.edge i)
    ((P k).codePath.edge i)
    (Q.codePath.edge_outgoing_at_initial w i).1
    ((P k).codePath.edge_outgoing_at_initial w i).1).1 hang
  exact (not_lt_of_ge harg) hraw


/-- Helper toward Lemma 5.6: a finite clockwise scan to each next-ray
departure exists, including the stored outgoing corner at step zero.
This theorem makes no first-admissibility assertion at step zero. -/
theorem m0GeodesicRightSide_nextRay_incomingScan (i : ℕ) :
    let M := m0GeodesicSide hp (P (k - 1)) .right
    let d := m0GeodesicRightSideNextDarts hp P T hleft hc k
    ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
      geometricSideRayIncomingCorner M d i a ∧
      geometricSideClockwiseScan M a f n ∧ f n = d i := by
  let M := m0GeodesicSide hp (P (k - 1)) .right
  let hcontain := m0GeodesicRightSide_nextRay_contained hp P T hleft hc k
  cases i with
  | zero =>
    let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨M.boundary 1, m0GeodesicRightSide_boundary_mem_edges hp (P (k - 1)) 1⟩
    let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((P k).codePath.edge 0, false), (hcontain 0).1⟩
    have hs := m0GeodesicRightSide_adjacent_start hp (P (k - 1))
    rw [sub_add_cancel] at hs
    have hv : geometricSideDartInitial M a.val = geometricSideDartInitial M b.val :=
      hs.trans ((m0Geodesic_initial_zero (P k)).symm.trans
        ((P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) 0).2.symm)
    obtain ⟨f, n, hf, hend⟩ := m0GeodesicSide_clockwiseScan_exists
      hp (P (k - 1)) .right a b hv
    exact ⟨.inr a, f, n, rfl, hf, hend⟩
  | succ i =>
    let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((P k).codePath.edge i, true), (hcontain i).1⟩
    let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((P k).codePath.edge (i + 1), false), (hcontain (i + 1)).1⟩
    have hv : geometricSideDartInitial M a.val = geometricSideDartInitial M b.val :=
      ((P k).codePath.edge_incoming_at_succ (shiftedStream W 0) i).2.trans
        ((P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) (i + 1)).2.symm
    obtain ⟨f, n, hf, hend⟩ := m0GeodesicSide_clockwiseScan_exists
      hp (P (k - 1)) .right a b hv
    exact ⟨.inr a, f, n, rfl, hf, hend⟩

/-- Helper toward Lemma 5.6: every competing intrinsic right-side ray
with the same prefix has at most the source ray's counterclockwise turn
from any reversed raw dart. This comparison includes step zero. -/
theorem m0GeodesicRightSide_nextRay_candidate_counterclockwiseTurn_le
    {v' d' : ℕ → GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)}
    (hcandidate : geometricSideAdjacentGeodesicCandidate
      (m0GeodesicSide hp (P (k - 1)) .right) longest v' d')
    (i e : ℕ)
    (hpref : ∀ j, j < i → d' j = m0GeodesicRightSideNextDarts hp P T hleft hc k j) :
    ccwTurn
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc (e, true)).initialDirection
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc
          (geoSliceCellDartValue (d' i))).initialDirection ≤
    ccwTurn
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc (e, true)).initialDirection
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc
          ((P k).codePath.edge i, false)).initialDirection := by
  have hlift := m0GeodesicRightSide_adjacentCandidate_coherentAmbientLift
    hp (P (k - 1)) hcandidate
  rw [show k - 1 + 1 = k by omega] at hlift
  obtain ⟨Q, _, q, _, hdq, _, hQq⟩ := hlift
  have hprefEdge (t : ℕ) (ht : t < i) :
      Q.codePath.edge t = (P k).codePath.edge t := by
    have he := (hdq t).symm.trans ((hpref t ht).trans rfl)
    exact (hQq t).trans (congrArg Prod.fst
      (congrArg Subtype.val (Sum.inr.inj he)))
  have hvertex : ((P k).codePath.initial i).1 = (Q.codePath.initial i).1 := by
    apply InfinitePresentPath.initial_vertex_eq_of_prefix_eq
    apply congrArg List.ofFn
    funext t
    exact (hprefEdge t.val t.isLt).symm
  rw [hdq i]
  change ccwTurn _ (((monotoneFamilyDrawing _ _ _).arc
    ((q i).val, false)).initialDirection) ≤ _
  rw [← hQq i]
  exact m0CutLeftmostXdp_raw_counterclockwiseTurn_le hp (P k) Q
    (T k) (hleft k) e i i hvertex

end SourceFamily

/-- Helper toward Lemma 5.6: right-side exterior marks are forward
darts. In particular boundary dart 1 is not a reversed incoming dart. -/
theorem m0GeodesicRightSide_boundary_bit
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) :
    ((m0GeodesicSide hp P .right).boundary i).2 = false := rfl

/-- Helper toward Lemma 5.6: reversing boundary dart 0 gives a geometric
incoming dart at the adjacent starting vertex, but it is a different stored
mark from boundary dart 1 in the existing intrinsic selector. -/
theorem m0GeodesicRightSide_reverse_boundary_zero_initial
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    geometricSideDartInitial (m0GeodesicSide hp P .right)
      (((m0GeodesicSide hp P .right).boundary 0).1, true) =
        boundaryVertex (shiftedStream W 0) h (k + 1) := by
  simpa only [m0GeodesicSide, m0GeodesicBoundaryDart, Nat.cast_zero, add_zero,
    geometricSideDartInitial, ↓reduceIte] using
    (boundaryOuterEdge_endpoints (shiftedStream W 0) h k).2.1

/-- Helper toward Lemma 5.6: the existing selector must choose boundary
dart 1 immediately whenever that outgoing dart itself extends to an adjacent
metric candidate. This exposes the separate zero-step selection obligation. -/
theorem intrinsicallyLeftmostAdjacentRay_initial_eq_boundary_candidate
    (M : GeometricSideSubmap) (longest : Bool)
    {v d v' d' : ℕ → GeometricSideCell M}
    (hl : IntrinsicallyLeftmostAdjacentRay M longest v d)
    (hc : geometricSideAdjacentGeodesicCandidate M longest v' d')
    (hb : geometricSideRelation M (.boundary 1) (d' 0) (d' 0)) :
    d 0 = d' 0 := by
  obtain ⟨a, f, n, ha, hf, hend, hfirst⟩ := hl.2 0
  have hab : a = d' 0 := geometricSideRelation_boundary_self_unique M 1 ha hb
  cases n with
  | zero => exact hend.symm.trans (hf.1.trans hab)
  | succ n =>
    exact False.elim (hfirst v' d' hc
      (fun j hj => (Nat.not_lt_zero j hj).elim) 0 (Nat.zero_lt_succ n)
      (hf.1.trans hab))


/-- Helper toward Lemma 5.6: the right-side clockwise code reader uses
the existing leftmost selector without reversing the stored rotation. -/
@[expose] noncomputable def geoSliceRightLeftmostRayCodeOption (longest : Bool)
    (M : GeometricSideSubmap) : Option GeoSliceSeamRayCode :=
  geoSliceOneSideRayCodeOption longest M

/-- Helper toward Lemma 5.6: the clockwise right-side individual-edge
reader has no invented edge when the countable search fails. -/
@[expose] noncomputable def geoSliceRightLeftmostRayEdgeOption (longest : Bool)
    (i : ℕ) (M : GeometricSideSubmap) : Option ℕ :=
  geoSliceOneSideRayEdgeOption longest i M

/-- Helper toward Lemma 5.6: clockwise right-side offsets are returned
in source order, old-seam offset first and next-ray offset second. -/
@[expose] noncomputable def geoSliceRightLeftmostOffsetsOption (longest : Bool)
    (M : GeometricSideSubmap) : Option (ℕ × ℕ) :=
  (geoSliceOneSideOffsetsOption longest M).map Prod.swap

local instance : MeasurableSpace GeoSliceSeamRayCode := ⊤
local instance : MeasurableSpace (Option GeoSliceSeamRayCode) := ⊤
local instance : MeasurableSpace (Option ℕ) := ⊤
local instance : MeasurableSpace (Option (ℕ × ℕ)) := ⊤

/-- Helper toward Lemma 5.6: the clockwise right-side ray code reader
is measurable in the ten-field complete side code. -/
theorem measurable_geoSliceRightLeftmostRayCodeOption (longest : Bool) :
    Measurable (geoSliceRightLeftmostRayCodeOption longest) :=
  measurable_geoSliceOneSideRayCodeOption longest

/-- Helper toward Lemma 5.6: every individual edge returned by the
clockwise right-side reader is measurable. -/
theorem measurable_geoSliceRightLeftmostRayEdgeOption (longest : Bool) (i : ℕ) :
    Measurable (geoSliceRightLeftmostRayEdgeOption longest i) :=
  measurable_geoSliceOneSideRayEdgeOption longest i

/-- Helper toward Lemma 5.6: the clockwise right-side least-offset
reader is jointly measurable in the source order of its two offsets. -/
theorem measurable_geoSliceRightLeftmostOffsetsOption (longest : Bool) :
    Measurable (geoSliceRightLeftmostOffsetsOption longest) :=
  (measurable_of_countable (fun p : Option (ℕ × ℕ) => p.map Prod.swap)).comp
    (measurable_geoSliceOneSideOffsetsOption longest)

/-- Helper toward Lemma 5.6: one event supplies both metrics and all cuts
with the actual right-side candidate and clockwise first admissibility at
every positive step. Initial-step first admissibility is not asserted. -/
theorem m0Cut_ae_rightSide_nextRay_candidate_and_positive_firstAdmissible :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ hleft : ∀ k,
        Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k),
      ∃ hc : ∀ m : ℤ, ∃ a b : ℕ,
        M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b,
      ∀ k : ℤ,
      let M := m0GeodesicSide hp (P (k - 1)) .right
      let v := m0GeodesicRightSideNextVertices hp P T hleft hc k
      let d := m0GeodesicRightSideNextDarts hp P T hleft hc k
      geometricSideAdjacentGeodesicCandidate M longest v d ∧
      ∀ l : ℕ,
        ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
          geometricSideRayIncomingCorner M d (l + 1) a ∧
          geometricSideClockwiseScan M a f n ∧ f n = d (l + 1) ∧
          ∀ (v' d' : ℕ → GeometricSideCell M),
            geometricSideAdjacentGeodesicCandidate M longest v' d' →
            (∀ j, j < l + 1 → d' j = d j) →
            ∀ j, j < n → f j ≠ d' (l + 1) := by
  filter_upwards [m0Cut_ae_geodesicSlice_left_right_side_containment] with W hW
  obtain ⟨H, h, hLL, hp, hmodes⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, _, hc, _⟩ := hmodes longest
  have hc' (m : ℤ) : ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b := by
    have hm := hc (m + 1)
    rw [show m + 1 - 1 = m by omega] at hm
    exact hm
  exact ⟨P, T, hleft, hc', fun k =>
    ⟨m0GeodesicRightSide_nextRay_candidate hp P T hleft hc' k,
      m0GeodesicRightSide_nextRay_firstAdmissible_succ hp P T hleft hc' k⟩⟩

end DirectedDistances.PaperProofs.Section5
































































































/- 31 declarations, including private helpers and definitions, compiled with
exit 0. Every transitive axiom set was contained in
{propext, Classical.choice, Quot.sound}; no custom axiom or sorryAx appeared.
The probes were removed before the final production compile. Independent
Only GeoSliceRightReaders2.lean was edited; no numbered result is closed. -/
