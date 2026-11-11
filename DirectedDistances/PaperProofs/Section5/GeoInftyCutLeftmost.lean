/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondenceFull
public import DirectedDistances.PaperProofs.Section5.GeoInftyIdentified

/-! # Infinite edge paths in the identified cut

Deterministic helpers toward Lemma 5.4 (`lem-geo-infty`,
These helpers do not assert the almost-sure leftmost-geodesic theorem. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- An infinite directed edge path in a cut, retaining parallel edges and
requiring the actual cut tail predicate on every traversed edge. -/
structure M0CutInfinitePath (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (D : M0CutData W H) (x : WholePlaneVertex W) where
  /-- The geometric edges in traversal order. -/
  edge : ℕ → WholePlaneEdge W
  /-- Every traversed edge belongs to the cut. -/
  inCut : ∀ n, edge n ∈ D.edges
  /-- Every traversed edge has the west-to-east cut orientation. -/
  directed : ∀ n, D.tail (edge n, false)
  /-- The initial endpoint is the prescribed starting vertex. -/
  start : wholePlaneEdgeWest W (edge 0) = x
  /-- Consecutive edges have matching endpoints. -/
  chain : ∀ n, wholePlaneEdgeEast W (edge n) = wholePlaneEdgeWest W (edge (n + 1))

namespace M0CutInfinitePath

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {D : M0CutData W H} {x : WholePlaneVertex W}

/-- The vertex reached after `n` edges, also the initial endpoint of edge `n`. -/
@[expose] def vertex (P : M0CutInfinitePath W H D x) (n : ℕ) : WholePlaneVertex W :=
  wholePlaneEdgeWest W (P.edge n)

/-- The edge stream supplies a directed cut step at every index. -/
theorem step (P : M0CutInfinitePath W H D x) (n : ℕ) :
    m0CutDirectedStep W H (D).seam (P.vertex n) (P.vertex (n + 1)) :=
  ⟨(P.edge n, false), P.directed n, P.inCut n, rfl, P.chain n⟩

/-- Each segment of the edge stream realizes its own length in the cut. -/
theorem segment_reachable (P : M0CutInfinitePath W H D x) (i n : ℕ) :
    m0CutReachableLength (m0CutDirectedStep W H D.seam) n
      (P.vertex i) (P.vertex (i + n)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨P.vertex (i + n), ih, P.step (i + n)⟩

/-- Infinite cut paths with the same edge stream are equal. -/
theorem edge_ext {P Q : M0CutInfinitePath W H D x} (he : P.edge = Q.edge) : P = Q := by
  cases P
  cases Q
  cases he
  rfl

/-- The actual segment from the `a`-th through the `b`-th edge is longest
among all finite cut paths between its endpoints (Definition 4.5). -/
@[expose] def HasLongestSegments (P : M0CutInfinitePath W H D x) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∀ n : ℕ,
    m0CutReachableLength (m0CutDirectedStep W H D.seam) n
      (P.vertex (a - 1)) (P.vertex b) → n ≤ b + 1 - a

end M0CutInfinitePath

section Identification

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

local notation "w" => shiftedStream W 0
local notation "V" => wholePlaneVertexι W 0
local notation "E" => wholePlaneEdgeι W 0
local notation "D" => m0CutData W H h hLL

/-- Every code path from the boundary maps to an infinite directed cut path,
without identifying distinct geometric edges. -/
@[expose] noncomputable def m0CutPathOfPresentPath (k : ℤ)
    (P : InfinitePresentPath w (boundaryPresentVertex w h k)) :
    M0CutInfinitePath W H D ((D).x k) where
  edge n := E (P.edge n)
  inCut n := by
    rw [(D).edges_eq h hLL]
    exact ⟨P.edge n, rfl⟩
  directed n := (m0Cut_tail_iff W H h hLL (P.edge n, false)).2
    ⟨rfl, (P.edge_outgoing_at_initial w n).1⟩
  start := by
    rw [m0Cut_edgeWest, (D).x_eq h hLL]
    exact congrArg V (P.first_edge_outgoing w).2
  chain n := by
    rw [m0Cut_edgeEast, m0Cut_edgeWest]
    exact congrArg V ((P.edge_incoming_at_succ w n).2.trans
      (P.edge_outgoing_at_initial w (n + 1)).2.symm)

/-- Every infinite cut path from `x_k` lifts to a code path. The equality
holds edge by edge, and the finite-prefix endpoints are identified as well. -/
theorem m0Cut_infinitePath_lift (k : ℤ)
    (Q : M0CutInfinitePath W H D ((D).x k)) :
    ∃ P : InfinitePresentPath w (boundaryPresentVertex w h k),
      (∀ n, E (P.edge n) = Q.edge n) ∧
      ∀ n, V (P.initial n).1.id = Q.vertex n := by
  classical
  have he : ∀ n, ∃ e : ℕ, E e = Q.edge n := by
    intro n
    have hn := Q.inCut n
    rw [(D).edges_eq h hLL] at hn
    exact hn
  choose e he using he
  have hp (n : ℕ) : EdgePresent w (e n) := by
    have ht := Q.directed n
    rw [← he n] at ht
    exact ((m0Cut_tail_iff W H h hLL (e n, false)).1 ht).2
  have hc (n : ℕ) : edgeEast w (e n) = edgeWest w (e (n + 1)) := by
    apply wholePlaneVertexι_injective W 0
    rw [← m0Cut_edgeEast, ← m0Cut_edgeWest, he n, he (n + 1)]
    exact Q.chain n
  have hstart : edgeWest w (e 0) = boundaryVertex w h k := by
    apply wholePlaneVertexι_injective W 0
    rw [← m0Cut_edgeWest, he 0, Q.start, (D).x_eq h hLL]
  have hprefix : ∀ n, ∃ q : Path (boundaryPresentVertex w h k)
      (⟨edgeWest w (e n)⟩ : PresentVertex w),
      q.length = n ∧ pathEdgeList q = List.ofFn (fun i : Fin n => e i.val) := by
    intro n
    induction n with
    | zero =>
      rw [hstart]
      exact ⟨.nil, rfl, rfl⟩
    | succ n ih =>
      obtain ⟨q, hlen, hedge⟩ := ih
      let a : (⟨edgeWest w (e n)⟩ : PresentVertex w) ⟶
          ⟨edgeWest w (e (n + 1))⟩ := ⟨e n, hp n, rfl, hc n⟩
      refine ⟨q.cons a, ?_, ?_⟩
      · exact congrArg (· + 1) hlen
      · simp only [pathEdgeList, hedge, List.ofFn_succ', List.concat_eq_append,
          Fin.val_castSucc, Fin.val_last]
        rfl
  choose q hlen hedge using hprefix
  let P : InfinitePresentPath w (boundaryPresentVertex w h k) :=
    ⟨e, fun n => ⟨⟨edgeWest w (e n)⟩, q n⟩, hlen, hedge⟩
  refine ⟨P, he, fun n => ?_⟩
  change V (edgeWest w (e n)) = wholePlaneEdgeWest W (Q.edge n)
  rw [← m0Cut_edgeWest, he n]

/-- The map from boundary-started code paths onto all infinite cut paths is
surjective, as equality of paths retaining their edge identities. -/
theorem m0Cut_infinitePath_surjective (k : ℤ) :
    Function.Surjective (m0CutPathOfPresentPath W H h hLL k) := by
  intro Q
  obtain ⟨P, he, _⟩ := m0Cut_infinitePath_lift W H h hLL k Q
  exact ⟨P, M0CutInfinitePath.edge_ext (funext he)⟩

/-- The mapped path visits exactly the represented prefix endpoints. -/
theorem m0CutPathOfPresentPath_vertex (k : ℤ)
    (P : InfinitePresentPath w (boundaryPresentVertex w h k)) (n : ℕ) :
    (m0CutPathOfPresentPath W H h hLL k P).vertex n = V (P.initial n).1.id := by
  change wholePlaneEdgeWest W (E (P.edge n)) = V (P.initial n).1.id
  rw [m0Cut_edgeWest, (P.edge_outgoing_at_initial w n).2]

/-- Finite paths between any two vertices of a lifted path preserve every
length. The comparison includes all cut competitors, not only mapped paths. -/
theorem m0Cut_path_lengths_iff (k : ℤ)
    (P : InfinitePresentPath w (boundaryPresentVertex w h k)) (i j n : ℕ) :
    m0CutReachableLength (m0CutDirectedStep W H (D).seam) n
      (V (P.initial i).1.id) (V (P.initial j).1.id) ↔
    ∃ q : Path (P.initial i).1 (P.initial j).1, q.length = n :=
  m0Cut_reachableLength_iff_presentPath W H h hLL (D).seam
    (m0Cut_seamEdge_iff W H h hLL) n (P.initial i).1.id (P.initial j).1.id

/-- Transport preserves precisely the LDP finite-segment condition, with
the source's `1 ≤ a ≤ b` indexing and all finite cut competitors. -/
theorem m0Cut_hasLongestSegments_iff (k : ℤ)
    (P : InfinitePresentPath w (boundaryPresentVertex w h k)) :
    (m0CutPathOfPresentPath W H h hLL k P).HasLongestSegments ↔
      P.HasLongestSegments := by
  constructor
  · intro hcut
    have hprefix (N : ℕ) : IsLongest (P.initial N).2 := by
      intro q
      cases N with
      | zero =>
        have hz := (P.initial 0).2.eq_of_length_zero (P.prefix_length 0)
        have hempty {u v : PresentVertex w} (r : Path u v) (huv : u = v) :
            r.length = 0 := by
          subst v
          exact presentVertex_acyclic w _ r
        have hq : q.length = 0 := hempty q hz
        rw [hq, P.prefix_length]
      | succ N =>
        have hq : m0CutReachableLength (m0CutDirectedStep W H (D).seam) q.length
            (V (P.initial 0).1.id) (V (P.initial (N + 1)).1.id) := by
          have hz := congrArg PresentVertex.id
            ((P.initial 0).2.eq_of_length_zero (P.prefix_length 0)).symm
          rw [hz]
          exact (m0Cut_reachableLength_iff_presentPath W H h hLL (D).seam
            (m0Cut_seamEdge_iff W H h hLL) q.length
            (boundaryVertex w h k) (P.initial (N + 1)).1.id).2 ⟨q, rfl⟩
        have hb := hcut 1 (N + 1) le_rfl (by omega) q.length
        rw [Nat.sub_self, m0CutPathOfPresentPath_vertex,
          m0CutPathOfPresentPath_vertex] at hb
        have hh := hb hq
        rw [P.prefix_length]
        omega
    intro a b ha hab
    obtain ⟨z, p, q, hpq, hp⟩ := (P.initial b).2.exists_eq_comp_of_le_length
      (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
    refine ⟨z, q, ?_, ?_, ?_⟩
    · have hlen := P.prefix_length b
      rw [hpq, Path.length_comp, hp] at hlen
      omega
    · rw [← P.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
      exact List.drop_left.symm
    · have hopt := hprefix b
      rw [hpq] at hopt
      exact hopt.of_comp_right
  · intro hP a b ha hab n hn
    rw [m0CutPathOfPresentPath_vertex, m0CutPathOfPresentPath_vertex] at hn
    obtain ⟨q, hq⟩ := (m0Cut_path_lengths_iff W H h hLL k P (a - 1) b n).1 hn
    have hi : a - 1 + (b + 1 - a) = b := by omega
    have hsplit := P.exists_shift_split (a - 1) (b + 1 - a)
    rw [hi] at hsplit
    obtain ⟨p, r, hpr, _, hlen, _⟩ := hsplit
    have hopt := P.initial_isLongest w hP b
    rw [hpr] at hopt
    have hh := hopt.of_comp_right q
    rw [hq, hlen] at hh
    exact hh

/-- Every infinite LDP geodesic on the cut is represented by the existing
identified-geodesic carrier, with exactly its original geometric edge stream.
No planar leftmost condition is included in this assertion. -/
theorem m0Cut_ldp_geodesic_lift (k : ℤ)
    (Q : M0CutInfinitePath W H D ((D).x k)) (hQ : Q.HasLongestSegments) :
    ∃ P : M0CutInfiniteGeodesic W H h hLL k true,
      ∀ n, E (P.codePath.edge n) = Q.edge n := by
  obtain ⟨P, he, hv⟩ := m0Cut_infinitePath_lift W H h hLL k Q
  have heq : m0CutPathOfPresentPath W H h hLL k P = Q :=
    M0CutInfinitePath.edge_ext (funext he)
  have hP : P.HasLongestSegments :=
    (m0Cut_hasLongestSegments_iff W H h hLL k P).1 (heq.symm ▸ hQ)
  let T : M0CutInfiniteGeodesic W H h hLL k true :=
    { codePath := P
      segments := hP
      startsAtCutBoundary := Q.start.symm.trans (hv 0).symm
      cutStep := fun n => by
        rw [hv n, hv (n + 1)]
        exact Q.step n }
  refine ⟨T, fun n => ?_⟩
  change E (P.edge n) = Q.edge n
  exact he n

/-- Conversely, the edge stream of an identified LDP geodesic is an actual
infinite LDP geodesic in the cut, with the same finite-segment condition. -/
theorem m0Cut_ldp_geodesic_realized (k : ℤ)
    (P : M0CutInfiniteGeodesic W H h hLL k true) :
    ∃ Q : M0CutInfinitePath W H D ((D).x k),
      Q.HasLongestSegments ∧ ∀ n, Q.edge n = E (P.codePath.edge n) := by
  refine ⟨m0CutPathOfPresentPath W H h hLL k P.codePath,
    (m0Cut_hasLongestSegments_iff W H h hLL k P.codePath).2 P.segments, ?_⟩
  intro n
  rfl

end Identification

section Drawing

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W))

local notation "w" => shiftedStream W 0
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hp H
local notation "P0" => monotoneFamilyDrawing w ((And.left H) 0) (monotone_family_all w)

/-- The glued drawing has exactly the same trace on every run-zero edge
stream. This uses the proved arc restriction, not just the rotation system. -/
theorem m0Cut_pathTrace_eq (e : ℕ → ℕ) :
    pathTrace G (fun n => wholePlaneDartι W 0 (e n, false)) =
      pathTrace P0 (fun n => (e n, false)) := by
  simp only [pathTrace, WholePlanePastGlueM0Restriction.restrict_arc]

/-- The full closed between-region agrees literally in the glued drawing
and the code drawing for any two represented edge streams. The two rays here
are arbitrary; identification of a source rightmost ray is a separate claim. -/
theorem m0Cut_closedBetween_eq (p r : ℕ → ℕ) :
    closedBetween
      (pathTrace G (fun n => wholePlaneDartι W 0 (p n, false)))
      (pathTrace G (fun n => wholePlaneDartι W 0 (r n, false))) =
    closedBetween (pathTrace P0 (fun n => (p n, false)))
      (pathTrace P0 (fun n => (r n, false))) := by
  rw [m0Cut_pathTrace_eq, m0Cut_pathTrace_eq]

variable (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

local notation "D" => m0CutData W H h hLL

/-- The universal LDP-geodesic containment comparison transfers in both
directions, including every infinite cut competitor. The reference streams
`p` and `r` are arbitrary: this does not identify `r` as a rightmost ray or
assert existence of a path with this comparison property. -/
theorem m0Cut_ldp_containment_iff (k : ℤ) (p r : ℕ → ℕ) :
    (∀ Q : M0CutInfinitePath W H D ((D).x k), Q.HasLongestSegments →
      pathTrace G (fun n => (Q.edge n, false)) ⊆
        closedBetween
          (pathTrace G (fun n => wholePlaneDartι W 0 (p n, false)))
          (pathTrace G (fun n => wholePlaneDartι W 0 (r n, false)))) ↔
    (∀ Q : InfinitePresentPath w (boundaryPresentVertex w h k),
      Q.HasLongestSegments → pathTrace P0 (fun n => (Q.edge n, false)) ⊆
        closedBetween (pathTrace P0 (fun n => (p n, false)))
          (pathTrace P0 (fun n => (r n, false)))) := by
  constructor
  · intro hc Q hQ
    have ht := hc (m0CutPathOfPresentPath W H h hLL k Q)
      ((m0Cut_hasLongestSegments_iff W H h hLL k Q).2 hQ)
    change pathTrace G (fun n => wholePlaneDartι W 0 (Q.edge n, false)) ⊆ _ at ht
    rw [m0Cut_pathTrace_eq, m0Cut_closedBetween_eq] at ht
    exact ht
  · intro hc Q hQ
    obtain ⟨P, rfl⟩ := m0Cut_infinitePath_surjective W H h hLL k Q
    have ht := hc P ((m0Cut_hasLongestSegments_iff W H h hLL k P).1 hQ)
    change pathTrace G (fun n => wholePlaneDartι W 0 (P.edge n, false)) ⊆ _
    rw [m0Cut_pathTrace_eq, m0Cut_closedBetween_eq]
    exact ht

end Drawing
end DirectedDistances.PaperProofs.Section5
