/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryData

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The two extremal directed path problems considered in Lemma `lem-lr-ind` -/
inductive XDP where
  | ldp
  | sdp
  deriving DecidableEq, Repr

/-- A simple directed source-to-sink dart path is an LDP geodesic when its
length is at least that of every such path (`lem-lr-ind`, -/
@[expose] def IsLDPGeodesic (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (_P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map B.source B.sink m), m ≤ n

/-- A simple directed source-to-sink dart path is an SDP geodesic when its
length is at most that of every such path (`lem-lr-ind`, -/
@[expose] def IsSDPGeodesic (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (_P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  ∀ {m : ℕ} (_Q : SimpleDirectedDartPath B.map B.source B.sink m), n ≤ m

/-- Dispatch to the longest or shortest directed path predicate named by the -/
@[expose] def IsXDPGeodesic (B : BipolarTriangulationWithBoundary D ℓ r)
    (x : XDP) {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  match x with
  | .ldp => IsLDPGeodesic B P
  | .sdp => IsSDPGeodesic B P

namespace SimpleDirectedDartPath

variable {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}

/-- For fixed endpoints and length, a simple directed dart path is determined
by its dart list: the start vertex and each dart incidence determine its -/
theorem eq_of_darts_eq {P Q : SimpleDirectedDartPath M s t n}
    (hd : P.darts = Q.darts) : P = Q := by
  have hv : P.vertices = Q.vertices := by
    apply List.ext_get_iff.mpr
    constructor
    · rw [P.vertices_length, Q.vertices_length]
    · intro i hiP hiQ
      induction i with
      | zero =>
          simp only [P.start_vertex, Q.start_vertex]
      | succ i ih =>
          have hiD : i < P.darts.length := by
            have hiN : i < n := by simpa [P.vertices_length] using hiP
            simpa [P.darts_length] using hiN
          have hiD' : i < Q.darts.length := by
            have hiN : i < n := by simpa [Q.vertices_length] using hiQ
            simpa [Q.darts_length] using hiN
          have get_of_eq : ∀ {xs ys : List D} (h : xs = ys) (j : ℕ)
              (hxs : j < xs.length) (hys : j < ys.length),
              xs.get ⟨j, hxs⟩ = ys.get ⟨j, hys⟩ := by
            intro xs ys h j hxs hys
            cases h
            rfl
          have hsP := P.edge_step ⟨i, hiD⟩
          have hsQ := Q.edge_step ⟨i, hiD'⟩
          have hdget := get_of_eq hd i hiD hiD'
          calc
            P.vertices.get ⟨i + 1, hiP⟩ = dartHeadVertex M (P.darts.get ⟨i, hiD⟩) :=
              hsP.2.2.2
            _ = dartHeadVertex M (Q.darts.get ⟨i, hiD'⟩) := by rw [hdget]
            _ = Q.vertices.get ⟨i + 1, hiQ⟩ := hsQ.2.2.2.symm
  cases P with
  | mk pd pv pdl pvl pnd ps pe pes =>
    cases Q with
    | mk qd qv qdl qvl qnd qs qe qes =>
        simp_all

/-- Equality of fixed-index simple directed paths is equivalent to equality
of their dart lists. -/
theorem ext_darts {P Q : SimpleDirectedDartPath M s t n} :
    P = Q ↔ P.darts = Q.darts := by
  constructor
  · intro h
    exact congrArg SimpleDirectedDartPath.darts h
  · exact eq_of_darts_eq

end SimpleDirectedDartPath

private theorem simplePath_length_lt_card
    (B : BipolarTriangulationWithBoundary D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    n < B.map.toCombinatorialMap.numVertices := by
  classical
  have hlen := P.vertices_nodup.length_le_card
  rw [P.vertices_length] at hlen
  have hcard : n + 1 ≤ B.map.toCombinatorialMap.numVertices := by
    simpa [CombinatorialMap.numVertices] using hlen
  omega

/-- The finite set of lengths realized by simple directed source-to-sink dart
paths. Every such length is strictly below the number of vertices, by
distinctness of the path's vertex list. -/
@[expose] noncomputable def sourceSinkPathLengths
    (B : BipolarTriangulationWithBoundary D ℓ r) : Finset ℕ := by
  classical
  exact (Finset.range B.map.toCombinatorialMap.numVertices).filter fun n =>
    ∃ _P : SimpleDirectedDartPath B.map B.source B.sink n, True

/-- Membership in `sourceSinkPathLengths` means that a path of that length
exists. -/
theorem mem_sourceSinkPathLengths
    (B : BipolarTriangulationWithBoundary D ℓ r) (n : ℕ) :
    n ∈ sourceSinkPathLengths B ↔
      ∃ _P : SimpleDirectedDartPath B.map B.source B.sink n, True := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨P, _⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (simplePath_length_lt_card B P), ⟨P, trivial⟩⟩

theorem sourceSinkPathLengths_nonempty
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    (sourceSinkPathLengths B).Nonempty := by
  refine ⟨ℓ, ?_⟩
  exact (mem_sourceSinkPathLengths B ℓ).2 ⟨B.leftPath, trivial⟩

/-- The maximum length of a simple directed source-to-sink dart path. -/
@[expose] noncomputable def ldpLength
    (B : BipolarTriangulationWithBoundary D ℓ r) : ℕ :=
  (sourceSinkPathLengths B).max' (sourceSinkPathLengths_nonempty B)

/-- The minimum length of a simple directed source-to-sink dart path. -/
@[expose] noncomputable def sdpLength
    (B : BipolarTriangulationWithBoundary D ℓ r) : ℕ :=
  (sourceSinkPathLengths B).min' (sourceSinkPathLengths_nonempty B)

/-- The maximal path length is attained. -/
theorem ldpLength_mem (B : BipolarTriangulationWithBoundary D ℓ r) :
    ldpLength B ∈ sourceSinkPathLengths B := by
  exact Finset.max'_mem _ _

/-- The minimal path length is attained. -/
theorem sdpLength_mem (B : BipolarTriangulationWithBoundary D ℓ r) :
    sdpLength B ∈ sourceSinkPathLengths B := by
  exact Finset.min'_mem _ _

/-- Every simple directed source-to-sink path has length at most `ldpLength`. -/
theorem le_ldpLength (B : BipolarTriangulationWithBoundary D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : n ≤ ldpLength B := by
  have hm := (mem_sourceSinkPathLengths B n).2 ⟨P, trivial⟩
  exact (sourceSinkPathLengths B).le_max' n hm

/-- `sdpLength` is at most the length of every simple directed source-to-sink
path. -/
theorem sdpLength_le (B : BipolarTriangulationWithBoundary D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : sdpLength B ≤ n := by
  have hm := (mem_sourceSinkPathLengths B n).2 ⟨P, trivial⟩
  exact (sourceSinkPathLengths B).min'_le n hm

/-- A longest directed path exists because the attained path-length set is -/
theorem exists_isLDPGeodesic (B : BipolarTriangulationWithBoundary D ℓ r) :
    ∃ n : ℕ, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsLDPGeodesic B P := by
  have hm := ldpLength_mem B
  obtain ⟨P, _⟩ := (mem_sourceSinkPathLengths B (ldpLength B)).1 hm
  refine ⟨ldpLength B, P, ?_⟩
  intro m Q
  exact (sourceSinkPathLengths B).le_max' m
    ((mem_sourceSinkPathLengths B m).2 ⟨Q, trivial⟩)

/-- A shortest directed path exists because the attained path-length set is -/
theorem exists_isSDPGeodesic (B : BipolarTriangulationWithBoundary D ℓ r) :
    ∃ n : ℕ, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsSDPGeodesic B P := by
  have hm := sdpLength_mem B
  obtain ⟨P, _⟩ := (mem_sourceSinkPathLengths B (sdpLength B)).1 hm
  refine ⟨sdpLength B, P, ?_⟩
  intro m Q
  exact (sourceSinkPathLengths B).min'_le m
    ((mem_sourceSinkPathLengths B m).2 ⟨Q, trivial⟩)

/-- A path is an LDP geodesic exactly when its length is `ldpLength`. -/
theorem isLDPGeodesic_iff_length_eq (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsLDPGeodesic B P ↔ n = ldpLength B := by
  constructor
  · intro h
    obtain ⟨m, Q, hQ⟩ := exists_isLDPGeodesic B
    have hmn : m ≤ n := h Q
    have hmax : n ≤ ldpLength B := le_ldpLength B P
    have hLength : m = ldpLength B := by
      have hmBound := le_ldpLength B Q
      obtain ⟨R, _⟩ :=
        (mem_sourceSinkPathLengths B (ldpLength B)).1 (ldpLength_mem B)
      exact Nat.le_antisymm hmBound (hQ R)
    omega
  · intro hn
    subst n
    intro m Q
    exact le_ldpLength B Q

/-- A path is an SDP geodesic exactly when its length is `sdpLength`. -/
theorem isSDPGeodesic_iff_length_eq (B : BipolarTriangulationWithBoundary D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsSDPGeodesic B P ↔ n = sdpLength B := by
  constructor
  · intro h
    obtain ⟨m, Q, hQ⟩ := exists_isSDPGeodesic B
    have hnm : n ≤ m := h Q
    have hmin : sdpLength B ≤ n := sdpLength_le B P
    have hLength : m = sdpLength B := by
      have hmBound := sdpLength_le B Q
      obtain ⟨R, _⟩ :=
        (mem_sourceSinkPathLengths B (sdpLength B)).1 (sdpLength_mem B)
      exact Nat.le_antisymm (hQ R) hmBound
    omega
  · intro hn
    subst n
    intro m Q
    exact sdpLength_le B Q

/-- The left half-domain from `lem-lr-ind`: its right boundary has length `s`
and is the unique XDP geodesic. Uniqueness is expressed by equality of dart -/
@[expose] def InHalfL {x : XDP} (s : ℕ)
    (B : BipolarTriangulationWithBoundary D ℓ r) : Prop :=
  r = s ∧ IsXDPGeodesic B x B.rightPath ∧
    ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
      IsXDPGeodesic B x Q → Q.darts = B.rightPath.darts

/-- The right half-domain from `lem-lr-ind`: its left boundary is an XDP
proof at line 354 writes `M^R_{ℓ,s}`, where `M^R_{s,r}` is intended; line 357
describes a “leftmost LDP” although the lemma covers both LDP and SDP. -/
@[expose] def InHalfR {x : XDP} (s : ℕ)
    (B : BipolarTriangulationWithBoundary D ℓ r) : Prop :=
  ℓ = s ∧ IsXDPGeodesic B x B.leftPath

/-- Boltzmann weight factorization from the edge-count identity in the proof
arithmetic helper; the cut/glue map bijection and its edge-count identity are
not proved here. -/
theorem boltzmannWeight_factor {E EL ER s : ℕ}
    (hE : E + s = EL + ER) :
    (3 : ℚ) ^ (-(E : ℤ)) =
      3 ^ s * 3 ^ (-(EL : ℤ)) * 3 ^ (-(ER : ℤ)) := by
  have hExp : -(E : ℤ) = (s : ℤ) + (-(EL : ℤ)) + (-(ER : ℤ)) := by omega
  rw [hExp, zpow_add₀ (by norm_num : (3 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (3 : ℚ) ≠ 0)]
  simp only [zpow_natCast]

end DirectedDistances.PlanarMap
