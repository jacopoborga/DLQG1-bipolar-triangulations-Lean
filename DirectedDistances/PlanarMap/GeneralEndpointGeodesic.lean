/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Extremal
public import DirectedDistances.PlanarMap.FiniteBipolarXDP

@[expose] public section
namespace DirectedDistances.PlanarMap

open Quiver

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
abbrev MapDart (M : DirectedMapWithMissing D) :=
  {d : D // ¬ M.missing d ∧ M.tail d}

/-- Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
instance mapQuiver (M : DirectedMapWithMissing D) : Quiver (MapVertex M) where
  Hom x y :=
    {d : MapDart M // dartTailVertex M d.1 = x ∧ dartHeadVertex M d.1 = y}

/-- Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
noncomputable instance mapVertexFintype (M : DirectedMapWithMissing D) :
    Fintype (MapVertex M) := Fintype.ofFinite _

/-- A directed map path is a quiver path whose arrows retain their present
oriented dart identities and whose length is fixed. Helper toward Definition
3.13 (def-geodesic, general finite acyclic planar maps); not a paper result. -/
structure MapPath (M : DirectedMapWithMissing D) (x y : MapVertex M) (n : ℕ) where
  /-- Helper toward Definition 3.13 (def-geodesic, general finite acyclic -/
  path : Path x y
  /-- Helper toward Definition 3.13 (def-geodesic, general finite acyclic -/
  length_eq : path.length = n

/-- The quiver path underlying a map path. Its arrows retain dart identity.
Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
def MapPath.toQuiverPath {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n : ℕ} (P : MapPath M x y n) : Path x y := P.path

/-- Map paths of fixed length correspond to quiver paths with that length.
Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
def mapPathEquivQuiverPath (M : DirectedMapWithMissing D)
    (x y : MapVertex M) (n : ℕ) :
    MapPath M x y n ≃ {p : Path x y // p.length = n} where
  toFun P := ⟨P.path, P.length_eq⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv P := by cases P; rfl
  right_inv p := by cases p; rfl

/-- A nonempty quiver path gives a nonempty chain of directed map steps.
Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
theorem mapPath_positive_to_transGen (M : DirectedMapWithMissing D)
    {x y : MapVertex M} (p : Path x y) (hp : 0 < p.length) :
    Relation.TransGen M.directedStep x y := by
  induction p with
  | nil => simp at hp
  | @cons b c p e ih =>
    have he : M.directedStep b c := by
      exact ⟨e.1.1, e.1.2.1, e.1.2.2, e.2.1, e.2.2⟩
    cases p with
    | nil => exact Relation.TransGen.single he
    | @cons a b p f =>
      exact Relation.TransGen.tail (ih (by simp)) he

/-- The dart quiver of an acyclic oriented map is acyclic. Helper toward
Definition 3.13 (def-geodesic, general finite acyclic planar maps); not a paper -/
theorem mapQuiver_acyclic (M : DirectedMapWithMissing D) (hM : M.IsAcyclic) :
    DirectedDistances.acyclic (MapVertex M) := by
  intro x p
  by_contra hp
  have hpos : 0 < p.length := Nat.pos_of_ne_zero hp
  exact hM x (mapPath_positive_to_transGen M p hpos)

namespace GeneralEndpointGeodesic

/-- An LDP or SDP map geodesic is a generic longest or shortest quiver path.
Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
def IsXDPGeodesic (M : DirectedMapWithMissing D)
    (_hM : M.IsAcyclic) (choice : XDP) {x y : MapVertex M} {n : ℕ}
    (P : MapPath M x y n) : Prop :=
  match choice with
  | .ldp => DirectedDistances.IsLongest P.path
  | .sdp => DirectedDistances.IsShortest P.path

/-- Geodesic extremality is equivalent to the absence of a better map path.
Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
theorem isXDPGeodesic_iff_no_better_mapPath (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) (choice : XDP) {x y : MapVertex M} {n : ℕ}
    (P : MapPath M x y n) :
    IsXDPGeodesic M hM choice P ↔
      (match choice with
      | .ldp => ∀ {m : ℕ} (_Q : MapPath M x y m), m ≤ n
      | .sdp => ∀ {m : ℕ} (_Q : MapPath M x y m), n ≤ m) := by
  cases choice with
  | ldp =>
    change DirectedDistances.IsLongest P.path ↔
      (∀ {m : ℕ} (_Q : MapPath M x y m), m ≤ n)
    constructor
    · intro h m Q
      have hq := h Q.path
      simpa [Q.length_eq, P.length_eq] using hq
    · intro h q
      let Q : MapPath M x y q.length := ⟨q, rfl⟩
      have hq := h Q
      simpa [P.length_eq] using hq
  | sdp =>
    change DirectedDistances.IsShortest P.path ↔
      (∀ {m : ℕ} (_Q : MapPath M x y m), n ≤ m)
    constructor
    · intro h m Q
      have hq := h Q.path
      simpa [Q.length_eq, P.length_eq] using hq
    · intro h q
      let Q : MapPath M x y q.length := ⟨q, rfl⟩
      have hq := h Q
      simpa [P.length_eq] using hq

/-- Geodesic length equals the corresponding generic directed distance.
Helper toward Definition 3.13 (def-geodesic, general finite acyclic planar -/
theorem isXDPGeodesic_iff_distance_eq (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) (choice : XDP) {x y : MapVertex M} {n : ℕ}
    (P : MapPath M x y n) :
    IsXDPGeodesic M hM choice P ↔
      (match choice with
      | .ldp => (n : WithBot ℕ) =
          DirectedDistances.finiteLdp (mapQuiver_acyclic M hM) x y
      | .sdp => (n : ℕ∞) = DirectedDistances.sdp x y) := by
  classical
  cases choice with
  | ldp =>
    simpa [IsXDPGeodesic, P.length_eq] using
      (DirectedDistances.isLongest_iff_length_eq_finiteLdp
        (mapQuiver_acyclic M hM) P.path)
  | sdp =>
    simpa [IsXDPGeodesic, P.length_eq] using
      (DirectedDistances.isShortest_iff_length_eq_sdp P.path)

/-- A reachable endpoint pair has an LDP and SDP map path. Helper toward
Definition 3.13 (def-geodesic, general finite acyclic planar maps); not a paper -/
theorem exists_isXDPGeodesic_mapPath (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) (choice : XDP) {x y : MapVertex M}
    (hr : Nonempty (Path x y)) :
    ∃ n, ∃ P : MapPath M x y n, IsXDPGeodesic M hM choice P := by
  classical
  cases choice with
  | ldp =>
    obtain ⟨p, hp⟩ := DirectedDistances.exists_isLongest
      (mapQuiver_acyclic M hM) hr
    exact ⟨p.length, ⟨p, rfl⟩, hp⟩
  | sdp =>
    obtain ⟨p, hp⟩ := DirectedDistances.exists_isShortest hr
    exact ⟨p.length, ⟨p, rfl⟩, hp⟩

/-- A reachable endpoint pair has both an LDP and an SDP map path. Helper
toward Definition 3.13 (def-geodesic, general finite acyclic planar maps); not -/
theorem exists_ldp_and_sdp_mapPath (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) {x y : MapVertex M} (hr : Nonempty (Path x y)) :
    (∃ n, ∃ P : MapPath M x y n, IsXDPGeodesic M hM .ldp P) ∧
      ∃ m, ∃ Q : MapPath M x y m, IsXDPGeodesic M hM .sdp Q := by
  obtain ⟨n, P, hP⟩ := exists_isXDPGeodesic_mapPath M hM .ldp hr
  obtain ⟨m, Q, hQ⟩ := exists_isXDPGeodesic_mapPath M hM .sdp hr
  exact ⟨⟨n, P, hP⟩, m, Q, hQ⟩

end GeneralEndpointGeodesic

end DirectedDistances.PlanarMap
