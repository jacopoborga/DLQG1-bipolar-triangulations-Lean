/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteAcyclicXDPDistance
public import DirectedDistances.PlanarMap.FiniteBipolarThreePathExtremal

/-! Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Ordinary geodesics retain the general finite acyclic map carrier. Only the
three-path leftmost clause uses finite bipolar maps, with arbitrary endpoints. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
The ordered present oriented dart identities of a quiver path. -/
def quiverPathDarts {M : DirectedMapWithMissing D} {x y : MapVertex M}
    (P : Quiver.Path x y) : List D :=
  match P with
  | .nil => []
  | .cons Q e => quiverPathDarts Q ++ [e.1.1]

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Forgetting quiver endpoints preserves the number of darts. -/
theorem quiverPathDarts_length {M : DirectedMapWithMissing D}
    {x y : MapVertex M} (P : Quiver.Path x y) :
    (quiverPathDarts P).length = P.length := by
  induction P with
  | nil => rfl
  | cons P e ih => simpa [quiverPathDarts] using ih

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
A present oriented arrow in an acyclic map has distinct endpoints and gives
a one-edge simple dart path, retaining its dart identity. -/
def simplePathOfArrow (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {x y : MapVertex M} (e : @Quiver.Hom (MapVertex M) (mapQuiver M) x y) :
    SimpleDirectedDartPath M x y 1 where
  darts := [e.1.1]
  vertices := [x, y]
  darts_length := rfl
  vertices_length := rfl
  vertices_nodup := by
    have hxy : x ≠ y := by
      intro he
      subst y
      exact hM x (.single ⟨e.1.1, e.1.2.1, e.1.2.2, e.2.1, e.2.2⟩)
    simp [hxy]
  start_vertex := rfl
  end_vertex := rfl
  edge_step := by
    intro i
    have hi' : i.val < 1 := i.isLt
    have hi : i = ⟨0, by simp⟩ := Fin.ext (by change i.val = 0; omega)
    subst i
    exact ⟨e.1.2.1, e.1.2.2, e.2.1.symm, e.2.2.symm⟩

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Every directed quiver path in an acyclic map is a simple directed dart path.
Simplicity is proved by acyclic concatenation, never assumed. -/
def simplePathOfQuiverPath (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {x y : MapVertex M} (P : Quiver.Path x y) :
    SimpleDirectedDartPath M x y P.length := by
  induction P with
  | nil => exact SimpleDirectedDartPath.nil M x
  | cons P e ih => exact ih.appendAcyclic M hM (simplePathOfArrow M hM e)

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
The acyclic conversion preserves the whole ordered dart list. -/
theorem simplePathOfQuiverPath_darts (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) {x y : MapVertex M} (P : Quiver.Path x y) :
    (simplePathOfQuiverPath M hM P).darts = quiverPathDarts P := by
  induction P with
  | nil => rfl
  | cons P e ih =>
    change (simplePathOfQuiverPath M hM P).darts ++ [e.1.1] =
      quiverPathDarts P ++ [e.1.1]
    rw [ih]

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
A simple dart path gives an ordinary map path of the same length. The last
dart is retained as the last arrow, including parallel-edge identity. -/
def mapPathOfSimplePath {M : DirectedMapWithMissing D} {x y : MapVertex M}
    {n : ℕ} (P : SimpleDirectedDartPath M x y n) : MapPath M x y n := by
  induction n generalizing y with
  | zero =>
    have hxy : x = y := P.start_vertex.symm.trans P.end_vertex
    subst y
    exact ⟨.nil, rfl⟩
  | succ n ih =>
    let i : Fin P.darts.length := ⟨n, by rw [P.darts_length]; omega⟩
    let j : Fin (n + 1 + 1) := ⟨n, by omega⟩
    let Q := ih (P.prefix j)
    let e : @Quiver.Hom (MapVertex M) (mapQuiver M)
        (P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩) y :=
      ⟨⟨P.darts.get i, (P.edge_step i).1, (P.edge_step i).2.1⟩,
        (P.edge_step i).2.2.1.symm,
        (P.edge_step i).2.2.2.symm.trans P.end_vertex⟩
    exact ⟨Q.path.cons e, by simp [Q.length_eq]⟩

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
The ordinary map-path conversion preserves the ordered dart list. -/
theorem mapPathOfSimplePath_darts {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n) :
    quiverPathDarts (mapPathOfSimplePath P).path = P.darts := by
  induction n generalizing y with
  | zero =>
    have hd : P.darts = [] := List.length_eq_zero_iff.mp P.darts_length
    rw [hd]
    exact List.length_eq_zero_iff.mp (by
      rw [quiverPathDarts_length, (mapPathOfSimplePath P).length_eq])
  | succ n ih =>
    change quiverPathDarts
        (mapPathOfSimplePath (P.prefix ⟨n, by omega⟩)).path ++
        [P.darts.get ⟨n, by rw [P.darts_length]; omega⟩] = P.darts
    rw [ih, SimpleDirectedDartPath.prefix_darts]
    have hsplit := List.take_append_drop n P.darts
    have hdrop : P.darts.drop n = [P.darts.get ⟨n, by rw [P.darts_length]; omega⟩] := by
      rw [List.drop_eq_getElem_cons (by rw [P.darts_length]; omega)]
      have hnil : P.darts.drop (n + 1) = [] :=
        List.drop_eq_nil_of_le (by rw [P.darts_length])
      simp only [List.get_eq_getElem, hnil]
    rw [hdrop] at hsplit
    exact hsplit

private theorem length_cast_darts {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n m : ℕ} (P : SimpleDirectedDartPath M x y n)
    (h : n = m) : (h ▸ P : SimpleDirectedDartPath M x y m).darts = P.darts := by
  cases h
  rfl

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Every ordinary map path in an acyclic map has a simple dart-path realization
of the same length; no simplicity assumption is needed. -/
def simplePathOfMapPath (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {x y : MapVertex M} {n : ℕ} (P : MapPath M x y n) :
    SimpleDirectedDartPath M x y n :=
  P.length_eq ▸ simplePathOfQuiverPath M hM P.path

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
The reverse conversion retains every dart identity in order. -/
theorem simplePathOfMapPath_darts (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) {x y : MapVertex M} {n : ℕ} (P : MapPath M x y n) :
    (simplePathOfMapPath M hM P).darts = quiverPathDarts P.path := by
  rw [simplePathOfMapPath, length_cast_darts, simplePathOfQuiverPath_darts]

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
At fixed endpoints, the ordered dart identities determine an ordinary path;
parallel edges are never collapsed to adjacency. -/
theorem quiverPathDarts_injective {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {P Q : Quiver.Path x y}
    (h : quiverPathDarts P = quiverPathDarts Q) : P = Q := by
  induction P with
  | nil =>
    have hz : Q.length = 0 := by
      rw [← quiverPathDarts_length Q, ← h]
      rfl
    exact (Q.eq_nil_of_length_zero hz).symm
  | @cons b c P e ih =>
    cases Q with
    | nil =>
      have hh := congrArg List.length h
      simp [quiverPathDarts] at hh
    | @cons b' _ Q f =>
      have hrev : e.1.1 :: (quiverPathDarts P).reverse =
          f.1.1 :: (quiverPathDarts Q).reverse := by
        simpa [quiverPathDarts] using congrArg List.reverse h
      have hd := (List.cons.inj hrev).1
      have hb : b = b' := e.2.1.symm.trans
        ((congrArg (dartTailVertex M) hd).trans f.2.1)
      subst b'
      have hef : e = f := Subtype.ext (Subtype.ext hd)
      subst f
      have hPQ : P = Q := ih (List.reverse_injective (List.cons.inj hrev).2)
      cases hPQ
      rfl

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Converting a simple dart path to an ordinary path and back gives the original
path, including its vertex and dart lists. -/
theorem simplePathOfMapPath_mapPathOfSimplePath
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n) :
    simplePathOfMapPath M hM (mapPathOfSimplePath P) = P := by
  apply SimpleDirectedDartPath.eq_of_darts_eq
  rw [simplePathOfMapPath_darts, mapPathOfSimplePath_darts]

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
The converse round trip also recovers the original ordinary map path. -/
theorem mapPathOfSimplePath_simplePathOfMapPath
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {x y : MapVertex M} {n : ℕ} (P : MapPath M x y n) :
    mapPathOfSimplePath (simplePathOfMapPath M hM P) = P := by
  have hp : (mapPathOfSimplePath (simplePathOfMapPath M hM P)).path = P.path := by
    apply quiverPathDarts_injective
    rw [mapPathOfSimplePath_darts, simplePathOfMapPath_darts]
  apply (mapPathEquivQuiverPath M x y n).injective
  exact Subtype.ext hp

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Simple directed dart paths and ordinary directed map paths are equivalent
on every acyclic map, with endpoints, length and ordered darts preserved. -/
def simplePathEquivMapPath (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    (x y : MapVertex M) (n : ℕ) :
    SimpleDirectedDartPath M x y n ≃ MapPath M x y n where
  toFun := mapPathOfSimplePath
  invFun := simplePathOfMapPath M hM
  left_inv := simplePathOfMapPath_mapPathOfSimplePath M hM
  right_inv := mapPathOfSimplePath_simplePathOfMapPath M hM

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Every directed map path in an acyclic map visits each vertex at most once,
including the initial and terminal vertices. -/
theorem mapPath_vertices_nodup (M : DirectedMapWithMissing D)
    (hM : M.IsAcyclic) {x y : MapVertex M} {n : ℕ} (P : MapPath M x y n) :
    P.path.vertices.Nodup :=
  DirectedDistances.vertices_nodup_of_acyclic (mapQuiver_acyclic M hM) P.path

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Extremality over simple dart paths equals the ordinary geodesic predicate,
because all map paths are simple on the acyclic domain. -/
theorem simple_extremal_iff_isXDPGeodesic
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic) (choice : XDP)
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n) :
    (match choice with
     | .ldp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath M x y m), m ≤ n
     | .sdp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath M x y m), n ≤ m) ↔
      GeneralEndpointGeodesic.IsXDPGeodesic M hM choice (mapPathOfSimplePath P) := by
  rw [GeneralEndpointGeodesic.isXDPGeodesic_iff_no_better_mapPath]
  cases choice <;> constructor
  · intro h m Q
    exact h (simplePathOfMapPath M hM Q)
  · intro h m Q
    exact h (mapPathOfSimplePath Q)
  · intro h m Q
    exact h (simplePathOfMapPath M hM Q)
  · intro h m Q
    exact h (mapPathOfSimplePath Q)

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
The simple-path extremality condition equals length equality with the ordinary
extended XDP distance, including the LDP bottom convention. -/
theorem simple_extremal_iff_extended_distance_eq
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic) (choice : XDP)
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n) :
    (match choice with
     | .ldp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath M x y m), m ≤ n
     | .sdp => ∀ {m : ℕ} (_Q : SimpleDirectedDartPath M x y m), n ≤ m) ↔
      (match choice with
       | .ldp => ((n : ℕ∞) : WithBot ℕ∞) = DirectedDistances.ldp x y
       | .sdp => (n : ℕ∞) = DirectedDistances.sdp x y) := by
  rw [simple_extremal_iff_isXDPGeodesic M hM choice P,
    def_3_13_finite_geodesic_iff_extended_distance_eq]
  rfl

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
A leftmost XDP geodesic is an ordinary XDP geodesic such that every ordinary
XDP geodesic with the same endpoints lies in its closed three-path submap.
The supplied three-path region includes all three paths and allows overlap
and degeneracy. This definition makes no lexicographic or tie-break choice. -/
def IsLeftmostXDPGeodesic (B : BipolarMapWithBoundaryBase D ℓ r)
    (choice : XDP) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) : Prop :=
  GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
      (mapPathOfSimplePath P) ∧
    ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map x y m),
      GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
        (mapPathOfSimplePath Q) →
      ∀ d ∈ Q.darts, d ∈ B.threePathFilledDarts P

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
A directed path between arbitrary endpoints in a finite bipolar map supplies
a leftmost geodesic, by the proved extremal three-path containment theorem. -/
theorem exists_isLeftmostXDPGeodesic
    (B : BipolarMapWithBoundaryBase D ℓ r) (choice : XDP)
    {x y : MapVertex B.map} (hr : Quiver.Reachable x y) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map x y n,
      IsLeftmostXDPGeodesic B choice P := by
  obtain ⟨R⟩ := hr
  obtain ⟨n, P, hP, hC⟩ := B.exists_extremal_connector_containing_all_three_path
    choice (simplePathOfQuiverPath B.map B.acyclic R)
  refine ⟨n, P, (simple_extremal_iff_isXDPGeodesic B.map B.acyclic choice P).mp hP, ?_⟩
  intro m Q hQ
  exact hC Q ((simple_extremal_iff_isXDPGeodesic B.map B.acyclic choice Q).mpr hQ)

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
Two leftmost geodesics between arbitrary endpoints have identical dart lists.
The proved geometric antisymmetry applies because the definition supplies
mutual containment of these ordinary geodesics. -/
theorem isLeftmostXDPGeodesic_darts_eq
    (B : BipolarMapWithBoundaryBase D ℓ r) (choice : XDP)
    {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m)
    (hP : IsLeftmostXDPGeodesic B choice P)
    (hQ : IsLeftmostXDPGeodesic B choice Q) : P.darts = Q.darts := by
  exact B.darts_eq_of_mutual_threePathFilledDarts P Q (hP.2 Q hQ.1) (hQ.2 P hP.1)

/-- Provider for Definition 3.13 (def-geodesic); not installed, not counted.
The ordinary length-distance clause holds on every finite acyclic map. The
leftmost three-path clause, existence for reachable arbitrary endpoints, and
uniqueness of dart lists hold on finite bipolar maps under the author ruling.
No geometric, simplicity, extremality or identification premise is added. -/
theorem def_leftmost_geodesic_provider (choice : XDP) :
    (∀ (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
      {x y : MapVertex M} {n : ℕ} (P : MapPath M x y n),
      GeneralEndpointGeodesic.IsXDPGeodesic M hM choice P ↔
        (match choice with
         | .ldp => ((n : ℕ∞) : WithBot ℕ∞) = DirectedDistances.ldp x y
         | .sdp => (n : ℕ∞) = DirectedDistances.sdp x y)) ∧
    (∀ (B : BipolarMapWithBoundaryBase D ℓ r)
      {x y : MapVertex B.map} {n : ℕ}
      (P : SimpleDirectedDartPath B.map x y n),
      IsLeftmostXDPGeodesic B choice P ↔
        GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
          (mapPathOfSimplePath P) ∧
        ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map x y m),
          GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
            (mapPathOfSimplePath Q) →
          ∀ d ∈ Q.darts, d ∈ B.threePathFilledDarts P) ∧
    (∀ (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map},
      Quiver.Reachable x y →
      ∃ n, ∃ P : SimpleDirectedDartPath B.map x y n,
        IsLeftmostXDPGeodesic B choice P) ∧
    (∀ (B : BipolarMapWithBoundaryBase D ℓ r)
      {x y : MapVertex B.map} {n m : ℕ}
      (P : SimpleDirectedDartPath B.map x y n)
      (Q : SimpleDirectedDartPath B.map x y m),
      IsLeftmostXDPGeodesic B choice P →
      IsLeftmostXDPGeodesic B choice Q → P.darts = Q.darts) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M hM x y n P
    exact def_3_13_finite_geodesic_iff_extended_distance_eq M hM choice P
  · intro B x y n P
    rfl
  · intro B x y hr
    exact exists_isLeftmostXDPGeodesic B choice hr
  · intro B x y n m P Q hP hQ
    exact isLeftmostXDPGeodesic_darts_eq B choice P Q hP hQ

end DirectedDistances.PaperProofs.SourceResults
