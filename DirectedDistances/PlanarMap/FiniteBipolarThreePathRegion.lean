/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarRightmostPaths
public import DirectedDistances.PlanarMap.PlanarFaceCycleSpace
import DirectedDistances.PlanarMap.PlanarPathCutNoStrictLeft

/-! # Local rotation sectors and global cut labels toward the three-path region

The canonical paths below are chosen only after their existence and dart-list
uniqueness have been proved in `FiniteBipolarRightmostPaths`.

The local right-sector lemmas rule out outgoing departures and incoming
entries in the corresponding forbidden rotation sectors. They retain dart
identities and apply without a triangular-face hypothesis. The outgoing and
incoming block intervals also include the all-outgoing source rotation and
all-incoming sink rotation, respectively.

`ThreePathFaceLabels` constructs the unique normalized mod-two face function
for any source-to-sink cut, proves the oriented path-dart signs, and splits
the exterior into its marked boundary arcs. Its labels are constant at each
off-path vertex and along off-path directed paths, with arbitrary face
degrees. An outgoing-selected suffix also confines reachable off-cut
vertices to the left label. These are proved cut properties, not premises
added to the intersection assertion.

The outgoing-selected and incoming-selected paths meet whenever their
endpoints admit a directed connector. The proof extends them to two cuts,
transports their side labels, and excludes mutually left entries at their
first common outgoing-selected corner. It includes arbitrary face degrees
and the source/sink cases. This file does not yet define the source's
three-path region; those remaining obligations are recorded at the end. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

namespace SimpleDirectedDartPath

/-- A path contains its start, including a zero-length path. Helper toward -/
theorem start_mem_vertices_three_path {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n) :
    x ∈ P.vertices := by
  exact List.mem_iff_get.mpr ⟨_, P.start_vertex⟩

/-- A path contains its endpoint, including a zero-length path. Helper toward -/
theorem end_mem_vertices_three_path {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n) :
    y ∈ P.vertices := by
  exact List.mem_iff_get.mpr ⟨_, P.end_vertex⟩

/-- A simple path with equal endpoints has no edges and only that vertex. -/
theorem self_path_lists {M : DirectedMapWithMissing D}
    {x : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x x n) :
    n = 0 ∧ P.darts = [] ∧ P.vertices = [x] := by
  have hi := P.vertices_nodup.get_inj_iff.mp
    (P.start_vertex.trans P.end_vertex.symm)
  have hn : n = 0 := (congrArg Fin.val hi).symm
  refine ⟨hn, List.eq_nil_iff_length_eq_zero.mpr (P.darts_length.trans hn), ?_⟩
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp (by rw [P.vertices_length, hn])
  have hx : v = x := by simpa only [hv, List.get_eq_getElem,
    List.getElem_cons_zero] using P.start_vertex
  exact hv.trans (congrArg List.singleton hx)

/-- The least common index, with absence of earlier meetings, whenever the
two given paths have a common vertex. This is a list fact, not the planar
meeting theorem. Helper toward Definition 3.13 -/
theorem exists_first_common_index {M : DirectedMapWithMissing D}
    {x y u v : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M x y n) (Q : SimpleDirectedDartPath M u v m)
    (h : ∃ z, z ∈ P.vertices ∧ z ∈ Q.vertices) :
    ∃ i : Fin P.vertices.length,
      P.vertices.get i ∈ Q.vertices ∧
        ∀ j : Fin P.vertices.length, j.val < i.val → P.vertices.get j ∉ Q.vertices := by
  classical
  have hex : ∃ k, ∃ hk : k < P.vertices.length,
      P.vertices.get ⟨k, hk⟩ ∈ Q.vertices := by
    obtain ⟨z, hz, hzQ⟩ := h
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
    exact ⟨i.val, i.isLt, hi ▸ hzQ⟩
  obtain ⟨hk, hmem⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hk⟩, hmem, ?_⟩
  intro j hj hmemj
  exact Nat.find_min hex hj ⟨j.isLt, hmemj⟩

/-- The first common index is unique; no arbitrary ordering of vertices is
used. This does not assert that the paths meet. Helper toward Definition -/
theorem exists_unique_first_common_index {M : DirectedMapWithMissing D}
    {x y u v : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M x y n) (Q : SimpleDirectedDartPath M u v m)
    (h : ∃ z, z ∈ P.vertices ∧ z ∈ Q.vertices) :
    ∃! i : Fin P.vertices.length,
      P.vertices.get i ∈ Q.vertices ∧
        ∀ j : Fin P.vertices.length, j.val < i.val → P.vertices.get j ∉ Q.vertices := by
  obtain ⟨i, hi, hfirst⟩ := P.exists_first_common_index Q h
  refine ⟨i, ⟨hi, hfirst⟩, ?_⟩
  intro j hj
  apply Fin.ext
  have hnotji : ¬ j.val < i.val := fun hlt => hfirst j hlt hj.1
  have hnotij : ¬ i.val < j.val := fun hlt => hj.2 i hlt hi
  omega

/-- A first meeting supplies indices on both paths, including meetings at
endpoints. Helper toward Definition 3.13
already proved intersection; it asserts no planar separation theorem. -/
theorem exists_first_common_indices {M : DirectedMapWithMissing D}
    {x y u v : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M x y n) (Q : SimpleDirectedDartPath M u v m)
    (h : ∃ z, z ∈ P.vertices ∧ z ∈ Q.vertices) :
    ∃ i : Fin P.vertices.length, ∃ j : Fin Q.vertices.length,
      P.vertices.get i = Q.vertices.get j ∧
        ∀ k : Fin P.vertices.length, k.val < i.val → P.vertices.get k ∉ Q.vertices := by
  obtain ⟨i, hi, hfirst⟩ := P.exists_first_common_index Q h
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
  exact ⟨i, j, hj.symm, hfirst⟩

/-- Increasing vertex indices give directed reachability along the path. -/
theorem reaches_between_indices_three_path {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n)
    (i j : Fin P.vertices.length) (hij : i.val ≤ j.val) :
    Relation.ReflTransGen M.directedStep (P.vertices.get i) (P.vertices.get j) := by
  generalize hj : j.val = k
  induction k generalizing j with
  | zero =>
      have he : i = j := Fin.ext (by omega)
      subst j
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      by_cases he : i.val = j.val
      · have he' : i = j := Fin.ext he
        subst j
        exact Relation.ReflTransGen.refl
      · have hk : k < P.darts.length := by
          have hlen := P.vertices_length
          have hdlen := P.darts_length
          have hjlt := j.isLt
          omega
        let prev : Fin P.vertices.length := ⟨k, by omega⟩
        have hp := ih prev (by dsimp [prev]; omega) rfl
        have hs := P.edge_step ⟨k, hk⟩
        apply hp.tail
        refine ⟨P.darts.get ⟨k, hk⟩, hs.1, hs.2.1, hs.2.2.1.symm, ?_⟩
        exact hs.2.2.2.symm.trans
          (congrArg P.vertices.get (Fin.ext (by change k + 1 = j.val; omega)))

/-- In an acyclic map, reachability between vertices of one simple path
cannot run backwards in its index order. Helper toward Definition 3.13 -/
theorem index_le_of_reaches_three_path {M : DirectedMapWithMissing D}
    (ha : M.IsAcyclic) {x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M x y n) (i j : Fin P.vertices.length)
    (h : Relation.ReflTransGen M.directedStep (P.vertices.get i) (P.vertices.get j)) :
    i.val ≤ j.val := by
  by_contra hn
  have hji := P.reaches_between_indices_three_path j i (by omega)
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with he | ht
  · have he' := P.vertices_nodup.get_inj_iff.mp he
    have heval := congrArg Fin.val he'
    omega
  · exact ha _ (ht.trans_right hji)

/-- Common vertices of two directed paths have the same order in an
acyclic map. Helper toward Definition 3.13 -/
theorem common_indices_le_iff_three_path {M : DirectedMapWithMissing D}
    (ha : M.IsAcyclic) {x y u v : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M x y n) (Q : SimpleDirectedDartPath M u v m)
    {i k : Fin P.vertices.length} {j l : Fin Q.vertices.length}
    (hij : P.vertices.get i = Q.vertices.get j)
    (hkl : P.vertices.get k = Q.vertices.get l) :
    i.val ≤ k.val ↔ j.val ≤ l.val := by
  constructor
  · intro hik
    apply Q.index_le_of_reaches_three_path ha
    rw [← hij, ← hkl]
    exact P.reaches_between_indices_three_path i k hik
  · intro hjl
    apply P.index_le_of_reaches_three_path ha
    rw [hij, hkl]
    exact Q.reaches_between_indices_three_path j l hjl

/-- Once two paths in an acyclic map meet, their first common vertex along
the first path is also their first common vertex along the second path.
The unique pair records both minimality clauses. Helper toward Definition
infrastructure, not the planar intersection assertion. -/
theorem exists_unique_first_common_pair_three_path {M : DirectedMapWithMissing D}
    (ha : M.IsAcyclic) {x y u v : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M x y n) (Q : SimpleDirectedDartPath M u v m)
    (h : ∃ z, z ∈ P.vertices ∧ z ∈ Q.vertices) :
    ∃! ij : Fin P.vertices.length × Fin Q.vertices.length,
      P.vertices.get ij.1 = Q.vertices.get ij.2 ∧
        (∀ k : Fin P.vertices.length, k.val < ij.1.val →
          P.vertices.get k ∉ Q.vertices) ∧
        (∀ l : Fin Q.vertices.length, l.val < ij.2.val →
          Q.vertices.get l ∉ P.vertices) := by
  obtain ⟨i, j, hij, hfirst⟩ := P.exists_first_common_indices Q h
  have hsecond : ∀ l : Fin Q.vertices.length, l.val < j.val →
      Q.vertices.get l ∉ P.vertices := by
    intro l hlj hl
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hl
    have hki : ¬ k.val < i.val := fun hlt =>
      hfirst k hlt (hk ▸ List.get_mem Q.vertices l)
    have hjl := (P.common_indices_le_iff_three_path ha Q hij hk).mp (by omega)
    omega
  refine ⟨(i, j), ⟨hij, hfirst, hsecond⟩, ?_⟩
  rintro ⟨k, l⟩ ⟨hkl, hkfirst, _⟩
  have hki : ¬ k.val < i.val := fun hlt =>
    hfirst k hlt (hkl ▸ List.get_mem Q.vertices l)
  have hik : ¬ i.val < k.val := fun hlt =>
    hkfirst i hlt (hij ▸ List.get_mem Q.vertices j)
  have hki' : k = i := Fin.ext (by omega)
  have hlj : l = j := Q.vertices_nodup.get_inj_iff.mp
    (hkl.symm.trans ((congrArg P.vertices.get hki').trans hij))
  exact Prod.ext hki' hlj

end SimpleDirectedDartPath

namespace ThreePathFaceLabels

private theorem edgeOrbit_sum (M : CombinatorialMap D) (d : D)
    (g : D → ZMod 2) [DecidableEq (CombinatorialMap.EdgeQuotient M)] :
    (∑ x : D, if edgeClass M x = edgeClass M d then g x else 0) =
      g d + g (M.edgeInv d) := by
  classical
  have hfilter :
      Finset.univ.filter (fun x : D => edgeClass M x = edgeClass M d) =
        {d, M.edgeInv d} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      have hrel : M.edgeInv.SameCycle d x := (Quotient.exact hx).symm
      rcases (CombinatorialMap.edgeInv_sameCycle_iff M d x).mp hrel with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · rfl
      · apply Quotient.sound
        exact ((CombinatorialMap.edgeInv_sameCycle_iff M d (M.edgeInv d)).mpr
          (Or.inr rfl)).symm
  have hne : d ≠ M.edgeInv d := Ne.symm (M.edgeInv_ne d)
  rw [← Finset.sum_filter, hfilter]
  simp [hne]

private theorem vertexBoundary_single_edge (M : CombinatorialMap D) (d : D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)] :
    vertexBoundary M (Pi.single (edgeClass M d) 1) =
      (fun v => if vertexClass M d = v then (1 : ZMod 2) else 0) +
        (fun v => if vertexClass M (M.edgeInv d) = v then 1 else 0) := by
  classical
  funext v
  unfold vertexBoundary
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  have hsum := edgeOrbit_sum M d
    (fun x => if vertexClass M x = v then (1 : ZMod 2) else 0)
  calc
    (∑ x : D, if vertexClass M x = v then
        if edgeClass M x = edgeClass M d then (1 : ZMod 2) else 0 else 0) =
      ∑ x : D, if edgeClass M x = edgeClass M d then
        if vertexClass M x = v then (1 : ZMod 2) else 0 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hv : vertexClass M x = v <;>
            by_cases he : edgeClass M x = edgeClass M d <;> simp [hv, he]
    _ = (if vertexClass M d = v then 1 else 0) +
        (if vertexClass M (M.edgeInv d) = v then 1 else 0) := hsum
    _ = (if vertexClass M d = v then (1 : ZMod 2) else 0) +
        (if vertexClass M (M.edgeInv d) = v then 1 else 0) := rfl

private noncomputable def dartPathChain (M : CombinatorialMap D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)] {k : ℕ}
    (edges : Fin k → D) : EdgeSpace M :=
  ∑ i : Fin k, Pi.single (edgeClass M (edges i)) 1

private theorem dartPathChain_succ (M : CombinatorialMap D) {k : ℕ}
    (edges : Fin (k + 1) → D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)] :
    dartPathChain M edges =
      Pi.single (edgeClass M (edges 0)) 1 +
        dartPathChain M (fun i => edges i.succ) := by
  classical
  simp [dartPathChain, Fin.sum_univ_succ]

private theorem indicator_eq_of_eq {α : Type*} [DecidableEq α]
    (a b x : α) (hab : a = b) :
    (if a = x then (1 : ZMod 2) else 0) =
      (if b = x then 1 else 0) := by
  cases hab
  rfl

private theorem vertexBoundary_dartPathChain (M : CombinatorialMap D)
    [DecidableEq (CombinatorialMap.EdgeQuotient M)]
    [DecidableEq (CombinatorialMap.VertexQuotient M)] {k : ℕ}
    (edges : Fin k → D) (vertices : Fin (k + 1) → CombinatorialMap.VertexQuotient M)
    (hstep : ∀ i : Fin k,
      vertexClass M (edges i) = vertices i.castSucc ∧
      vertexClass M (M.edgeInv (edges i)) = vertices i.succ) :
    vertexBoundary M (dartPathChain M edges) =
      (fun v => (if vertices 0 = v then (1 : ZMod 2) else 0) +
        (if vertices (Fin.last k) = v then 1 else 0)) := by
  induction k with
  | zero =>
      funext v
      simp [dartPathChain, CharTwo.add_self_eq_zero]
  | succ k ih =>
      let edges' : Fin k → D := fun i => edges i.succ
      let vertices' : Fin (k + 1) → CombinatorialMap.VertexQuotient M :=
        fun i => vertices i.succ
      have hstep' : ∀ i : Fin k,
          vertexClass M (edges' i) = vertices' i.castSucc ∧
          vertexClass M (M.edgeInv (edges' i)) = vertices' i.succ := by
        intro i
        simpa [edges', vertices'] using hstep i.succ
      have hrec := ih edges' vertices' hstep'
      rw [dartPathChain_succ, LinearMap.map_add, vertexBoundary_single_edge,
        hrec]
      funext v
      simp only [Pi.add_apply]
      have hfirst := hstep 0
      have hcast : Fin.castSucc (0 : Fin (k + 1)) = (0 : Fin (k + 2)) := by
        ext
        rfl
      have hmiddle :
          (if vertices' 0 = v then (1 : ZMod 2) else 0) +
            (if vertices' 0 = v then 1 else 0) = 0 := by
        exact CharTwo.add_self_eq_zero _
      have hstart : vertexClass M (edges 0) = vertices 0 := by
        calc
          vertexClass M (edges 0) = vertices (Fin.castSucc 0) := hfirst.1
          _ = vertices 0 := congrArg vertices hcast
      have hhead : vertexClass M (M.edgeInv (edges 0)) = vertices' 0 := by
        simpa [vertices'] using hfirst.2
      have hfinish : vertices' (Fin.last k) = vertices (Fin.last (k + 1)) := by
        dsimp [vertices']
      have hstartVal :
          (if vertexClass M (edges 0) = v then (1 : ZMod 2) else 0) =
            (if vertices 0 = v then 1 else 0) := by
        exact indicator_eq_of_eq _ _ _ hstart
      have hheadVal :
          (if vertexClass M (M.edgeInv (edges 0)) = v then (1 : ZMod 2) else 0) =
            (if vertices' 0 = v then 1 else 0) := by
        exact indicator_eq_of_eq _ _ _ hhead
      have hfinishVal :
          (if vertices' (Fin.last k) = v then (1 : ZMod 2) else 0) =
            (if vertices (Fin.last (k + 1)) = v then 1 else 0) := by
        exact indicator_eq_of_eq _ _ _ hfinish
      rw [hstartVal, hheadVal, hfinishVal]
      calc
        _ = (if vertices 0 = v then (1 : ZMod 2) else 0) +
            ((if vertices' 0 = v then 1 else 0) +
              (if vertices' 0 = v then 1 else 0)) +
            (if vertices (Fin.last (k + 1)) = v then 1 else 0) := by
              abel
        _ = (if vertices 0 = v then (1 : ZMod 2) else 0) +
            (if vertices (Fin.last (k + 1)) = v then 1 else 0) := by
              rw [hmiddle]
              simp

private def simplePathEdges {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k) :
    Fin k → D := fun i => P.darts.get ⟨i.val, by
      rw [P.darts_length]
      exact i.isLt⟩

private def simplePathVertices {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k) :
    Fin (k + 1) → MapVertex M := fun i => P.vertices.get ⟨i.val, by
      rw [P.vertices_length]
      omega⟩

private theorem simplePath_chain_step {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k)
    (i : Fin k) :
    vertexClass M.toCombinatorialMap (simplePathEdges P i) =
        simplePathVertices P i.castSucc ∧
      vertexClass M.toCombinatorialMap
          (M.toCombinatorialMap.edgeInv (simplePathEdges P i)) =
        simplePathVertices P i.succ := by
  have hi : i.val < P.darts.length := by
    simp [P.darts_length]
  have hstep := P.edge_step ⟨i.val, hi⟩
  constructor
  · calc
      vertexClass M.toCombinatorialMap (simplePathEdges P i) =
          dartTailVertex M (simplePathEdges P i) := rfl
      _ = P.vertices.get ⟨i.val, by
          have hk := P.darts_length
          rw [P.vertices_length]
          omega⟩ := hstep.2.2.1.symm
      _ = simplePathVertices P i.castSucc := by
        dsimp [simplePathVertices]
  · calc
      vertexClass M.toCombinatorialMap
          (M.toCombinatorialMap.edgeInv (simplePathEdges P i)) =
          dartHeadVertex M (simplePathEdges P i) := rfl
      _ = P.vertices.get ⟨i.val + 1, by
          have hk := P.darts_length
          rw [P.vertices_length]
          omega⟩ := hstep.2.2.2.symm
      _ = simplePathVertices P i.succ := by
        dsimp [simplePathVertices]

private theorem simplePath_vertexBoundary {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k)
    [DecidableEq (CombinatorialMap.EdgeQuotient M.toCombinatorialMap)]
    [DecidableEq (CombinatorialMap.VertexQuotient M.toCombinatorialMap)] :
    vertexBoundary M.toCombinatorialMap (dartPathChain M.toCombinatorialMap
      (simplePathEdges P)) =
      (fun v => (if s = v then (1 : ZMod 2) else 0) +
        (if t = v then 1 else 0)) := by
  classical
  have h := vertexBoundary_dartPathChain M.toCombinatorialMap
    (simplePathEdges P) (simplePathVertices P) (simplePath_chain_step P)
  have hstart : simplePathVertices P 0 = s := by
    simpa [simplePathVertices] using P.start_vertex
  have hfinish : simplePathVertices P (Fin.last k) = t := by
    simpa [simplePathVertices, P.vertices_length] using P.end_vertex
  funext v
  have hpoint := congrFun h v
  rw [indicator_eq_of_eq _ _ _ hstart, indicator_eq_of_eq _ _ _ hfinish] at hpoint
  exact hpoint

private theorem zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with hval | hval
  · left
    apply ZMod.val_injective 2
    simp [hval]
  · right
    apply ZMod.val_injective 2
    rw [hval, ZMod.val_one_eq_one_mod]


/-- The mod-two geometric-edge chain of a directed path. Parallel edges
retain their distinct edge orbits. Helper toward Definition 3.13 -/
@[expose] noncomputable def pathChain
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) : EdgeSpace M.toCombinatorialMap := by
  classical
  exact ∑ i : Fin k, Pi.single (edgeClass M.toCombinatorialMap
    (P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩)) 1

/-- The chain of a path has precisely its endpoint incidence boundary,
including zero-length paths. Helper toward Definition 3.13 -/
theorem vertexBoundary_pathChain
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    [DecidableEq (MapVertex M)]
    (P : SimpleDirectedDartPath M s t k) :
    vertexBoundary M.toCombinatorialMap (pathChain P) =
      (fun v => (if s = v then (1 : ZMod 2) else 0) +
        (if t = v then 1 else 0)) := by
  classical
  exact simplePath_vertexBoundary P

/-- Two directed paths with the same endpoints have a mod-two cycle as
their sum, without a face-degree restriction. Helper toward Definition 3.13 -/
theorem vertexBoundary_pathChain_add
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k j : ℕ}
    (P : SimpleDirectedDartPath M s t k)
    (Q : SimpleDirectedDartPath M s t j) :
    vertexBoundary M.toCombinatorialMap (pathChain P + pathChain Q) = 0 := by
  classical
  rw [map_add, vertexBoundary_pathChain, vertexBoundary_pathChain]
  funext v
  exact CharTwo.add_self_eq_zero
    ((if s = v then (1 : ZMod 2) else 0) + (if t = v then 1 else 0))

/-- A source-to-sink path in a finite bipolar map determines a unique
mod-two face function, with boundary equal to its chain plus the left
boundary chain and with exterior value zero. This is face-label
infrastructure, not the three-path region. No triangularity is assumed. -/
theorem exists_unique_normalized
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    ∃! S : FaceSpace B.map.toCombinatorialMap,
      faceBoundary B.map.toCombinatorialMap S =
          pathChain P + pathChain B.leftPath ∧
        S (faceClass B.map.toCombinatorialMap B.map.outer) = 0 := by
  classical
  let M := B.map.toCombinatorialMap
  let c := pathChain P + pathChain B.leftPath
  obtain ⟨T, hT⟩ := planar_cycle_eq_faceBoundary M B.planar c
    (vertexBoundary_pathChain_add P B.leftPath)
  let outer := faceClass M B.map.outer
  let S : FaceSpace M := if T outer = 0 then T else T + 1
  have hboundary : faceBoundary M S = c := by
    by_cases hz : T outer = 0
    · simpa only [S, ite_eq_left hz] using hT
    · simp only [S, ite_eq_right hz, map_add, faceBoundary_one, add_zero, hT]
  have houter : S outer = 0 := by
    by_cases hz : T outer = 0
    · simpa only [S, ite_eq_left hz] using hz
    · have ho : T outer = 1 := (zmodTwo_eq_zero_or_one (T outer)).resolve_left hz
      simp only [S, ite_eq_right hz, Pi.add_apply, Pi.one_apply, ho,
        CharTwo.add_self_eq_zero]
  refine ⟨S, ⟨hboundary, houter⟩, ?_⟩
  intro U hU
  rcases planar_faceBoundary_unique_up_to_complement M B.planar c U S hU.1 hboundary
      with heq | heq
  · exact heq
  · have he := congrFun heq outer
    rw [hU.2, Pi.add_apply, houter, Pi.one_apply, zero_add] at he
    exact (zero_ne_one he).elim

/-- The normalized face labels are chosen only after their existence and
uniqueness. Helper toward Definition 3.13
yet identify oriented sides of the cut at its marked outer corners. -/
@[expose] noncomputable def normalized
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    FaceSpace B.map.toCombinatorialMap :=
  Classical.choose (exists_unique_normalized B P)

/-- Complete characterization of the normalized face labels. Helper toward -/
theorem eq_normalized_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap) :
    S = normalized B P ↔
      faceBoundary B.map.toCombinatorialMap S =
          pathChain P + pathChain B.leftPath ∧
        S (faceClass B.map.toCombinatorialMap B.map.outer) = 0 := by
  have hs := Classical.choose_spec (exists_unique_normalized B P)
  constructor
  · intro he
    exact he ▸ hs.1
  · exact hs.2 S

private theorem outerSplit_leftPath_darts_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    d ∈ B.leftPath.darts ↔ d ∈ B.map.ulDarts := by
  rcases B.outerSplit with ⟨_, _, hleft, _, _, _⟩
  exact hleft d

private theorem outerSplit_rightPath_reverse_edgeInv_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    d ∈ B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv ↔
      d ∈ B.map.lrDarts := by
  rcases B.outerSplit with ⟨_, _, _, hright, _, _⟩
  exact hright d

private theorem outerSplit_isOuterCycle
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    IsOuterCycle B.map B.outerWord := by
  rcases B.outerSplit with ⟨hcycle, _, _, _, _, _⟩
  exact hcycle

private theorem outerSplit_outerWord_perm
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.outerWord.letters ~r
      (B.leftPath.darts ++ [] ++
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv) ++ []) := by
  rcases B.outerSplit with ⟨_, hperm, _, _, _, _⟩
  exact hperm

private def pathCutSeamDarts
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts}


private def pathCutLeftOuterArc
    (B : BipolarMapWithBoundaryBase D ℓ r) : Set D :=
  B.map.ulDarts


private def pathCutRightOuterArc
    (B : BipolarMapWithBoundaryBase D ℓ r) : Set D :=
  B.map.lrDarts

private theorem mem_pathCutLeftOuterArc_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    d ∈ pathCutLeftOuterArc B ↔ d ∈ B.leftPath.darts := by
  exact (outerSplit_leftPath_darts_iff B d).symm


private theorem mem_pathCutRightOuterArc_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    d ∈ pathCutRightOuterArc B ↔
      d ∈ B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv := by
  exact (outerSplit_rightPath_reverse_edgeInv_iff B d).symm


private theorem pathCut_outerArcs_disjoint
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    Disjoint (pathCutLeftOuterArc B) (pathCutRightOuterArc B) := by
  have hnodup :
      (B.leftPath.darts ++
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)).Nodup := by
    have h := (outerSplit_outerWord_perm B).perm.nodup_iff.mp B.outerWord.nodup
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using h
  have hdisj := List.disjoint_of_nodup_append hnodup
  refine Set.disjoint_left.mpr ?_
  intro d hleft hright
  apply hdisj
  · exact (outerSplit_leftPath_darts_iff B d).mpr hleft
  · exact (outerSplit_rightPath_reverse_edgeInv_iff B d).mpr hright


private theorem isOuter_iff_mem_outerArcs
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    B.map.IsOuter d ↔
      d ∈ pathCutLeftOuterArc B ∨ d ∈ pathCutRightOuterArc B := by
  rw [← mem_iff_isOuter B.map B.outerWord (outerSplit_isOuterCycle B)]
  rw [(outerSplit_outerWord_perm B).mem_iff]
  simp only [List.append_nil, List.mem_append, mem_pathCutLeftOuterArc_iff,
    mem_pathCutRightOuterArc_iff]

private theorem pathCutSeamDarts_edgeInv_iff
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    B.map.toCombinatorialMap.edgeInv d ∈ pathCutSeamDarts B P ↔
      d ∈ pathCutSeamDarts B P := by
  change (B.map.toCombinatorialMap.edgeInv d ∈ P.darts ∨
      B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.edgeInv d) ∈ P.darts) ↔
    (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts)
  rw [B.map.toCombinatorialMap.edgeInv_invol]
  exact or_comm
private theorem simplePath_edgeClass_injective {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {k : ℕ} (P : SimpleDirectedDartPath M s t k) :
    Function.Injective (fun i : Fin k =>
      edgeClass M.toCombinatorialMap (simplePathEdges P i)) := by
  intro i j hij
  let di := simplePathEdges P i
  let dj := simplePathEdges P j
  have hi : i.val < P.darts.length := by simp [P.darts_length]
  have hj : j.val < P.darts.length := by simp [P.darts_length]
  have hrel : M.toCombinatorialMap.edgeInv.SameCycle di dj := Quotient.exact hij
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap di dj).mp hrel with
    hsame | hinv
  · have hiStep := P.edge_step ⟨i.val, hi⟩
    have hjStep := P.edge_step ⟨j.val, hj⟩
    have hvertices :
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ := by
      calc
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
            dartTailVertex M di := hiStep.2.2.1
        _ = dartTailVertex M dj := by rw [hsame]
        _ = P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ :=
          hjStep.2.2.1.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hvertices
    exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val) hidx)
  · have hiStep := P.edge_step ⟨i.val, hi⟩
    have hjStep := P.edge_step ⟨j.val, hj⟩
    have hnotTail := (M.tail_iff di hiStep.1).mp hiStep.2.1
    have hjTail : M.tail dj := hjStep.2.1
    rw [hinv] at hjTail
    exact (hnotTail hjTail).elim

private theorem simplePath_tail_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ P.darts) :
    M.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact (P.edge_step i).2.1

private theorem pathChain_apply_eq_one_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ P.darts) :
    pathChain P (edgeClass M.toCombinatorialMap d) = 1 := by
  classical
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  let j : Fin k := ⟨i.val, by simpa [P.darts_length] using i.isLt⟩
  have hdj : simplePathEdges P j = d := by
    dsimp [simplePathEdges, j]
    simpa using hi
  unfold pathChain
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_apply]
    have hval : edgeClass M.toCombinatorialMap d =
        edgeClass M.toCombinatorialMap (P.darts[j.val]) := by
      simpa [simplePathEdges, List.get_eq_getElem] using
        (congrArg (edgeClass M.toCombinatorialMap) hdj).symm
    simp [hval]
  · intro q hq hqj
    simp only [Pi.single_apply]
    have hneq :
        edgeClass M.toCombinatorialMap (simplePathEdges P q) ≠
          edgeClass M.toCombinatorialMap d := by
      intro heq
      have hclass :
          edgeClass M.toCombinatorialMap (simplePathEdges P q) =
            edgeClass M.toCombinatorialMap (simplePathEdges P j) := by
        rw [heq, hdj]
      exact hqj (simplePath_edgeClass_injective P hclass)
    have hneq' : edgeClass M.toCombinatorialMap d ≠
        edgeClass M.toCombinatorialMap
          (P.darts.get ⟨q.val, by rw [P.darts_length]; exact q.isLt⟩) := by
      simpa [simplePathEdges, List.get_eq_getElem] using hneq.symm
    simpa [List.get_eq_getElem] using hneq'
  · simp


private theorem pathChain_apply_eq_zero_of_not_seam
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D)
    (hseam : d ∉ pathCutSeamDarts B P) :
    pathChain P (edgeClass B.map.toCombinatorialMap d) = 0 := by
  classical
  unfold pathChain
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  let e := P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩
  have he_mem : e ∈ P.darts := by
    dsimp [e]
    exact List.get_mem _ _
  have hneq : edgeClass B.map.toCombinatorialMap e ≠
      edgeClass B.map.toCombinatorialMap d := by
    intro heq
    have hrel : B.map.toCombinatorialMap.edgeInv.SameCycle d e :=
      (Quotient.exact heq).symm
    rcases (CombinatorialMap.edgeInv_sameCycle_iff
      B.map.toCombinatorialMap d e).mp hrel with hedge | hedge
    · have hmem : d ∈ P.darts := by
        rw [← hedge]
        exact he_mem
      change ¬ (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts) at hseam
      exact hseam (Or.inl hmem)
    · have hmem : B.map.toCombinatorialMap.edgeInv d ∈ P.darts := by
        rw [← hedge]
        exact he_mem
      change ¬ (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts) at hseam
      exact hseam (Or.inr hmem)
  have hneq' : edgeClass B.map.toCombinatorialMap d ≠
      edgeClass B.map.toCombinatorialMap
        (P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩) := hneq.symm
  simp only [Pi.single_apply]
  simpa [List.get_eq_getElem] using hneq'

private theorem pathCutLeftBoundaryChain_apply_eq_one
    (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ pathCutLeftOuterArc B) :
    pathChain B.leftPath (edgeClass B.map.toCombinatorialMap d) = 1 := by
  apply pathChain_apply_eq_one_of_mem B.leftPath
  exact (mem_pathCutLeftOuterArc_iff B d).mp hd

private theorem pathCutLeftBoundaryChain_apply_eq_zero_of_both_inner
    (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : ¬ B.map.IsOuter d)
    (hinv : ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d)) :
    pathChain B.leftPath (edgeClass B.map.toCombinatorialMap d) = 0 := by
  apply pathChain_apply_eq_zero_of_not_seam B B.leftPath d
  intro hseam
  change d ∈ B.leftPath.darts ∨
      B.map.toCombinatorialMap.edgeInv d ∈ B.leftPath.darts at hseam
  rcases hseam with hleft | hleft
  · have houter : B.map.IsOuter d :=
      (isOuter_iff_mem_outerArcs B d).2
        (.inl ((mem_pathCutLeftOuterArc_iff B d).mpr hleft))
    exact hd houter
  · have houter : B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d) :=
      (isOuter_iff_mem_outerArcs B (B.map.toCombinatorialMap.edgeInv d)).2
        (.inl ((mem_pathCutLeftOuterArc_iff B _).mpr hleft))
    exact hinv houter

private theorem pathCutFaceBoundary_coeff
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath) (d : D) :
    S (faceClass B.map.toCombinatorialMap d) +
        S (faceClass B.map.toCombinatorialMap
          (B.map.toCombinatorialMap.edgeInv d)) =
      pathChain P (edgeClass B.map.toCombinatorialMap d) +
        pathChain B.leftPath (edgeClass B.map.toCombinatorialMap d) := by
  have h := congrFun hS (edgeClass B.map.toCombinatorialMap d)
  simpa only [faceBoundary_apply, Pi.add_apply] using h


private noncomputable def pathCutSideFromFace
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (S : FaceSpace B.map.toCombinatorialMap) (d : D) : Bool := by
  classical
  exact if d ∈ pathCutLeftOuterArc B then true
    else if d ∈ pathCutRightOuterArc B then false
    else decide (S (faceClass B.map.toCombinatorialMap d) = 1)

private theorem pathCutSideFromFace_faceSucc_of_inner
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (S : FaceSpace B.map.toCombinatorialMap) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    pathCutSideFromFace B S (B.map.toCombinatorialMap.faceSucc d) =
      pathCutSideFromFace B S d := by
  classical
  let M := B.map.toCombinatorialMap
  let f := M.faceSucc
  have hnextInner : ¬ B.map.IsOuter (f d) := by
    intro hnext
    have houter : f.SameCycle B.map.outer d := by
      change f.SameCycle B.map.outer (f d) at hnext
      exact Equiv.Perm.sameCycle_apply_right.mp hnext
    exact hinner houter
  have hdLeft : d ∉ pathCutLeftOuterArc B := by
    intro hd
    exact hinner ((isOuter_iff_mem_outerArcs B d).2 (Or.inl hd))
  have hdRight : d ∉ pathCutRightOuterArc B := by
    intro hd
    exact hinner ((isOuter_iff_mem_outerArcs B d).2 (Or.inr hd))
  have hnextLeft : f d ∉ pathCutLeftOuterArc B := by
    intro hd
    exact hnextInner ((isOuter_iff_mem_outerArcs B (f d)).2 (Or.inl hd))
  have hnextRight : f d ∉ pathCutRightOuterArc B := by
    intro hd
    exact hnextInner ((isOuter_iff_mem_outerArcs B (f d)).2 (Or.inr hd))
  have hface : faceClass M (f d) = faceClass M d := by
    apply Quotient.sound
    exact (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
  have hnextLeft' : B.map.toCombinatorialMap.faceSucc d ∉
      pathCutLeftOuterArc B := by simpa [f, M] using hnextLeft
  have hnextRight' : B.map.toCombinatorialMap.faceSucc d ∉
      pathCutRightOuterArc B := by simpa [f, M] using hnextRight
  unfold pathCutSideFromFace
  rw [ite_eq_right hnextLeft', ite_eq_right hnextRight',
    ite_eq_right hdLeft, ite_eq_right hdRight]
  rw [hface]

private theorem pathCutSideFromFace_edgeInv_of_outer
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    (d : D) (hseam : d ∉ pathCutSeamDarts B P)
    (houter : B.map.IsOuter d) :
    pathCutSideFromFace B S (B.map.toCombinatorialMap.edgeInv d) =
      pathCutSideFromFace B S d := by
  classical
  let M := B.map.toCombinatorialMap
  let e := M.edgeInv d
  have hseamE : e ∉ pathCutSeamDarts B P := by
    intro h
    have h' : d ∈ pathCutSeamDarts B P := by
      have hiff := pathCutSeamDarts_edgeInv_iff B P e
      simpa [e, M, M.edgeInv_invol] using hiff.mpr h
    exact hseam h'
  have hPzero := pathChain_apply_eq_zero_of_not_seam B P d hseam
  have hcoeff := pathCutFaceBoundary_coeff B P S hS d
  have hsum : S (faceClass M d) + S (faceClass M e) =
      pathChain B.leftPath (edgeClass M d) := by
    simpa [hPzero, e] using hcoeff
  have hfaceD : faceClass M d = faceClass M B.map.outer := by
    apply Quotient.sound
    change M.faceSucc.SameCycle B.map.outer d at houter
    exact houter.symm
  rcases (isOuter_iff_mem_outerArcs B d).mp houter with hdLeft | hdRight
  · have hdLeftData : ¬ B.map.missing d ∧ B.map.tail d ∧ B.map.IsOuter d := hdLeft
    have hnotTailE : ¬ B.map.tail e :=
      (B.map.tail_iff d (B.noMissingDarts d)).mp hdLeftData.2.1
    by_cases heOuter : B.map.IsOuter e
    · have heArc := (isOuter_iff_mem_outerArcs B e).mp heOuter
      have heRight : e ∈ pathCutRightOuterArc B := by
        rcases heArc with heLeft | heRight
        · have heLeftData : ¬ B.map.missing e ∧ B.map.tail e ∧ B.map.IsOuter e := heLeft
          exact (hnotTailE heLeftData.2.1).elim
        · exact heRight
      have hleftOne := pathCutLeftBoundaryChain_apply_eq_one B hdLeft
      rw [hleftOne] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : faceClass M e = faceClass M B.map.outer := by
        apply Quotient.sound
        change M.faceSucc.SameCycle B.map.outer e at heOuter
        exact heOuter.symm
      rw [hfaceE, houterFace] at hsum
      simp at hsum
    · have hleftOne := pathCutLeftBoundaryChain_apply_eq_one B hdLeft
      rw [hleftOne] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : S (faceClass M e) = 1 := by simpa [e, M] using hsum
      have heLeft : e ∉ pathCutLeftOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inl he))
      have heRight : e ∉ pathCutRightOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inr he))
      simp [pathCutSideFromFace, heLeft, heRight, hdLeft, hfaceE, e, M]
  · have hdRightData : ¬ B.map.missing d ∧ ¬ B.map.tail d ∧ B.map.IsOuter d := hdRight
    have htailE : B.map.tail e := by
      by_contra hnot
      have htailD : B.map.tail d := (B.map.tail_iff d (B.noMissingDarts d)).mpr hnot
      exact hdRightData.2.1 htailD
    by_cases heOuter : B.map.IsOuter e
    · have heArc := (isOuter_iff_mem_outerArcs B e).mp heOuter
      have heLeft : e ∈ pathCutLeftOuterArc B := by
        rcases heArc with heLeft | heRight
        · exact heLeft
        · have heRightData :
              ¬ B.map.missing e ∧ ¬ B.map.tail e ∧ B.map.IsOuter e := heRight
          exact (heRightData.2.1 htailE).elim
      have hleftOneE := pathCutLeftBoundaryChain_apply_eq_one B heLeft
      have hleftOne :
          pathChain B.leftPath (edgeClass M d) = 1 := by
        have hclass : edgeClass M e = edgeClass M d := by
          apply Quotient.sound
          exact (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
        rw [← hclass]
        exact hleftOneE
      rw [hleftOne] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : faceClass M e = faceClass M B.map.outer := by
        apply Quotient.sound
        change M.faceSucc.SameCycle B.map.outer e at heOuter
        exact heOuter.symm
      rw [hfaceE, houterFace] at hsum
      simp at hsum
    · have hnotLeft : d ∉ pathCutLeftOuterArc B := by
        intro hleft
        exact (Set.disjoint_left.mp (pathCut_outerArcs_disjoint B)) hleft hdRight
      have hnotLeftSeam : d ∉ pathCutSeamDarts B B.leftPath := by
        intro h
        change d ∈ B.leftPath.darts ∨ M.edgeInv d ∈ B.leftPath.darts at h
        rcases h with h | h
        · exact hnotLeft ((mem_pathCutLeftOuterArc_iff B d).mpr h)
        · have heOuter' : B.map.IsOuter e :=
            (isOuter_iff_mem_outerArcs B e).2
              (.inl ((mem_pathCutLeftOuterArc_iff B e).mpr h))
          exact heOuter heOuter'
      have hleftZero :=
        pathChain_apply_eq_zero_of_not_seam B B.leftPath d hnotLeftSeam
      rw [hleftZero] at hsum
      rw [hfaceD, houterFace] at hsum
      have hfaceE : S (faceClass M e) = 0 := by simpa [e, M] using hsum
      have heLeft : e ∉ pathCutLeftOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inl he))
      have heRight : e ∉ pathCutRightOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inr he))
      simp [pathCutSideFromFace, hnotLeft, hdRight, heLeft, heRight,
        hfaceE, e, M]

private theorem pathCutSideFromFace_edgeInv_of_not_seam
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    (d : D) (hseam : d ∉ pathCutSeamDarts B P) :
    pathCutSideFromFace B S (B.map.toCombinatorialMap.edgeInv d) =
      pathCutSideFromFace B S d := by
  classical
  let M := B.map.toCombinatorialMap
  let e := M.edgeInv d
  have hseamE : e ∉ pathCutSeamDarts B P := by
    intro h
    have h' : d ∈ pathCutSeamDarts B P := by
      have hiff := pathCutSeamDarts_edgeInv_iff B P e
      simpa [e, M, M.edgeInv_invol] using hiff.mpr h
    exact hseam h'
  by_cases hdOuter : B.map.IsOuter d
  · exact pathCutSideFromFace_edgeInv_of_outer B P S hS houterFace d hseam hdOuter
  · by_cases heOuter : B.map.IsOuter e
    · have h := pathCutSideFromFace_edgeInv_of_outer B P S hS houterFace e hseamE heOuter
      simpa [e, M, M.edgeInv_invol] using h.symm
    · have hPzero := pathChain_apply_eq_zero_of_not_seam B P d hseam
      have hleftZero :=
        pathCutLeftBoundaryChain_apply_eq_zero_of_both_inner B hdOuter heOuter
      have hcoeff := pathCutFaceBoundary_coeff B P S hS d
      have hsum :
          S (faceClass M d) + S (faceClass M e) = 0 := by
        rw [hPzero, hleftZero] at hcoeff
        simpa using hcoeff
      have hfaceEq : S (faceClass M d) = S (faceClass M e) :=
        CharTwo.add_eq_zero.mp hsum
      have hdLeft : d ∉ pathCutLeftOuterArc B := by
        intro hd
        exact hdOuter ((isOuter_iff_mem_outerArcs B d).2 (.inl hd))
      have hdRight : d ∉ pathCutRightOuterArc B := by
        intro hd
        exact hdOuter ((isOuter_iff_mem_outerArcs B d).2 (.inr hd))
      have heLeft : e ∉ pathCutLeftOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inl he))
      have heRight : e ∉ pathCutRightOuterArc B := by
        intro he
        exact heOuter ((isOuter_iff_mem_outerArcs B e).2 (.inr he))
      simp [pathCutSideFromFace, hdLeft, hdRight, heLeft, heRight,
        hfaceEq, e, M]



/-- Dart side labels with the marked exterior split into its left and right
boundary arcs. Their existence follows from the unique normalized face
function, for arbitrary face degrees. Helper toward Definition 3.13
darts are a separate proof obligation. -/
@[expose] noncomputable def side
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : D → Bool := by
  classical
  exact fun d => if d ∈ B.map.ulDarts then true
    else if d ∈ B.map.lrDarts then false
    else decide (normalized B P (faceClass B.map.toCombinatorialMap d) = 1)

/-- The left exterior arc has label true, including shared boundary edges. -/
theorem side_left_outer
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ B.leftPath.darts) : side B P d = true := by
  have hl := (mem_pathCutLeftOuterArc_iff B d).mpr hd
  change pathCutSideFromFace B (normalized B P) d = true
  simp only [pathCutSideFromFace, ite_eq_left hl]

/-- The reversed right exterior arc has label false, also when the two
boundaries share geometric edges. Helper toward Definition 3.13 -/
theorem side_right_outer
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ B.rightPath.darts.reverse.map B.map.edgeInv) :
    side B P d = false := by
  have hr := (mem_pathCutRightOuterArc_iff B d).mpr hd
  have hl : d ∉ pathCutLeftOuterArc B :=
    fun h => Set.disjoint_left.mp (pathCut_outerArcs_disjoint B) h hr
  change pathCutSideFromFace B (normalized B P) d = false
  simp only [pathCutSideFromFace, ite_eq_right hl, ite_eq_left hr]

/-- Side labels are constant around each internal face, with no restriction
on its degree or bipolar boundary length. Helper toward Definition 3.13 -/
theorem side_faceSucc_of_inner
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D)
    (hd : ¬ B.map.IsOuter d) :
    side B P (B.map.toCombinatorialMap.faceSucc d) = side B P d :=
  pathCutSideFromFace_faceSucc_of_inner B (normalized B P) d hd

/-- Reversing an edge outside the cut path preserves its side label,
including edges incident to the marked exterior face. Helper toward
No intersection or additional geometric separation premise is assumed. -/
theorem side_edgeInv_of_not_seam
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D)
    (hd : d ∉ P.darts) (he : B.map.edgeInv d ∉ P.darts) :
    side B P (B.map.edgeInv d) = side B P d := by
  have hs := (eq_normalized_iff B P (normalized B P)).mp rfl
  exact pathCutSideFromFace_edgeInv_of_not_seam B P (normalized B P)
    hs.1 hs.2 d (fun h => h.elim hd he)

/-- Both endpoint vertices of a listed dart belong to its path. -/
private theorem endpoints_mem {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) {d : D} (hd : d ∈ P.darts) :
    dartTailVertex M d ∈ P.vertices ∧ dartHeadVertex M d ∈ P.vertices := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  have hstep := P.edge_step i
  exact ⟨hstep.2.2.1 ▸ List.get_mem _ _,
    hstep.2.2.2 ▸ List.get_mem _ _⟩

/-- If either endpoint of an edge is off the cut path, reversing its dart
preserves the side label. Helper toward Definition 3.13 -/
theorem side_edgeInv_of_endpoint_not_mem
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D)
    (hd : dartTailVertex B.map d ∉ P.vertices ∨
      dartHeadVertex B.map d ∉ P.vertices) :
    side B P (B.map.edgeInv d) = side B P d := by
  apply side_edgeInv_of_not_seam B P d
  · intro hm
    exact hd.elim (fun h => h (endpoints_mem P hm).1)
      (fun h => h (endpoints_mem P hm).2)
  · intro hm
    have hv := endpoints_mem P hm
    simp only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] at hv
    exact hd.elim (fun h => h hv.2) (fun h => h hv.1)



private theorem bipolar_source_ne_sink (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.source ≠ B.sink := by
  intro he
  have hi := B.leftPath.vertices_nodup.get_inj_iff.mp
    (B.leftPath.start_vertex.trans (he.trans B.leftPath.end_vertex.symm))
  have hv := congrArg Fin.val hi
  dsimp at hv
  have hp := B.left_length_pos
  omega

private theorem rotInv_sameVertex (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.rot.symm d) = dartTailVertex B.map d := by
  apply Quotient.sound
  exact ⟨1, by simp⟩

private theorem rot_sameVertex (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.rot d) = dartTailVertex B.map d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl B.map.rot d).apply_left

private theorem vertexRotationCycle_successor_mem
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (d : {d : D // dartTailVertex B.map d = v}) :
    dartTailVertex B.map (B.map.rot.symm d.1) = v :=
  (rotInv_sameVertex B d.1).trans d.2
private def pathLastDart
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (hn : 0 < n) : D :=
  P.darts.get ⟨n - 1, by rw [P.darts_length]; omega⟩

private noncomputable def blockLeftIncoming
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) : D :=
  Classical.choose (B.incoming_block v hs ht)

private noncomputable def leftmostOutgoing
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) : D := by
  classical
  exact if hs : v = B.source then
    B.map.toCombinatorialMap.faceSucc
      (B.map.toCombinatorialMap.edgeInv
        (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)))
  else
    B.map.toCombinatorialMap.rot.symm
      (blockLeftIncoming B v (fun h => hs h) hvs)

private noncomputable def leftmostIncoming
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.source) : D := by
  classical
  exact if ht : v = B.sink then
    B.map.toCombinatorialMap.edgeInv
      (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos))
  else
    blockLeftIncoming B v hvs (fun h => ht h)

private theorem leftmostOutgoing_source_eq_firstLeftDart
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    leftmostOutgoing B B.source (bipolar_source_ne_sink B) =
      B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
  simpa [leftmostOutgoing] using B.outerFace_sourceCorner_eq_firstLeftDart

private theorem leftmostOutgoing_internal_characterization
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    dartTailVertex B.map (leftmostOutgoing B v ht) = v ∧
      B.map.tail (leftmostOutgoing B v ht) ∧
      ¬ B.map.tail (B.map.toCombinatorialMap.rot (leftmostOutgoing B v ht)) ∧
      ∀ q, dartTailVertex B.map q = v → B.map.tail q →
        ¬ B.map.tail (B.map.toCombinatorialMap.rot q) →
          q = leftmostOutgoing B v ht := by
  classical
  let hblock := B.incoming_block v hs ht
  rcases Classical.choose_spec (Classical.choose_spec hblock) with
    ⟨hliV, hliNot, hroV, hro, hliNext, hroNext,
      hstayIn, hstayOut, huniqueUp, huniqueDown⟩
  have hsel : leftmostOutgoing B v ht =
      B.map.toCombinatorialMap.rot.symm (Classical.choose hblock) := by
    simp [leftmostOutgoing, hs, blockLeftIncoming]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsel]
    exact (rotInv_sameVertex B (Classical.choose hblock)).trans hliV
  · rw [hsel]
    exact hliNext
  · rw [hsel]
    simpa using hliNot
  · intro q hqv hq hqprev
    have hprevV : dartTailVertex B.map (B.map.toCombinatorialMap.rot q) = v :=
      (rot_sameVertex B q).trans hqv
    have hprev := huniqueUp (B.map.toCombinatorialMap.rot q)
      hprevV hqprev (by simpa using hq)
    calc
      q = B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.rot q) := by simp
      _ = B.map.toCombinatorialMap.rot.symm (Classical.choose hblock) :=
        congrArg B.map.toCombinatorialMap.rot.symm hprev
      _ = leftmostOutgoing B v ht := hsel.symm

private theorem leftmostIncoming_internal_characterization
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    dartTailVertex B.map (leftmostIncoming B v hs) = v ∧
      ¬ B.map.tail (leftmostIncoming B v hs) ∧
      B.map.tail (B.map.toCombinatorialMap.rot.symm
        (leftmostIncoming B v hs)) ∧
      ∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
        B.map.tail (B.map.toCombinatorialMap.rot.symm q) →
          q = leftmostIncoming B v hs := by
  classical
  let hblock := B.incoming_block v hs ht
  rcases Classical.choose_spec (Classical.choose_spec hblock) with
    ⟨hliV, hliNot, hroV, hro, hliNext, hroNext,
      hstayIn, hstayOut, huniqueUp, huniqueDown⟩
  have hsel : leftmostIncoming B v hs = blockLeftIncoming B v hs ht := by
    simp [leftmostIncoming, ht, blockLeftIncoming]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsel]
    exact hliV
  · rw [hsel]
    exact hliNot
  · rw [hsel]
    exact hliNext
  · intro q hqv hq hqnext
    exact (huniqueUp q hqv hq hqnext).trans hsel.symm


private theorem leftmostIncoming_rot_symm_eq_leftmostOutgoing
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    B.map.rot.symm (leftmostIncoming B v hs) = leftmostOutgoing B v ht := by
  classical
  simp only [leftmostIncoming, leftmostOutgoing, dite_eq_right hs, dite_eq_right ht]
private theorem simplePath_dart_eq_first_of_tail_source
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) (hk : 0 < k) {d : D}
    (hd : d ∈ P.darts) (hsource : dartTailVertex M d = s) :
    d = P.darts.get ⟨0, by rw [P.darts_length]; exact hk⟩ := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hiLt : i.val < k := by simpa [P.darts_length] using i.isLt
  have hstep := P.edge_step i
  have hvertex : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ = s := by
    calc
      P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex M (P.darts.get i) := hstep.2.2.1
      _ = dartTailVertex M d := congrArg (dartTailVertex M) hi
      _ = s := hsource
  have hi0 : i.val = 0 := by
    by_contra hne
    have hget :
        P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := by
      calc
        _ = s := hvertex
        _ = _ := P.start_vertex.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hget
    have hval : i.val = 0 := by simpa using congrArg Fin.val hidx
    exact hne hval
  have hifin : i = ⟨0, by rw [P.darts_length]; exact hk⟩ := Fin.ext hi0
  rw [hifin] at hi
  exact hi.symm

private theorem simplePath_dart_eq_of_endpoint_eq
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {a b : D}
    (ha : a ∈ P.darts) (hb : b ∈ P.darts)
    (h : dartTailVertex M a = dartTailVertex M b ∨
      dartHeadVertex M a = dartHeadVertex M b) : a = b := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hb
  have hi := P.edge_step i
  have hj := P.edge_step j
  have hij : i.val = j.val := by
    rcases h with h | h
    · have he := hi.2.2.1.trans (h.trans hj.2.2.1.symm)
      have he' := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp he)
      exact he'
    · have he := hi.2.2.2.trans (h.trans hj.2.2.2.symm)
      have he' := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp he)
      dsimp at he'
      omega
  exact congrArg P.darts.get (Fin.ext hij)

private theorem rotation_first_visit (p : Equiv.Perm D) (x y : D)
    (hcycle : p.SameCycle x y) :
    ∃ m : ℕ, p^[m] x = y ∧
      (∀ j < m, p^[j] x ≠ y) ∧
      (∀ j, 0 < j → j ≤ m → p^[j] x ≠ x) := by
  obtain ⟨k, _, hk⟩ := hcycle.exists_pow_eq'
  have hex : ∃ j : ℕ, p^[j] x = y :=
    ⟨k, by simpa [Equiv.Perm.iterate_eq_pow] using hk⟩
  let m := Nat.find hex
  have hm : p^[m] x = y := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j < m) : p^[j] x ≠ y := Nat.find_min hex hj
  refine ⟨m, hm, hmin, ?_⟩
  intro j hj hjm heq
  have hsplit : m - j + j = m := Nat.sub_add_cancel hjm
  have hperiod : p^[m] x = p^[m - j] x := by
    calc
      p^[m] x = p^[m - j + j] x := by rw [hsplit]
      _ = p^[m - j] (p^[j] x) := Function.iterate_add_apply p (m - j) j x
      _ = p^[m - j] x := by rw [heq]
  exact hmin (m - j) (by omega) (hperiod.symm.trans hm)

private theorem rotation_iterate_vertex
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (x : D) (j : ℕ) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot.symm^[j] x) =
      dartTailVertex B.map x := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact vertexRotationCycle_successor_mem B _ ⟨_, ih⟩


private theorem outgoing_from_left
    (B : BipolarMapWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (q : D) (hqv : dartTailVertex B.map q = v) (hq : B.map.tail q) :
    ∃ k : ℕ, B.map.rot.symm^[k] (leftmostOutgoing B v ht) = q ∧
      ∀ j ≤ k, B.map.tail (B.map.rot.symm^[j] (leftmostOutgoing B v ht)) := by
  let p : Equiv.Perm D := B.map.rot.symm
  let x := leftmostOutgoing B v ht
  have hx := leftmostOutgoing_internal_characterization B v hs ht
  have hc : p.SameCycle x q :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hx.1.trans hqv.symm))
  obtain ⟨k, hk, _, hreturn⟩ := rotation_first_visit p x q hc
  refine ⟨k, hk, ?_⟩
  intro j hj
  apply Nat.decreasingInduction (motive := fun j _ => B.map.tail (p^[j] x)) ?_ ?_ hj
  · intro i hi hiTail
    by_contra hn
    have hiv : dartTailVertex B.map (p^[i + 1] x) = v :=
      (rotation_iterate_vertex B x (i + 1)).trans hx.1
    have hprev : ¬ B.map.tail (B.map.rot (p^[i + 1] x)) := by
      simpa only [Function.iterate_succ_apply', p, Equiv.apply_symm_apply] using hn
    have he := hx.2.2.2 _ hiv hiTail hprev
    exact hreturn (i + 1) (by omega) hi he
  · exact hk.symm ▸ hq

private theorem source_rotation_segment
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D)
    (hd : dartTailVertex B.map d = B.source) :
    ∃ k : ℕ, B.map.rot.symm^[k]
        (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) = d ∧
      ∀ j ≤ k, B.map.tail (B.map.rot.symm^[j]
        (leftmostOutgoing B B.source (bipolar_source_ne_sink B))) := by
  let x := leftmostOutgoing B B.source (bipolar_source_ne_sink B)
  have hx : dartTailVertex B.map x = B.source := by
    dsimp only [x]
    rw [leftmostOutgoing_source_eq_firstLeftDart]
    exact (B.leftPath.edge_step
      ⟨0, by rw [B.leftPath.darts_length]; exact Nat.zero_lt_of_lt B.left_length_pos⟩).2.2.1.symm.trans
        B.leftPath.start_vertex
  have hc : Equiv.Perm.SameCycle B.map.rot.symm x d :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hx.trans hd.symm))
  obtain ⟨k, _, hk⟩ := hc.exists_pow_eq'
  refine ⟨k, by simpa only [Equiv.Perm.iterate_eq_pow] using hk, ?_⟩
  intro j _
  exact B.source_rotation_all_outgoing.1 _
    ((rotation_iterate_vertex B x j).trans hx)

private theorem pathCutFaceBoundary_rotSymm_eq_of_zero
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath) (d : D)
    (hzero : (pathChain P + pathChain B.leftPath)
      (edgeClass B.map.toCombinatorialMap d) = 0) :
    S (faceClass B.map.toCombinatorialMap
      (B.map.toCombinatorialMap.rot.symm d)) =
        S (faceClass B.map.toCombinatorialMap d) := by
  let M := B.map.toCombinatorialMap
  have hcoeff := pathCutFaceBoundary_coeff B P S hS d
  have hsum : S (faceClass M d) + S (faceClass M (M.edgeInv d)) = 0 := by
    exact hcoeff.trans hzero
  have heq : S (faceClass M d) = S (faceClass M (M.edgeInv d)) :=
    CharTwo.add_eq_zero.mp hsum
  have hclass : faceClass M (M.rot.symm d) = faceClass M (M.edgeInv d) := by
    apply Quotient.sound
    change M.faceSucc.SameCycle (M.rot.symm d) (M.edgeInv d)
    have h : M.faceSucc.SameCycle (M.edgeInv d) (M.faceSucc (M.edgeInv d)) :=
      Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
    simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h.symm
  calc
    S (faceClass M (M.rot.symm d)) = S (faceClass M (M.edgeInv d)) :=
      congrArg S hclass
    _ = S (faceClass M d) := heq.symm

private theorem pathCut_firstDart_faceCoeff_eq_one
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hn : 0 < n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    (hinner : ¬ B.map.IsOuter
      (P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩)) :
    S (faceClass B.map.toCombinatorialMap
      (P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩)) = 1 := by
  classical
  let M := B.map.toCombinatorialMap
  let d := P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩
  change ¬ B.map.IsOuter d at hinner
  have hdMem : d ∈ P.darts := List.get_mem _ _
  have hdSource : dartTailVertex B.map d = B.source := by
    have hstep := P.edge_step ⟨0, by rw [P.darts_length]; exact hn⟩
    calc
      dartTailVertex B.map d = P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ :=
        hstep.2.2.1.symm
      _ = B.source := P.start_vertex
  let x := leftmostOutgoing B B.source (bipolar_source_ne_sink B)
  let p : Equiv.Perm D := M.rot.symm
  have hxEq : x = B.leftPath.darts.get
      ⟨0, by rw [B.leftPath.darts_length]; exact Nat.zero_lt_of_lt B.left_length_pos⟩ := by
    simpa [x, SimpleDirectedDartPath.firstDart, List.get_eq_getElem] using
      leftmostOutgoing_source_eq_firstLeftDart B
  have hxMem : x ∈ B.leftPath.darts := by
    rw [hxEq]
    exact List.get_mem _ _
  have hxStep := B.leftPath.edge_step
    ⟨0, by rw [B.leftPath.darts_length]; exact Nat.zero_lt_of_lt B.left_length_pos⟩
  have hxSource : dartTailVertex B.map x = B.source := by
    rw [hxEq]
    exact hxStep.2.2.1.symm.trans B.leftPath.start_vertex
  have hxTail : B.map.tail x := by rw [hxEq]; exact hxStep.2.1
  have hxLeft : x ∈ pathCutLeftOuterArc B :=
    (mem_pathCutLeftOuterArc_iff B x).2 hxMem
  have hxOuter : B.map.IsOuter x :=
    (isOuter_iff_mem_outerArcs B x).2 (.inl hxLeft)
  have hdx : d ≠ x := by
    intro h
    exact hinner (h.symm ▸ hxOuter)
  have hxFace : faceClass M x = faceClass M B.map.outer := by
    apply Quotient.sound
    change M.faceSucc.SameCycle x B.map.outer
    exact hxOuter.symm
  have hxNotP : x ∉ P.darts := by
    intro h
    have hfirst := simplePath_dart_eq_first_of_tail_source P hn h hxSource
    exact hdx hfirst.symm
  have hxInvNotP : M.edgeInv x ∉ P.darts := by
    have hnotTail := (B.map.tail_iff x (B.noMissingDarts x)).mp hxTail
    intro h
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    have hstep := P.edge_step i
    have hinvTail : B.map.tail (M.edgeInv x) := by
      rw [← hi]
      exact hstep.2.1
    exact hnotTail hinvTail
  have hxSeam : x ∉ pathCutSeamDarts B P := by
    intro h
    change x ∈ P.darts ∨ M.edgeInv x ∈ P.darts at h
    rcases h with h | h
    · exact hxNotP h
    · exact hxInvNotP h
  have hPzeroX := pathChain_apply_eq_zero_of_not_seam B P x hxSeam
  have hLoneX := pathCutLeftBoundaryChain_apply_eq_one B hxLeft
  have hC_one : (pathChain P + pathChain B.leftPath)
      (edgeClass M x) = 1 := by
    change pathChain P (edgeClass M x) +
      pathChain B.leftPath (edgeClass M x) = 1
    rw [hPzeroX, hLoneX]
    simp
  have hcoeffX := pathCutFaceBoundary_coeff B P S hS x
  have hsumX : S (faceClass M x) + S (faceClass M (M.edgeInv x)) = 1 :=
    hcoeffX.trans hC_one
  have hinvX : S (faceClass M (M.edgeInv x)) = 1 := by
    rw [hxFace, houterFace] at hsumX
    simpa using hsumX
  have hfaceRotX : faceClass M (M.rot.symm x) = faceClass M (M.edgeInv x) := by
    apply Quotient.sound
    change M.faceSucc.SameCycle (M.rot.symm x) (M.edgeInv x)
    have h : M.faceSucc.SameCycle (M.edgeInv x) (M.faceSucc (M.edgeInv x)) :=
      Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
    simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h.symm
  have hbase : S (faceClass M (p x)) = 1 := by
    calc
      S (faceClass M (p x)) = S (faceClass M (M.rot.symm x)) := rfl
      _ = S (faceClass M (M.edgeInv x)) := congrArg S hfaceRotX
      _ = 1 := hinvX
  obtain ⟨k, hget, hprefix⟩ := source_rotation_segment B d hdSource
  have hQ : ∃ j, p^[j] x = d := by
    refine ⟨k, ?_⟩
    simpa [p, x] using hget
  let m := Nat.find hQ
  have hm : p^[m] x = d := Nat.find_spec hQ
  have hmle : m ≤ k := Nat.find_min' hQ (by simpa [p, x] using hget)
  have hmpos : 0 < m := by
    by_contra hnotpos
    have hm0 : m = 0 := by omega
    have hxd : x = d := by simpa [hm0] using hm
    exact hinner (hxd ▸ hxOuter)
  have hmin (j : ℕ) (hj : j < m) : p^[j] x ≠ d := Nat.find_min hQ hj
  have htailIter (j : ℕ) (hj : j ≤ m) : B.map.tail (p^[j] x) := by
    have hjk : j ≤ k := le_trans hj hmle
    simpa [p, x] using hprefix j hjk
  have hsourceIter : ∀ j : ℕ,
      dartTailVertex B.map (p^[j] x) = B.source := by
    intro j
    induction j with
    | zero => simpa using hxSource
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact vertexRotationCycle_successor_mem B B.source ⟨p^[j] x, ih⟩
  have hneqStart (j : ℕ) (hj : 0 < j) (hjm : j < m) :
      p^[j] x ≠ x := by
    intro heq
    have hsplit : m - j + j = m := Nat.sub_add_cancel (Nat.le_of_lt hjm)
    have hperiod : p^[m] x = p^[m - j] x := by
      calc
        p^[m] x = p^[m - j + j] x :=
          congrArg (fun a : ℕ => p^[a] x) hsplit.symm
        _ = p^[m - j] (p^[j] x) := Function.iterate_add_apply p (m - j) j x
        _ = p^[m - j] x := congrArg (fun y : D => p^[m - j] y) heq
    have hsmaller : p^[m - j] x = d := hperiod.symm.trans hm
    exact hmin (m - j) (by omega) hsmaller
  have hseq : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
        intro hlow hup
        by_cases hj0 : j = 0
        · subst j
          simpa [Function.iterate_succ_apply'] using hbase
        · have hjlow : 1 ≤ j := by omega
          have hjup : j ≤ m := by omega
          have hprev := ih hjlow hjup
          have hjlt : j < m := by omega
          let q := p^[j] x
          have hqTail : B.map.tail q := by simpa [q] using htailIter j hjup
          have hqSource : dartTailVertex B.map q = B.source := by
            simpa [q] using hsourceIter j
          have hqNotP : q ∉ P.darts := by
            intro hq
            have hfirst := simplePath_dart_eq_first_of_tail_source P hn hq hqSource
            have hpred : p^[j] x = d := by simpa [q, d] using hfirst
            exact hmin j hjlt hpred
          have hqNotLeft : q ∉ B.leftPath.darts := by
            intro hq
            have hfirst := simplePath_dart_eq_first_of_tail_source B.leftPath
              (Nat.zero_lt_of_lt B.left_length_pos) hq hqSource
            have hqx : q = x := hfirst.trans hxEq.symm
            exact hneqStart j (by omega) hjlt hqx
          have hqNoInvTail := (B.map.tail_iff q (B.noMissingDarts q)).mp hqTail
          have hqInvNotP : M.edgeInv q ∉ P.darts := by
            intro hq
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
            have hstep := P.edge_step i
            have hinvTail : B.map.tail (M.edgeInv q) := by
              rw [← hi]
              exact hstep.2.1
            exact hqNoInvTail hinvTail
          have hqInvNotLeft : M.edgeInv q ∉ B.leftPath.darts := by
            intro hq
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
            have hstep := B.leftPath.edge_step i
            have hinvTail : B.map.tail (M.edgeInv q) := by
              rw [← hi]
              exact hstep.2.1
            exact hqNoInvTail hinvTail
          have hseamP : q ∉ pathCutSeamDarts B P := by
            intro h
            change q ∈ P.darts ∨ M.edgeInv q ∈ P.darts at h
            rcases h with h | h
            · exact hqNotP h
            · exact hqInvNotP h
          have hseamL : q ∉ pathCutSeamDarts B B.leftPath := by
            intro h
            change q ∈ B.leftPath.darts ∨ M.edgeInv q ∈ B.leftPath.darts at h
            rcases h with h | h
            · exact hqNotLeft h
            · exact hqInvNotLeft h
          have hPzero := pathChain_apply_eq_zero_of_not_seam B P q hseamP
          have hLzero := pathChain_apply_eq_zero_of_not_seam B B.leftPath q hseamL
          have hCzero : (pathChain P + pathChain B.leftPath)
              (edgeClass M q) = 0 := by
            change pathChain P (edgeClass M q) +
              pathChain B.leftPath (edgeClass M q) = 0
            rw [hPzero, hLzero]
            simp
          have htrans := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hCzero
          calc
            S (faceClass M (p^[j + 1] x)) = S (faceClass M (p (p^[j] x))) := by
              rw [show j + 1 = Nat.succ j by omega, Function.iterate_succ_apply']
            _ = S (faceClass M q) := by simpa [q, p] using htrans
            _ = 1 := hprev
  have hfinal := hseq m (by omega) le_rfl
  have hresult : S (faceClass M d) = 1 := by
    simpa [hm] using hfinal
  exact hresult


private theorem simplePath_endpoints_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ P.darts) :
    dartTailVertex M d ∈ P.vertices ∧ dartHeadVertex M d ∈ P.vertices := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  have hi := P.edge_step i
  constructor
  · rw [← hi.2.2.1]
    exact List.get_mem _ _
  · rw [← hi.2.2.2]
    exact List.get_mem _ _


private theorem pathCutLeftBoundaryChain_zero_at_vertex
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {v : MapVertex B.map} (hv : v ∉ B.leftPath.vertices)
    {q : D} (hq : dartTailVertex B.map q = v) :
    pathChain B.leftPath (edgeClass B.map.toCombinatorialMap q) = 0 := by
  apply pathChain_apply_eq_zero_of_not_seam B B.leftPath q
  rintro (h | h)
  · exact hv (hq ▸ (simplePath_endpoints_mem B.leftPath h).1)
  · have hmem := (simplePath_endpoints_mem B.leftPath h).2
    have heq : dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv q) = v := by
      simpa [dartHeadVertex, dartTailVertex,
        B.map.toCombinatorialMap.edgeInv_invol] using hq
    exact hv (heq ▸ hmem)


private theorem pathChain_zero_of_outgoing_ne
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {k : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink k)
    {b q : D} (hb : b ∈ P.darts) (hq : B.map.tail q)
    (hv : dartTailVertex B.map q = dartTailVertex B.map b) (hne : q ≠ b) :
    pathChain P (edgeClass B.map.toCombinatorialMap q) = 0 := by
  apply pathChain_apply_eq_zero_of_not_seam B P q
  rintro (h | h)
  · exact hne (simplePath_dart_eq_of_endpoint_eq P h hb (.inl hv))
  · exact ((B.map.tail_iff q (B.noMissingDarts q)).mp hq)
      (simplePath_tail_of_mem P h)


private theorem pathCutFaceCoeff_outgoing_of_not_leftBoundary
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hv : v ∉ B.leftPath.vertices) {b : D} (hb : b ∈ P.darts)
    (hbv : dartTailVertex B.map b = v)
    (hbase : S (faceClass B.map.toCombinatorialMap
      (leftmostOutgoing B v ht)) = 1) :
    S (faceClass B.map.toCombinatorialMap b) = 1 := by
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let x := leftmostOutgoing B v ht
  have hxv := (leftmostOutgoing_internal_characterization B v hs ht).1
  have hout := outgoing_from_left B v hs ht
  obtain ⟨k, hk, hprefix⟩ := hout b hbv (simplePath_tail_of_mem P hb)
  have hcycle : p.SameCycle x b := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hbv.symm)
  obtain ⟨m, hm, hmin, _⟩ := rotation_first_visit p x b hcycle
  have hmk : m ≤ k := by
    by_contra h
    exact hmin k (by omega) hk
  have hseq : ∀ j, j ≤ m → S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro _; exact hbase
    | succ j ih =>
        intro hj
        have hjm : j < m := by omega
        let q := p^[j] x
        have hqv : dartTailVertex B.map q = v :=
          (rotation_iterate_vertex B x j).trans hxv
        have hqt : B.map.tail q := hprefix j (by omega)
        have hP := pathChain_zero_of_outgoing_ne B P hb hqt
          (hqv.trans hbv.symm) (hmin j hjm)
        have hL := pathCutLeftBoundaryChain_zero_at_vertex B hv hqv
        have hzero : (pathChain P + pathChain B.leftPath)
            (edgeClass M q) = 0 := by
          change pathChain P _ + pathChain B.leftPath _ = 0
          rw [hP, hL, zero_add]
        have hstep := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hzero
        rw [Function.iterate_succ_apply']
        exact hstep.trans (ih (by omega))
  simpa [hm] using hseq m le_rfl


private theorem pathCutFaceCoeff_leftmostOutgoing_of_incoming
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hv : v ∉ B.leftPath.vertices) {a : D} (ha : a ∈ P.darts)
    (hav : dartHeadVertex B.map a = v)
    (haS : S (faceClass B.map.toCombinatorialMap a) = 1) :
    S (faceClass B.map.toCombinatorialMap (leftmostOutgoing B v ht)) = 1 := by
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let x := M.edgeInv a
  let y := leftmostIncoming B v hs
  have hxv : dartTailVertex B.map x = v := hav
  have hxt : ¬ B.map.tail x :=
    (B.map.tail_iff a (B.noMissingDarts a)).mp (simplePath_tail_of_mem P ha)
  have hy := leftmostIncoming_internal_characterization B v hs ht
  have hcycle : p.SameCycle x y := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hy.1.symm)
  obtain ⟨m, hm, hmin, hreturn⟩ := rotation_first_visit p x y hcycle
  have hvertex (j : ℕ) : dartTailVertex B.map (p^[j] x) = v :=
    (rotation_iterate_vertex B x j).trans hxv
  have hincoming : ∀ j, j ≤ m → ¬ B.map.tail (p^[j] x) := by
    intro j
    induction j with
    | zero => intro _; exact hxt
    | succ j ih =>
        intro hj htail
        have hprev := ih (show j ≤ m by omega)
        have hnext : B.map.tail (p (p^[j] x)) := by
          simpa only [Function.iterate_succ_apply'] using htail
        exact hmin j (by omega) (hy.2.2.2 _ (hvertex j) hprev hnext)
  have hbase : S (faceClass M (p x)) = 1 := by
    have hclass : faceClass M (p x) = faceClass M a := by
      apply Quotient.sound
      have h : M.faceSucc.SameCycle (M.faceSucc a) a :=
        (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
      exact h
    exact (congrArg S hclass).trans haS
  have hseq : ∀ j, 1 ≤ j → j ≤ m + 1 →
      S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
        intro hlo hhi
        by_cases hj0 : j = 0
        · subst j
          simpa only [Nat.zero_add, Function.iterate_one] using hbase
        · let q := p^[j] x
          have hjm : j ≤ m := by omega
          have hqv : dartTailVertex B.map q = v := hvertex j
          have hqt : ¬ B.map.tail q := hincoming j hjm
          have hqne : q ≠ x := hreturn j (by omega) hjm
          have hP : pathChain P (edgeClass M q) = 0 := by
            apply pathChain_apply_eq_zero_of_not_seam B P q
            rintro (h | h)
            · exact hqt (simplePath_tail_of_mem P h)
            · have hhead : dartHeadVertex B.map (M.edgeInv q) =
                  dartHeadVertex B.map a := by
                change dartTailVertex B.map (M.edgeInv (M.edgeInv q)) =
                  dartHeadVertex B.map a
                rw [M.edgeInv_invol]
                exact hqv.trans hav.symm
              have heq := simplePath_dart_eq_of_endpoint_eq P h ha (.inr hhead)
              apply hqne
              change M.edgeInv q = a at heq
              have heq' := congrArg M.edgeInv heq
              rw [M.edgeInv_invol] at heq'
              exact heq'
          have hL := pathCutLeftBoundaryChain_zero_at_vertex B hv hqv
          have hzero : (pathChain P + pathChain B.leftPath)
              (edgeClass M q) = 0 := by
            change pathChain P _ + pathChain B.leftPath _ = 0
            rw [hP, hL, zero_add]
          have hstep := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hzero
          rw [Function.iterate_succ_apply']
          exact hstep.trans (ih (by omega) (by omega))
  have hfinal := hseq (m + 1) (by omega) le_rfl
  have hlast : p^[m + 1] x = leftmostOutgoing B v ht := by
    rw [Function.iterate_succ_apply', hm]
    exact leftmostIncoming_rot_symm_eq_leftmostOutgoing B v hs ht
  simpa only [hlast] using hfinal


private theorem simplePath_exists_outgoing_of_mem_vertex
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) {v : MapVertex M}
    (hv : v ∈ P.vertices) (ht : v ≠ t) :
    ∃ d ∈ P.darts, dartTailVertex M d = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hik : i.val ≤ k := by have := i.isLt; have := P.vertices_length; omega
  have hine : i.val ≠ k := by
    intro heq
    have hifin : i = ⟨k, by rw [P.vertices_length]; omega⟩ := Fin.ext heq
    rw [hifin, P.end_vertex] at hi
    exact ht hi.symm
  let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; omega⟩
  refine ⟨P.darts.get j, List.get_mem _ _, ?_⟩
  exact (P.edge_step j).2.2.1.symm.trans hi


private theorem pathCut_leftBoundary_faceSucc_get
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (i : ℕ) (hi : i + 1 < ℓ) :
    B.map.toCombinatorialMap.faceSucc
        (B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩) =
      B.leftPath.darts.get ⟨i + 1, by rw [B.leftPath.darts_length]; omega⟩ := by
  let xs := B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv
  have hnodup : xs.Nodup := by
    simpa [xs] using B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hlen : xs.length = ℓ + r := by
    simp [xs, B.leftPath.darts_length, B.rightPath.darts_length]
  let d := B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩
  have hdOuter : B.map.IsOuter d :=
    ((B.outerSplit.2.2.1 d).mp (List.get_mem _ _)).2.2
  have hdWord : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hdOuter
  have hface : B.map.toCombinatorialMap.faceSucc d = xs.formPerm d := by
    rw [B.outerSplit.1.2.2 d hdWord]
    simpa [xs] using congrArg (fun p : Equiv.Perm D => p d)
      (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)
  have hidx : d = xs[i]'(by rw [hlen]; omega) := by
    dsimp [d, xs]
    rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; omega)]
  have hform := List.formPerm_apply_getElem xs hnodup i (by rw [hlen]; omega)
  have hmod : (i + 1) % xs.length = i + 1 := Nat.mod_eq_of_lt (by rw [hlen]; omega)
  change B.map.toCombinatorialMap.faceSucc d = _
  rw [hface, hidx, hform]
  simp only [hmod]
  dsimp [xs]
  rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; exact hi)]


private theorem pathCut_leftBoundary_eq_leftmostOutgoing
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    {x : D} (hx : x ∈ B.leftPath.darts) (hxv : dartTailVertex B.map x = v) :
    x = leftmostOutgoing B v ht := by
  let M := B.map.toCombinatorialMap
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  have hil : i.val < ℓ := by simpa [B.leftPath.darts_length] using i.isLt
  have hipos : 0 < i.val := by
    by_contra h
    have hi0 : i.val = 0 := by omega
    have hstep := B.leftPath.edge_step i
    have hsource : dartTailVertex B.map x = B.source := by
      rw [← hi, ← hstep.2.2.1]
      simpa only [hi0] using B.leftPath.start_vertex
    exact hs (hxv.symm.trans hsource)
  let j : Fin B.leftPath.darts.length :=
    ⟨i.val - 1, by have := B.leftPath.darts_length; omega⟩
  let a := B.leftPath.darts.get j
  have hax : M.faceSucc a = x := by
    have h := pathCut_leftBoundary_faceSucc_get B (i.val - 1) (by omega)
    have hadd : i.val - 1 + 1 = i.val := by omega
    simpa only [hadd] using h.trans (by simpa only [hadd] using hi)
  have hrot : M.rot x = M.edgeInv a := by
    rw [← hax]
    change M.rot (M.rot.symm (M.edgeInv a)) = M.edgeInv a
    exact M.rot.apply_symm_apply _
  apply (leftmostOutgoing_internal_characterization B v hs ht).2.2.2 x hxv
    (simplePath_tail_of_mem B.leftPath hx)
  rw [hrot]
  exact (B.map.tail_iff a (B.noMissingDarts a)).mp
    (simplePath_tail_of_mem B.leftPath (List.get_mem _ j))


private theorem pathCutFaceCoeff_outgoing_of_leftBoundary
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (hv : v ∈ B.leftPath.vertices) {b : D} (hb : b ∈ P.darts)
    (hbv : dartTailVertex B.map b = v) (hbinner : ¬ B.map.IsOuter b) :
    S (faceClass B.map.toCombinatorialMap b) = 1 := by
  let M := B.map.toCombinatorialMap
  let p : Equiv.Perm D := M.rot.symm
  let x := leftmostOutgoing B v ht
  obtain ⟨z, hz, hzv⟩ := simplePath_exists_outgoing_of_mem_vertex B.leftPath hv ht
  have hzx : z = x := pathCut_leftBoundary_eq_leftmostOutgoing B hs ht hz hzv
  have hx : x ∈ B.leftPath.darts := hzx ▸ hz
  have hxv : dartTailVertex B.map x = v := hzx ▸ hzv
  have hxt : B.map.tail x := simplePath_tail_of_mem B.leftPath hx
  have hxOuter : B.map.IsOuter x := ((B.outerSplit.2.2.1 x).mp hx).2.2
  have hxb : x ≠ b := by intro h; exact hbinner (h ▸ hxOuter)
  have hPzero := pathChain_zero_of_outgoing_ne B P hb hxt
    (hxv.trans hbv.symm) hxb
  have hLone := pathChain_apply_eq_one_of_mem B.leftPath hx
  have hxFace : faceClass M x = faceClass M B.map.outer :=
    Quotient.sound hxOuter.symm
  have hcoeff := pathCutFaceBoundary_coeff B P S hS x
  rw [hPzero, hLone, hxFace, houterFace, zero_add, zero_add] at hcoeff
  have hbase : S (faceClass M (p x)) = 1 := by
    have hclass : faceClass M (p x) = faceClass M (M.edgeInv x) := by
      apply Quotient.sound
      change M.faceSucc.SameCycle (M.rot.symm x) (M.edgeInv x)
      have h : M.faceSucc.SameCycle (M.faceSucc (M.edgeInv x)) (M.edgeInv x) :=
        (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl).symm
      simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h
    exact (congrArg S hclass).trans hcoeff
  have hout := outgoing_from_left B v hs ht
  obtain ⟨k, hk, hprefix⟩ := hout b hbv (simplePath_tail_of_mem P hb)
  have hcycle : p.SameCycle x b := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hbv.symm)
  obtain ⟨m, hm, hmin, hreturn⟩ := rotation_first_visit p x b hcycle
  have hmk : m ≤ k := by by_contra h; exact hmin k (by omega) hk
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    exact hxb (by simpa [hm0] using hm)
  have hseq : ∀ j, 1 ≤ j → j ≤ m → S (faceClass M (p^[j] x)) = 1 := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
        intro hlo hhi
        by_cases hj0 : j = 0
        · subst j
          simpa only [Nat.zero_add, Function.iterate_one] using hbase
        · let q := p^[j] x
          have hqv : dartTailVertex B.map q = v :=
            (rotation_iterate_vertex B x j).trans hxv
          have hqt : B.map.tail q := hprefix j (by omega)
          have hP := pathChain_zero_of_outgoing_ne B P hb hqt
            (hqv.trans hbv.symm) (hmin j (by omega))
          have hL := pathChain_zero_of_outgoing_ne B B.leftPath hx hqt
            (hqv.trans hxv.symm) (hreturn j (by omega) (by omega))
          have hzero : (pathChain P + pathChain B.leftPath)
              (edgeClass M q) = 0 := by
            change pathChain P _ + pathChain B.leftPath _ = 0
            rw [hP, hL, zero_add]
          have hstep := pathCutFaceBoundary_rotSymm_eq_of_zero B P S hS q hzero
          rw [Function.iterate_succ_apply']
          exact hstep.trans (ih (by omega) (by omega))
  simpa [hm] using hseq m hmpos le_rfl


private theorem pathCut_pathDart_faceCoeff_eq_one
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    {d : D} (hd : d ∈ P.darts) (hinner : ¬ B.map.IsOuter d) :
    S (faceClass B.map.toCombinatorialMap d) = 1 := by
  have hAll : ∀ (i : ℕ) (hi : i < n),
      ¬ B.map.IsOuter (P.darts.get ⟨i, by rw [P.darts_length]; exact hi⟩) →
      S (faceClass B.map.toCombinatorialMap
        (P.darts.get ⟨i, by rw [P.darts_length]; exact hi⟩)) = 1 := by
    intro i
    induction i with
    | zero =>
        intro hi hin
        exact pathCut_firstDart_faceCoeff_eq_one B P hi S hS houterFace hin
    | succ j ih =>
        intro hi hin
        let ai : Fin P.darts.length := ⟨j, by rw [P.darts_length]; omega⟩
        let bi : Fin P.darts.length := ⟨j + 1, by rw [P.darts_length]; exact hi⟩
        let a := P.darts.get ai
        let b := P.darts.get bi
        let v := dartTailVertex B.map b
        have ha : a ∈ P.darts := List.get_mem _ _
        have hb : b ∈ P.darts := List.get_mem _ _
        have hbstep := P.edge_step bi
        have hastep := P.edge_step ai
        have hav : dartHeadVertex B.map a = v :=
          hastep.2.2.2.symm.trans hbstep.2.2.1
        have hs : v ≠ B.source := by
          intro heq
          have hget :
              P.vertices.get ⟨j + 1, by rw [P.vertices_length]; omega⟩ =
                P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ :=
            hbstep.2.2.1.trans (heq.trans P.start_vertex.symm)
          have hidx := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp hget)
          dsimp at hidx
          omega
        have ht : v ≠ B.sink := by
          intro heq
          apply B.isSink
          exact ⟨dartHeadVertex B.map b, b, B.noMissingDarts b,
            hbstep.2.1, heq, rfl⟩
        by_cases hv : v ∈ B.leftPath.vertices
        · exact pathCutFaceCoeff_outgoing_of_leftBoundary B P S hS houterFace
            hs ht hv hb rfl hin
        · have hainner : ¬ B.map.IsOuter a := by
            intro hao
            rcases (isOuter_iff_mem_outerArcs B a).mp hao with hal | har
            · have hamem := (mem_pathCutLeftOuterArc_iff B a).mp hal
              exact hv (hav ▸ (simplePath_endpoints_mem B.leftPath hamem).2)
            · have harnot : ¬ B.map.tail a := har.2.1
              exact harnot hastep.2.1
          have haS : S (faceClass B.map.toCombinatorialMap a) = 1 :=
            ih (by omega) hainner
          have hbase := pathCutFaceCoeff_leftmostOutgoing_of_incoming
            B P S hS hs ht hv ha hav haS
          exact pathCutFaceCoeff_outgoing_of_not_leftBoundary
            B P S hS hs ht hv hb rfl hbase
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hin : i.val < n := by simpa only [P.darts_length] using i.isLt
  have h := hAll i.val hin (by simpa only [hi] using hinner)
  simpa only [hi] using h


private theorem pathCut_pathDart_reverseFaceCoeff_eq_zero
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (S : FaceSpace B.map.toCombinatorialMap)
    (hS : faceBoundary B.map.toCombinatorialMap S =
      pathChain P + pathChain B.leftPath)
    (houterFace : S (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    {d : D} (hd : d ∈ P.darts) :
    S (faceClass B.map.toCombinatorialMap
      (B.map.toCombinatorialMap.edgeInv d)) = 0 := by
  let M := B.map.toCombinatorialMap
  have htail := simplePath_tail_of_mem P hd
  have hP := pathChain_apply_eq_one_of_mem P hd
  have hcoeff := pathCutFaceBoundary_coeff B P S hS d
  by_cases hout : B.map.IsOuter d
  · have hleft : d ∈ pathCutLeftOuterArc B := by
      rcases (isOuter_iff_mem_outerArcs B d).mp hout with h | h
      · exact h
      · exact (h.2.1 htail).elim
    have hL := pathCutLeftBoundaryChain_apply_eq_one B hleft
    have hclass : faceClass M d = faceClass M B.map.outer := Quotient.sound hout.symm
    rw [hP, hL, hclass, houterFace, zero_add, CharTwo.add_self_eq_zero] at hcoeff
    exact hcoeff
  · have hL : pathChain B.leftPath (edgeClass M d) = 0 := by
      apply pathChain_apply_eq_zero_of_not_seam B B.leftPath d
      rintro (h | h)
      · exact hout (((B.outerSplit.2.2.1 d).mp h).2.2)
      · exact ((B.map.tail_iff d (B.noMissingDarts d)).mp htail)
          (simplePath_tail_of_mem B.leftPath h)
    have hleft := pathCut_pathDart_faceCoeff_eq_one B P S hS houterFace hd hout
    rw [hP, hL, hleft, add_zero] at hcoeff
    exact add_left_cancel (hcoeff.trans (add_zero 1).symm)



/-- Each forward cut-path dart has left-side label true. This includes
boundary coincidences and uses the exterior corner normalization. -/
theorem side_path_dart
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) : side B P d = true := by
  classical
  have hs := (eq_normalized_iff B P (normalized B P)).mp rfl
  by_cases ho : B.map.IsOuter d
  · have hl : d ∈ pathCutLeftOuterArc B := by
      rcases (isOuter_iff_mem_outerArcs B d).mp ho with hl | hr
      · exact hl
      · exact (hr.2.1 (simplePath_tail_of_mem P hd)).elim
    exact side_left_outer B P ((mem_pathCutLeftOuterArc_iff B d).mp hl)
  · have hl : d ∉ pathCutLeftOuterArc B :=
      fun h => ho ((isOuter_iff_mem_outerArcs B d).mpr (.inl h))
    have hr : d ∉ pathCutRightOuterArc B :=
      fun h => ho ((isOuter_iff_mem_outerArcs B d).mpr (.inr h))
    have hf := pathCut_pathDart_faceCoeff_eq_one B P
      (normalized B P) hs.1 hs.2 hd ho
    change pathCutSideFromFace B (normalized B P) d = true
    simp only [pathCutSideFromFace, ite_eq_right hl, ite_eq_right hr, hf, decide_true]

/-- The reverse of each cut-path dart has right-side label false, including
edges shared with either exterior boundary. Helper toward Definition 3.13 -/
theorem side_reverse_path_dart
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ P.darts) : side B P (B.map.edgeInv d) = false := by
  classical
  have hs := (eq_normalized_iff B P (normalized B P)).mp rfl
  have hl : B.map.edgeInv d ∉ pathCutLeftOuterArc B :=
    fun h => ((B.map.tail_iff d (B.noMissingDarts d)).mp
      (simplePath_tail_of_mem P hd)) h.2.1
  have hf := pathCut_pathDart_reverseFaceCoeff_eq_zero B P
    (normalized B P) hs.1 hs.2 hd
  change pathCutSideFromFace B (normalized B P) (B.map.edgeInv d) = false
  by_cases hr : B.map.edgeInv d ∈ pathCutRightOuterArc B
  · simp only [pathCutSideFromFace, ite_eq_right hl, ite_eq_left hr]
  · simp only [pathCutSideFromFace, ite_eq_right hl, ite_eq_right hr,
      hf, zero_ne_one, decide_false]


private def pathCutLeftSeeds
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | d ∈ pathCutLeftOuterArc B ∨ d ∈ P.darts}


private def pathCutRightSeeds
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | d ∈ pathCutRightOuterArc B ∨
    ∃ p ∈ P.darts, d = B.map.toCombinatorialMap.edgeInv p}

private theorem corner_consecutiveDarts
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) :
    B.map.toCombinatorialMap.faceSucc d =
        B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.edgeInv d) ∧
      dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
        dartHeadVertex B.map d ∧
      dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d) =
        dartHeadVertex B.map d := by
  constructor
  · simp [CombinatorialMap.faceSucc]
  · constructor
    · simp [dartTailVertex, dartHeadVertex]
    · apply Quotient.sound
      change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.edgeInv d))
        (B.map.toCombinatorialMap.edgeInv d)
      exact ⟨1, by simp⟩

private def canonicalOuterBoundaryDarts
    (B : BipolarMapWithBoundaryBase D ℓ r) : List D :=
  B.leftPath.darts ++ B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv


private theorem canonicalOuterBoundaryDarts_nodup
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    (canonicalOuterBoundaryDarts B).Nodup := by
  simpa [canonicalOuterBoundaryDarts] using
    B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup


private theorem canonicalOuterBoundaryDarts_length
    (B : BipolarMapWithBoundaryBase D ℓ r) :
    (canonicalOuterBoundaryDarts B).length = ℓ + r := by
  simp [canonicalOuterBoundaryDarts, B.leftPath.darts_length,
    B.rightPath.darts_length]


private theorem canonicalOuterBoundaryDarts_mem_isOuter
    (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ canonicalOuterBoundaryDarts B) : B.map.IsOuter d := by
  have hword : d ∈ B.outerWord.letters :=
    (B.outerSplit.2.1.perm.mem_iff).mpr (by
      simpa [canonicalOuterBoundaryDarts] using hd)
  exact (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mp hword


private theorem canonicalOuterBoundaryDarts_faceSucc_eq_formPerm
    (B : BipolarMapWithBoundaryBase D ℓ r) {d : D}
    (hd : B.map.IsOuter d) :
    B.map.toCombinatorialMap.faceSucc d =
      (canonicalOuterBoundaryDarts B).formPerm d := by
  have hword : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hd
  calc
    B.map.toCombinatorialMap.faceSucc d = B.outerWord.letters.formPerm d :=
      B.outerSplit.1.2.2 d hword
    _ = (canonicalOuterBoundaryDarts B).formPerm d := by
      simpa [canonicalOuterBoundaryDarts] using congrArg (fun f : Equiv.Perm D => f d)
        (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)


private theorem outerFace_leftPath_successor
    (B : BipolarMapWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i + 1 < ℓ) :
    B.map.toCombinatorialMap.faceSucc
        (B.leftPath.darts[i]'(by rw [B.leftPath.darts_length]; omega)) =
      B.leftPath.darts[i + 1]'(by rw [B.leftPath.darts_length]; omega) := by
  have hlefti : i < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    omega
  have hleftNext : i + 1 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact hi
  have hxi : i < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    omega
  have hxnext : i + 1 < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    omega
  have hmod : (i + 1) % (ℓ + r) < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    exact Nat.mod_lt _ (by omega)
  have hxi_eq : (canonicalOuterBoundaryDarts B)[i]'hxi = B.leftPath.darts[i]'hlefti := by
    simpa [canonicalOuterBoundaryDarts] using
      (List.getElem_append_left hlefti :
        (B.leftPath.darts ++
          B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i] =
          B.leftPath.darts[i])
  have hxnext_eq : (canonicalOuterBoundaryDarts B)[i + 1]'hxnext =
      B.leftPath.darts[i + 1]'hleftNext := by
    simpa [canonicalOuterBoundaryDarts] using
      (List.getElem_append_left hleftNext :
        (B.leftPath.darts ++
          B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i + 1] =
          B.leftPath.darts[i + 1])
  have houter : B.map.IsOuter ((canonicalOuterBoundaryDarts B)[i]'hxi) :=
    canonicalOuterBoundaryDarts_mem_isOuter B (List.getElem_mem hxi)
  have hsucc : B.map.toCombinatorialMap.faceSucc ((canonicalOuterBoundaryDarts B)[i]'hxi) =
      (canonicalOuterBoundaryDarts B)[(i + 1) % (ℓ + r)]'hmod := by
    rw [canonicalOuterBoundaryDarts_faceSucc_eq_formPerm B houter]
    simpa only [canonicalOuterBoundaryDarts_length] using
      List.formPerm_apply_getElem (canonicalOuterBoundaryDarts B)
      (canonicalOuterBoundaryDarts_nodup B) i hxi
  have hsucc' : B.map.toCombinatorialMap.faceSucc
      ((canonicalOuterBoundaryDarts B)[i]'hxi) =
      (canonicalOuterBoundaryDarts B)[i + 1]'hxnext := by
    have hiLt : i + 1 < ℓ + r := by omega
    have hmodEq : (i + 1) % (ℓ + r) = i + 1 := Nat.mod_eq_of_lt hiLt
    simpa only [hmodEq] using hsucc
  rw [← hxi_eq, ← hxnext_eq]
  exact hsucc'


private theorem outerFace_rightPath_successor
    (B : BipolarMapWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i + 1 < r) :
    B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv
          (B.rightPath.darts[i + 1]'(by rw [B.rightPath.darts_length]; omega))) =
      B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i]'(by rw [B.rightPath.darts_length]; omega)) := by
  let k := r - 2 - i
  let p := ℓ + k
  have hrighti : i < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    omega
  have hrightNext : i + 1 < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    exact hi
  have hp : p < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    dsimp [p, k]
    omega
  have hpNext : p + 1 < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    dsimp [p, k]
    omega
  have hp' : p < (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length := by
    simpa [canonicalOuterBoundaryDarts] using hp
  have hpNext' : p + 1 < (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length := by
    simpa [canonicalOuterBoundaryDarts] using hpNext
  have hreverse : k < B.rightPath.darts.reverse.length := by
    simp [B.rightPath.darts_length, k]
    omega
  have hreverseNext : k + 1 < B.rightPath.darts.reverse.length := by
    simp [B.rightPath.darts_length, k]
    omega
  have hcurrent : (canonicalOuterBoundaryDarts B)[p]'hp =
      B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i + 1]'hrightNext) := by
    change (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[p]'hp' = _
    have hsplit : p - B.leftPath.darts.length = k := by
      rw [B.leftPath.darts_length]
      dsimp [p]
      omega
    have hrev := List.getElem_reverse (l := B.rightPath.darts) (i := k) hreverse
    have hindex : B.rightPath.darts.length - 1 - k = i + 1 := by
      rw [B.rightPath.darts_length]
      dsimp [k]
      omega
    have hrev' : B.rightPath.darts.reverse[k]'hreverse =
        B.rightPath.darts[i + 1]'hrightNext := by
      simpa only [hindex] using hrev
    have hmap : (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[k]'(by
        simpa using hreverse) =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts[i + 1]'hrightNext) := by
      rw [List.getElem_map]
      exact congrArg B.map.toCombinatorialMap.edgeInv hrev'
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; dsimp [p, k]; omega)]
    simpa only [hsplit] using hmap
  have hnext : (canonicalOuterBoundaryDarts B)[p + 1]'hpNext =
      B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i]'hrighti) := by
    change (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[p + 1]'hpNext' = _
    have hsplit : (p + 1) - B.leftPath.darts.length = k + 1 := by
      rw [B.leftPath.darts_length]
      dsimp [p]
      omega
    have hrev := List.getElem_reverse (l := B.rightPath.darts) (i := k + 1) hreverseNext
    have hindex : B.rightPath.darts.length - 1 - (k + 1) = i := by
      rw [B.rightPath.darts_length]
      dsimp [k]
      omega
    have hrev' : B.rightPath.darts.reverse[k + 1]'hreverseNext =
        B.rightPath.darts[i]'hrighti := by
      simpa only [hindex] using hrev
    have hmap : (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[k + 1]'(by
        simpa using hreverseNext) =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts[i]'hrighti) := by
      rw [List.getElem_map]
      exact congrArg B.map.toCombinatorialMap.edgeInv hrev'
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; dsimp [p, k]; omega)]
    simpa only [hsplit] using hmap
  have hmod : (p + 1) % (ℓ + r) < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    exact Nat.mod_lt _ (by omega)
  have houter : B.map.IsOuter ((canonicalOuterBoundaryDarts B)[p]'hp) :=
    canonicalOuterBoundaryDarts_mem_isOuter B (List.getElem_mem hp)
  have hsucc : B.map.toCombinatorialMap.faceSucc
      ((canonicalOuterBoundaryDarts B)[p]'hp) =
      (canonicalOuterBoundaryDarts B)[(p + 1) % (ℓ + r)]'hmod := by
    rw [canonicalOuterBoundaryDarts_faceSucc_eq_formPerm B houter]
    simpa only [canonicalOuterBoundaryDarts_length] using
      List.formPerm_apply_getElem (canonicalOuterBoundaryDarts B)
        (canonicalOuterBoundaryDarts_nodup B) p hp
  have hmodEq : (p + 1) % (ℓ + r) = p + 1 :=
    Nat.mod_eq_of_lt (by rw [canonicalOuterBoundaryDarts_length] at hpNext; omega)
  have hsucc' : B.map.toCombinatorialMap.faceSucc
      ((canonicalOuterBoundaryDarts B)[p]'hp) =
      (canonicalOuterBoundaryDarts B)[p + 1]'hpNext := by
    simpa only [hmodEq] using hsucc
  rw [← hcurrent, ← hnext]
  exact hsucc'

private theorem pathCutSeamDarts_tailVertex_mem
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutSeamDarts B P) :
    dartTailVertex B.map d ∈ P.vertices := by
  change d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts at hd
  rcases hd with hd | hd
  · exact (endpoints_mem P hd).1
  · have hhead := (endpoints_mem P hd).2
    simpa [dartHeadVertex, dartTailVertex,
      B.map.toCombinatorialMap.edgeInv_invol] using hhead

private theorem pathCutSide_eq_rotSymm_of_inner_offSeam
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hface : ∀ d, ¬ B.map.IsOuter d →
      side (B.map.toCombinatorialMap.faceSucc d) = side d)
    (hedge : ∀ d, d ∉ pathCutSeamDarts B P →
      side (B.map.toCombinatorialMap.edgeInv d) = side d)
    (d : D)
    (hinner : ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d))
    (hseam : d ∉ pathCutSeamDarts B P) :
    side (B.map.toCombinatorialMap.rot.symm d) = side d := by
  calc
    side (B.map.toCombinatorialMap.rot.symm d) =
        side (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.edgeInv d)) := by
      rw [(corner_consecutiveDarts B (B.map.toCombinatorialMap.edgeInv d)).1]
      simp only [B.map.toCombinatorialMap.edgeInv_invol]
    _ = side (B.map.toCombinatorialMap.edgeInv d) := hface _ hinner
    _ = side d := hedge d hseam

private theorem pathCutOneSided_outerCorner_sameArc
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hleft : ∀ d, d ∈ pathCutLeftSeeds B P → side d = true)
    (hright : ∀ d, d ∈ pathCutRightSeeds B P → side d = false)
    {d : D} (hdOuter : B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d))
    (hdTail : dartTailVertex B.map d ∉ P.vertices) :
    side (B.map.toCombinatorialMap.faceSucc
      (B.map.toCombinatorialMap.edgeInv d)) =
      side (B.map.toCombinatorialMap.edgeInv d) := by
  let o := B.map.toCombinatorialMap.edgeInv d
  rcases (isOuter_iff_mem_outerArcs B o).mp hdOuter with hoLeft | hoRight
  · have hoPath : o ∈ B.leftPath.darts :=
      (mem_pathCutLeftOuterArc_iff B o).mp hoLeft
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hoPath
    have hiLt : i.val < ℓ := by simpa [B.leftPath.darts_length] using i.isLt
    by_cases hnext : i.val + 1 < ℓ
    · have hnextD : i.val + 1 < B.leftPath.darts.length := by
        simpa [B.leftPath.darts_length] using hnext
      have hget : B.leftPath.darts[i.val] = o := by
        simpa only [List.get_eq_getElem] using hi
      have hsucc : B.map.toCombinatorialMap.faceSucc o =
          B.leftPath.darts[i.val + 1]'hnextD := by
        rw [← hget]
        exact outerFace_leftPath_successor B i.val hnext
      have hnextLeft : B.leftPath.darts[i.val + 1]'hnextD ∈ pathCutLeftOuterArc B :=
        (mem_pathCutLeftOuterArc_iff B _).2 (List.getElem_mem _)
      calc
        side (B.map.toCombinatorialMap.faceSucc o) = true := by
          rw [hsucc]
          exact hleft _ (.inl hnextLeft)
        _ = side o := (hleft _ (.inl hoLeft)).symm
    · have hlast : i.val + 1 = ℓ := by omega
      have hstep := B.leftPath.edge_step i
      have hhead : dartHeadVertex B.map o = B.sink := by
        have hheadGet : dartHeadVertex B.map o = B.leftPath.vertices.get
            ⟨i.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ := by
          simpa only [hi] using hstep.2.2.2.symm
        calc
          dartHeadVertex B.map o = B.leftPath.vertices.get
              ⟨i.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ := hheadGet
          _ = B.leftPath.vertices.get
              ⟨ℓ, by rw [B.leftPath.vertices_length]; omega⟩ := by
            congr 1
            exact Fin.ext hlast
          _ = B.sink := B.leftPath.end_vertex
      have htailFace : dartTailVertex B.map
          (B.map.toCombinatorialMap.faceSucc o) = dartHeadVertex B.map o :=
        (corner_consecutiveDarts B o).2.2
      have htailD : dartTailVertex B.map d =
          dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc o) := by
        have h := (corner_consecutiveDarts B o).2.2
        simpa [o, dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol] using h.symm
      have htailEq : dartTailVertex B.map d = B.sink :=
        htailD.trans (htailFace.trans hhead)
      have hsinkP : B.sink ∈ P.vertices := by
        simpa only [P.end_vertex] using
          List.get_mem P.vertices ⟨n, by rw [P.vertices_length]; omega⟩
      have htailP : dartTailVertex B.map d ∈ P.vertices := by
        simpa only [htailEq] using hsinkP
      apply False.elim
      exact hdTail htailP
  · have hoPath : o ∈
        B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv :=
      (mem_pathCutRightOuterArc_iff B o).mp hoRight
    obtain ⟨p, hpRev, hpo⟩ := List.mem_map.mp hoPath
    have hp : p ∈ B.rightPath.darts := List.mem_reverse.mp hpRev
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    have hiLt : i.val < r := by simpa [B.rightPath.darts_length] using i.isLt
    have hget : B.rightPath.darts[i.val] = p := by
      simpa only [List.get_eq_getElem] using hi
    have hoEq : o = B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i.val]) := by
      calc
        o = B.map.toCombinatorialMap.edgeInv p := hpo.symm
        _ = B.map.toCombinatorialMap.edgeInv
            (B.rightPath.darts[i.val]) := congrArg _ hget.symm
    by_cases hi0 : i.val = 0
    · have htailP : dartTailVertex B.map p = B.source := by
        have htailGet : dartTailVertex B.map p = B.rightPath.vertices.get
            ⟨i.val, by rw [B.rightPath.vertices_length]; omega⟩ := by
          simpa only [hi] using (B.rightPath.edge_step i).2.2.1.symm
        calc
          dartTailVertex B.map p = B.rightPath.vertices.get
              ⟨i.val, by rw [B.rightPath.vertices_length]; omega⟩ := htailGet
          _ = B.rightPath.vertices.get
              ⟨0, by rw [B.rightPath.vertices_length]; omega⟩ := by
            congr 1
            exact Fin.ext hi0
          _ = B.source := B.rightPath.start_vertex
      have hhead : dartHeadVertex B.map o = B.source := by
        calc
          dartHeadVertex B.map o = dartTailVertex B.map p := by
            simp [hoEq, hget, dartHeadVertex, dartTailVertex,
              B.map.toCombinatorialMap.edgeInv_invol]
          _ = B.source := htailP
      have htailFace : dartTailVertex B.map
          (B.map.toCombinatorialMap.faceSucc o) = dartHeadVertex B.map o :=
        (corner_consecutiveDarts B o).2.2
      have htailD : dartTailVertex B.map d =
          dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc o) := by
        have h := (corner_consecutiveDarts B o).2.2
        simpa [o, dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol] using h.symm
      have htailEq : dartTailVertex B.map d = B.source :=
        htailD.trans (htailFace.trans hhead)
      have hsourceP : B.source ∈ P.vertices := by
        simpa only [P.start_vertex] using
          List.get_mem P.vertices ⟨0, by rw [P.vertices_length]; omega⟩
      have htailP : dartTailVertex B.map d ∈ P.vertices := by
        simpa only [htailEq] using hsourceP
      apply False.elim
      exact hdTail htailP
    · let j : Fin B.rightPath.darts.length := ⟨i.val - 1, by
        omega⟩
      have hgetPrev : B.rightPath.darts[i.val - 1] = B.rightPath.darts.get j := by
        simp [j, List.get_eq_getElem]
      have hsucc : B.map.toCombinatorialMap.faceSucc o =
          B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) := by
        calc
          B.map.toCombinatorialMap.faceSucc o =
              B.map.toCombinatorialMap.faceSucc
                (B.map.toCombinatorialMap.edgeInv
                  (B.rightPath.darts[i.val])) := by rw [hoEq]
          _ = B.map.toCombinatorialMap.edgeInv
              (B.rightPath.darts[i.val - 1]) := by
            have hpos : 1 ≤ i.val := by omega
            have hbound : i.val - 1 + 1 < r := by
              simpa [Nat.sub_add_cancel hpos] using hiLt
            have hs := outerFace_rightPath_successor B (i.val - 1) hbound
            simpa only [List.get_eq_getElem, Nat.sub_add_cancel hpos] using hs
          _ = B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) :=
            congrArg _ hgetPrev
      have hnextRight : B.map.toCombinatorialMap.faceSucc o ∈
          pathCutRightOuterArc B := by
        apply (mem_pathCutRightOuterArc_iff B _).2
        apply List.mem_map.mpr
        refine ⟨B.rightPath.darts.get j,
          List.mem_reverse.mpr (List.get_mem _ j), ?_⟩
        exact hsucc.symm
      calc
        side (B.map.toCombinatorialMap.faceSucc o) = false :=
          hright _ (.inl hnextRight)
        _ = side o := (hright _ (.inl hoRight)).symm

private theorem pathCutOneSided_side_eq_rotSymm
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hleft : ∀ d, d ∈ pathCutLeftSeeds B P → side d = true)
    (hright : ∀ d, d ∈ pathCutRightSeeds B P → side d = false)
    (hface : ∀ d, ¬ B.map.IsOuter d →
      side (B.map.toCombinatorialMap.faceSucc d) = side d)
    (hedge : ∀ d, d ∉ pathCutSeamDarts B P →
      side (B.map.toCombinatorialMap.edgeInv d) = side d)
    {d : D} (hdTail : dartTailVertex B.map d ∉ P.vertices) :
    side (B.map.toCombinatorialMap.rot.symm d) = side d := by
  have hdSeam : d ∉ pathCutSeamDarts B P := by
    intro h
    exact hdTail (pathCutSeamDarts_tailVertex_mem B P h)
  by_cases hinner : ¬ B.map.IsOuter
      (B.map.toCombinatorialMap.edgeInv d)
  · exact pathCutSide_eq_rotSymm_of_inner_offSeam
      B P side hface hedge d hinner hdSeam
  · have houter := pathCutOneSided_outerCorner_sameArc B P side hleft hright
      (Classical.not_not.mp hinner) hdTail
    calc
      side (B.map.toCombinatorialMap.rot.symm d) =
          side (B.map.toCombinatorialMap.faceSucc
            (B.map.toCombinatorialMap.edgeInv d)) := by
        rw [(corner_consecutiveDarts B
          (B.map.toCombinatorialMap.edgeInv d)).1]
        simp only [B.map.toCombinatorialMap.edgeInv_invol]
      _ = side (B.map.toCombinatorialMap.edgeInv d) := houter
      _ = side d := hedge d hdSeam

private theorem pathCutOneSided_side_eq_of_sameTail
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hleft : ∀ d, d ∈ pathCutLeftSeeds B P → side d = true)
    (hright : ∀ d, d ∈ pathCutRightSeeds B P → side d = false)
    (hface : ∀ d, ¬ B.map.IsOuter d →
      side (B.map.toCombinatorialMap.faceSucc d) = side d)
    (hedge : ∀ d, d ∉ pathCutSeamDarts B P →
      side (B.map.toCombinatorialMap.edgeInv d) = side d)
    {w : MapVertex B.map} {d e : D}
    (hdTail : dartTailVertex B.map d = w)
    (heTail : dartTailVertex B.map e = w)
    (hw : w ∉ P.vertices) : side d = side e := by
  let rot := B.map.toCombinatorialMap.rot
  have hlocal (x : D) (hx : dartTailVertex B.map x = w) :
      side (rot.symm x) = side x := by
    exact pathCutOneSided_side_eq_rotSymm B P side hleft hright hface hedge
      (by simpa [hx] using hw)
  have htailRot (x : D) : dartTailVertex B.map (rot x) =
      dartTailVertex B.map x := by
    apply Quotient.sound
    change rot.SameCycle (rot x) x
    exact Equiv.Perm.SameCycle.rfl.apply_left
  have hforward (x : D) (hx : dartTailVertex B.map x = w) :
      side (rot x) = side x := by
    have h := hlocal (rot x) (by simpa [htailRot x] using hx)
    change side (rot.symm (rot x)) = side (rot x) at h
    simpa [rot] using h.symm
  have hcycle : rot.SameCycle d e := by
    exact Quotient.exact (hdTail.trans heTail.symm)
  obtain ⟨k, _, hpow⟩ := hcycle.exists_pow_eq'
  have hiterEq : (rot : D → D)^[k] d = e := by
    simpa only [Equiv.Perm.iterate_eq_pow] using hpow
  have htailIter : ∀ k : ℕ,
      dartTailVertex B.map ((rot : D → D)^[k] d) = dartTailVertex B.map d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (htailRot _).trans ih
  have hiter : ∀ k : ℕ, side ((rot : D → D)^[k] d) = side d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (hforward _ ((htailIter k).trans hdTail)).trans ih
  calc
    side d = side ((rot : D → D)^[k] d) := (hiter k).symm
    _ = side e := congrArg side hiterEq



private theorem side_seed_properties
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    (∀ d, d ∈ pathCutLeftSeeds B P → side B P d = true) ∧
      (∀ d, d ∈ pathCutRightSeeds B P → side B P d = false) := by
  constructor
  · intro d hd
    rcases hd with hl | hp
    · exact side_left_outer B P ((mem_pathCutLeftOuterArc_iff B d).mp hl)
    · exact side_path_dart B P hp
  · intro d hd
    rcases hd with hr | ⟨p, hp, rfl⟩
    · exact side_right_outer B P ((mem_pathCutRightOuterArc_iff B d).mp hr)
    · exact side_reverse_path_dart B P hp

/-- At a vertex off the cut path, clockwise rotation preserves the side
label. The proof includes marked exterior corners and coincident boundary
paths. Helper toward Definition 3.13 -/
theorem side_rotSymm_of_not_mem
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : dartTailVertex B.map d ∉ P.vertices) :
    side B P (B.map.rot.symm d) = side B P d := by
  have hs := side_seed_properties B P
  apply pathCutOneSided_side_eq_rotSymm B P (side B P) hs.1 hs.2
    (side_faceSucc_of_inner B P) ?_ hd
  intro e he
  exact side_edgeInv_of_not_seam B P e
    (fun h => he (.inl h)) (fun h => he (.inr h))

/-- Every dart based at the same off-path vertex has the same side label.
This is global cut-side consistency without a triangularity assumption. -/
theorem side_eq_of_sameTail
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} {d e : D}
    (hd : dartTailVertex B.map d = v) (he : dartTailVertex B.map e = v)
    (hv : v ∉ P.vertices) : side B P d = side B P e := by
  have hs := side_seed_properties B P
  apply pathCutOneSided_side_eq_of_sameTail B P (side B P) hs.1 hs.2
    (side_faceSucc_of_inner B P) ?_ hd he hv
  intro a ha
  exact side_edgeInv_of_not_seam B P a
    (fun h => ha (.inl h)) (fun h => ha (.inr h))

/-- The side of an off-path vertex, independent of the representative dart
by `side_eq_of_sameTail`. The domain excludes the path, where both sides
are incident. Helper toward Definition 3.13 -/
@[expose] noncomputable def offPathSide
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (v : {v : MapVertex B.map // v ∉ P.vertices}) : Bool :=
  side B P (Quotient.out v.val)

/-- Complete dart characterization of the off-path vertex side. -/
theorem offPathSide_eq
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (v : {v : MapVertex B.map // v ∉ P.vertices}) (d : D)
    (hd : dartTailVertex B.map d = v.val) :
    offPathSide B P v = side B P d := by
  exact side_eq_of_sameTail B P (Quotient.out_eq v.val) hd v.property

/-- A directed edge with both endpoints off a source-to-sink cut cannot
change sides, including along the marked exterior boundary. -/
theorem offPathSide_eq_of_directedStep
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (u v : {v : MapVertex B.map // v ∉ P.vertices})
    (huv : B.map.directedStep u.val v.val) :
    offPathSide B P u = offPathSide B P v := by
  obtain ⟨d, _, _, hd, he⟩ := huv
  rw [offPathSide_eq B P u d hd,
    offPathSide_eq B P v (B.map.edgeInv d) he]
  exact (side_edgeInv_of_endpoint_not_mem B P d
    (Or.inl (fun h => u.property (hd ▸ h)))).symm

/-- Every directed path wholly off the cut remains on one side.
The reachability relation is on off-path vertices, so no side conclusion is
assumed as a premise. Helper toward Definition 3.13 -/
theorem offPathSide_eq_of_reaches
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {u v : {v : MapVertex B.map // v ∉ P.vertices}}
    (huv : Relation.ReflTransGen
      (fun a b : {v : MapVertex B.map // v ∉ P.vertices} =>
        B.map.directedStep a.val b.val) u v) :
    offPathSide B P u = offPathSide B P v := by
  induction huv with
  | refl => rfl
  | @tail v w _ hvw ih =>
      exact ih.trans (offPathSide_eq_of_directedStep B P v w hvw)


end ThreePathFaceLabels


/-- The open interval in a finite dart rotation, cut at its first visit to
the ending dart. Both endpoint darts are excluded; equal endpoints give the
empty interval. Choosing `rot` reads counter-clockwise, and choosing
`rot.symm` reads clockwise. Helper toward Definition 3.13
region of the planar map. -/
@[expose] def openRotationInterval_three_path
    (p : Equiv.Perm D) (a b : D) : Set D :=
  {d | ∃ k : ℕ, (p ^ k) a = b ∧
    (∀ j < k, (p ^ j) a ≠ b) ∧
    ∃ j : ℕ, 0 < j ∧ j < k ∧ (p ^ j) a = d}

namespace BipolarMapWithBoundaryBase

private theorem rotation_vertex_three_path (M : DirectedMapWithMissing D)
    (d : D) (j : ℕ) :
    dartTailVertex M ((M.rot ^ j) d) = dartTailVertex M d := by
  apply Quotient.sound
  exact (Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl M.rot d)).symm

private theorem clockwise_vertex_three_path (M : DirectedMapWithMissing D)
    (d : D) (j : ℕ) :
    dartTailVertex M ((M.rot.symm ^ j) d) = dartTailVertex M d := by
  apply Quotient.sound
  exact (Equiv.Perm.sameCycle_inv.mp
    (Equiv.Perm.sameCycle_pow_right.mpr
      (Equiv.Perm.SameCycle.refl M.rot.symm d))).symm

/-- Every outgoing dart at a vertex reaches the rightmost outgoing
dart clockwise through outgoing darts only, stopping at its first visit.
This gives the outgoing block's full interval, rather than just its endpoint
transition; the source's all-outgoing rotation is included.
Helper toward Definition 3.13 -/
theorem outgoing_clockwise_interval_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (ht : v ≠ B.sink)
    (d : D) (hv : dartTailVertex B.map d = v) (hd : B.map.tail d) :
    ∃ k : ℕ, (B.map.rot.symm ^ k) d = B.out v ht ∧
      (∀ j < k, (B.map.rot.symm ^ j) d ≠ B.out v ht) ∧
      ∀ j ≤ k, B.map.tail ((B.map.rot.symm ^ j) d) := by
  classical
  have hc : Equiv.Perm.SameCycle B.map.rot.symm d (B.out v ht) :=
    Equiv.Perm.sameCycle_inv.mpr
      (Quotient.exact (hv.trans (B.out_spec v ht).1.symm))
  let hex := hc.exists_nat_pow_eq
  let k := Nat.find hex
  have hk : (B.map.rot.symm ^ k) d = B.out v ht := Nat.find_spec hex
  have hmin : ∀ j < k, (B.map.rot.symm ^ j) d ≠ B.out v ht :=
    fun j hj => Nat.find_min hex hj
  refine ⟨k, hk, hmin, ?_⟩
  intro j
  induction j with
  | zero => intro _; exact hd
  | succ j ih =>
      intro hj
      have htail := ih (by omega)
      have hvertex := (clockwise_vertex_three_path B.map d j).trans hv
      have hnext : B.map.tail (B.map.rot.symm ((B.map.rot.symm ^ j) d)) := by
        by_cases hs : v = B.source
        · exact B.source_rotation_all_outgoing.1 _
            (by simpa only [pow_succ', Equiv.Perm.mul_apply] using
              (clockwise_vertex_three_path B.map d (j + 1)).trans (hv.trans hs))
        by_contra hn
        exact hmin j (by omega)
          (B.out_eq_of_extreme v hs ht _ hvertex htail hn)
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hnext

/-- Every reverse incoming dart at a vertex reaches the rightmost
reverse incoming dart counter-clockwise through incoming darts only, stopping
at its first visit; the sink's all-incoming rotation is included.
Helper toward Definition 3.13 -/
theorem incoming_counterclockwise_interval_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source)
    (d : D) (hv : dartTailVertex B.map d = v) (hd : ¬ B.map.tail d) :
    ∃ k : ℕ, (B.map.rot ^ k) d = B.inc v hs ∧
      (∀ j < k, (B.map.rot ^ j) d ≠ B.inc v hs) ∧
      ∀ j ≤ k, ¬ B.map.tail ((B.map.rot ^ j) d) := by
  classical
  have hc : B.map.rot.SameCycle d (B.inc v hs) :=
    Quotient.exact (hv.trans (B.inc_spec v hs).1.symm)
  let hex := hc.exists_nat_pow_eq
  let k := Nat.find hex
  have hk : (B.map.rot ^ k) d = B.inc v hs := Nat.find_spec hex
  have hmin : ∀ j < k, (B.map.rot ^ j) d ≠ B.inc v hs :=
    fun j hj => Nat.find_min hex hj
  refine ⟨k, hk, hmin, ?_⟩
  intro j
  induction j with
  | zero => intro _; exact hd
  | succ j ih =>
      intro hj
      have hnot := ih (by omega)
      have hvertex := (rotation_vertex_three_path B.map d j).trans hv
      have hnext : ¬ B.map.tail (B.map.rot ((B.map.rot ^ j) d)) := by
        by_cases ht : v = B.sink
        · exact B.sink_rotation_all_incoming.1 _
            (by simpa only [pow_succ', Equiv.Perm.mul_apply] using
              (rotation_vertex_three_path B.map d (j + 1)).trans (hv.trans ht))
        intro hn
        exact hmin j (by omega)
          (B.inc_eq_of_extreme v hs ht _ hvertex hnot hn)
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hnext

/-- Starting at any incoming reverse dart at an internal vertex, the first
outgoing dart counter-clockwise is the rightmost outgoing dart. Every dart
strictly before that first exit is incoming. This is the local obstruction
to leaving a rightmost outgoing path on its right. Helper toward Definition -/
theorem first_outgoing_counterclockwise_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (d : D) (hv : dartTailVertex B.map d = v) (hd : ¬ B.map.tail d) :
    ∃ k : ℕ, 0 < k ∧ (B.map.rot ^ k) d = B.out v ht ∧
      ∀ j < k, ¬ B.map.tail ((B.map.rot ^ j) d) := by
  classical
  obtain ⟨k, hk, _, hblock⟩ :=
    B.incoming_counterclockwise_interval_three_path v hs d hv hd
  refine ⟨k + 1, by omega, ?_, fun j hj => hblock j (by omega)⟩
  rw [pow_succ', Equiv.Perm.mul_apply, hk, inc, dite_eq_right ht,
    Equiv.apply_symm_apply]

/-- Starting at any outgoing dart at an internal vertex, the first reverse
incoming dart clockwise is the rightmost incoming selector. Every dart
strictly before that exit is outgoing. Helper toward Definition 3.13 -/
theorem first_incoming_clockwise_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (d : D) (hv : dartTailVertex B.map d = v) (hd : B.map.tail d) :
    ∃ k : ℕ, 0 < k ∧ (B.map.rot.symm ^ k) d = B.inc v hs ∧
      ∀ j < k, B.map.tail ((B.map.rot.symm ^ j) d) := by
  classical
  obtain ⟨k, hk, _, hblock⟩ :=
    B.outgoing_clockwise_interval_three_path v ht d hv hd
  refine ⟨k + 1, by omega, ?_, fun j hj => hblock j (by omega)⟩
  rw [pow_succ', Equiv.Perm.mul_apply, hk, inc, dite_eq_right ht]

private theorem first_rotation_visit_three_path (p : Equiv.Perm D) (a b : D)
    (hc : p.SameCycle a b) :
    ∃ k : ℕ, (p ^ k) a = b ∧
      (∀ j < k, (p ^ j) a ≠ b) ∧
      ∀ j, 0 < j → j ≤ k → (p ^ j) a ≠ a := by
  classical
  let hex := hc.exists_nat_pow_eq
  let k := Nat.find hex
  have hk : (p ^ k) a = b := Nat.find_spec hex
  have hmin : ∀ j < k, (p ^ j) a ≠ b := fun j hj => Nat.find_min hex hj
  refine ⟨k, hk, hmin, ?_⟩
  intro j hj hjk he
  have hperiod : (p ^ k) a = (p ^ (k - j)) a := by
    calc
      (p ^ k) a = (p ^ (k - j + j)) a := by rw [Nat.sub_add_cancel hjk]
      _ = (p ^ (k - j)) ((p ^ j) a) := by rw [pow_add, Equiv.Perm.mul_apply]
      _ = (p ^ (k - j)) a := by rw [he]
  exact hmin (k - j) (by omega) (hperiod.symm.trans hk)

private theorem incoming_reverse_not_source_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) (hd : ¬ B.map.tail d) :
    dartTailVertex B.map d ≠ B.source := by
  intro hv
  have hi : B.map.tail (B.map.edgeInv d) := by
    by_contra hn
    exact hd ((B.map.tail_iff d (B.noMissingDarts d)).mpr hn)
  apply B.isSource
  refine ⟨_, B.map.edgeInv d, B.noMissingDarts _, hi, rfl, ?_⟩
  simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using hv

private theorem outgoing_not_sink_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) (d : D) (hd : B.map.tail d) :
    dartTailVertex B.map d ≠ B.sink := by
  intro hv
  exact B.isSink ⟨_, d, B.noMissingDarts d, hd, hv, rfl⟩

/-- At any dart of an outgoing-selected path, start the counter-clockwise
rotation scan at any incoming reverse dart at that vertex. The path's dart
is the first outgoing dart. Every other outgoing dart is visited strictly
later, before a return to the incoming starting dart. Thus all alternative
directed departures lie on the same local side of the selected path, with
edge identities retained. An incoming starting dart itself proves that the
vertex is not the source. Helper toward Definition 3.13
vertices off the path. -/
theorem out_path_departure_rotation_order_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P)
    (i : Fin P.darts.length) (a : D)
    (ha : ¬ B.map.tail a)
    (hav : dartTailVertex B.map a = dartTailVertex B.map (P.darts.get i)) :
    ∃ k : ℕ, 0 < k ∧ (B.map.rot ^ k) a = P.darts.get i ∧
      (∀ j < k, ¬ B.map.tail ((B.map.rot ^ j) a)) ∧
      ∀ e : D, dartTailVertex B.map e = dartTailVertex B.map (P.darts.get i) →
        B.map.tail e → e ≠ P.darts.get i →
        ∃ l : ℕ, k < l ∧ (B.map.rot ^ l) a = e ∧
          (∀ j < l, (B.map.rot ^ j) a ≠ e) ∧
          ∀ j, 0 < j → j ≤ l → (B.map.rot ^ j) a ≠ a := by
  obtain ⟨ht, hsel⟩ := hP i
  have hs : dartTailVertex B.map (P.darts.get i) ≠ B.source :=
    fun h => incoming_reverse_not_source_three_path B a ha (hav.trans h)
  obtain ⟨k, hkpos, hk, hbefore⟩ := B.first_outgoing_counterclockwise_three_path
    _ hs ht a hav ha
  have hk' : (B.map.rot ^ k) a = P.darts.get i := hk.trans hsel.symm
  refine ⟨k, hkpos, hk', hbefore, ?_⟩
  intro e hev he hne
  have hc : B.map.rot.SameCycle a e := Quotient.exact (hav.trans hev.symm)
  obtain ⟨l, hl, hfirst, hreturn⟩ := first_rotation_visit_three_path B.map.rot a e hc
  have hkl : k < l := by
    have hnot : ¬ l < k := fun hlt => hbefore l hlt (hl.symm ▸ he)
    have hneq : l ≠ k := fun heq => hne (hl.symm.trans (heq ▸ hk'))
    omega
  exact ⟨l, hkl, hl, hfirst, hreturn⟩

/-- Dual local order at an incoming-selected path: in a clockwise scan
started at any outgoing dart, the path's reverse incoming dart is the first
incoming dart. All other reverse incoming darts occur strictly later and
before returning to the outgoing starting dart. This controls directed
entries into the path, without a global separation premise. Helper toward -/
theorem in_path_entry_rotation_order_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.In P)
    (i : Fin P.darts.length) (a : D) (ha : B.map.tail a)
    (hav : dartTailVertex B.map a = dartHeadVertex B.map (P.darts.get i)) :
    ∃ k : ℕ, 0 < k ∧ (B.map.rot.symm ^ k) a = B.map.edgeInv (P.darts.get i) ∧
      (∀ j < k, B.map.tail ((B.map.rot.symm ^ j) a)) ∧
      ∀ e : D, dartTailVertex B.map e = dartHeadVertex B.map (P.darts.get i) →
        ¬ B.map.tail e → e ≠ B.map.edgeInv (P.darts.get i) →
        ∃ l : ℕ, k < l ∧ (B.map.rot.symm ^ l) a = e ∧
          (∀ j < l, (B.map.rot.symm ^ j) a ≠ e) ∧
          ∀ j, 0 < j → j ≤ l → (B.map.rot.symm ^ j) a ≠ a := by
  obtain ⟨hs, hsel⟩ := hP i
  have ht : dartHeadVertex B.map (P.darts.get i) ≠ B.sink :=
    fun h => outgoing_not_sink_three_path B a ha (hav.trans h)
  obtain ⟨k, hkpos, hk, hbefore⟩ := B.first_incoming_clockwise_three_path
    _ hs ht a hav ha
  have hk' : (B.map.rot.symm ^ k) a = B.map.edgeInv (P.darts.get i) :=
    hk.trans hsel.symm
  refine ⟨k, hkpos, hk', hbefore, ?_⟩
  intro e hev he hne
  have hc : Equiv.Perm.SameCycle B.map.rot.symm a e :=
    Equiv.Perm.sameCycle_inv.mpr (Quotient.exact (hav.trans hev.symm))
  obtain ⟨l, hl, hfirst, hreturn⟩ :=
    first_rotation_visit_three_path B.map.rot.symm a e hc
  have hkl : k < l := by
    have hnot : ¬ l < k := fun hlt => he (hl ▸ hbefore l hlt)
    have hneq : l ≠ k := fun heq => hne (hl.symm.trans (heq ▸ hk'))
    omega
  exact ⟨l, hkl, hl, hfirst, hreturn⟩

/-- The open counter-clockwise sector from any incoming reverse dart to an
outgoing-selected path's dart contains no outgoing dart. Thus no directed
departure at that vertex can use this right-hand local sector. The sector is
defined solely by the finite rotation, with no side or separation premise. -/
theorem out_path_right_sector_not_outgoing_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P)
    (i : Fin P.darts.length) (a : D)
    (ha : ¬ B.map.tail a)
    (hav : dartTailVertex B.map a = dartTailVertex B.map (P.darts.get i))
    {e : D} (he : e ∈ openRotationInterval_three_path B.map.rot a (P.darts.get i)) :
    ¬ B.map.tail e := by
  obtain ⟨k, _, hk, hbefore, _⟩ :=
    B.out_path_departure_rotation_order_three_path P hP i a ha hav
  obtain ⟨l, _, hfirst, j, _, hj, hje⟩ := he
  have hlk : l ≤ k := Nat.le_of_not_gt (fun hkl => hfirst k hkl hk)
  exact hje ▸ hbefore j (by omega)

/-- The open clockwise sector from any outgoing dart to an incoming-selected
path's reverse dart contains only outgoing darts. Consequently a reverse
incoming dart cannot lie in this right-hand local sector. Helper toward
the global side of an off-path vertex. -/
theorem in_path_right_sector_outgoing_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.In P)
    (i : Fin P.darts.length) (a : D) (ha : B.map.tail a)
    (hav : dartTailVertex B.map a = dartHeadVertex B.map (P.darts.get i))
    {e : D} (he : e ∈ openRotationInterval_three_path B.map.rot.symm a
      (B.map.edgeInv (P.darts.get i))) : B.map.tail e := by
  obtain ⟨k, _, hk, hbefore, _⟩ :=
    B.in_path_entry_rotation_order_three_path P hP i a ha hav
  obtain ⟨l, _, hfirst, j, _, hj, hje⟩ := he
  have hlk : l ≤ k := Nat.le_of_not_gt (fun hkl => hfirst k hkl hk)
  exact hje ▸ hbefore j (by omega)

/-- The unique rightmost path from a vertex to the sink, retaining its
length. Existence and uniqueness precede this choice. Helper toward -/
@[expose] noncomputable def rightmostOutPath
    (B : BipolarMapWithBoundaryBase D ℓ r) (x : MapVertex B.map) :
    Σ n, SimpleDirectedDartPath B.map x B.sink n :=
  ⟨Classical.choose (B.exists_unique_out_path x),
    Classical.choose (Classical.choose_spec (B.exists_unique_out_path x))⟩

/-- The unique rightmost path from the source into a vertex, retaining its
length. Existence and uniqueness precede this choice. Helper toward -/
@[expose] noncomputable def rightmostInPath
    (B : BipolarMapWithBoundaryBase D ℓ r) (y : MapVertex B.map) :
    Σ n, SimpleDirectedDartPath B.map B.source y n :=
  ⟨Classical.choose (B.exists_unique_in_path y),
    Classical.choose (Classical.choose_spec (B.exists_unique_in_path y))⟩

/-- The chosen outgoing path follows every outgoing selector. Helper toward -/
theorem rightmostOutPath_out (B : BipolarMapWithBoundaryBase D ℓ r)
    (x : MapVertex B.map) : B.Out (B.rightmostOutPath x).2 :=
  (Classical.choose_spec (Classical.choose_spec (B.exists_unique_out_path x))).1

/-- The chosen incoming path follows every incoming selector. Helper toward -/
theorem rightmostInPath_in (B : BipolarMapWithBoundaryBase D ℓ r)
    (y : MapVertex B.map) : B.In (B.rightmostInPath y).2 :=
  (Classical.choose_spec (Classical.choose_spec (B.exists_unique_in_path y))).1

/-- Full outgoing-selector characterization, independent of the witness
chosen above. Helper toward Definition 3.13 -/
theorem out_iff_darts_eq_rightmostOutPath (B : BipolarMapWithBoundaryBase D ℓ r)
    {x : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x B.sink n) :
    B.Out P ↔ P.darts = (B.rightmostOutPath x).2.darts := by
  constructor
  · intro hP
    exact B.out_path_darts_eq (B.rightmostOutPath x).2 P
      (B.rightmostOutPath_out x) hP
  · intro hd
    unfold Out
    rw [hd]
    exact B.rightmostOutPath_out x

/-- Full incoming-selector characterization, independent of the witness
chosen above. Helper toward Definition 3.13 -/
theorem in_iff_darts_eq_rightmostInPath (B : BipolarMapWithBoundaryBase D ℓ r)
    {y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source y n) :
    B.In P ↔ P.darts = (B.rightmostInPath y).2.darts := by
  constructor
  · intro hP
    exact B.in_path_darts_eq (B.rightmostInPath y).2 P
      (B.rightmostInPath_in y) hP
  · intro hd
    unfold In
    rw [hd]
    exact B.rightmostInPath_in y

/-- The endpoint of an outgoing-selected path occurs at its length on the
canonical outgoing path. The given path need not end at the sink.
Helper toward Definition 3.13 -/
theorem end_index_rightmostOutPath_of_out (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P) :
    ∃ i : Fin (B.rightmostOutPath x).2.vertices.length,
      i.val = n ∧ (B.rightmostOutPath x).2.vertices.get i = y := by
  let Q := (B.rightmostOutPath x).2
  have hQ : B.Out Q := B.rightmostOutPath_out x
  have hv : ∀ i (hiP : i ≤ n) (hiQ : i ≤ (B.rightmostOutPath x).1),
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ =
        Q.vertices.get ⟨i, by rw [Q.vertices_length]; omega⟩ := by
    intro i
    induction i with
    | zero => intro _ _; exact P.start_vertex.trans Q.start_vertex.symm
    | succ i ih =>
        intro hiP hiQ
        have hp := P.edge_step ⟨i, by rw [P.darts_length]; omega⟩
        have hq := Q.edge_step ⟨i, by rw [Q.darts_length]; omega⟩
        obtain ⟨htP, hdP⟩ := hP ⟨i, by rw [P.darts_length]; omega⟩
        obtain ⟨htQ, hdQ⟩ := hQ ⟨i, by rw [Q.darts_length]; omega⟩
        have htail := hp.2.2.1.symm.trans
          ((ih (by omega) (by omega)).trans hq.2.2.1)
        have hd : P.darts.get ⟨i, by rw [P.darts_length]; omega⟩ =
            Q.darts.get ⟨i, by rw [Q.darts_length]; omega⟩ := by
          rw [hdP, hdQ]
          congr 1
        exact hp.2.2.2.trans
          ((congrArg (dartHeadVertex B.map) hd).trans hq.2.2.2.symm)
  have hn : n ≤ (B.rightmostOutPath x).1 := by
    by_contra hlt
    have hp := P.edge_step
      ⟨(B.rightmostOutPath x).1, by rw [P.darts_length]; omega⟩
    have htail := hp.2.2.1.symm.trans ((hv _ (by omega) le_rfl).trans Q.end_vertex)
    exact B.isSink ⟨_, _, hp.1, hp.2.1, htail, rfl⟩
  exact ⟨⟨n, by rw [Q.vertices_length]; omega⟩, rfl,
    (hv n le_rfl hn).symm.trans P.end_vertex⟩

/-- The start of an incoming-selected path occurs on the canonical incoming
path at the given path's length from the end. The given path need not start
at the source. Helper toward Definition 3.13 -/
theorem start_index_rightmostInPath_of_in (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.In P) :
    ∃ i : Fin (B.rightmostInPath y).2.vertices.length,
      i.val + n = (B.rightmostInPath y).1 ∧
        (B.rightmostInPath y).2.vertices.get i = x := by
  let Q := (B.rightmostInPath y).2
  let m := (B.rightmostInPath y).1
  have hQ : B.In Q := B.rightmostInPath_in y
  have hv : ∀ i (hiP : i ≤ n) (hiQ : i ≤ m),
      P.vertices.get ⟨n - i, by rw [P.vertices_length]; omega⟩ =
        Q.vertices.get ⟨m - i, by rw [Q.vertices_length]; omega⟩ := by
    intro i
    induction i with
    | zero => intro _ _; exact P.end_vertex.trans Q.end_vertex.symm
    | succ i ih =>
        intro hiP hiQ
        have hp := P.edge_step ⟨n - (i + 1), by rw [P.darts_length]; omega⟩
        have hq := Q.edge_step ⟨m - (i + 1), by rw [Q.darts_length]; omega⟩
        obtain ⟨hsP, hdP⟩ := hP ⟨n - (i + 1), by rw [P.darts_length]; omega⟩
        obtain ⟨hsQ, hdQ⟩ := hQ ⟨m - (i + 1), by rw [Q.darts_length]; omega⟩
        have hhead : dartHeadVertex B.map
            (P.darts.get ⟨n - (i + 1), by rw [P.darts_length]; omega⟩) =
            dartHeadVertex B.map
              (Q.darts.get ⟨m - (i + 1), by rw [Q.darts_length]; omega⟩) := by
          rw [← hp.2.2.2, ← hq.2.2.2]
          have hpn : n - (i + 1) + 1 = n - i := by omega
          have hqm : m - (i + 1) + 1 = m - i := by omega
          simpa only [hpn, hqm] using ih (by omega) (by omega)
        have hd : P.darts.get ⟨n - (i + 1), by rw [P.darts_length]; omega⟩ =
            Q.darts.get ⟨m - (i + 1), by rw [Q.darts_length]; omega⟩ := by
          apply B.map.edgeInv.injective
          rw [hdP, hdQ]
          congr 1
        exact hp.2.2.1.trans
          ((congrArg (dartTailVertex B.map) hd).trans hq.2.2.1.symm)
  have hn : n ≤ m := by
    by_contra hlt
    have hp := P.edge_step ⟨n - (m + 1), by rw [P.darts_length]; omega⟩
    have hhead : dartHeadVertex B.map
        (P.darts.get ⟨n - (m + 1), by rw [P.darts_length]; omega⟩) = B.source := by
      rw [← hp.2.2.2]
      have he := hv m (by omega) le_rfl
      simp only [Nat.sub_self] at he
      have hpn : n - (m + 1) + 1 = n - m := by omega
      simpa only [hpn] using he.trans Q.start_vertex
    exact B.isSource ⟨_, _, hp.1, hp.2.1, rfl, hhead⟩
  refine ⟨⟨m - n, by rw [Q.vertices_length]; omega⟩, by dsimp [m]; omega, ?_⟩
  have he := hv n le_rfl hn
  simpa only [Nat.sub_self, P.start_vertex] using he.symm

/-- The canonical outgoing path at the sink is empty. Helper toward -/
theorem rightmostOutPath_sink (B : BipolarMapWithBoundaryBase D ℓ r) :
    (B.rightmostOutPath B.sink).1 = 0 ∧
      (B.rightmostOutPath B.sink).2.darts = [] ∧
      (B.rightmostOutPath B.sink).2.vertices = [B.sink] :=
  (B.rightmostOutPath B.sink).2.self_path_lists

/-- The canonical incoming path at the source is empty. Helper toward -/
theorem rightmostInPath_source (B : BipolarMapWithBoundaryBase D ℓ r) :
    (B.rightmostInPath B.source).1 = 0 ∧
      (B.rightmostInPath B.source).2.darts = [] ∧
      (B.rightmostInPath B.source).2.vertices = [B.source] :=
  (B.rightmostInPath B.source).2.self_path_lists

/-- Starting at the source recovers the right boundary's outgoing dart list. -/
theorem rightmostOutPath_source_darts (B : BipolarMapWithBoundaryBase D ℓ r) :
    (B.rightmostOutPath B.source).2.darts = B.rightPath.darts :=
  B.out_path_darts_eq B.rightPath (B.rightmostOutPath B.source).2
    B.out_rightPath (B.rightmostOutPath_out B.source)

/-- Ending at the sink recovers the right boundary's incoming dart list. -/
theorem rightmostInPath_sink_darts (B : BipolarMapWithBoundaryBase D ℓ r) :
    (B.rightmostInPath B.sink).2.darts = B.rightPath.darts :=
  B.in_path_darts_eq B.rightPath (B.rightmostInPath B.sink).2
    B.in_rightPath (B.rightmostInPath_in B.sink)

/-- If `x` is on the incoming path into `y`, it is the first common vertex
along the outgoing path from `x`. This includes `x = y`. Helper toward -/
theorem first_meeting_at_start (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} (hx : x ∈ (B.rightmostInPath y).2.vertices) :
    ∃ i : Fin (B.rightmostOutPath x).2.vertices.length,
      i.val = 0 ∧ (B.rightmostOutPath x).2.vertices.get i = x ∧
        (B.rightmostOutPath x).2.vertices.get i ∈ (B.rightmostInPath y).2.vertices ∧
        ∀ j : Fin (B.rightmostOutPath x).2.vertices.length,
          j.val < i.val → (B.rightmostOutPath x).2.vertices.get j ∉
            (B.rightmostInPath y).2.vertices := by
  refine ⟨⟨0, by rw [(B.rightmostOutPath x).2.vertices_length]; omega⟩,
    rfl, (B.rightmostOutPath x).2.start_vertex, ?_, ?_⟩
  · simpa only [(B.rightmostOutPath x).2.start_vertex] using hx
  · intro j hj
    exact (Nat.not_lt_zero j.val hj).elim

/-- Equal endpoints give a meeting at that vertex even when it is a pole. -/
theorem rightmost_paths_meet_self (B : BipolarMapWithBoundaryBase D ℓ r)
    (x : MapVertex B.map) :
    x ∈ (B.rightmostOutPath x).2.vertices ∧
      x ∈ (B.rightmostInPath x).2.vertices :=
  ⟨(B.rightmostOutPath x).2.start_mem_vertices_three_path,
    (B.rightmostInPath x).2.end_mem_vertices_three_path⟩

/-- If `y` is on the outgoing path, a first common vertex exists, possibly
before `y`. Helper toward Definition 3.13 -/
theorem exists_first_meeting_of_end_mem_out (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} (hy : y ∈ (B.rightmostOutPath x).2.vertices) :
    ∃ i : Fin (B.rightmostOutPath x).2.vertices.length,
      (B.rightmostOutPath x).2.vertices.get i ∈ (B.rightmostInPath y).2.vertices ∧
        ∀ j : Fin (B.rightmostOutPath x).2.vertices.length, j.val < i.val →
          (B.rightmostOutPath x).2.vertices.get j ∉ (B.rightmostInPath y).2.vertices := by
  exact SimpleDirectedDartPath.exists_first_common_index _ _
    ⟨y, hy, (B.rightmostInPath y).2.end_mem_vertices_three_path⟩

/-- When the initial endpoint is the source, the two rightmost paths meet
at the source. Helper toward Definition 3.13 -/
theorem rightmost_paths_meet_source (B : BipolarMapWithBoundaryBase D ℓ r)
    (y : MapVertex B.map) :
    B.source ∈ (B.rightmostOutPath B.source).2.vertices ∧
      B.source ∈ (B.rightmostInPath y).2.vertices :=
  ⟨(B.rightmostOutPath B.source).2.start_mem_vertices_three_path,
    (B.rightmostInPath y).2.start_mem_vertices_three_path⟩

/-- When the terminal endpoint is the sink, the two rightmost paths meet
at the sink. Helper toward Definition 3.13 -/
theorem rightmost_paths_meet_sink (B : BipolarMapWithBoundaryBase D ℓ r)
    (x : MapVertex B.map) :
    B.sink ∈ (B.rightmostOutPath x).2.vertices ∧
      B.sink ∈ (B.rightmostInPath B.sink).2.vertices :=
  ⟨(B.rightmostOutPath x).2.end_mem_vertices_three_path,
    (B.rightmostInPath B.sink).2.end_mem_vertices_three_path⟩

/-- A directed path following the outgoing selector throughout, or the
incoming selector throughout, supplies a unique first common pair on the
two canonical paths. Both minimality clauses include the zero-length and
pole cases. Helper toward Definition 3.13 -/
theorem exists_unique_first_rightmost_pair_of_out_or_in
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P ∨ B.In P) :
    ∃! ij : Fin (B.rightmostOutPath x).2.vertices.length ×
        Fin (B.rightmostInPath y).2.vertices.length,
      (B.rightmostOutPath x).2.vertices.get ij.1 =
          (B.rightmostInPath y).2.vertices.get ij.2 ∧
        (∀ k : Fin (B.rightmostOutPath x).2.vertices.length, k.val < ij.1.val →
          (B.rightmostOutPath x).2.vertices.get k ∉ (B.rightmostInPath y).2.vertices) ∧
        (∀ l : Fin (B.rightmostInPath y).2.vertices.length, l.val < ij.2.val →
          (B.rightmostInPath y).2.vertices.get l ∉ (B.rightmostOutPath x).2.vertices) := by
  apply SimpleDirectedDartPath.exists_unique_first_common_pair_three_path B.acyclic
  rcases hP with hOut | hIn
  · obtain ⟨i, _, hi⟩ := B.end_index_rightmostOutPath_of_out P hOut
    exact ⟨y, List.mem_iff_get.mpr ⟨i, hi⟩,
      (B.rightmostInPath y).2.end_mem_vertices_three_path⟩
  · obtain ⟨j, _, hj⟩ := B.start_index_rightmostInPath_of_in P hIn
    exact ⟨x, (B.rightmostOutPath x).2.start_mem_vertices_three_path,
      List.mem_iff_get.mpr ⟨j, hj⟩⟩

/-- T1 holds when some directed path between the endpoints follows one
of the two rightmost selectors throughout. No intersection or endpoint
membership is assumed. Helper toward Definition 3.13 -/
theorem exists_first_rightmost_meeting_of_out_or_in
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P ∨ B.In P) :
    ∃ i : Fin (B.rightmostOutPath x).2.vertices.length,
      (B.rightmostOutPath x).2.vertices.get i ∈ (B.rightmostInPath y).2.vertices ∧
        ∀ j : Fin (B.rightmostOutPath x).2.vertices.length, j.val < i.val →
          (B.rightmostOutPath x).2.vertices.get j ∉ (B.rightmostInPath y).2.vertices := by
  obtain ⟨⟨i, j⟩, ⟨hij, hfirst, _⟩, _⟩ :=
    B.exists_unique_first_rightmost_pair_of_out_or_in P hP
  exact ⟨i, List.mem_iff_get.mpr ⟨j, hij.symm⟩, hfirst⟩


private theorem out_eq_of_reverse_outer_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {v : MapVertex B.map}
    (ht : v ≠ B.sink) (d : D) (hdv : dartTailVertex B.map d = v)
    (hd : B.map.tail d) (ho : B.map.IsOuter (B.map.edgeInv d)) :
    d = B.out v ht := by
  have hn := (B.map.tail_iff d (B.noMissingDarts d)).mp hd
  rcases (ThreePathFaceLabels.isOuter_iff_mem_outerArcs B _).mp ho with hl | hr
  · exact (hn hl.2.1).elim
  · obtain ⟨e, he, hed⟩ := List.mem_map.mp
      ((ThreePathFaceLabels.mem_pathCutRightOuterArc_iff B _).mp hr)
    have hed' : e = d := B.map.edgeInv.injective hed
    have hm : d ∈ B.rightPath.darts := hed' ▸ List.mem_reverse.mp he
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    obtain ⟨ht', hs⟩ := B.out_rightPath i
    simpa only [hi, hdv] using hs

/-- At an outgoing-selected dart of any source-to-sink cut, every outgoing
dart at that vertex has the left-side label. This connects the local
rightmost selector to global face labels, including the source corner.
It does not assert that arbitrary-endpoint selected paths intersect. -/
theorem side_outgoing_at_out_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (ht : v ≠ B.sink) {b : D}
    (hb : b ∈ C.darts) (hbOut : b = B.out v ht)
    (d : D) (hdv : dartTailVertex B.map d = v) (hd : B.map.tail d) :
    ThreePathFaceLabels.side B C d = true := by
  have hbv : dartTailVertex B.map b = v := by
    rw [hbOut]
    exact (B.out_spec v ht).1
  obtain ⟨k, hk, hmin, htail⟩ :=
    B.outgoing_clockwise_interval_three_path v ht d hdv hd
  have hseq : ∀ j, j ≤ k →
      ThreePathFaceLabels.side B C ((B.map.rot.symm ^ j) d) =
        ThreePathFaceLabels.side B C d := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
        intro hj
        let q := (B.map.rot.symm ^ j) d
        have hqv : dartTailVertex B.map q = v :=
          (clockwise_vertex_three_path B.map d j).trans hdv
        have hqt : B.map.tail q := htail j (by omega)
        have hqb : q ≠ b := by
          intro he
          exact hmin j (by omega) (he.trans hbOut)
        have hqC : q ∉ C.darts := by
          intro he
          exact hqb (ThreePathFaceLabels.simplePath_dart_eq_of_endpoint_eq C he hb
            (.inl (hqv.trans hbv.symm)))
        have hqiC : B.map.edgeInv q ∉ C.darts := by
          intro he
          exact ((B.map.tail_iff q (B.noMissingDarts q)).mp hqt)
            (ThreePathFaceLabels.simplePath_tail_of_mem C he)
        have hinner : ¬ B.map.IsOuter (B.map.edgeInv q) := by
          intro ho
          exact hqb ((B.out_eq_of_reverse_outer_three_path ht q hqv hqt ho).trans
            hbOut.symm)
        have hs := ThreePathFaceLabels.pathCutSide_eq_rotSymm_of_inner_offSeam
          B C (ThreePathFaceLabels.side B C)
          (ThreePathFaceLabels.side_faceSucc_of_inner B C)
          (fun a ha => ThreePathFaceLabels.side_edgeInv_of_not_seam B C a
            (fun h => ha (.inl h)) (fun h => ha (.inr h)))
          q hinner (fun h => h.elim hqC hqiC)
        simpa only [pow_succ', Equiv.Perm.mul_apply] using
          hs.trans (ih (by omega))
  have he := hseq k le_rfl
  rw [hk, ← hbOut] at he
  exact he.symm.trans (ThreePathFaceLabels.side_path_dart B C hb)



/-- Every vertex reachable from the start of an outgoing-selected suffix
lies on the cut or on its left side. The suffix selection is stated on the
actual cut darts; no side or intersection premise is used. Helper toward
This is a source-to-sink extension lemma, not the arbitrary-endpoint
intersection assertion. -/
theorem offPathSide_of_reaches_selected_suffix_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : Fin C.vertices.length)
    (hsel : ∀ j : Fin C.darts.length, i.val ≤ j.val →
      ∃ ht : dartTailVertex B.map (C.darts.get j) ≠ B.sink,
        C.darts.get j = B.out _ ht)
    {z : MapVertex B.map}
    (hreach : Relation.ReflTransGen B.map.directedStep (C.vertices.get i) z)
    (hz : z ∉ C.vertices) :
    ThreePathFaceLabels.offPathSide B C ⟨z, hz⟩ = true := by
  revert hz
  induction hreach with
  | refl =>
      intro hz
      exact (hz (List.get_mem C.vertices i)).elim
  | @tail u v hxu huv ih =>
      intro hv
      by_cases hu : u ∈ C.vertices
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hu
        have hij := C.index_le_of_reaches_three_path B.acyclic i j
          (by simpa only [hj] using hxu)
        obtain ⟨d, hmiss, hdt, hdU, hdV⟩ := huv
        have hnotSink : u ≠ B.sink := by
          intro he
          exact B.isSink ⟨v, d, hmiss, hdt, hdU.trans he, hdV⟩
        have hjn : j.val < n := by
          have hjlt := j.isLt
          have hlen := C.vertices_length
          by_contra hn
          have hjlast : j = ⟨n, by rw [C.vertices_length]; omega⟩ :=
            Fin.ext (show j.val = n by omega)
          apply hnotSink
          exact hj.symm.trans (by rw [hjlast]; exact C.end_vertex)
        let jd : Fin C.darts.length := ⟨j.val, by rw [C.darts_length]; exact hjn⟩
        have hstep := C.edge_step jd
        have hbv : dartTailVertex B.map (C.darts.get jd) = u :=
          hstep.2.2.1.symm.trans
            ((congrArg C.vertices.get (Fin.ext rfl)).trans hj)
        obtain ⟨ht, hbsel⟩ := hsel jd (by simpa only [jd] using hij)
        have hside := B.side_outgoing_at_out_cut_three_path C hnotSink
          (List.get_mem C.darts jd) (by simpa only [hbv] using hbsel)
          d hdU hdt
        rw [ThreePathFaceLabels.offPathSide_eq B C ⟨v, hv⟩
          (B.map.edgeInv d) hdV]
        exact (ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B C d
          (.inr (fun h => hv (hdV ▸ h)))).trans hside
      · exact (ThreePathFaceLabels.offPathSide_eq_of_directedStep B C
          ⟨u, hu⟩ ⟨v, hv⟩ huv).symm.trans (ih hu)


private theorem incoming_outer_predecessor_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {v : MapVertex B.map}
    (hs : v ≠ B.source) (d : D) (hdv : dartTailVertex B.map d = v)
    (hd : ¬ B.map.tail d) (hp : ¬ B.map.tail (B.map.rot.symm d))
    (ho : B.map.IsOuter (B.map.edgeInv d)) :
    B.map.rot.symm d = B.inc v hs := by
  classical
  have he : B.map.tail (B.map.edgeInv d) :=
    (B.map.tail_iff _ (B.noMissingDarts _)).mpr
      (by simpa only [B.map.edgeInv_invol] using hd)
  have hf : B.map.faceSucc (B.map.edgeInv d) = B.map.rot.symm d := by
    simpa only [B.map.edgeInv_invol] using
      (ThreePathFaceLabels.corner_consecutiveDarts B (B.map.edgeInv d)).1
  rcases (ThreePathFaceLabels.isOuter_iff_mem_outerArcs B _).mp ho with hl | hr
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp
      ((ThreePathFaceLabels.mem_pathCutLeftOuterArc_iff B _).mp hl)
    have hil : i.val < ℓ := by simpa only [B.leftPath.darts_length] using i.isLt
    by_cases hn : i.val + 1 < ℓ
    · have hnext := ThreePathFaceLabels.outerFace_leftPath_successor B i.val hn
      have hget : B.leftPath.darts[i.val] = B.map.edgeInv d := hi
      rw [hget, hf] at hnext
      exact (hp (hnext.symm ▸
        ThreePathFaceLabels.simplePath_tail_of_mem B.leftPath
          (List.getElem_mem _))).elim
    · have hlast : i.val = ℓ - 1 := by omega
      have hlend : B.map.edgeInv d = B.leftPath.darts.get
          ⟨ℓ - 1, by rw [B.leftPath.darts_length]; omega⟩ := by
        exact hi.symm.trans (congrArg B.leftPath.darts.get (Fin.ext hlast))
      have hvSink : v = B.sink := by
        have hstep := B.leftPath.edge_step i
        have hhead : dartHeadVertex B.map (B.map.edgeInv d) = v := by
          simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using hdv
        have hidx : (⟨i.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ :
            Fin B.leftPath.vertices.length) =
            ⟨ℓ, by rw [B.leftPath.vertices_length]; omega⟩ :=
          Fin.ext (by change i.val + 1 = ℓ; omega)
        exact hhead.symm.trans ((hi ▸ hstep.2.2.2.symm).trans
          ((congrArg B.leftPath.vertices.get hidx).trans B.leftPath.end_vertex))
      rw [← hf, hlend, B.outerFace_sinkCorner_eq_lastRightDart]
      simp only [inc, dite_eq_left hvSink]
  · exact (hr.2.1 he).elim

/-- At an incoming-selected cut dart, every other reverse incoming dart
has the left label. The selected reverse dart itself has the right label.
The sink corner is included. Helper toward Definition 3.13 -/
theorem side_incoming_at_in_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hs : v ≠ B.source) {b : D}
    (hb : b ∈ C.darts) (hbIn : B.map.edgeInv b = B.inc v hs)
    (d : D) (hdv : dartTailVertex B.map d = v) (hd : ¬ B.map.tail d)
    (hdb : d ≠ B.map.edgeInv b) :
    ThreePathFaceLabels.side B C d = true := by
  have hbv : dartTailVertex B.map (B.map.edgeInv b) = v := by
    rw [hbIn]
    exact (B.inc_spec v hs).1
  obtain ⟨k, hk, hmin, htail⟩ :=
    B.incoming_counterclockwise_interval_three_path v hs d hdv hd
  have hpos : 0 < k := by
    by_contra hn
    have hz : k = 0 := by omega
    exact hdb (by simpa only [hz, pow_zero, Equiv.Perm.one_apply] using hk.trans hbIn.symm)
  have hseq : ∀ j, j < k →
      ThreePathFaceLabels.side B C ((B.map.rot ^ j) d) =
        ThreePathFaceLabels.side B C d := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
        intro hj
        let q := (B.map.rot ^ j) d
        let a := B.map.rot q
        have hqv : dartTailVertex B.map q = v :=
          (rotation_vertex_three_path B.map d j).trans hdv
        have hav : dartTailVertex B.map a = v := by
          simpa only [a, q, pow_succ', Equiv.Perm.mul_apply] using
            (rotation_vertex_three_path B.map d (j + 1)).trans hdv
        have hqt : ¬ B.map.tail q := htail j (by omega)
        have hat : ¬ B.map.tail a := by
          simpa only [a, q, pow_succ', Equiv.Perm.mul_apply] using
            htail (j + 1) (by omega)
        have hai : a ≠ B.inc v hs := by
          simpa only [a, q, pow_succ', Equiv.Perm.mul_apply] using hmin (j + 1) hj
        have haC : a ∉ C.darts := fun hm =>
          hat (ThreePathFaceLabels.simplePath_tail_of_mem C hm)
        have haiC : B.map.edgeInv a ∉ C.darts := by
          intro hm
          have he := ThreePathFaceLabels.simplePath_dart_eq_of_endpoint_eq C hm hb
            (.inr (by
              simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using
                hav.trans hbv.symm))
          exact hai (by simpa only [B.map.edgeInv_invol] using
            (congrArg B.map.edgeInv he).trans hbIn)
        have hinner : ¬ B.map.IsOuter (B.map.edgeInv a) := by
          intro ho
          have he := B.incoming_outer_predecessor_three_path hs a hav hat
            (by simpa only [a, Equiv.symm_apply_apply] using hqt) ho
          have hqi : q = B.inc v hs := by
            simpa only [a, Equiv.symm_apply_apply] using he
          exact hmin j (by omega) hqi
        have he := ThreePathFaceLabels.pathCutSide_eq_rotSymm_of_inner_offSeam
          B C (ThreePathFaceLabels.side B C)
          (ThreePathFaceLabels.side_faceSucc_of_inner B C)
          (fun e he => ThreePathFaceLabels.side_edgeInv_of_not_seam B C e
            (fun h => he (.inl h)) (fun h => he (.inr h)))
          a hinner (fun h => h.elim haC haiC)
        have hqa : ThreePathFaceLabels.side B C q = ThreePathFaceLabels.side B C a := by
          simpa only [a, Equiv.symm_apply_apply] using he
        simpa only [a, q, pow_succ', Equiv.Perm.mul_apply] using
          hqa.symm.trans (ih (by omega))
  let q := (B.map.rot ^ (k - 1)) d
  have hqi : q ≠ B.inc v hs := hmin (k - 1) (by omega)
  have hqeq : q = B.map.rot.symm (B.map.edgeInv b) := by
    apply B.map.rot.injective
    have hpow : B.map.rot q = (B.map.rot ^ k) d := by
      dsimp only [q]
      rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos]
    rw [hpow, hk, Equiv.apply_symm_apply, hbIn]
  have hinner : ¬ B.map.IsOuter b := by
    intro ho
    have he := B.incoming_outer_predecessor_three_path hs (B.map.edgeInv b) hbv
      ((B.map.tail_iff b (B.noMissingDarts b)).mp
        (ThreePathFaceLabels.simplePath_tail_of_mem C hb))
      (by rw [← hqeq]; exact htail (k - 1) (by omega))
      (by simpa only [B.map.edgeInv_invol] using ho)
    exact hqi (hqeq.trans he)
  have hface : B.map.faceSucc b = q := by
    rw [hqeq]
    rfl
  have hside : ThreePathFaceLabels.side B C q = true := by
    rw [← hface, ThreePathFaceLabels.side_faceSucc_of_inner B C b hinner]
    exact ThreePathFaceLabels.side_path_dart B C hb
  exact (hseq (k - 1) (by omega)).symm.trans hside

/-- Every off-cut vertex that reaches the endpoint of an incoming-selected
prefix has the left label. Acyclicity prevents entry through the later
suffix. This includes the sink endpoint and a zero-length prefix. -/
theorem offPathSide_of_reaches_selected_prefix_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : Fin C.vertices.length)
    (hsel : ∀ j : Fin C.darts.length, j.val < i.val →
      ∃ hs : dartHeadVertex B.map (C.darts.get j) ≠ B.source,
        B.map.edgeInv (C.darts.get j) = B.inc _ hs)
    {z : MapVertex B.map}
    (hreach : Relation.ReflTransGen B.map.directedStep z (C.vertices.get i))
    (hz : z ∉ C.vertices) :
    ThreePathFaceLabels.offPathSide B C ⟨z, hz⟩ = true := by
  revert hz
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hz
      exact (hz (List.get_mem C.vertices i)).elim
  | @head u v huv hvi ih =>
      intro hu
      by_cases hv : v ∈ C.vertices
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
        have hji := C.index_le_of_reaches_three_path B.acyclic j i
          (by simpa only [hj] using hvi)
        obtain ⟨d, hmiss, hdt, hdU, hdV⟩ := huv
        have hnotSource : v ≠ B.source := by
          intro he
          exact B.isSource ⟨u, d, hmiss, hdt, hdU, hdV.trans he⟩
        have hjpos : 0 < j.val := by
          by_contra hn
          have hjzero : j = ⟨0, by rw [C.vertices_length]; omega⟩ :=
            Fin.ext (by change j.val = 0; omega)
          apply hnotSource
          exact hj.symm.trans (by rw [hjzero]; exact C.start_vertex)
        let jd : Fin C.darts.length :=
          ⟨j.val - 1, by
            have := j.isLt
            have := C.vertices_length
            rw [C.darts_length]
            omega⟩
        have hstep := C.edge_step jd
        have hbv : dartHeadVertex B.map (C.darts.get jd) = v :=
          hstep.2.2.2.symm.trans
            ((congrArg C.vertices.get (Fin.ext (by dsimp only [jd]; omega))).trans hj)
        obtain ⟨hs, hbsel⟩ := hsel jd (by dsimp only [jd]; omega)
        have hdb : B.map.edgeInv d ≠ B.map.edgeInv (C.darts.get jd) := by
          intro he
          have hdmem : d ∈ C.darts :=
            (B.map.edgeInv.injective he).symm ▸ List.get_mem C.darts jd
          exact hu (hdU ▸ (ThreePathFaceLabels.endpoints_mem C hdmem).1)
        have hside := B.side_incoming_at_in_cut_three_path C hnotSource
          (List.get_mem C.darts jd) (by simpa only [hbv] using hbsel)
          (B.map.edgeInv d) hdV
          ((B.map.tail_iff d (B.noMissingDarts d)).mp hdt) hdb
        rw [ThreePathFaceLabels.offPathSide_eq B C ⟨u, hu⟩ d hdU]
        exact (ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B C d
          (.inl (fun h => hu (hdU ▸ h)))).symm.trans hside
      · exact (ThreePathFaceLabels.offPathSide_eq_of_directedStep B C
          ⟨u, hu⟩ ⟨v, hv⟩ huv).trans (ih hv)

private theorem side_rot_incoming_off_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hs : v ≠ B.source) (q : D)
    (hqv : dartTailVertex B.map q = v) (hqt : ¬ B.map.tail q)
    (hqi : q ≠ B.inc v hs) (hat : ¬ B.map.tail (B.map.rot q))
    (haC : B.map.edgeInv (B.map.rot q) ∉ C.darts) :
    ThreePathFaceLabels.side B C (B.map.rot q) =
      ThreePathFaceLabels.side B C q := by
  let a := B.map.rot q
  have hav : dartTailVertex B.map a = v :=
    (rotation_vertex_three_path B.map q 1).trans hqv
  have hinner : ¬ B.map.IsOuter (B.map.edgeInv a) := by
    intro ho
    have he := B.incoming_outer_predecessor_three_path hs a hav hat
      (by simpa only [a, Equiv.symm_apply_apply] using hqt) ho
    exact hqi (by simpa only [a, Equiv.symm_apply_apply] using he)
  have he := ThreePathFaceLabels.pathCutSide_eq_rotSymm_of_inner_offSeam
    B C (ThreePathFaceLabels.side B C)
    (ThreePathFaceLabels.side_faceSucc_of_inner B C)
    (fun e he => ThreePathFaceLabels.side_edgeInv_of_not_seam B C e
      (fun h => he (.inl h)) (fun h => he (.inr h))) a hinner
    (fun h => h.elim
      (fun hm => hat (ThreePathFaceLabels.simplePath_tail_of_mem C hm)) haC)
  simpa only [a, Equiv.symm_apply_apply] using he.symm

/-- The incoming right extreme is on the right of a cut that uses the
outgoing right extreme. At the sink the marked outer corner gives the same -/
theorem side_inc_at_out_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hs : v ≠ B.source)
    (hsel : v = B.sink ∨ ∃ ht : v ≠ B.sink, B.out v ht ∈ C.darts) :
    ThreePathFaceLabels.side B C (B.inc v hs) = false := by
  classical
  by_cases ht : v = B.sink
  · rw [inc, dite_eq_left ht]
    exact ThreePathFaceLabels.side_right_outer B C
      (List.mem_map.mpr ⟨_, List.mem_reverse.mpr (List.get_mem _ _), rfl⟩)
  obtain ⟨_, hb⟩ := hsel.resolve_left ht
  let b := B.out v ht
  have hinc : B.inc v hs = B.map.rot.symm b := by
    simp only [inc, dite_eq_right ht, b]
  have hf : B.map.faceSucc (B.map.edgeInv b) = B.map.rot.symm b := by
    simpa only [B.map.edgeInv_invol] using
      (ThreePathFaceLabels.corner_consecutiveDarts B (B.map.edgeInv b)).1
  rw [hinc, ← hf]
  by_cases ho : B.map.IsOuter (B.map.edgeInv b)
  · rcases (ThreePathFaceLabels.isOuter_iff_mem_outerArcs B _).mp ho with hl | hr
    · exact (((B.map.tail_iff b (B.noMissingDarts b)).mp
        (B.out_spec v ht).2.1) hl.2.1).elim
    · obtain ⟨e, he, heb⟩ := List.mem_map.mp
        ((ThreePathFaceLabels.mem_pathCutRightOuterArc_iff B _).mp hr)
      have heb' : e = b := B.map.edgeInv.injective heb
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_reverse.mp he)
      have hib : B.rightPath.darts.get i = b := hi.trans heb'
      have hip : 0 < i.val := by
        by_contra hn
        have hi0 : i = ⟨0, by
            rw [B.rightPath.darts_length]
            exact B.right_length_pos⟩ := Fin.ext (by change i.val = 0; omega)
        have hstep := B.rightPath.edge_step i
        apply hs
        exact (B.out_spec v ht).1.symm.trans
          ((hib ▸ hstep.2.2.1.symm).trans
            (by simpa only [hi0] using B.rightPath.start_vertex))
      have hir : i.val < r := by simpa only [B.rightPath.darts_length] using i.isLt
      have hsucc := ThreePathFaceLabels.outerFace_rightPath_successor B
        (i.val - 1) (by omega)
      have hei : B.rightPath.darts[i.val - 1 + 1]'(by
          have := i.isLt; omega) = b := by
        have hix : i.val - 1 + 1 = i.val := by omega
        simpa only [hix, List.get_eq_getElem] using hib
      rw [hei] at hsucc
      rw [hsucc]
      exact ThreePathFaceLabels.side_right_outer B C
        (List.mem_map.mpr ⟨_, List.mem_reverse.mpr (List.getElem_mem _), rfl⟩)
  · rw [ThreePathFaceLabels.side_faceSucc_of_inner B C _ ho]
    exact ThreePathFaceLabels.side_reverse_path_dart B C hb

private theorem incoming_cut_distance_lt_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hs : v ≠ B.source) {b d : D}
    (hb : b ∈ C.darts) (hbv : dartHeadVertex B.map b = v)
    (hdv : dartTailVertex B.map d = v) (_hdt : ¬ B.map.tail d)
    (hdside : ThreePathFaceLabels.side B C d = true)
    (hiside : ThreePathFaceLabels.side B C (B.inc v hs) = false)
    {a k : ℕ} (_ha : (B.map.rot ^ a) (B.map.edgeInv b) = B.inc v hs)
    (hamin : ∀ j < a, (B.map.rot ^ j) (B.map.edgeInv b) ≠ B.inc v hs)
    (hk : (B.map.rot ^ k) d = B.inc v hs)
    (hkmin : ∀ j < k, (B.map.rot ^ j) d ≠ B.inc v hs)
    (hktail : ∀ j ≤ k, ¬ B.map.tail ((B.map.rot ^ j) d)) : a < k := by
  classical
  have hhit : ∃ j, 0 < j ∧ j ≤ k ∧ (B.map.rot ^ j) d = B.map.edgeInv b := by
    by_contra hn
    have havoid : ∀ j, 0 < j → j ≤ k →
        (B.map.rot ^ j) d ≠ B.map.edgeInv b := by
      intro j hj hjk he
      exact hn ⟨j, hj, hjk, he⟩
    have hseq : ∀ j, j ≤ k →
        ThreePathFaceLabels.side B C ((B.map.rot ^ j) d) = true := by
      intro j
      induction j with
      | zero => intro _; exact hdside
      | succ j ih =>
          intro hj
          let q := (B.map.rot ^ j) d
          have hnot : B.map.edgeInv (B.map.rot q) ∉ C.darts := by
            intro hm
            have he := ThreePathFaceLabels.simplePath_dart_eq_of_endpoint_eq C hm hb
              (.inr (by
                simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol,
                  q, pow_succ', Equiv.Perm.mul_apply] using
                  ((rotation_vertex_three_path B.map d (j + 1)).trans hdv).trans hbv.symm))
            apply havoid (j + 1) (by omega) hj
            simpa only [q, pow_succ', Equiv.Perm.mul_apply,
              B.map.edgeInv_invol] using congrArg B.map.edgeInv he
          have he := B.side_rot_incoming_off_cut_three_path C hs q
            ((rotation_vertex_three_path B.map d j).trans hdv)
            (hktail j (by omega)) (hkmin j (by omega))
            (by simpa only [q, pow_succ', Equiv.Perm.mul_apply] using hktail (j + 1) hj)
            hnot
          simpa only [q, pow_succ', Equiv.Perm.mul_apply] using he.trans (ih (by omega))
    have he := hseq k le_rfl
    rw [hk, hiside] at he
    exact Bool.false_ne_true he
  obtain ⟨j, hjpos, hjk, hj⟩ := hhit
  have hreach : (B.map.rot ^ (k - j)) (B.map.edgeInv b) = B.inc v hs := by
    rw [← hj, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjk]
    exact hk
  have hale : a ≤ k - j := by
    by_contra hn
    exact hamin (k - j) (by omega) hreach
  omega

/-- Two cuts cannot approach a common outgoing-selected corner from
mutually left incoming darts. This includes a common sink corner. -/
theorem not_mutually_left_at_selected_merge_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n m : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    (E : SimpleDirectedDartPath B.map B.source B.sink m)
    {v : MapVertex B.map} (hs : v ≠ B.source) {b c : D}
    (hb : b ∈ C.darts) (hc : c ∈ E.darts)
    (hbv : dartHeadVertex B.map b = v) (hcv : dartHeadVertex B.map c = v)
    (hC : v = B.sink ∨ ∃ ht : v ≠ B.sink, B.out v ht ∈ C.darts)
    (hE : v = B.sink ∨ ∃ ht : v ≠ B.sink, B.out v ht ∈ E.darts)
    (hleftC : ThreePathFaceLabels.side B C (B.map.edgeInv c) = true)
    (hleftE : ThreePathFaceLabels.side B E (B.map.edgeInv b) = true) : False := by
  obtain ⟨a, ha, hamin, hatail⟩ :=
    B.incoming_counterclockwise_interval_three_path v hs (B.map.edgeInv b) hbv
      ((B.map.tail_iff b (B.noMissingDarts b)).mp
        (ThreePathFaceLabels.simplePath_tail_of_mem C hb))
  obtain ⟨k, hk, hkmin, hktail⟩ :=
    B.incoming_counterclockwise_interval_three_path v hs (B.map.edgeInv c) hcv
      ((B.map.tail_iff c (B.noMissingDarts c)).mp
        (ThreePathFaceLabels.simplePath_tail_of_mem E hc))
  have hak := B.incoming_cut_distance_lt_three_path C hs hb hbv hcv
    ((B.map.tail_iff c (B.noMissingDarts c)).mp
      (ThreePathFaceLabels.simplePath_tail_of_mem E hc))
    hleftC (B.side_inc_at_out_cut_three_path C hs hC) ha hamin hk hkmin hktail
  have hka := B.incoming_cut_distance_lt_three_path E hs hc hcv hbv
    ((B.map.tail_iff b (B.noMissingDarts b)).mp
      (ThreePathFaceLabels.simplePath_tail_of_mem C hb))
    hleftE (B.side_inc_at_out_cut_three_path E hs hE) hk hkmin ha hamin hatail
  omega

private theorem path_start_reaches_three_path {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n)
    {z : MapVertex M} (hz : z ∈ P.vertices) :
    Relation.ReflTransGen M.directedStep x z := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
  have h := P.reaches_between_indices_three_path
    ⟨0, by rw [P.vertices_length]; omega⟩ i (by change 0 ≤ i.val; omega)
  simpa only [P.start_vertex, hi] using h

private theorem path_reaches_end_three_path {M : DirectedMapWithMissing D}
    {x y : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M x y n)
    {z : MapVertex M} (hz : z ∈ P.vertices) :
    Relation.ReflTransGen M.directedStep z y := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
  have h := P.reaches_between_indices_three_path i
    ⟨n, by rw [P.vertices_length]; omega⟩
    (by have := i.isLt; have := P.vertices_length; change i.val ≤ n; omega)
  simpa only [P.end_vertex, hi] using h

private theorem reaches_antisymm_three_path {M : DirectedMapWithMissing D}
    (ha : M.IsAcyclic) {x y : MapVertex M}
    (hxy : Relation.ReflTransGen M.directedStep x y)
    (hyx : Relation.ReflTransGen M.directedStep y x) : x = y := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy with he | ht
  · exact he.symm
  · exact (ha x (ht.trans_left hyx)).elim

private theorem mem_append_vertices_three_path {M : DirectedMapWithMissing D}
    (ha : M.IsAcyclic) {s v t : MapVertex M} {a b : ℕ}
    (P : SimpleDirectedDartPath M s v a) (Q : SimpleDirectedDartPath M v t b)
    (z : MapVertex M) :
    z ∈ (P.appendAcyclic M ha Q).vertices ↔ z ∈ P.vertices ∨ z ∈ Q.vertices := by
  change z ∈ P.vertices.take a ++ Q.vertices ↔ _
  rw [List.mem_append]
  constructor
  · exact Or.imp List.mem_of_mem_take id
  · rintro (hP | hQ)
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
      by_cases hia : i.val < a
      · exact .inl (List.mem_iff_get.mpr
          ⟨⟨i.val, by simp only [List.length_take, P.vertices_length]; omega⟩,
            by simpa only [List.get_eq_getElem, List.getElem_take] using hi⟩)
      · have he : i = ⟨a, by rw [P.vertices_length]; omega⟩ :=
          Fin.ext (by have := i.isLt; have := P.vertices_length; change i.val = a; omega)
        have hz : z = v := hi.symm.trans (by rw [he]; exact P.end_vertex)
        exact .inr (hz ▸ Q.start_mem_vertices_three_path)
    · exact .inr hQ

private theorem append_join_vertex_three_path {M : DirectedMapWithMissing D}
    (ha : M.IsAcyclic) {s v t : MapVertex M} {a b : ℕ}
    (P : SimpleDirectedDartPath M s v a) (Q : SimpleDirectedDartPath M v t b) :
    (P.appendAcyclic M ha Q).vertices.get
      ⟨a, by rw [(P.appendAcyclic M ha Q).vertices_length]; omega⟩ = v := by
  have hv : (P.appendAcyclic M ha Q).vertices = P.vertices.take a ++ Q.vertices := rfl
  simp only [List.get_eq_getElem, hv]
  have hlen : (P.vertices.take a).length = a := by
    simp only [List.length_take, P.vertices_length, Nat.min_eq_left (by omega : a ≤ a + 1)]
  rw [List.getElem_append_right (by omega)]
  simpa only [hlen, Nat.sub_self, List.get_eq_getElem] using Q.start_vertex

private theorem append_selected_suffix_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x : MapVertex B.map} {a b : ℕ}
    (A : SimpleDirectedDartPath B.map B.source x a)
    (P : SimpleDirectedDartPath B.map x B.sink b) (hP : B.Out P)
    (j : Fin (A.appendAcyclic B.map B.acyclic P).darts.length) (hj : a ≤ j.val) :
    ∃ ht : dartTailVertex B.map ((A.appendAcyclic B.map B.acyclic P).darts.get j) ≠ B.sink,
      (A.appendAcyclic B.map B.acyclic P).darts.get j = B.out _ ht := by
  have hlen := j.isLt
  simp only [SimpleDirectedDartPath.appendAcyclic_darts, List.length_append,
    A.darts_length, P.darts_length] at hlen
  have he : (A.appendAcyclic B.map B.acyclic P).darts.get j =
      P.darts.get ⟨j.val - a, by rw [P.darts_length]; omega⟩ := by
    have hh : (A.darts ++ P.darts)[j.val]'(by
        simp only [List.length_append, A.darts_length, P.darts_length]; omega) =
        P.darts[j.val - a]'(by rw [P.darts_length]; omega) := by
      rw [List.getElem_append_right (by rw [A.darts_length]; exact hj)]
      simp only [A.darts_length]
    exact hh
  rw [he]
  exact hP _

private theorem append_selected_prefix_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {y : MapVertex B.map} {a b : ℕ}
    (Q : SimpleDirectedDartPath B.map B.source y a)
    (S : SimpleDirectedDartPath B.map y B.sink b) (hQ : B.In Q)
    (j : Fin (Q.appendAcyclic B.map B.acyclic S).darts.length) (hj : j.val < a) :
    ∃ hs : dartHeadVertex B.map ((Q.appendAcyclic B.map B.acyclic S).darts.get j) ≠ B.source,
      B.map.edgeInv ((Q.appendAcyclic B.map B.acyclic S).darts.get j) = B.inc _ hs := by
  have he : (Q.appendAcyclic B.map B.acyclic S).darts.get j =
      Q.darts.get ⟨j.val, by rw [Q.darts_length]; exact hj⟩ := by
    have hh : (Q.darts ++ S.darts)[j.val]'(by
        simp only [List.length_append, Q.darts_length, S.darts_length]; omega) =
        Q.darts[j.val]'(by rw [Q.darts_length]; exact hj) :=
      List.getElem_append_left (by rw [Q.darts_length]; exact hj)
    exact hh
  rw [he]
  exact hQ _

private theorem out_mem_of_vertex_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x v : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x B.sink n) (hP : B.Out P)
    (hv : v ∈ P.vertices) (ht : v ≠ B.sink) : B.out v ht ∈ P.darts := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hin : i.val < n := by
    by_contra hn
    have he : i = ⟨n, by rw [P.vertices_length]; omega⟩ :=
      Fin.ext (by have := i.isLt; have := P.vertices_length; change i.val = n; omega)
    exact ht (hi.symm.trans (by rw [he]; exact P.end_vertex))
  let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hin⟩
  have hbv : dartTailVertex B.map (P.darts.get j) = v :=
    (P.edge_step j).2.2.1.symm.trans
      ((congrArg P.vertices.get (Fin.ext rfl)).trans hi)
  obtain ⟨_, he⟩ := hP j
  have he' : P.darts.get j = B.out v ht := by simpa only [hbv] using he
  exact he' ▸ List.get_mem P.darts j

private theorem offPathSide_along_path_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n k : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {x y : MapVertex B.map} (P : SimpleDirectedDartPath B.map x y k)
    (i : Fin P.vertices.length)
    (hoff : ∀ j : Fin P.vertices.length, j.val ≤ i.val → P.vertices.get j ∉ C.vertices)
    (hx : x ∉ C.vertices)
    (hside : ThreePathFaceLabels.offPathSide B C ⟨x, hx⟩ = true) :
    ThreePathFaceLabels.offPathSide B C ⟨P.vertices.get i, hoff i le_rfl⟩ = true := by
  suffices h : ∀ a (i : Fin P.vertices.length), i.val = a →
      ∀ hoff : ∀ j : Fin P.vertices.length, j.val ≤ i.val → P.vertices.get j ∉ C.vertices,
      ThreePathFaceLabels.offPathSide B C ⟨P.vertices.get i, hoff i le_rfl⟩ = true from
    h i.val i rfl hoff
  clear i hoff
  intro a
  induction a with
  | zero =>
      intro i hi hoff
      have hi0 : i = ⟨0, by rw [P.vertices_length]; omega⟩ := Fin.ext hi
      simpa only [hi0, P.start_vertex] using hside
  | succ a ih =>
      intro i hi hoff
      let j : Fin P.vertices.length := ⟨a, by have := i.isLt; omega⟩
      have hp := ih j rfl (fun q hq => hoff q (by dsimp only [j] at hq; omega))
      let d : Fin P.darts.length := ⟨a, by
        have := i.isLt
        have := P.vertices_length
        rw [P.darts_length]
        omega⟩
      have hs := P.edge_step d
      have hstep : B.map.directedStep (P.vertices.get j) (P.vertices.get i) :=
        ⟨P.darts.get d, hs.1, hs.2.1,
          hs.2.2.1.symm.trans (congrArg P.vertices.get (Fin.ext rfl)),
          hs.2.2.2.symm.trans (congrArg P.vertices.get (Fin.ext (by dsimp only [d]; omega)))⟩
      exact (ThreePathFaceLabels.offPathSide_eq_of_directedStep B C
        ⟨P.vertices.get j, hoff j (by dsimp only [j]; omega)⟩
        ⟨P.vertices.get i, hoff i le_rfl⟩ hstep).symm.trans hp

/-- An outgoing-selected path from `x` and an incoming-selected path to
`y` meet whenever a directed connector from `x` to `y` exists. The connector
need not follow a selector. Helper toward Definition 3.13 -/
theorem out_in_intersect_of_directed_path
    (B : BipolarMapWithBoundaryBase D ℓ r)
    {x y : MapVertex B.map} {n m k : ℕ}
    (P : SimpleDirectedDartPath B.map x B.sink n)
    (Q : SimpleDirectedDartPath B.map B.source y m)
    (R : SimpleDirectedDartPath B.map x y k)
    (hP : B.Out P) (hQ : B.In Q) :
    ∃ z, z ∈ P.vertices ∧ z ∈ Q.vertices := by
  classical
  by_contra hn
  have hdis : ∀ z, z ∈ P.vertices → z ∉ Q.vertices :=
    fun z hp hq => hn ⟨z, hp, hq⟩
  have hne : x ≠ y := by
    intro he
    exact hdis x P.start_mem_vertices_three_path (he ▸ Q.end_mem_vertices_three_path)
  have hxy := path_reaches_end_three_path R R.start_mem_vertices_three_path
  let A := (B.rightmostInPath x).2
  let S := (B.rightmostOutPath y).2
  have hS : B.Out S := B.rightmostOutPath_out y
  have hSA : ∀ z, z ∈ S.vertices → z ∉ A.vertices := by
    intro z hzS hzA
    exact hne (reaches_antisymm_three_path B.acyclic hxy
      ((path_start_reaches_three_path S hzS).trans (path_reaches_end_three_path A hzA)))
  have hxS : x ∉ S.vertices := by
    intro hx
    exact hne (reaches_antisymm_three_path B.acyclic hxy
      (path_start_reaches_three_path S hx))
  let C := A.appendAcyclic B.map B.acyclic P
  let E := Q.appendAcyclic B.map B.acyclic S
  have hCmem (z) : z ∈ C.vertices ↔ z ∈ A.vertices ∨ z ∈ P.vertices :=
    mem_append_vertices_three_path B.acyclic A P z
  have hEmem (z) : z ∈ E.vertices ↔ z ∈ Q.vertices ∨ z ∈ S.vertices :=
    mem_append_vertices_three_path B.acyclic Q S z
  have hxE : x ∉ E.vertices := fun hx => (hEmem x).mp hx |>.elim
    (hdis x P.start_mem_vertices_three_path) hxS
  let ic : Fin C.vertices.length := ⟨(B.rightmostInPath x).1, by
    rw [C.vertices_length]
    omega⟩
  let ie : Fin E.vertices.length := ⟨m, by rw [E.vertices_length]; omega⟩
  have hic : C.vertices.get ic = x := append_join_vertex_three_path B.acyclic A P
  have hie : E.vertices.get ie = y := append_join_vertex_three_path B.acyclic Q S
  have hxside : ThreePathFaceLabels.offPathSide B E ⟨x, hxE⟩ = true :=
    B.offPathSide_of_reaches_selected_prefix_three_path E ie
      (fun j hj => B.append_selected_prefix_three_path Q S hQ j hj)
      (by rw [hie]; exact hxy) hxE
  obtain ⟨⟨i, j⟩, ⟨hij, hfirstP, hfirstS⟩, _⟩ :=
    SimpleDirectedDartPath.exists_unique_first_common_pair_three_path B.acyclic P S
      ⟨B.sink, P.end_mem_vertices_three_path, S.end_mem_vertices_three_path⟩
  have hip : 0 < i.val := by
    by_contra hi
    have hi0 : i = ⟨0, by rw [P.vertices_length]; omega⟩ :=
      Fin.ext (by change i.val = 0; omega)
    exact hxS (by rw [← P.start_vertex, ← hi0, hij]; exact List.get_mem _ _)
  have hjp : 0 < j.val := by
    by_contra hj
    have hj0 : j = ⟨0, by rw [S.vertices_length]; omega⟩ :=
      Fin.ext (by change j.val = 0; omega)
    have hyP : y ∈ P.vertices := by
      rw [← S.start_vertex, ← hj0, ← hij]
      exact List.get_mem _ _
    exact hdis y hyP Q.end_mem_vertices_three_path
  have hPoff : ∀ t : Fin P.vertices.length, t.val < i.val → P.vertices.get t ∉ E.vertices := by
    intro t ht he
    exact ((hEmem _).mp he).elim
      (hdis _ (List.get_mem _ _)) (hfirstP t ht)
  have hSoff : ∀ t : Fin S.vertices.length, t.val < j.val → S.vertices.get t ∉ C.vertices := by
    intro t ht hc
    exact ((hCmem _).mp hc).elim
      (hSA _ (List.get_mem _ _)) (hfirstS t ht)
  let ip : Fin P.vertices.length := ⟨i.val - 1, by have := i.isLt; omega⟩
  let jp : Fin S.vertices.length := ⟨j.val - 1, by have := j.isLt; omega⟩
  let ib : Fin P.darts.length := ⟨i.val - 1, by
    have := i.isLt
    have := P.vertices_length
    rw [P.darts_length]
    omega⟩
  let jb : Fin S.darts.length := ⟨j.val - 1, by
    have := j.isLt
    have := S.vertices_length
    rw [S.darts_length]
    omega⟩
  let b := P.darts.get ib
  let c := S.darts.get jb
  have hbP : b ∈ P.darts := List.get_mem _ _
  have hcS : c ∈ S.darts := List.get_mem _ _
  have hbv : dartHeadVertex B.map b = P.vertices.get i :=
    (P.edge_step ib).2.2.2.symm.trans
      (congrArg P.vertices.get (Fin.ext (by dsimp only [ib]; omega)))
  have hcv : dartHeadVertex B.map c = P.vertices.get i :=
    ((S.edge_step jb).2.2.2.symm.trans
      (congrArg S.vertices.get (Fin.ext (by dsimp only [jb]; omega)))).trans hij.symm
  have hbt : dartTailVertex B.map b = P.vertices.get ip :=
    (P.edge_step ib).2.2.1.symm.trans (congrArg P.vertices.get (Fin.ext rfl))
  have hct : dartTailVertex B.map c = S.vertices.get jp :=
    (S.edge_step jb).2.2.1.symm.trans (congrArg S.vertices.get (Fin.ext rfl))
  have hipoff := hPoff ip (by dsimp only [ip]; omega)
  have hjpoff := hSoff jp (by dsimp only [jp]; omega)
  have hbside : ThreePathFaceLabels.side B E (B.map.edgeInv b) = true := by
    have hp := B.offPathSide_along_path_three_path E P ip
      (fun t ht => hPoff t (by dsimp only [ip] at ht; omega)) hxE hxside
    rw [ThreePathFaceLabels.offPathSide_eq B E ⟨P.vertices.get ip, hipoff⟩ b hbt] at hp
    exact (ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B E b
      (.inl (by rw [hbt]; exact hipoff))).trans hp
  have hcside : ThreePathFaceLabels.side B C (B.map.edgeInv c) = true := by
    have hr : Relation.ReflTransGen B.map.directedStep
        (C.vertices.get ic) (S.vertices.get jp) := by
      rw [hic]
      exact hxy.trans (path_start_reaches_three_path S (List.get_mem _ _))
    have hp := B.offPathSide_of_reaches_selected_suffix_three_path C ic
      (fun t ht => B.append_selected_suffix_three_path A P hP t ht) hr hjpoff
    rw [ThreePathFaceLabels.offPathSide_eq B C ⟨S.vertices.get jp, hjpoff⟩ c hct] at hp
    exact (ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B C c
      (.inl (by rw [hct]; exact hjpoff))).trans hp
  have hs : P.vertices.get i ≠ B.source := by
    intro he
    exact B.isSource ⟨dartTailVertex B.map b, b, B.noMissingDarts b,
      ThreePathFaceLabels.simplePath_tail_of_mem P hbP, rfl, hbv.trans he⟩
  have hbC : b ∈ C.darts := List.mem_append.mpr (.inr hbP)
  have hcE : c ∈ E.darts := List.mem_append.mpr (.inr hcS)
  have hCsel : P.vertices.get i = B.sink ∨
      ∃ ht : P.vertices.get i ≠ B.sink, B.out _ ht ∈ C.darts := by
    by_cases ht : P.vertices.get i = B.sink
    · exact .inl ht
    · exact .inr ⟨ht, List.mem_append.mpr (.inr
        (B.out_mem_of_vertex_three_path P hP (List.get_mem _ _) ht))⟩
  have hEsel : P.vertices.get i = B.sink ∨
      ∃ ht : P.vertices.get i ≠ B.sink, B.out _ ht ∈ E.darts := by
    by_cases ht : P.vertices.get i = B.sink
    · exact .inl ht
    · exact .inr ⟨ht, List.mem_append.mpr (.inr
        (B.out_mem_of_vertex_three_path S hS (hij ▸ List.get_mem _ _) ht))⟩
  exact B.not_mutually_left_at_selected_merge_three_path C E hs hbC hcE hbv hcv
    hCsel hEsel hcside hbside

private theorem exists_path_of_reaches_three_path
    {M : DirectedMapWithMissing D} (ha : M.IsAcyclic) {x y : MapVertex M}
    (hxy : Relation.ReflTransGen M.directedStep x y) :
    ∃ n, Nonempty (SimpleDirectedDartPath M x y n) := by
  induction hxy with
  | refl =>
      exact ⟨0, ⟨{
        darts := []
        vertices := [x]
        darts_length := rfl
        vertices_length := rfl
        vertices_nodup := List.nodup_singleton x
        start_vertex := rfl
        end_vertex := rfl
        edge_step := fun i => Fin.elim0 i
      }⟩⟩
  | @tail y z _ hyz ih =>
      obtain ⟨n, ⟨P⟩⟩ := ih
      have hyzne : y ≠ z := by
        intro he
        exact ha y (Relation.TransGen.single (he ▸ hyz))
      obtain ⟨d, hm, ht, hdy, hdz⟩ := hyz
      let Q : SimpleDirectedDartPath M y z 1 := {
        darts := [d]
        vertices := [y, z]
        darts_length := rfl
        vertices_length := rfl
        vertices_nodup := List.nodup_cons.mpr
          ⟨by simpa only [List.mem_singleton] using hyzne, List.nodup_singleton z⟩
        start_vertex := rfl
        end_vertex := rfl
        edge_step := by
          intro i
          have hi : i = ⟨0, by simp only [List.length_singleton]; omega⟩ :=
            Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
          subst i
          exact ⟨hm, ht, hdy.symm, hdz.symm⟩
      }
      exact ⟨n + 1, ⟨P.appendAcyclic M ha Q⟩⟩

/-- The first meeting of the two canonical rightmost paths exists under
directed-step reachability, including equal endpoints and poles. Helper -/
theorem exists_first_rightmost_meeting
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map}
    (hxy : Relation.ReflTransGen B.map.directedStep x y) :
    ∃ i : Fin (B.rightmostOutPath x).2.vertices.length,
      (B.rightmostOutPath x).2.vertices.get i ∈ (B.rightmostInPath y).2.vertices ∧
        ∀ j : Fin (B.rightmostOutPath x).2.vertices.length, j.val < i.val →
          (B.rightmostOutPath x).2.vertices.get j ∉ (B.rightmostInPath y).2.vertices := by
  obtain ⟨n, ⟨R⟩⟩ := exists_path_of_reaches_three_path B.acyclic hxy
  exact (B.rightmostOutPath x).2.exists_first_common_index (B.rightmostInPath y).2
    (B.out_in_intersect_of_directed_path (B.rightmostOutPath x).2
      (B.rightmostInPath y).2 R (B.rightmostOutPath_out x) (B.rightmostInPath_in y))

/- T1 is proved by `out_in_intersect_of_directed_path` for arbitrary
selector-certified paths and by `exists_first_rightmost_meeting` for the
canonical paths under directed-step reachability. The construction uses
`C = A ++ P` and `E = Q ++ S`, where `A` ends at x and S is outgoing-selected
from y to the sink. Both the suffix and prefix reachability lemmas give the
left label `true`; the prefix sign is not `false`. Disjoint P and Q would
give mutually left incoming darts at the first common vertex of P and S,
contradicting `not_mutually_left_at_selected_merge_three_path`.

T2 remains the construction of `threePathRegion B x y P`,
including the boundary walk

  out.darts.take i ++ inc.darts.drop j ++
    P.darts.reverse.map B.map.edgeInv

where `out.vertices[i] = inc.vertices[j]` is the first meeting along `out`.
One must prove the walk closes and identify its right-hand enclosed
`faceSucc` cycles, including overlaps. No filled-hull identification with
the source picture is claimed by this file.

T3 remains inclusion of all three boundary portions, exclusion of the
marked exterior face, and equality with P's support when P is the rightmost
outgoing segment. T4 remains equivalence (at least one direction) between
edge containment in that region and the dart-local right-leaving rotation
condition. No region, global side characterization, or implication assuming these
proof obligations is installed here. -/

end BipolarMapWithBoundaryBase
end DirectedDistances.PlanarMap
