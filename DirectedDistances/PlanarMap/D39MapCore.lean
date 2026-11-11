/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CombinatorialMap
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMap
public import Mathlib.Data.Set.Countable

/-! Supporting lemmas for paper labels `def-bs-topology` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. A locally finite directed map without a distinguished root dart. The
local finiteness counts dart incidences, including missing and parallel edges. -/
structure D39MapCore where
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper -/
  D : Type
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Cyclic order around each vertex. Source: -/
  rot : Equiv.Perm D
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Opposite dart on the same geometric edge. Source: -/
  edgeInv : Equiv.Perm D
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Edge reversal is an involution. Source: -/
  edgeInv_invol : ∀ d, edgeInv (edgeInv d) = d
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. No edge has a dart fixed by reversal. Source: -/
  edgeInv_ne : ∀ d, edgeInv d ≠ d
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Tag for darts of missing geometric edges. Source: -/
  missing : D → Prop
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Missingness is constant across an edge. Source: -/
  missing_edgeInv : ∀ d, missing d ↔ missing (edgeInv d)
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Tail dart tag for present oriented edges. Source: -/
  tail : D → Prop
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Exactly one dart is the tail of each present edge. Source: -/
  tail_iff : ∀ d, ¬ missing d → (tail d ↔ ¬ tail (edgeInv d))
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Missing edges have no orientation. Source: -/
  tail_missing : ∀ d, missing d → ¬ tail d
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. A dart marking the outer face. Source: -/
  outer : D
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Every missing edge is incident to the outer face. Source: -/
  missing_outer : ∀ d, missing d →
    Equiv.Perm.SameCycle (rot.symm * edgeInv) outer d ∨
      Equiv.Perm.SameCycle (rot.symm * edgeInv) outer (edgeInv d)
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Every vertex has finitely many dart incidences. Source: -/
  locallyFinite : ∀ d, {e : D | rot.SameCycle d e}.Finite
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. The geometric map is connected using all edges. Source: -/
  connected : ∀ d e, Relation.ReflTransGen
    (fun x y : D => y = rot x ∨ y = rot.symm x ∨
      y = edgeInv x ∨ y = edgeInv.symm x) d e
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Present-edge orientation is acyclic. Source: -/
  acyclic : ∀ v : RootedLocallyFiniteVertex D rot,
    ¬ Relation.TransGen (rootedLocallyFiniteDirectedStep rot edgeInv missing tail) v v

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. Finite dart layers reached from the outer marker by the four -/
private noncomputable def d39DartLayer (M : D39MapCore) : ℕ → Finset M.D
  | 0 => by
      classical
      exact {M.outer}
  | n + 1 => by
      classical
      exact d39DartLayer M n ∪
        ((d39DartLayer M n).image M.rot ∪
          ((d39DartLayer M n).image M.rot.symm ∪
            ((d39DartLayer M n).image M.edgeInv ∪
              (d39DartLayer M n).image M.edgeInv.symm)))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. One connectedness step advances to a finite dart layer. Source: -/
private theorem d39DartLayer_step (M : D39MapCore) (n : ℕ) {x y : M.D}
    (hx : x ∈ d39DartLayer M n)
    (hxy : y = M.rot x ∨ y = M.rot.symm x ∨
      y = M.edgeInv x ∨ y = M.edgeInv.symm x) :
    y ∈ d39DartLayer M (n + 1) := by
  classical
  simp only [d39DartLayer, Finset.mem_union]
  rcases hxy with h | h | h | h
  · subst y
    exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  · subst y
    exact Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
  · subst y
    exact Or.inr
      (Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩))))
  · subst y
    exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. Connectedness and finite dart layers imply countability of the dart
carrier. The layers use geometric edges, including missing edges. Source: -/
theorem D39MapCore.countable_darts (M : D39MapCore) : Countable M.D := by
  classical
  have hcover : ∀ d : M.D, d ∈ ⋃ n, (d39DartLayer M n : Set M.D) := by
    intro d
    have hpath := M.connected M.outer d
    induction hpath with
    | refl =>
        exact Set.mem_iUnion.mpr ⟨0, by simp [d39DartLayer]⟩
    | @tail x y hpath hstep ih =>
        rcases Set.mem_iUnion.mp ih with ⟨n, hn⟩
        refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
        exact d39DartLayer_step M n (by simpa using hn) hstep
  have hcount : (⋃ n, (d39DartLayer M n : Set M.D)).Countable :=
    Set.countable_iUnion fun n => (d39DartLayer M n).countable_toSet
  apply Set.countable_univ_iff.mp
  apply hcount.mono
  intro d _
  exact hcover d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. Countability is derived from connectedness and local finiteness rather -/
instance (M : D39MapCore) : Countable M.D := M.countable_darts

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. An ordered root mark is either a present directed tail dart or a
missing unoriented dart. The marked dart's first endpoint is its rotation -/
inductive D39RootMark (M : D39MapCore) where
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. A present root dart is marked in its directed tail direction. -/
  | present (d : M.D) (hp : ¬ M.missing d) (ht : M.tail d)
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. A missing root dart has no orientation. Source: -/
  | missing (d : M.D) (hm : M.missing d)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. The dart carrying the ordered root mark. Source: -/
@[expose] def D39RootMark.dart {M : D39MapCore} (m : D39RootMark M) : M.D :=
  match m with
  | .present d _ _ => d
  | .missing d _ => d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. The first endpoint of the ordered mark is its rotation-orbit vertex. -/
@[expose] def D39RootMark.firstVertex {M : D39MapCore} (m : D39RootMark M) :
    RootedLocallyFiniteVertex M.D M.rot :=
  rootedLocallyFiniteVertexClass M.rot m.dart



structure D39RootedMap where
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. Marker-free map data. Source: -/
  core : D39MapCore
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
  result. The ordered root mark on the core. Source: -/
  rootMark : D39RootMark core

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. Forget the old root and mark its missing frame dart as the local topology root. -/
@[expose] def RootedLocallyFiniteMap.toD39RootedMap
    (M : RootedLocallyFiniteMap) : D39RootedMap := by
  let c : D39MapCore :=
    { D := M.D
      rot := M.rot
      edgeInv := M.edgeInv
      edgeInv_invol := M.edgeInv_invol
      edgeInv_ne := M.edgeInv_ne
      missing := M.missing
      missing_edgeInv := M.missing_edgeInv
      tail := M.tail
      tail_iff := M.tail_iff
      tail_missing := M.tail_missing
      outer := M.outer
      missing_outer := M.missing_outer
      locallyFinite := M.locallyFinite
      connected := M.connected
      acyclic := M.acyclic }
  exact ⟨c, .missing M.frameEdgeDart M.frameEdge_missing⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper
result. The converted mark starts at the existing root vertex. Source: -/
theorem RootedLocallyFiniteMap.toD39RootedMap_firstVertex
    (M : RootedLocallyFiniteMap) :
    M.toD39RootedMap.rootMark.firstVertex =
      rootedLocallyFiniteVertexClass M.rot M.rootDart := by
  change rootedLocallyFiniteVertexClass M.rot M.frameEdgeDart = _
  exact (Quotient.sound M.frameEdge_at_root).symm

end DirectedDistances.PlanarMap
end
