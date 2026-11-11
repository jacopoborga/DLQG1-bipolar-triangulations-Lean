/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Extremal









public section
namespace DirectedDistances

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V] {a b : V}

/-- A bounded set of natural path lengths is finite, without a finite ambient quiver. -/
theorem pathLengths_finite_of_bddAbove (hb : BddAbove (pathLengths a b)) :
    (pathLengths a b).Finite := by
  obtain ⟨N, hN⟩ := hb
  exact (Set.finite_Iic N).subset (fun _ hn => hN hn)

/-- For natural path lengths, finiteness and boundedness are equivalent. -/
theorem pathLengths_finite_iff_bddAbove :
    (pathLengths a b).Finite ↔ BddAbove (pathLengths a b) :=
  ⟨Set.Finite.bddAbove, pathLengths_finite_of_bddAbove⟩

/-- A reachable bounded path-length set attains its maximum. No global finiteness
or acyclicity hypothesis is required by this generic attainment lemma. -/
theorem exists_isLongest_of_bddAbove (hb : BddAbove (pathLengths a b))
    (hr : Reachable a b) : ∃ p : Path a b, IsLongest p := by
  obtain ⟨p⟩ := hr
  have hne : (pathLengths a b).Nonempty := ⟨p.length, ⟨p, rfl⟩⟩
  have hfin := pathLengths_finite_of_bddAbove hb
  obtain ⟨q, hq⟩ := hne.csSup_mem hfin
  refine ⟨q, fun r => ?_⟩
  exact (le_csSup hb ⟨r, rfl⟩).trans_eq hq.symm

/-- Existence of a genuine longest path is equivalent to reachability and
boundedness of the path-length set, on an arbitrary quiver. -/
theorem exists_isLongest_iff_reachable_bddAbove :
    (∃ p : Path a b, IsLongest p) ↔ Reachable a b ∧ BddAbove (pathLengths a b) := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨⟨p⟩, p.length, ?_⟩
    rintro n ⟨q, rfl⟩
    exact hp q
  · rintro ⟨hr, hb⟩
    exact exists_isLongest_of_bddAbove hb hr

/-- The attained longest natural length is unique, even when several different
arrow-valued paths attain it. This is a well-definedness result, not a choice
of a leftmost geodesic. -/
theorem existsUnique_longest_length_of_bddAbove (hb : BddAbove (pathLengths a b))
    (hr : Reachable a b) :
    ∃! n : ℕ, (∃ p : Path a b, p.length = n) ∧ ∀ q : Path a b, q.length ≤ n := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove hb hr
  refine ⟨p.length, ⟨⟨p, rfl⟩, hp⟩, ?_⟩
  rintro n ⟨⟨q, hq⟩, hn⟩
  apply le_antisymm
  · rw [← hq]
    exact hp q
  · exact hn p

/-- A finite vertex set containing every relevant path bounds all relevant
lengths in an acyclic quiver. It may lie inside an infinite ambient map. -/
theorem pathLengths_bddAbove_of_finite_vertex_confinement (ha : acyclic V)
    (s : Set V) (hs : s.Finite)
    (hc : ∀ p : Path a b, ∀ x ∈ p.vertices, x ∈ s) :
    BddAbove (pathLengths a b) := by
  classical
  refine ⟨hs.toFinset.card, ?_⟩
  rintro n ⟨p, rfl⟩
  have hsub : p.vertices.toFinset ⊆ hs.toFinset := by
    intro x hx
    exact hs.mem_toFinset.2 (hc p x (List.mem_toFinset.1 hx))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (vertices_nodup_of_acyclic ha p),
    Path.vertices_length] at hcard
  exact Nat.le_of_succ_le hcard

/-- Finite vertex confinement supplies an actual longest path on an infinite
ambient carrier. The confinement premise is exposed and must be proved in each
source application; it is not a substitute theorem for `lem-geo-exist`. -/
theorem exists_isLongest_of_finite_vertex_confinement (ha : acyclic V)
    (s : Set V) (hs : s.Finite)
    (hc : ∀ p : Path a b, ∀ x ∈ p.vertices, x ∈ s) (hr : Reachable a b) :
    ∃ p : Path a b, IsLongest p :=
  exists_isLongest_of_bddAbove
    (pathLengths_bddAbove_of_finite_vertex_confinement ha s hs hc) hr

end DirectedDistances
