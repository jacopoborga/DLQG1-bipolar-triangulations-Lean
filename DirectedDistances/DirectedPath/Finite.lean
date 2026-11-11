/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Distance
public import DirectedDistances.DirectedPath.Acyclic
public import Mathlib.Algebra.Order.Monoid.WithTop

/-! # Longest distance on finite acyclic quivers

This is finite-domain infrastructure supporting manuscript label `def-ldp`.
`finiteLdp` requires a finite vertex type and a proof of literal acyclicity; it
is not a definition for arbitrary infinite manuscript maps. Finiteness of arrow
types is unnecessary: parallel arrows retain their identities, while only the
set of their path lengths needs to be finite. -/

@[expose] public section
namespace DirectedDistances

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V] {a b c : V}

/-- All attainable natural directed-path lengths between two endpoints. -/
def pathLengths (a b : V) : Set ℕ := Set.range (fun p : Path a b => p.length)

/-- On finitely many acyclic vertices the set of attainable lengths is finite,
even when there are infinitely many parallel arrows. -/
theorem pathLengths_finite [Fintype V] (h : acyclic V) (a b : V) :
    (pathLengths a b).Finite := by
  apply (Set.finite_Iio (Fintype.card V)).subset
  rintro n ⟨p, rfl⟩
  exact length_lt_card_of_acyclic h p

/-- Finite acyclic LDP is the supremum of the finite set of attained path lengths,
with bottom (`−∞`) for unreachable endpoints. The proof argument restricts its
public domain to acyclic quivers; no unbounded-set default is used on that domain. -/
noncomputable def finiteLdp [Fintype V] (_h : acyclic V) (a b : V) : WithBot ℕ :=
  sSup ((fun n : ℕ => (n : WithBot ℕ)) '' pathLengths a b)

variable [Fintype V]

/-- The supremum defining finite LDP is always over a finite set. -/
theorem finiteLdp_lengths_finite (h : acyclic V) (a b : V) :
    ((fun n : ℕ => (n : WithBot ℕ)) '' pathLengths a b).Finite :=
  (pathLengths_finite h a b).image _

/-- Every path is bounded above by the finite acyclic longest distance. -/
theorem length_le_finiteLdp (h : acyclic V) (p : Path a b) :
    (p.length : WithBot ℕ) ≤ finiteLdp h a b :=
  le_csSup (finiteLdp_lengths_finite h a b).bddAbove ⟨p.length, ⟨p, rfl⟩, rfl⟩

/-- Longest distance is bounded above by any bound on all directed-path lengths. -/
theorem finiteLdp_le (h : acyclic V) {n : ℕ} (hn : ∀ p : Path a b, p.length ≤ n) :
    finiteLdp h a b ≤ (n : WithBot ℕ) := by
  apply csSup_le'
  rintro _ ⟨m, ⟨p, rfl⟩, rfl⟩
  exact WithBot.coe_le_coe.mpr (hn p)

/-- A reachable finite acyclic longest distance is attained by an actual edge path. -/
theorem exists_length_eq_finiteLdp (h : acyclic V) (hr : Reachable a b) :
    ∃ p : Path a b, (p.length : WithBot ℕ) = finiteLdp h a b := by
  have hne : ((fun n : ℕ => (n : WithBot ℕ)) '' pathLengths a b).Nonempty := by
    obtain ⟨p⟩ := hr
    exact ⟨p.length, ⟨p.length, ⟨p, rfl⟩, rfl⟩⟩
  obtain ⟨n, ⟨p, rfl⟩, hp⟩ := hne.csSup_mem (finiteLdp_lengths_finite h a b)
  exact ⟨p, hp⟩

/-- Bottom longest distance means exactly that the endpoints are unreachable. -/
@[simp] theorem finiteLdp_eq_bot_iff_not_reachable (h : acyclic V) :
    finiteLdp h a b = ⊥ ↔ ¬ Reachable a b := by
  constructor
  · intro hb hr
    obtain ⟨p, hp⟩ := exists_length_eq_finiteLdp h hr
    exact WithBot.coe_ne_bot (hp.trans hb)
  · intro hn
    have he : pathLengths a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨p, _⟩
      exact hn ⟨p⟩
    simp only [finiteLdp, he, Set.image_empty, csSup_empty]

/-- The empty path is the unique possible closed path in the acyclic domain. -/
@[simp] theorem finiteLdp_self (h : acyclic V) (a : V) : finiteLdp h a a = 0 := by
  apply le_antisymm
  · exact finiteLdp_le h (fun p => Nat.le_of_eq (h a p))
  · exact length_le_finiteLdp h (Path.nil : Path a a)

/-- The finite longest distance obeys the sharp cardinality bound. -/
theorem finiteLdp_le_card_sub_one (h : acyclic V) (a b : V) :
    finiteLdp h a b ≤ ((Fintype.card V - 1 : ℕ) : WithBot ℕ) :=
  finiteLdp_le h (fun p => Nat.le_sub_one_of_lt (length_lt_card_of_acyclic h p))

/-- Reachable composable endpoints satisfy the reverse triangle inequality.
The concatenation is a genuine non-repeating path by
`vertices_comp_nodup_of_acyclic`; its length is additive by Mathlib's `Path.length_comp`. -/
theorem finiteLdp_reverse_triangle (h : acyclic V) (hab : Reachable a b)
    (hbc : Reachable b c) :
    finiteLdp h a b + finiteLdp h b c ≤ finiteLdp h a c := by
  obtain ⟨p, hp⟩ := exists_length_eq_finiteLdp h hab
  obtain ⟨q, hq⟩ := exists_length_eq_finiteLdp h hbc
  calc
    finiteLdp h a b + finiteLdp h b c = ((p.comp q).length : WithBot ℕ) := by
      rw [← hp, ← hq, Path.length_comp]
      rfl
    _ ≤ finiteLdp h a c := length_le_finiteLdp h _

/-- Shortest and longest distances have compatible finite natural values whenever
reachable. This avoids an unjustified comparison of different infinity extensions. -/
theorem exists_sdp_finiteLdp_values (h : acyclic V) (hr : Reachable a b) :
    ∃ m n : ℕ, sdp a b = m ∧ finiteLdp h a b = n ∧ m ≤ n := by
  obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
  obtain ⟨q, hq⟩ := exists_length_eq_finiteLdp h hr
  refine ⟨p.length, q.length, hp.symm, hq.symm, ?_⟩
  have hle := sdp_le_length q
  rw [← hp] at hle
  exact ENat.natCast_le_natCast.mp hle

/-- SDP ≤ LDP after extracting their proved finite values; `toNat` at infinity
is never used to manufacture a comparison. -/
theorem sdp_toNat_le_finiteLdp_unbot (h : acyclic V) (hr : Reachable a b) :
    (sdp a b).toNat ≤ (finiteLdp h a b).unbot
      (fun hb => (finiteLdp_eq_bot_iff_not_reachable h).mp hb hr) := by
  obtain ⟨m, n, hm, hn, hmn⟩ := exists_sdp_finiteLdp_values h hr
  have hu : (finiteLdp h a b).unbot
      (fun hb => (finiteLdp_eq_bot_iff_not_reachable h).mp hb hr) = n :=
    (WithBot.unbot_eq_iff _).mpr hn
  calc
    (sdp a b).toNat = m := by rw [hm]; rfl
    _ ≤ n := hmn
    _ = _ := hu.symm

end DirectedDistances
