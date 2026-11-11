/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.LongestDistance

/-! Supporting lemmas for paper labels `def-ldp` (see CORRESPONDENCE.md). -/

/- # Isolated proof provider for Definition 1.2 (`def-ldp`)


A directed map is represented by its quiver of oriented (present) edges, with arrows retaining
edge identity, including parallel edges; missing edges are unoriented and are not arrows. Directed
paths are `Quiver.Path`s, including the empty path. `LDP` takes values in `WithBot ℕ∞`, i.e.
`{-∞} ∪ ℕ ∪ {+∞}`, and `SDP` in `ℕ∞`. The characterization covers every case: unreachable pairs
(`LDP = ⊥ = -∞`, `SDP = ⊤ = +∞`), reachable pairs with bounded path lengths (attained maximum),
reachable pairs with unbounded path lengths (`LDP = ⊤`), and the attained SDP minimum. No finiteness
counting remain the coordinator's responsibility. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open Quiver

universe u v



theorem def_ldp_provider {V : Type u} [Quiver.{v} V] (a b : V) :
    ((¬ Reachable a b ∧ ldp a b = ⊥) ∨
      (Reachable a b ∧
        (∃ N : ℕ, ∀ p : Path a b, p.length ≤ N) ∧
        ∃ p : Path a b,
          ldp a b = ((p.length : ℕ∞) : WithBot ℕ∞) ∧
            ∀ q : Path a b, q.length ≤ p.length) ∨
      ((∀ N : ℕ, ∃ p : Path a b, N < p.length) ∧ ldp a b = ⊤)) ∧
    (ldp a b = ⊥ ↔ ¬ Reachable a b) ∧
    (∀ p : Path a b, ((p.length : ℕ∞) : WithBot ℕ∞) ≤ ldp a b) ∧
    (∀ x : WithBot ℕ∞,
      ((¬ Reachable a b ∧ x = ⊥) ∨
        (Reachable a b ∧
          (∃ N : ℕ, ∀ p : Path a b, p.length ≤ N) ∧
          ∃ p : Path a b,
            x = ((p.length : ℕ∞) : WithBot ℕ∞) ∧
              ∀ q : Path a b, q.length ≤ p.length) ∨
        ((∀ N : ℕ, ∃ p : Path a b, N < p.length) ∧ x = ⊤)) →
      x = ldp a b) ∧
    (sdp a b = ⊤ ↔ ¬ Reachable a b) ∧
    (∀ p : Path a b, sdp a b ≤ p.length) ∧
    (Reachable a b →
      ∃ p : Path a b,
        sdp a b = (p.length : ℕ∞) ∧ ∀ q : Path a b, (p.length : ℕ∞) ≤ q.length) :=
  ⟨ldp_trichotomy a b, ldp_eq_bot_iff_not_reachable, length_le_ldp,
    fun _ hx => ldp_eq_of_characterization hx, sdp_eq_top_iff_not_reachable,
    sdp_le_length, exists_sdp_min⟩

end DirectedDistances.PaperProofs.SourceResults
