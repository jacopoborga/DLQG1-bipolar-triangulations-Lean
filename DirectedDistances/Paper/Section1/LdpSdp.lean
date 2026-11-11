 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.LdpSdpDefinition

/-!
# Definition 1.2 (`def-ldp`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/















public section
namespace DirectedDistances.Paper.Section1

open Quiver

universe u v

 
theorem def_ldp {V : Type u} [Quiver.{v} V] (a b : V) :
    ((¬ Reachable a b ∧ DirectedDistances.ldp a b = ⊥) ∨
      (Reachable a b ∧
        (∃ N : ℕ, ∀ p : Path a b, p.length ≤ N) ∧
        ∃ p : Path a b,
          DirectedDistances.ldp a b = ((p.length : ℕ∞) : WithBot ℕ∞) ∧
            ∀ q : Path a b, q.length ≤ p.length) ∨
      ((∀ N : ℕ, ∃ p : Path a b, N < p.length) ∧ DirectedDistances.ldp a b = ⊤)) ∧
    (DirectedDistances.ldp a b = ⊥ ↔ ¬ Reachable a b) ∧
    (∀ p : Path a b, ((p.length : ℕ∞) : WithBot ℕ∞) ≤ DirectedDistances.ldp a b) ∧
    (∀ x : WithBot ℕ∞,
      ((¬ Reachable a b ∧ x = ⊥) ∨
        (Reachable a b ∧
          (∃ N : ℕ, ∀ p : Path a b, p.length ≤ N) ∧
          ∃ p : Path a b,
            x = ((p.length : ℕ∞) : WithBot ℕ∞) ∧
              ∀ q : Path a b, q.length ≤ p.length) ∨
        ((∀ N : ℕ, ∃ p : Path a b, N < p.length) ∧ x = ⊤)) →
      x = DirectedDistances.ldp a b) ∧
    (DirectedDistances.sdp a b = ⊤ ↔ ¬ Reachable a b) ∧
    (∀ p : Path a b, DirectedDistances.sdp a b ≤ p.length) ∧
    (Reachable a b →
      ∃ p : Path a b,
        DirectedDistances.sdp a b = (p.length : ℕ∞) ∧
          ∀ q : Path a b, (p.length : ℕ∞) ≤ q.length) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_ldp_provider a b
 
 

end DirectedDistances.Paper.Section1
 
