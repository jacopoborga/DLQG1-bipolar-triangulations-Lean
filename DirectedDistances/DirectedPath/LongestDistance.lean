/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Distance

/-! Supporting lemmas for paper labels `def-ldp` (see CORRESPONDENCE.md). -/

/-! # Longest directed distance

Extended supremum of the lengths of all finite directed paths, including the
unreachable and unbounded cases of manuscript label `def-ldp`. -/

@[expose] public section

namespace DirectedDistances

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V] {a b : V}





@[expose] noncomputable def ldp (a b : V) : WithBot ℕ∞ :=
  ⨆ p : Path a b, (((p.length : ℕ) : ℕ∞) : WithBot ℕ∞)

 
theorem length_le_ldp (p : Path a b) :
    ((p.length : ℕ∞) : WithBot ℕ∞) ≤ ldp a b :=
  le_iSup (fun q : Path a b => (((q.length : ℕ) : ℕ∞) : WithBot ℕ∞)) p

 
theorem ldp_eq_bot_iff_not_reachable : ldp a b = ⊥ ↔ ¬ Reachable a b := by
  constructor
  · intro h hr
    obtain ⟨p⟩ := hr
    have hp := length_le_ldp p
    rw [h] at hp
    exact (not_le_of_gt (WithBot.bot_lt_coe _) hp).elim
  · intro hn
    rw [ldp, iSup_eq_bot]
    intro p
    exact (hn ⟨p⟩).elim




theorem exists_ldp_max_of_bounded (h : Reachable a b)
    (hb : ∃ N : ℕ, ∀ p : Path a b, p.length ≤ N) :
    ∃ p : Path a b,
      ldp a b = ((p.length : ℕ∞) : WithBot ℕ∞) ∧
        ∀ q : Path a b, q.length ≤ p.length := by
  letI : Nonempty (Path a b) := h
  obtain ⟨N, hN⟩ := hb
  have hsup_le : (⨆ q : Path a b, (q.length : ℕ∞)) ≤ (N : ℕ∞) := by
    apply iSup_le
    intro q
    exact WithTop.coe_le_coe.mpr (hN q)
  have hsup_lt : (⨆ q : Path a b, (q.length : ℕ∞)) < ⊤ :=
    hsup_le.trans_lt (WithTop.coe_lt_top N)
  obtain ⟨p, hp⟩ := ENat.exists_eq_iSup_of_lt_top hsup_lt
  have hmax : ∀ q : Path a b, q.length ≤ p.length := by
    intro q
    have hq : (q.length : ℕ∞) ≤ ⨆ r : Path a b, (r.length : ℕ∞) :=
      le_iSup (fun r : Path a b => (r.length : ℕ∞)) q
    rw [← hp] at hq
    exact WithTop.coe_le_coe.mp hq
  refine ⟨p, ?_, ?_⟩
  · apply le_antisymm
    · apply iSup_le
      intro q
      exact WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
        hmax q
    · exact length_le_ldp p
  · intro q
    exact hmax q



theorem ldp_eq_top_of_unbounded
    (hu : ∀ N : ℕ, ∃ p : Path a b, N < p.length) : ldp a b = ⊤ := by
  apply le_antisymm le_top
  cases hldp : ldp a b with
  | bot =>
    obtain ⟨p, _⟩ := hu 0
    have hp := length_le_ldp p
    rw [hldp] at hp
    exact (not_le_of_gt (WithBot.bot_lt_coe _) hp).elim
  | coe x =>
    have hx : (⊤ : ℕ∞) ≤ x := by
      rw [← ENat.iSup_natCast]
      apply iSup_le
      intro N
      obtain ⟨p, hp⟩ := hu N
      have hN :
          ((N : ℕ∞) : WithBot ℕ∞) ≤ (((p.length : ℕ) : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr (Nat.le_of_lt hp)
      have hle := hN.trans (length_le_ldp p)
      rw [hldp] at hle
      exact WithBot.coe_le_coe.mp hle
    exact WithBot.coe_le_coe.mpr hx




theorem ldp_trichotomy (a b : V) :
    (¬ Reachable a b ∧ ldp a b = ⊥) ∨
      (Reachable a b ∧
        (∃ N : ℕ, ∀ p : Path a b, p.length ≤ N) ∧
        ∃ p : Path a b,
          ldp a b = ((p.length : ℕ∞) : WithBot ℕ∞) ∧
            ∀ q : Path a b, q.length ≤ p.length) ∨
      ((∀ N : ℕ, ∃ p : Path a b, N < p.length) ∧ ldp a b = ⊤) := by
  classical
  by_cases hr : Reachable a b
  · by_cases hb : ∃ N : ℕ, ∀ p : Path a b, p.length ≤ N
    · obtain ⟨p, hp, hmax⟩ := exists_ldp_max_of_bounded hr hb
      exact Or.inr (Or.inl ⟨hr, hb, p, hp, hmax⟩)
    · have hu : ∀ N : ℕ, ∃ p : Path a b, N < p.length := by
        intro N
        by_contra hn
        apply hb
        refine ⟨N, ?_⟩
        intro p
        exact Nat.le_of_not_gt (fun hlt => hn ⟨p, hlt⟩)
      exact Or.inr (Or.inr ⟨hu, ldp_eq_top_of_unbounded hu⟩)
  · exact Or.inl ⟨hr, ldp_eq_bot_iff_not_reachable.mpr hr⟩




theorem ldp_eq_of_characterization {x : WithBot ℕ∞}
    (hx : (¬ Reachable a b ∧ x = ⊥) ∨
      (Reachable a b ∧
        (∃ N : ℕ, ∀ p : Path a b, p.length ≤ N) ∧
        ∃ p : Path a b,
          x = ((p.length : ℕ∞) : WithBot ℕ∞) ∧
            ∀ q : Path a b, q.length ≤ p.length) ∨
      ((∀ N : ℕ, ∃ p : Path a b, N < p.length) ∧ x = ⊤)) :
    x = ldp a b := by
  rcases hx with h | h | h
  · exact h.2.trans (ldp_eq_bot_iff_not_reachable.mpr h.1).symm
  · rcases h with ⟨hr, hb, p, hp, hmax⟩
    obtain ⟨q, hq, hqmax⟩ := exists_ldp_max_of_bounded hr hb
    have hlen : p.length = q.length := Nat.le_antisymm (hqmax p) (hmax q)
    calc
      x = ((p.length : ℕ∞) : WithBot ℕ∞) := hp
      _ = ((q.length : ℕ∞) : WithBot ℕ∞) := by rw [hlen]
      _ = ldp a b := hq.symm
  · exact h.2.trans (ldp_eq_top_of_unbounded h.1).symm




theorem exists_sdp_min (h : Reachable a b) :
    ∃ p : Path a b,
      sdp a b = (p.length : ℕ∞) ∧
        ∀ q : Path a b, (p.length : ℕ∞) ≤ q.length := by
  obtain ⟨p, hp⟩ := exists_length_eq_sdp h
  refine ⟨p, hp.symm, ?_⟩
  intro q
  exact hp.trans_le (sdp_le_length q)

end DirectedDistances
