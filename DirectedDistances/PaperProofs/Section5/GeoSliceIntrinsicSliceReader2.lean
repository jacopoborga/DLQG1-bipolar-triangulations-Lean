/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceIntrinsicSliceReader

/-! Countable finite certificates for reachability and first return are
measurable when their individual relation and carrier tests are measurable.
The concrete varying-cell tests for `geoSliceIntrinsicSliceCore` remain
separate obligations. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory

/-- Helper toward Lemma 5.6: a finite chain certificate is measurable as a
countable union of finite intersections of measurable relation tests. -/
theorem measurableSet_existsFiniteChain
    {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (R : Ω → α → α → Prop)
    (hR : ∀ a b, MeasurableSet {ω | R ω a b}) (u v : α) :
    MeasurableSet {ω | ∃ n : ℕ, 0 < n ∧
      ∃ f : Fin (n + 1) → α,
        f 0 = u ∧ f ⟨n, Nat.lt_succ_self n⟩ = v ∧
        ∀ j : Fin n, R ω (f (Fin.castSucc j)) (f (Fin.succ j))} := by
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro n
  apply (MeasurableSet.const (0 < n)).inter
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro f
  have hrel : MeasurableSet (⋂ j : Fin n,
      {ω | R ω (f (Fin.castSucc j)) (f (Fin.succ j))}) :=
    MeasurableSet.iInter fun j => hR _ _
  exact (MeasurableSet.const (f 0 = u)).inter
    ((MeasurableSet.const (f ⟨n, Nat.lt_succ_self n⟩ = v)).inter hrel)

/-- Helper toward Lemma 5.6: first return to a measurable retained carrier
has a measurable finite-chain certificate, including avoidance by every
interior cell. -/
theorem measurableSet_existsFirstReturnChain
    {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (R : Ω → α → α → Prop) (K : Ω → α → Prop)
    (hR : ∀ a b, MeasurableSet {ω | R ω a b})
    (hK : ∀ a, MeasurableSet {ω | K ω a}) (u v : α) :
    MeasurableSet {ω | ∃ n : ℕ, 0 < n ∧
      ∃ f : Fin (n + 1) → α,
        f 0 = u ∧ f ⟨n, Nat.lt_succ_self n⟩ = v ∧
        (∀ j : Fin n, R ω (f (Fin.castSucc j)) (f (Fin.succ j))) ∧
        ∀ j : Fin (n + 1), 0 < j.val → j.val < n → ¬ K ω (f j)} := by
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro n
  apply (MeasurableSet.const (0 < n)).inter
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro f
  have hrel : MeasurableSet (⋂ j : Fin n,
      {ω | R ω (f (Fin.castSucc j)) (f (Fin.succ j))}) :=
    MeasurableSet.iInter fun j => hR _ _
  have havoid : MeasurableSet (⋂ j : Fin (n + 1),
      ⋂ (_ : 0 < j.val), ⋂ (_ : j.val < n), {ω | ¬ K ω (f j)}) := by
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro _
    change MeasurableSet ({ω | K ω (f j)}ᶜ)
    exact (hK (f j)).compl
  exact (MeasurableSet.const (f 0 = u)).inter
    ((MeasurableSet.const (f ⟨n, Nat.lt_succ_self n⟩ = v)).inter
      (hrel.inter havoid))







































































end DirectedDistances.PaperProofs.Section5
