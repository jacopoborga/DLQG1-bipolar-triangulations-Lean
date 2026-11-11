/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.RenewalRegenerationLaw
public import DirectedDistances.PaperProofs.Section4.SelectedCutPastMapLaw
public import DirectedDistances.RandomWalk.BlockBoundUnconditional
public import DirectedDistances.RandomWalk.RenewalGraphShift
public import DirectedDistances.RandomWalk.RenewalStoppedSliceTransport
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Data.Set.Card






public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk
open scoped ENNReal Classical

/-- Ambient post-selector path, centered at its selected endpoint. -/
@[expose] def selectorRenewalFuture
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) : (ℕ → ℤ × ℤ) → ℕ → ℤ × ℤ :=
  stoppedVectorFuture (fun p => (T 1 p).toNat) id

/-- Tagged prefix through the first positive selector time, retaining its duration
and both endpoints. Its raw values equal centered values almost surely under the
source law because paths start at `(0, 0)`. -/
@[expose] def selectorRenewalBlock
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (p : ℕ → ℤ × ℤ) :
    Σ n : ℕ, Fin (n + 1) → ℤ × ℤ :=
  stoppedVectorHistory (fun q => (T 1 q).toNat) id p

private theorem selector_successThreshold_iff_exists_count (S : ℕ → Prop) (m : ℕ) :
    (m : ℕ∞) ≤ {n : ℕ | S (n + 1)}.encard ↔
      ∃ N, m ≤ positiveSuccessCount S N := by
  classical
  constructor
  · intro h
    obtain ⟨f, hf, hfi⟩ :=
      (Set.le_encard_iff_exists_fin_injective {n : ℕ | S (n + 1)} m).mp h
    let N : ℕ := ∑ i : Fin m, (f i + 1)
    let F : Finset ℕ := (Finset.Icc 1 N).filter S
    have hbound (i : Fin m) : f i + 1 ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum (fun j hj => Nat.zero_le (f j + 1))
        (Finset.mem_univ i)
    have hmem (i : Fin m) : f i + 1 ∈ F := by
      change f i + 1 ∈ (Finset.Icc 1 N).filter S
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hbound i⟩, hf i⟩
    have hinj : Function.Injective
        (fun i : Fin m => (⟨f i + 1, hmem i⟩ : {j // j ∈ F})) := by
      intro i j hij
      have hval := congrArg Subtype.val hij
      exact hfi (Nat.succ.inj hval)
    have hcard : m ≤ F.card := by
      have h' := Fintype.card_le_of_injective
        (fun i : Fin m => (⟨f i + 1, hmem i⟩ : {j // j ∈ F})) hinj
      simpa only [Fintype.card_fin, Fintype.card_coe] using h'
    refine ⟨N, ?_⟩
    rw [positiveSuccessCount_eq_card]
    exact hcard
  · rintro ⟨N, hN⟩
    rw [positiveSuccessCount_eq_card] at hN
    let F : Finset ℕ := (Finset.Icc 1 N).filter S
    change m ≤ F.card at hN
    obtain ⟨G, hGF, hGcard⟩ := Finset.exists_subset_card_eq hN
    have hcard : Fintype.card (Fin m) = Fintype.card {j // j ∈ G} := by
      simp only [Fintype.card_fin, Fintype.card_coe, hGcard]
    let e : Fin m ≃ {j // j ∈ G} := Fintype.equivOfCardEq hcard
    apply (Set.le_encard_iff_exists_fin_injective {n : ℕ | S (n + 1)} m).mpr
    refine ⟨fun i => (e i).val - 1, ?_, ?_⟩
    · intro i
      have hjF : (e i).val ∈ F := hGF (e i).property
      change (e i).val ∈ (Finset.Icc 1 N).filter S at hjF
      rcases Finset.mem_filter.mp hjF with ⟨hjIcc, hs⟩
      have hjpos : 1 ≤ (e i).val := (Finset.mem_Icc.mp hjIcc).1
      change S (((e i).val - 1) + 1)
      rw [Nat.sub_add_cancel hjpos]
      exact hs
    · intro i j hij
      apply e.injective
      apply Subtype.ext
      have hiF : (e i).val ∈ F := hGF (e i).property
      have hjF : (e j).val ∈ F := hGF (e j).property
      change (e i).val ∈ (Finset.Icc 1 N).filter S at hiF
      change (e j).val ∈ (Finset.Icc 1 N).filter S at hjF
      have hi : 1 ≤ (e i).val := (Finset.mem_Icc.mp (Finset.mem_filter.mp hiF).1).1
      have hj : 1 ≤ (e j).val := (Finset.mem_Icc.mp (Finset.mem_filter.mp hjF).1).1
      calc
        (e i).val = ((e i).val - 1) + 1 := (Nat.sub_add_cancel hi).symm
        _ = ((e j).val - 1) + 1 := congrArg (fun x : ℕ => x + 1) hij
        _ = (e j).val := Nat.sub_add_cancel hj

private theorem selector_successThreshold_iff_finiteRank (S : ℕ → Prop) (m : ℕ) :
    (m : ℕ∞) ≤ {n : ℕ | S (n + 1)}.encard ↔
      ∃ n : ℕ, IsPositiveSuccessTime S m (n : ℕ∞) := by
  by_cases hm : m = 0
  · subst m
    constructor
    · intro _
      exact ⟨0, (isPositiveSuccessTime_zero_iff S _).mpr rfl⟩
    · intro _
      exact bot_le
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    rw [selector_successThreshold_iff_exists_count]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨n, hn⟩ := (exists_positiveSuccessRank_iff S hmpos).2 ⟨N, hN⟩
      exact ⟨n, (isPositiveSuccessTime_natCast_iff S hmpos n).mpr hn⟩
    · rintro ⟨n, hn⟩
      obtain ⟨_, _, hcount⟩ := (isPositiveSuccessTime_natCast_iff S hmpos n).mp hn
      exact ⟨n, hcount.ge⟩

private theorem selector_finite_iff_count
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (p : ℕ → ℤ × ℤ) (m : ℕ) :
    T m p < ⊤ ↔ (m : ℕ∞) ≤ {n : ℕ | literalSuccessGraph p (n + 1)}.encard := by
  by_cases hm : m = 0
  · subst m
    have ht : T 0 p = 0 := (isPositiveSuccessTime_zero_iff _ _).mp (hT p 0)
    rw [ht]
    exact ⟨fun _ => bot_le, fun _ => WithTop.coe_lt_top 0⟩
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    constructor
    · intro ht
      cases htp : T m p with
      | top => simp [htp] at ht
      | coe n =>
        have hrank := (isPositiveSuccessTime_natCast_iff _ hmpos n).mp
          (htp ▸ hT p m)
        exact (selector_successThreshold_iff_finiteRank (literalSuccessGraph p) m).2
          ⟨n, (isPositiveSuccessTime_natCast_iff _ hmpos n).mpr hrank⟩
    · intro hcount
      obtain ⟨n, hn⟩ :=
        (selector_successThreshold_iff_finiteRank (literalSuccessGraph p) m).1 hcount
      obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (literalSuccessGraph p) m
      have heq := (hu (T m p) (hT p m)).trans (hu (n : ℕ∞) hn).symm
      rw [heq]
      exact WithTop.coe_lt_top n




theorem selectorRenewalTime_measurable
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (m : ℕ) : Measurable (T m) :=
  measurable_selector_component_of_graph T hT m





theorem selectorRenewalTime_zero
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ p, T 0 p = 0 := by
  intro p
  exact (isPositiveSuccessTime_zero_iff _ _).mp (hT p 0)




theorem selectorRenewalTime_finite_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (m : ℕ) : ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), T m p < ⊤ := by
  filter_upwards [conditionedVectorPathLaw_ae_infinite_success] with p hp
  have hinf : {n : ℕ | literalSuccessGraph p (n + 1)}.Infinite := by
    simpa only [literalSuccessGraph] using hp
  have hcount : (m : ℕ∞) ≤ {n : ℕ | literalSuccessGraph p (n + 1)}.encard := by
    rw [Set.Infinite.encard_eq hinf]
    exact le_top
  exact (selector_finite_iff_count T hT p m).2 hcount

private theorem measurable_selectorRenewalFuture
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectorRenewalFuture T) := by
  have ht := selectorRenewalTime_measurable T hT 1
  have hn : Measurable (fun p => (T 1 p).toNat) :=
    (measurable_of_countable ENat.toNat).comp ht
  exact measurable_stoppedVectorFuture _ _ hn measurable_id

private theorem measurable_selectorRenewalBlock
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectorRenewalBlock T) := by
  have ht := selectorRenewalTime_measurable T hT 1
  have hn : Measurable (fun p => (T 1 p).toNat) :=
    (measurable_of_countable ENat.toNat).comp ht
  exact measurable_stoppedVectorHistory _ _ hn measurable_id




theorem selectorRenewalBlock_measurable
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectorRenewalBlock T) :=
  measurable_selectorRenewalBlock T hT




theorem selectorRenewalFuture_measurable
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    Measurable (selectorRenewalFuture T) :=
  measurable_selectorRenewalFuture T hT

private theorem selector_firstBlock_start_ae :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), p 0 = (0, 0) := by
  exact conditionedSource_ae_zero_start (conditionedVectorPathLaw 0 0) (fun k => by
    simpa only [Nat.cast_zero] using
      (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).2.1 k)




theorem selectorRenewalBlock_centered_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) :
    selectorRenewalBlock T =ᵐ[conditionedVectorPathLaw 0 0]
      (fun p => ⟨(T 1 p).toNat,
        fun j : Fin ((T 1 p).toNat + 1) => p j.val - p 0⟩) := by
  filter_upwards [selector_firstBlock_start_ae] with p hp
  let n := (T 1 p).toNat
  have hv : (fun j : Fin (n + 1) => p j.val) = (fun j => p j.val - p 0) := by
    funext j
    simp only [hp, ← Prod.zero_eq_mk, sub_zero]
  change (⟨n, fun j : Fin (n + 1) => p j.val⟩ :
      Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) = ⟨n, fun j => p j.val - p 0⟩
  exact congrArg (fun f : Fin (n + 1) → ℤ × ℤ =>
    (⟨n, f⟩ : Σ n : ℕ, Fin (n + 1) → ℤ × ℤ)) hv

end DirectedDistances.PaperProofs.Section4
