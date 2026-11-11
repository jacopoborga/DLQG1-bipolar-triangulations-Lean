/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalSelectorConsequence
import DirectedDistances.RandomWalk.RenewalGraphShift
import DirectedDistances.RandomWalk.RenewalSuccessMeasurability
import Mathlib.Data.Set.Card
import Mathlib.Probability.Kernel.CondDistrib
meta import Lean.Elab.Tactic.Omega

/-! # Geometric identity for the actual source success count

The geometric count identity in Lemma 4.9 (`lem-renewal`,
future law and the deterministic renewal-rank shift. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

private theorem successThreshold_iff_exists_count (S : ℕ → Prop) (m : ℕ) :
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

private theorem successThreshold_iff_finiteRank (S : ℕ → Prop) (m : ℕ) :
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
    rw [successThreshold_iff_exists_count]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨n, hn⟩ := (exists_positiveSuccessRank_iff S hmpos).2 ⟨N, hN⟩
      exact ⟨n, (isPositiveSuccessTime_natCast_iff S hmpos n).mpr hn⟩
    · rintro ⟨n, hn⟩
      obtain ⟨hnpos, _, hcount⟩ :=
        (isPositiveSuccessTime_natCast_iff S hmpos n).mp hn
      exact ⟨n, hcount.ge⟩

/-- Geometric identity for the success count under the actual source law, -/
theorem conditionedSource_successCount_geometric (ν : Measure (ℕ → ℤ × ℤ))
    [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (m : ℕ) :
    ν {p | ((m + 1 : ℕ) : ℕ∞) ≤ {n : ℕ |
      (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
        ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.encard} =
      ν {p | (m : ℕ∞) ≤ {n : ℕ |
        (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
          ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.encard} *
      ν {p | (1 : ℕ∞) ≤ {n : ℕ |
        (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
          ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.encard} := by
  classical
  let S : (ℕ → ℤ × ℤ) → ℕ → Prop := fun p j =>
    (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
      ∀ i, j ≤ i → (p j).1 ≤ (p i).1
  let T : (ℕ → ℤ × ℤ) → WithTop ℕ := fun p =>
    Classical.choose (existsUnique_positiveSuccessTime (S p) m).exists
  have hGraph : ∀ p, IsPositiveSuccessTime (S p) m (T p) := by
    intro p
    exact Classical.choose_spec (existsUnique_positiveSuccessTime (S p) m).exists
  have hFiber (p : ℕ → ℤ × ℤ) (t : WithTop ℕ) :
      T p = t ↔ IsPositiveSuccessTime (S p) m t := by
    constructor
    · intro ht
      rw [← ht]
      exact hGraph p
    · intro ht
      obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (S p) m
      exact (hu (T p) (hGraph p)).trans (hu t ht).symm
  have hT : Measurable T := by
    intro s hs
    have hpre : T ⁻¹' s = ⋃ t : s, {p | T p = t.val} := by
      ext p
      constructor
      · intro hp
        exact Set.mem_iUnion.mpr ⟨⟨T p, hp⟩, rfl⟩
      · intro hp
        obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
        change T p = t.val at ht
        change T p ∈ s
        rw [ht]
        exact t.property
    rw [hpre]
    apply MeasurableSet.iUnion
    intro t
    have hEq : {p | T p = t.val} =
        {p | IsPositiveSuccessTime (S p) m t.val} := by
      ext p
      exact hFiber p t.val
    rw [hEq]
    induction t.val using ENat.recTopCoe with
    | top =>
      exact measurableSet_isPositiveSuccessTime_top
        _ (fun j _ => measurableSet_renewal_success j) m
    | coe n =>
      exact measurableSet_isPositiveSuccessTime_natCast
        _ (fun j _ => measurableSet_renewal_success j) m n

  have hfiniteThreshold (p : ℕ → ℤ × ℤ) :
      T p < ⊤ ↔ (m : ℕ∞) ≤ {n : ℕ | S p (n + 1)}.encard := by
    by_cases hm : m = 0
    · subst m
      have ht : T p = 0 :=
        (isPositiveSuccessTime_zero_iff _ _).mp (hGraph p)
      rw [ht]
      exact ⟨fun _ => bot_le, fun _ => WithTop.coe_lt_top 0⟩
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      constructor
      · intro ht
        cases htp : T p with
        | top => simp [htp] at ht
        | coe n =>
          have hrank := (isPositiveSuccessTime_natCast_iff _ hmpos n).mp
            (htp ▸ hGraph p)
          exact (successThreshold_iff_finiteRank (S p) m).2
            ⟨n, (isPositiveSuccessTime_natCast_iff _ hmpos n).mpr hrank⟩
      · intro hcount
        obtain ⟨n, hn⟩ := (successThreshold_iff_finiteRank (S p) m).1 hcount
        obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (S p) m
        have heq := (hu (T p) (hGraph p)).trans (hu (n : ℕ∞) hn).symm
        rw [heq]
        exact WithTop.coe_lt_top n

  let μf : Measure {p // T p < ⊤} :=
    ν.comap (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ))
  let history := stoppedVectorHistory (finiteTimeIndex T) (fun ω => ω.val)
  let future := stoppedVectorFuture (finiteTimeIndex T) (fun ω => ω.val)
  have hcond := conditionedSource_selector_condDistrib_ae_eq_const ν hRN m T (by
    intro p
    simpa only [S] using hGraph p)
  have hhistory : Measurable history :=
    measurable_finiteTime_vectorHistory T (fun p => p) hT measurable_id
  have hfuture : Measurable future :=
    measurable_finiteTime_vectorFuture T (fun p => p) hT measurable_id
  have hjoint : μf.map (fun ω => (history ω, future ω)) =
      μf.map history ⊗ₘ Kernel.const (Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) ν := by
    apply (condDistrib_ae_eq_iff_measure_eq_compProd
      hhistory.aemeasurable hfuture.aemeasurable _).mp
    simpa only [μf, history, future] using hcond

  have hfutureLaw : μf.map future = μf Set.univ • ν := by
    calc
      μf.map future = Measure.map Prod.snd
          (μf.map (fun ω => (history ω, future ω))) := by
        rw [Measure.map_map measurable_snd (hhistory.prodMk hfuture)]
        congr 1
      _ = Measure.map Prod.snd ((μf.map history).prod ν) := by
        rw [hjoint, Measure.compProd_const]
      _ = (μf.map history) Set.univ • ν := Measure.map_snd_prod
      _ = μf Set.univ • ν := by
        simpa using congrArg (fun x : ℝ≥0∞ => x • ν)
          (Measure.map_apply hhistory MeasurableSet.univ)

  let G : Set (ℕ → ℤ × ℤ) :=
    {q | (1 : ℕ∞) ≤ {n : ℕ | S q (n + 1)}.encard}
  have hGmeas : MeasurableSet G := by
    have hG : G = ⋃ n : ℕ, {q | S q (n + 1)} := by
      ext q
      simp only [G, Set.mem_ofPred_eq, Set.mem_iUnion]
      rw [Set.one_le_encard_iff_nonempty]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, hn⟩
    rw [hG]
    exact MeasurableSet.iUnion fun n => measurableSet_renewal_success (n + 1)

  have hshiftEvent (ω : {p // T p < ⊤}) :
      ((m + 1 : ℕ) : ℕ∞) ≤ {n : ℕ | S ω.val (n + 1)}.encard ↔
        future ω ∈ G := by
    let p := ω.val
    let t := finiteTimeIndex T ω
    have htgraph : IsPositiveSuccessTime (S p) m (t : ℕ∞) := by
      have htemp := hGraph p
      rw [← coe_finiteTimeIndex T ω] at htemp
      exact htemp
    let shifted : ℕ → Prop := fun j => S (fun a => p (t + a) - p t) j
    have hrankShift (s : ℕ∞) :
        IsPositiveSuccessTime (S p) (m + 1) ((t : ℕ∞) + s) ↔
          IsPositiveSuccessTime shifted 1 s := by
      simpa only [shifted] using
        isPositiveSuccessTime_renewal_add_pathShift_iff p (m := m) (t := t)
          (r := 1) (by omega) htgraph s
    constructor
    · intro hcount
      obtain ⟨t₂, ht₂⟩ :=
        (successThreshold_iff_finiteRank (S p) (m + 1)).1 hcount
      have hle : t ≤ t₂ := by
        by_cases hm : m = 0
        · subst m
          have htzero : t = 0 := by
            exact WithTop.coe_injective
              ((isPositiveSuccessTime_zero_iff _ _).mp htgraph)
          omega
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
          have hmt := (isPositiveSuccessTime_natCast_iff _ hmpos t).mp htgraph
          have hm1pos : 0 < m + 1 := by omega
          have hnext := (isPositiveSuccessTime_natCast_iff _ hm1pos t₂).mp ht₂
          have hcountt : positiveSuccessCount (S p) t = m := hmt.2.2
          have hcountt₂ : positiveSuccessCount (S p) t₂ = m + 1 := hnext.2.2
          have hmono := positiveSuccessCount_mono (S p)
          by_contra hnot
          have hlt : t₂ < t := Nat.lt_of_not_ge hnot
          have hc := hmono (Nat.le_of_lt hlt)
          omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hshift := hrankShift (s : ℕ∞)
      have hshifted := hshift.mp (by simpa only [← ENat.natCast_add] using ht₂)
      have hG := (successThreshold_iff_finiteRank shifted 1).2 ⟨s, hshifted⟩
      have hfut : future ω = (fun a => p (t + a) - p t) := rfl
      simpa only [G, Set.mem_ofPred_eq, hfut, shifted, Nat.cast_one] using hG
    · intro hG
      have hfut : future ω = (fun a => p (t + a) - p t) := rfl
      have hG' : (1 : ℕ∞) ≤ {n : ℕ | shifted (n + 1)}.encard := by
        simpa only [G, Set.mem_ofPred_eq, hfut, shifted, Nat.cast_one] using hG
      have hshifted := (successThreshold_iff_finiteRank shifted 1).1 hG'
      obtain ⟨s, hs⟩ := hshifted
      have hshift := hrankShift (s : ℕ∞)
      have horig := hshift.mpr hs
      exact (successThreshold_iff_finiteRank (S p) (m + 1)).2
        ⟨t + s, by simpa only [← ENat.natCast_add] using horig⟩

  have hImage :
      Subtype.val '' (future ⁻¹' G) =
        {p | ((m + 1 : ℕ) : ℕ∞) ≤ {n : ℕ | S p (n + 1)}.encard} := by
    ext p
    constructor
    · rintro ⟨ω, hω, rfl⟩
      exact (hshiftEvent ω).2 hω
    · intro hp
      have hmcount : (m : ℕ∞) ≤ {n : ℕ | S p (n + 1)}.encard := by
        have hlecast : (m : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) := by
          exact_mod_cast (Nat.le_succ m)
        exact hlecast.trans hp
      have hfinite := (hfiniteThreshold p).2 hmcount
      refine ⟨⟨p, hfinite⟩, ?_, rfl⟩
      exact (hshiftEvent ⟨p, hfinite⟩).1 hp

  have hmass : μf Set.univ = ν {p | (m : ℕ∞) ≤
      {n : ℕ | S p (n + 1)}.encard} := by
    have he : MeasurableEmbedding
        (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ)) :=
      MeasurableEmbedding.subtype_coe (hT measurableSet_Iio)
    have hset : Subtype.val '' (Set.univ : Set {p // T p < ⊤}) =
        {p | T p < ⊤} := by
      ext p
      change (∃ q : {p // T p < ⊤}, q ∈ Set.univ ∧ q.val = p) ↔ T p < ⊤
      constructor
      · rintro ⟨q, -, hq⟩
        cases hq
        exact q.property
      · intro hp
        exact ⟨⟨p, hp⟩, Set.mem_univ _, rfl⟩
    calc
      μf Set.univ = ν (Subtype.val '' (Set.univ : Set {p // T p < ⊤})) := by
        change ν.comap Subtype.val Set.univ = _
        exact he.comap_apply ν _
      _ = ν {p | T p < ⊤} := by rw [hset]
      _ = ν {p | (m : ℕ∞) ≤ {n : ℕ | S p (n + 1)}.encard} := by
        congr 1
        ext p
        exact hfiniteThreshold p

  have hleft :
      ν {p | ((m + 1 : ℕ) : ℕ∞) ≤
        {n : ℕ | S p (n + 1)}.encard} = μf.map future G := by
    have he : MeasurableEmbedding
        (Subtype.val : {p // T p < ⊤} → (ℕ → ℤ × ℤ)) :=
      MeasurableEmbedding.subtype_coe (hT measurableSet_Iio)
    calc
      ν {p | ((m + 1 : ℕ) : ℕ∞) ≤ {n : ℕ | S p (n + 1)}.encard} =
          ν (Subtype.val '' (future ⁻¹' G)) := by rw [hImage]
      _ = ν.comap Subtype.val (future ⁻¹' G) := (he.comap_apply ν _).symm
      _ = μf (future ⁻¹' G) := rfl
      _ = μf.map future G := (Measure.map_apply hfuture hGmeas).symm

  have hresult : μf.map future G = μf Set.univ * ν G := by
    have h := congrArg (fun η : Measure (ℕ → ℤ × ℤ) => η G) hfutureLaw
    simpa only [Measure.smul_apply, smul_eq_mul] using h

  calc
    ν {p | ((m + 1 : ℕ) : ℕ∞) ≤ {n : ℕ |
        (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
          ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.encard} =
        μf.map future G := hleft
    _ = μf Set.univ * ν G := hresult
    _ = ν {p | (m : ℕ∞) ≤ {n : ℕ |
          (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
            ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.encard} *
        ν {p | (1 : ℕ∞) ≤ {n : ℕ |
          (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
            ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.encard} := by
      rw [hmass]

end DirectedDistances.RandomWalk
