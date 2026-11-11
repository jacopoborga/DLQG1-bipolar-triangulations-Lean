module

public import DirectedDistances.PaperProofs.Section4.RenewalIIDBlockProducts
public import DirectedDistances.PaperProofs.Section4.RenewalIIDBlocks

/-! identification of iterated blocks for a supplied literal success graph T
(NOT the admitted source T_m or Lemma 4.9); not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk
open scoped ENNReal Classical

private theorem selector_rank_add_pathShift
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (p : ℕ → ℤ × ℤ) (j : ℕ) (hj : T j p < ⊤) :
    T (j + 1) p = T j p +
      T 1 (fun k => p ((T j p).toNat + k) - p (T j p).toNat) := by
  have hcast := ENat.natCast_toNat (ne_of_lt hj)
  have hgraph : IsPositiveSuccessTime (literalSuccessGraph p) j
      ((T j p).toNat : ℕ∞) := by
    rw [hcast]
    exact hT p j
  have hshift := (isPositiveSuccessTime_renewal_add_pathShift_iff p
    (m := j) (t := (T j p).toNat) (r := 1) (by decide) hgraph
    (T 1 (fun k => p ((T j p).toNat + k) - p (T j p).toNat))).mpr
      (hT (fun k => p ((T j p).toNat + k) - p (T j p).toNat) 1)
  change IsPositiveSuccessTime (literalSuccessGraph p) (j + 1) _ at hshift
  rw [hcast] at hshift
  obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (literalSuccessGraph p) (j + 1)
  exact (hu _ (hT p (j + 1))).trans (hu _ hshift).symm

private theorem selector_next_shift_ne_top {a b c : ℕ∞}
    (h : a = b + c) (ha : a < ⊤) : c ≠ ⊤ := by
  intro hc
  rw [hc, add_top] at h
  exact (ne_of_lt ha) h

private theorem selector_iterate_future_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), ∀ j : ℕ,
      (selectorRenewalFuture T)^[j] p =
        fun k => p ((T j p).toNat + k) - p (T j p).toNat := by
  have hfinite : ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), ∀ j : ℕ, T j p < ⊤ :=
    ae_all_iff.mpr (selectorRenewalTime_finite_ae T hT)
  have hstart : ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), p 0 = (0, 0) :=
    conditionedSource_ae_zero_start (conditionedVectorPathLaw 0 0) (fun k => by
      simpa only [Nat.cast_zero] using
        (DirectedDistances.Paper.Section4.cond_walk_rn_law (0 : ℕ) (0 : ℤ)).2.1 k)
  filter_upwards [hfinite, hstart] with p hp hzero
  intro j
  induction j with
  | zero =>
      funext k
      simp only [Function.iterate_zero, id_eq, selectorRenewalTime_zero T hT,
        ENat.toNat_zero, Nat.zero_add, hzero, ← Prod.zero_eq_mk, sub_zero]
  | succ j ih =>
      let q : ℕ → ℤ × ℤ := fun k =>
        p ((T j p).toNat + k) - p (T j p).toNat
      have hadd := selector_rank_add_pathShift T hT p j (hp j)
      have hq : T 1 q ≠ ⊤ := selector_next_shift_ne_top hadd (hp (j + 1))
      have hn : (T (j + 1) p).toNat = (T j p).toNat + (T 1 q).toNat := by
        rw [hadd, ENat.toNat_add (ne_of_lt (hp j)) hq]
      rw [Function.iterate_succ_apply', ih]
      change (fun k => q ((T 1 q).toNat + k) - q (T 1 q).toNat) = _
      funext k
      dsimp only [q]
      rw [← Nat.add_assoc, ← hn, sub_sub_sub_cancel_right]




theorem selectorRenewalTime_rankShift_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), ∀ j : ℕ,
      T (j + 1) p = T j p + T 1 ((selectorRenewalFuture T)^[j] p) := by
  have hfinite : ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), ∀ j : ℕ, T j p < ⊤ :=
    ae_all_iff.mpr (selectorRenewalTime_finite_ae T hT)
  filter_upwards [hfinite, selector_iterate_future_ae T hT] with p hp hiter
  intro j
  rw [hiter j]
  exact selector_rank_add_pathShift T hT p j (hp j)





theorem selectorRenewalBlock_iterate_eq_segment_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), ∀ j : ℕ,
      selectorRenewalBlock T ((selectorRenewalFuture T)^[j] p) =
        (⟨(T (j + 1) p).toNat - (T j p).toNat,
          fun i => p ((T j p).toNat + i.val) - p (T j p).toNat⟩ :
          Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) := by
  have hfinite : ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), ∀ j : ℕ, T j p < ⊤ :=
    ae_all_iff.mpr (selectorRenewalTime_finite_ae T hT)
  filter_upwards [hfinite, selector_iterate_future_ae T hT,
    selectorRenewalTime_rankShift_ae T hT] with p hp hiter hrank
  intro j
  have hq := selector_next_shift_ne_top (hrank j) (hp (j + 1))
  have hn : (T (j + 1) p).toNat = (T j p).toNat +
      (T 1 ((selectorRenewalFuture T)^[j] p)).toNat := by
    rw [hrank j, ENat.toNat_add (ne_of_lt (hp j)) hq]
  have hlen : (T 1 ((selectorRenewalFuture T)^[j] p)).toNat =
      (T (j + 1) p).toNat - (T j p).toNat := by omega
  change (⟨(T 1 ((selectorRenewalFuture T)^[j] p)).toNat,
    fun i => ((selectorRenewalFuture T)^[j] p) i.val⟩ :
      Σ n : ℕ, Fin (n + 1) → ℤ × ℤ) = _
  rw [hlen]
  simp only [hiter j]

end DirectedDistances.PaperProofs.Section4
