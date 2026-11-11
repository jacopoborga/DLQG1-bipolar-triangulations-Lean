module

public import DirectedDistances.PaperProofs.Section3.BSTopologyGeneric

public section
namespace DirectedDistances.PaperProofs.Section3

open Filter
open scoped ENNReal Topology

universe u v

namespace RootedBallSystem

variable {C : Type v} [Countable C]

/-- Helper toward Definition 3.8. Zero distance means agreement at every
indexed radius. The converse uses the vanishing weights `2⁻¹^(r+1)`. -/
theorem bsLocalDistance_eq_zero_iffGeneric (S : RootedBallSystem C)
    (x y : S.Object) :
    bsLocalDistanceGeneric S x y = 0 ↔
      ∀ r, S.ballClass r x = S.ballClass r y := by
  constructor
  · intro hzero r
    apply (bsLocalDistance_le_iff_ballClass_eqGeneric S x y r).mp
    rw [hzero]
    exact bot_le
  · intro hall
    have hpow : Tendsto (fun r : ℕ => (2 : ℝ≥0∞)⁻¹ ^ (r + 1)) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => (2 : ℝ≥0∞)⁻¹ ^ n) atTop (𝓝 0) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1)
      exact h.comp
        (tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id)
    apply le_antisymm
    · apply le_of_tendsto_of_tendsto' tendsto_const_nhds hpow
      intro r
      exact bsLocalDistance_le_of_ballClass_eqGeneric S x y r (hall r)
    · exact bot_le

/-- Helper toward Definition 3.8. The local distance is positive exactly when -/
theorem bsLocalDistance_pos_iffGeneric (S : RootedBallSystem C)
    (x y : S.Object) :
    0 < bsLocalDistanceGeneric S x y ↔
      ∃ r, S.ballClass r x ≠ S.ballClass r y := by
  constructor
  · intro hpos
    by_contra hnone
    have hall : ∀ r, S.ballClass r x = S.ballClass r y := by
      intro r
      by_contra hne
      exact hnone ⟨r, hne⟩
    have hzero := (bsLocalDistance_eq_zero_iffGeneric S x y).2 hall
    exact (ne_of_gt hpos) hzero
  · rintro ⟨r, hne⟩
    have hnonzero : bsLocalDistanceGeneric S x y ≠ 0 := by
      intro hzero
      have hall := (bsLocalDistance_eq_zero_iffGeneric S x y).1 hzero
      exact hne (hall r)
    exact lt_of_le_of_ne bot_le (Ne.symm hnonzero)

end RootedBallSystem
end DirectedDistances.PaperProofs.Section3
