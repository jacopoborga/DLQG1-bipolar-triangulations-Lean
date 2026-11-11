/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartInvariance2
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIsoSymm

/-! # Whole-map storage-flip invariance of geometric dart distance -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open Filter
open scoped ENNReal Topology

/-- Helper toward Definition 3.8: a whole-map endpoint storage flip induces
the corresponding rooted geometric ball isomorphism at every positive radius. -/
@[expose]
def D39GeomBallIsoV2.flipEdges {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E)
    {r : ℕ} (hr : 0 < r) :
    D39GeomBallIsoV2 r M rho (flipEdges M S)
      (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) :=
  (D39GeomRootedMapIsoV2.storeFlip M rho S).toBallIsoV2 r hr

/-- Helper toward Definition 3.8: the infimum of the positive-radius weights
`(1 / 2)^r` is zero. -/
theorem d39GeomDistanceV2_halfPow_iInf_eq_zero :
    (⨅ r : {r : ℕ // 0 < r}, (1 / 2 : ℝ≥0∞) ^ r.1) = 0 := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0∞) ^ (n + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0∞) ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
    exact h.comp
      (tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id)
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto' tendsto_const_nhds hpow
    intro n
    exact iInf_le (fun r : {r : ℕ // 0 < r} => (1 / 2 : ℝ≥0∞) ^ r.1)
      ⟨n + 1, Nat.succ_pos n⟩
  · exact bot_le

/-- Helper toward Definition 3.8: a rooted map and its whole-map endpoint
storage flip have zero geometric distance. -/
theorem d39GeomDistanceV2_storeFlip_eq_zero {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E) :
    d39GeomDistanceV2 M rho (flipEdges M S)
      (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) = 0 := by
  rw [← d39GeomDistanceV2_halfPow_iInf_eq_zero]
  apply le_antisymm
  · apply le_iInf
    intro r
    change d39GeomDistanceV2 M rho (flipEdges M S)
        (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) ≤
      (1 / 2 : ℝ≥0∞) ^ r.1
    exact (iInf_le (fun q : {q : ℕ // 0 < q} =>
        ⨅ (_ : Nonempty (D39GeomBallIsoV2 q.1 M rho (flipEdges M S)
          (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)))),
          (1 / 2 : ℝ≥0∞) ^ q.1) r).trans
      (iInf_le (fun _ : Nonempty (D39GeomBallIsoV2 r.1 M rho (flipEdges M S)
          (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1))) =>
          (1 / 2 : ℝ≥0∞) ^ r.1)
        ⟨D39GeomBallIsoV2.flipEdges M rho S r.2⟩)
  · rw [d39GeomDistanceV2_halfPow_iInf_eq_zero]
    exact bot_le

/-- Helper toward Definition 3.8: storage flips preserve geometric distance
in the first argument. -/
theorem d39GeomDistanceV2_storeFlip_congr_left {V E V' E' : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E)
    (N : DirectedPlaneMapWithMissing V' E') (sigma : E' × Bool) :
    d39GeomDistanceV2 (flipEdges M S)
        (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) N sigma =
      d39GeomDistanceV2 M rho N sigma := by
  exact (D39GeomRootedMapIsoV2.d39GeomDistanceV2_congr_left
    (D39GeomRootedMapIsoV2.storeFlip M rho S)).symm

/-- Helper toward Definition 3.8: storage flips preserve geometric distance
in the second argument. -/
theorem d39GeomDistanceV2_storeFlip_congr_right {V E V' E' : Type*}
    (N : DirectedPlaneMapWithMissing V E) (sigma : E × Bool)
    (M : DirectedPlaneMapWithMissing V' E') (rho : E' × Bool) (S : Set E') :
    d39GeomDistanceV2 N sigma (flipEdges M S)
        (rho.1, Bool.xor rho.2 (d39GeomEdgeFlipBit S rho.1)) =
      d39GeomDistanceV2 N sigma M rho := by
  exact (D39GeomRootedMapIsoV2.d39GeomDistanceV2_congr_right
    (D39GeomRootedMapIsoV2.storeFlip M rho S)).symm

end DirectedDistances.PaperProofs.Section3

end
