/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39BallBridgePart1







public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.D39BallBridge

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section5
open scoped ENNReal

universe u

/-- Helper toward Definition 3.8 consumers: any two compatible PL
representatives of one geometric class have the same exterior-marked ball. -/
theorem representative_independent {c : D39GeomRootedMapClass.{u}}
    (x y : PLCylinderBall.Representative c) (r : ℕ) (hr : 0 < r) :
    representedExteriorMarkedBallClass x.representation r hr =
      representedExteriorMarkedBallClass y.representation r hr := by
  apply (edist_le_iff_markedClass_eq x.representation y.representation r hr).mp
  rw [x.class_eq, y.class_eq, edist_self]
  exact bot_le

/-- Helper toward Definition 3.8 consumers: the exterior-marked class
exists uniquely with its all-representative characterization. -/
theorem ballClass_existsUnique {c : D39GeomRootedMapClass.{u}}
    (hc : PLCylinderBall.IsPLRepresentable c) (r : ℕ) (hr : 0 < r) :
    ∃! k : ExteriorMarkedBallClass, ∀ R : PLCylinderBall.Representative c,
      representedExteriorMarkedBallClass R.representation r hr = k := by
  obtain ⟨R⟩ := hc
  refine ⟨representedExteriorMarkedBallClass R.representation r hr, ?_, ?_⟩
  · intro S
    exact representative_independent S R r hr
  · intro k hk
    exact (hk R).symm

/-- Helper toward Definition 3.8 consumers: the ball-class map on the
existing PL-representable subspace, indexed by positive source radius `r+1`.
The exterior marker is the unique unbounded orbit of the restricted drawing. -/
@[expose] def ballClass (r : ℕ) (x : PLCylinderBall.X_PL.{u}) : ExteriorMarkedBallClass :=
  Classical.choose (ballClass_existsUnique x.property (r + 1) (Nat.succ_pos r))

/-- Helper toward Definition 3.8 consumers: complete characterization of
the chosen ball class for every compatible PL representative. -/
theorem ballClass_eq (r : ℕ) (x : PLCylinderBall.X_PL.{u})
    (R : PLCylinderBall.Representative x.val) :
    ballClass r x = representedExteriorMarkedBallClass R.representation
      (r + 1) (Nat.succ_pos r) :=
  ((Classical.choose_spec
    (ballClass_existsUnique x.property (r + 1) (Nat.succ_pos r))).1 R).symm

/-- Helper toward Definition 3.8 consumers: the exact dyadic closed-ball
characterization for the specified exterior-marked ball-class map. -/
theorem hball (r : ℕ) (x y : PLCylinderBall.X_PL.{u}) :
    edist (x.val : D39GeomRootedMapClass) y.val ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔
      ballClass r x = ballClass r y := by
  obtain ⟨R⟩ := x.property
  obtain ⟨S⟩ := y.property
  rw [ballClass_eq r x R, ballClass_eq r y S]
  conv_lhs => rw [← R.class_eq, ← S.class_eq]
  exact edist_le_iff_markedClass_eq R.representation S.representation
    (r + 1) (Nat.succ_pos r)

/-- Helper toward Definition 3.8 consumers: equality at a larger observed
radius implies equality at every smaller observed radius. -/
theorem ballClass_restrict {s r : ℕ} (hsr : s ≤ r) (x y : PLCylinderBall.X_PL.{u})
    (h : ballClass r x = ballClass r y) : ballClass s x = ballClass s y := by
  apply (hball s x y).mp
  apply ((hball r x y).mpr h).trans
  exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.add_le_add_right hsr 1)

/-- Helper toward Definition 3.8 consumers: the exterior-marked cylinder
topology is exactly the existing geometric class subspace topology. -/
theorem ballClass_topology :
    DirectedDistances.Probability.localClassTopology ballClass =
      (inferInstance : TopologicalSpace PLCylinderBall.X_PL.{u}) :=
  DirectedDistances.Probability.localClassTopology_eq_induced ballClass hball
    (fun r x y h => ballClass_restrict (Nat.le_succ r) x y h)















































end DirectedDistances.PaperProofs.Section3.D39BallBridge

end
