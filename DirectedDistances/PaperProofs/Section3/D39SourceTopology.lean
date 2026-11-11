/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RootedMapIsoBall
public import DirectedDistances.PaperProofs.Section3.D39ConcreteDistance

/-! Supporting lemmas for paper labels `def-bs-topology` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open scoped ENNReal



theorem D39RootedMapIso.d39BallClass_eq {M N : D39RootedMap}
    (I : D39RootedMapIso M N) (r : ℕ) :
    d39BallClass M (r + 1) (Nat.succ_pos r) =
      d39BallClass N (r + 1) (Nat.succ_pos r) := by
  apply (d39BallClass_eq_iff M N (r + 1) (Nat.succ_pos r)).2
  exact ⟨I.ballIso (r + 1) (by omega)⟩

/-- Helper toward Definition 3.8. The local distance is invariant when its
first argument is changed along a rooted whole-map isomorphism. -/
theorem d39RootedBallSystem_distance_congr_left {M M' N : D39RootedMap}
    (I : D39RootedMapIso M M') :
    RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M N =
      RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M' N := by
  have hzero :
      RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M M' = 0 :=
    (d39RootedBallSystem_distance_eq_zero_iff M M').2
      (fun r => D39RootedMapIso.d39BallClass_eq I r)
  apply le_antisymm
  · have h := RootedBallSystem.bsLocalDistance_ultrametricGeneric
      d39RootedBallSystem M M' N
    simpa [hzero] using h
  · have h := RootedBallSystem.bsLocalDistance_ultrametricGeneric
      d39RootedBallSystem M' M N
    rw [RootedBallSystem.bsLocalDistance_symmGeneric
      d39RootedBallSystem M' M] at h
    simpa [hzero] using h

/-- Helper toward Definition 3.8. The local distance is invariant when its
second argument is changed along a rooted whole-map isomorphism. -/
theorem d39RootedBallSystem_distance_congr_right {M N N' : D39RootedMap}
    (I : D39RootedMapIso N N') :
    RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M N =
      RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M N' := by
  rw [RootedBallSystem.bsLocalDistance_symmGeneric d39RootedBallSystem M N,
    d39RootedBallSystem_distance_congr_left I,
    RootedBallSystem.bsLocalDistance_symmGeneric d39RootedBallSystem N' M]



theorem d39RootedBallSystem_distance_congr {M M' N N' : D39RootedMap}
    (I : D39RootedMapIso M M') (J : D39RootedMapIso N N') :
    RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M N =
      RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M' N' := by
  rw [d39RootedBallSystem_distance_congr_left I,
    d39RootedBallSystem_distance_congr_right J]





@[expose] noncomputable def d39PlanarRootedMapClassDistance
    (M N : D39PlanarRootedMapClass) : ℝ≥0∞ :=
  Quotient.liftOn₂ M N
    (fun A B => RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem
      A.toD39RootedMap B.toD39RootedMap)
    (by
      intro A B A' B' hA hB
      rcases hA with ⟨I⟩
      rcases hB with ⟨J⟩
      calc
        RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem
            A.toD39RootedMap B.toD39RootedMap =
          RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem
            A'.toD39RootedMap B.toD39RootedMap :=
          d39RootedBallSystem_distance_congr_left I
        _ = RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem
            A'.toD39RootedMap B'.toD39RootedMap :=
          d39RootedBallSystem_distance_congr_right J)

/-- Helper toward Definition 3.8. On representatives the descended distance
is the concrete rooted-ball-system distance. -/
@[simp] theorem d39PlanarRootedMapClassDistance_mk_mk
    (M N : D39PlanarRootedMap) :
    d39PlanarRootedMapClassDistance
      (Quotient.mk D39PlanarRootedMap.setoid M)
      (Quotient.mk D39PlanarRootedMap.setoid N) =
      RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem
        M.toD39RootedMap N.toD39RootedMap := by
  simp only [d39PlanarRootedMapClassDistance, Quotient.liftOn₂_mk]



theorem d39PlanarRootedMapClassDistance_mk_mk_eq_source_formula
    (M N : D39PlanarRootedMap) :
    d39PlanarRootedMapClassDistance
      (Quotient.mk D39PlanarRootedMap.setoid M)
      (Quotient.mk D39PlanarRootedMap.setoid N) =
      ⨅ r : ℕ, ⨅ (_ : d39BallClass M.toD39RootedMap (r + 1)
          (Nat.succ_pos r) =
        d39BallClass N.toD39RootedMap (r + 1) (Nat.succ_pos r)),
        (2 : ℝ≥0∞)⁻¹ ^ (r + 1) := by
  rw [d39PlanarRootedMapClassDistance_mk_mk,
    d39RootedBallSystem_distance_eq_source_formula]

/-- Helper toward Definition 3.8. The descended distance is symmetric. -/
theorem d39PlanarRootedMapClassDistance_symm
    (M N : D39PlanarRootedMapClass) :
    d39PlanarRootedMapClassDistance M N =
      d39PlanarRootedMapClassDistance N M := by
  refine Quotient.inductionOn₂ M N ?_
  intro M N
  rw [d39PlanarRootedMapClassDistance_mk_mk,
    d39PlanarRootedMapClassDistance_mk_mk]
  exact RootedBallSystem.bsLocalDistance_symmGeneric d39RootedBallSystem
    M.toD39RootedMap N.toD39RootedMap

/-- Helper toward Definition 3.8. The descended distance vanishes on the
diagonal. -/
theorem d39PlanarRootedMapClassDistance_self
    (M : D39PlanarRootedMapClass) :
    d39PlanarRootedMapClassDistance M M = 0 := by
  refine Quotient.inductionOn M ?_
  intro M
  rw [d39PlanarRootedMapClassDistance_mk_mk]
  exact RootedBallSystem.bsLocalDistance_selfGeneric d39RootedBallSystem
    M.toD39RootedMap

/-- Helper toward Definition 3.8. The descended distance satisfies the
ultrametric triangle inequality. -/
theorem d39PlanarRootedMapClassDistance_ultrametric
    (M N P : D39PlanarRootedMapClass) :
    d39PlanarRootedMapClassDistance M P ≤
      max (d39PlanarRootedMapClassDistance M N)
        (d39PlanarRootedMapClassDistance N P) := by
  refine Quotient.inductionOn₃ M N P ?_
  intro M N P
  simp only [d39PlanarRootedMapClassDistance_mk_mk]
  exact RootedBallSystem.bsLocalDistance_ultrametricGeneric
    d39RootedBallSystem M.toD39RootedMap N.toD39RootedMap P.toD39RootedMap









end DirectedDistances.PaperProofs.Section3
