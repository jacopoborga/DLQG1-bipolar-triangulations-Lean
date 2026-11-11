/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteBall
public import DirectedDistances.PlanarMap.D39PlanarBallPlanarity
public import DirectedDistances.PlanarMap.KMSWMapIsoClass
public import DirectedDistances.PaperProofs.Section5.D39UIBHBOTMeasurability

public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.PaperProofs.Section5

private theorem cyclicFirstReturn_val_eq_of_mem_iff
    {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (S T : Finset α)
    (hST : ∀ a, a ∈ S ↔ a ∈ T)
    (hS : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hT : ∀ x : T, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ T)
    (x : S) (y : T) (hxy : x.1 = y.1) :
    (cyclicFirstReturn σ S hS x).1 =
      (cyclicFirstReturn σ T hT y).1 := by
  let k := cyclicFirstReturnTime σ S hS x
  let l := cyclicFirstReturnTime σ T hT y
  have hk := cyclicFirstReturnTime_spec σ S hS x
  have hl := cyclicFirstReturnTime_spec σ T hT y
  have hkl : k = l := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hkl | hlk
    · have hret : (σ ^ k) y.1 ∈ T := by simpa [hxy] using (hST _).mp hk.2.1
      exact hl.2.2 k hk.1 hkl hret
    · have hret : (σ ^ l) x.1 ∈ S := by simpa [hxy] using (hST _).mpr hl.2.1
      exact hk.2.2 l hl.1 hlk hret
  have hx := (firstReturn_spec σ S hS x).1
  have hy := (firstReturn_spec σ T hT y).1
  have hkl' : cyclicFirstReturnTime σ S hS x =
      cyclicFirstReturnTime σ T hT y := by simpa [k, l] using hkl
  change (cyclicFirstReturn σ S hS x).1 = (cyclicFirstReturn σ T hT y).1
  rw [hx, hy, hkl', hxy]

/-- Helper toward Definition 3.8. -/
theorem rootedLocallyFinitePlanarMap_d39Ball_genusZero
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r) :
    D39BallGenusZero (M.toRootedLocallyFiniteMap.toD39RootedMap) r := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let T := A.toD39RootedMap
  have hplanar := M.ball_isPlanar r hr
  have hdarts := d39BallDarts_toD39RootedMap A r
  let S := rootedLocallyFiniteBallDarts A r
  let U := d39BallDarts T r
  have hST : ∀ d : A.D, d ∈ S ↔ d ∈ U := by
    intro d
    change d ∈ rootedLocallyFiniteBallDarts A r ↔ d ∈ d39BallDarts T r
    exact Iff.of_eq (congrArg (fun V : Finset A.D => d ∈ V) hdarts).symm
  have hS : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (A.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, hperiod⟩ := rootedLocallyFiniteRotationReturn A x.1
    exact ⟨k, hk, by rw [hperiod]; exact x.2⟩
  have hU : ∀ x : U, ∃ k : ℕ, 0 < k ∧ (A.rot ^ k) x.1 ∈ U := by
    intro x
    obtain ⟨k, hk, hperiod⟩ := d39RotationReturn T x.1
    refine ⟨k, hk, ?_⟩
    change (T.core.rot ^ k) x.1 ∈ U
    rw [hperiod]
    exact x.2
  let e : {d : A.D // d ∈ rootedLocallyFiniteBallDarts A r} ≃
      {d : T.core.D // d ∈ d39BallDarts T r} := {
    toFun := fun d => ⟨d.1, hdarts.symm ▸ d.2⟩
    invFun := fun d => ⟨d.1, hdarts ▸ d.2⟩
    left_inv := by intro d; apply Subtype.ext; rfl
    right_inv := by intro d; apply Subtype.ext; rfl }
  have hplanarTransport :
      (rootedLocallyFiniteBallCombinatorialMap A r).transport e |>.IsPlanar :=
    CombinatorialMap.transport_isPlanar e
      (rootedLocallyFiniteBallCombinatorialMap A r) hplanar
  have hmap : d39BallMap T r =
      (rootedLocallyFiniteBallCombinatorialMap A r).transport e := by
    simp only [d39BallMap, rootedLocallyFiniteBallCombinatorialMap,
      CombinatorialMap.transport, CombinatorialMap.mk.injEq]
    constructor
    · ext d
      rfl
    · ext d
      let x := e.symm d
      have hval : x.1 = d.1 := congrArg Subtype.val (e.apply_symm_apply d)
      have h := cyclicFirstReturn_val_eq_of_mem_iff A.rot S U hST hS hU x d hval
      change (cyclicFirstReturn A.rot U hU d).1 =
        (cyclicFirstReturn A.rot S hS x).1
      exact h.symm
  have hplanarD : (d39BallMap T r).IsPlanar := by
    rw [hmap]
    exact hplanarTransport
  exact (d39Ball_isPlanar_iff T r hr).1 hplanarD

/-- Helper toward Definition 3.8. Package a rooted locally finite planar map
with the local topology positive-ball genus-zero condition, retaining its converted map. -/
@[expose] def RootedLocallyFinitePlanarMap.toD39PlanarRootedMap
    (M : RootedLocallyFinitePlanarMap) : D39PlanarRootedMap where
  toD39RootedMap := M.toRootedLocallyFiniteMap.toD39RootedMap
  positiveBallGenusZero := rootedLocallyFinitePlanarMap_d39Ball_genusZero M

/-- Helper toward Definition 3.8. The wrapper's underlying rooted map is the
existing conversion by definition. -/
theorem RootedLocallyFinitePlanarMap.toD39PlanarRootedMap_toD39RootedMap
    (M : RootedLocallyFinitePlanarMap) :
    M.toD39PlanarRootedMap.toD39RootedMap =
      M.toRootedLocallyFiniteMap.toD39RootedMap := rfl

/-- Helper toward Definition 3.8 and Proposition 5.16. The wrapper's positive
ball class is definitionally the existing rooted-map ball class, so the
measurability development's faced-framed-ball conversion applies unchanged. -/
theorem d39PlanarRootedMap_ballClass_eq_facedFramedBallClassToD39BallClass
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) :
    d39BallClass M.toD39PlanarRootedMap.toD39RootedMap (r + 1) (Nat.succ_pos r) =
      facedFramedBallClassToD39BallClass
        (rootedLocallyFiniteFacedBallClass r M) := by
  change d39BallClass
      M.toRootedLocallyFiniteMap.toD39RootedMap (r + 1) (Nat.succ_pos r) = _
  exact d39BallClass_eq_facedFramedBallClassToD39BallClass M r

end DirectedDistances.PlanarMap
