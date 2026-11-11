module

public import DirectedDistances.PaperProofs.Section3.BSTopologyDefinitionProvider
public import DirectedDistances.PlanarMap.FramedBallClassRestrict

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5




theorem cyclicFirstReturn_map_of_equiv {α β : Type*}
    [DecidableEq α] [DecidableEq β] (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (S : Finset α) (T : Finset β) (e : α ≃ β)
    (hmem : ∀ x, x ∈ S ↔ e x ∈ T)
    (hcomm : ∀ x, e (σ x) = τ (e x))
    (hperS : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (σ ^ k) x.1 ∈ S)
    (hperT : ∀ y : T, ∃ k : ℕ, 0 < k ∧ (τ ^ k) y.1 ∈ T)
    (x : S) :
    e (cyclicFirstReturn σ S hperS x).1 =
      (cyclicFirstReturn τ T hperT ⟨e x.1, (hmem x.1).mp x.2⟩).1 := by
  have hpow : ∀ n z, e ((σ ^ n) z) = (τ ^ n) (e z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ,
        Equiv.Perm.mul_apply, ih, hcomm]
  let k := cyclicFirstReturnTime σ S hperS x
  let y : T := ⟨e x.1, (hmem x.1).mp x.2⟩
  let l := cyclicFirstReturnTime τ T hperT y
  have hk := cyclicFirstReturnTime_spec σ S hperS x
  have hl := cyclicFirstReturnTime_spec τ T hperT y
  have hkl : k = l := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlk : l < k := by omega
      have hsource : (σ ^ l) x.1 ∈ S := by
        apply (hmem _).2
        rw [hpow]
        exact hl.2.1
      exact hk.2.2 l hl.1 hlk hsource
    · by_contra hnot
      have hkl' : k < l := by omega
      have htarget : (τ ^ k) y.1 ∈ T := by
        rw [← hpow k x.1]
        exact (hmem _).mp hk.2.1
      exact hl.2.2 k hk.1 hkl' htarget
  have hs := (firstReturn_spec σ S hperS x).1
  have ht := (firstReturn_spec τ T hperT y).1
  rw [hs, ht]
  change e ((σ ^ k) x.1) = (τ ^ l) y.1
  rw [hkl, hpow]




@[expose] noncomputable def planarFramedBallRadiusClass
    (B : PlanarConnectedFramedBall) (r : ℕ) (hr : 0 < r) : FramedBallClass :=
  Quotient.mk FramedBall.setoid (planarFramedBallRestrictRadius B r hr).1




@[expose] def framedBallRadiusDartEquiv {B B' : FramedBall}
    (I : FramedBallIso B B') (r : ℕ) :
    {d : B.D // d ∈ framedBallRadiusDarts B r} ≃
      {d : B'.D // d ∈ framedBallRadiusDarts B' r} where
  toFun d := ⟨I.mapIso.toEquiv d.1,
    (framedBallRadiusDarts_mem_iso_iff I r d.1).2 d.2⟩
  invFun d := ⟨I.mapIso.toEquiv.symm d.1, by
    have h := framedBallRadiusDarts_mem_iso_iff I r
      (I.mapIso.toEquiv.symm d.1)
    apply h.mp
    rw [Equiv.apply_symm_apply]
    exact d.2⟩
  left_inv d := by simp
  right_inv d := by simp

end DirectedDistances.PaperProofs.Section3
end
