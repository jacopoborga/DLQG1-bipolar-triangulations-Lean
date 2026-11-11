module

public import DirectedDistances.KMSW.WholePlaneDrawingCombinatorics
public import Mathlib.Basic.Countable.Basic

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
These local rotation and edge-reversal facts support a future rooted-map object. -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The quotient carrier is countable because its representatives are pairs of
natural numbers and darts add only a two-element side tag. Source: -/
theorem wholePlaneDart_countable (W : ℤ → Fin 3) :
    Countable (WholePlaneDart W) := by
  unfold WholePlaneDart
  have hEdge : Countable (WholePlaneEdge W) := by
    unfold WholePlaneEdge
    exact Quotient.mk_surjective.countable
  obtain ⟨f, hf⟩ := @Countable.exists_injective_nat (WholePlaneEdge W) hEdge
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat Bool
  exact (Nat.pairEquiv.injective.comp (hf.prodMap hg)).countable

private theorem function_eq_of_sameCycle {D A : Type*} (f : Equiv.Perm D)
    (g : D → A) (hforward : ∀ d, g (f d) = g d)
    (hbackward : ∀ d, g (f.symm d) = g d) {d e : D}
    (h : f.SameCycle d e) : g e = g d := by
  obtain ⟨i, hi⟩ := h
  have hpow : ∀ i : ℤ, g ((f ^ i) d) = g d := by
    intro i
    refine Int.induction_on i ?_ ?_ ?_
    · simp
    · intro i ih
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      rw [hforward, ih]
    · intro i ih
      have hneg : (-(i : ℤ) - 1) = -1 + -(i : ℤ) := by ring
      rw [hneg, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      change g (f.symm ((f ^ (-(i : ℤ))) d)) = g d
      rw [hbackward, ih]
  rw [← hi]
  exact hpow i

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Darts in one whole-plane rotation cycle have the same incident vertex. -/
theorem wholePlaneRotation_sameCycle_dartVertex (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d e : WholePlaneDart W)
    (h : (wholePlaneRotation W H).SameCycle d e) :
    wholePlaneDartVertex W e = wholePlaneDartVertex W d := by
  have hbackward (x : WholePlaneDart W) :
      wholePlaneDartVertex W ((wholePlaneRotation W H).symm x) =
        wholePlaneDartVertex W x := by
    have hrot := wholePlaneRotation_preserves_dartVertex W H
      ((wholePlaneRotation W H).symm x)
    simpa only [Equiv.apply_symm_apply] using hrot.symm
  exact function_eq_of_sameCycle (wholePlaneRotation W H)
    (wholePlaneDartVertex W) (wholePlaneRotation_preserves_dartVertex W H)
    hbackward h

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The converse vertex-to-cycle statement is isolated for later proof; it is not
(Definition 5.8). -/
@[expose] def wholePlaneRotation_sameVertex_sameCycle
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) : Prop :=
  ∀ d e : WholePlaneDart W,
    wholePlaneDartVertex W d = wholePlaneDartVertex W e →
      (wholePlaneRotation W H).SameCycle d e

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every whole-plane rotation orbit is finite, by containment in its incident -/
theorem wholePlaneRotation_sameCycleOrbit_finite (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : WholePlaneDart W) :
    {e : WholePlaneDart W | (wholePlaneRotation W H).SameCycle d e}.Finite := by
  apply (wholePlaneStar_finite W H (wholePlaneDartVertex W d)).subset
  intro e he
  exact wholePlaneRotation_sameCycle_dartVertex W H d e he

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The whole-plane edge reversal is involutive. Source: -/
theorem wholePlaneDartFlip_involutive (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    wholePlaneDartFlip W ((wholePlaneDartFlip W) d) = d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
No whole-plane geometric edge has a fixed dart under reversal. Source: -/
theorem wholePlaneDartFlip_ne (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    wholePlaneDartFlip W d ≠ d := by
  rcases d with ⟨e, b⟩
  change (e, !b) ≠ (e, b)
  intro h
  have hb := congrArg Prod.snd h
  cases b <;> simp at hb

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Reversal preserves the identity of the underlying geometric edge. Source: -/
theorem wholePlaneDartFlip_edge (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    (wholePlaneDartFlip W d).1 = d.1 := rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The missing-edge predicate defined by absence of `wholePlaneEdgePresent` is
(Definition 5.8). -/
theorem wholePlaneDartMissing_flip_iff (W : ℤ → Fin 3)
    (d : WholePlaneDart W) :
    (¬ wholePlaneEdgePresent W d.1) ↔
      ¬ wholePlaneEdgePresent W (wholePlaneDartFlip W d).1 := Iff.rfl

end DirectedDistances.KMSW
