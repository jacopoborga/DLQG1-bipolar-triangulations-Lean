/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole7

/-! Finite root-port adjustment transport toward Lemma 5.5 -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

private theorem equiv_apply_swap_transport {α β : Type*} [DecidableEq α]
    [DecidableEq β] (e : α ≃ β)
    {a b : α} {a' b' : β} (ha : e a = a') (hb : e b = b') (d : α) :
    e (Equiv.swap a b d) = Equiv.swap a' b' (e d) := by
  by_cases hda : d = a
  · subst d
    simp only [Equiv.swap_apply_left, ha, hb]
  · by_cases hdb : d = b
    · subst d
      simp only [Equiv.swap_apply_right, ha, hb]
    · have hda' : e d ≠ a' := by
        intro h
        apply hda
        exact e.injective (h.trans ha.symm)
      have hdb' : e d ≠ b' := by
        intro h
        apply hdb
        exact e.injective (h.trans hb.symm)
      rw [Equiv.swap_apply_of_ne_of_ne hda hdb,
        Equiv.swap_apply_of_ne_of_ne hda' hdb']

private theorem stageDart_transport_apply {m n : ℕ} (h : m = n)
    (d : StageDart m) :
    Eq.mp (congrArg StageDart h) d = (Fin.cast h d.1, d.2) := by
  cases h
  rfl

private theorem codePrefixDart_transport {F G : State}
    (M : GeometricSideSubmap) (h : F = G) (z : StageDart F.nextEdge) :
    transportEquivOfTypeEq
      (congrArg (fun s : State => RMinusCodeGluedDart s M) h)
      (rMinusCodePrefixDart F M z) =
    rMinusCodePrefixDart G M
      (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) h) z) := by
  cases h
  rfl

/-- Helper toward Lemma 5.5: across streams with the same first `n` letters,
the initial root-port transposition in `rMinusCodeInitialAdjustedRotation`
commutes with transport of the finite-state quotient dart carrier. This
records the adjustment factor only; it assumes no splice or whole-rotation
conjugacy. -/
theorem rMinusCodeInitialRootPortAdjustment_conj_of_sharedPrefix
    (x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (q : Coherent x)
    (d : RMinusCodeGluedDart (kmswStage u n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
    let iU : Fin ((kmswStage u n).active :: (kmswStage u n).UR).length :=
      ⟨0, by simp⟩
    let iV : Fin ((kmswStage v n).active :: (kmswStage v n).UR).length :=
      ⟨0, by simp⟩
    rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
      (Equiv.swap
        (rMinusCodeBoundaryDart u n M (iU, false))
        (rMinusCodePrefixDart (kmswStage u n) M
          (stageRot u n (rMinusPrefixBoundaryDart u n (iU, false)))) d) =
      Equiv.swap
        (rMinusCodeBoundaryDart v n M (iV, false))
        (rMinusCodePrefixDart (kmswStage v n) M
          (stageRot v n (rMinusPrefixBoundaryDart v n (iV, false))))
        (rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp d) := by
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  let iU : Fin ((kmswStage u n).active :: (kmswStage u n).UR).length := ⟨0, by simp⟩
  let iV : Fin ((kmswStage v n).active :: (kmswStage v n).UR).length := ⟨0, by simp⟩
  let hstate := kmswStage_eq_of_prefix u v n hp
  let hnextNat := congrArg (fun s : State => s.nextEdge) hstate
  let hnext := congrArg StageDart hnextNat
  let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
  have hrootU : rMinusPrefixBoundaryDart u n (iU, false) =
      (⟨(kmswStage u n).active, act_lt_nextEdge u (le_refl n)⟩, false) := by
    simp [rMinusPrefixBoundaryDart, iU]
  have hrootV : rMinusPrefixBoundaryDart v n (iV, false) =
      (⟨(kmswStage v n).active, act_lt_nextEdge v (le_refl n)⟩, false) := by
    simp [rMinusPrefixBoundaryDart, iV]
  have hprefixPort : Eq.mp hnext
      (rMinusPrefixBoundaryDart u n (iU, false)) =
      rMinusPrefixBoundaryDart v n (iV, false) := by
    rw [hrootU, hrootV, stageDart_transport_apply hnextNat]
    apply Prod.ext
    · apply Fin.ext
      change (kmswStage u n).active = (kmswStage v n).active
      exact congrArg (fun s : State => s.active) hstate
    · rfl
  have hprefixTransport (z : StageDart (kmswStage u n).nextEdge) :
      e (rMinusCodePrefixDart (kmswStage u n) M z) =
        rMinusCodePrefixDart (kmswStage v n) M (Eq.mp hnext z) := by
    change transportEquivOfTypeEq
      (congrArg (fun s : State => RMinusCodeGluedDart s M) hstate)
      (rMinusCodePrefixDart (kmswStage u n) M z) = _
    exact codePrefixDart_transport M hstate z
  have hrootBoundary :
      e (rMinusCodeBoundaryDart u n M (iU, false)) =
        rMinusCodeBoundaryDart v n M (iV, false) := by
    rw [rMinusCodeBoundaryDart_eq_prefix, rMinusCodeBoundaryDart_eq_prefix]
    rw [hprefixTransport, hprefixPort]
  have hrootSuccessor :
      e (rMinusCodePrefixDart (kmswStage u n) M
        (stageRot u n (rMinusPrefixBoundaryDart u n (iU, false)))) =
      rMinusCodePrefixDart (kmswStage v n) M
        (stageRot v n (rMinusPrefixBoundaryDart v n (iV, false))) := by
    rw [hprefixTransport]
    rw [stageRot_cast_conj_of_prefix n hp]
    rw [hprefixPort]
  simpa only [M, iU, iV, e] using
    equiv_apply_swap_transport e hrootBoundary hrootSuccessor d

end DirectedDistances.PaperProofs.Section5
