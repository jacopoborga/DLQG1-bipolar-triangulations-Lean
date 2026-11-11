/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWInverseStepLink

/-! # A local rotation decoder for KMSW letters

The inverse-procedure Peano configurations give a decoder using only two
orientation tests around the current dart. The decoder is invariant under
rotation-, reversal-, and orientation-preserving dart relabelling. On finite
bipolar triangulations it recovers the literal inverse-code letter.

This does not yet identify the chronological whole-plane exploration from -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 3.9: the local inverse-code rule. The first
test detects descent (code `2`); otherwise the rotation test distinguishes
rotation (code `1`) from climb (code `0`). It uses no enumeration of darts. -/
@[expose] def uibotLocalCodeLetter {D : Type*} (rot : Equiv.Perm D)
    (flip : D → D) (tail : D → Prop) (d : D) : Fin 3 := by
  classical
  exact if tail (rot.symm (flip d)) then 2 else if tail (rot d) then 1 else 0

/-- Helper toward Proposition 3.9: the local letter is unchanged by any
dart equivalence preserving rotation, edge reversal, and orientation. -/
theorem uibotLocalCodeLetter_equiv {D E : Type*}
    (rot : Equiv.Perm D) (rot' : Equiv.Perm E)
    (flip : D → D) (flip' : E → E) (tail : D → Prop) (tail' : E → Prop)
    (e : D ≃ E)
    (hrot : ∀ d, e (rot d) = rot' (e d))
    (hflip : ∀ d, e (flip d) = flip' (e d))
    (htail : ∀ d, tail' (e d) ↔ tail d) (d : D) :
    uibotLocalCodeLetter rot' flip' tail' (e d) =
      uibotLocalCodeLetter rot flip tail d := by
  have hinv (x : D) : e (rot.symm x) = rot'.symm (e x) := by
    apply rot'.injective
    rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  unfold uibotLocalCodeLetter
  rw [← hflip, ← hinv, ← hrot, htail, htail]

private theorem localCode_bounce_face_reverse
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ ρ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ ρ)
    (a : D) (ha : B.map.tail a)
    (hb : contourNext B a = B.map.toCombinatorialMap.edgeInv a) :
    ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc a) := by
  classical
  intro hf
  have hs := contour_forward_head_ne_source B a ha
  have hn := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
  have hv : dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc a) =
      dartHeadVertex B.map a := by
    apply Quotient.sound
    refine ⟨1, ?_⟩
    change B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.rot.symm (B.map.toCombinatorialMap.edgeInv a)) = _
    exact B.map.toCombinatorialMap.rot.apply_symm_apply _
  have ht : dartHeadVertex B.map a ≠ B.sink := by
    intro he
    exact B.isSink ⟨dartHeadVertex B.map (B.map.toCombinatorialMap.faceSucc a),
      B.map.toCombinatorialMap.faceSucc a, B.noMissingDarts _, hf, hv.trans he, rfl⟩
  have hsel : B.map.toCombinatorialMap.edgeInv a =
      leftmostIncoming B (dartHeadVertex B.map a) hs :=
    (leftmostIncoming_internal_characterization B _ hs ht).2.2.2 _ rfl hn hf
  have he : contourNext B a = rightmostOutgoing B (dartHeadVertex B.map a) ht := by
    simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
  have hforward := (rightmostOutgoing_internal_characterization B _ hs ht).2.1
  rw [← he, hb] at hforward
  exact hn hforward

/-- Helper toward Proposition 3.9: at every nonfinal finite Peano edge,
the two local orientation tests recover its step kind's exact code. In
particular no tree heights or other Peano indices are inputs to the decoder. -/
theorem uibotLocalCodeLetter_peano
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ ρ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ ρ) (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    uibotLocalCodeLetter B.map.toCombinatorialMap.rot
      B.map.toCombinatorialMap.edgeInv B.map.tail
      (peanoEdge B ⟨j, by omega⟩) =
        stepCode (peanoStepKind B j hj).increment := by
  classical
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  have ha : B.map.tail a := peanoEdge_forward B _
  have hb : B.map.tail b := peanoEdge_forward B _
  have h := peanoStepKind_config B j hj
  change uibotLocalCodeLetter B.map.toCombinatorialMap.rot
    B.map.toCombinatorialMap.edgeInv B.map.tail a = _
  cases hk : peanoStepKind B j hj with
  | descend =>
      rw [hk] at h
      obtain ⟨hs, ht, hsel, _⟩ := h
      have hf : B.map.tail (B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.edgeInv a)) := by
        rw [hsel]
        exact (leftmostIncoming_internal_characterization B _ hs ht).2.2.1
      simp only [uibotLocalCodeLetter, hf, ite_eq_left]
      rfl
  | rotate =>
      rw [hk] at h
      obtain ⟨he, _, hbounce, _, _, _⟩ := h
      have hf := localCode_bounce_face_reverse B a ha hbounce
      have hr : B.map.tail (B.map.toCombinatorialMap.rot a) := he ▸ hb
      change ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm
        (B.map.toCombinatorialMap.edgeInv a)) at hf
      simp only [uibotLocalCodeLetter, hf, hr, ite_eq_left]
      rfl
  | climb =>
      rw [hk] at h
      obtain ⟨hs, hbounce, _, _, _, hsel, _, _, _⟩ := h
      have hf := localCode_bounce_face_reverse B a ha hbounce
      have hr : ¬ B.map.tail (B.map.toCombinatorialMap.rot a) := by
        rw [hsel]
        have ht : dartTailVertex B.map a ≠ B.sink := by
          intro he
          exact B.isSink ⟨dartHeadVertex B.map a, a, B.noMissingDarts a,
            ha, he, rfl⟩
        exact (leftmostIncoming_internal_characterization B _ hs ht).2.1
      change ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm
        (B.map.toCombinatorialMap.edgeInv a)) at hf
      simp only [uibotLocalCodeLetter, hf, hr]
      rfl

/-- Helper toward Proposition 3.9: the literal finite inverse code is
recovered from the local rotation and orientation at its current Peano dart. -/
theorem uibotLocalCodeLetter_inverseCode {ℓ ρ n : ℕ}
    (R : KMSWMapRep ℓ ρ n) (j : ℕ) (hj : j + 1 < n) :
    uibotLocalCodeLetter R.B.map.toCombinatorialMap.rot
      R.B.map.toCombinatorialMap.edgeInv R.B.map.tail
      (peanoEdge R.B ⟨j, by simpa only [R.edges] using Nat.lt_of_succ_lt hj⟩) =
        kmswRepInverseCode R ⟨j, by omega⟩ := by
  rw [kmswRepInverseCode_eq_stepCode_peanoStepHeightDifference R j hj,
    peanoStepConfig_height_increment R.B j _ _ (peanoStepKind_config R.B j _)]
  exact uibotLocalCodeLetter_peano R.B j _

end DirectedDistances.PaperProofs.Section3

end
