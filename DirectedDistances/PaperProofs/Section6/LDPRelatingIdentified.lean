/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section6.LDPRelating
public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified

/-! Supporting lemmas for paper labels `lem:LDP-relating-X1-X` (see CORRESPONDENCE.md). -/

/-! The three first-step LDP relations on the identified future maps at times zero and one.
The existing boundary-to-cut equivalence transfers the characterized functions directly;
the bounded-path witnesses come from the iid carrier theorem. No drawing or face assertion -/

public section
namespace DirectedDistances.PaperProofs.Section6

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive DirectedDistances.PaperProofs.Section1
open DirectedDistances.PaperProofs.Section7



theorem measurePreserving_wholePlane_shift_one :
    MeasurePreserving (fun W : ℤ → Fin 3 => fun i => W (i + 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure := by
  refine ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply (i + 1)), ?_⟩
  exact wholePlaneIIDCodeMeasure_map_shift 1



theorem shiftedStream_one_eq (W : ℤ → Fin 3) :
    (fun i => shiftedStream W 0 (1 + i)) =
      shiftedStream (fun k => W (k + 1)) 0 := by
  funext i
  simp only [shiftedStream, Nat.cast_zero, Int.sub_zero, Nat.cast_add, Nat.cast_one,
    Int.add_comm]



private theorem identifiedLDPBusemann_pinning_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W) := by
  filter_upwards [thm_busemann_paper,
    identifiedLDPBusemann_characterization_ae] with W hW hchar
  obtain ⟨H, h, hLL, _⟩ := hW
  exact ⟨H, h, hLL, hchar H h hLL⟩




private theorem boundaryBusemannLDP_of_identified_eq
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (w : ℕ → Fin 3) (hw : w = shiftedStream W 0)
    (hb : PresentPathLengthsBounded (w := w)) (h' : BoundaryHitWitnesses w)
    (X : ℤ → ℤ) (hX : IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X) :
    IsBoundaryBusemannLDP hb (boundaryPresentVertex w h') X := by
  subst w
  exact (boundaryBusemannLDP_iff_identified W H h hLL hb X).mpr hX






theorem lem_ldp_relating_identified :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let W1 : ℤ → Fin 3 := fun i => W (i + 1)
      let X := identifiedLDPBusemann W
      let X1 := identifiedLDPBusemann W1
      let c := shiftedStream W 0 0
      (∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X) ∧
      (∃ H : WholePlaneRotationHypothesis W1,
        ∃ h : BoundaryHitWitnesses (shiftedStream W1 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W1
          (wholePlaneEdgeι W1 0 (kmswLLCreatedEdge (shiftedStream W1 0)
            (boundaryHitTime (shiftedStream W1 0) h (k - 1)))),
          IsIdentifiedM0BusemannLDP (m0CutData W1 H h hLL) X1) ∧
      (c = 2 → (X (-1), X 1) =
        (X1 (-2) - max (X1 (-1)) 1, -max (X1 (-1)) 1)) ∧
      (c = 0 → (X (-1), X 1) = (-X1 1 - 1, -1)) ∧
      (c = 1 → (X (-1), X 1) = (X1 (-1), X1 2)) := by
  have hpin1 := measurePreserving_wholePlane_shift_one.quasiMeasurePreserving.ae
    identifiedLDPBusemann_pinning_ae
  have hrel := lem_ldp_relating_X1_X
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hrel
  have hpull := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hrel
  filter_upwards [identifiedLDPBusemann_pinning_ae, hpin1, hpull] with W hp0 hp1 hr
  have htail : (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
    funext i
    simp only [shiftedCodePath, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ite_false, Nat.add_sub_cancel]
  have htail1 : (fun i => shiftedCodePath W 0 (1 + i + 1)) =
      shiftedStream (fun k => W (k + 1)) 0 := by
    calc
      _ = (fun i => shiftedStream W 0 (1 + i)) :=
        funext (fun i => congrFun htail (1 + i))
      _ = _ := shiftedStream_one_eq W
  have hfirst : shiftedCodePath W 0 1 = shiftedStream W 0 0 := rfl
  rw [hfirst] at hr
  obtain ⟨hfin0, hfin1, h0, h1, _, _, hall⟩ := hr
  obtain ⟨H0, h0', hLL0, hX0⟩ := hp0
  obtain ⟨H1, h1', hLL1, hX1⟩ := hp1
  have hb0 := boundaryBusemannLDP_of_identified_eq W H0 h0' hLL0 _ htail
    (presentPathLengthsBounded_of_hfin _ hfin0) h0 _ hX0
  have hb1 := boundaryBusemannLDP_of_identified_eq (fun i => W (i + 1)) H1 h1' hLL1
    _ htail1 (presentPathLengthsBounded_of_hfin _ hfin1) h1 _ hX1
  exact ⟨⟨H0, h0', hLL0, hX0⟩, ⟨H1, h1', hLL1, hX1⟩, hall _ _ hb0 hb1⟩

end DirectedDistances.PaperProofs.Section6
