module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTFutureSubmapTags

/-! Rotation comparison for the future submap away from its past-boundary edges. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Lemma 5.10. Away from both sides of the future past-boundary
edges, the future dart equivalence preserves the whole-plane rotation. -/
theorem ae_uibhbotFutureSubmapDartEquiv_rotation :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
              e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
                ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
                  (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite,
              ∀ d : ℕ × Bool,
                (¬ limitExternalDart (fun i => uibhbotFutureCode k W (i + 1)) d ∧
                  ¬ limitExternalDart (fun i => uibhbotFutureCode k W (i + 1))
                    (d.1, !d.2)) →
                  wholePlaneRotation W H ((uibhbotFutureSubmapDartEquiv k W h d).1) =
                    (uibhbotFutureSubmapDartEquiv k W h
                      (kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin d)).1 := by
  filter_upwards [uibhbotFutureInteriorFaceCompatibility_ae] with W hface k h H hfin d hd
  let w : ℕ → Fin 3 := fun i => uibhbotFutureCode k W (i + 1)
  let r := kmswInfRot w hfin
  let q : ℕ × Bool := ((r d).1, !(r d).2)
  have hcancel : kmswInfFaceSucc w hfin q = d := by
    change r.symm (q.1, !q.2) = d
    simp only [q, Bool.not_not, Prod.eta, Equiv.symm_apply_apply]
  have hq : ¬ limitExternalDart w q := by
    intro hq
    have he := futureMap_external_faceSucc w hfin q hq
    rw [hcancel] at he
    exact hd.1 he
  have hf := hface k H hfin q hq
  have hf' : (wholePlaneRotation W H).symm
      (uibhbotFutureEdge k W (r d).1, (r d).2) =
        (uibhbotFutureEdge k W d.1, d.2) := by
    change (wholePlaneRotation W H).symm (uibhbotFutureEdge k W q.1, !q.2) =
      (uibhbotFutureEdge k W (kmswInfFaceSucc w hfin q).1,
        (kmswInfFaceSucc w hfin q).2) at hf
    rw [hcancel] at hf
    have hflip : (uibhbotFutureEdge k W q.1, !q.2) =
        (uibhbotFutureEdge k W (r d).1, (r d).2) := by
      dsimp only [q]
      rw [Bool.not_not]
    rw [hflip] at hf
    exact hf
  rw [uibhbotFutureSubmapDartEquiv_val, uibhbotFutureSubmapDartEquiv_val]
  change wholePlaneRotation W H (uibhbotFutureEdge k W d.1, d.2) =
    (uibhbotFutureEdge k W (r d).1, (r d).2)
  rw [← hf']
  exact (wholePlaneRotation W H).apply_symm_apply _

/-- Helper toward Lemma 5.10. Away from both sides of the future past-boundary
edges, the future dart equivalence preserves the inverse whole-plane rotation. -/
theorem ae_uibhbotFutureSubmapDartEquiv_rotation_symm :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
              e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
                ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
                  (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite,
              ∀ d : ℕ × Bool,
                (¬ limitExternalDart (fun i => uibhbotFutureCode k W (i + 1)) d ∧
                  ¬ limitExternalDart (fun i => uibhbotFutureCode k W (i + 1))
                    (d.1, !d.2)) →
                  (wholePlaneRotation W H).symm
                      ((uibhbotFutureSubmapDartEquiv k W h d).1) =
                    (uibhbotFutureSubmapDartEquiv k W h
                      ((kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin).symm
                        d)).1 := by
  filter_upwards [uibhbotFutureInteriorFaceCompatibility_ae] with W hface k h H hfin d hd
  let w : ℕ → Fin 3 := fun i => uibhbotFutureCode k W (i + 1)
  have hf := hface k H hfin (d.1, !d.2) hd.2
  change (wholePlaneRotation W H).symm (uibhbotFutureEdge k W d.1, !(!d.2)) =
    (uibhbotFutureEdge k W (kmswInfFaceSucc w hfin (d.1, !d.2)).1,
      (kmswInfFaceSucc w hfin (d.1, !d.2)).2) at hf
  have hcancel : kmswInfFaceSucc w hfin (d.1, !d.2) =
      (kmswInfRot w hfin).symm d := by
    change (kmswInfRot w hfin).symm (d.1, !(!d.2)) = _
    rw [Bool.not_not]
  rw [Bool.not_not, hcancel] at hf
  rw [uibhbotFutureSubmapDartEquiv_val, uibhbotFutureSubmapDartEquiv_val]
  exact hf

end DirectedDistances.RandomWalk
