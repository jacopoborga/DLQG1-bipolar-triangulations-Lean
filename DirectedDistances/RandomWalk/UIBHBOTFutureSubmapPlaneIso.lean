module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTFutureSubmapRotation2
public import DirectedDistances.PaperProofs.Section4.ThinSideCodeFidelity

/-! Plane structure for the UIBHBOT future submap and its comparison with the shifted KMSW future code. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.10. The face successor on an interior dart of the
future-code submap agrees with the ambient whole-plane face successor. The
external future face is excluded because its successor is a boundary successor
of the submap, not an asserted ambient face successor. -/
theorem ae_uibhbotFutureSubmapDartEquiv_faceSucc_interior :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
              e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
                ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
                  (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite,
              ∀ d : ℕ × Bool,
                ¬ limitExternalDart (fun i => uibhbotFutureCode k W (i + 1)) d →
                  wholePlaneFaceSucc W H
                      ((uibhbotFutureSubmapDartEquiv k W h d).1) =
                    (uibhbotFutureSubmapDartEquiv k W h
                      (kmswInfFaceSucc
                        (fun i => uibhbotFutureCode k W (i + 1)) hfin d)).1 := by
  filter_upwards [uibhbotFutureInteriorFaceCompatibility_ae]
    with W hcompat k h H hfin d hd
  simpa only [uibhbotFutureSubmapDartEquiv_val] using hcompat k H hfin d hd

/-- Helper toward Lemma 5.10. The future-code face successor at a labelled
boundary dart moves to the preceding boundary dart. This is the exact boundary
rule for the code map; it does not identify that outer-face successor with the
ambient whole-plane face successor. -/
theorem uibhbotFutureSubmapDartEquiv_boundaryFaceSucc (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
        ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
          (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite)
    (j : ℤ) :
    uibhbotFutureSubmapDartEquiv k W h
        (kmswInfFaceSucc (fun i => uibhbotFutureCode k W (i + 1)) hfin
          (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)) =
      uibhbotFutureSubmapDartEquiv k W h
        (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1)) := by
  apply congrArg (uibhbotFutureSubmapDartEquiv k W h)
  exact futureMapBoundaryDart_faceSucc
    (w := fun i => uibhbotFutureCode k W (i + 1)) (hfin := hfin) h j

/-- Helper toward Lemma 5.10. Each marked submap boundary vertex is the image,
under the proved future vertex map, of the correspondingly indexed KMSW
future-code boundary vertex. -/
theorem uibhbotFutureSubmap_boundary_codeVertex (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (j : ℤ) (hj : j ≤ 0) :
    ((uibhbotFutureSubmap k W h).boundary ⟨j, hj⟩).1 =
      uibhbotFutureVertex k W
        (boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j) := rfl

/-- Helper toward Lemma 5.10. Almost surely, the marked future-submap boundary
vertex at relative index `j ≤ 0` is the original UIBHBOT boundary vertex at
index `k + j`. -/
theorem ae_uibhbotFutureSubmap_boundary_originalIndex :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ (j : ℤ) (hj : j ≤ 0),
            ((uibhbotFutureSubmap k W h).boundary ⟨j, hj⟩).1 =
              uibhbotFutureVertex (k + j) W 0 := by
  exact ae_uibhbotFutureSubmap_boundary_index






















end DirectedDistances.RandomWalk
