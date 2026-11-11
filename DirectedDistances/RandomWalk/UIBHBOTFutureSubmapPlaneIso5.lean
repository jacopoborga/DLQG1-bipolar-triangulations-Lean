module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso4




public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5

/-- Helper toward Lemma 5.10. When the future code starts at a nonpositive
absolute time, its negative external boundary dart has first return length one:
the missing-boundary successor rule supplies the next future boundary dart. -/
theorem ae_uibhbotFuturePlaneGeometricSide_externalFaceNext_negative_nonpositiveStart :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ _hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
              e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
                ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
                  (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite,
              uibhbotBoundaryHitTime k W ≤ 0 →
                ∀ j : ℤ, j ≤ -1 →
                  (uibhbotFuturePlaneGeometricSide k W h H).faceNext
                    (futureMapBoundaryDart
                      (fun i => uibhbotFutureCode k W (i + 1)) h j)
                    (futureMapBoundaryDart
                      (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1)) := by
  filter_upwards [ae_uibhbotFutureSubmap_externalEdge_missing_negative]
    with W hmissing k h H hfin ht j hj
  let t := uibhbotBoundaryHitTime k W
  let N := t.natAbs
  have hstream : (fun i => uibhbotFutureCode k W (i + 1)) = shiftedStream W N := by
    rw [uibhbotFutureCode_stream, lemma38StartStream_eq_shifted W t ht]
  have hN : BoundaryHitWitnesses (shiftedStream W N) := by
    rw [← hstream]
    exact h
  have hmissing' : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N
        (boundaryOuterEdge (shiftedStream W N) hN j)) := by
    have hm := hmissing k h j hj
    simpa [uibhbotFutureEdge, lemma38StartEdgeι, t, N, ht, hstream] using hm
  have hstep := (wholePlane_missing_boundary_faceSucc W H N hN j hj hmissing').2
  have hmap (d : ℕ × Bool) :
      (uibhbotFutureSubmapDartEquiv k W h d).1 = wholePlaneDartι W N d := by
    rw [uibhbotFutureSubmapDartEquiv_val]
    cases d with
    | mk e b =>
        simp [wholePlaneDartι, uibhbotFutureEdge, lemma38StartEdgeι, t, N, ht]
        rfl
  have hstep' :
      wholePlaneFaceSucc W H
          (wholePlaneDartι W N
            (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)) =
        wholePlaneDartι W N
          (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1)) := by
    simpa only [hstream] using hstep
  change ∃ n : ℕ, 0 < n ∧
    (wholePlaneFaceSucc W H)^[n]
        (uibhbotFutureSubmapDartEquiv k W h
          (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)).1 =
      (uibhbotFutureSubmapDartEquiv k W h
        (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1))).1 ∧
    ∀ m : ℕ, 0 < m → m < n →
      ((wholePlaneFaceSucc W H)^[m]
        (uibhbotFutureSubmapDartEquiv k W h
          (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)).1).1 ∉
        (uibhbotFutureSubmap k W h).edges
  refine ⟨1, by norm_num, ?_, ?_⟩
  · change wholePlaneFaceSucc W H
      (uibhbotFutureSubmapDartEquiv k W h
        (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)).1 = _
    rw [hmap, hmap]
    exact hstep'
  · intro m hm0 hm1
    omega
























end DirectedDistances.RandomWalk
