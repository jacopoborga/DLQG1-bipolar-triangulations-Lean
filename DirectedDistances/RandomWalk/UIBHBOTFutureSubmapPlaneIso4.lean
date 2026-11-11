module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso3




public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5

/-- Helper toward Lemma 5.10. A past-side external future dart has the
whole-plane edge image of the LL edge created at its local boundary hit. -/
theorem uibhbotFutureSubmap_externalDart_negative_image (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (j : ℤ) (hj : j ≤ -1) :
    (uibhbotFutureSubmapDartEquiv k W h
      (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)).1 =
        (uibhbotFutureEdge k W
          (kmswLLCreatedEdge (fun i => uibhbotFutureCode k W (i + 1))
            (boundaryHitTime (fun i => uibhbotFutureCode k W (i + 1)) h j)), true) := by
  rw [uibhbotFutureSubmapDartEquiv_val, futureMapBoundaryDart,
    boundaryOuterEdge_of_negative _ h hj]

/-- Helper toward Lemma 5.10. The zero-index future boundary dart is the
whole-plane image of the future code's root edge. -/
theorem uibhbotFutureSubmap_externalDart_zero_image (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) :
    (uibhbotFutureSubmapDartEquiv k W h
      (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h 0)).1 =
        (uibhbotFutureEdge k W 0, true) := by
  rw [uibhbotFutureSubmapDartEquiv_val, futureMapBoundaryDart,
    boundaryOuterEdge_zero]

/-- Helper toward Lemma 5.10. A positive-index future boundary dart is the
whole-plane image of the corresponding KMSW right-boundary edge. -/
theorem uibhbotFutureSubmap_externalDart_positive_image (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (j : ℤ) (hj : 1 ≤ j) :
    (uibhbotFutureSubmapDartEquiv k W h
      (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)).1 =
        (uibhbotFutureEdge k W
          (kmswRightBoundaryEdge (fun i => uibhbotFutureCode k W (i + 1)) j.toNat), true) := by
  rw [uibhbotFutureSubmapDartEquiv_val, futureMapBoundaryDart,
    boundaryOuterEdge_of_positive _ h hj]

/-- Helper toward Lemma 5.10. Nonnegative future boundary edges are present
in the whole-plane map, so the missing-boundary face rule does not apply to
these darts. -/
theorem uibhbotFutureSubmap_externalEdge_present_nonnegative (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (j : ℤ) (hj : 0 ≤ j) :
    wholePlaneEdgePresent W (uibhbotFutureEdge k W
      (boundaryOuterEdge (fun i => uibhbotFutureCode k W (i + 1)) h j)) := by
  apply uibhbotFutureEdge_present
  exact (boundaryOuterEdge_endpoints _ h j).2.2.1 hj



theorem ae_uibhbotFutureSubmap_externalEdge_missing_negative :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ j : ℤ, j ≤ -1 →
            ¬ wholePlaneEdgePresent W (uibhbotFutureEdge k W
              (boundaryOuterEdge (fun i => uibhbotFutureCode k W (i + 1)) h j)) := by
  filter_upwards [ae_uibhbotFutureSubmap_edgePresent_iff] with W hp k h j hj hpresent
  have hcode : EdgePresent (fun i => uibhbotFutureCode k W (i + 1))
      (boundaryOuterEdge (fun i => uibhbotFutureCode k W (i + 1)) h j) :=
    (hp k _).2 hpresent
  exact (boundaryOuterEdge_endpoints _ h j).2.2.2 hj hcode





























end DirectedDistances.RandomWalk

