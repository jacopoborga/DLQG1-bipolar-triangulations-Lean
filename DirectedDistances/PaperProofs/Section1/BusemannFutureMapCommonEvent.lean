/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BusemannCommonEventBridge
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary

/-! Helper toward Theorem 1.4 (thm-busemann); not a paper result. Source:
This combines the common code-side Busemann event with the future-map boundary
labelling on the same finite-incidence and boundary-hit witnesses. The
code-side carrier is used; source binding open. -/

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Theorem 1.4 (thm-busemann); not a paper result.
For one iid-code event, the unique LDP and SDP code predicates share the same
finite-incidence and hit witnesses as the future-map boundary vertex and face
successor identities. This is a code-side carrier; source binding open. -/
theorem iidCodes_ae_boundaryBusemann_futureMap_common :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses w,
        (∃! X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin w hfin)
            (boundaryPresentVertex w h) X) ∧
        (∃! X : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex w h) X) ∧
        (∀ k : ℤ,
          futureMapVertexEquiv w hfin
            (rootedLocallyFiniteVertexClass (kmswInfRot w hfin)
              (futureMapBoundaryDart w h (k - 1))) =
                boundaryPresentVertex w h k) ∧
        (∀ k : ℤ,
          kmswInfFaceSucc w hfin (futureMapBoundaryDart w h k) =
            futureMapBoundaryDart w h (k - 1)) := by
  filter_upwards [iidCodes_ae_boundaryBusemann_common] with ω hω
  obtain ⟨hfin, h, hLDP, hSDP⟩ := hω
  refine ⟨hfin, h, hLDP, hSDP, ?_, ?_⟩
  · intro k
    rw [futureMapVertexEquiv_class]
    apply congrArg (fun n => (⟨n⟩ : PresentVertex (fun i => ω (i + 1))))
    exact futureMap_outerVertex_eq_boundaryVertex (fun i => ω (i + 1)) h k
  · intro k
    exact futureMapBoundaryDart_faceSucc
      (w := fun i => ω (i + 1)) (hfin := hfin) h k

end DirectedDistances.PaperProofs.Section1
