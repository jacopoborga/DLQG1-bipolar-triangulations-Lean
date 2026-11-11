module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso11
public import DirectedDistances.PaperProofs.Section5.GeometricSideClass

/-! The plane side uses the corrected induced rotation and face structure of Iso11.
The marked isomorphism is the geometric identification needed before transporting
code laws; it is not itself the paper's first claim, which is equality in law. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.10. In the common future-code coordinates, the
corrected embedded future side and its KMSW code side agree in every field,
including missing-edge presence, induced rotation, faces, root and both marks. -/
theorem ae_uibhbotFutureInducedPlaneGeometricSide_eq :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              uibhbotFutureInducedPlaneGeometricSide k W h H =
                uibhbotFutureCodeGeometricSide k W h hfin := by
  filter_upwards [ae_uibhbotFutureInducedPlaneGeometricSide_rotation_iff,
    ae_uibhbotFutureInducedPlaneGeometricSide_faceNext_iff,
    ae_uibhbotFutureSubmap_edgePresent_iff]
    with W hrot hface hpresent k h H hfin
  have hp : {e | wholePlaneEdgePresent W (uibhbotFutureEdge k W e)} =
      {e | EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) e} := by
    ext e
    exact (hpresent k e).symm
  have hr : (uibhbotFutureInducedPlaneGeometricSide k W h H).rotation =
      (uibhbotFutureCodeGeometricSide k W h hfin).rotation := by
    funext d e
    exact propext (hrot k h H hfin d e)
  have hf : (uibhbotFutureInducedPlaneGeometricSide k W h H).faceNext =
      (uibhbotFutureCodeGeometricSide k W h hfin).faceNext := by
    funext d e
    exact propext (hface k h H hfin d e)
  dsimp only [uibhbotFutureInducedPlaneGeometricSide, uibhbotFuturePlaneGeometricSide,
    uibhbotFutureCodeGeometricSide] at hr hf ⊢
  congr 1

/-- Helper toward Lemma 5.10. Almost surely, simultaneously at every integer
 boundary hit, the corrected embedded future submap is isomorphic to its
 shifted-code KMSW map as a rooted planar map with both boundary marks. -/
theorem ae_uibhbotFutureInducedPlaneGeometricSide_markedIso :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              Nonempty (GeometricSideMarkedIso
                (uibhbotFutureInducedPlaneGeometricSide k W h H)
                (uibhbotFutureCodeGeometricSide k W h hfin)) := by
  filter_upwards [ae_uibhbotFutureInducedPlaneGeometricSide_eq]
    with W heq k h H hfin
  rw [heq k h H hfin]
  exact ⟨{ equiv := Equiv.refl _, relation_iff := fun _ _ _ => Iff.rfl }⟩

/-- Helper toward Lemma 5.10. The corrected embedded future side has the same
 existing marked geometric-map class as its shifted KMSW code, simultaneously
 for every boundary hit and every choice of construction witnesses. -/
theorem ae_uibhbotFutureInducedPlaneGeometricSide_class_eq :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              geometricSideClass (uibhbotFutureInducedPlaneGeometricSide k W h H) =
                geometricSideClass (uibhbotFutureCodeGeometricSide k W h hfin) := by
  filter_upwards [ae_uibhbotFutureInducedPlaneGeometricSide_eq]
    with W heq k h H hfin
  exact congrArg geometricSideClass (heq k h H hfin)

























































end DirectedDistances.RandomWalk
