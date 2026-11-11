/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.DirectedContainMapClause
public import DirectedDistances.PaperProofs.Section5.QuadrantWalk
public import DirectedDistances.KMSW.PrimedExternalCycle
public import DirectedDistances.KMSW.QuadrantCodesIncrements
import DirectedDistances.KMSW.PrimedInteriorArcBridge

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Joint source-walk and rooted-map identification for Lemma 5.13

The literal selected-time source walks are identified with the codes used by
both rooted geometric maps on one iid event. The primed map retains its
missing, unoriented root under C18, and uses the initial triangle convention first-triangle convention.
The bounded-face exclusion is proved on the same witnesses, not assumed. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap




@[expose] def primedRootedMapClause (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) : Prop :=
    let u := primedCode (primedSimInput w) h
    let hf := primedCode_finiteIncidence w h hfin
    let ρ := kmswInfRot u hf
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    let S := primeDartSet w hfin hb
    ∃ (H : (ℕ × Bool) ≃ {d // d ∈ S})
      (V : RootedLocallyFiniteVertex (ℕ × Bool) ρ ≃ RestrictedVertex P S)
      (F : PrimedFaceOrbit w h hfin ≃ Q.Face),
      (∀ d, (H d).val = primedLimitDartMap w h d) ∧
      (∀ d, V (rootedLocallyFiniteVertexClass ρ d) = restrictedVertex P S (H d)) ∧
      (H futureMapRootDart).val = (kmswLLCreatedEdge w (walkNL w h 0), false) ∧
      primeMissingEdge w hfin hb (H futureMapRootDart).val.1 ∧
      ¬ PrimedEdgePresent w h 0 ∧
      (∀ d, d.1 = 0 → ¬ ((H d).val.2 = false ∧ primePresentEdge w (H d).val.1)) ∧
      (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
      (∀ d, ¬ PrimedEdgePresent w h d.1 ↔ primeMissingEdge w hfin hb (H d).val.1) ∧
      (∀ d, PrimedEdgePresent w h d.1 ↔ primePresentEdge w (H d).val.1) ∧
      (∀ d, (d.2 = false ∧ PrimedEdgePresent w h d.1) ↔
        ((H d).val.2 = false ∧ primePresentEdge w (H d).val.1)) ∧
      (∀ d, kmswLimitDartVertex w (H d).val =
        primedLimitVertexMap w h (kmswLimitDartVertex u d)) ∧
      (∀ d, H (ρ d) = drawingFirstReturnPerm P S (H d)) ∧
      (∀ d, H (kmswInfFaceSucc u hf d) =
        (drawingFirstReturnPerm P S).symm
          (restrictedFlip P S (primeDartSet_flip_closed w hfin hb) (H d))) ∧
      (∀ d q, Q.dartBorders (H d) (F q) ↔ Quotient.mk _ d = q) ∧
      (∀ q, Q.IsUnbounded (F q) ↔ q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, Q.dartBorders (H d) (F (Quotient.mk _ futureMapOuterDart)) ↔
        limitExternalDart u d)



theorem primedRootedMapClause_holds (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedRootedMapClause w h hfin hb :=
  primedRootedMapIdentification w h hfin hb
    (primedBoundedFace_deletedGeometryExclusionGoal_holds w h hfin hb)




theorem quadrantPrimedSourceWalk_eq_integrateCodes_primedCode
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    quadrantPrimedSourceWalk w h = integrateCodes (primedCode (primedSimInput w) h) := by
  simpa only [primedSimInput, quadrantPrimedIntervalWalk] using
    quadrantPrimedSourceWalk_eq_quadrantPrimedIntervalWalk (primedSimInput w) h






@[expose] def lemma513Statement : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (hfin_hat : hatLimitFiniteIncidence w)
      (hfin_primed : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w),
      sourceQuadrantHatWalk w h = integrateCodes (hatCodes w h) ∧
      sourceQuadrantPrimedWalk w h = integrateCodes (primedCode (primedSimInput w) h) ∧
      hatRootedMapClause w h hfin_hat ∧
      primedRootedMapClause w h hfin_primed hb




theorem lemma513_holds : lemma513Statement := by
  unfold lemma513Statement
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses,
    iidCodes_ae_hatCodes_left_transient] with ω h hfin hb htrans
  refine ⟨h, hfin, hfin, hb, ?_, ?_,
    hatRootedMapClause_of_left_transient _ h hfin (htrans h),
    primedRootedMapClause_holds _ h hfin hb⟩
  · exact (sourceQuadrantHatWalk_eq_quadrantHatSourceWalk _ h).trans
      (quadrantHatSourceWalk_eq_integrateCodes_hatCodes _ h)
  · exact (sourceQuadrantPrimedWalk_eq_quadrantPrimedSourceWalk _ h).trans
      (quadrantPrimedSourceWalk_eq_integrateCodes_primedCode _ h)

end DirectedDistances.PaperProofs.Section5
