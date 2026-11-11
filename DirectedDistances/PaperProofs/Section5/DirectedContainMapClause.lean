/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.DirectedContainIdentified
public import DirectedDistances.KMSW.HatFaceOrbitEquiv

/-! Supporting lemmas for paper labels `lem-directed-contain` (see CORRESPONDENCE.md). -/

/-! # The rooted planar-map clause of Lemma 5.2

The strong Markov code law transfers flow hits, finite incidence and compressed
left transience to every boundary-hit future on a single probability-one event.
The rooted dart/rotation/face identification then identifies the hatted code's
map with the reachable restricted drawing. The vertex and arrow equivalences
below identify that drawing's directed multigraph with the path-lift carrier. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap





@[expose] def hatRootedMapClause (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) : Prop :=
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := hatRealizedDrawing w hfin
    let S := {d : ℕ × Bool | MhatGeometricEdge w d.1}
    ∃ (H : (ℕ × Bool) ≃ {d : ℕ × Bool // MhatGeometricEdge w d.1})
      (F : HatFaceOrbit w h hfin ≃ Q.Face),
      (∀ d, (H d).val = (hatLimitEdgeMap w h d.1, d.2)) ∧
      (H futureMapRootDart).val = futureMapRootDart ∧
      (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
      (∀ d, futureMapMissing (hatCodes w h) d ↔ futureMapMissing w (H d).val) ∧
      (∀ d, futureMapTail (hatCodes w h) d ↔ futureMapTail w (H d).val) ∧
      (∀ e, edgeWest w (hatLimitEdgeMap w h e) =
          hatLimitVertexMap w h (edgeWest (hatCodes w h) e) ∧
        edgeEast w (hatLimitEdgeMap w h e) =
          hatLimitVertexMap w h (edgeEast (hatCodes w h) e)) ∧
      (∀ d, H (kmswInfRot (hatCodes w h) (hatCodes_finiteIncidence w h hfin) d) =
        drawingFirstReturnPerm P S (H d)) ∧
      (∀ d, H (kmswInfFaceSucc (hatCodes w h) (hatCodes_finiteIncidence w h hfin) d) =
        (drawingFirstReturnPerm P S).symm (restrictedFlip P S (fun _ => Iff.rfl) (H d))) ∧
      (∀ d q, Q.dartBorders (H d) (F q) ↔ Quotient.mk _ d = q) ∧
      (∀ q, Q.IsUnbounded (F q) ↔ q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, Q.dartBorders (H d) (F (Quotient.mk _ futureMapOuterDart)) ↔
        limitExternalDart (hatCodes w h) d)



theorem hatRootedMapClause_of_left_transient (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop) :
    hatRootedMapClause w h hfin :=
  hatRootedMapIdentification w h hfin htrans




theorem wholePlane_ae_boundaryFutureCode_hatRootedMapHypotheses :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ,
      let u := fun i => boundaryFutureCode k W (i + 1)
      ∃ _h : HasFlowLineHits u,
        hatLimitFiniteIncidence u ∧
        ∀ h' : HasFlowLineHits u,
          Filter.Tendsto (L (hatCodes u h')) Filter.atTop Filter.atTop := by
  have hiid : ∀ᵐ ω ∂iidCodeMeasure,
      let u := fun i => ω (i + 1)
      ∃ _h : HasFlowLineHits u,
        hatLimitFiniteIncidence u ∧
        ∀ h' : HasFlowLineHits u,
          Filter.Tendsto (L (hatCodes u h')) Filter.atTop Filter.atTop := by
    filter_upwards [iidCodeMeasure_ae_hasFlowLineHits,
      iidCodes_ae_finite_incident_edges, iidCodes_ae_hatCodes_left_transient]
      with ω hflow hfin htrans
    exact ⟨hflow, hfin, htrans⟩
  apply ae_all_iff.mpr
  intro k
  have hm : ∀ᵐ ω ∂wholePlaneIIDCodeMeasure.map (boundaryFutureCode k),
      let u := fun i => ω (i + 1)
      ∃ _h : HasFlowLineHits u,
        hatLimitFiniteIncidence u ∧
        ∀ h' : HasFlowLineHits u,
          Filter.Tendsto (L (hatCodes u h')) Filter.atTop Filter.atTop := by
    rw [boundaryFutureCode_law]
    exact hiid
  exact (Measure.tendsto_ae_map
    (measurable_boundaryFutureCode k).aemeasurable).eventually hm




theorem wholePlane_ae_boundaryShift_hatRootedMapHypotheses :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ h : BoundaryHitWitnesses (shiftedStream W 0), ∀ k : ℤ,
        let u := fun i => shiftedStream W 0
          (boundaryHitTime (shiftedStream W 0) h k + i)
        ∃ _hτ : HasFlowLineHits u,
          hatLimitFiniteIncidence u ∧
          ∀ h' : HasFlowLineHits u,
            Filter.Tendsto (L (hatCodes u h')) Filter.atTop Filter.atTop := by
  filter_upwards [wholePlane_ae_boundaryFutureCode_hatRootedMapHypotheses] with W hW
  intro h k
  have hk := hW k
  dsimp only at hk ⊢
  rw [boundaryFutureCode_tail W h k] at hk
  exact hk




theorem hatRealizedVertex_iff_reachable (w : ℕ → Fin 3) (v : ℕ) :
    (∃ d : ℕ × Bool, MhatGeometricEdge w d.1 ∧
      kmswLimitDartVertex w d = v) ↔ MhatVertex w v := by
  constructor
  · rintro ⟨⟨e, b⟩, he, hv⟩
    cases b
    · change edgeWest w e = v at hv
      exact hv ▸ he.1
    · change edgeEast w e = v at hv
      exact hv ▸ he.2
  · rintro ⟨p⟩
    cases p with
    | nil =>
      have e : (⟨0⟩ : PresentVertex w) ⟶ ⟨edgeEast w 0⟩ :=
        ⟨0, futureMap_root_present w, rfl, rfl⟩
      exact ⟨(0, false), ⟨Reachable.refl _, ⟨e.toPath⟩⟩, rfl⟩
    | @cons b c p e =>
      refine ⟨(e.val, true), ⟨?_, ?_⟩, ?_⟩
      · change Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e.val⟩
        rw [e.property.2.1]
        exact ⟨p⟩
      · change Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e.val⟩
        rw [e.property.2.2]
        exact ⟨p.cons e⟩
      · exact e.property.2.2



@[expose] def hatRealizedVertexEquiv (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) :
    RestrictedVertex (monotoneFamilyDrawing w hfin (monotone_family_all w))
      {d : ℕ × Bool | MhatGeometricEdge w d.1} ≃
      {b : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) b} where
  toFun v := ⟨⟨v.val⟩, (hatRealizedVertex_iff_reachable w v.val).mp v.property⟩
  invFun b := ⟨b.val.id, (hatRealizedVertex_iff_reachable w b.val.id).mpr b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl




@[expose] def hatRealizedArrowEquiv (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w)
    (a b : RestrictedVertex (monotoneFamilyDrawing w hfin (monotone_family_all w))
      {d : ℕ × Bool | MhatGeometricEdge w d.1}) :
    {e : ℕ // MhatGeometricEdge w e ∧ EdgePresent w e ∧
      edgeWest w e = a.val ∧ edgeEast w e = b.val} ≃
      ((hatRealizedVertexEquiv w hfin a).val ⟶
        (hatRealizedVertexEquiv w hfin b).val) where
  toFun e := ⟨e.val, e.property.2⟩
  invFun e := ⟨e.val, ⟨by
    constructor
    · rw [e.property.2.1]
      exact (hatRealizedVertexEquiv w hfin a).property
    · rw [e.property.2.2]
      exact (hatRealizedVertexEquiv w hfin b).property, e.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl





@[expose] def boundaryFutureRootedMapClause (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) : Prop :=
  let u := fun i => shiftedStream W 0
    (boundaryHitTime (shiftedStream W 0) h k + i)
  ∃ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
    hatLawCodes (boundaryFutureCode k W) = hatCodes u hτ ∧
    hatRootedMapClause u hτ hfin



theorem wholePlane_ae_boundaryFutureRootedMapClause :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ h : BoundaryHitWitnesses (shiftedStream W 0), ∀ k : ℤ,
        boundaryFutureRootedMapClause W h k := by
  filter_upwards [wholePlane_ae_boundaryShift_hatRootedMapHypotheses] with W hW
  intro h k
  obtain ⟨hτ, hfin, htrans⟩ := hW h k
  exact ⟨hτ, hfin, boundaryFuture_hatLawCodes_eq_hatCodes W h k hτ,
    hatRootedMapClause_of_left_transient _ hτ hfin (htrans hτ)⟩




@[expose] def lemma52FullStatement : Prop :=
  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    ∃ H : WholePlaneRotationHypothesis W,
    ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
    ∀ k : ℤ,
      wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
        wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
      wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
        iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
      (fun i => boundaryFutureCode k W (i + 1)) =
        (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)) ∧
      (∃ hτ : HasFlowLineHits
          (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)),
        hatLawCodes (boundaryFutureCode k W) =
          hatCodes (fun i => shiftedStream W 0
            (boundaryHitTime (shiftedStream W 0) h k + i)) hτ) ∧
      M0CutShiftContainment W H h hLL k ∧
      boundaryFutureRootedMapClause W h k



theorem lemma52Full_holds : lemma52FullStatement := by
  unfold lemma52FullStatement
  have hc := lemma52_code_and_path_statement
  unfold lemma52Statement at hc
  filter_upwards [hc, wholePlane_ae_boundaryFutureRootedMapClause] with W hc hm
  obtain ⟨H, h, hLL, hc⟩ := hc
  refine ⟨H, h, hLL, fun k => ?_⟩
  obtain ⟨hlaw, hhatlaw, htail, hcode, hpath⟩ := hc k
  exact ⟨hlaw, hhatlaw, htail, hcode, hpath, hm h k⟩

end DirectedDistances.PaperProofs.Section5
