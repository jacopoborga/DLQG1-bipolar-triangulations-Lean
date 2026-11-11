module

public import DirectedDistances.KMSW.PlaneWitnessInterface
public import DirectedDistances.PaperProofs.Section4.GeoExistPlanar
public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification
public import DirectedDistances.KMSW.LimitExternalFace
public import DirectedDistances.KMSW.InfiniteBoundary

/-! Helper toward Definition 3.8 / Theorem 1.4 (plane realization: outer-face witness of the -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Filter
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization: outer-face witness of the
The two-sided classification supplies the unbounded face and its prescribed successor orbit. -/
theorem twoSided_outerWitness_heq (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) :
    ∃ W : OuterWitness (kmswInfRot w hfin) kmswFlip
        (kmswInfFaceSucc w hfin) futureMapOuterDart,
      HEq W.P (monotoneFamilyDrawing w hfin (monotone_family_all w)) := by
  obtain ⟨U, hU, huniq, hborder, _, _, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided w hfin h
  let p0 := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let hflip : ⇑kmswFlip = fun d => (d.1, !d.2) := kmswFlip_apply
  let p : PLDrawing (ℕ × Bool) ℕ (⇑kmswFlip) (kmswInfRot w hfin)
      (kmswLimitDartVertex w) := hflip.symm ▸ p0
  let W : OuterWitness (kmswInfRot w hfin) kmswFlip
      (kmswInfFaceSucc w hfin) futureMapOuterDart := {
    V := ℕ
    vert := kmswLimitDartVertex w
    P := p
    vert_iff := fun d e => kmswLimitDartVertex_eq_iff_sameCycle w hfin d e
    vert_surj := by
      intro v
      obtain ⟨c, hc⟩ := futureMapVertexId_surjective w hfin v
      revert hc
      refine Quotient.inductionOn c ?_
      intro d hd
      exact ⟨d, (futureMapVertexId_class w hfin d).trans hd⟩
    faceSucc_eq := kmswInfFaceSucc_eq w hfin
    U := U
    U_unb := hU
    U_uniq := huniq
    U_iff := hborder
  }
  refine ⟨W, ?_⟩
  dsimp [W, p, p0]
  cases hflip
  rfl


/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization: outer-face witness of the
The one-sided exterior classification and orbit lemma identify its unbounded face. -/
theorem oneSided_outerWitness_heq (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    ∃ W : OuterWitness (kmswInfRot w hfin) kmswFlip
        (kmswInfFaceSucc w hfin) (kmswLeftBoundaryEdge w 0, false),
      HEq W.P (monotoneFamilyDrawing w hfin (monotone_family_all w)) := by
  obtain ⟨U, hU, huniq, hborder⟩ :=
    monotoneFamilyDrawing_faceClassification w hfin htrans hR hL0
  let p0 := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let hflip : ⇑kmswFlip = fun d => (d.1, !d.2) := kmswFlip_apply
  let p : PLDrawing (ℕ × Bool) ℕ (⇑kmswFlip) (kmswInfRot w hfin)
      (kmswLimitDartVertex w) := hflip.symm ▸ p0
  let W : OuterWitness (kmswInfRot w hfin) kmswFlip
      (kmswInfFaceSucc w hfin) (kmswLeftBoundaryEdge w 0, false) := {
    V := ℕ
    vert := kmswLimitDartVertex w
    P := p
    vert_iff := fun d e => kmswLimitDartVertex_eq_iff_sameCycle w hfin d e
    vert_surj := by
      intro v
      obtain ⟨c, hc⟩ := futureMapVertexId_surjective w hfin v
      revert hc
      refine Quotient.inductionOn c ?_
      intro d hd
      exact ⟨d, (futureMapVertexId_class w hfin d).trans hd⟩
    faceSucc_eq := kmswInfFaceSucc_eq w hfin
    U := U
    U_unb := hU
    U_uniq := huniq
    U_iff := by
      intro d
      exact (hborder d).trans
        (limitExternalDart_iff_sameCycle w hfin htrans hR hL0 d)
  }
  refine ⟨W, ?_⟩
  dsimp [W, p, p0]
  cases hflip
  rfl


end DirectedDistances.KMSW
