module

public import DirectedDistances.KMSW.KMSWConstructedRealization
public import DirectedDistances.KMSW.UIQBOTCutVertex

/- # Boundary vertices of a classified constructed drawing

Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv
No existence or uniqueness of a constructed drawing is asserted here. -/

public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW Filter

variable (w : ℕ → Fin 3)
variable {hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}

/- Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv
Left boundary membership means endpoint membership of a dart bordering the given face. -/
@[expose] def TopLeftBoundaryVertex
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face) (v : ℕ) : Prop :=
  ∃ e, P.dartBorders (e, false) U ∧ (edgeWest w e = v ∨ edgeEast w e = v)

/- Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv
Right boundary membership uses the reversed dart bordering the given face. -/
@[expose] def TopRightBoundaryVertex
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face) (v : ℕ) : Prop :=
  ∃ e, P.dartBorders (e, true) U ∧ (edgeWest w e = v ∨ edgeEast w e = v)

/- Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv -/
theorem topLeftBoundaryVertex_iff_uiqbotLeftBoundaryVertex
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d) (v : ℕ) :
    TopLeftBoundaryVertex w P U v ↔ uiqbotLeftBoundaryVertex w v := by
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e, (dartBorders_iff_limitLeftBoundaryEdge w hfin htrans hR hL0 P U hU).1 he,
      hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨e, (dartBorders_iff_limitLeftBoundaryEdge w hfin htrans hR hL0 P U hU).2 he,
      hv⟩

/- Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv -/
theorem topRightBoundaryVertex_iff_uiqbotRightBoundaryVertex
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d) (v : ℕ) :
    TopRightBoundaryVertex w P U v ↔ uiqbotRightBoundaryVertex w v := by
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e, (dartBorders_iff_limitRightBoundaryEdge w hfin htrans hR hL0 P U hU).1 he,
      hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨e, (dartBorders_iff_limitRightBoundaryEdge w hfin htrans hR hL0 P U hU).2 he,
      hv⟩

/- Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv
The two drawings may use different proofs of finite incidence. -/
theorem topLeftBoundaryVertex_iff_of_classified
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d)
    {hfin' : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (P' : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin') (kmswLimitDartVertex w)) (U' : P'.Face)
    (hU' : ∀ d, P'.dartBorders d U' ↔ limitExternalDart w d) (v : ℕ) :
    TopLeftBoundaryVertex w P U v ↔ TopLeftBoundaryVertex w P' U' v := by
  exact (topLeftBoundaryVertex_iff_uiqbotLeftBoundaryVertex w htrans hR hL0 P U hU v).trans
    (topLeftBoundaryVertex_iff_uiqbotLeftBoundaryVertex w htrans hR hL0 P' U' hU' v).symm

/- Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv
The two drawings may use different proofs of finite incidence. -/
theorem topRightBoundaryVertex_iff_of_classified
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d)
    {hfin' : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (P' : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin') (kmswLimitDartVertex w)) (U' : P'.Face)
    (hU' : ∀ d, P'.dartBorders d U' ↔ limitExternalDart w d) (v : ℕ) :
    TopRightBoundaryVertex w P U v ↔ TopRightBoundaryVertex w P' U' v := by
  exact (topRightBoundaryVertex_iff_uiqbotRightBoundaryVertex w htrans hR hL0 P U hU v).trans
    (topRightBoundaryVertex_iff_uiqbotRightBoundaryVertex w htrans hR hL0 P' U' hU' v).symm

/- Helper toward def-cut-vertex / prop-cut-vertex / lem-cut-equiv -/
theorem topBoundaryVertices_iff_uiqbotCutVertex
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d) (v : ℕ) :
    (TopLeftBoundaryVertex w P U v ∧ TopRightBoundaryVertex w P U v) ↔
      uiqbotCutVertex w v := by
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨(topLeftBoundaryVertex_iff_uiqbotLeftBoundaryVertex w htrans hR hL0 P U hU v).1 hl,
      (topRightBoundaryVertex_iff_uiqbotRightBoundaryVertex w htrans hR hL0 P U hU v).1 hr⟩
  · rintro ⟨hl, hr⟩
    exact ⟨(topLeftBoundaryVertex_iff_uiqbotLeftBoundaryVertex w htrans hR hL0 P U hU v).2 hl,
      (topRightBoundaryVertex_iff_uiqbotRightBoundaryVertex w htrans hR hL0 P U hU v).2 hr⟩

end DirectedDistances.PlanarMap
