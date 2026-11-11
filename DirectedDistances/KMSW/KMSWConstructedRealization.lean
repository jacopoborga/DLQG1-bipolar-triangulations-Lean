module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.KMSW.KMSWStageDrawing
public import DirectedDistances.KMSW.LimitExternalFace











public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW DirectedDistances.RandomWalk Filter







@[expose] def KMSWConstructedPlaneRealizationStatement (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_htrans : Tendsto (L w) atTop atTop) (_hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (_hL0 : ∀ j, 0 ≤ L w j) : Prop :=
  let Drawing := PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot w hfin) (kmswLimitDartVertex w)
  ∃ Q : ∀ n, StageDrawing w n,
    (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
    ∃ P : Drawing,
      (∀ n v, P.pos v.val = (Q n).pos v) ∧
      (∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d) ∧
      ∃ U : P.Face,
        P.IsUnbounded U ∧
        (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        ∀ d, P.dartBorders d U ↔ limitExternalDart w d

/-- A persistent upper-left edge gives a left-bordering dart in any drawing
whose external-face classification is `limitExternalDart` -/
theorem limitLeftBoundaryEdge_dartBorders (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d)
    (hleft : limitLeftBoundaryEdge w e) : P.dartBorders (e, false) U := by
  apply (hU (e, false)).2
  obtain ⟨N, hN⟩ := hleft
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h, ho⟩ := hN n hn
  exact ⟨h, ho.2.2⟩

/-- A persistent lower-right edge gives a left-bordering dart in its reversed
orientation in any drawing with the classified external face -/
theorem limitRightBoundaryEdge_dartBorders (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d)
    (hright : limitRightBoundaryEdge w e) : P.dartBorders (e, true) U := by
  apply (hU (e, true)).2
  obtain ⟨N, hN⟩ := hright
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h, ho⟩ := hN n hn
  exact ⟨h, ho.2.2⟩

/-- With the hypotheses classifying all persistent external darts, the converse
also holds: finite-stage outer membership alone does not identify upper-left
membership, since missing and other boundary darts can be outer -/
theorem dartBorders_iff_limitLeftBoundaryEdge (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d) :
    P.dartBorders (e, false) U ↔ limitLeftBoundaryEdge w e := by
  constructor
  · intro hB
    have hex := (hU (e, false)).1 hB
    have hc := (limitExternalDart_iff w htrans hR hL0 (e, false)).1 hex
    rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
    · have he := congrArg Prod.fst hi
      exact (limitLeftBoundaryEdge_iff w htrans e).2 ⟨i, he⟩
    · have hb := congrArg Prod.snd hi
      cases hb
  · exact limitLeftBoundaryEdge_dartBorders w hfin P U hU

/-- With the hypotheses classifying all persistent external darts, the converse
also holds for the lower-right ray; the eventual external-dart classification -/
theorem dartBorders_iff_limitRightBoundaryEdge (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) (U : P.Face)
    (hU : ∀ d, P.dartBorders d U ↔ limitExternalDart w d) :
    P.dartBorders (e, true) U ↔ limitRightBoundaryEdge w e := by
  constructor
  · intro hB
    have hex := (hU (e, true)).1 hB
    have hc := (limitExternalDart_iff w htrans hR hL0 (e, true)).1 hex
    rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hb := congrArg Prod.snd hi
      cases hb
    · have he := congrArg Prod.fst hi
      exact (limitRightBoundaryEdge_iff w hR e).2 ⟨i, he⟩
  · exact limitRightBoundaryEdge_dartBorders w hfin P U hU

end DirectedDistances.PlanarMap
