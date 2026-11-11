module

public import DirectedDistances.KMSW.KMSWConstructedRealization
public import DirectedDistances.KMSW.CutEquivalence
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.PlanarMap.GeneralPlaneMap

/-! Helper toward Definition 4.1: identify KMSW edge IDs with geometric edges. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Definition 4.1: KMSW edge identities correspond bijectively
with the flip-orbit geometric edges of a constructed plane drawing. The two
Boolean darts have the same edge identity, and the flip changes only that bit. -/
@[expose] noncomputable def kmswGeometricEdgeEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨
       (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) :
    ℕ ≃ P.GeometricEdge := by
  let f : ℕ → P.GeometricEdge := fun e => Quotient.mk P.edgeSetoid (e, false)
  let g : P.GeometricEdge → ℕ :=
    Quotient.lift (fun d : ℕ × Bool => d.1) (by
      intro d e he
      rcases he with he | he
      · exact congrArg Prod.fst he
      · simpa using congrArg Prod.fst he)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro e₁ e₂ he
    have hg := congrArg g he
    simpa [f, g] using hg
  · intro q
    refine Quotient.inductionOn q ?_
    intro d
    rcases d with ⟨e, b⟩
    refine ⟨e, ?_⟩
    cases b
    · rfl
    · change Quotient.mk P.edgeSetoid (e, false) =
        Quotient.mk P.edgeSetoid (e, true)
      exact Quotient.sound (Or.inr rfl)

@[simp] theorem kmswGeometricEdgeEquiv_apply
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨
       (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (e : ℕ) :
    kmswGeometricEdgeEquiv w hfin P e =
      Quotient.mk P.edgeSetoid (e, false) := rfl

@[simp] theorem kmswGeometricEdgeEquiv_dart
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨
       (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (e : ℕ) (b : Bool) :
    Quotient.mk P.edgeSetoid (e, b) = kmswGeometricEdgeEquiv w hfin P e := by
  cases b
  · rfl
  · rw [kmswGeometricEdgeEquiv_apply]
    exact P.geometricEdge_flip (e, false)

/-- Helper toward Definition 4.1: orient each flip-orbit class from its west
endpoint to its east endpoint, using the dart representative only to choose
which way the general drawing's stored endpoints are read. -/
theorem kmswConstructedDrawing_directedMap_compat
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨
       (kmswStage w n).east e = v)}.Finite)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w)) :
    ∃ M : DirectedPlaneMap ℕ P.GeometricEdge,
      ∃ iota : ℕ ≃ P.GeometricEdge,
        M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
        ∀ e, M.tail (iota e) = edgeWest w e ∧ M.head (iota e) = edgeEast w e := by
  let M : DirectedPlaneMap ℕ P.GeometricEdge :=
    { toPlaneGraphDrawing := P.toPlaneGraphDrawing
      forward := fun q => !q.out.2 }
  let iota := kmswGeometricEdgeEquiv w hfin P
  refine ⟨M, iota, rfl, ?_⟩
  intro e
  have hiota : iota e = Quotient.mk P.edgeSetoid (e, false) :=
    kmswGeometricEdgeEquiv_apply w hfin P e
  have htail (q : P.GeometricEdge) :
      M.tail q = (if !q.out.2 then kmswLimitDartVertex w q.out
        else kmswLimitDartVertex w (q.out.1, !q.out.2)) := by rfl
  have hhead (q : P.GeometricEdge) :
      M.head q = (if !q.out.2 then kmswLimitDartVertex w (q.out.1, !q.out.2)
        else kmswLimitDartVertex w q.out) := by rfl
  rw [hiota, htail, hhead]
  obtain hout | hout := P.geometricEdge_out_mk (e, false)
  · rw [hout]
    simp [kmswLimitDartVertex, edgeWest, edgeEast]
  · rw [hout]
    simp [kmswLimitDartVertex, edgeWest, edgeEast]

/-- Helper toward Definition 4.1: the drawing witness supplied by the
constructed-realization statement carries the directed KMSW edge identities. -/
theorem kmswConstructedPlaneRealization_compatibility
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨
       (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (hreal : KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0) :
    ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w),
      ∃ M : DirectedPlaneMap ℕ P.GeometricEdge,
        ∃ iota : ℕ ≃ P.GeometricEdge,
          M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
          ∀ e, M.tail (iota e) = edgeWest w e ∧ M.head (iota e) = edgeEast w e := by
  dsimp [KMSWConstructedPlaneRealizationStatement] at hreal
  rcases hreal with ⟨Q, hQ, P, hPos, hArc, U, hUnbounded, hUnique, hBorders⟩
  exact ⟨P, kmswConstructedDrawing_directedMap_compat w hfin P⟩

end DirectedDistances.KMSW

