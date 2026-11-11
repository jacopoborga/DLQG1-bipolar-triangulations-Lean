module

public import DirectedDistances.PaperProofs.Section4.UIQBOTBoundaryIntervalOrder
public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder7

/-! This file records the proved canonical index bridges and the dart carrier
transport. The full position, endpoint-label, and external-face instances -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the canonical upper-left index is the
constructor's natural-number index. -/
noncomputable def uiqbotCanonicalUpperLeftIndexEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0).upperLeft.Index ≃ ℕ := by
  rw [uiqbotCanonicalBoundaryPresentation_eq]
  rfl

/-- Helper toward Definition 3.2: the canonical lower-right index is the
constructor's natural-number index. -/
noncomputable def uiqbotCanonicalLowerRightIndexEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0).lowerRight.Index ≃ ℕ := by
  rw [uiqbotCanonicalBoundaryPresentation_eq]
  rfl


































































































































/-- Helper toward Definition 3.2: transport KMSW darts bijectively to the
geometric-edge dart carrier, retaining the drawing's dart-orientation bit. -/
noncomputable def uiqbotCanonicalDrawingDartEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    ℕ × Bool ≃ (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool :=
  Equiv.prodCongr (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))
    (Equiv.refl Bool)

/-- Helper toward Definition 3.2: the dart equivalence preserves flipping. -/
theorem uiqbotCanonicalDrawingDartEquiv_flip
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    uiqbotCanonicalDrawingDartEquiv w hfin (d.1, !d.2) =
      ((uiqbotCanonicalDrawingDartEquiv w hfin d).1,
        !(uiqbotCanonicalDrawingDartEquiv w hfin d).2) := by
  cases d with
  | mk e b => rfl

/-- Helper toward Definition 3.2: transport the KMSW rotation to the
geometric-edge dart carrier along the canonical dart equivalence. -/
noncomputable def uiqbotCanonicalDrawingDartRotation
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) :=
  let e := uiqbotCanonicalDrawingDartEquiv w hfin
  e.symm.trans ((kmswInfRot w hfin).trans e)

/-- Helper toward Definition 3.2: the transported rotation commutes with the
canonical dart equivalence. -/
theorem uiqbotCanonicalDrawingDartRotation_compat
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    uiqbotCanonicalDrawingDartRotation w hfin
        (uiqbotCanonicalDrawingDartEquiv w hfin d) =
      uiqbotCanonicalDrawingDartEquiv w hfin (kmswInfRot w hfin d) := by
  simp [uiqbotCanonicalDrawingDartRotation, Equiv.trans_apply]

/-- Helper toward Definition 3.2: the constructor's empty lower-left side
prevents the v3 endpoint predicate for a successor from LR to UL. -/
noncomputable def uiqbotDefinition32PresentationUpperLeftIndexEquiv
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) :
    (uiqbotDefinition32Presentation w htrans hR hL0 M iota).upperLeft.Index ≃ ℕ := by
  unfold uiqbotDefinition32Presentation
  exact Equiv.refl ℕ

/-- Helper toward Definition 3.2: the constructor's lower-right index is
natural-number indexed. -/
noncomputable def uiqbotDefinition32PresentationLowerRightIndexEquiv
    {E : Type*} (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (M : DirectedPlaneMap ℕ E) (iota : ℕ ≃ E) :
    (uiqbotDefinition32Presentation w htrans hR hL0 M iota).lowerRight.Index ≃ ℕ := by
  unfold uiqbotDefinition32Presentation
  exact Equiv.refl ℕ

/-- Helper toward Definition 3.2: supplying the canonical infinite boundary
wrapper reduces the v7 goal exactly to its v3 branch. -/
theorem uiqbotCanonicalBoundaryPresentation_v7_of_v3
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {rot : Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)}
    (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) ℕ
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial
        (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))))
    (U : G.Face)
    (S : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool →
      (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)
    (hinfinite : ¬ (externalBoundaryDartSet4
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))).Finite)
    (h3 : IsExternalFaceIntervalOrder3
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) G U S) :
    IsExternalFaceIntervalOrder7
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
      { presentation := uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0
        finiteJunctions? := none } G U S := by
  apply (IsExternalFaceIntervalOrder7.infinite_iff hinfinite).2
  exact ⟨rfl, h3⟩

end DirectedDistances.PaperProofs.Section4

end

