module

public import DirectedDistances.PlanarMap.EdgeRestrictedDrawing
public import DirectedDistances.KMSW.MhatPrimeGeometricCarrier
public import DirectedDistances.KMSW.MonotoneStageFamily
public import DirectedDistances.KMSW.StageTriangleBoundedFace

/-! Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
variable (hb : BoundaryHitWitnesses w)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def primeDartSet : Set (ℕ × Bool) :=
  {d | primeGeomEdge w hfin hb d.1}

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The retained dart set is closed under the ambient flip -/
theorem primeDartSet_flip_closed (d : ℕ × Bool) :
    d ∈ primeDartSet w hfin hb ↔ (d.1, !d.2) ∈ primeDartSet w hfin hb := by
  change primeGeomEdge w hfin hb d.1 ↔ primeGeomEdge w hfin hb d.1
  rfl

variable (hfam : ∀ n, ∃ h : LayoutGood w n,
  Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)))

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The primed drawing restricts the ambient realization to retained geometric darts -/
@[expose] noncomputable def mhatPrimeDrawing :=
  restrictDrawing (monotoneFamilyDrawing w hfin hfam)
    (primeDartSet w hfin hb) (primeDartSet_flip_closed w hfin hb)

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Restricted ambient darts are identified with primed geometric darts -/
@[expose] def restrictedDartEquivPrimeDart :
    RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb) ≃ PrimeDart w hfin hb where
  toFun d := ⟨⟨d.1.1, d.2⟩, d.1.2⟩
  invFun d := ⟨(d.1.1, d.2), d.1.2⟩
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv d := by
    cases d with
    | mk e b =>
      cases e with
      | mk edge h =>
        rfl

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The dart equivalence preserves edge IDs -/
theorem restrictedDartEquivPrimeDart_edgeId
    (d : RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb)) :
    (restrictedDartEquivPrimeDart w hfin hb d).1.1 = d.1.1 := rfl

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The primed dart arc is inherited from the ambient realization -/
theorem mhatPrimeDrawing_arc
    (d : RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb)) :
    (mhatPrimeDrawing w hfin hb hfam).arc d =
      (monotoneFamilyDrawing w hfin hfam).arc d.1 := by
  exact restrictDrawing_arc _ _ _ _

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The primed vertex position is inherited from the ambient realization -/
theorem mhatPrimeDrawing_pos
    (v : RestrictedVertex (monotoneFamilyDrawing w hfin hfam)
      (primeDartSet w hfin hb)) :
    (mhatPrimeDrawing w hfin hb hfam).pos v =
      (monotoneFamilyDrawing w hfin hfam).pos v.1 := by
  exact restrictDrawing_pos _ _ _ _

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The primed drawing image is contained in the ambient image -/
theorem mhatPrimeDrawing_image_subset :
    (mhatPrimeDrawing w hfin hb hfam).image ⊆
      (monotoneFamilyDrawing w hfin hfam).image := by
  exact restrictDrawing_image_subset _ _ _

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Bounded complementary components of the primed drawing -/
@[expose] def MhatPrimeFaces := PlaneFaces (mhatPrimeDrawing w hfin hb hfam)

end DirectedDistances.KMSW
