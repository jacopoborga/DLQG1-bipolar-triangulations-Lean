module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTFutureSubmapIdentification
public import DirectedDistances.RandomWalk.UIBHBOTFutureMissingEdgeReflection

/-! The future code edge IDs retain both their present status and their geometric
endpoint-side tags in the whole-plane submap. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW

/-- Helper toward Lemma 5.10. Almost surely, simultaneously for every boundary
index and every future suffix edge, code presence is equivalent to presence of
its whole-plane geometric image. -/
theorem ae_uibhbotFutureSubmap_edgePresent_iff :
    ∀ᵐ W ∂(DirectedDistances.PaperProofs.Section5.uibhbotCodeLawRel :
      Measure (ℤ → Fin 3)), ∀ k : ℤ, ∀ e : ℕ,
        EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) e ↔
          wholePlaneEdgePresent W (uibhbotFutureEdge k W e) := by
  filter_upwards [uibhbotFutureMissingEdgeReflection_ae] with W href k e
  constructor
  · exact uibhbotFutureEdge_present k W e
  · intro hglobal
    by_contra hcode
    exact href k e hcode hglobal

/-- Helper toward Lemma 5.10. Repackage a submap edge and endpoint bit as a
whole-plane dart in the submap carrier. -/
@[expose] def uibhbotFutureSubmapDartSubtypeEquiv (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) :
    ({e : WholePlaneEdge W // e ∈ (uibhbotFutureSubmap k W h).edges} × Bool) ≃
      {d : WholePlaneDart W // d.1 ∈ (uibhbotFutureSubmap k W h).edges} where
  toFun p := ⟨(p.1.1, p.2), p.1.2⟩
  invFun d := (⟨d.1.1, d.2⟩, d.1.2)
  left_inv := by rintro ⟨⟨e, he⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨e, b⟩, he⟩; rfl

/-- Helper toward Lemma 5.10. The future-code dart carrier, including both
endpoint sides of missing geometric edges, is equivalent to the darts of the
whole-plane geometric submap. -/
@[expose] noncomputable def uibhbotFutureSubmapDartEquiv (k : ℤ)
    (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) :
    (ℕ × Bool) ≃
      {d : WholePlaneDart W // d.1 ∈ (uibhbotFutureSubmap k W h).edges} :=
  (Equiv.prodCongr (uibhbotFutureSubmapEdgeEquiv k W h) (Equiv.refl Bool)).trans
    (uibhbotFutureSubmapDartSubtypeEquiv k W h)

/-- Helper toward Lemma 5.10. The dart equivalence acts by the future edge map
and preserves its endpoint-side bit. -/
theorem uibhbotFutureSubmapDartEquiv_val (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (d : ℕ × Bool) :
    (uibhbotFutureSubmapDartEquiv k W h d).1 =
      (uibhbotFutureEdge k W d.1, d.2) := by
  simp only [uibhbotFutureSubmapDartEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply,
    uibhbotFutureSubmapDartSubtypeEquiv, uibhbotFutureSubmapEdgeEquiv]
  exact Prod.ext rfl rfl

/-- Helper toward Lemma 5.10. The dart equivalence preserves the endpoint-side
bit; its false and true sides commute with the west (tail) and east (head)
endpoint maps of the directed future code. -/
theorem uibhbotFutureSubmapDartEquiv_endpoint (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (d : ℕ × Bool) :
    wholePlaneDartVertex W ((uibhbotFutureSubmapDartEquiv k W h d).1) =
      uibhbotFutureVertex k W
        (if d.2 then edgeEast (fun i => uibhbotFutureCode k W (i + 1)) d.1
          else edgeWest (fun i => uibhbotFutureCode k W (i + 1)) d.1) := by
  rw [uibhbotFutureSubmapDartEquiv_val]
  cases d with
  | mk e b =>
      cases b <;>
        simp [wholePlaneDartVertex, uibhbotFutureEdge_west,
          uibhbotFutureEdge_east]

/-- Helper toward Lemma 5.10. The opposite side of the image dart gives the
future code's other endpoint, so the induced dart equivalence commutes with
both dart endpoints (tail and head). -/
theorem uibhbotFutureSubmapDartEquiv_tail_head (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (d : ℕ × Bool) :
    wholePlaneDartVertex W ((uibhbotFutureSubmapDartEquiv k W h d).1) =
        uibhbotFutureVertex k W
          (if d.2 then edgeEast (fun i => uibhbotFutureCode k W (i + 1)) d.1
            else edgeWest (fun i => uibhbotFutureCode k W (i + 1)) d.1) ∧
      wholePlaneDartVertex W
          (wholePlaneDartFlip W ((uibhbotFutureSubmapDartEquiv k W h d).1)) =
        uibhbotFutureVertex k W
          (if d.2 then edgeWest (fun i => uibhbotFutureCode k W (i + 1)) d.1
            else edgeEast (fun i => uibhbotFutureCode k W (i + 1)) d.1) := by
  constructor
  · exact uibhbotFutureSubmapDartEquiv_endpoint k W h d
  · cases d with
    | mk e b =>
        have hv := uibhbotFutureSubmapDartEquiv_val k W h (e, b)
        rw [hv]
        cases b with
        | false =>
            change wholePlaneDartVertex W (uibhbotFutureEdge k W e, true) = _
            change wholePlaneEdgeEast W (uibhbotFutureEdge k W e) = _
            exact uibhbotFutureEdge_east k W e
        | true =>
            change wholePlaneDartVertex W (uibhbotFutureEdge k W e, false) = _
            change wholePlaneEdgeWest W (uibhbotFutureEdge k W e) = _
            exact uibhbotFutureEdge_west k W e

/-- Helper toward Lemma 5.10. The induced dart equivalence leaves each endpoint
side bit unchanged. -/
theorem uibhbotFutureSubmapDartEquiv_side (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (d : ℕ × Bool) :
    ((uibhbotFutureSubmapDartEquiv k W h d).1).2 = d.2 := by
  rw [uibhbotFutureSubmapDartEquiv_val]





















end DirectedDistances.RandomWalk
