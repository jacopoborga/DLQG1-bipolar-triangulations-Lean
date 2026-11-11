module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmap

/-! The selected future carrier has all geometric edges of the one-sided KMSW suffix,
including its missing boundary edges. The submap records the global whole-plane edge
identities and the boundary vertices with relative indices `j ≤ 0`. This is an
incidence submap; no face or rotation identification is asserted here. -/

public section
namespace DirectedDistances.RandomWalk

open DirectedDistances.KMSW
open MeasureTheory

/-- Helper toward Lemma 5.10. Incidence data for the embedded future carrier, with
all suffix geometric edges retained and the earlier boundary vertices marked. -/
structure UIBHBOTFutureSubmapData (W : ℤ → Fin 3) where
  vertices : Set (WholePlaneVertex W)
  edges : Set (WholePlaneEdge W)
  west : WholePlaneEdge W → WholePlaneVertex W
  east : WholePlaneEdge W → WholePlaneVertex W
  present : WholePlaneEdge W → Prop
  boundary : {j : ℤ // j ≤ 0} → {v : WholePlaneVertex W // v ∈ vertices}

/-- Helper toward Lemma 5.10. The future submap after the `k`th boundary hit,
using exactly the geometric vertex and edge images of the future-code carrier.
Its boundary field retains the source vertices indexed by `j ≤ 0`. -/
@[expose] noncomputable def uibhbotFutureSubmap (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) :
    UIBHBOTFutureSubmapData W where
  vertices := Set.range (uibhbotFutureVertex k W)
  edges := Set.range (uibhbotFutureEdge k W)
  west := wholePlaneEdgeWest W
  east := wholePlaneEdgeEast W
  present := wholePlaneEdgePresent W
  boundary := fun j =>
    ⟨uibhbotFutureVertex k W
      (boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j.1),
      ⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j.1, rfl⟩⟩

/-- Helper toward Lemma 5.10. Almost surely, the retained relative boundary vertex
`j ≤ 0` is the original boundary vertex with index `k + j`. -/
theorem ae_uibhbotFutureSubmap_boundary_index :
    ∀ᵐ W ∂(DirectedDistances.PaperProofs.Section5.uibhbotCodeLawRel :
      Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ (j : ℤ) (hj : j ≤ 0),
          ((uibhbotFutureSubmap k W h).boundary ⟨j, hj⟩).1 =
            uibhbotFutureVertex (k + j) W 0 := by
  simpa [uibhbotFutureSubmap] using ae_uibhbotFutureBoundary_index

/-- Helper toward Lemma 5.10. The code edge IDs of the shifted KMSW assembly are
in bijection with the retained geometric edge IDs of the embedded future submap. -/
@[expose] noncomputable def uibhbotFutureSubmapEdgeEquiv (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) :
    ℕ ≃ {e : WholePlaneEdge W // e ∈ (uibhbotFutureSubmap k W h).edges} where
  toFun e := ⟨uibhbotFutureEdge k W e, ⟨e, rfl⟩⟩
  invFun e := Classical.choose (Set.mem_range.mp e.2)
  left_inv e := uibhbotFutureEdge_injective k W
    (Classical.choose_spec (Set.mem_range.mp (show
      uibhbotFutureEdge k W e ∈ Set.range (uibhbotFutureEdge k W) from ⟨e, rfl⟩)))
  right_inv e := by
    apply Subtype.ext
    exact Classical.choose_spec (Set.mem_range.mp e.2)

/-- Helper toward Lemma 5.10. The edge-ID bijection commutes with the west endpoint. -/
theorem uibhbotFutureSubmapEdgeEquiv_west (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) (e : ℕ) :
    (uibhbotFutureSubmap k W h).west
        ((uibhbotFutureSubmapEdgeEquiv k W h e).1) =
      uibhbotFutureVertex k W (edgeWest (fun i => uibhbotFutureCode k W (i + 1)) e) :=
  uibhbotFutureEdge_west k W e

/-- Helper toward Lemma 5.10. The edge-ID bijection commutes with the east endpoint. -/
theorem uibhbotFutureSubmapEdgeEquiv_east (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) (e : ℕ) :
    (uibhbotFutureSubmap k W h).east
        ((uibhbotFutureSubmapEdgeEquiv k W h e).1) =
      uibhbotFutureVertex k W (edgeEast (fun i => uibhbotFutureCode k W (i + 1)) e) :=
  uibhbotFutureEdge_east k W e

/-- Helper toward Lemma 5.10. A present directed edge of the shifted code remains
present in the whole-plane assembly, with its west-to-east orientation preserved. -/
theorem uibhbotFutureSubmapEdgeEquiv_present (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1))) (e : ℕ)
    (he : EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) e) :
    (uibhbotFutureSubmap k W h).present
      ((uibhbotFutureSubmapEdgeEquiv k W h e).1) ∧
    (uibhbotFutureSubmap k W h).west
        ((uibhbotFutureSubmapEdgeEquiv k W h e).1) =
      uibhbotFutureVertex k W (edgeWest (fun i => uibhbotFutureCode k W (i + 1)) e) ∧
    (uibhbotFutureSubmap k W h).east
        ((uibhbotFutureSubmapEdgeEquiv k W h e).1) =
      uibhbotFutureVertex k W (edgeEast (fun i => uibhbotFutureCode k W (i + 1)) e) := by
  exact ⟨uibhbotFutureEdge_present k W e he,
    uibhbotFutureSubmapEdgeEquiv_west k W h e,
    uibhbotFutureSubmapEdgeEquiv_east k W h e⟩










end DirectedDistances.RandomWalk
