module

public import DirectedDistances.KMSW.KMSWStageZeroDrawing
public import DirectedDistances.KMSW.CutEquivalenceConverse
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

noncomputable section



@[expose] def stageVertex (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) : Fin (kmswStage w n).nextVertex :=
  ⟨stageEndpoint (kmswStage w n) d, by
    cases hb : d.2
    · simpa [stageEndpoint, hb] using
        (kmswStage_endpoints_lt_nextVertex w n d.1.val d.1.isLt).1
    · simpa [stageEndpoint, hb] using
        (kmswStage_endpoints_lt_nextVertex w n d.1.val d.1.isLt).2⟩



@[expose] def StageDrawing (w : ℕ → Fin 3) (n : ℕ) :=
  PLDrawing (StageDart (kmswStage w n).nextEdge) (Fin (kmswStage w n).nextVertex)
    (edgeFlip _) (stageRot w n) (stageVertex w n)



@[expose] def stageDartIncl (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    StageDart (kmswStage w (n + 1)).nextEdge :=
  (d.1.castLE (kmswStage_nextEdge_mono w (Nat.le_succ n)), d.2)



@[expose] def stageVertexIncl (w : ℕ → Fin 3) (n : ℕ)
    (v : Fin (kmswStage w n).nextVertex) : Fin (kmswStage w (n + 1)).nextVertex :=
  v.castLE (CutConverse.nextVertex_mono w (Nat.le_succ n))




@[expose] def StageExtends (w : ℕ → Fin 3) (n : ℕ)
    (P : StageDrawing w n) (Q : StageDrawing w (n + 1)) : Prop :=
  (∀ v, P.pos v = Q.pos (stageVertexIncl w n v)) ∧
  (∀ d, P.arc d = Q.arc (stageDartIncl w n d))



@[expose] def openTriangle (a b c : ℂ) : Set ℂ :=
  interior (convexHull ℝ ({a, b, c} : Set ℂ))





@[expose] def stageEdgeTrace {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (e : ℕ) : Set ℂ :=
  if h : e < (kmswStage w n).nextEdge then (P.arc (⟨e, h⟩, false)).image else ∅




theorem stageVertex_zero (w : ℕ → Fin 3) :
    stageVertex w 0 = kmswStage0Vertex w := rfl

-- The existing drawing needs no transport or replacement.
example (w : ℕ → Fin 3) : StageDrawing w 0 := kmswStage0Drawing w







structure StageExteriorSector {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (ext : Set ℂ) where
  a : ℂ
  b : ℂ
  c : ℂ
  noncollinear : ¬ Collinear ℝ ({a, b, c} : Set ℂ)
  region : Set ℂ
  region_eq : region = openTriangle a b c
  region_nonempty : region.Nonempty
  region_subset_ext : region ⊆ ext
  closure_region : closure region = convexHull ℝ ({a, b, c} : Set ℂ)
  boundary : frontier region = segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
  attachment : Set ℂ
  attachment_nonempty : attachment.Nonempty
  attachment_boundary : attachment ⊆ frontier region
  closure_inter_image : closure region ∩ P.image = attachment
  slotBefore : (v : Fin (kmswStage w n).nextVertex) →
    P.pos v ∈ attachment → StageDart (kmswStage w n).nextEdge
  slotAfter : (v : Fin (kmswStage w n).nextVertex) →
    P.pos v ∈ attachment → StageDart (kmswStage w n).nextEdge
  slot_vertex : ∀ v hv, stageVertex w n (slotBefore v hv) = v
  slot_successor : ∀ v hv, stageRot w n (slotBefore v hv) = slotAfter v hv
  slotDirection : (v : Fin (kmswStage w n).nextVertex) → P.pos v ∈ attachment → ℂ
  slot_direction_nonzero : ∀ v hv, slotDirection v hv ≠ 0
  slot_direction_enters : ∀ v hv, ∃ ε : ℝ, 0 < ε ∧
    ∀ t : ℝ, 0 < t → t < ε → P.pos v + (t : ℂ) * slotDirection v hv ∈ region
  slot_direction_ccw : ∀ v hv,
    0 < ccwTurn (P.arc (slotBefore v hv)).initialDirection (slotDirection v hv) ∧
    ccwTurn (P.arc (slotBefore v hv)).initialDirection (slotDirection v hv) <
      ccwTurn (P.arc (slotBefore v hv)).initialDirection
        (P.arc (slotAfter v hv)).initialDirection
  cap_remainder_connected : IsConnected (ext \ closure region)
  cap_remainder_unbounded : ∀ R : ℝ, ∃ z ∈ ext \ closure region, R < ‖z‖
  pendant_remainder_connected : ∀ x ∈ attachment, ∀ y ∈ region,
    IsConnected (ext \ segment ℝ x y)
  pendant_remainder_unbounded : ∀ x ∈ attachment, ∀ y ∈ region,
    ∀ R : ℝ, ∃ z ∈ ext \ segment ℝ x y, R < ‖z‖




structure StageGeom (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) where
  ext : Set ℂ
  cells : Fin (kmswStage w n).triangles.length → Set ℂ
  corners : Fin (kmswStage w n).triangles.length → ℂ × ℂ × ℂ
  noncollinear : ∀ i, ¬ Collinear ℝ
    ({(corners i).1, (corners i).2.1, (corners i).2.2} : Set ℂ)
  cell_eq : ∀ i, cells i = openTriangle (corners i).1
    (corners i).2.1 (corners i).2.2
  cell_open : ∀ i, IsOpen (cells i)
  cell_bounded : ∀ i, Bornology.IsBounded (cells i)
  cell_boundary : ∀ i, frontier (cells i) =
    stageEdgeTrace P ((kmswStage w n).triangles.get i).1 ∪
    stageEdgeTrace P ((kmswStage w n).triangles.get i).2.1 ∪
    stageEdgeTrace P ((kmswStage w n).triangles.get i).2.2
  cells_pairwise_disjoint : ∀ i j, i ≠ j → Disjoint (cells i) (cells j)
  cells_disjoint_ext : ∀ i, Disjoint (cells i) ext
  cells_disjoint_image : ∀ i, Disjoint (cells i) P.image
  ext_open : IsOpen ext
  ext_connected : IsConnected ext
  ext_unbounded : ∀ R : ℝ, ∃ z ∈ ext, R < ‖z‖
  complement : P.imageᶜ = ext ∪ ⋃ i, cells i
  activeSector : StageExteriorSector P ext
  activeSector_attachment :
    activeSector.attachment = stageEdgeTrace P (kmswStage w n).active
  leftSector : Option (StageExteriorSector P ext)
  leftSector_attachment :
    match (kmswStage w n).UL.dropLast.reverse, leftSector with
    | [], none => True
    | e :: _, some S =>
      S.attachment = stageEdgeTrace P e ∪ stageEdgeTrace P (kmswStage w n).active
    | _, _ => False
  exteriorFace : P.Face
  exteriorFace_eq : exteriorFace.val = ext
  exteriorFace_unbounded : P.IsUnbounded exteriorFace
  dartBorders_iff : ∀ d,
    P.dartBorders d exteriorFace ↔ (kmswStageDirectedMap w n).IsOuter d

end
end DirectedDistances.KMSW
