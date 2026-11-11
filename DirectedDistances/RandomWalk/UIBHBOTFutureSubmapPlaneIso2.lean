module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso

/-! Both side structures use the future-code edge and vertex indices as their
abstract identifiers. The plane-side endpoints, presence, dart rotation, and
face successor are pulled back along the proved future-submap maps. Thus the
plane realization retains every geometric edge, including missing edges. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.10. The full future-code vertex carrier, including
vertices incident only to missing geometric edges. -/
@[expose] def uibhbotFutureCodeVertices (k : ℤ) (W : ℤ → Fin 3) : Set ℕ :=
  {v | ∃ e, edgeWest (fun i => uibhbotFutureCode k W (i + 1)) e = v ∨
    edgeEast (fun i => uibhbotFutureCode k W (i + 1)) e = v}

/-- Helper toward Lemma 5.10. The edge IDs appearing at a finite stage of the
KMSW future code, without filtering out missing edges. -/
@[expose] def uibhbotFutureCodeEdges (k : ℤ) (W : ℤ → Fin 3) : Set ℕ :=
  {e | ∃ n, e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge}

/-- Helper toward Lemma 5.10. The marked KMSW future code represented on its
own edge and vertex identifiers. The two indexed darts are the past and
future rays of its external boundary, with the latter using the directed
side of each edge. -/
@[expose] noncomputable def uibhbotFutureCodeGeometricSide (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
        ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
          (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite) :
    GeometricSideSubmap where
  vertices := uibhbotFutureCodeVertices k W
  edges := uibhbotFutureCodeEdges k W
  west := edgeWest (fun i => uibhbotFutureCode k W (i + 1))
  east := edgeEast (fun i => uibhbotFutureCode k W (i + 1))
  present := {e | EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) e}
  rotation d e := kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin d = e
  faceNext d e := kmswInfFaceSucc (fun i => uibhbotFutureCode k W (i + 1)) hfin d = e
  root := boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h 0
  boundary := fun i => futureMapBoundaryDart
    (fun j => uibhbotFutureCode k W (j + 1)) h (-(i : ℤ) - 1)
  seam := fun i => (boundaryOuterEdge
    (fun j => uibhbotFutureCode k W (j + 1)) h (i : ℤ), false)

/-- Helper toward Lemma 5.10. The same future-code indices represent the
embedded plane carrier, using the established dart equivalence to interpret
each edge in the whole-plane colimit. Rotation and face succession are induced
from ambient plane permutations by taking the first return to the future
carrier, so darts in omitted past faces remain part of its outer face. -/
@[expose] noncomputable def uibhbotFuturePlaneGeometricSide (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (H : WholePlaneRotationHypothesis W) :
    GeometricSideSubmap where
  vertices := uibhbotFutureCodeVertices k W
  edges := uibhbotFutureCodeEdges k W
  west := edgeWest (fun i => uibhbotFutureCode k W (i + 1))
  east := edgeEast (fun i => uibhbotFutureCode k W (i + 1))
  present := {e | wholePlaneEdgePresent W (uibhbotFutureEdge k W e)}
  rotation d e :=
    ∃ n : ℕ, 0 < n ∧
      (wholePlaneRotation W H)^[n]
          (uibhbotFutureSubmapDartEquiv k W h d).1 =
        (uibhbotFutureSubmapDartEquiv k W h e).1 ∧
      ∀ j : ℕ, 0 < j → j < n →
        ((wholePlaneRotation W H)^[j]
          (uibhbotFutureSubmapDartEquiv k W h d).1).1 ∉
            (uibhbotFutureSubmap k W h).edges
  faceNext d e :=
    ∃ n : ℕ, 0 < n ∧
      (wholePlaneFaceSucc W H)^[n]
          (uibhbotFutureSubmapDartEquiv k W h d).1 =
        (uibhbotFutureSubmapDartEquiv k W h e).1 ∧
      ∀ j : ℕ, 0 < j → j < n →
        ((wholePlaneFaceSucc W H)^[j]
          (uibhbotFutureSubmapDartEquiv k W h d).1).1 ∉
            (uibhbotFutureSubmap k W h).edges
  root := boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h 0
  boundary := fun i => futureMapBoundaryDart
    (fun j => uibhbotFutureCode k W (j + 1)) h (-(i : ℤ) - 1)
  seam := fun i => (boundaryOuterEdge
    (fun j => uibhbotFutureCode k W (j + 1)) h (i : ℤ), false)

/-- Helper toward Lemma 5.10. On the KMSW future-code side, every external
future-boundary dart advances to the preceding boundary label. -/
theorem uibhbotFutureCodeGeometricSide_boundaryFaceSucc (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
        ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
          (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite)
    (j : ℤ) :
    (uibhbotFutureCodeGeometricSide k W h hfin).faceNext
        (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)
        (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1)) := by
  exact futureMapBoundaryDart_faceSucc (w := fun i => uibhbotFutureCode k W (i + 1))
    (hfin := hfin) h j






































end DirectedDistances.RandomWalk
