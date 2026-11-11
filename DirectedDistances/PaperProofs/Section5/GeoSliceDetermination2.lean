/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination

/-! # Marked-side slice carriers -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

/-- The vertex and geometric-edge carrier of a slice cut from a marked side.
This deliberately records carriers only; it does not assert a reconstruction
of the side's induced face or rotation structure. -/
structure GeometricSideSliceCarrier where
  vertices : Set ℕ
  edges : Set ℕ

/-- The initial vertex of an oriented dart in a side submap, using the side's
own endpoint maps and the dart's reversal bit. -/
@[expose] def geometricSideDartInitial (S : GeometricSideSubmap)
    (d : ℕ × Bool) : ℕ :=
  if d.2 then S.east d.1 else S.west d.1

/-- Helper toward Lemma 5.6: clip a side carrier at two marked segments. The
side submap is the only map input. Its `boundary` and `seam` marks supply the
two dart sequences; the strict vertex tails and the edge tails beginning at
the supplied offsets are deleted, as in the ambient slice carrier. -/
@[expose] def geometricSideMarkedSliceCarrier
    (S : GeometricSideSubmap) (a b : ℕ) : GeometricSideSliceCarrier where
  vertices := S.vertices \
    ({v | ∃ n, a < n ∧ v = geometricSideDartInitial S (S.boundary n)} ∪
      {v | ∃ n, b < n ∧ v = geometricSideDartInitial S (S.seam n)})
  edges := S.edges \
    (Set.range (fun n => (S.boundary (a + n)).1) ∪
      Set.range (fun n => (S.seam (b + n)).1))

/-- Helper toward Lemma 5.6: membership in the clipped vertex carrier is
membership in the input carrier with both strict marked vertex tails removed. -/
theorem geometricSideMarkedSliceCarrier_mem_vertices_iff
    (S : GeometricSideSubmap) (a b v : ℕ) :
    v ∈ (geometricSideMarkedSliceCarrier S a b).vertices ↔
      v ∈ S.vertices ∧
        v ∉ ({v | ∃ n, a < n ∧ v = geometricSideDartInitial S (S.boundary n)} ∪
          {v | ∃ n, b < n ∧ v = geometricSideDartInitial S (S.seam n)}) := by
  rfl


/-- Helper toward Lemma 5.6: membership in the clipped edge carrier is
membership in the input carrier with both marked edge tails removed. -/
theorem geometricSideMarkedSliceCarrier_mem_edges_iff
    (S : GeometricSideSubmap) (a b e : ℕ) :
    e ∈ (geometricSideMarkedSliceCarrier S a b).edges ↔
      e ∈ S.edges ∧
        e ∉ (Set.range (fun n => (S.boundary (a + n)).1) ∪
          Set.range (fun n => (S.seam (b + n)).1)) := by
  rfl




























end DirectedDistances.PaperProofs.Section5
