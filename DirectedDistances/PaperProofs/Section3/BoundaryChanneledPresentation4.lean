/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation3

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the integer position map is injective on
each of the two present-side index families. -/
theorem boundaryChanneledPresentation_sidePosition_injective
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    Function.Injective (fun i : Fin ℓ =>
      boundaryChanneledPresentation_position R G (.upperLeft i)) ∧
    Function.Injective (fun i : Fin r =>
      boundaryChanneledPresentation_position R G (.lowerRight i)) := by
  constructor
  · intro i j h
    have hij : (InfiniteBoundaryDartIndex.upperLeft i) =
        InfiniteBoundaryDartIndex.upperLeft j :=
      boundaryChanneledPresentation_position_injective R G h
    cases hij
    rfl
  · intro i j h
    have hij : (InfiniteBoundaryDartIndex.lowerRight i) =
        InfiniteBoundaryDartIndex.lowerRight j :=
      boundaryChanneledPresentation_position_injective R G h
    cases hij
    rfl

/-- Helper toward Definition 3.2: neither finite present-side successor has a
directed cycle. -/
theorem boundaryChanneledPresentation_sides_acyclic
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    (∀ i, ¬ Relation.TransGen
      (fun i j => (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.next i = some j)
      i i) ∧
    (∀ i, ¬ Relation.TransGen
      (fun i j => (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.next i = some j)
      i i) := by
  constructor
  · intro i hcycle
    have hstep : ∀ {i j : Fin ℓ},
        (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.next i = some j →
          i.val < j.val := by
      intro i j h
      change (if h' : i.val + 1 < ℓ then some ⟨i.val + 1, h'⟩ else none) = some j at h
      by_cases hi : i.val + 1 < ℓ
      · rw [dif_pos hi] at h
        have hv := congrArg Fin.val (Option.some.inj h)
        simp at hv
        omega
      · rw [dif_neg hi] at h
        cases h
    have hlt : ∀ {i j : Fin ℓ},
        Relation.TransGen
          (fun i j => (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.next i = some j)
          i j → i.val < j.val := by
      intro i j h
      induction h with
      | single hstep' => exact hstep hstep'
      | tail hprefix hlast ih => exact lt_trans ih (hstep hlast)
    exact (Nat.lt_irrefl i.val (hlt hcycle)).elim
  · intro i hcycle
    have hstep : ∀ {i j : Fin r},
        (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.next i = some j →
          i.val < j.val := by
      intro i j h
      change (if h' : i.val + 1 < r then some ⟨i.val + 1, h'⟩ else none) = some j at h
      by_cases hi : i.val + 1 < r
      · rw [dif_pos hi] at h
        have hv := congrArg Fin.val (Option.some.inj h)
        simp at hv
        omega
      · rw [dif_neg hi] at h
        cases h
    have hlt : ∀ {i j : Fin r},
        Relation.TransGen
          (fun i j => (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.next i = some j)
          i j → i.val < j.val := by
      intro i j h
      induction h with
      | single hstep' => exact hstep hstep'
      | tail hprefix hlast ih => exact lt_trans ih (hstep hlast)
    exact (Nat.lt_irrefl i.val (hlt hcycle)).elim

/- Remaining targets, with full binders.

The position-injectivity lemma and no-cycle conjunct are proved above. Three
routes were examined for the remaining vertex-injectivity part of side simplicity:
transport `vertices_nodup` through the dependent sum of dart-initial and
terminal occurrences; first use the integer position injection to distinguish
dart indices, then derive vertex-occurrence uniqueness from path edge steps;
and prove directly that each finite successor strictly increases its index,
which excludes cycles but does not by itself separate nonadjacent vertices.
The remaining target is
`IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
    (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft ∧
 IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
    (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight`
for `{ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
 (G : BoundaryChanneledPLDrawing R)`.

Three routes were examined for present-side endpoint labels: expand the
`BoundarySideEndpointLabels` conjunction and prove the first/last `Fin`
indices directly; transfer the path's `start_vertex`/`end_vertex` and
`edge_step` equations through the left and reversed-right dart endpoint
calculations; and use the carrier's positive path lengths to discharge the
empty-index clauses. The path equations give the endpoint equalities, but the
finite predecessor/successor clauses have not yet been assembled into a
checked proof. The remaining target is
`BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
    (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft ∧
 BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
    (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight`
for `{ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
 (G : BoundaryChanneledPLDrawing R)`.

Three routes were examined for the required finite join labels: use the
present-side endpoint labels and the existing empty-side endpoint helper;
split according to whether both present sides are nonempty and apply the UL
and LR join lemmas; and use the integer position order to identify the
terminal-to-initial side transition. Each route still needs a relation between
`S` and the geometric boundary successor. The stated binders give only an
arbitrary `S : G.GeometricEdge × Bool → G.GeometricEdge × Bool`, so that
relation cannot be inferred and no premise was added. The remaining target is
`RequiredFiniteBoundaryJoinEndpointLabels7
  (boundaryChanneledPresentationWithJunctions R G).presentation S`
for `{ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
 (G : BoundaryChanneledPLDrawing R) (U : G.Face)
 (S : G.GeometricEdge × Bool → G.GeometricEdge × Bool)`. -/

end DirectedDistances.PaperProofs.Section3

end
end
