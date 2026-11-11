/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarInverseWalkCharacterization

/-! Supporting lemmas for paper labels `defn:KMSW-inv` (see CORRESPONDENCE.md). -/
















public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}



theorem defn_kmsw_inv_provider (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (∀ (v : MapVertex B.map) (hv : v ≠ B.source),
      (canonicalULSelector B v hv).val =
        B.map.toCombinatorialMap.edgeInv (leftmostIncoming B v hv)) ∧
    (∀ (v : MapVertex B.map) (hv : v ≠ B.sink),
      (canonicalLRSelector B v hv).val = rightmostOutgoing B v hv) ∧
    canonicalULHeight B B.source = 0 ∧
    (∀ v, v ≠ B.source →
      canonicalULHeight B v =
        canonicalULHeight B (ulParent B (canonicalULSelector B) v) + 1) ∧
    (∀ h : MapVertex B.map → ℕ, h B.source = 0 →
      (∀ v, v ≠ B.source → h v = h (ulParent B (canonicalULSelector B) v) + 1) →
        h = canonicalULHeight B) ∧
    canonicalLRHeight B B.sink = 0 ∧
    (∀ v, v ≠ B.sink →
      canonicalLRHeight B v =
        canonicalLRHeight B (lrParent B (canonicalLRSelector B) v) + 1) ∧
    (∀ h : MapVertex B.map → ℕ, h B.sink = 0 →
      (∀ v, v ≠ B.sink → h v = h (lrParent B (canonicalLRSelector B) v) + 1) →
        h = canonicalLRHeight B) ∧
    (∀ j : Fin B.map.toCombinatorialMap.numEdges,
      peanoEdge B j = (firstVisitOrder B).get
        ⟨j.val, by rw [firstVisitOrder_length]; exact j.isLt⟩) ∧
    Function.Bijective (fun j : Fin B.map.toCombinatorialMap.numEdges =>
      (Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.edgeInv)
        (peanoEdge B j) : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap)) ∧
    (∀ j : Fin B.map.toCombinatorialMap.numEdges,
      bipolarInverseWalk B j =
        ((canonicalULHeight B (dartTailVertex B.map (peanoEdge B j)) : ℤ),
          (canonicalLRHeight B (dartHeadVertex B.map (peanoEdge B j)) : ℤ) -
            ((r - 1 : ℕ) : ℤ))) :=
  ⟨canonicalULParentEdge_leftmostIncoming B, canonicalLRParentEdge_rightmostOutgoing B,
    ulHeight_source B (canonicalULSelector B),
    fun _ hv => ulHeight_parent B (canonicalULSelector B) hv,
    fun h h0 hs => canonicalULHeight_unique B h h0 hs,
    lrHeight_sink B (canonicalLRSelector B),
    fun _ hv => lrHeight_parent B (canonicalLRSelector B) hv,
    fun h h0 hs => canonicalLRHeight_unique B h h0 hs,
    peanoEdge_eq_firstVisitOrder_get B, peanoEdge_bijective_edges B, fun _ => rfl⟩

end DirectedDistances.PaperProofs.SourceResults
