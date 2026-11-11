module

public import DirectedDistances.PlanarMap.BdyReverseSizedSlices

/-! # Uniform and unfolding helpers for restricted endpoint reversal

Restricted simple-boundary helpers for `lem-bdy-reverse`
The uniform measures below are on labelled structures. Their identification
with uniform measure on isomorphism classes holds, for instance, when all
structures in the slice have trivial automorphisms (or a common automorphism
order), together with `Perm D`-equivariance of the reversal; those
obligations remain recorded under simple-boundary restriction/I1 and are not proved here. -/

public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {l : ℕ}

open BipolarTriangulationWithBoundary

/-- Endpoint symmetry transports counting-normalised uniform measure between
the size-`s` labelled restricted slices for every `l ≥ 1`, including `l = 1`.
This is a restricted simple-boundary helper for `lem-bdy-reverse`
isomorphism classes holds, for instance, when all structures in the slice have
trivial automorphisms (or a common automorphism order), together with
`Perm D`-equivariance of the reversal; these are not proved here. -/
theorem endpointSymmetrySizedEquiv_uniform (l s : ℕ) (hl : 1 ≤ l) :
    let A := {B : BoundaryMbcClass D l 1 // innerEdgeCount B.val = s}
    let C := {B : BoundaryMbcClass D 1 l // innerEdgeCount B.val = s}
    ∀ (mA : MeasurableSpace A) (mC : MeasurableSpace C)
      [MeasurableSingletonClass A] [MeasurableSingletonClass C],
      (@uniformCountingMeasure A inferInstance mA).map
          (endpointSymmetrySizedEquiv (D := D) l s hl) =
        @uniformCountingMeasure C inferInstance mC := by
  intro A C mA mC hA hC
  exact uniformCountingMeasure_map_of_bijective
    (endpointSymmetrySizedEquiv (D := D) l s hl)
    (endpointSymmetrySizedEquiv (D := D) l s hl).bijective

/-- Marked-prefix version of the sized right-endpoint transport. The marked
index ranges over `Fin (r - 1)`, indexing right-prefix darts; it is not the
source's missing-root edge. This is an alias for the earlier transport, whose
name is retained for compatibility. Restricted simple-boundary helper for
instance, when all structures in the slice have trivial automorphisms (or a
common automorphism order), together with `Perm D`-equivariance of the
reversal (simple-boundary restriction/I1); not proved here. -/
noncomputable abbrev endpointMarkedPrefixSizedTransport (r s : ℕ) (hr : 2 ≤ r) :=
  endpointMissingRootSizedTransport (D := D) r s hr

/-- The marked-prefix transport pushes uniform measure on the labelled
size-`s` slice times `Fin (r - 1)` to the target uniform measure. The marked
index ranges over the right-prefix darts, not the source's missing-root edge.
Restricted simple-boundary helper for `lem-bdy-reverse`
Labelled uniform equals isomorphism-class uniform holds, for instance, when all
structures in the slice have trivial automorphisms (or a common automorphism
order), together with `Perm D`-equivariance of the reversal (simple-boundary restriction/I1); not
proved here. -/
theorem endpointMarkedPrefixSizedTransport_uniform (r s : ℕ) (hr : 2 ≤ r) :
    let A :=
      {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s} × Fin (r - 1)
    let C :=
      {B : BoundaryMbcClass D r 1 // innerEdgeCount B.val = s} × Fin (r - 1)
    ∀ (mA : MeasurableSpace A) (mC : MeasurableSpace C)
      [MeasurableSingletonClass A] [MeasurableSingletonClass C],
      (@uniformCountingMeasure A inferInstance mA).map
          (endpointMarkedPrefixSizedTransport (D := D) r s hr) =
        @uniformCountingMeasure C inferInstance mC :=
  endpointMissingRootSizedTransport_uniform (D := D) r s hr

private theorem boundaryMbcClassEquiv_val_unfold {a b c d : ℕ}
    (ha : a = c) (hb : b = d) (B : BoundaryMbcClass D a b) :
    (boundaryMbcClassEquiv (D := D) ha hb B).val =
      cast (by cases ha; cases hb; rfl) B.val := by
  cases ha
  cases hb
  rfl

private theorem cast_boundary_leftPath_darts {a b c d : ℕ}
    (ha : a = c) (hb : b = d)
    (B : BipolarTriangulationWithBoundary D a b) :
    (cast (by cases ha; cases hb; rfl) B :
      BipolarTriangulationWithBoundary D c d).leftPath.darts = B.leftPath.darts := by
  cases ha
  cases hb
  rfl

private theorem cast_boundary_rightPath_darts {a b c d : ℕ}
    (ha : a = c) (hb : b = d)
    (B : BipolarTriangulationWithBoundary D a b) :
    (cast (by cases ha; cases hb; rfl) B :
      BipolarTriangulationWithBoundary D c d).rightPath.darts = B.rightPath.darts := by
  cases ha
  cases hb
  rfl

private theorem cast_boundary_outerWord {a b c d : ℕ}
    (ha : a = c) (hb : b = d)
    (B : BipolarTriangulationWithBoundary D a b) :
    (cast (by cases ha; cases hb; rfl) B :
      BipolarTriangulationWithBoundary D c d).outerWord = B.outerWord := by
  cases ha
  cases hb
  rfl

/-- Underlying structure of the literal left endpoint reversal, unfolded as
the left-prefix reversal followed by transport of its length indices.
Restricted simple-boundary helper for `lem-bdy-reverse` -/
theorem leftEndpointReversalEquiv_val (hl : 2 ≤ l)
    (B : BoundaryMbcClass D l 1) :
    (leftEndpointReversalEquiv (D := D) hl B).val =
      cast (by congr 1 <;> omega)
        (leftPrefixReversal B.val (l - 1) (by omega) (by omega) B.property) := by
  simp only [leftEndpointReversalEquiv, Equiv.trans_apply,
    Equiv.ofBijective_apply, leftPrefixReversalMbc]
  exact boundaryMbcClassEquiv_val_unfold (D := D) (by omega) (by omega)
    ⟨leftPrefixReversal B.val (l - 1) (by omega) (by omega) B.property,
      leftPrefixReversal_InMbc B.val (l - 1) (by omega) (by omega) B.property⟩

/-- Left boundary darts after the literal left endpoint reversal (`l ≥ 2`),
expressed by dropping the reversed prefix from the input left boundary.
Restricted simple-boundary helper for `lem-bdy-reverse` -/
@[simp] theorem leftEndpointReversalEquiv_leftPath_darts (hl : 2 ≤ l)
    (B : BoundaryMbcClass D l 1) :
    (leftEndpointReversalEquiv (D := D) hl B).val.leftPath.darts =
      B.val.leftPath.darts.drop (l - 1) := by
  rw [leftEndpointReversalEquiv_val]
  rw [cast_boundary_leftPath_darts (D := D) (by omega) (by omega)]
  exact leftPrefixReversal_leftPath_darts B.val (l - 1) (by omega) (by omega)
    B.property

/-- Right boundary darts after the literal left endpoint reversal (`l ≥ 2`),
expressed as the reversed, orientation-flipped input left prefix followed by
the input right boundary. Restricted simple-boundary helper for -/
@[simp] theorem leftEndpointReversalEquiv_rightPath_darts (hl : 2 ≤ l)
    (B : BoundaryMbcClass D l 1) :
    (leftEndpointReversalEquiv (D := D) hl B).val.rightPath.darts =
      (B.val.leftPath.darts.take (l - 1)).reverse.map
        B.val.map.toCombinatorialMap.edgeInv ++ B.val.rightPath.darts := by
  rw [leftEndpointReversalEquiv_val]
  rw [cast_boundary_rightPath_darts (D := D) (by omega) (by omega)]
  exact leftPrefixReversal_rightPath_darts B.val (l - 1) (by omega) (by omega)
    B.property

/-- The outer word is unchanged by the literal left endpoint reversal
(`l ≥ 2`). Restricted simple-boundary helper for `lem-bdy-reverse` -/
@[simp] theorem leftEndpointReversalEquiv_outerWord (hl : 2 ≤ l)
    (B : BoundaryMbcClass D l 1) :
    (leftEndpointReversalEquiv (D := D) hl B).val.outerWord = B.val.outerWord := by
  rw [leftEndpointReversalEquiv_val]
  rw [cast_boundary_outerWord (D := D) (by omega) (by omega)]
  exact leftPrefixReversal_outerWord B.val (l - 1) (by omega) (by omega)
    B.property

/-- Underlying structure of the identity endpoint equivalence at `l = 1`.
Restricted simple-boundary helper for `lem-bdy-reverse` -/
@[simp] theorem leftEndpointReversalEquiv_one_val (B : BoundaryMbcClass D 1 1) :
    (leftEndpointReversalEquiv_one (D := D) B).val = B.val := rfl

/-- Left boundary darts are unchanged by the identity endpoint equivalence
at `l = 1`. Restricted simple-boundary helper for `lem-bdy-reverse` -/
theorem leftEndpointReversalEquiv_one_leftPath_darts
    (B : BoundaryMbcClass D 1 1) :
    (leftEndpointReversalEquiv_one (D := D) B).val.leftPath.darts =
      B.val.leftPath.darts := rfl

/-- Right boundary darts are unchanged by the identity endpoint equivalence
at `l = 1`. Restricted simple-boundary helper for `lem-bdy-reverse` -/
theorem leftEndpointReversalEquiv_one_rightPath_darts
    (B : BoundaryMbcClass D 1 1) :
    (leftEndpointReversalEquiv_one (D := D) B).val.rightPath.darts =
      B.val.rightPath.darts := rfl

/-- The outer word is unchanged by the identity endpoint equivalence at
`l = 1`. Restricted simple-boundary helper for `lem-bdy-reverse` -/
theorem leftEndpointReversalEquiv_one_outerWord
    (B : BoundaryMbcClass D 1 1) :
    (leftEndpointReversalEquiv_one (D := D) B).val.outerWord =
      B.val.outerWord := rfl

end DirectedDistances.PlanarMap
