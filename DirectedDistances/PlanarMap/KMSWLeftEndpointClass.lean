/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier
public import DirectedDistances.PlanarMap.BdyReverseRelabelLeft

/-! # Reversing the left endpoint in the KMSW map class

specifically the reversal step at `:432`. These declarations use only the
restricted simple-boundary reversal carrier. They do not assume the general
Lemma 3.18 or simple-boundary restriction, and they are not the paper result. -/

public section
namespace DirectedDistances.PlanarMap

variable {ℓ n : ℕ}

/-- Boundary channeling on the restricted carrier implies its base-carrier
formulation for any pair of boundary lengths. Helper toward -/
theorem BipolarTriangulationWithBoundary.isBoundaryChanneledBase_toBase
    {D : Type*} [Fintype D] [DecidableEq D] {a b : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (hbc : B.IsBoundaryChanneled) :
    B.toBase.IsBoundaryChanneledBase := hbc

namespace KMSWMapRep

/-- Boundary channeling on a KMSW representative with arbitrary boundary
lengths, expressed on its general base carrier. Helper toward
paper result. -/
@[expose] def IsBoundaryChanneledBase {a b n : ℕ}
    (R : KMSWMapRep a b n) : Prop := R.B.IsBoundaryChanneledBase

/-- The general base-carrier channeling predicate is invariant under
representative isomorphism. Helper toward `lem-kmsw-left` -/
theorem isBoundaryChanneledBase_iff_of_iso {a b n : ℕ}
    (R R' : KMSWMapRep a b n) (I : BipolarBoundaryBaseIso R.B R'.B) :
    R.IsBoundaryChanneledBase ↔ R'.IsBoundaryChanneledBase :=
  DirectedDistances.PlanarMap.isBoundaryChanneledBase_iff_of_iso I

end KMSWMapRep

namespace KMSWMapIsoClass

/-- Boundary channeling on the general base carrier descended to KMSW
isomorphism classes with arbitrary boundary lengths. Helper toward
paper result. -/
@[expose] def IsBoundaryChanneledBase {a b n : ℕ}
    (q : KMSWMapIsoClass a b n) : Prop :=
  Quotient.lift (fun R : KMSWMapRep a b n => R.IsBoundaryChanneledBase)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      exact propext (KMSWMapRep.isBoundaryChanneledBase_iff_of_iso R R' I)) q

/-- The descended general channeling predicate agrees with its representative
415–440`); not the paper result. -/
@[simp] theorem isBoundaryChanneledBase_mk {a b n : ℕ}
    (R : KMSWMapRep a b n) :
    IsBoundaryChanneledBase (KMSWMapIsoClass.mk R) ↔ R.IsBoundaryChanneledBase := Iff.rfl

end KMSWMapIsoClass

/-- Restricted left endpoint reversal preserves the total number of edges.
The combinatorial edge involution is unchanged by mirroring and by flipping
the boundary orientations. Helper toward `lem-kmsw-left` -/
theorem leftPrefixReversal_numEdges
    {D : Type*} [Fintype D] [DecidableEq D] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).map.toCombinatorialMap.numEdges =
      B.map.toCombinatorialMap.numEdges := by
  rw [leftPrefixReversal_map]
  rfl

@[simp] private theorem mirrorVertexMap_mirrorVertexMap
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (v : MapVertex M) :
    DirectedMapWithMissing.mirrorVertexMap M.mirror
      (DirectedMapWithMissing.mirrorVertexMap M v) = v := by
  rw [DirectedMapWithMissing.mirrorVertexMap_eq M.mirror,
    DirectedMapWithMissing.mirrorVertexMap_eq M]
  obtain ⟨d, hd⟩ := Quotient.exists_rep v
  have hv : v = dartTailVertex M d := by
    simpa [dartTailVertex] using hd.symm
  rw [hv]
  rw [DirectedMapWithMissing.mirror_dartTailVertex M d,
    DirectedMapWithMissing.mirror_dartTailVertex M.mirror d]
  cases M with
  | mk C missing hm tail ht htm outer ho => rfl

private theorem leftPrefixReversal_source
    {D : Type*} [Fintype D] [DecidableEq D] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).source =
      B.leftPath.vertices.get ⟨k, by rw [B.leftPath.vertices_length]; omega⟩ := by
  change DirectedMapWithMissing.mirrorVertexMap B.mirror.map
    (rightPrefixReversal B.mirror k hk hka
      (B.mirror_isBoundaryChanneled hbc)).source = _
  rw [rightPrefixReversal_source (B := B.mirror) (k := k) hk hka
    (B.mirror_isBoundaryChanneled hbc)]
  simp [rightBoundaryVertexAt, BipolarTriangulationWithBoundary.mirror,
    DirectedMapWithMissing.SimpleDirectedDartPath.mirror]
  rfl

private theorem leftPrefixReversal_sink
    {D : Type*} [Fintype D] [DecidableEq D] {a b k : ℕ}
    (B : BipolarTriangulationWithBoundary D a b)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).sink = B.sink := by
  change DirectedMapWithMissing.mirrorVertexMap B.mirror.map
    (rightPrefixReversal B.mirror k hk hka
      (B.mirror_isBoundaryChanneled hbc)).sink = _
  rw [rightPrefixReversal_sink (B := B.mirror) (k := k) hk hka
    (B.mirror_isBoundaryChanneled hbc)]
  simp [BipolarTriangulationWithBoundary.mirror]
  rfl

/-- The boundary-length cast in the restricted reversal equivalence leaves
the underlying map, and hence its edge count, unchanged. Helper toward -/
theorem boundaryMbcClassEquiv_numEdges
    {D : Type*} [Fintype D] [DecidableEq D] {a b c d : ℕ}
    (ha : a = c) (hb : b = d) (B : BoundaryMbcClass D a b) :
    (boundaryMbcClassEquiv (D := D) ha hb B).val.map.toCombinatorialMap.numEdges =
      B.val.map.toCombinatorialMap.numEdges := by
  cases ha
  cases hb
  rfl

/-- Produce the restricted strong-carrier output of left endpoint reversal
from a boundary-channeled `(ℓ,1)` representative. This construction is used
only for `ℓ ≥ 2`; `ℓ = 1` is the identity case. Helper toward `lem-kmsw-left`
assumed; not the paper result. -/
@[expose] noncomputable def kmswLeftEndpointReverseStrong
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ)
    (hbc : R.IsBoundaryChanneled) :
    BipolarTriangulationWithBoundary (Fin R.dartCount) 1 ℓ :=
  (leftEndpointReversalEquiv (D := Fin R.dartCount) hℓ
    (toBoundaryMbcClassLeftEndpoint R.B hℓ hbc)).val

/-- Apply the restricted left endpoint reversal to a boundary-channeled
`(ℓ,1)` representative, retaining its dart type and total edge count. For
`ℓ = 1` this helper is intentionally not used; the endpoint step is identity.
direction; simple-boundary restriction is not assumed; not the paper result. -/
@[expose] noncomputable def kmswLeftEndpointReverseRep
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ)
    (hbc : R.IsBoundaryChanneled) : KMSWMapRep 1 ℓ n := by
  refine ⟨R.dartCount, (kmswLeftEndpointReverseStrong R hℓ hbc).toBase, ?_⟩
  change (kmswLeftEndpointReverseStrong R hℓ hbc).map.toCombinatorialMap.numEdges = n
  let C := toBoundaryMbcClassLeftEndpoint R.B hℓ hbc
  have hleft : ℓ - (ℓ - 1) = 1 := by omega
  have hright : 1 + (ℓ - 1) = ℓ := by omega
  have hcount := leftPrefixReversal_numEdges C.val (k := ℓ - 1)
    (by omega) (by omega) C.property
  have hcast := boundaryMbcClassEquiv_numEdges hleft hright
    (leftPrefixReversalMbc (D := Fin R.dartCount) (a := ℓ) (b := 1)
      (ℓ - 1) (by omega) (by omega) C)
  have hcount' :
      (kmswLeftEndpointReverseStrong R hℓ hbc).map.toCombinatorialMap.numEdges =
      R.B.map.toCombinatorialMap.numEdges := by
    change (boundaryMbcClassEquiv (D := Fin R.dartCount) hleft hright
      (leftPrefixReversalMbc (D := Fin R.dartCount) (a := ℓ) (b := 1)
        (ℓ - 1) (by omega) (by omega) C)).val.map.toCombinatorialMap.numEdges = _
    exact hcast.trans hcount
  exact hcount'.trans R.edges

/-- The reversed representative remains boundary-channeled on the general
base carrier. Helper toward `lem-kmsw-left`
assumed; not the paper result. -/
theorem kmswLeftEndpointReverseRep_isBoundaryChanneled
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ)
    (hbc : R.IsBoundaryChanneled) :
    (kmswLeftEndpointReverseRep R hℓ hbc).B.IsBoundaryChanneledBase := by
  exact BipolarTriangulationWithBoundary.isBoundaryChanneledBase_toBase _
    ((leftEndpointReversalEquiv (D := Fin R.dartCount) hℓ
      (toBoundaryMbcClassLeftEndpoint R.B hℓ hbc)).2)

/-- The `ℓ = 1` endpoint operation is the identity on representatives. This
records the identity case used alongside S7-inverse at `:432`; helper only,
simple-boundary restriction is not assumed, and this is not the paper result. -/
@[expose] def kmswLeftEndpointReverseRepOne {n : ℕ}
    (R : KMSWMapRep 1 1 n) : KMSWMapRep 1 1 n := R

/-- On a channeled representative, the left reversal can be passed to the
quotient while retaining the general base-channeling predicate. This is a
map on representatives only; helper toward `lem-kmsw-left`
and not the paper result. -/
@[expose] noncomputable def kmswLeftEndpointReverseRepClass
    (R : {R : KMSWMapRep ℓ 1 n // R.IsBoundaryChanneled}) (hℓ : 2 ≤ ℓ) :
    {q : KMSWMapIsoClass 1 ℓ n // q.IsBoundaryChanneledBase} := by
  refine ⟨KMSWMapIsoClass.mk (kmswLeftEndpointReverseRep R.val hℓ R.property), ?_⟩
  rw [KMSWMapIsoClass.isBoundaryChanneledBase_mk]
  exact kmswLeftEndpointReverseRep_isBoundaryChanneled R.val hℓ R.property

end DirectedDistances.PlanarMap
