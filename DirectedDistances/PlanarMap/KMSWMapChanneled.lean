/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier

/-! Supporting lemmas for paper labels `lem-kmsw-left` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.PlanarMap

namespace KMSWMapRep

variable {ℓ r n : ℕ}

/-- representative of any boundary lengths: every incoming edge at a boundary
vertex other than the sink is a boundary edge. Helper toward `lem-kmsw-left`
(`:415–440`), not the paper result; simple-boundary restriction not assumed. -/
@[expose] def IsChanneled (R : KMSWMapRep ℓ r n) : Prop :=
  R.B.IsBoundaryChanneledBase

/-- Channeling is preserved by an isomorphism of KMSW representatives -/
theorem isChanneled_iff_of_iso (R R' : KMSWMapRep ℓ r n)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    R.IsChanneled ↔ R'.IsChanneled :=
  isBoundaryChanneledBase_iff_of_iso I

/-- On `(ℓ,1)` representatives the general predicate is the one from
`KMSWLeftEndpointCarrier` (Definition 3.17, first form, -/
theorem isChanneled_iff_isBoundaryChanneled (R : KMSWMapRep ℓ 1 n) :
    R.IsChanneled ↔ R.IsBoundaryChanneled :=
  Iff.rfl

end KMSWMapRep

namespace KMSWMapIsoClass

variable {ℓ r n : ℕ}

/-- to KMSW map isomorphism classes of any boundary lengths. Helper toward
result; simple-boundary restriction not assumed. -/
@[expose] def IsChanneled (q : KMSWMapIsoClass ℓ r n) : Prop :=
  Quotient.lift (fun R : KMSWMapRep ℓ r n => R.IsChanneled)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      exact propext (KMSWMapRep.isChanneled_iff_of_iso R R' I)) q

/-- The descended predicate agrees with the representative predicate. Helper,
not the paper result. -/
@[simp] theorem isChanneled_mk (R : KMSWMapRep ℓ r n) :
    IsChanneled (KMSWMapIsoClass.mk R) ↔ R.IsChanneled :=
  Iff.rfl

/-- On `(ℓ,1)` classes the general predicate is the one from
`KMSWLeftEndpointCarrier` (Definition 3.17, first form, -/
theorem isChanneled_iff_isBoundaryChanneled (q : KMSWMapIsoClass ℓ 1 n) :
    q.IsChanneled ↔ q.IsBoundaryChanneled := by
  induction q using KMSWMapIsoClass.ind with
  | h R => exact Iff.rfl

end KMSWMapIsoClass

end DirectedDistances.PlanarMap
