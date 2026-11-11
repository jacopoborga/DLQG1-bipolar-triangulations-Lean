/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination12

/-! The intrinsic adjacent-ray candidate relation descends to marked-side
isomorphism classes. This records candidate existence, without claiming that
an intrinsic leftmost candidate has been selected. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: existence of an intrinsic adjacent metric
candidate is invariant under a marked-side isomorphism. The witnesses are
transported pointwise, retaining their dart identities. -/
theorem geometricSideAdjacentGeodesicCandidate_exists_iff
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (longest : Bool) :
    (∃ v d : ℕ → GeometricSideCell M,
      geometricSideAdjacentGeodesicCandidate M longest v d) ↔
    (∃ v d : ℕ → GeometricSideCell N,
      geometricSideAdjacentGeodesicCandidate N longest v d) := by
  constructor
  · rintro ⟨v, d, h⟩
    exact ⟨I.equiv ∘ v, I.equiv ∘ d,
      (geometricSideAdjacentGeodesicCandidate_iff I longest v d).1 h⟩
  · rintro ⟨v, d, h⟩
    have hm := (geometricSideAdjacentGeodesicCandidate_iff
      (GeometricSideMarkedIso.symm I) longest v d).1 h
    exact ⟨I.equiv.symm ∘ v, I.equiv.symm ∘ d, hm⟩

/-- Helper toward Lemma 5.6: the marked-side classes admitting an intrinsic
adjacent metric candidate, as a quotient predicate. This predicate records
nonemptiness only; it does not select a ray. -/
@[expose] def geometricSideClassHasAdjacentGeodesicCandidate
    (longest : Bool) : GeometricSideClass → Prop :=
  Quotient.lift
    (fun M => ∃ v d : ℕ → GeometricSideCell M,
      geometricSideAdjacentGeodesicCandidate M longest v d)
    (fun _ _ h => h.elim fun I =>
      propext (geometricSideAdjacentGeodesicCandidate_exists_iff I longest))

/-- Helper toward Lemma 5.6: the quotient predicate has its stated intrinsic
meaning on every representative. -/
theorem geometricSideClassHasAdjacentGeodesicCandidate_mk
    (longest : Bool) (M : GeometricSideSubmap) :
    geometricSideClassHasAdjacentGeodesicCandidate longest (geometricSideClass M) ↔
      ∃ v d : ℕ → GeometricSideCell M,
        geometricSideAdjacentGeodesicCandidate M longest v d :=
  Iff.rfl








































































end DirectedDistances.PaperProofs.Section5
