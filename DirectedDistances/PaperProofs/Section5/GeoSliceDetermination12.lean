/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination11





public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: the adjacent metric candidate predicate is
invariant under marked-side isomorphism in both directions. The ray is mapped
pointwise, retaining its dart identities, boundary incidence and every
attained optimal segment. -/
theorem geometricSideAdjacentGeodesicCandidate_iff
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (longest : Bool) (v d : ℕ → GeometricSideCell M) :
    geometricSideAdjacentGeodesicCandidate M longest v d ↔
      geometricSideAdjacentGeodesicCandidate N longest (I.equiv ∘ v) (I.equiv ∘ d) := by
  constructor
  · exact geometricSideAdjacentGeodesicCandidate_map I longest
  · intro h
    have hm := geometricSideAdjacentGeodesicCandidate_map
      (GeometricSideMarkedIso.symm I) longest h
    simp only [GeometricSideMarkedIso.symm] at hm
    have hv : I.equiv.symm ∘ I.equiv ∘ v = v := by
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    have hd : I.equiv.symm ∘ I.equiv ∘ d = d := by
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [hv, hd] at hm
    exact hm












































end DirectedDistances.PaperProofs.Section5
