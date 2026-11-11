/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWRightPrefixReversalClass

/-! This single-declaration leaf assembles the checked class-map theorems
`kmswRightPrefixReversalClassMap_bijective` and `kmswRightPrefixReversalClassMap_mk`,
which remain unchanged. The simple-boundary restriction correction (both classes restricted to a simple outer
boundary; operation, range of `k`, boundary lengths and bijective conclusion kept) was
Installation, sealing and counting are separate gates. No conclusion or source hypothesis
is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

/-- Isolated source-domain proof provider for Lemma 3.18 (lem-bdy-reverse) on the -/
theorem bdy_reverse (ℓ r k N : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r) :
    Function.Bijective
        (KMSWMapIsoClass.kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := N)
          k hℓ hk hkr) ∧
      ∀ (R : KMSWMapRep ℓ r N) (hc : R.IsChanneled) (hs : R.IsSimpleOuterBoundary),
        (KMSWMapIsoClass.kmswRightPrefixReversalClassMap k hℓ hk hkr
          ⟨KMSWMapIsoClass.mk R, (KMSWMapIsoClass.isChanneled_mk R).mpr hc,
            (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mpr hs⟩).val =
          KMSWMapIsoClass.mk (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc) :=
by exact ⟨KMSWMapIsoClass.kmswRightPrefixReversalClassMap_bijective k hℓ hk hkr,
  fun R hc hs => KMSWMapIsoClass.kmswRightPrefixReversalClassMap_mk k hℓ hk hkr R hc hs⟩

end DirectedDistances.PaperProofs.SourceResults
