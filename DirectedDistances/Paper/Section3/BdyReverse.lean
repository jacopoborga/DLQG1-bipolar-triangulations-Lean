 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BdyReverse

/-!
# Lemma 3.18 (`lem-bdy-reverse`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/




























public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.PlanarMap



theorem bdy_reverse (ℓ r k N : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r) :
    Function.Bijective
        (KMSWMapIsoClass.kmswRightPrefixReversalClassMap (ℓ := ℓ) (r := r) (n := N)
          k hℓ hk hkr) ∧
      ∀ (R : KMSWMapRep ℓ r N) (hc : R.IsChanneled) (hs : R.IsSimpleOuterBoundary),
        (KMSWMapIsoClass.kmswRightPrefixReversalClassMap k hℓ hk hkr
          ⟨KMSWMapIsoClass.mk R, (KMSWMapIsoClass.isChanneled_mk R).mpr hc,
            (KMSWMapIsoClass.isSimpleOuterBoundary_mk R).mpr hs⟩).val =
          KMSWMapIsoClass.mk (R.kmswRightPrefixReverseRep k hℓ hk hkr hs hc) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.bdy_reverse ℓ r k N hℓ hk hkr
 
 

end DirectedDistances.Paper.Section3
 
