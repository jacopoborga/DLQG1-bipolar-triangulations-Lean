 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.KMSW

/-!
# Theorem 3.5 (`thm-kmsw`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/




































public section
namespace DirectedDistances.Paper.Section3



theorem kmsw (ℓ r n : ℕ)
    (_hℓ : 1 ≤ ℓ) (_hr : 1 ≤ r) (hn : 1 ≤ n) :
    Function.Bijective
      (@DirectedDistances.KMSW.kmswToMapIsoClass ℓ r n hn) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.kmsw ℓ r n _hℓ _hr hn
 
 

end DirectedDistances.Paper.Section3
 
