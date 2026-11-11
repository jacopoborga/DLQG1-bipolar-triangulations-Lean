 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section4.RenewalTimeExistsUnique

/-!
# Lemma 4.9 (`lem-renewal`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/







public section
namespace DirectedDistances.Paper.Section4


@[expose] noncomputable def renewalTime (m : ℕ) (p : ℕ → ℤ × ℤ) : ℕ∞ :=
 
  Classical.choose (existsUnique_renewalTime m p)
 
 

end DirectedDistances.Paper.Section4
 
