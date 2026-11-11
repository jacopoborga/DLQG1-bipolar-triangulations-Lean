/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWProcedureReading

/-! Supporting lemmas for paper labels `thm-kmsw` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.PaperProofs.SourceResults

/-- Isolated source-domain proof provider for Theorem 3.5 (thm-kmsw). -/
theorem kmsw (ℓ r n : ℕ)
    (_hℓ : 1 ≤ ℓ) (_hr : 1 ≤ r) (hn : 1 ≤ n) :
    Function.Bijective
      (@DirectedDistances.KMSW.kmswToMapIsoClass ℓ r n hn) :=
by exact DirectedDistances.KMSW.thm_kmsw_procedureReading ℓ r n hn

end DirectedDistances.PaperProofs.SourceResults
