/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWLeftProcedureEndpoint
public import DirectedDistances.PlanarMap.KMSWLeftEndpointClassNat

/-! # The `(ℓ,1)`-side procedure-reading bijection behind Lemma 3.19

This file discharges the left-naturality hypothesis of
`kmswLeftEndpointSideEquivOf` with `kmswLeftEndpointReverseRep_iso`.

the paper result. Status:

* restricted endpoint reversal only; simple-boundary restriction not assumed.

Two things separate this from the printed statement:

* the declared-missing decoration of the target;
* the correspondence with the KMSW run made directly on the `n`-step walk. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- For `ℓ ≥ 2`, the walks `Z^bc_ℓ` with `n` steps are in bijection with the
boundary-channeled `(ℓ,1)` KMSW map classes with `n + ℓ` edges. The forward
map:

1. prepends the `ℓ − 1` forced `D` steps;
2. applies the KMSW procedure;
3. inverts the restricted endpoint reversal. -/
@[expose] noncomputable def kmswLeftEndpointSideEquiv (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    KMSWLeftWalkClass ℓ n ≃
      {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
  kmswLeftEndpointSideEquivOf ℓ n hℓ
    (fun R R' hbc hbc' h => h.elim fun I =>
      kmswLeftEndpointReverseRep_iso hℓ R R' hbc hbc' I)

end DirectedDistances.KMSW
