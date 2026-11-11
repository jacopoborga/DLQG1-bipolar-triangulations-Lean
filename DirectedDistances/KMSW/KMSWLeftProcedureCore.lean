/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWLeftProcedureBijection
public import DirectedDistances.KMSW.KMSWBoundaryPrefixForward
public import DirectedDistances.KMSW.KMSWBoundaryPrefixConverse





























public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The `(1,ℓ)`-side bijection of the proof of `lem-kmsw-left`
receives the `ℓ − 1` forced `D` steps and is sent through the procedure-reading
KMSW bijection; the image is exactly the boundary-channeled classes in
`M_{1,ℓ}` with `n + ℓ` edges. -/
@[expose] noncomputable def kmswLeftRightSideEquiv (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    KMSWLeftWalkClass ℓ n ≃
      {q : KMSWMapIsoClass 1 ℓ (n + ℓ) // q.IsChanneled} :=
  (kmswLeftWalkCutAdd ℓ n hℓ).symm.trans
    (kmswPrefixChanneledEquivOf (ℓ := ℓ) (N := n + ℓ) (by omega)
      (fun c hc => kmswToMapIsoClass_isChanneled_of_prefix (by omega) c hc)
      (fun c hc => prefix_of_kmswToMapIsoClass_isChanneled (by omega) c hc))

/-- The bijection is the KMSW procedure applied to the walk with the `ℓ − 1` -/
theorem kmswLeftRightSideEquiv_apply (ℓ n : ℕ) (hℓ : 1 ≤ ℓ)
    (w : KMSWLeftWalkClass ℓ n) :
    (kmswLeftRightSideEquiv ℓ n hℓ w).val =
      kmswToMapIsoClass (by omega) ((kmswLeftWalkCutAdd ℓ n hℓ).symm w).val := by
  simp [kmswLeftRightSideEquiv]

/-- Bijectivity form of `kmswLeftRightSideEquiv`

Helper toward `lem-kmsw-left`, not the paper result. It uses the procedure
still needs the class-level endpoint reversal and the direct-run
correspondence. -/
theorem lem_kmsw_left_procedureReading_rightSide (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    Function.Bijective (kmswLeftRightSideEquiv ℓ n hℓ) :=
  (kmswLeftRightSideEquiv ℓ n hℓ).bijective

end DirectedDistances.KMSW
