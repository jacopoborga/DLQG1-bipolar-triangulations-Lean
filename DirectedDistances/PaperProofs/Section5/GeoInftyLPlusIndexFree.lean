/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE

/-! L-plus realization currently depends on its boundary index. This module
records an index-carrying presentation interface; it does not claim
cross-index invariance or prove the side-identification fields of the
Lemma 5.5 assembly. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Lemma 5.5. Retain the nonnegative boundary index needed by
the existing L-plus realization alongside the complete three-code
presentation. -/
structure LPlusIndexedSidePresentation (x : XDP) where
  boundaryIndex : ℤ
  boundaryIndex_nonneg : 0 ≤ boundaryIndex
  presentation : LPlusSidePresentation x

/-- Helper toward Lemma 5.5. Read an indexed presentation using exactly the
existing index-specific L-plus class reader. The stored index is part of the
reader's input; no index is chosen. -/
@[expose] noncomputable def LPlusIndexedSidePresentation.classOption
    (x : XDP) (r : LPlusIndexedSidePresentation x) :
    Option GeometricSideClass :=
  LPlusSidePresentation.classOptionAt x r.boundaryIndex r.presentation

/-- Helper toward Lemma 5.5. Attach the observation index to the decoded
three-code presentation. -/
@[expose] def decodeLPlusWithIndex (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (c : (ℕ → Fin 3) × (ℕ → Option DirectedDistances.PaperProofs.Section4.FiniteThinMap) × (ℕ → Fin 3)) :
    LPlusIndexedSidePresentation x where
  boundaryIndex := k
  boundaryIndex_nonneg := hk
  presentation := decodeLPlus x k c

/-- Helper toward Lemma 5.5. The indexed reader on a decoded observation is
the existing reader at the index carried by that observation. -/
theorem LPlusIndexedSidePresentation.classOption_decodeLPlusWithIndex
    (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (c : (ℕ → Fin 3) × (ℕ → Option DirectedDistances.PaperProofs.Section4.FiniteThinMap) × (ℕ → Fin 3)) :
    LPlusIndexedSidePresentation.classOption x
        (decodeLPlusWithIndex x k hk c) =
      LPlusSidePresentation.classOptionAt x k (decodeLPlus x k c) := rfl

/-- Helper toward Lemma 5.5. Reading any indexed presentation is definitionally
the existing class reader at its stored index. -/
theorem LPlusIndexedSidePresentation.classOption_eq_classOptionAt
    (x : XDP) (r : LPlusIndexedSidePresentation x) :
    LPlusIndexedSidePresentation.classOption x r =
      LPlusSidePresentation.classOptionAt x r.boundaryIndex r.presentation := rfl















































































end DirectedDistances.PaperProofs.Section5
