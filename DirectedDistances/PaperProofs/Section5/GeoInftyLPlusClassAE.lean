/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusIndexFree
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable13

/-! # Code factorization for the nonnegative left class reader

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Classical

local notation "LPlusCode" =>
  (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)

/-- Helper toward Lemma 5.5. Two nonnegative left presentations are equal
exactly when their complete three-coordinate codes are equal. -/
theorem lPlusSidePresentation_ext_iff_code_eq
    (x : XDP) (r r' : LPlusSidePresentation x) :
    r = r' ↔ r.code = r'.code := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases r with
    | mk code =>
      cases r' with
      | mk code' =>
        simp_all

/-- Helper toward Lemma 5.5. Read the existing index-specific optional class
reader directly from a complete nonnegative left presentation code. -/
@[expose] noncomputable def lPlusSidePresentationClassOptionCode
    (x : XDP) (k : ℤ) (c : LPlusCode) : Option GeometricSideClass :=
  LPlusSidePresentation.classOptionAt x k (decodeLPlus x k c)

/-- Helper toward Lemma 5.5. The presentation class reader factors through
its complete three-coordinate code, with the given boundary index retained. -/
theorem lPlusSidePresentation_classOptionAt_eq_codeReader
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) :
    LPlusSidePresentation.classOptionAt x k r =
      lPlusSidePresentationClassOptionCode x k r.code := by
  change LPlusSidePresentation.classOptionAt x k r =
    LPlusSidePresentation.classOptionAt x k (decodeLPlus x k r.code)
  rw [LPlusSidePresentation.decode_code]

/-- Helper toward Lemma 5.5. Reading a decoded observation is the code reader
applied to exactly the observed triple. -/
theorem lPlusSidePresentation_classOptionAt_decodeLPlus
    (x : XDP) (k : ℤ) (c : LPlusCode) :
    LPlusSidePresentation.classOptionAt x k (decodeLPlus x k c) =
      lPlusSidePresentationClassOptionCode x k c := rfl






















































end DirectedDistances.PaperProofs.Section5
