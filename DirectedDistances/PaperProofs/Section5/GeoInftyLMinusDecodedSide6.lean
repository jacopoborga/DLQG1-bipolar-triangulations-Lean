/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusDecodedSide5

/-! module records code-fiber invariance for the corrected optional class reader.
It does not claim class-reader measurability or paper completion. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The corrected optional reader factors through
the complete two-block presentation code. This is full-code invariance; it
does not assert finite-prefix dependence. -/
theorem LMinusSidePresentation.classOption4_eq_of_code_eq
    {x : XDP} (r r' : LMinusSidePresentation x)
    (hc : r.code = r'.code) : r.classOption4 = r'.classOption4 := by
  by_cases hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code
  · have hq' : ∃ q : LMinusPreimage x, lMinusCodeOf q = r'.code :=
      ⟨hq.choose, hq.choose_spec.trans hc⟩
    rw [r.classOption4_eq_some hq.choose hq.choose_spec,
      r'.classOption4_eq_some hq.choose (hq.choose_spec.trans hc)]
  · have hq' : ¬ ∃ q : LMinusPreimage x, lMinusCodeOf q = r'.code := by
      rintro ⟨q, hqCode⟩
      exact hq ⟨q, hqCode.trans hc.symm⟩
    rw [r.classOption4_eq_none_iff.mpr hq,
      r'.classOption4_eq_none_iff.mpr hq']















































end DirectedDistances.PaperProofs.Section5
