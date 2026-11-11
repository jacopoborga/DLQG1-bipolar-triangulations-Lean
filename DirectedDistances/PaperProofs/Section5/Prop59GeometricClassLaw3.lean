/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59GeometricClassLaw2

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/

/- Helper toward Proposition 5.9 (`prop-uihbot-sym`, -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9: use the geometric Borel sigma algebra. -/
local instance prop59GeometricClassLaw3_measurable :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}

/-- Helper toward Proposition 5.9: the geometric sigma algebra is Borel. -/
local instance prop59GeometricClassLaw3_borel :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩








































theorem prop59_paper_facing :
    uibhbotSourceGeometricClassLaw.map prop59GeometricClassMirror =
      uibhbotSourceGeometricClassLaw := by
  exact prop59_sourceGeometricClassLaw_mirror_invariant

end DirectedDistances.PaperProofs.Section5
end
