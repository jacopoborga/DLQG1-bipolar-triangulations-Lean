/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59GeometricClassLaw3

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/

/-! # Provider for Proposition 5.9 (`prop-uihbot-sym`)

of the plane is a directed, edge-rooted triangulation with missing boundary edges. That rooted map has the same law as
the UIBHBOT.

Encoding:
- Law: `uibhbotSourceGeometricClassLaw` is the law of the geometric class (rooted embedded map modulo
  orientation-preserving homeomorphism) of the Definition 5.8 object (`Prop516SourceGeometricLaw.lean:127`).
- Reflection: `prop59GeometricClassMirror` (`Prop59GeometricClassLaw.lean:62-99`) is the class-level geometric mirror.
  It keeps present-edge directions and missing tags, and marks the same missing root edge in reversed endpoint order
- Measurable structure: the Borel structure of the installed Definition 3.8 geometric topology.

The proof is `prop59_paper_facing` (`Prop59GeometricClassLaw3.lean:73`), which has no law-equality premise. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5

-- The geometric Borel structure on rooted map classes.
local instance instBorelD39Class_Prop59UIHBOTSymProvider :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance instBorelSpaceD39Class_Prop59UIHBOTSymProvider :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩




theorem prop_uihbot_sym_source_provider :
    uibhbotSourceGeometricClassLaw.map prop59GeometricClassMirror =
      uibhbotSourceGeometricClassLaw :=
  prop59_paper_facing

end DirectedDistances.PaperProofs.SourceResults
