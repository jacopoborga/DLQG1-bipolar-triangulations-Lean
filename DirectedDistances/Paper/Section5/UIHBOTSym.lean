 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.Prop59UIHBOTSymProvider

/-!
# Proposition 5.9 (`prop-uihbot-sym`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/



















public section
noncomputable section
namespace DirectedDistances.Paper.Section5

open MeasureTheory
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5

 
local instance instBorelD39Class_PaperUIHBOTSym :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance instBorelSpaceD39Class_PaperUIHBOTSym :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

 
theorem prop_uihbot_sym :
    uibhbotSourceGeometricClassLaw.map prop59GeometricClassMirror =
      uibhbotSourceGeometricClassLaw :=
 
by exact DirectedDistances.PaperProofs.SourceResults.prop_uihbot_sym_source_provider
 
 

end DirectedDistances.Paper.Section5
 
