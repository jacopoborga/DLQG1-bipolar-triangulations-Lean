module
public import Palomar.Principal.Support.HalfPlaneSource
@[expose] public section
noncomputable section
attribute [local instance] DLQG1.Palomar.GeometryInterface.metric DLQG1.Palomar.GeometryInterface.topology
namespace DLQG1.Palomar.Principal
open MeasureTheory
open DLQG1.Palomar.GeometryInterface DLQG1.Palomar.GeometryLawMinimal
local instance principalMeasurable : MeasurableSpace MapClass := borel MapClass
local instance principalBorel : BorelSpace MapClass := ⟨rfl⟩
/-- Proposition5.9 for the actual source law, using a proved complete realization characterization. -/
theorem half_plane_reflection : sourceLaw.map mirror = sourceLaw := by
  rw [sourceLaw_eq_source, mirror_eq_source]
  convert DirectedDistances.Paper.Section5.prop_uihbot_sym using 1; rfl
end DLQG1.Palomar.Principal
