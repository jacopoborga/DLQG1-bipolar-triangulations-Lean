/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeometricSideClass
public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusLemma55Assembly

/-! # Optional classes of coherent right-side codes

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`),

The optional class below is defined exactly on codes with a coherent preimage.
Its characterization does not assert that the coherent-code range is measurable. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Code" => (ℕ → Option FiniteThinMap)
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The usual optional-class sigma algebra: a set
is measurable exactly when its `some` preimage is measurable. In particular,
`none` is a measurable singleton, separately from the geometric classes. -/
noncomputable instance : MeasurableSpace (Option GeometricSideClass) :=
  MeasurableSpace.map (some : GeometricSideClass → Option GeometricSideClass) inferInstance

/-- Helper toward Lemma 5.5. Including a geometric class as a present value
is measurable for the optional-class sigma algebra. -/
theorem measurable_some_geometricSideClass :
    Measurable (some : GeometricSideClass → Option GeometricSideClass) := by
  rw [measurable_iff_le_map]
  exact le_rfl

/-- Helper toward Lemma 5.5. Absence is a measurable event in the optional
class space; this sigma algebra does not hide the coherent-code domain. -/
theorem measurableSet_optionGeometricSideClass_none :
    MeasurableSet ({none} : Set (Option GeometricSideClass)) := by
  change MeasurableSet
    ((some : GeometricSideClass → Option GeometricSideClass) ⁻¹' {none})
  have he : (some : GeometricSideClass → Option GeometricSideClass) ⁻¹' {none} = ∅ := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.some_ne_none,
      Set.mem_empty_iff_false]
  rw [he]
  exact MeasurableSet.empty

/-- Helper toward Lemma 5.5. Codes having a coherent right-side preimage.
This is a range definition, without any assertion of range measurability. -/
@[expose] noncomputable def coherentRightSideCodes (x : XDP) : Set Code :=
  Set.range (fun q : Coherent x =>
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1)




@[expose] noncomputable def Psi (x : XDP) (c : Code) : Option GeometricSideClass :=
  (decodeRPlus x 0 c).realization.map geometricSideClass

/-- Helper toward Lemma 5.5. The reader is absent exactly off the coherent-code
range; passing to a marked-isomorphism class creates no new realizations. -/
theorem psi_eq_none_iff (x : XDP) (c : Code) :
    Psi x c = none ↔ c ∉ coherentRightSideCodes x := by
  rw [Psi, Option.map_eq_none_iff,
    RPlusSidePresentation.realization_eq_none_iff]
  rfl

/-- Helper toward Lemma 5.5. The preimage of the measurable absence singleton
is exactly the complement of the coherent-code range. -/
theorem psi_preimage_none (x : XDP) :
    Psi x ⁻¹' {none} = (coherentRightSideCodes x)ᶜ := by
  ext c
  exact psi_eq_none_iff x c

/-- Helper toward Lemma 5.5. Every coherent input is read as the class of its
complete geometric right side, independently of the realization choice. -/
theorem psi_thinSideCode (x : XDP) (q : Coherent x) :
    Psi x (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1) =
      some (geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) := by
  let c := thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1
  have hc : ∃ q' : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1 = c :=
    ⟨q, rfl⟩
  change (decodeRPlus x 0 c).realization.map geometricSideClass = _
  rw [RPlusSidePresentation.realization, decodeRPlus_code, dite_eq_left hc,
    Option.map_some]
  apply congrArg some
  apply (geometricSideClass_eq_iff _ _).mpr
  exact rightSideCode_markedIso_of_eq x hc.choose q hc.choose_spec
















































end DirectedDistances.PaperProofs.Section5
