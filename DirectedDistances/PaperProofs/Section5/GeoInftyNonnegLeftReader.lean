/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyIndCodeLevel







public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Code" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)

/-- Helper toward Lemma 5.5: the complete nonnegative left-side code
observation, retaining the prefix, hatted-left, and primed coordinates. -/
structure LPlusSidePresentation (x : XDP) where
  code : Code

/-- Helper toward Lemma 5.5: the cylinder sigma algebra of all three codes. -/
noncomputable instance (x : XDP) : MeasurableSpace (LPlusSidePresentation x) :=
  MeasurableSpace.comap LPlusSidePresentation.code inferInstance

/-- Helper toward Lemma 5.5: retain all three input codes in the presentation. -/
@[expose] def decodeLPlus (x : XDP) (_k : ℤ) (c : Code) :
    LPlusSidePresentation x := ⟨c⟩

/-- Helper toward Lemma 5.5: decoding is measurable for the specified
cylinder sigma algebra. -/
theorem measurable_decodeLPlus (x : XDP) (k : ℤ) :
    Measurable (decodeLPlus x k) :=
  measurable_comap_iff.mpr measurable_id

/-- Helper toward Lemma 5.5: decoding preserves the entire observed triple. -/
theorem decodeLPlus_code (x : XDP) (k : ℤ) (c : Code) :
    (decodeLPlus x k c).code = c := rfl

/-- Helper toward Lemma 5.5: the code projection is measurable. -/
theorem measurable_lPlusSidePresentation_code (x : XDP) :
    Measurable (LPlusSidePresentation.code (x := x)) := comap_measurable _

/-- Helper toward Lemma 5.5: reading the code after decoding recovers every
presentation. -/
theorem LPlusSidePresentation.decode_code {x : XDP}
    (r : LPlusSidePresentation x) (k : ℤ) :
    decodeLPlus x k r.code = r := rfl

/-- Helper toward Lemma 5.5: the presentation-valued reader of the
nonnegative left observation is almost-everywhere measurable. -/
theorem aemeasurable_decodeLPlus_leftSideObsNonneg (x : XDP) (k : ℤ) :
    AEMeasurable (fun W => decodeLPlus x k (leftSideObsNonneg x k W))
      wholePlaneIIDCodeMeasure :=
  (measurable_decodeLPlus x k).comp_aemeasurable
    ((aemeasurable_boundaryFourObservations x k 0).prodMk
      ((aemeasurable_boundaryFourObservations x k 1).prodMk
        (aemeasurable_boundaryFourObservations x k 3)))














end DirectedDistances.PaperProofs.Section5
