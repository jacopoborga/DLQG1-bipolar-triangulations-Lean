/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.FutureMapLawIdentified

/-! Supporting lemmas for paper labels `prop-future-map-law` (see CORRESPONDENCE.md). -/

/-! # Isolated proof provider for Proposition 5.1 (prop-future-map-law)


Reading: for every n : ℤ, hat M_{n,inf} and hat M'_{n,inf} are the KMSW
maps of the hatted and primed codes of the whole-plane stream shifted by n,
encoded by `futureMapShiftedCodePath n`. Independence is rendered as
independence of these generating codes together with a.s. faithful rooted
planar-map identification of each map with the KMSW image of its code;
the maps are measurable functions of their codes. "Same law as the UIQBOT"
is rendered as equality of the hatted code law with the UIQBOT Pitman-code
law of the counted Definition 4.1 carrier, together with the hatted rooted-map
clause. Hat M' retains beta-zero. C18 makes the primed root missing and
unoriented, retaining its geometric edge, endpoints and face incidences.
initial triangle convention uses, for k = 1, the triangle with a fresh missing geometric edge joining
the initial vertices of the previously active and newly active edges;
it is unoriented and retains its endpoints and face incidence. Lean streams
start at 0; source edge streams start at 1, and `fun i => ω (i + 1)` is the
raw stream. One a.s. event under `wholePlaneIIDCodeMeasure` supplies the shared
witnesses and both rooted-map identifications for all n : ℤ.

This is exactly the unfolded content of `prop51Statement`, retaining its
exposed `hatRootedMapClause` and `primedRootedMapClause` predicates. The import
closure uses `HatLimitDartIdentification`, without `HatInducedFirstReturn`.
and counting remain the coordinator's responsibility. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5




theorem future_map_law_provider :
    (∀ n : ℤ,
      (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
        (hatLawPrimedCodes ∘ futureMapShiftedCodePath n)) ∧
    (∀ n : ℤ,
      wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
        iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      u = shiftedStream (fun k => W (k + n)) 0 ∧
        ∃ (h : HasFlowLineHits u) (hfin_hat : hatLimitFiniteIncidence u)
          (hfin_primed : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
          hatLawCodes (futureMapShiftedCodePath n W) = hatCodes u h ∧
          hatLawPrimedCodes (futureMapShiftedCodePath n W) =
            primedCode (primedSimInput u) h ∧
          hatRootedMapClause u h hfin_hat ∧
          primedRootedMapClause u h hfin_primed hb) := by
  exact prop51_holds

end DirectedDistances.PaperProofs.SourceResults
