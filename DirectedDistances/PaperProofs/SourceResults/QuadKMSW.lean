/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.QuadKMSWIdentified

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Isolated proof provider for Lemma 5.13 (lem-quad-kmsw)


Reading: hat Z is `sourceQuadrantHatWalk` and hat Z' is
`sourceQuadrantPrimedWalk`, identified with the integrated hatted and primed
codes. Hat M_{0,inf} is `hatRealizedDrawing`, the reachable restricted drawing;
hat M'_{0,inf} is `mhatPrimeDrawing`, with beta-zero retained. Under C18 the
primed root is a missing, unoriented geometric edge. Under initial triangle convention the k = 1
triangle has a fresh missing edge, retaining endpoints and face incidence.
"Is" means rooted planar-map identification: dart, vertex and face
equivalences preserve root, orientation, missing tags, rotation, faces and
exterior. Lean streams start at 0; source edge streams start at 1, and
`fun i => ω (i + 1)` is the raw stream. One a.s. event under `iidCodeMeasure`
supplies the shared witnesses and both walk and rooted-map identifications.

This is exactly the unfolded content of `lemma513Statement`, retaining its
exposed `hatRootedMapClause` and `primedRootedMapClause` predicates. The import
closure uses `HatLimitDartIdentification`, without `HatInducedFirstReturn`.
and counting remain the coordinator's responsibility. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5




theorem quad_kmsw_provider :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin_hat : hatLimitFiniteIncidence w)
        (hfin_primed : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w),
        sourceQuadrantHatWalk w h = integrateCodes (hatCodes w h) ∧
        sourceQuadrantPrimedWalk w h = integrateCodes (primedCode (primedSimInput w) h) ∧
        hatRootedMapClause w h hfin_hat ∧
        primedRootedMapClause w h hfin_primed hb := by
  exact lemma513_holds

end DirectedDistances.PaperProofs.SourceResults
