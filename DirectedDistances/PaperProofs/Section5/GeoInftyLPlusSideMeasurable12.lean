/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable11

/- # Code-indexed primed compatibility for the nonnegative left presentation

Helpers toward Lemma 5.5 (lem-geo-infty-ind),

indices are ℕ and the local primed dart indices are ℕ × Bool
(GeoInftyNonnegLeftSide.lean:68,99). Their block images are different
objects: they apply boundaryGluingPrimedEdgeMap or
boundaryGluingPrimedVertexMap (BoundaryGeodesicSideGluing.lean:157–158,
GeoInftySideVertices.lean:265–270), which in turn use the witness-specific
primedLimit*Map and future embedding. Those limit maps are defined from
primedAll*Map (KMSW/PrimedImageLimit.lean:108–117), whose recursive
realizations use the witness stream and its stages (KMSW/PrimedSimAll.lean:183–215).
Thus equal presentation codes identify the local code-indexed primed model;
they do not establish equality of the ambient natural-number images.

The line-116 proposition quantifies transports, so this distinction does not
by itself refute that existential statement. Its full truth remains undecided
here. The corrected results below assert only the canonical local-model
identifications, and the one mixed dart kernel case already justified by
disjointness. They do not claim the unresolved cross-component compatibility
needed for the full glued-block kernel equivalences. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Equal presentation codes identify every finite
stage of the local primed simulation. This replaces any proposed equality of
the witnesses' ambient primed vertex or edge IDs: it gives equality of the
code-determined local stages, not equality of their witness-dependent block
images. -/
theorem lPlusSourceWitnessAligned_primedLocalStage_eq_corrected
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r') (m : ℕ)
    (hr : r.code = r'.code) :
    kmswMissingRootStage
        (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ) m =
      kmswMissingRootStage
        (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ) m := by
  have hcode := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
    x k r r' s s' hr
  exact congrArg (fun c : ℕ → Fin 3 => kmswMissingRootStage c m) hcode

/-- Helper toward Lemma 5.5. The common primed code gives the same local
primed limiting rotation. This is the rotation-level code-indexed replacement
for raw ambient-ID identification; it does not assert that either witness's
embedding into its whole-plane map is equal to the other's. -/
theorem lPlusSourceWitnessAligned_primedLocalRotation_eq_corrected
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    kmswInfRot
        (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)
        (primedCode_finiteIncidence (boundaryGluingFutureStream s.W s.h k)
          s.hτ s.hfin) =
      kmswInfRot
        (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ)
        (primedCode_finiteIncidence (boundaryGluingFutureStream s'.W s'.h k)
          s'.hτ s'.hfin) :=
  lPlusSourceWitnessAligned_primedRotation_eq_of_presentation_codes_eq
    x k r r' s s' hr

/-- Helper toward Lemma 5.5. The prefix/hatted dart cross-kernel clause is
preserved under witness change. This corrected restricted statement differs
from GeoInftyLPlusSideMeasurable9.lean:116: it covers only this dart pair,
whose images are disjoint, and does not assert any prefix/primed, vertex, or
primed/hatted compatibility. -/
theorem lPlusSourceWitnessAligned_prefixHattedDartCrossKernel_iff_corrected
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (_phi : GeometricSideMarkedIso M M')
      (_fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      ∀ a : LPlusPrefixDart s.W s.h k,
        ∀ b : LPlusHattedDart M,
          lPlusBlockDartImage (M := M) s.hτ (.inl a) =
              lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
            lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
              lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b))) := by
  exact lPlusSourceWitnessAligned_prefixHattedDartCrossKernel_iff
    x k r r' s s' hk hr





































































































end DirectedDistances.PaperProofs.Section5
