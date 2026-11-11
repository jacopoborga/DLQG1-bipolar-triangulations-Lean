/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundaryOrder




public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ}

/-- Helper toward Lemma 5.5: at each beta boundary index, the primed and
hatted embeddings use the same geometric edge and opposite endpoint bits. -/
theorem lPlus_primed_beta_boundary_dart
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (i : ℕ) (b : Bool) :
    (boundaryGluingPrimedEdgeMap W h k hτ
        (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
          (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) hfin i),
      b ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ
        (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
          (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) hfin i)) =
      (boundaryGluingHatEdgeMap W h k hτ
        (kmswLeftBoundaryEdge
          (hatCodes (boundaryGluingFutureStream W h k) hτ) i), !b) := by
  simpa only [lMinusPrimedDartImage, boundaryGluingPrimedEdgeMap,
    boundaryGluingHatEdgeMap] using
    (lMinusPrimedDartImage_boundary (W := W) (h := h) (k := k)
      hτ hfin i b)





























end DirectedDistances.PaperProofs.Section5
