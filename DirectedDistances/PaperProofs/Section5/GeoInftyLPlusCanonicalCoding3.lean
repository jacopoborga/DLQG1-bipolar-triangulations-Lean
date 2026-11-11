/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCanonicalCoding2

/-! Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "B4" => lPlusCodeBlockSide4 hτ hp P hqMode Tpath hfin hleft hk
local notation "C4" => lPlusCanonicalSide4 hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5. Equality of all geometric fields gives
equality of whole-side records. -/
theorem geometricSideSubmap_ext {M N : GeometricSideSubmap}
    (hvertices : M.vertices = N.vertices) (hedges : M.edges = N.edges)
    (hwest : M.west = N.west) (heast : M.east = N.east)
    (hpresent : M.present = N.present) (hrotation : M.rotation = N.rotation)
    (hfaceNext : M.faceNext = N.faceNext) (hroot : M.root = N.root)
    (hboundary : M.boundary = N.boundary) (hseam : M.seam = N.seam) : M = N := by
  cases M
  cases N
  simp_all

/-- Helper toward Lemma 5.5. The canonical side is equal as a complete
geometric record to decoder 4. -/
theorem lPlusCanonicalSide4_eq_codeBlockSide4 : C4 = B4 := by
  exact geometricSideSubmap_ext
    (lPlusCanonicalSide4_vertices_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_edges_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_west_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_east_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_present_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_rotation_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_faceNext_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_root_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_boundary_eq_old hqMode hτ hp P Tpath hfin hleft hk)
    (lPlusCanonicalSide4_seam_eq_old hqMode hτ hp P Tpath hfin hleft hk)

/-- Helper toward Lemma 5.5. An equality of whole-side records induces the
identity marked isomorphism. -/
noncomputable def geometricSideMarkedIsoOfEq {M N : GeometricSideSubmap}
    (h : M = N) : GeometricSideMarkedIso M N := by
  cases h
  exact { equiv := Equiv.refl _, relation_iff := by intro t u v; rfl }

/-- Helper toward Lemma 5.5. The canonical side has a marked isomorphism
to decoder 4; equality of the complete side records transports every tag. -/
noncomputable def lPlusCanonicalSide4MarkedIso :
    GeometricSideMarkedIso B4 C4 := by
  exact geometricSideMarkedIsoOfEq
    (lPlusCanonicalSide4_eq_codeBlockSide4
      hτ hp P hqMode Tpath hfin hleft hk).symm

/-- Helper toward Lemma 5.5. Decoder 4 and the canonical side have the same
marked isomorphism class. -/
theorem lPlusCanonicalSide4_class_eq_codeBlockSide4 :
    geometricSideClass C4 = geometricSideClass B4 := by
  rw [lPlusCanonicalSide4_eq_codeBlockSide4 hτ hp P hqMode Tpath hfin hleft hk]

/-- Helper toward Lemma 5.5. On the existing nonnegative source-witness
guard, the class reader is the class of the canonical side. -/
theorem LPlusSidePresentation.classOptionAt4_eq_canonical
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (hk : 0 ≤ k)
    (hw : Nonempty (LPlusSidePresentationSourceWitness x k r)) :
    LPlusSidePresentation.classOptionAt4 x k r =
      some (geometricSideClass
        (lPlusCanonicalSide4 (W := (Classical.choice hw).W)
          (h := (Classical.choice hw).h) (k := k)
          (H := (Classical.choice hw).H)
          (hLL := (Classical.choice hw).hLL)
          (longest := (Classical.choice hw).longest)
          (Classical.choice hw).hτ (Classical.choice hw).hp
          (Classical.choice hw).P (Classical.choice hw).hqMode
          (Classical.choice hw).Tpath (Classical.choice hw).hfin
          (Classical.choice hw).hleft hk)) := by
  rw [LPlusSidePresentation.classOptionAt4_eq_some x k r hk hw]
  exact congrArg some
    (lPlusCanonicalSide4_class_eq_codeBlockSide4
      (W := (Classical.choice hw).W) (h := (Classical.choice hw).h)
      (k := k) (H := (Classical.choice hw).H)
      (hLL := (Classical.choice hw).hLL)
      (longest := (Classical.choice hw).longest)
      (Classical.choice hw).hτ (Classical.choice hw).hp
      (Classical.choice hw).P (Classical.choice hw).hqMode
      (Classical.choice hw).Tpath (Classical.choice hw).hfin
      (Classical.choice hw).hleft hk).symm





























end DirectedDistances.PaperProofs.Section5
