/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation3

/-! # Finite stage drawing representation continuation

This file makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. The all-stage induction's outer-boundary
word identifies exactly the darts bordering the unique unbounded face as the
outer darts of the finite directed KMSW map. This proves the
`StageGeom.dartBorders_iff` field for the drawing and exterior face supplied
by `kmswStageGeometry_induction_all`. -/
theorem kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face),
      P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d := by
  obtain ⟨Q, _, _, hfaces, _, _⟩ := kmswStageGeometry_induction_all w
  obtain ⟨U, hU, hunique, hborder⟩ := hfaces n
  refine ⟨Q n, U, hU, hunique, ?_⟩
  intro d
  rw [hborder, kmswStage_isOuter_iff_boundary]
























/- Conditioned on the missing StageGeom construction and a base representation,
the two remaining fields of `D39DrawingRepresentationData3` have the exact
binders:

    ∀ (M : D39RootedMap) (B : D39DomainRootedMapV2)
      (hbase : D39DrawingRepresentationData M B),
      (∀ d : M.core.D,
        D39TopologicalCcwSuccessor
          {e | rootedLocallyFiniteVertexClass M.core.rot e =
            rootedLocallyFiniteVertexClass M.core.rot d}
          (d39DrawingDartArc B hbase) d (M.core.rot d)) ∧
      (∀ d : M.core.D
        (v : RootedLocallyFiniteVertex M.core.D M.core.rot),
        B.map.toPlaneMapWithMissing.pos (hbase.vertexEquiv v) ∈
          frontier (hbase.faceOfDart d).val ↔
        ∃ e : M.core.D,
          Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
            rootedLocallyFiniteVertexClass M.core.rot e = v)

The three checked routes and their obstructions are recorded at
`Prop516StageDrawingRepresentation3.lean` above the original residual fields:
the finite-star straightening route and the cyclic-order side route do not
prove the first field for an arbitrary represented drawing; the face-orbit
and corner-sector routes do not give the global frontier/incidence
equivalence in the second field. -/

/- The finite-sample rooted-map identification remains conditional on the two
preceding constructions. Its full target is: for `ell n : ℕ`, `hell : 0 < ell`,
and

    p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell,

let

    c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
    k := Fin.cast (by omega : ell = (ell + 1) - 1) p.2
    w := finiteCodeExtend (n := n + 1) c.val,

and for the stage drawing `P : StageDrawing w n` with its needed `StageGeom`
certificate, construct a source-specific `B : D39DomainRootedMapV2` and prove

    D39DrawingRepresentationData3
      (diskRootedD39MapOfSample n ell hell p) B.

The rooted map to identify is exactly `diskRootedMapOfCodeMark c k`. The
identification must retain vertex and individual-dart equivalences, face
correspondence, missing tags, reversal, rotation, and the ordered root dart.
The three checked routes are direct comparison of finite dart carriers and
root marks, transport through the stage rooted-mirror map, and construction
from the KMSW boundary word and its edge tags. None supplies the required
stage-to-code-mark rooted-map isomorphism. -/

end DirectedDistances.PaperProofs.Section5

end
