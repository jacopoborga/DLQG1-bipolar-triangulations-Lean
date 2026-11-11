module

public import DirectedDistances.PlanarMap.D39MapCore
public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorShifted
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorContinuity
public import DirectedDistances.PlanarMap.Prop59RootMarkFacts
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic

/-! Helper toward Proposition 5.9 (prop-uihbot-sym, convention B mirror in the local topology topology);
not a paper result.


STOP: the source-plane mirror has not been constructed on the local topology carrier.
`D39MapCore.rot` and `edgeInv` specify only a rotation system; the core has no
plane-realization or global planarity field. `missing_outer` identifies a marked
face-permutation orbit, without identifying an unbounded complementary component.
`D39FiniteBall.original`, as constructed by `d39FacedBall`, selects completely
retained ambient face-permutation orbits via `d39BallContainsOriginalFace`.
Its interpretation as precisely the source's retained complementary faces,
including their boundary vertices, is the blocking correspondence below.
`D39BallGenusZero` is already explicitly open in `D39Ball.lean`; proving only
finite-ball genus zero would not supply the missing plane correspondence.

The parameters below describe candidate geometric data of a realization. No
realization is constructed or presumed, and no properness or one-endedness
condition is substituted for the source category. The proposition records the
face-and-boundary sub-obligation only; it does not certify an edge embedding or
its compatibility with reflection. Those must also be supplied before transport.
The proposition is OPEN, has no proof, and is never used as a hypothesis here.

Convention B applies to the canonical missing-root mark. Swapping the dart of
an arbitrary `D39RootMark.present` while preserving `tail` need not give a valid
present mark. No universal endpoint-swap operation on present marks is claimed.
The missing tags and present-edge orientations themselves are available in the
core and are not the face-correspondence obstruction.

No local topology mirror, shifted ball-class determinacy, continuity, or involution theorem
is claimed. The helper-topology mirror results are not promoted to local topology results. -/

public section

namespace DirectedDistances.PlanarMap












@[expose] def prop59D39PlaneFaceCorrespondenceOpen
    (M : D39RootedMap) (image : Set ℂ)
    (vertexPos : RootedLocallyFiniteVertex M.core.D M.core.rot → ℂ)
    (leftFace : M.core.D → Set ℂ) : Prop :=
  (∀ d, ∃ z, z ∉ image ∧ leftFace d = connectedComponentIn imageᶜ z) ∧
    (∀ z, z ∉ image → ∃ d, leftFace d = connectedComponentIn imageᶜ z) ∧
    (∀ d e, leftFace d = leftFace e ↔
      Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e) ∧
    (∀ d v, vertexPos v ∈ frontier (leftFace d) ↔
      ∃ e, Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
        d39VertexClass M e = v) ∧
    (∀ r, 0 < r → ∀ d, d39BallContainsOriginalFace M r d ↔
      ∀ v, vertexPos v ∈ frontier (leftFace d) → v ∈ d39BallVertices M r) ∧
    (∀ R : ℝ, ∃ z ∈ leftFace M.core.outer, R < ‖z‖)

end DirectedDistances.PlanarMap
