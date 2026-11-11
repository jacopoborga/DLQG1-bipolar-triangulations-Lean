/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BusemannM0
public import DirectedDistances.KMSW.M0CutBusemannAE
public import DirectedDistances.KMSW.M0CutIdentificationAE

/-! Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: Busemann predicates on the identified future map); not a paper result.

The predicates below literally use the cut data's labels and extended distances.
The existing cut transport accounts for all common reachable injective sequences,
including targets initially presented as ambient whole-plane vertices. LDP differences
use explicit finite natural witnesses. The common almost-sure result is combined with
all clauses of the rooted directed-carrier identification. The inherited plane drawing
and complementary-component face identification are separate obligations. -/

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: Busemann predicates on the identified future map); not a paper result.
The provider's normalized SDP characterization, with the cut labels and distances
substituted. Reachability is in the cut directed graph; unreachable distance stays top. -/
@[expose] def IsIdentifiedM0BusemannSDP {W : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} (D : M0CutData W H) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W, Function.Injective y →
      (∀ j, m0CutReachable W H D.seam (D.x k) (y j) ∧
        m0CutReachable W H D.seam (D.x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        X k' - X k =
          ((D.sdp (D.x k') (y j)).toNat : ℤ) -
            ((D.sdp (D.x k) (y j)).toNat : ℤ)






@[expose] def IsIdentifiedM0BusemannLDP {W : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} (D : M0CutData W H) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W, Function.Injective y →
      (∀ j, m0CutReachable W H D.seam (D.x k) (y j) ∧
        m0CutReachable W H D.seam (D.x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        ∃ n n' : ℕ,
          D.ldp (D.x k') (y j) = ((n : ℕ∞) : WithBot ℕ∞) ∧
          D.ldp (D.x k) (y j) = ((n' : ℕ∞) : WithBot ℕ∞) ∧
          X k' - X k = (n : ℤ) - (n' : ℤ)

section Transfer
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: Busemann predicates on the identified future map); not a paper result.
Deterministic equivalence of the provider SDP predicate and the canonical cut-data
predicate, using the proved identification without an additional premise. -/
theorem boundaryBusemannSDP_iff_identified (X : ℤ → ℤ) :
    IsBoundaryBusemannSDP (boundaryPresentVertex (shiftedStream W 0) h) X ↔
      IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X := by
  let D := m0CutData W H h hLL
  change IsBoundaryBusemannSDP (boundaryPresentVertex (shiftedStream W 0) h) X ↔
    m0CutIsBoundaryBusemannSDP W H D.seam D.x X
  have hx : D.x = fun k =>
      wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k) := by
    funext k
    exact D.x_eq h hLL k
  rw [hx]
  exact (m0Cut_isBoundaryBusemannSDP_iff W H h hLL D.seam
    (m0Cut_seamEdge_iff W H h hLL) X).symm

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: Busemann predicates on the identified future map); not a paper result.
Deterministic equivalence of the provider LDP predicate and the canonical cut-data
predicate. The provider's bounded-path witness proves the finite-cast clauses; it is
supplied almost surely by local finiteness in the provider theorem. -/
theorem boundaryBusemannLDP_iff_identified
    (hbound : PresentPathLengthsBounded (w := shiftedStream W 0)) (X : ℤ → ℤ) :
    IsBoundaryBusemannLDP hbound (boundaryPresentVertex (shiftedStream W 0) h) X ↔
      IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X := by
  let D := m0CutData W H h hLL
  change IsBoundaryBusemannLDP hbound (boundaryPresentVertex (shiftedStream W 0) h) X ↔
    m0CutIsBoundaryBusemannLDP W H D.seam D.x X
  have hx : D.x = fun k =>
      wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k) := by
    funext k
    exact D.x_eq h hLL k
  rw [hx]
  exact (m0Cut_isBoundaryBusemannLDP_iff W H h hLL D.seam
    (m0Cut_seamEdge_iff W H h hLL) hbound X).symm

end Transfer

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: Busemann predicates on the identified future map); not a paper result.
On one whole-plane probability-one event, the full rooted directed-carrier
identification and unique normalized SDP and LDP Busemann predicates hold for the same
canonical cut data. The input `m0Cut_busemann_ae` already transports the provider through
`wholePlaneIIDCodeMeasure_map_shiftedPath 0`, respecting the dummy coordinate.
This identifies the distance predicates, not the inherited drawing or its faces. -/
theorem m0Cut_busemann_identified_ae :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
        ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
          wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
          wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
        (∀ e, (D).missing (E e) ↔
          ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
        (∀ a b, (D).sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ k k', (D).sdp ((D).x k) ((D).x k') =
          DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
        (∀ k k', (D).ldp ((D).x k) ((D).x k') =
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X) := by
  filter_upwards [m0Cut_identification_ae, m0Cut_busemann_ae] with W hid hb
  obtain ⟨H, h, hLL, hid⟩ := hid
  obtain ⟨H', D', hsdp, hldp⟩ := hb
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  let D := m0CutData W H h hLL
  have hx : D'.x = D.x := (m0CutData_eq_fields W H h hLL D' D).2.2.2.2
  change (∃! X : ℤ → ℤ, m0CutIsBoundaryBusemannSDP W H D.seam D'.x X) at hsdp
  change (∃! X : ℤ → ℤ, m0CutIsBoundaryBusemannLDP W H D.seam D'.x X) at hldp
  rw [hx] at hsdp hldp
  exact ⟨H, h, hLL, hid, hsdp, hldp⟩

end DirectedDistances.PaperProofs.Section1
