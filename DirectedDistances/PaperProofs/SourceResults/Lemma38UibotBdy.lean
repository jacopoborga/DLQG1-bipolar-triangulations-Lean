/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.Lemma38Statement

/- # Isolated proof provider for Lemma 3.10 (`lem-uibot-bdy`)

`DirectedDistances.KMSW.Lemma38At` written out for `V = shiftWordInt W n`), and the proof
forwards to the proved helper `DirectedDistances.KMSW.lemma38_uibot_bdy_ae`; installation,
sealing and counting are separate gates. No conclusion or source hypothesis is added.

two-sided code, simultaneously for every integer start `n`, the run `m_{n,∞}` of the shifted code
satisfies C1 (its boundary edges are `λ_n`, the unique ambient rightmost path `P` from the
terminal vertex of `λ_n` and the unique ambient leftmost chain `Q` into its initial vertex),
C2 (run presence of `λ_n` and of `P`, absence of `Q`, ambient presence of `Q`), C3 (every run
vertex has a present outgoing edge, and a present incoming edge exactly off the left boundary)
and C4 in both readings (intrinsic rightmost rays in `m_{n,∞}` and ambient rightmost rays in
`m_{-∞,∞}` from boundary vertices coalesce after positive times); the shifted map is tied to
the same `m_{-∞,∞}` by a start isomorphism. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap

/-- almost-sure reading of author ruling probability-one scope); packaging only. -/
theorem lem_uibot_bdy :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      (let V := shiftWordInt W n
      ∃ (H : WholePlaneRotationHypothesis V)
        (_h : BoundaryHitWitnesses (shiftedStream V 0)),
        let w := shiftedStream V 0
        let incl := wholePlaneEdgeι V 0
        let lam := m0CutLambdaZero V
        ∃ (P : WholePlaneRightmostRay V H)
          (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam)),
          lam = wholePlaneEdgeι V 0 0 ∧
          P.vertex 0 = wholePlaneEdgeEast V lam ∧
          (∀ P' : WholePlaneRightmostRay V H,
            P'.vertex 0 = wholePlaneEdgeEast V lam →
              P'.vertex = P.vertex ∧ P'.edge = P.edge) ∧
          (∀ Q' : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam),
            Q'.vertex = Q.vertex ∧ Q'.edge = Q.edge) ∧
          incl '' kmswRunBoundaryEdges w =
            {lam} ∪ Set.range P.edge ∪ Set.range Q.edge ∧
          (∀ v : ℕ, RunBoundaryVertex w v ↔
            wholePlaneVertexι V 0 v ∈ Set.range P.vertex ∪ Set.range Q.vertex) ∧
          EdgePresent w 0 ∧
          (∀ e ∈ kmswRunBoundaryEdges w,
            (incl e ∈ ({lam} ∪ Set.range P.edge) → EdgePresent w e) ∧
            (incl e ∈ Set.range Q.edge → ¬ EdgePresent w e)) ∧
          (∀ j : ℕ, wholePlaneEdgePresent V (Q.edge j) ∧
            wholePlaneLeftmostIncomingAt V H (Q.vertex j) (Q.edge j) ∧
            wholePlaneEdgeEast V (Q.edge j) = Q.vertex j) ∧
          (∀ j : ℕ, wholePlaneEdgeWest V (Q.edge j) = Q.vertex (j + 1)) ∧
          (∀ v : ℕ,
            (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
            ((∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
              wholePlaneVertexι V 0 v ∉ Set.range Q.vertex)) ∧
          (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0), R.vertex 0 = v) ∧
          (∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = R'.vertex 0 → R.vertex = R'.vertex ∧ R.edge = R'.edge) ∧
          (∀ R : KMSWRunRightmostRay w (H.1 0),
            wholePlaneVertexι V 0 (R.vertex 0) = P.vertex 0 →
              ∀ i, wholePlaneVertexι V 0 (R.vertex i) = P.vertex i ∧
                incl (R.edge i) = P.edge i) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ R R' : KMSWRunRightmostRay w (H.1 0),
              R.vertex 0 = x → R'.vertex 0 = x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  R.vertex (s + t) = R'.vertex (s' + t) ∧
                  R.edge (s + t) = R'.edge (s' + t)) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
              edgeWest w e = x → edgeWest w e' = x' →
              ∀ R R' : KMSWRunRightmostRay w (H.1 0),
                R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
                  ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                    R.vertex (s - 1 + t) = R'.vertex (s' - 1 + t) ∧
                    R.edge (s - 1 + t) = R'.edge (s' - 1 + t)) ∧
          (∀ x : ℕ, RunBoundaryVertex w x →
            ∃ P1 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ P1 P2 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x →
              P2.vertex 0 = wholePlaneVertexι V 0 x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  P1.vertex (s + t) = P2.vertex (s' + t))) ∧
      Nonempty (WholePlaneStartIso W n) := by
  exact DirectedDistances.KMSW.lemma38_uibot_bdy_ae

end DirectedDistances.PaperProofs.SourceResults
