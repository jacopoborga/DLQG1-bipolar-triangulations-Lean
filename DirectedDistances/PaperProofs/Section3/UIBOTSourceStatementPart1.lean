/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section3.BSTopologyDefinition
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassMetric













public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PaperProofs.SourceResults
open scoped ENNReal

universe u

/-- Helper toward Proposition 3.9: the distance on geometric rooted-map
classes is exactly the installed Definition 3.8 distance on representatives,
with every field of the source domain preserved. -/
theorem uibotSourceClass_edist_eq_installed (A B : D39DomainRootedMap.{u}) :
    edist (Quotient.mk d39DomainSetoid A) (Quotient.mk d39DomainSetoid B) =
      d39LocalDistanceV2
        ⟨A.V, A.E, A.map, A.root, A.domain⟩
        ⟨B.V, B.E, B.map, B.root, B.domain⟩ := rfl

/-- Helper toward Proposition 3.9: the installed source definition gives
both the positive-radius infimum and the ball-isomorphism threshold for
the very class distance used by the finite-law convergence theorem. -/
theorem uibotSourceClass_distance_characterization (A B : D39DomainRootedMap.{u}) :
    (edist (Quotient.mk d39DomainSetoid A) (Quotient.mk d39DomainSetoid B) =
      ⨅ r : {r : ℕ // 0 < r},
        ⨅ (_ : Nonempty (D39GeomBallIsoV2 r.1 A.map A.root B.map B.root)),
          (1 / 2 : ℝ≥0∞) ^ r.1) ∧
    (∀ (r : ℕ), 0 < r →
      (edist (Quotient.mk d39DomainSetoid A) (Quotient.mk d39DomainSetoid B) ≤
          (1 / 2 : ℝ≥0∞) ^ r ↔
        Nonempty (D39GeomBallIsoV2 r A.map A.root B.map B.root))) := by
  let A' : D39DomainRootedMapV2.{u} := ⟨A.V, A.E, A.map, A.root, A.domain⟩
  let B' : D39DomainRootedMapV2.{u} := ⟨B.V, B.E, B.map, B.root, B.domain⟩
  have h := DirectedDistances.Paper.Section3.def_bs_topology.{u, 0, 0} A' B' A'
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end DirectedDistances.PaperProofs.Section3
end
