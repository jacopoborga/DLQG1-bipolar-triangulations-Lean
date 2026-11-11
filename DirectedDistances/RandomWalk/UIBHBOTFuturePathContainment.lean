module

public import DirectedDistances.RandomWalk.UIBHBOTFutureInfiniteRay
public import DirectedDistances.PaperProofs.Section5.UIBHBOTFutureSubmapIdentification

/-! Path containment in the UIBHBOT future submap, toward Lemma 5.10

The future submap's vertex and geometric-edge carriers are the ranges of the
shifted-code vertex and edge maps. The lifted ray below identifies each global
ray vertex and edge with its shifted-code representative. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory Quiver
open DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5

/-- Helper toward Lemma 5.10. Every UIBHBOT directed ray from `x_l`, `l ≤ k`,
is contained in the future submap after the `k`th boundary hit, in both
vertices and geometric edges. The accompanying shifted-code ray witnesses
the identification with the future submap carrier. -/
theorem ae_uibhbotFuture_ray_contained_in_submap :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k l : ℤ, l ≤ k →
        ∀ v : ℕ → UIBHBOTPresentVertex W,
          v 0 = ⟨uibhbotFutureVertex l W 0⟩ →
            ∀ a : ∀ n : ℕ, v n ⟶ v (n + 1),
              ∃ h : BoundaryHitWitnesses
                  (fun i => uibhbotFutureCode k W (i + 1)),
                ∃ u : ℕ → PresentVertex
                    (fun i => uibhbotFutureCode k W (i + 1)),
                ∃ e : ∀ n, u n ⟶ u (n + 1),
                  u 0 = ⟨boundaryVertex
                    (fun i => uibhbotFutureCode k W (i + 1)) h (l - k)⟩ ∧
                  (∀ n, (uibhbotFutureToGlobal k W).obj (u n) = v n) ∧
                  (∀ n, ((uibhbotFutureToGlobal k W).map (e n)).val =
                    (a n).val) ∧
                  (∀ n, (v n).id ∈ (uibhbotFutureSubmap k W h).vertices) ∧
                  (∀ n, (a n).val ∈ (uibhbotFutureSubmap k W h).edges) := by
  filter_upwards [ae_uibhbotFuture_infiniteRay_lift_from_source_index]
    with W hLift k l hl v hv a
  obtain ⟨h, u, e, hu0, hobj, hmap, hunique⟩ :=
    hLift k l hl v hv a
  refine ⟨h, u, e, hu0, hobj, hmap, ?_, ?_⟩
  · intro n
    change (v n).id ∈ Set.range (uibhbotFutureVertex k W)
    exact ⟨(u n).id, congrArg UIBHBOTPresentVertex.id (hobj n)⟩
  · intro n
    change (a n).val ∈ Set.range (uibhbotFutureEdge k W)
    exact ⟨(e n).val, hmap n⟩

end DirectedDistances.RandomWalk
