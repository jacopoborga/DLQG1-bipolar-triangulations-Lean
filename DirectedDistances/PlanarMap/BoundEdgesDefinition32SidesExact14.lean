/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact13
import DirectedDistances.PaperProofs.Section5.Prop516PLFrameInsertion







public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Definition 3.2: first-contact trimming of a simple
polyline at a closed set preserves simplicity, stays in the original image,
and meets that set only at the new endpoint. -/
theorem Polyline.exists_simple_first_contact (p : Polyline) {K : Set ℂ}
    (hK : IsClosed K) (hp : p.IsSimple) (hstart : p.start ∉ K)
    (hmeet : (p.image ∩ K).Nonempty) :
    ∃ q : Polyline, q.start = p.start ∧ q.finish ∈ K ∧ q.IsSimple ∧
      q.image ⊆ p.image ∧ q.image ∩ K = {q.finish} ∧
      q.initialDirection.arg = p.initialDirection.arg := by
  obtain ⟨q, hqs, hqK, hqimage, hqcontact, hqsimple⟩ :=
    Polyline.exists_first_contact_polyline p hK hstart hmeet
  obtain ⟨hqsimple, hqangle⟩ := hqsimple hp
  exact ⟨q, hqs, hqK, hqsimple, hqimage, hqcontact, hqangle⟩
































































































end DirectedDistances.PlanarMap

end
