module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperAssembly












public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap

attribute [local instance 1100] presentDartQuiver

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: planar boundary-path intersection);
The first and last ordered left-boundary vertices are the source and sink. -/
private theorem boundaryIntersection_endpoints {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) :
    boltzmannSdpUpper_leftVertex q 0 = q.1.2.2.out.B.source ∧
      boltzmannSdpUpper_leftVertex q (Fin.last q.1.1) = q.1.2.2.out.B.sink := by
  let B := q.1.2.2.out.B
  constructor
  · change B.leftPath.vertices.get
      ⟨0, by rw [B.leftPath.vertices_length]; simp⟩ = B.source
    exact B.leftPath.start_vertex
  · change B.leftPath.vertices.get
      ⟨q.1.1, by rw [B.leftPath.vertices_length]; omega⟩ = B.sink
    simpa [B.leftPath.vertices_length] using B.leftPath.end_vertex

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: planar boundary-path intersection);
Shared endpoints settle the source, sink, and equal-index cases. -/
theorem boltzmannSdpUpper_boundaryPathIntersection_degenerate {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) (i j : Fin (q.1.1 + 1))
    (P : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j))
    (Q : Quiver.Path (boltzmannSdpUpper_leftVertex q i) q.1.2.2.out.B.sink)
    (h : i = 0 ∨ j = Fin.last q.1.1 ∨ i = j) :
    ∃ v, v ∈ P.vertices ∧ v ∈ Q.vertices := by
  obtain ⟨hs, ht⟩ := boundaryIntersection_endpoints q
  rcases h with rfl | rfl | rfl
  · exact ⟨_, P.start_mem_vertices, by simpa only [hs] using Q.start_mem_vertices⟩
  · exact ⟨_, by simpa only [ht] using P.end_mem_vertices, Q.end_mem_vertices⟩
  · exact ⟨_, P.end_mem_vertices, Q.start_mem_vertices⟩





@[expose] def boltzmannSdpUpper_strictBoundaryPathIntersection_OPEN : Prop :=
  ∀ r : ℕ, ∀ q : RightVertexMarkedBoltzmannSpace r,
    ∀ i j : Fin (q.1.1 + 1), i ≤ q.2 → q.2 ≤ j →
      0 < i.val → i.val < j.val → j.val < q.1.1 →
        ∀ P : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j),
          ∀ Q : Quiver.Path (boltzmannSdpUpper_leftVertex q i) q.1.2.2.out.B.sink,
            ∃ v, v ∈ P.vertices ∧ v ∈ Q.vertices

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: planar boundary-path intersection);
Exact reduction to the named OPEN strict-interior case. Neither side is asserted. -/
theorem boltzmannSdpUpper_boundaryPathIntersection_iff_strict :
    boltzmannSdpUpper_boundaryPathIntersection ↔
      boltzmannSdpUpper_strictBoundaryPathIntersection_OPEN := by
  constructor
  · intro h r q i j hi hj _ _ _ P Q
    exact h r q i j hi hj P Q
  · intro h r q i j hi hj P Q
    by_cases hi0 : i = 0
    · exact boltzmannSdpUpper_boundaryPathIntersection_degenerate q i j P Q (.inl hi0)
    by_cases hjlast : j = Fin.last q.1.1
    · exact boltzmannSdpUpper_boundaryPathIntersection_degenerate q i j P Q
        (.inr (.inl hjlast))
    by_cases hij : i = j
    · exact boltzmannSdpUpper_boundaryPathIntersection_degenerate q i j P Q
        (.inr (.inr hij))
    have hi0' : i.val ≠ 0 := fun heq => hi0 (Fin.ext heq)
    have hjlast' : j.val ≠ q.1.1 := fun heq => hjlast (Fin.ext heq)
    have hij' : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    have hle : i.val ≤ j.val := Fin.le_iff_val_le_val.mp (hi.trans hj)
    exact h r q i j hi hj (by omega) (by omega) (by omega) P Q

end DirectedDistances.PaperProofs.Section7
