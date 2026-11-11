module

public import DirectedDistances.KMSW.BoundaryLabelling

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann); not a paper result. The source
boundary vertices `x_k` and the hit-indexed labels are described in -/
theorem boundaryVertex_mem_stageLLLRVertices (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    (k ≤ 0 →
      ∃ n e, e ∈ (kmswStage w n).LL ∧
        ((kmswStage w n).west e = boundaryVertex w h k ∨
          (kmswStage w n).east e = boundaryVertex w h k)) ∧
    (0 ≤ k →
      ∃ n e, e ∈ (kmswStage w n).LR ∧
        ((kmswStage w n).west e = boundaryVertex w h k ∨
          (kmswStage w n).east e = boundaryVertex w h k)) := by
  constructor
  · intro hk
    by_cases hkneg : k ≤ -1
    · let n := boundaryHitTime w h k
      let e := kmswLLCreatedEdge w n
      have hpersist := boundary_left_edge_persistent w h hkneg
      have hstage := hpersist.2 n le_rfl
      exact ⟨n, e, hstage.1, Or.inl hstage.2.2.1⟩
    · have hkzero : k = 0 := by omega
      subst k
      have hstage :=
        (boundary_left_edge_persistent w h (k := -1) (by omega)).2
          (boundaryHitTime w h (-1)) le_rfl
      exact ⟨boundaryHitTime w h (-1), kmswLLCreatedEdge w
        (boundaryHitTime w h (-1)), hstage.1, Or.inr (by simpa using hstage.2.2.2)⟩
  · intro hk
    by_cases hkzero : k = 0
    · subst k
      obtain ⟨_, hwest, _, _⟩ := boundaryVertex_root_edge w h
      exact ⟨0, 0, by simp [kmswStage, kmswInit], Or.inl hwest⟩
    · have hkpos : 1 ≤ k := by omega
      obtain ⟨N, _, hright⟩ := boundaryVertex_right_edge w h hkpos
      have hstage := hright N le_rfl
      exact ⟨N, act w (boundaryHitTime w h k), hstage.1,
        Or.inl hstage.2.2.1⟩

/-- Helper toward Theorem 1.4 (thm-busemann); not a paper result. The source
boundary vertices `x_k` and the hit-indexed labels are described in -/
theorem stageLLLRVertex_eq_boundaryVertex (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : ℕ)
    (hv : ∃ n e,
      (e ∈ (kmswStage w n).LL ∨ e ∈ (kmswStage w n).LR) ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)) :
    ∃ k : ℤ, boundaryVertex w h k = v :=
  boundaryVertex_covers_lowerBoundary w h v hv

/-- Helper toward Theorem 1.4 (thm-busemann); not a paper result. The source
boundary vertices `x_k` and the hit-indexed labels are described in -/
theorem boundaryVertex_range_eq_stageLLLRVertices (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    Set.range (boundaryVertex w h) =
      {v | ∃ n e,
        (e ∈ (kmswStage w n).LL ∨ e ∈ (kmswStage w n).LR) ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} := by
  ext v
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨hLL, hLR⟩ := boundaryVertex_mem_stageLLLRVertices w h k
    by_cases hk : k ≤ 0
    · obtain ⟨n, e, he, hend⟩ := hLL hk
      exact ⟨n, e, Or.inl he, hend⟩
    · have hkpos : 0 ≤ k := by omega
      obtain ⟨n, e, he, hend⟩ := hLR hkpos
      exact ⟨n, e, Or.inr he, hend⟩
  · intro hv
    obtain ⟨k, hk⟩ := stageLLLRVertex_eq_boundaryVertex w h v hv
    exact ⟨k, hk⟩

end DirectedDistances.KMSW
