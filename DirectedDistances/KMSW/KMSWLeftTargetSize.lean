module

public import DirectedDistances.KMSW.KMSWLeftZeroStep

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- target size identity; not the paper result. -/
theorem kmswLeftRep_nonBoundaryEdgeCount_add {l N : ℕ} (R : KMSWMapRep l 1 N)
    (hl : 1 ≤ l) (hN : 2 ≤ N) : R.nonBoundaryEdgeCount + (l + 1) = N := by
  by_cases h : l = 1
  · subst l
    rw [R.nonBoundaryEdgeCount_eq_oneOne hN,
      R.oneOneNonBoundaryEdgeCount_eq_total hN]
    omega
  · have hl2 : 2 ≤ l := by omega
    rw [R.nonBoundaryEdgeCount_eq_leftEndpoint hl2]
    have hcount := innerEdgeCount_add_boundaryLength (toStrongLeftEndpoint R.B hl2)
    change R.leftEndpointNonBoundaryEdgeCount hl2 + (l + 1) =
      R.B.map.toCombinatorialMap.numEdges at hcount
    exact hcount.trans R.edges

/-- target size identity on isomorphism classes; not the paper result. -/
theorem kmswLeftClass_nonBoundaryEdgeCount_add {l N : ℕ}
    (q : KMSWMapIsoClass l 1 N) (hl : 1 ≤ l) (hN : 2 ≤ N) :
    KMSWMapIsoClass.nonBoundaryEdgeCount q + (l + 1) = N := by
  have h := kmswLeftRep_nonBoundaryEdgeCount_add q.out hl hN
  have hq : KMSWMapIsoClass.mk q.out = q := Quotient.out_eq q
  rw [← KMSWMapIsoClass.nonBoundaryEdgeCount_mk, hq] at h
  exact h

/-- target size identity as an interior-count equivalence; not the paper result. -/
theorem kmswLeftClass_interior_iff {l n N : ℕ} (q : KMSWMapIsoClass l 1 N)
    (hl : 1 ≤ l) (hn : 1 ≤ n) (hN : 2 ≤ N) :
    KMSWMapIsoClass.nonBoundaryEdgeCount q = n - 1 ↔ N = n + l := by
  have h := kmswLeftClass_nonBoundaryEdgeCount_add q hl hN
  omega

/-- target size identity's exceptional size is one, with left length one; not the paper result. -/
theorem kmswLeftRep_numEdges_pos_or {l N : ℕ} (R : KMSWMapRep l 1 N)
    (hl : 1 ≤ l) : N ≠ 0 ∧ (N = 1 → l = 1) := by
  have hpos := contour_numEdges_pos R.B
  rw [R.edges] at hpos
  refine ⟨by omega, ?_⟩
  intro hN
  by_contra hleft
  have hl2 : 2 ≤ l := by omega
  have hbound := boundaryLength_le_numEdges (toStrongLeftEndpoint R.B hl2)
  change l + 1 ≤ R.B.map.toCombinatorialMap.numEdges at hbound
  rw [R.edges] at hbound
  omega

/-- target size identity's sole class below size two is m₀; not the paper result.
Heterogeneous equality records equality after identifying both size indices with one. -/
theorem kmswLeftClass_eq_zeroStep_of_lt_two {l N : ℕ}
    (q : {q : KMSWMapIsoClass l 1 N // q.IsChanneled}) (hl : 1 ≤ l)
    (hN : N < 2) : l = 1 ∧ N = 1 ∧ HEq q kmswZeroStepMapClass := by
  have h := kmswLeftRep_numEdges_pos_or q.val.out hl
  have hN1 : N = 1 := by omega
  have hl1 : l = 1 := h.2 hN1
  subst l
  subst N
  exact ⟨rfl, rfl, heq_of_eq (kmswZeroStepMapClass_unique q)⟩

end DirectedDistances.KMSW
