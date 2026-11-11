module

public import DirectedDistances.KMSW.InftyCutEastChain
public import DirectedDistances.KMSW.InftyCutWest
public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.BoundaryEnumeration
public import DirectedDistances.KMSW.LLBoundaryPersistent

import DirectedDistances.KMSW.FlowLineReachability

/-! Supporting lemmas for paper labels `def-uiqbot`, `thm-busemann` (see CORRESPONDENCE.md). -/

/-! # Hit-indexed west-to-east boundary labelling

For a fixed `BoundaryHitWitnesses` witness, this packages the root edge, the
present right-boundary chain, and the missing lower-left chain as one
west-to-east sequence. The hit convention is `eqn-bdy-vertex-hit` and
record sequences are those of `def-uiqbot` and
supports, but does not replace, the author ruling F1 about whether this hit
definition is the geometric labelling intended by `thm-busemann`

The negative hit edges are the missing LL edges created at first hits. They
are not terms of `kmswLeftBoundaryEdge`: that sequence consists of active,
present edges selected by strict future records of `L`. The theorem below
records their disjointness. The finite-stage LL/LR edge set is the
combinatorial lower boundary used here; identification with a geometric -/

public section
namespace DirectedDistances.KMSW

open scoped Classical






@[expose] noncomputable def boundaryOuterEdge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ :=
  if k ≤ -1 then kmswLLCreatedEdge w (boundaryHitTime w h k)
  else if 1 ≤ k then kmswRightBoundaryEdge w k.toNat
  else 0

/-- At index zero the boundary edge is the root edge `λ₀ = (x₀,x₁)`. -/
theorem boundaryOuterEdge_zero (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    boundaryOuterEdge w h 0 = 0 := by
  simp [boundaryOuterEdge]

/-- At a negative index the sequence uses exactly the LL edge created at the
first hit of that level (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryOuterEdge_of_negative (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryOuterEdge w h k = kmswLLCreatedEdge w (boundaryHitTime w h k) := by
  simp [boundaryOuterEdge, hk]

/-- At a positive index the sequence uses the corresponding strict
right-record edge (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryOuterEdge_of_positive (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryOuterEdge w h k = kmswRightBoundaryEdge w k.toNat := by
  have hn : ¬ k ≤ -1 := by omega
  simp [boundaryOuterEdge, hn, hk]

/-- Every consecutive pair in the hit-indexed sequence is joined by its
specified geometric edge, with stable limit-level endpoints. The edge is
present exactly on the root/right side; for `k ≤ -1` it is not a directed
edge and is missing from the LL list's directed-edge carrier
(`eqn-bdy-vertex-hit`, `eqn-bdy-vertex-kmsw`,
vertex sequence supporting, but not replacing, author ruling F1 for -/
theorem boundaryOuterEdge_endpoints (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    edgeWest w (boundaryOuterEdge w h k) = boundaryVertex w h k ∧
      edgeEast w (boundaryOuterEdge w h k) = boundaryVertex w h (k + 1) ∧
      (0 ≤ k → EdgePresent w (boundaryOuterEdge w h k)) ∧
      (k ≤ -1 → ¬ EdgePresent w (boundaryOuterEdge w h k)) := by
  by_cases hkneg : k ≤ -1
  · rw [boundaryOuterEdge_of_negative w h hkneg]
    have hpersist := boundary_left_edge_persistent w h hkneg
    have hbound : kmswLLCreatedEdge w (boundaryHitTime w h k) <
        (kmswStage w (boundaryHitTime w h k)).nextEdge := hpersist.1
    have hstage := (boundaryVertex_left_missing_edge w h hkneg)
    have hends := edge_endpoints_eq w hbound
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hends.1.symm.trans hstage.1
    · exact hends.2.symm.trans hstage.2.1
    · intro hnonneg
      omega
    · intro _
      exact boundary_left_edge_not_present w h hkneg
  · by_cases hkpos : 1 ≤ k
    · rw [boundaryOuterEdge_of_positive w h hkpos]
      have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
      have hkNat : 1 ≤ k.toNat := by
        have hcast : (1 : ℤ) ≤ (k.toNat : ℤ) := by simpa [hkcast] using hkpos
        exact_mod_cast hcast
      have hp := boundaryVertex_right_edge_present_source w h
        (k := k.toNat) hkNat
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hkcast] using hp.2.1
      · simpa [hkcast] using hp.2.2
      · intro _
        exact hp.1
      · intro hkn
        omega
    · have hkzero : k = 0 := by omega
      subst k
      rw [boundaryOuterEdge_zero]
      have hr := boundaryVertex_root_edge w h
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [edgeWest, kmswStage, kmswInit] using hr.2.1
      · simp [edgeEast, kmswStage, kmswInit, boundaryVertex_one]
      · intro _
        exact ⟨0, by simp [kmswStage, kmswInit], hr.2.2.2⟩
      · intro hkneg'
        omega

/-- Every edge in the hit-indexed sequence occurs in a finite lower-boundary
list: the negative terms lie in LL, the root and positive terms lie in LR -/
theorem boundaryOuterEdge_mem_finite_LL_LR (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    ∃ n, boundaryOuterEdge w h k ∈ (kmswStage w n).LL ∨
      boundaryOuterEdge w h k ∈ (kmswStage w n).LR := by
  by_cases hkneg : k ≤ -1
  · rw [boundaryOuterEdge_of_negative w h hkneg]
    refine ⟨boundaryHitTime w h k, Or.inl ?_⟩
    exact (boundary_left_edge_persistent w h hkneg).2 _ le_rfl |>.1
  · by_cases hkpos : 1 ≤ k
    · have hkNat : 1 ≤ k.toNat := by
        have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
        have hcast : (1 : ℤ) ≤ (k.toNat : ℤ) := by simpa [hkcast] using hkpos
        exact_mod_cast hcast
      obtain ⟨N, hN, hLR⟩ := boundaryVertex_right_edge w h
        (k := (k.toNat : ℤ)) (by exact_mod_cast hkNat)
      have htime := boundaryHitTime_right_boundary_edge w h hkNat
      refine ⟨N, Or.inr ?_⟩
      rw [boundaryOuterEdge_of_positive w h hkpos, ← htime.1]
      exact (hLR N le_rfl).1
    · have hkzero : k = 0 := by omega
      subst k
      rw [boundaryOuterEdge_zero]
      exact ⟨0, Or.inr (by simp [kmswStage, kmswInit])⟩

/-- Every hit-indexed negative LL edge is disjoint from every edge in the
`kmswLeftBoundaryEdge` record sequence: the former is missing, while each
record edge is active and hence present. In particular there is no index
correspondence `i` identifying these two edge sequences under the stated -/
theorem boundaryLLCreatedEdge_ne_kmswLeftBoundaryEdge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) (i : ℕ) :
    kmswLLCreatedEdge w (boundaryHitTime w h k) ≠ kmswLeftBoundaryEdge w i := by
  intro heq
  have hleft : EdgePresent w (kmswLeftBoundaryEdge w i) := by
    let m := natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) i
    refine ⟨m, act_lt_nextEdge w (Nat.le_refl m), ?_⟩
    dsimp [kmswLeftBoundaryEdge, m]
    exact kmswStage_active_present w _
  have hmissing := boundary_left_edge_not_present w h hk
  apply hmissing
  rw [heq]
  exact hleft

/-- The root, present right chain, and missing left chain form exactly the
range of `boundaryOuterEdge`. This is an edge-ID set characterization of
the hit-indexed sequence (`eqn-bdy-vertex-hit`, `eqn-bdy-vertex-kmsw`,
combinatorial lower boundary and does not assert an additional geometric
identification with the paper's outer boundary. -/
@[expose] def boundaryOuterEdgeSet (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : Set ℕ :=
  ({0} : Set ℕ) ∪
    {e | ∃ k : ℤ, 1 ≤ k ∧ e = kmswRightBoundaryEdge w k.toNat} ∪
    {e | ∃ k : ℤ, k ≤ -1 ∧
      e = kmswLLCreatedEdge w (boundaryHitTime w h k)}

/-- The range of the consecutive-edge sequence is exactly the root edge,
present LR chain, and missing LL chain. -/
theorem boundaryOuterEdge_range (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    Set.range (boundaryOuterEdge w h) = boundaryOuterEdgeSet w h := by
  ext e
  constructor
  · rintro ⟨k, rfl⟩
    by_cases hkneg : k ≤ -1
    · apply Or.inr
      exact ⟨k, hkneg, boundaryOuterEdge_of_negative w h hkneg⟩
    · by_cases hkpos : 1 ≤ k
      · apply Or.inl
        right
        exact ⟨k, hkpos, boundaryOuterEdge_of_positive w h hkpos⟩
      · have hkzero : k = 0 := by omega
        subst k
        apply Or.inl
        left
        simp [boundaryOuterEdge_zero]
  · intro he
    rcases he with (he | ⟨k, hkpos, he⟩) | ⟨k, hkneg, he⟩
    · refine ⟨0, ?_⟩
      simpa [boundaryOuterEdge_zero] using he.symm
    · refine ⟨k, ?_⟩
      calc
        boundaryOuterEdge w h k = kmswRightBoundaryEdge w k.toNat :=
          boundaryOuterEdge_of_positive w h hkpos
        _ = e := he.symm
    · refine ⟨k, ?_⟩
      calc
        boundaryOuterEdge w h k = kmswLLCreatedEdge w (boundaryHitTime w h k) :=
          boundaryOuterEdge_of_negative w h hkneg
        _ = e := he.symm

/-- Injectivity and the consecutive-edge characterization together state
that `boundaryVertex` is the hit-indexed west-to-east vertex sequence of the
packaged outer boundary, with `x₀` and `x₁` the west and east endpoints of
`λ₀`. This supports, but does not replace, author ruling F1 for -/
theorem boundaryVertex_westToEast_outerBoundary (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    Function.Injective (boundaryVertex w h) ∧
      (∀ k : ℤ,
        edgeWest w (boundaryOuterEdge w h k) = boundaryVertex w h k ∧
          edgeEast w (boundaryOuterEdge w h k) = boundaryVertex w h (k + 1)) ∧
      boundaryOuterEdge w h 0 = 0 ∧
      boundaryVertex w h 0 = edgeWest w 0 ∧
      boundaryVertex w h 1 = edgeEast w 0 := by
  refine ⟨boundaryVertex_injective w h, ?_, boundaryOuterEdge_zero w h, ?_, ?_⟩
  · intro k
    exact ⟨(boundaryOuterEdge_endpoints w h k).1,
      (boundaryOuterEdge_endpoints w h k).2.1⟩
  · rw [boundaryVertex_zero]
    rfl
  · rw [boundaryVertex_one]
    rfl

end DirectedDistances.KMSW
