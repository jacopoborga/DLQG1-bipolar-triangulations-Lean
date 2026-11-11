module

public import DirectedDistances.KMSW.M0CutData
public import DirectedDistances.KMSW.M0CutBusemann

/-! Helper toward Theorem 1.4 (thm-busemann F1: west-to-east boundary labels of
M_{0,infinity}; finite distances for reachable pairs); not a paper result.

The source root and extremal-path labels enumerate exactly the seam vertices.
Consecutive labels are the west and east endpoints of the corresponding geometric
seam edge, including the missing negative boundary edges. Reachability uses the
present directed cut edges, and both extended distances are finite on reachable pairs. -/

public section
namespace DirectedDistances.KMSW

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

local notation "D" => m0CutData W H h hLL

/-- Helper toward Theorem 1.4 (thm-busemann F1: west-to-east boundary labels of
M_{0,infinity}; finite distances for reachable pairs); not a paper result.
The root and extremal-path boundary labels are injective, using their proved
agreement with the hit-indexed labels and the injective whole-plane inclusion. -/
theorem m0CutData_x_injective : Function.Injective (D).x := by
  intro k l hkl
  apply boundaryVertex_injective (shiftedStream W 0) h
  apply wholePlaneVertexι_injective W 0
  rw [← (D).x_eq h hLL k, ← (D).x_eq h hLL l]
  exact hkl

/-- Helper toward Theorem 1.4 (thm-busemann F1: west-to-east boundary labels of
M_{0,infinity}; finite distances for reachable pairs); not a paper result.
Each geometric boundary edge lies on the source seam and has its consecutive
labels as west and east endpoints. Missing edges retain these geometric endpoints. -/
theorem m0CutData_x_order (k : ℤ) :
    m0CutSeamEdge W H
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
      wholePlaneEdgeWest W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = (D).x k ∧
      wholePlaneEdgeEast W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
        (D).x (k + 1) := by
  have hb := boundaryOuterEdge_endpoints (shiftedStream W 0) h k
  refine ⟨(m0Cut_seamEdge_iff W H h hLL _).mpr ?_, ?_, ?_⟩
  · apply Set.mem_image_of_mem
    rw [← boundaryOuterEdge_range (shiftedStream W 0) h]
    exact Set.mem_range_self k
  · rw [wholePlaneEdgeWest_ι, hb.1, (D).x_eq h hLL k]
  · rw [wholePlaneEdgeEast_ι, hb.2.1, (D).x_eq h hLL (k + 1)]

/-- Helper toward Theorem 1.4 (thm-busemann F1: west-to-east boundary labels of
M_{0,infinity}; finite distances for reachable pairs); not a paper result.
The label range is exactly the endpoint set of the independently defined source
seam, namely the root together with the rightmost and leftmost extremal paths. -/
theorem m0CutData_x_range :
    Set.range (D).x = {v | ∃ e, m0CutSeamEdge W H e ∧
      (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} := by
  ext v
  constructor
  · rintro ⟨k, rfl⟩
    have ho := m0CutData_x_order W H h hLL k
    exact ⟨_, ho.1, Or.inl ho.2.1⟩
  · rintro ⟨e, he, hv⟩
    obtain ⟨a, ha, hae⟩ := (m0Cut_seamEdge_iff W H h hLL e).mp he
    rw [← boundaryOuterEdge_range (shiftedStream W 0) h] at ha
    obtain ⟨k, rfl⟩ := ha
    have ho := m0CutData_x_order W H h hLL k
    rw [← hae] at hv
    rcases hv with hw | ht
    · exact ⟨k, ho.2.1.symm.trans hw⟩
    · exact ⟨k + 1, ho.2.2.symm.trans ht⟩

/-- Helper toward Theorem 1.4 (thm-busemann F1: west-to-east boundary labels of
M_{0,infinity}; finite distances for reachable pairs); not a paper result.
The index-zero boundary edge is the root, with endpoints labelled zero and one. -/
theorem m0CutData_x_root :
    wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
        m0CutLambdaZero W ∧
      m0CutSeamEdge W H (m0CutLambdaZero W) ∧
      wholePlaneEdgeWest W (m0CutLambdaZero W) = (D).x 0 ∧
      wholePlaneEdgeEast W (m0CutLambdaZero W) = (D).x 1 := by
  have hroot : wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
      m0CutLambdaZero W := by
    rw [boundaryOuterEdge_zero]
    rfl
  have ho := m0CutData_x_order W H h hLL 0
  rw [hroot] at ho
  exact ⟨hroot, ho⟩

/-- Helper toward Theorem 1.4 (thm-busemann F1: west-to-east boundary labels of
M_{0,infinity}; finite distances for reachable pairs); not a paper result.
Cut reachability supplies a finite path length bounding SDP, so the provider's
natural-value conversion is never applied to top on a reachable pair. -/
theorem m0CutData_sdp_ne_top_of_reachable (a b : WholePlaneVertex W)
    (hr : m0CutReachable W H (D).seam a b) : (D).sdp a b ≠ ⊤ := by
  obtain ⟨n, hn⟩ := hr
  have hle : (D).sdp a b ≤ (n : ℕ∞) :=
    iInf_le_of_le n (iInf_le _ hn)
  exact ne_of_lt (lt_of_le_of_lt hle (ENat.natCast_lt_top n))

/-- Helper toward Theorem 1.4 (thm-busemann F1: west-to-east boundary labels of
M_{0,infinity}; finite distances for reachable pairs); not a paper result.
On every reachable pair, LDP is an actual finite natural value. Local finiteness
from the standing rotation hypothesis supplies the bounded-path-length theorem. -/
theorem m0CutData_ldp_eq_finite_of_reachable (a b : WholePlaneVertex W)
    (hr : m0CutReachable W H (D).seam a b) :
    ∃ n : ℕ, (D).ldp a b = ((n : ℕ∞) : WithBot ℕ∞) := by
  classical
  by_cases ha : a ∈ Set.range (wholePlaneVertexι W 0)
  · obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := m0Cut_reachable_target_is_vertex W H h hLL (D).seam
      (m0Cut_seamEdge_iff W H h hLL) hr
    have hp := (m0Cut_reachable_iff_present W H h hLL (D).seam
      (m0Cut_seamEdge_iff W H h hLL) u v).mp hr
    refine ⟨presentLdpFiniteNat
      (presentPathLengthsBounded_of_hfin (shiftedStream W 0) (H.1 0)) hp, ?_⟩
    exact m0Cut_ldp_eq_finiteNat W H h hLL (D).seam
      (m0Cut_seamEdge_iff W H h hLL)
      (presentPathLengthsBounded_of_hfin (shiftedStream W 0) (H.1 0)) u v hr
  · have hzero : ∀ n v, m0CutReachableLength (m0CutDirectedStep W H (D).seam)
        n a v → n = 0 := by
      intro n
      induction n with
      | zero => intro v _; rfl
      | succ n ih =>
        rintro v ⟨c, hac, hcv⟩
        have hn := ih c hac
        subst n
        have hac' : a = c := hac
        obtain ⟨e, _, he, _⟩ :=
          (m0Cut_directedStep_iff_present W H h hLL (D).seam
            (m0Cut_seamEdge_iff W H h hLL) c v).mp hcv
        exact (ha ⟨edgeWest (shiftedStream W 0) e, he.trans hac'.symm⟩).elim
    refine ⟨0, le_antisymm ?_ ?_⟩
    · apply iSup_le
      intro n
      apply iSup_le
      intro hn
      have hn0 := hzero n b hn
      subst n
      exact le_rfl
    · obtain ⟨n, hn⟩ := hr
      have hn0 := hzero n b hn
      subst n
      exact le_iSup_of_le 0 (le_iSup_of_le hn le_rfl)

end DirectedDistances.KMSW
