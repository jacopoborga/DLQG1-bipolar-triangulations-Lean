module

public import DirectedDistances.KMSW.M0CutData
public import DirectedDistances.KMSW.M0CutLeftEdgesPackaged
public import DirectedDistances.KMSW.M0CutEdgeStatus
public import DirectedDistances.KMSW.BusemannBoundaryM0

public section
namespace DirectedDistances.KMSW

section Identification
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

local notation "w" => shiftedStream W 0
local notation "V" => wholePlaneVertexι W 0
local notation "E" => wholePlaneEdgeι W 0
local notation "D" => m0CutData W H h hLL

include W H h hLL

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
The run-zero vertex inclusion is injective and has exactly the cut vertex range. -/
theorem m0Cut_identification_vertices :
    Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) := by
  exact ⟨wholePlaneVertexι_injective W 0,
    (m0Cut_leftVertices_eq_runZero W H h (m0CutSeamEdge W H)
      (m0Cut_seamEdge_iff W H h hLL)).symm⟩

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
The run-zero edge inclusion is injective and has exactly the geometric cut edge range. -/
theorem m0Cut_identification_edges :
    Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) := by
  exact ⟨wholePlaneEdgeι_injective W 0,
    (m0Cut_leftEdges_seam_eq_runZero W H h hLL).symm⟩

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
The cut labels are the transported west-to-east run-zero boundary labels. -/
theorem m0Cut_identification_labels (k : ℤ) :
    (D).x k = V (boundaryVertex w h k) :=
  (D).x_eq h hLL k

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
The root dart, root edge, ordered endpoints, ambient presence and cut tail agree. -/
theorem m0Cut_identification_root :
    (D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
      (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
      wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
      wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
      wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart := by
  have hr := (D).root_eq h hLL
  exact ⟨hr.1, rfl, rfl, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2⟩

omit hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
Present cut edges inherit ambient presence with exactly the negative boundary exception. -/
theorem m0Cut_identification_status (e : ℕ) :
    EdgePresent w e ↔
      (wholePlaneEdgePresent W (E e) ∧
        ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) :=
  m0Cut_edgeStatus W H h e

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
The cut's missing tag singles out precisely the negative boundary edges. -/
theorem m0Cut_identification_missing (e : ℕ) :
    (D).missing (E e) ↔ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k := by
  rw [(D).missing_eq h hLL]
  constructor
  · exact m0Cut_nonpresent_implies_negative_boundaryOuterEdge W h e
  · rintro ⟨k, hk, rfl⟩
    exact (boundaryOuterEdge_endpoints w h k).2.2.2 hk

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
The cut directed steps are exactly the transported present run-zero edges. -/
theorem m0Cut_identification_directedStep (a b : ℕ) :
    m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
      ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b :=
  m0Cut_directedStep_iff_present W H h hLL (m0CutSeamEdge W H)
    (m0Cut_seamEdge_iff W H h hLL) (V a) (V b)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
Shortest distances agree on all transported vertices, including unreachable pairs. -/
theorem m0Cut_identification_sdp (a b : ℕ) :
    (D).sdp (V a) (V b) = DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩ :=
  (D).sdp_eq h hLL a b

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
Longest distances agree with both extended-value conventions preserved. -/
theorem m0Cut_identification_ldp (a b : ℕ) :
    (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩ :=
  (D).ldp_eq h hLL a b

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
Shortest distances agree for every ordered pair of boundary labels. -/
theorem m0Cut_identification_boundary_sdp (k k' : ℤ) :
    (D).sdp ((D).x k) ((D).x k') =
      DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k') := by
  rw [(D).x_eq h hLL k, (D).x_eq h hLL k']
  exact (D).sdp_eq h hLL (boundaryVertex w h k) (boundaryVertex w h k')

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
Longest distances agree for every ordered pair of boundary labels. -/
theorem m0Cut_identification_boundary_ldp (k k' : ℤ) :
    (D).ldp ((D).x k) ((D).x k') =
      presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k') := by
  rw [(D).x_eq h hLL k, (D).x_eq h hLL k']
  exact (D).ldp_eq h hLL (boundaryVertex w h k) (boundaryVertex w h k')

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: packaged rooted directed-map identification); not a paper result.
Pathwise rooted directed-carrier identification, including labels and all distances.
The identification of the inherited plane drawing and its faces is separate. -/
theorem m0Cut_identification :
    Function.Injective V ∧
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
      presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) := by
  obtain ⟨hV, hvertices⟩ := m0Cut_identification_vertices W H h hLL
  obtain ⟨hE, hedges⟩ := m0Cut_identification_edges W H h hLL
  exact ⟨hV, hvertices, hE, hedges, m0Cut_identification_labels W H h hLL,
    m0Cut_identification_root W H h hLL, m0Cut_identification_status W H h,
    m0Cut_identification_missing W H h hLL, m0Cut_identification_directedStep W H h hLL,
    m0Cut_identification_sdp W H h hLL, m0Cut_identification_ldp W H h hLL,
    m0Cut_identification_boundary_sdp W H h hLL,
    m0Cut_identification_boundary_ldp W H h hLL⟩

end Identification
end DirectedDistances.KMSW
