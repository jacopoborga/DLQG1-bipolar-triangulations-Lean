module

public import DirectedDistances.KMSW.M0CutIdentificationPackaged
public import DirectedDistances.KMSW.M0CutBusemann

/-! Helper toward Lemma 5.3 (lem-infty-cut on the identified future map
M_{0,infinity}: path transport); not a paper result. Source: -/

public section
namespace DirectedDistances.KMSW

section PathTransport

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

local notation "w" => shiftedStream W 0
local notation "V" => wholePlaneVertexι W 0
local notation "D" => m0CutData W H h hLL

include W H h hLL

/-- Helper toward Lemma 5.3 (lem-infty-cut on the identified future map
M_{0,infinity}: path transport); not a paper result. Source:
The target of a cut step from a run-zero vertex is a run-zero vertex. -/
theorem m0Cut_step_source_target_vertex (a : ℕ)
    {v : WholePlaneVertex W}
    (hs : m0CutDirectedStep W H (D).seam (V a) v) :
    ∃ b, v = V b := by
  have hreach : m0CutReachable W H (D).seam (V a) v := by
    refine ⟨1, ?_⟩
    exact ⟨V a, rfl, hs⟩
  have hS : ∀ e, (D).seam e ↔
      e ∈ wholePlaneEdgeι W 0 ''
        boundaryOuterEdgeSet (shiftedStream W 0) h := by
    intro e
    exact m0Cut_seamEdge_iff W H h hLL e
  obtain ⟨b, hb⟩ :=
    m0Cut_reachable_target_is_vertex W H h hLL (D).seam hS hreach
  exact ⟨b, hb.symm⟩

/-- Helper toward Lemma 5.3 (lem-infty-cut on the identified future map
M_{0,infinity}: path transport); not a paper result. Source:
A finite cut vertex path lifts to a present-edge path with the same vertex list. -/
theorem m0Cut_vertexPath_lift (n : ℕ)
    (p : Fin (n + 1) → WholePlaneVertex W) (a : ℕ)
    (h0 : p 0 = V a)
    (hs : ∀ i : Fin n,
      m0CutDirectedStep W H (D).seam (p i.castSucc) (p i.succ)) :
    ∃ b, p (Fin.last n) = V b ∧
      ∃ q : Quiver.Path (⟨a⟩ : PresentVertex w) ⟨b⟩,
        q.vertices.map (fun z => V z.id) = List.ofFn p := by
  revert p a h0 hs
  induction n with
  | zero =>
    intro p a h0 hs
    refine ⟨a, ?_, Quiver.Path.nil, ?_⟩
    · simpa using h0
    · simp [h0]
  | succ n ih =>
    intro p a h0 hs
    let p' : Fin (n + 1) → WholePlaneVertex W := fun i => p i.castSucc
    have h0' : p' 0 = V a := by
      simpa [p'] using h0
    have hs' : ∀ i : Fin n,
        m0CutDirectedStep W H (D).seam (p' i.castSucc) (p' i.succ) := by
      intro i
      simpa [p'] using hs i.castSucc
    obtain ⟨c, hc, q, hq⟩ := ih p' a h0' hs'
    have hlast : m0CutDirectedStep W H (D).seam
        (V c) (p (Fin.last n).succ) := by
      rw [← hc]
      exact hs (Fin.last n)
    obtain ⟨b, hb⟩ := m0Cut_step_source_target_vertex W H h hLL c hlast
    have hcut : m0CutDirectedStep W H (m0CutSeamEdge W H)
        (V c) (V b) := by
      rw [← hb]
      exact hlast
    obtain ⟨e, he, hwest, heast⟩ :=
      (m0Cut_identification_directedStep W H h hLL c b).mp hcut
    have hwest' : edgeWest (shiftedStream W 0) e = c :=
      wholePlaneVertexι_injective W 0 hwest
    have heast' : edgeEast (shiftedStream W 0) e = b :=
      wholePlaneVertexι_injective W 0 heast
    let f : (⟨c⟩ : PresentVertex w) ⟶ ⟨b⟩ :=
      ⟨e, he, hwest', heast'⟩
    have hend : p (Fin.last (n + 1)) = V b := by
      simpa only [Fin.succ_last] using hb
    refine ⟨b, hend, q.cons f, ?_⟩
    rw [Quiver.Path.vertices_cons, List.map_concat, hq, ← hend,
      List.ofFn_succ' p]

end PathTransport
end DirectedDistances.KMSW
