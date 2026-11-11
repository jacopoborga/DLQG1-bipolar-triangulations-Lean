module

public import DirectedDistances.KMSW.M0CutPathTransport

/-! Helper toward Lemma 5.3 (lem-infty-cut on the identified future map
M_{0,infty}: path transport); not a paper result. Source: -/

public section
namespace DirectedDistances.KMSW

section PathVisit

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
M_{0,infty}: path transport); not a paper result. Source:
Every present-edge path gives a cut vertex path with the same vertex list. -/
private theorem m0Cut_vertexPath_of_present
    {u v : PresentVertex w} (q : Quiver.Path u v) :
    ∃ n, ∃ p : Fin (n + 1) → WholePlaneVertex W,
      p 0 = V u.id ∧ p (Fin.last n) = V v.id ∧
      (∀ i : Fin n,
        m0CutDirectedStep W H (D).seam (p i.castSucc) (p i.succ)) ∧
      List.ofFn p = q.vertices.map (fun z => V z.id) := by
  induction q with
  | nil =>
    refine ⟨0, fun _ => V u.id, by simp, by simp, ?_, by simp⟩
    intro i
    exact Fin.elim0 i
  | @cons c b q e ih =>
    obtain ⟨n, p, hp0, hpend, hsteps, hvertices⟩ := ih
    have hstep : m0CutDirectedStep W H (D).seam (V c.id) (V b.id) :=
      (m0Cut_identification_directedStep W H h hLL c.id b.id).2
        ⟨e.1, e.2.1, congrArg V e.2.2.1, congrArg V e.2.2.2⟩
    refine ⟨n + 1, Fin.snoc p (V b.id), ?_, ?_, ?_, ?_⟩
    · simpa using hp0
    · simp
    · intro i
      cases i using Fin.lastCases with
      | cast j =>
        simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using hsteps j
      | last =>
        simpa [hpend] using hstep
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hvertices, Quiver.Path.vertices_cons]
      simp only [List.map_concat]

/-- Helper toward Lemma 5.3 (lem-infty-cut on the identified future map
M_{0,infty}: path transport); not a paper result. Source:
The carrier-indexed statement is the specialization to run-zero vertices. -/
theorem m0Cut_vertexPath_of_carrier {a b : ℕ}
    (q : Quiver.Path (⟨a⟩ : PresentVertex w) ⟨b⟩) :
    ∃ n, ∃ p : Fin (n + 1) → WholePlaneVertex W,
      p 0 = V a ∧ p (Fin.last n) = V b ∧
      (∀ i : Fin n,
        m0CutDirectedStep W H (D).seam (p i.castSucc) (p i.succ)) ∧
      List.ofFn p = q.vertices.map (fun z => V z.id) := by
  obtain ⟨n, p, hp0, hpend, hsteps, hvertices⟩ :=
    m0Cut_vertexPath_of_present W H h hLL q
  exact ⟨n, p, hp0, hpend, hsteps, hvertices⟩

/-- Helper toward Lemma 5.3 (lem-infty-cut on the identified future map
M_{0,infty}: path transport); not a paper result. Source:
Finite cut vertex paths visit a run-zero vertex exactly when present paths do. -/
theorem m0Cut_visit_iff (a b c : ℕ) :
    (∀ n (p : Fin (n + 1) → WholePlaneVertex W),
      p 0 = V a → p (Fin.last n) = V b →
      (∀ i : Fin n,
        m0CutDirectedStep W H (D).seam (p i.castSucc) (p i.succ)) →
      ∃ i, p i = V c) ↔
    (∀ q : Quiver.Path (⟨a⟩ : PresentVertex w) ⟨b⟩,
      (⟨c⟩ : PresentVertex w) ∈ q.vertices) := by
  constructor
  · intro hvisit q
    obtain ⟨n, p, hp0, hpend, hsteps, hvertices⟩ :=
      m0Cut_vertexPath_of_carrier W H h hLL q
    obtain ⟨i, hi⟩ := hvisit n p hp0 hpend hsteps
    have hmem : V c ∈ List.ofFn p := by
      exact List.mem_ofFn.mpr ⟨i, hi⟩
    rw [hvertices] at hmem
    obtain ⟨z, hz, hzc⟩ := List.mem_map.mp hmem
    have hzid : z.id = c := wholePlaneVertexι_injective W 0 hzc
    have hzvertex : z = (⟨c⟩ : PresentVertex w) := by
      cases z with
      | mk id => cases hzid; rfl
    rw [← hzvertex]
    exact hz
  · intro hvisit n p hp0 hpend hsteps
    obtain ⟨b', hb', q, hvertices⟩ :=
      m0Cut_vertexPath_lift W H h hLL n p a hp0 hsteps
    have hb : b' = b := wholePlaneVertexι_injective W 0 (hb'.symm.trans hpend)
    subst b'
    have hmem : V c ∈ q.vertices.map (fun z => V z.id) := by
      exact List.mem_map.mpr ⟨⟨c⟩, hvisit q, rfl⟩
    rw [hvertices] at hmem
    simpa only [List.mem_ofFn] using hmem

end PathVisit
end DirectedDistances.KMSW
