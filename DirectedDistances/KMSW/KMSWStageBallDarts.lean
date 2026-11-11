module

public import DirectedDistances.KMSW.KMSWWindowBallCapture
public import DirectedDistances.KMSW.StageRotation

/-! Helper toward prop-disk-bs-conv (Proposition 5.16,
adopting no reading of the missing-edge extension; not a paper result. -/

public section
namespace DirectedDistances.KMSW

/-- The stage darts whose two geometric endpoints lie in the radius ball -/
@[expose] noncomputable def kmswStageBallDarts
    (P : KMSWStageEdgePredicate) (s : State) (r c : ℕ) :
    Finset (StageDart s.nextEdge) := by
  classical
  exact Finset.univ.filter (fun d =>
    stageEndpoint s d ∈ kmswStageBallVertices P s r c ∧
      stageEndpoint s (edgeFlip _ d) ∈ kmswStageBallVertices P s r c)

/-- Membership records exactly that both endpoints lie in the ball -/
theorem kmswStageBallDarts_mem_iff (P : KMSWStageEdgePredicate)
    (s : State) (r c : ℕ) (d : StageDart s.nextEdge) :
    d ∈ kmswStageBallDarts P s r c ↔
      stageEndpoint s d ∈ kmswStageBallVertices P s r c ∧
        stageEndpoint s (edgeFlip _ d) ∈ kmswStageBallVertices P s r c := by
  classical
  simp [kmswStageBallDarts]

/-- Membership is invariant under reversing a retained dart -/
theorem kmswStageBallDarts_edgeFlip (P : KMSWStageEdgePredicate)
    (s : State) (r c : ℕ) (d : StageDart s.nextEdge) :
    d ∈ kmswStageBallDarts P s r c ↔
      edgeFlip _ d ∈ kmswStageBallDarts P s r c := by
  cases d with
  | mk e b => cases b <;>
      simp [kmswStageBallDarts_mem_iff, edgeFlip_apply, stageEndpoint,
        and_comm]

/-- Bounded distance is monotone in its radius -/
theorem kmswStageDistanceLe_mono (P : KMSWStageEdgePredicate) (s : State)
    {r r' x y : ℕ} (hrr : r ≤ r')
    (hxy : kmswStageDistanceLe P s r x y) :
    kmswStageDistanceLe P s r' x y := by
  obtain ⟨k, hk, hpath⟩ := hxy
  exact ⟨k, hk.trans hrr, hpath⟩

/-- The vertex balls are monotone in their radius -/
theorem kmswStageBallVertices_mono (P : KMSWStageEdgePredicate)
    (s : State) {r r' c : ℕ} (hrr : r ≤ r') :
    kmswStageBallVertices P s r c ⊆ kmswStageBallVertices P s r' c := by
  classical
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  rw [kmswStageBallVertices, Finset.mem_filter]
  exact ⟨hx'.1, kmswStageDistanceLe_mono P s hrr hx'.2⟩

/-- The center belongs to its ball when it is a stage vertex -/
theorem kmswStageBallVertices_center (P : KMSWStageEdgePredicate)
    (s : State) (r c : ℕ) (hc : c < s.nextVertex) :
    c ∈ kmswStageBallVertices P s r c := by
  classical
  rw [kmswStageBallVertices, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr hc, ?_⟩
  exact ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩

/-- The retained dart set is monotone in its radius -/
theorem kmswStageBallDarts_mono (P : KMSWStageEdgePredicate)
    (s : State) {r r' c : ℕ} (hrr : r ≤ r') :
    kmswStageBallDarts P s r c ⊆ kmswStageBallDarts P s r' c := by
  have hvertices := kmswStageBallVertices_mono P s
    (r := r) (r' := r') (c := c) hrr
  intro d hd
  rw [kmswStageBallDarts_mem_iff] at hd ⊢
  exact ⟨hvertices hd.1, hvertices hd.2⟩

/-- The subtype of darts retained in the stage ball -/
abbrev KMSWStageBallDart (P : KMSWStageEdgePredicate)
    (s : State) (r c : ℕ) :=
  {d : StageDart s.nextEdge // d ∈ kmswStageBallDarts P s r c}

/-- The finite dart subtype has decidable equality. -/
noncomputable instance instDecidableEqKMSWStageBallDart
    (P : KMSWStageEdgePredicate) (s : State) (r c : ℕ) :
    DecidableEq (KMSWStageBallDart P s r c) := by
  classical
  exact Classical.decEq _

/-- The finite dart subtype has a finite enumeration. -/
noncomputable instance instFintypeKMSWStageBallDart
    (P : KMSWStageEdgePredicate) (s : State) (r c : ℕ) :
    Fintype (KMSWStageBallDart P s r c) := by
  classical
  exact Fintype.subtype (kmswStageBallDarts P s r c) (fun _ => Iff.rfl)

/-- The edge flip restricts to a permutation of retained ball darts -/
@[expose] def kmswStageBallDartFlip (P : KMSWStageEdgePredicate)
    (s : State) (r c : ℕ) :
    Equiv.Perm (KMSWStageBallDart P s r c) :=
  (edgeFlip s.nextEdge).subtypePerm
    (fun d => (kmswStageBallDarts_edgeFlip P s r c d).symm)

end DirectedDistances.KMSW
