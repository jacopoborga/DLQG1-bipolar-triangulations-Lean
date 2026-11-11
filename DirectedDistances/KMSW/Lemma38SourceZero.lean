module

public import DirectedDistances.KMSW.M0CutSeam
public import DirectedDistances.KMSW.M0CutPresence
public import DirectedDistances.KMSW.RunBoundaryStackSets
public import DirectedDistances.KMSW.RunInfDartPartition
public import DirectedDistances.KMSW.BoundaryLabelling
public import DirectedDistances.KMSW.WholePlaneRightBoundaryRot

public section
namespace DirectedDistances.KMSW

open Filter
open scoped Classical

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
membership at infinitely many stages. -/
@[expose] def kmswRunBoundaryEdges (w : ℕ → Fin 3) : Set ℕ :=
  {e | (∃ᶠ j in Filter.atTop, e ∈ (kmswStage w j).UL) ∨
    (∃ᶠ j in Filter.atTop, e ∈ (kmswStage w j).LL) ∨
    (∃ᶠ j in Filter.atTop, e ∈ (kmswStage w j).LR) ∨
    (∃ᶠ j in Filter.atTop, e ∈ (kmswStage w j).UR)}

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
frequently remains in every later lower-left stack. -/
private theorem kmswRun_LL_mem_mono_source (w : ℕ → Fin 3)
    {m n e : ℕ} (hmn : m ≤ n) (he : e ∈ (kmswStage w m).LL) :
    e ∈ (kmswStage w n).LL := by
  induction n, hmn using Nat.le_induction with
  | base => exact he
  | succ n _ ih =>
    change e ∈ (kmswStep (kmswStage w n) (w n)).LL
    unfold kmswStep
    cases kmswCodeStep (w n) with
    | down =>
      cases hs : (kmswStage w n).UR <;>
        simpa [kmswStepOfStep, hs, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w n).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil =>
        simpa only [kmswStepOfStep, hs, State.addEdge, List.mem_cons] using
          (Or.inr ih)

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
frequently remains in every later lower-right stack. -/
private theorem kmswRun_LR_mem_mono_source (w : ℕ → Fin 3)
    {m n e : ℕ} (hmn : m ≤ n) (he : e ∈ (kmswStage w m).LR) :
    e ∈ (kmswStage w n).LR := by
  induction n, hmn using Nat.le_induction with
  | base => exact he
  | succ n _ ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w n
    rw [ht]
    exact List.mem_append_left _ ih

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
frequent membership is equivalent to eventual membership. -/
private theorem kmswRun_frequently_iff_eventually_source
    (P : ℕ → Prop) (hmono : ∀ {m n}, m ≤ n → P m → P n) :
    (∃ᶠ n in Filter.atTop, P n) ↔ ∃ N, ∀ n ≥ N, P n := by
  constructor
  · intro hf
    obtain ⟨n, _, hn⟩ := (Filter.frequently_atTop.mp hf) 0
    exact ⟨n, fun m hm => hmono hm hn⟩
  · rintro ⟨N, hN⟩
    apply Filter.frequently_atTop.mpr
    intro a
    exact ⟨max a N, le_max_left _ _, hN _ (le_max_right _ _)⟩

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
upper-left edge eventually out of that stack. -/
private theorem kmswRun_left_unbounded_source (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ n, L w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
  exact ⟨n, hn.le.trans (min_le_left _ _)⟩

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
upper-right edge eventually out of that stack. -/
private theorem kmswRun_right_unbounded_source (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
  refine ⟨n, ?_⟩
  have hm := le_max_left (-a) 1
  omega

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
boundary equals the two persistent lower-stack sets. -/
theorem kmswRunBoundaryEdges_eq_eventuallyStacks (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    kmswRunBoundaryEdges w =
      {e | ∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LL} ∪
      {e | ∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LR} := by
  have hL := kmswRun_left_unbounded_source w h
  have hR := kmswRun_right_unbounded_source w h
  ext e
  constructor
  · intro he
    rcases he with hUL | hLL | hLR | hUR
    · obtain ⟨N, hN⟩ := kmswRun_UL_eventually_absent w hL e
      have ⟨n, hn, he⟩ := (Filter.frequently_atTop.mp hUL) N
      exact (hN n hn he).elim
    · exact Or.inl ((kmswRun_frequently_iff_eventually_source _
        (fun hm he => kmswRun_LL_mem_mono_source w hm he)).mp hLL)
    · exact Or.inr ((kmswRun_frequently_iff_eventually_source _
        (fun hm he => kmswRun_LR_mem_mono_source w hm he)).mp hLR)
    · obtain ⟨N, hN⟩ := kmswRun_UR_eventually_absent w hR e
      have ⟨n, hn, he⟩ := (Filter.frequently_atTop.mp hUR) N
      exact (hN n hn he).elim
  · rintro (hLL | hLR)
    · exact Or.inr (Or.inl ((kmswRun_frequently_iff_eventually_source _
        (fun hm he => kmswRun_LL_mem_mono_source w hm he)).mpr hLL))
    · exact Or.inr (Or.inr (Or.inl ((kmswRun_frequently_iff_eventually_source _
        (fun hm he => kmswRun_LR_mem_mono_source w hm he)).mpr hLR)))

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
are exactly the source's root/right/left boundary edge set. -/
theorem kmswRunBoundaryEdges_eq_boundaryOuterEdgeSet (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    kmswRunBoundaryEdges w = boundaryOuterEdgeSet w h := by
  rw [kmswRunBoundaryEdges_eq_eventuallyStacks w h,
    kmswRunEventuallyLL_eq_range w h, kmswRunEventuallyLR_eq_range w h]
  have hrange :
      Set.range (boundaryOuterEdge w h) =
        Set.range (fun j : ℕ => kmswRightBoundaryEdge w j) ∪
          Set.range (fun j : ℕ => kmswLLCreatedEdge w
            (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
    ext e
    constructor
    · rintro ⟨k, rfl⟩
      by_cases hkneg : k ≤ -1
      · right
        let j : ℕ := (-k - 1).toNat
        have hj : (j : ℤ) = -k - 1 := by
          dsimp [j]
          exact Int.toNat_of_nonneg (by omega)
        have hindex : -((j : ℤ) + 1) = k := by omega
        refine ⟨j, ?_⟩
        change kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1))) = _
        rw [boundaryOuterEdge_of_negative w h hkneg, hindex]
      · have hkpos : 0 ≤ k := by omega
        left
        let j : ℕ := k.toNat
        refine ⟨j, ?_⟩
        by_cases hkzero : k = 0
        · simp [j, hkzero, boundaryOuterEdge_zero,
            kmswRightBoundaryEdge_zero]
        · have hkpos' : 1 ≤ k := by omega
          rw [boundaryOuterEdge_of_positive w h hkpos']
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · cases j with
        | zero =>
          refine ⟨0, ?_⟩
          change boundaryOuterEdge w h 0 = kmswRightBoundaryEdge w 0
          rw [boundaryOuterEdge_zero, kmswRightBoundaryEdge_zero]
        | succ j =>
          refine ⟨(j : ℤ) + 1, ?_⟩
          rw [boundaryOuterEdge_of_positive w h (by omega)]
          simp
      · refine ⟨-((j : ℤ) + 1), ?_⟩
        rw [boundaryOuterEdge_of_negative w h (by omega)]
  rw [← boundaryOuterEdge_range w h]
  rw [Set.union_comm]
  exact hrange.symm

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
is the root and the two extremal paths in the whole-plane map, and both paths
exist using the formal inputs `H` (`WholePlaneRotationHypothesis`), `h`
(`BoundaryHitWitnesses` for the run-zero code), and `hLL` (ambient presence of
the run-zero LL record edges, discharged almost surely elsewhere). This covers
start zero only; transfer to other integer starts and clauses C3/C4 are separate. -/
theorem kmswRunBoundaryEdges_sourceZero_seam (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    wholePlaneEdgeι W 0 '' kmswRunBoundaryEdges (shiftedStream W 0) =
        {e | m0CutSeamEdge W H e} ∧
      (∃ P : WholePlaneRightmostRay W H,
        P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)) ∧
      (∃ _P : M0CutLeftmostChain W H
          (wholePlaneEdgeWest W (m0CutLambdaZero W)), True) := by
  constructor
  · rw [kmswRunBoundaryEdges_eq_boundaryOuterEdgeSet (shiftedStream W 0) h]
    ext e
    exact (m0Cut_seamEdge_iff W H h hLL e).symm
  constructor
  · obtain ⟨P, hP, _⟩ := wholePlaneRightmostRay_exists_root_terminal W H 0 h
    exact ⟨P, by
      have hr := (m0Cut_lambdaZero_endpoints W h).2
      rw [boundaryVertex_one] at hr
      exact hP.trans hr.symm⟩
  · obtain ⟨_P, _⟩ := m0Cut_betaL_exists W H h hLL
    exact ⟨_P, trivial⟩

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper
path use present run edges, while the leftmost path uses missing run edges
that remain present as whole-plane geometric edges; the two path ranges are
the eventual lower-right and lower-left boundaries. -/
theorem kmswRunBoundaryEdges_sourceZero_status (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W))
    (Q : M0CutLeftmostChain W H
      (wholePlaneEdgeWest W (m0CutLambdaZero W))) :
    EdgePresent (shiftedStream W 0) 0 ∧
    (∀ j, EdgePresent (shiftedStream W 0)
      (kmswRightBoundaryEdge (shiftedStream W 0) (j + 1))) ∧
    (∀ j, P.edge j = wholePlaneEdgeι W 0
      (kmswRightBoundaryEdge (shiftedStream W 0) (j + 1))) ∧
    wholePlaneEdgeι W 0 ''
      {e | ∃ N, ∀ n ≥ N, e ∈ (kmswStage (shiftedStream W 0) n).LR} =
      {m0CutLambdaZero W} ∪ Set.range P.edge ∧
    (∀ j : ℕ, ¬ EdgePresent (shiftedStream W 0)
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (-((j : ℤ) + 1))))) ∧
    (∀ j : ℕ, wholePlaneEdgePresent W (Q.edge j)) ∧
    (∀ j : ℕ, Q.edge j = wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (-((j : ℤ) + 1))))) ∧
    wholePlaneEdgeι W 0 ''
      {e | ∃ N, ∀ n ≥ N, e ∈ (kmswStage (shiftedStream W 0) n).LL} =
      Set.range Q.edge := by
  let w := shiftedStream W 0
  have hrightPresent (j : ℕ) : EdgePresent w
      (kmswRightBoundaryEdge w (j + 1)) :=
    (boundaryVertex_right_edge_present_source w h (by omega)).1
  have hrootPresent : EdgePresent w 0 := by
    obtain ⟨_, _, _, hp⟩ := boundaryVertex_root_edge w h
    exact ⟨0, by simp [kmswStage, kmswInit], hp⟩
  have hrightPath (j : ℕ) : P.edge j = wholePlaneEdgeι W 0
      (kmswRightBoundaryEdge w (j + 1)) :=
    m0Cut_betaR_edges W H h P hP j
  have hrightRange : Set.range (fun i : ℕ => kmswRightBoundaryEdge w i) =
      {0} ∪ Set.range (fun j : ℕ => kmswRightBoundaryEdge w (j + 1)) := by
    ext e
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | zero => exact Or.inl (by rw [kmswRightBoundaryEdge_zero] at hi; exact hi.symm)
      | succ j => exact Or.inr ⟨j, hi⟩
    · rintro (he | ⟨j, he⟩)
      · refine ⟨0, ?_⟩
        rw [kmswRightBoundaryEdge_zero]
        exact he.symm
      · exact ⟨j + 1, he⟩
  have himageRange (f : ℕ → ℕ) :
      wholePlaneEdgeι W 0 '' Set.range f =
        Set.range (fun j => wholePlaneEdgeι W 0 (f j)) := by
    ext e
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨a, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨f j, ⟨j, rfl⟩, rfl⟩
  have hrightImage : wholePlaneEdgeι W 0 '' Set.range
      (fun i : ℕ => kmswRightBoundaryEdge w i) =
      {m0CutLambdaZero W} ∪ Set.range P.edge := by
    rw [hrightRange, Set.image_union, himageRange]
    simp only [Set.image_singleton, m0CutLambdaZero]
    have hpathFun : (fun j => wholePlaneEdgeι W 0
        (kmswRightBoundaryEdge w (j + 1))) = P.edge := by
      funext j
      exact (hrightPath j).symm
    rw [hpathFun]
  have hleftPath (j : ℕ) : Q.edge j = wholePlaneEdgeι W 0
      (kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
    have hp := m0Cut_betaL_edges W H h hLL Q j
    have hindex : -(j : ℤ) - 1 = -((j : ℤ) + 1) := by omega
    rw [hindex] at hp
    exact hp
  have hleftImage : wholePlaneEdgeι W 0 '' Set.range
      (fun j : ℕ => kmswLLCreatedEdge w
        (boundaryHitTime w h (-((j : ℤ) + 1)))) = Set.range Q.edge := by
    ext e
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨a, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, hleftPath j⟩
    · rintro ⟨j, rfl⟩
      exact ⟨kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1))),
        ⟨j, rfl⟩, (hleftPath j).symm⟩
  have heventLL : wholePlaneEdgeι W 0 ''
      {e | ∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LL} = Set.range Q.edge := by
    rw [kmswRunEventuallyLL_eq_range w h]
    exact hleftImage
  have heventLR : wholePlaneEdgeι W 0 ''
      {e | ∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LR} =
        {m0CutLambdaZero W} ∪ Set.range P.edge := by
    rw [kmswRunEventuallyLR_eq_range w h]
    exact hrightImage
  have hleftNotPresent (j : ℕ) : ¬ EdgePresent w
      (kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
    exact boundary_left_edge_not_present w h (by omega)
  have hleftAmbient (j : ℕ) : wholePlaneEdgePresent W (Q.edge j) := by
    rw [hleftPath j]
    have hp := hLL (-(j : ℤ)) (by omega)
    have hindex : -(j : ℤ) - 1 = -((j : ℤ) + 1) := by omega
    rw [hindex] at hp
    exact hp
  exact ⟨hrootPresent, hrightPresent, hrightPath, heventLR, hleftNotPresent,
    hleftAmbient, hleftPath, heventLL⟩

end DirectedDistances.KMSW
