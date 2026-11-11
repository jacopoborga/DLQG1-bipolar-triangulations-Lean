module

public import DirectedDistances.KMSW.WholePlaneLemma38AllStarts
import DirectedDistances.KMSW.RunBoundaryOuterFace

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk



@[expose] def lemma38StartStream (W : ℤ → Fin 3) (n : ℤ) : ℕ → Fin 3 :=
  fun i => W ((i : ℤ) + n)



@[expose] def lemma38StartEdgeι (W : ℤ → Fin 3) (n : ℤ) (e : ℕ) :
    WholePlaneEdge W :=
  if n ≤ 0 then
    wholePlaneEdgeι W n.natAbs e
  else
    wholePlaneEdgeι W 0
      (kmswWindowEdgeMapInf (shiftedStream W 0) n.toNat e)



@[expose] def lemma38StartVertexι (W : ℤ → Fin 3) (n : ℤ) (v : ℕ) :
    WholePlaneVertex W :=
  if n ≤ 0 then
    wholePlaneVertexι W n.natAbs v
  else
    wholePlaneVertexι W 0
      (kmswWindowVertexMapInf (shiftedStream W 0) n.toNat v)



theorem lemma38StartStream_eq_shifted (W : ℤ → Fin 3) (n : ℤ) (hn : n ≤ 0) :
    lemma38StartStream W n = shiftedStream W n.natAbs := by
  funext i
  simp only [lemma38StartStream, shiftedStream]
  have hnat : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos hn
  rw [hnat, sub_neg_eq_add]



theorem lemma38StartStream_eq_nonnegative (W : ℤ → Fin 3) (n : ℤ)
    (hn : 0 ≤ n) :
    lemma38StartStream W n = fun i : ℕ => W ((i : ℤ) + n.toNat) := by
  funext i
  simp only [lemma38StartStream]
  have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  rw [hnat]

/-- The run embedding at an integer start is injective. -/
theorem lemma38StartEdgeι_injective (W : ℤ → Fin 3) (n : ℤ) :
    Function.Injective (lemma38StartEdgeι W n) := by
  intro e f hef
  by_cases hn : n ≤ 0
  · apply wholePlaneEdgeι_injective W n.natAbs
    simpa [lemma38StartEdgeι, hn] using hef
  · apply (wholePlaneEdgeι_injective W 0).comp
      (kmswWindowEdgeMapInf_injective (shiftedStream W 0) n.toNat)
    simpa [lemma38StartEdgeι, hn] using hef

/-- The run vertex embedding at an integer start is injective. -/
theorem lemma38StartVertexι_injective (W : ℤ → Fin 3) (n : ℤ) :
    Function.Injective (lemma38StartVertexι W n) := by
  intro v z hvz
  by_cases hn : n ≤ 0
  · apply wholePlaneVertexι_injective W n.natAbs
    simpa [lemma38StartVertexι, hn] using hvz
  · apply (wholePlaneVertexι_injective W 0).comp
      (kmswWindowVertexMapInf_injective (shiftedStream W 0) n.toNat)
    simpa [lemma38StartVertexι, hn] using hvz



theorem lemma38StartEdgeWest (W : ℤ → Fin 3) (n : ℤ) (e : ℕ) :
    wholePlaneEdgeWest W (lemma38StartEdgeι W n e) =
      lemma38StartVertexι W n (edgeWest (lemma38StartStream W n) e) := by
  by_cases hn : n ≤ 0
  · simp [lemma38StartEdgeι, lemma38StartVertexι, hn, wholePlaneEdgeWest_ι,
      lemma38StartStream_eq_shifted W n hn]
  · have hn' : 0 ≤ n := by omega
    have hwindow : (fun i : ℕ => shiftedStream W 0 (n.toNat + i)) =
        lemma38StartStream W n := by
      funext i
      change W ((↑(n.toNat + i) : ℤ) - (0 : ℤ)) = W ((↑i : ℤ) + n)
      rw [sub_zero, Nat.cast_add, Int.toNat_of_nonneg hn']
      congr 1
      omega
    simp [lemma38StartEdgeι, lemma38StartVertexι, hn, wholePlaneEdgeWest_ι,
      lemma38StartStream_eq_nonnegative W n hn', kmswWindowEdgeMapInf_edgeWest,
      hwindow]



theorem lemma38StartEdgeEast (W : ℤ → Fin 3) (n : ℤ) (e : ℕ) :
    wholePlaneEdgeEast W (lemma38StartEdgeι W n e) =
      lemma38StartVertexι W n (edgeEast (lemma38StartStream W n) e) := by
  by_cases hn : n ≤ 0
  · simp [lemma38StartEdgeι, lemma38StartVertexι, hn, wholePlaneEdgeEast_ι,
      lemma38StartStream_eq_shifted W n hn]
  · have hn' : 0 ≤ n := by omega
    have hwindow : (fun i : ℕ => shiftedStream W 0 (n.toNat + i)) =
        lemma38StartStream W n := by
      funext i
      change W ((↑(n.toNat + i) : ℤ) - (0 : ℤ)) = W ((↑i : ℤ) + n)
      rw [sub_zero, Nat.cast_add, Int.toNat_of_nonneg hn']
      congr 1
      omega
    simp [lemma38StartEdgeι, lemma38StartVertexι, hn, wholePlaneEdgeEast_ι,
      lemma38StartStream_eq_nonnegative W n hn', kmswWindowEdgeMapInf_edgeEast,
      hwindow]

/-- The combinatorial run outer-face edge set maps to the root and the two
boundary edge sequences at an arbitrary integer start. -/
theorem wholePlaneStart_outerFace_edges_eq_paths (W : ℤ → Fin 3) (n : ℤ)
    (h : BoundaryHitWitnesses (lemma38StartStream W n)) :
    Set.image (lemma38StartEdgeι W n)
        {e : ℕ | ¬ ∃ j : TriangleCreationTime (lemma38StartStream W n),
          (e, true) ∈ stageTriangleDartList (lemma38StartStream W n) j} =
      {lemma38StartEdgeι W n 0} ∪
        Set.range (fun j : ℕ => lemma38StartEdgeι W n
          (kmswRightBoundaryEdge (lemma38StartStream W n) (j + 1))) ∪
        Set.range (fun j : ℕ => lemma38StartEdgeι W n
          (kmswLLCreatedEdge (lemma38StartStream W n)
            (boundaryHitTime (lemma38StartStream W n) h (-((j : ℤ) + 1))))) := by
  have hright (w : ℕ → Fin 3) :
      Set.range (kmswRightBoundaryEdge w) =
        {kmswRightBoundaryEdge w 0} ∪
          Set.range (fun j : ℕ => kmswRightBoundaryEdge w (j + 1)) := by
    ext e
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | zero => exact Or.inl rfl
      | succ j => exact Or.inr ⟨j, rfl⟩
    · intro he
      rcases he with he | ⟨j, rfl⟩
      · simp only [Set.mem_singleton_iff] at he
        exact ⟨0, he.symm⟩
      · exact ⟨j + 1, rfl⟩
  have himage (g : ℕ → ℕ) :
      Set.image (lemma38StartEdgeι W n) (Set.range g) =
        Set.range (fun j => lemma38StartEdgeι W n (g j)) := by
    ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨g j, ⟨j, rfl⟩, rfl⟩
  rw [kmswRun_outerFace_edges_eq_of_hits (lemma38StartStream W n) h]
  calc
    Set.image (lemma38StartEdgeι W n)
        (Set.range (kmswRightBoundaryEdge (lemma38StartStream W n)) ∪
          Set.range (fun j : ℕ => kmswLLCreatedEdge (lemma38StartStream W n)
            (boundaryHitTime (lemma38StartStream W n) h (-((j : ℤ) + 1))))) =
      Set.image (lemma38StartEdgeι W n)
          ({kmswRightBoundaryEdge (lemma38StartStream W n) 0} ∪
            Set.range (fun j : ℕ => kmswRightBoundaryEdge
              (lemma38StartStream W n) (j + 1))) ∪
        Set.image (lemma38StartEdgeι W n)
          (Set.range (fun j : ℕ => kmswLLCreatedEdge (lemma38StartStream W n)
            (boundaryHitTime (lemma38StartStream W n) h (-((j : ℤ) + 1))))) := by
        rw [hright, Set.image_union]
    _ = {lemma38StartEdgeι W n 0} ∪
          Set.range (fun j : ℕ => lemma38StartEdgeι W n
            (kmswRightBoundaryEdge (lemma38StartStream W n) (j + 1))) ∪
          Set.range (fun j : ℕ => lemma38StartEdgeι W n
            (kmswLLCreatedEdge (lemma38StartStream W n)
              (boundaryHitTime (lemma38StartStream W n) h (-((j : ℤ) + 1))))) := by
        rw [Set.image_union, Set.image_singleton,
          himage (fun j : ℕ =>
            kmswRightBoundaryEdge (lemma38StartStream W n) (j + 1)),
          himage (fun j : ℕ =>
            kmswLLCreatedEdge (lemma38StartStream W n)
              (boundaryHitTime (lemma38StartStream W n) h (-((j : ℤ) + 1)))),
          kmswRightBoundaryEdge_zero]




theorem wholePlaneIID_ae_lemma38_integer_starts :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
        ∀ n : ℤ, ∃ h : BoundaryHitWitnesses (lemma38StartStream W n),
          (∃ v : ℕ → WholePlaneVertex W, ∃ e : ℕ → WholePlaneEdge W,
            v 0 = lemma38StartVertexι W n 1 ∧
              (∀ j : ℕ, e j = lemma38StartEdgeι W n
                (kmswRightBoundaryEdge (lemma38StartStream W n) (j + 1))) ∧
              ∀ j : ℕ, wholePlaneRightmostOutgoingAt W H (v j) (e j) ∧
                wholePlaneEdgeEast W (e j) = v (j + 1)) ∧
          wholePlaneEdgePresent W (lemma38StartEdgeι W n 0) ∧
          (∀ j : ℕ, wholePlaneEdgePresent W (lemma38StartEdgeι W n
            (kmswRightBoundaryEdge (lemma38StartStream W n) j))) ∧
          (∀ k : ℤ, k ≤ 0 →
            wholePlaneEdgePresent W (lemma38StartEdgeι W n
              (kmswLLCreatedEdge (lemma38StartStream W n)
                (boundaryHitTime (lemma38StartStream W n) h (k - 1)))) ∧
            ¬ EdgePresent (lemma38StartStream W n)
              (kmswLLCreatedEdge (lemma38StartStream W n)
                (boundaryHitTime (lemma38StartStream W n) h (k - 1)))) ∧
          (∃ v : ℕ → WholePlaneVertex W, ∃ e : ℕ → WholePlaneEdge W,
            v 0 = lemma38StartVertexι W n 0 ∧
              (∀ j : ℕ, e j = lemma38StartEdgeι W n
                (kmswLLCreatedEdge (lemma38StartStream W n)
                  (boundaryHitTime (lemma38StartStream W n) h (-(j : ℤ) - 1)))) ∧
              ∀ j : ℕ, wholePlaneLeftmostIncomingAt W H (v j) (e j) ∧
                wholePlaneEdgeWest W (e j) = v (j + 1)) ∧
          {e | ∃ n₀, ∀ m ≥ n₀, e ∈ (kmswStage (lemma38StartStream W n) m).LR} =
            Set.range (fun j : ℕ =>
              kmswRightBoundaryEdge (lemma38StartStream W n) j) ∧
          {e | ∃ n₀, ∀ m ≥ n₀, e ∈ (kmswStage (lemma38StartStream W n) m).LL} =
            Set.range (fun j : ℕ =>
              kmswLLCreatedEdge (lemma38StartStream W n)
                (boundaryHitTime (lemma38StartStream W n) h (-((j : ℤ) + 1)))) ∧
          Disjoint
            {e | ∃ n₀, ∀ m ≥ n₀,
              e ∈ (kmswStage (lemma38StartStream W n) m).LR}
            {e | ∃ n₀, ∀ m ≥ n₀,
              e ∈ (kmswStage (lemma38StartStream W n) m).LL} ∧
          (∀ v, (∃ m, v < (kmswStage (lemma38StartStream W n) m).nextVertex) →
            (∃ e, EdgePresent (lemma38StartStream W n) e ∧
              edgeWest (lemma38StartStream W n) e = v) ∧
              ((¬ ∃ e, EdgePresent (lemma38StartStream W n) e ∧
                edgeEast (lemma38StartStream W n) e = v) ↔
                ∃ k : ℤ, k ≤ 0 ∧
                  v = boundaryVertex (lemma38StartStream W n) h k)) ∧
          (∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay W H),
            P.vertex 0 = lemma38StartVertexι W n
              (boundaryVertex (lemma38StartStream W n) h k) →
            Q.vertex 0 = lemma38StartVertexι W n
              (boundaryVertex (lemma38StartStream W n) h k') →
            ∃ s s', 0 < s ∧ 0 < s' ∧
              ∀ t, P.vertex (s + t) = Q.vertex (s' + t)) := by
  filter_upwards [wholePlaneIID_ae_lemma38_all_starts] with W hW
  rcases hW with ⟨H, hNeg, hPos⟩
  refine ⟨H, fun n => ?_⟩
  by_cases hn : n ≤ 0
  · have h := hNeg n.natAbs
    have hstream := lemma38StartStream_eq_shifted W n hn
    rw [hstream]
    simpa [lemma38StartEdgeι, lemma38StartVertexι, hn] using h
  · have hn' : 0 ≤ n := by omega
    have h := hPos n.toNat
    have hstream := lemma38StartStream_eq_nonnegative W n hn'
    rw [hstream]
    have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn'
    simpa [lemma38StartEdgeι, lemma38StartVertexι, hn, hnat] using h

end DirectedDistances.KMSW
