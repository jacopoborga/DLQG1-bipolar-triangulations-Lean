module

public import DirectedDistances.KMSW.KMSWStageBallDarts

/-! Helper toward prop-disk-bs-conv (Proposition 5.16,
not a paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem kmswStagePath_endpoint_lt_nextVertex
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n c : ℕ)
    {k v : ℕ} (hc : c < (kmswStage w n).nextVertex)
    (hpath : KMSWStagePath P (kmswStage w n) Set.univ c k v) :
    v < (kmswStage w n).nextVertex := by
  cases hpath with
  | nil _ => exact hc
  | @snoc k y z hpre hy hz hadj =>
      obtain ⟨d, hdP, hstart, hend⟩ := hadj
      cases d with
      | mk e b =>
          have hends := kmswStage_endpoints_lt_nextVertex w n e.val e.isLt
          rw [edgeFlip_apply] at hend
          cases b
          · change (kmswStage w n).east e.val = v at hend
            calc
              v = (kmswStage w n).east e.val := hend.symm
              _ < (kmswStage w n).nextVertex := hends.2
          · change (kmswStage w n).west e.val = v at hend
            calc
              v = (kmswStage w n).west e.val := hend.symm
              _ < (kmswStage w n).nextVertex := hends.1

/-- Every vertex reached within bounded distance from an allocated center is
allocated in the generated stage (`def-kmsw`, -/
theorem kmswStageDistanceLe_endpoint_lt_nextVertex
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c v : ℕ)
    (hc : c < (kmswStage w n).nextVertex)
    (hcv : kmswStageDistanceLe P (kmswStage w n) r c v) :
    v < (kmswStage w n).nextVertex := by
  obtain ⟨k, hk, hpath⟩ := hcv
  exact kmswStagePath_endpoint_lt_nextVertex P w n c hc hpath

/-- On a generated stage, the finite vertex ball is exactly bounded-distance
reachability from an allocated center -/
theorem kmswStageBallVertices_mem_iff_distanceLe
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c v : ℕ)
    (hc : c < (kmswStage w n).nextVertex) :
    v ∈ kmswStageBallVertices P (kmswStage w n) r c ↔
      kmswStageDistanceLe P (kmswStage w n) r c v := by
  classical
  rw [kmswStageBallVertices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hv⟩
    exact hv
  · intro hv
    exact ⟨kmswStageDistanceLe_endpoint_lt_nextVertex P w n r c v hc hv, hv⟩

/-- On a generated stage, a dart belongs to the finite ball-dart set exactly
when both endpoints are within bounded distance from an allocated center -/
theorem kmswStageBallDarts_mem_iff_distanceLe_endpoints
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (hc : c < (kmswStage w n).nextVertex)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageBallDarts P (kmswStage w n) r c ↔
      kmswStageDistanceLe P (kmswStage w n) r c
        (stageEndpoint (kmswStage w n) d) ∧
      kmswStageDistanceLe P (kmswStage w n) r c
        (stageEndpoint (kmswStage w n) (edgeFlip _ d)) := by
  rw [kmswStageBallDarts_mem_iff,
    kmswStageBallVertices_mem_iff_distanceLe P w n r c
      (stageEndpoint (kmswStage w n) d) hc,
    kmswStageBallVertices_mem_iff_distanceLe P w n r c
      (stageEndpoint (kmswStage w n) (edgeFlip _ d)) hc]

private theorem kmswStageEndpoint_lt_nextVertex
    (w : ℕ → Fin 3) (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d < (kmswStage w n).nextVertex := by
  cases d with
  | mk e b =>
      have hends := kmswStage_endpoints_lt_nextVertex w n e.val e.isLt
      cases b
      · simpa [stageEndpoint] using hends.1
      · simpa [stageEndpoint] using hends.2

/-- Generated-stage dart membership has no centre-bound premise because each -/
theorem kmswStageBallDarts_mem_iff_distanceLe
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageBallDarts P (kmswStage w n) r c ↔
      kmswStageDistanceLe P (kmswStage w n) r c
        (stageEndpoint (kmswStage w n) d) ∧
      kmswStageDistanceLe P (kmswStage w n) r c
        (stageEndpoint (kmswStage w n) (edgeFlip _ d)) := by
  rw [kmswStageBallDarts_mem_iff]
  simp only [kmswStageBallVertices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hleft⟩, ⟨_, hright⟩⟩
    exact ⟨hleft, hright⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨⟨kmswStageEndpoint_lt_nextVertex w n d, hleft⟩,
      ⟨kmswStageEndpoint_lt_nextVertex w n (edgeFlip _ d), hright⟩⟩

private theorem kmswStageDistanceLe_succ_of_adj
    (P : KMSWStageEdgePredicate) (s : State) (r c x y : ℕ)
    (hxy : kmswStageDistanceLe P s r c x)
    (hadj : kmswStageAdjacent P s x y) :
    kmswStageDistanceLe P s (r + 1) c y := by
  obtain ⟨k, hk, hpath⟩ := hxy
  refine ⟨k + 1, Nat.add_le_add_right hk 1, ?_⟩
  exact .snoc hpath (Set.mem_univ _) (Set.mem_univ _) hadj

/-- An admissible dart step enlarges the distance radius by one in either -/
theorem kmswStageDistanceLe_otherEndpoint_succ
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : P (kmswStage w n) d.1) :
    (kmswStageDistanceLe P (kmswStage w n) r c
        (stageEndpoint (kmswStage w n) d) →
      kmswStageDistanceLe P (kmswStage w n) (r + 1) c
        (stageEndpoint (kmswStage w n) (edgeFlip _ d))) ∧
    (kmswStageDistanceLe P (kmswStage w n) r c
        (stageEndpoint (kmswStage w n) (edgeFlip _ d)) →
      kmswStageDistanceLe P (kmswStage w n) (r + 1) c
        (stageEndpoint (kmswStage w n) d)) := by
  constructor
  · intro hdist
    apply kmswStageDistanceLe_succ_of_adj P (kmswStage w n) r c
      (stageEndpoint (kmswStage w n) d)
      (stageEndpoint (kmswStage w n) (edgeFlip _ d)) hdist
    exact ⟨d, hd, rfl, rfl⟩
  · intro hdist
    apply kmswStageDistanceLe_succ_of_adj P (kmswStage w n) r c
      (stageEndpoint (kmswStage w n) (edgeFlip _ d))
      (stageEndpoint (kmswStage w n) d) hdist
    cases d with
    | mk e b =>
        refine ⟨(e, !b), ?_, rfl, ?_⟩
        · exact hd
        · cases b <;> rfl

end DirectedDistances.KMSW
