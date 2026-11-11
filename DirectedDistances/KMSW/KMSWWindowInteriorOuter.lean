module

public import DirectedDistances.KMSW.KMSWWindowPatchStar

/-! are exactly those whose fresh vertex has no outer-face dart (Definition 3.8 independent; S3 -/

public section
namespace DirectedDistances.KMSW

/-- darts are exactly those whose fresh vertex has no outer-face dart (Definition 3.8 independent; -/
theorem stage_rot_orbit_triangle_iff_no_outer (u : ℕ → Fin 3) (m : ℕ)
    (x : StageDart (kmswStage u m).nextEdge) :
    (∀ k : ℕ,
      ((((kmswMap u m).rot ^ k) x).1.val, (((kmswMap u m).rot ^ k) x).2) ∈
        stageTriangleDartsVal u m) ↔
    ∀ y : StageDart (kmswStage u m).nextEdge,
      stageEndpoint (kmswStage u m) y = stageEndpoint (kmswStage u m) x →
        y ∉ stageOuterWord u m := by
  constructor
  · intro h y hy hout
    have hc := (stageRot_sameCycle_iff_endpoint_eq u m x y).mpr hy.symm
    obtain ⟨k, hk⟩ := hc.exists_nat_pow_eq
    have hk' : ((kmswMap u m).rot ^ k) x = y := hk
    have h1 := h k
    rw [hk'] at h1
    exact stage_outer_triangle_disjoint u m ((stageOuterWord_mem_val u m y).mp hout) h1
  · intro h k
    have hend : stageEndpoint (kmswStage u m) (((kmswMap u m).rot ^ k) x) =
        stageEndpoint (kmswStage u m) x := by
      apply (stageRot_sameCycle_iff_endpoint_eq u m _ _).mp
      exact Equiv.Perm.SameCycle.rfl.pow_left
    rcases stage_dart_partition u m (((kmswMap u m).rot ^ k) x) with ho | ⟨j, ⟨hj, hmem⟩, _⟩
    · exact absurd ho (h _ hend)
    · exact List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes u m j).mpr hj, hmem⟩

/-- darts are exactly those whose fresh vertex has no outer-face dart (Definition 3.8 independent; -/
theorem kmswWindowInteriorDart_iff_no_outer (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    KMSWWindowInteriorDart w s m x ↔
      ∀ y : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
        stageEndpoint (kmswStage (fun i => w (s + i)) m) y =
            stageEndpoint (kmswStage (fun i => w (s + i)) m) x →
          y ∉ stageOuterWord (fun i => w (s + i)) m :=
  stage_rot_orbit_triangle_iff_no_outer (fun i => w (s + i)) m x

end DirectedDistances.KMSW
