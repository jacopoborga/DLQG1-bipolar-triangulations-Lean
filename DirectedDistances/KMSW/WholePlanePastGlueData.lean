module

public import DirectedDistances.KMSW.PastDrawingTransfer
public import DirectedDistances.KMSW.PastSeamMatch
public import DirectedDistances.KMSW.WholePlaneDrawingCombinatorics
import all DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import DirectedDistances.KMSW.StageVertices

public section
namespace DirectedDistances.KMSW.WholePlanePastGlueData

open DirectedDistances.PlanarMap Set

noncomputable section




theorem windowVertex_boundary_or_new (w : ℕ → Fin 3) (s j v : ℕ) :
    (∃ e ∈ (kmswStage w s).UL ++ (kmswStage w s).UR,
      (kmswStage w s).west e = kmswWindowPatchVertexMap w s j v ∨
      (kmswStage w s).east e = kmswWindowPatchVertexMap w s j v) ∨
    (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s j v := by
  induction j generalizing v with
  | zero =>
    left
    refine ⟨(kmswStage w s).active, List.mem_append_left _ ?_, ?_⟩
    · obtain ⟨es, hes⟩ := kmswStage_UL_last w s
      rw [hes]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · unfold kmswWindowPatchVertexMap
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
  | succ j ih =>
    let G := kmswStage w (s + j)
    let F := kmswStage (fun i => w (s + i)) j
    let d := kmswWindowPatchData w s j
    have hrel := kmswWindowPatchData_rel w s j
    have hnew : (kmswStage w s).nextVertex ≤ G.nextVertex :=
      CutConverse.nextVertex_mono w (Nat.le_add_right s j)
    have hres (q : ℕ) (hq : q ∈ d.A ++ d.B) :
        q ∈ (kmswStage w s).UL ++ (kmswStage w s).UR := by
      rcases List.mem_append.mp hq with hq | hq
      · apply List.mem_append_left
        apply List.dropLast_subset
        rw [hrel.left_residual]
        exact List.mem_append_left _ hq
      · apply List.mem_append_right
        rw [hrel.right_residual]
        exact List.mem_append_right _ hq
    have hend (q : ℕ) (hq : q ∈ d.A ++ d.B) :=
      kmswStage_endpoints_stable w (Nat.le_add_right s j)
        ((kmswStage_boundary_ids_lt_nextEdge w s).2 q (by
          have hm := hres q hq
          simp only [List.mem_append] at hm ⊢
          tauto))
    have hl (q : ℕ) (hq : q ∈ d.A) :
        (∃ e ∈ (kmswStage w s).UL ++ (kmswStage w s).UR,
          (kmswStage w s).west e = G.west q ∨
          (kmswStage w s).east e = G.west q) :=
      ⟨q, hres q (List.mem_append_left _ hq),
        Or.inl (hend q (List.mem_append_left _ hq)).1.symm⟩
    have hr (q : ℕ) (hq : q ∈ d.B) :
        (∃ e ∈ (kmswStage w s).UL ++ (kmswStage w s).UR,
          (kmswStage w s).west e = G.east q ∨
          (kmswStage w s).east e = G.east q) :=
      ⟨q, hres q (List.mem_append_right _ hq),
        Or.inr (hend q (List.mem_append_right _ hq)).2.symm⟩
    change (∃ e ∈ (kmswStage w s).UL ++ (kmswStage w s).UR,
      (kmswStage w s).west e = _ ∨ (kmswStage w s).east e = _) ∨ _
    rw [kmswWindowPatchVertexMap]
    cases hc : kmswCodeStep (w (s + j)) with
    | up =>
      dsimp only
      split
      · exact ih v
      · exact Or.inr hnew
    | down =>
      cases hu : F.UR with
      | cons e es => exact ih v
      | nil =>
        cases hb : d.B with
        | nil =>
          dsimp only
          split
          · exact ih v
          · exact Or.inr hnew
        | cons q qs =>
          dsimp only
          split
          · exact ih v
          · exact Or.inl (hr q (by rw [hb]; exact List.mem_cons_self))
    | left =>
      cases hu : F.UL.dropLast.reverse with
      | cons e es => exact ih v
      | nil =>
        cases ha : d.A.reverse with
        | nil =>
          dsimp only
          split
          · exact ih v
          · exact Or.inr hnew
        | cons q qs =>
          dsimp only
          split
          · exact ih v
          · exact Or.inl (hl q (List.mem_reverse.mp (by rw [ha]; exact List.mem_cons_self)))

variable (W : ℤ → Fin 3)




theorem pastDart_vertex (d : ℕ × Bool) :
    wholePlaneDartVertex W (kmswPastDart W d) =
      kmswPastVertex W (kmswLimitDartVertex (kmswPastCode W) d) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp only [kmswPastDart, Bool.not_false, Bool.not_true,
    wholePlaneDartVertex, Bool.false_eq_true, ite_false, ite_true,
    kmswLimitDartVertex, kmswPastEdge_west, kmswPastEdge_east]




theorem pastDart_flip (d : ℕ × Bool) :
    wholePlaneDartFlip W (kmswPastDart W d) = kmswPastDart W (d.1, !d.2) := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl




theorem dart_cover (D : WholePlaneDart W) :
    D ∈ range (wholePlaneDartι W 0) ∨ D ∈ range (kmswPastDart W) := by
  rcases D with ⟨E, b⟩
  rcases kmswPastEdge_cover W E with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · right
    refine ⟨(e, !b), ?_⟩
    cases b <;> rfl
  · exact Or.inl ⟨(e, b), rfl⟩




theorem vertex_incident (V : WholePlaneVertex W) :
    ∃ D, wholePlaneDartVertex W D = V := by
  obtain ⟨⟨N, v⟩, rfl⟩ := Quotient.exists_rep V
  obtain ⟨d, hd⟩ := stageEndpoint_exists (shiftedStream W N) (4 * v + 1) v
    (vertex_allocated_at _ v)
  refine ⟨wholePlaneDartι W N (d.1.val, d.2), ?_⟩
  rw [wholePlaneDartVertex_ι]
  apply congrArg (wholePlaneVertexι W N)
  have he := edge_endpoints_eq (shiftedStream W N) d.1.isLt
  cases hb : d.2 <;>
    simpa only [kmswLimitDartVertex, stageEndpoint, hb, Bool.false_eq_true,
      ite_false, ite_true, he.1, he.2] using hd




theorem vertex_cover (V : WholePlaneVertex W) :
    V ∈ range (wholePlaneVertexι W 0) ∨ V ∈ range (kmswPastVertex W) := by
  obtain ⟨D, rfl⟩ := vertex_incident W V
  rcases dart_cover W D with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact Or.inl ⟨_, (wholePlaneDartVertex_ι W 0 d).symm⟩
  · exact Or.inr ⟨_, (pastDart_vertex W d).symm⟩




theorem past_finiteIncidence (H : WholePlaneRotationHypothesis W) :
    KMSWFiniteIncidence (kmswPastCode W) := by
  intro v
  have hf := (wholePlane_incidentEdges_finite W H (kmswPastVertex W v)).preimage
    (fun _ _ _ _ h => kmswPastEdge_injective W h)
  apply hf.subset
  rintro e ⟨n, he, hv⟩
  have hend := edge_endpoints_eq (kmswPastCode W) he
  change wholePlaneEdgeWest W (kmswPastEdge W e) = kmswPastVertex W v ∨
    wholePlaneEdgeEast W (kmswPastEdge W e) = kmswPastVertex W v
  rw [kmswPastEdge_west, kmswPastEdge_east]
  rcases hv with hv | hv
  · exact Or.inr (congrArg (kmswPastVertex W) (hend.1.symm.trans hv))
  · exact Or.inl (congrArg (kmswPastVertex W) (hend.2.symm.trans hv))

variable (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))




theorem seam_vertex (k : ℤ) :
    kmswPastVertex W (boundaryVertex (kmswPastCode W) hp k) =
      wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h0 (1 - k)) := by
  have he := congrArg (wholePlaneEdgeEast W) (kmswPastEdge_seam_match_neg W h0 hp k)
  rw [kmswPastEdge_east, wholePlaneEdgeEast_ι,
    (boundaryOuterEdge_endpoints (kmswPastCode W) hp k).1,
    (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 (-k)).2.1] at he
  simpa only [show -k + 1 = 1 - k by omega] using he




theorem boundary_vertex_mem_runZero (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) :
    kmswPastVertex W (boundaryVertex (kmswPastCode W) hp k) ∈
      range (wholePlaneVertexι W 0) :=
  ⟨_, (seam_vertex W h0 hp k).symm⟩




theorem past_vertex_boundary_of_mem_runZero (v : ℕ)
    (hv0 : kmswPastVertex W v ∈ range (wholePlaneVertexι W 0)) :
    v ∈ range (boundaryVertex (kmswPastCode W) hp) := by
  obtain ⟨u, hu⟩ := hv0
  let N := 4 * v + 1
  have hv : v < (kmswStage (kmswPastCode W) N).nextVertex := vertex_allocated_at _ v
  have hbound : kmswPastStageVertex W N v <
      (kmswStage (shiftedStream W N) N).nextVertex := by
    obtain ⟨S, hS, hSv⟩ := kmswSlotVertex_surjective (kmswPastCode W) N v hv
    change kmswReversalPhi (kmswPastCode W) (shiftedStream W N) N v < _
    rw [← hSv, kmswReversalPhi_slot _ _ N (kmswPastCode_rev W N) S hS]
    apply kmswSlotVertex_lt
    rw [KMSWSlot.time_mirror]
    exact Nat.sub_le _ _
  have hmap : kmswWindowVertexMapInf (shiftedStream W N) N u =
      kmswPastStageVertex W N v := by
    apply wholePlaneVertexι_injective W N
    change wholePlaneVertexι W N (wholePlaneVertexTrans W 0 N (Nat.zero_le N) u) = _
    exact (congrFun (wholePlaneVertexι_trans W 0 N (Nat.zero_le N)) u).trans
      (hu.trans (kmswPastVertex_eq_stage W N v hv))
  have hb := windowVertex_boundary_or_new (shiftedStream W N) N (4 * u + 1) u
  change (∃ e ∈ (kmswStage (shiftedStream W N) N).UL ++
    (kmswStage (shiftedStream W N) N).UR,
    (kmswStage (shiftedStream W N) N).west e =
      kmswWindowVertexMapInf (shiftedStream W N) N u ∨
    (kmswStage (shiftedStream W N) N).east e =
      kmswWindowVertexMapInf (shiftedStream W N) N u) ∨
    (kmswStage (shiftedStream W N) N).nextVertex ≤
      kmswWindowVertexMapInf (shiftedStream W N) N u at hb
  rw [hmap] at hb
  obtain hb | hb := hb
  · obtain ⟨z, hz, hphi⟩ := kmswReversalPhi_lower_preimage
      (kmswPastCode W) (shiftedStream W N) N (kmswPastCode_rev W N) _ hb
    have hzb : z < (kmswStage (kmswPastCode W) N).nextVertex := by
      obtain ⟨e, he, hez⟩ := hz
      have heb : e < (kmswStage (kmswPastCode W) N).nextEdge := by
        apply (kmswStage_boundary_ids_lt_nextEdge _ N).2
        simp only [List.mem_append] at he ⊢
        tauto
      have hend := kmswStage_endpoints_lt_nextVertex (kmswPastCode W) N e heb
      rcases hez with hez | hez
      · exact hez ▸ hend.1
      · exact hez ▸ hend.2
    have hzv : z = v := by
      apply kmswPastVertex_injective W
      rw [kmswPastVertex_eq_stage W N z hzb, kmswPastVertex_eq_stage W N v hv]
      exact congrArg (wholePlaneVertexι W N) hphi
    obtain ⟨k, hk⟩ := boundaryVertex_covers_lowerBoundary (kmswPastCode W) hp z (by
      obtain ⟨e, he, hez⟩ := hz
      exact ⟨N, e, List.mem_append.mp he, hez⟩)
    exact ⟨k, hk.trans hzv⟩
  · exact (not_le_of_gt hbound hb).elim




theorem past_vertex_mem_runZero_iff (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (v : ℕ) :
    kmswPastVertex W v ∈ range (wholePlaneVertexι W 0) ↔
      v ∈ range (boundaryVertex (kmswPastCode W) hp) := by
  constructor
  · exact past_vertex_boundary_of_mem_runZero W hp v
  · rintro ⟨k, rfl⟩
    exact boundary_vertex_mem_runZero W hp h0 k




theorem dart_cover_off_seam (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (D : WholePlaneDart W) :
    D ∈ range (wholePlaneDartι W 0) ∨
      ∃ d, ¬ kmswPastSeamEdge W d.1 ∧ kmswPastDart W d = D := by
  classical
  by_cases h : D.1 ∈ range (wholePlaneEdgeι W 0)
  · obtain ⟨e, he⟩ := h
    exact Or.inl ⟨(e, D.2), Prod.ext he rfl⟩
  · obtain ⟨e, he⟩ := (kmswPastEdge_cover W D.1).resolve_right h
    have hn : ¬ kmswPastSeamEdge W e := by
      intro hs
      exact h (he ▸ (kmswPastEdge_mem_runZero_iff W h0 e).mpr hs)
    refine Or.inr ⟨(e, !D.2), hn, ?_⟩
    apply Prod.ext he
    exact Bool.not_not D.2

variable (H : WholePlaneRotationHypothesis W)




@[expose] def pastDrawing :
    PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot (kmswPastCode W) (past_finiteIncidence W H))
      (kmswLimitDartVertex (kmswPastCode W)) :=
  Classical.choose (PastDrawingTransfer.pastDrawing_transfer
    (shiftedStream W 0) (kmswPastCode W) h0 hp (H.1 0) (past_finiteIncidence W H))




theorem pastDrawing_pos :
    (pastDrawing W h0 hp H).pos =
      PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W) h0 hp
        (H.1 0) (past_finiteIncidence W H) ∘
      (monotoneFamilyDrawing (kmswPastCode W) (past_finiteIncidence W H)
        (monotone_family_all (kmswPastCode W))).pos :=
  (Classical.choose_spec (PastDrawingTransfer.pastDrawing_transfer
    (shiftedStream W 0) (kmswPastCode W) h0 hp (H.1 0)
    (past_finiteIncidence W H))).1




theorem pastDrawing_arc (d : ℕ × Bool) :
    ((pastDrawing W h0 hp H).arc d).image =
        PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W) h0 hp
          (H.1 0) (past_finiteIncidence W H) ''
        ((monotoneFamilyDrawing (kmswPastCode W) (past_finiteIncidence W H)
          (monotone_family_all (kmswPastCode W))).arc d).image ∧
      ((pastDrawing W h0 hp H).arc d).interior =
        PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W) h0 hp
          (H.1 0) (past_finiteIncidence W H) ''
        ((monotoneFamilyDrawing (kmswPastCode W) (past_finiteIncidence W H)
          (monotone_family_all (kmswPastCode W))).arc d).interior :=
  (Classical.choose_spec (PastDrawingTransfer.pastDrawing_transfer
    (shiftedStream W 0) (kmswPastCode W) h0 hp (H.1 0)
    (past_finiteIncidence W H))).2 d




theorem pastDrawing_seam_pos (k : ℤ) :
    (pastDrawing W h0 hp H).pos (boundaryVertex (kmswPastCode W) hp k) =
      (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).pos
        (boundaryVertex (shiftedStream W 0) h0 (1 - k)) := by
  rw [pastDrawing_pos]
  exact PastDrawingTransfer.transfer_seam_vertex (shiftedStream W 0) (kmswPastCode W)
    h0 hp (H.1 0) (past_finiteIncidence W H) k




@[expose] def gluedPos (V : WholePlaneVertex W) : ℂ := by
  classical
  exact if h : V ∈ range (wholePlaneVertexι W 0) then
    (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).pos (Classical.choose h)
  else
    (pastDrawing W h0 hp H).pos
      (Classical.choose ((vertex_cover W V).resolve_left h))




theorem gluedPos_runZero (v : ℕ) :
    gluedPos W h0 hp H (wholePlaneVertexι W 0 v) =
      (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).pos v := by
  classical
  have h : wholePlaneVertexι W 0 v ∈ range (wholePlaneVertexι W 0) := ⟨v, rfl⟩
  unfold gluedPos
  rw [dite_eq_left h]
  exact congrArg _ (wholePlaneVertexι_injective W 0 (Classical.choose_spec h))




theorem gluedPos_pastDrawing (v : ℕ) :
    gluedPos W h0 hp H (kmswPastVertex W v) = (pastDrawing W h0 hp H).pos v := by
  classical
  unfold gluedPos
  by_cases h : kmswPastVertex W v ∈ range (wholePlaneVertexι W 0)
  · rw [dite_eq_left h]
    obtain ⟨k, rfl⟩ := past_vertex_boundary_of_mem_runZero W hp v h
    have he : Classical.choose h = boundaryVertex (shiftedStream W 0) h0 (1 - k) :=
      wholePlaneVertexι_injective W 0
        ((Classical.choose_spec h).trans (seam_vertex W h0 hp k))
    rw [he]
    exact (pastDrawing_seam_pos W h0 hp H k).symm
  · rw [dite_eq_right h]
    exact congrArg _ (kmswPastVertex_injective W
      (Classical.choose_spec ((vertex_cover W (kmswPastVertex W v)).resolve_left h)))




theorem gluedPos_past (v : ℕ) :
    gluedPos W h0 hp H (kmswPastVertex W v) =
      PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W) h0 hp
        (H.1 0) (past_finiteIncidence W H)
        ((monotoneFamilyDrawing (kmswPastCode W) (past_finiteIncidence W H)
          (monotone_family_all (kmswPastCode W))).pos v) := by
  rw [gluedPos_pastDrawing, pastDrawing_pos]
  rfl




@[expose] def gluedArc (D : WholePlaneDart W) : Polyline := by
  classical
  exact if h : D.1 ∈ range (wholePlaneEdgeι W 0) then
    (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc (Classical.choose h, D.2)
  else
    (pastDrawing W h0 hp H).arc
      (Classical.choose ((kmswPastEdge_cover W D.1).resolve_right h), !D.2)




theorem gluedArc_runZero (d : ℕ × Bool) :
    gluedArc W h0 hp H (wholePlaneDartι W 0 d) =
      (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc d := by
  classical
  have hh : (wholePlaneDartι W 0 d).1 ∈ range (wholePlaneEdgeι W 0) := ⟨d.1, rfl⟩
  unfold gluedArc
  rw [dite_eq_left hh]
  have he : Classical.choose hh = d.1 :=
    wholePlaneEdgeι_injective W 0 (Classical.choose_spec hh)
  rw [he]
  rfl




theorem gluedArc_past (d : ℕ × Bool) (hd : ¬ kmswPastSeamEdge W d.1) :
    gluedArc W h0 hp H (kmswPastDart W d) = (pastDrawing W h0 hp H).arc d := by
  classical
  have hh : (kmswPastDart W d).1 ∉ range (wholePlaneEdgeι W 0) := by
    intro h
    exact hd ((kmswPastEdge_mem_runZero_iff W h0 d.1).mp h)
  unfold gluedArc
  rw [dite_eq_right hh]
  have he : Classical.choose
      ((kmswPastEdge_cover W (kmswPastDart W d).1).resolve_right hh) = d.1 :=
    kmswPastEdge_injective W (Classical.choose_spec
      ((kmswPastEdge_cover W (kmswPastDart W d).1).resolve_right hh))
  rw [he]
  rcases d with ⟨e, b⟩
  cases b <;> rfl




theorem gluedArc_simple (D : WholePlaneDart W) :
    (gluedArc W h0 hp H D).IsSimple := by
  classical
  unfold gluedArc
  split
  · exact (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc_simple _
  · exact (pastDrawing W h0 hp H).arc_simple _




theorem gluedArc_length (D : WholePlaneDart W) :
    2 ≤ (gluedArc W h0 hp H D).points.length := by
  classical
  unfold gluedArc
  split
  · exact (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc_length _
  · exact (pastDrawing W h0 hp H).arc_length _




theorem gluedArc_initial_nonzero (D : WholePlaneDart W) :
    (gluedArc W h0 hp H D).initialDirection ≠ 0 := by
  classical
  unfold gluedArc
  split
  · exact (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).initial_nonzero _
  · exact (pastDrawing W h0 hp H).initial_nonzero _




theorem gluedArc_flip (D : WholePlaneDart W) :
    gluedArc W h0 hp H (wholePlaneDartFlip W D) =
      (gluedArc W h0 hp H D).reverse := by
  classical
  rcases D with ⟨E, b⟩
  change gluedArc W h0 hp H (E, !b) = _
  unfold gluedArc
  by_cases h : E ∈ range (wholePlaneEdgeι W 0)
  · rw [dite_eq_left h, dite_eq_left h]
    exact (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc_flip (_, b)
  · rw [dite_eq_right h, dite_eq_right h]
    exact (pastDrawing W h0 hp H).arc_flip (_, !b)




theorem gluedArc_start (D : WholePlaneDart W) :
    (gluedArc W h0 hp H D).start = gluedPos W h0 hp H (wholePlaneDartVertex W D) := by
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
  · rw [gluedArc_runZero, wholePlaneDartVertex_ι, gluedPos_runZero]
    exact (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc_start d
  · rw [gluedArc_past W h0 hp H d hd, pastDart_vertex, gluedPos_pastDrawing]
    exact (pastDrawing W h0 hp H).arc_start d




theorem gluedArc_finish (D : WholePlaneDart W) :
    (gluedArc W h0 hp H D).finish =
      gluedPos W h0 hp H (wholePlaneDartVertex W (wholePlaneDartFlip W D)) := by
  have hs := gluedArc_start W h0 hp H (wholePlaneDartFlip W D)
  rw [gluedArc_flip, Polyline.start_reverse] at hs
  exact hs

end
end DirectedDistances.KMSW.WholePlanePastGlueData
