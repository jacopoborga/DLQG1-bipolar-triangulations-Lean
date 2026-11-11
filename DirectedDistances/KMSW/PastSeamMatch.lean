module

public import DirectedDistances.KMSW.PastReversalColimit
public import DirectedDistances.KMSW.StageReversalEdges
public import DirectedDistances.KMSW.M0CutSeam
public import DirectedDistances.KMSW.M0CutLeftSide
public import DirectedDistances.KMSW.M0CutPresence
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.KMSWWholePlaneColimit

import all DirectedDistances.KMSW.M0CutLeftSide
import all DirectedDistances.KMSW.StageReversalEdges
import all DirectedDistances.KMSW.KMSWWindowPatchTriangles
import all DirectedDistances.KMSW.KMSWWindowInfiniteMaps

public section
namespace DirectedDistances.KMSW




@[expose] def kmswPastSeamEdge (W : ℤ → Fin 3) (e : ℕ) : Prop :=
  ∃ N, e ∈ (kmswStage (kmswPastCode W) N).LL ++
    (kmswStage (kmswPastCode W) N).LR




theorem kmswPastEdge_stage_cover (W : ℤ → Fin 3) (N e : ℕ)
    (he : e < (kmswStage (shiftedStream W N) N).nextEdge) :
    ∃ f, kmswPastEdge W f = wholePlaneEdgeι W N e := by
  obtain ⟨f, hf, hfe⟩ :=
    (kmswRevEdge_bijOn _ _ N (kmswPastCode_rev W N)).surjOn he
  refine ⟨f, ?_⟩
  rw [kmswPastEdge_eq_stage W N f hf]
  exact congrArg (wholePlaneEdgeι W N) hfe




theorem kmswPastEdge_root (W : ℤ → Fin 3) :
    kmswPastEdge W 0 = wholePlaneEdgeι W 0 0 := by
  rw [kmswPastEdge_eq_stage W 0 0 (by change 0 < 1; decide)]
  change wholePlaneEdgeι W 0 (kmswRevEdge (shiftedStream W 0) (kmswPastCode W) 0
    (kmswStage (kmswPastCode W) 0).active) = _
  rw [kmswRevEdge_active _ _ 0 0 le_rfl]
  rfl




theorem kmswPastDart_root (W : ℤ → Fin 3) :
    kmswPastDart W (0, false) = (wholePlaneEdgeι W 0 0, true) := by
  change (kmswPastEdge W 0, true) = _
  rw [kmswPastEdge_root]




theorem kmswPastStageEdge_lower_boundary (W : ℤ → Fin 3) (N : ℕ) :
    ((kmswStage (kmswPastCode W) N).LL ++
      (kmswStage (kmswPastCode W) N).LR).map (kmswPastStageEdge W N) =
    ((kmswStage (shiftedStream W N) N).UL ++
      (kmswStage (shiftedStream W N) N).UR).reverse :=
  kmswRevEdge_lower_boundary _ _ N (kmswPastCode_rev W N)




theorem kmswPastStage_UR_length (W : ℤ → Fin 3) (N : ℕ) :
    (kmswStage (shiftedStream W N) N).UR.length =
      (kmswStage (kmswPastCode W) N).LL.length :=
  (kmswStage_reverse_LL_length _ _ N (kmswPastCode_rev W N)).symm




theorem kmswPastSeam_index_neg (W : ℤ → Fin 3) (N : ℕ) (k : ℤ) :
    (((kmswStage (shiftedStream W N) N).UL ++
      (kmswStage (shiftedStream W N) N).UR).length : ℤ) - 1 -
        ((kmswStage (kmswPastCode W) N).LL.length + k) =
      ((kmswStage (shiftedStream W N) N).UL.length : ℤ) - 1 - k := by
  rw [List.length_append, Nat.cast_add, kmswPastStage_UR_length]
  omega




private theorem seam_window_triangle_preimage (w : ℕ → Fin 3) (s j : ℕ)
    (hc : w (s + j) = 0 ∨ w (s + j) = 1) (e : ℕ)
    (he : ∃ b, (e, b) ∈ stageTriangleDartList w ⟨s + j, hc⟩) :
    ∃ f, kmswWindowEdgeMapInf w s f = e := by
  obtain ⟨b, hb⟩ := he
  have hr := kmswWindowPatchData_triangle_rotated w s (j + 1) j
    (Nat.lt_succ_self j) hc
  have hm := hr.perm.mem_iff.mpr hb
  obtain ⟨d, hd, hde⟩ := List.mem_map.mp hm
  refine ⟨d.1, ?_⟩
  rw [kmswWindowEdgeMapInf_eq_stage w s (j + 1) d.1
    (stageTriangleDartList_lt _ _ _ (Nat.lt_succ_self j) d hd)]
  exact congrArg Prod.fst hde




theorem kmswWindowEdgeMapInf_range_of_new (w : ℕ → Fin 3) (s e : ℕ)
    (he : (kmswStage w s).nextEdge ≤ e) :
    e ∈ Set.range (kmswWindowEdgeMapInf w s) := by
  let n := max s e
  have hen : e < (kmswStage w n).nextEdge :=
    (kmsw_edge_allocated_by_self w e).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_max_right _ _))
  cases hp : (kmswStage w n).present e with
  | true =>
    obtain ⟨t, _, ht⟩ := kmswStage_present_eq_active w n e hen hp
    have hst : s ≤ t := by
      by_contra h
      have hb := (kmswStage_active_lt w t).trans_le
        (kmswStage_nextEdge_mono w (show t ≤ s by omega))
      rw [ht] at hb
      omega
    refine ⟨(kmswStage (fun i => w (s + i)) (t - s)).active, ?_⟩
    rw [kmswWindowEdgeMapInf_active, Nat.add_sub_of_le hst, ht]
  | false =>
    have hr : ∃ t, kmswRevUpRecord w n e t ∨ kmswRevLeftRecord w n e t := by
      rcases (kmswStage_missing_iff_UR_or_LL w n e hen).mp hp with hu | hl
      · obtain ⟨t, ht⟩ := kmswStage_UR_exists_revUpRecord w n e hu
        exact ⟨t, Or.inl ht⟩
      · obtain ⟨t, ht⟩ := kmswStage_LL_exists_revLeftRecord w n e hl
        exact ⟨t, Or.inr ht⟩
    obtain ⟨t, ht⟩ := hr
    have hb := kmswRevRecord_allocated w n e t ht
    have hst : s ≤ t := by
      by_contra h
      have hb' := hb.2.trans_le
        (kmswStage_nextEdge_mono w (show t + 1 ≤ s by omega))
      omega
    have hc : w t = 0 ∨ w t = 1 := by
      rcases ht with ht | ht
      · exact Or.inr ht.2.1
      · exact Or.inl ht.2.1
    have hm : ∃ b, (e, b) ∈ stageTriangleDartList w ⟨t, hc⟩ := by
      rcases ht with ht | ht
      · refine ⟨true, ?_⟩
        simp [stageTriangleDartList, stageTriangleDartTriple, ht.2.1, hb.1]
      · have hn : (kmswStage w t).UL.dropLast.reverse = [] := by
          have hl := kmswStage_UL_length w t
          apply List.length_eq_zero_iff.mp
          simp only [List.length_reverse, List.length_dropLast]
          have hm := ht.2.2.1
          omega
        refine ⟨false, ?_⟩
        simp [stageTriangleDartList, stageTriangleDartTriple, ht.2.1, hn, hb.1]
    apply seam_window_triangle_preimage w s (t - s)
      (by rwa [Nat.add_sub_of_le hst]) e
    simpa only [Nat.add_sub_of_le hst] using hm




theorem kmswPastEdge_cover (W : ℤ → Fin 3) (E : WholePlaneEdge W) :
    E ∈ Set.range (kmswPastEdge W) ∨ E ∈ Set.range (wholePlaneEdgeι W 0) := by
  obtain ⟨⟨N, e⟩, rfl⟩ := Quotient.exists_rep E
  change wholePlaneEdgeι W N e ∈ _ ∨ wholePlaneEdgeι W N e ∈ _
  by_cases he : e < (kmswStage (shiftedStream W N) N).nextEdge
  · obtain ⟨f, hf⟩ := kmswPastEdge_stage_cover W N e he
    exact Or.inl ⟨f, hf⟩
  · obtain ⟨f, hf⟩ := kmswWindowEdgeMapInf_range_of_new (shiftedStream W N) N e
      (by omega)
    right
    refine ⟨f, ?_⟩
    have htrans : wholePlaneEdgeTrans W 0 N (Nat.zero_le N) f = e := by
      unfold wholePlaneEdgeTrans
      simp only [Nat.sub_zero]
      exact hf
    rw [← htrans]
    exact (congrFun (wholePlaneEdgeι_trans W 0 N (Nat.zero_le N)) f).symm





private theorem seam_patch_residual {G0 G F : State} {d : KMSWWindowPatchData}
    (h : KMSWWindowPatchRel G0 G F d.φ d.A d.B d.YL d.YR d.XL d.XR)
    {q : ℕ} (hq : q ∈ d.A ++ d.B) : q ∈ G0.UL ++ G0.UR := by
  rcases List.mem_append.mp hq with ha | hb
  · apply List.mem_append_left
    apply List.dropLast_subset
    rw [h.left_residual]
    exact List.mem_append_left _ ha
  · apply List.mem_append_right
    rw [h.right_residual]
    exact List.mem_append_right _ hb




private theorem seam_patch_new_old {G0 G F : State} {d : KMSWWindowPatchData}
    (h : KMSWWindowPatchRel G0 G F d.φ d.A d.B d.YL d.YR d.XL d.XR)
    (hbase : G0.nextEdge ≤ G.nextEdge) (c : Step) (f : ℕ)
    (hf : F.nextEdge ≤ f) (hb : f < (kmswStepOfStep F c).nextEdge)
    (hold : (d.step G F c).φ f < G0.nextEdge) :
    (d.step G F c).φ f ∈ G0.UL ++ G0.UR := by
  have hnot : ¬ f < F.nextEdge := by omega
  cases c with
  | up =>
    simp only [KMSWWindowPatchData.step, ite_eq_right hnot] at hold
    omega
  | down =>
    cases hu : F.UR with
    | cons q qs => simp only [kmswStepOfStep, hu] at hb; omega
    | nil =>
      cases hB : d.B with
      | nil =>
        simp only [KMSWWindowPatchData.step, hu, hB, ite_eq_right hnot] at hold
        omega
      | cons q qs =>
        have hq : q ∈ d.A ++ d.B := by rw [hB]; simp only [List.mem_append,
          List.mem_cons, true_or, or_true]
        simpa only [KMSWWindowPatchData.step, hu, hB, ite_eq_right hnot] using
          seam_patch_residual h hq
  | left =>
    cases hu : F.UL.dropLast.reverse with
    | cons q qs =>
      simp only [KMSWWindowPatchData.step, hu, ite_eq_right hnot] at hold
      omega
    | nil =>
      cases hA : d.A.reverse with
      | nil =>
        simp only [KMSWWindowPatchData.step, hu, hA, ite_eq_right hnot] at hold
        omega
      | cons q qs =>
        by_cases hfe : f = F.nextEdge
        · simp only [KMSWWindowPatchData.step, hu, hA, ite_eq_right hnot,
            ite_eq_left hfe] at hold
          omega
        · have hq : q ∈ d.A ++ d.B := by
            apply List.mem_append_left
            apply List.mem_reverse.mp
            rw [hA]
            exact List.mem_cons_self
          simpa only [KMSWWindowPatchData.step, hu, hA, ite_eq_right hnot,
            ite_eq_right hfe] using seam_patch_residual h hq




private theorem seam_window_old (w : ℕ → Fin 3) (s m f : ℕ)
    (hf : f < (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hold : (kmswWindowPatchData w s m).φ f < (kmswStage w s).nextEdge) :
    (kmswWindowPatchData w s m).φ f ∈
      (kmswStage w s).UL ++ (kmswStage w s).UR := by
  induction m with
  | zero =>
    change (kmswStage w s).active ∈ _
    obtain ⟨es, hes⟩ := kmswStage_UL_last w s
    apply List.mem_append_left
    rw [hes]
    exact List.mem_append_right _ (List.mem_cons_self)
  | succ m ih =>
    by_cases hfm : f < (kmswStage (fun i => w (s + i)) m).nextEdge
    · rw [kmswWindowPatchData_extends w s m f hfm] at hold ⊢
      exact ih hfm hold
    · exact seam_patch_new_old (kmswWindowPatchData_rel w s m)
        (kmswStage_nextEdge_mono w (Nat.le_add_right s m))
        (kmswCodeStep (w (s + m))) f (by omega) hf hold




theorem kmswWindowEdgeMapInf_old_mem_upper (w : ℕ → Fin 3) (s f : ℕ)
    (hold : kmswWindowEdgeMapInf w s f < (kmswStage w s).nextEdge) :
    kmswWindowEdgeMapInf w s f ∈
      (kmswStage w s).UL ++ (kmswStage w s).UR := by
  rw [kmswWindowEdgeMapInf_eq_stage w s f f (kmsw_edge_allocated_by_self _ f)]
    at hold ⊢
  exact seam_window_old w s f f (kmsw_edge_allocated_by_self _ f) hold




theorem kmswPastStageEdge_mem_upper_iff (W : ℤ → Fin 3) (N e : ℕ)
    (he : e < (kmswStage (kmswPastCode W) N).nextEdge) :
    kmswPastStageEdge W N e ∈ (kmswStage (shiftedStream W N) N).UL ++
        (kmswStage (shiftedStream W N) N).UR ↔
      e ∈ (kmswStage (kmswPastCode W) N).LL ++
        (kmswStage (kmswPastCode W) N).LR := by
  rw [← List.mem_reverse, ← kmswPastStageEdge_lower_boundary]
  constructor
  · intro hm
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hm
    have hfb : f < (kmswStage (kmswPastCode W) N).nextEdge := by
      apply (kmswStage_boundary_ids_lt_nextEdge _ N).2
      simp only [List.mem_append] at hf ⊢
      tauto
    have hsame := (kmswRevEdge_bijOn _ _ N (kmswPastCode_rev W N)).injOn hfb he hfe
    exact hsame ▸ hf
  · intro hm
    exact List.mem_map.mpr ⟨e, hm, rfl⟩




theorem kmswPastEdge_inter (W : ℤ → Fin 3) (e : ℕ)
    (he : kmswPastEdge W e ∈ Set.range (wholePlaneEdgeι W 0)) :
    kmswPastSeamEdge W e := by
  obtain ⟨f, hf⟩ := he
  rw [kmswPastEdge_eq_stage W e e (kmsw_edge_allocated_by_self _ e)] at hf
  obtain ⟨M, h0M, heM, hh⟩ := Quotient.exact hf
  change wholePlaneEdgeTrans W 0 M h0M f =
    wholePlaneEdgeTrans W e M heM (kmswPastStageEdge W e e) at hh
  rw [kmswPastStageEdge_trans W e M e heM (kmsw_edge_allocated_by_self _ e)] at hh
  have heb : e < (kmswStage (kmswPastCode W) M).nextEdge :=
    (kmsw_edge_allocated_by_self _ e).trans_le (kmswStage_nextEdge_mono _ heM)
  have hb := kmswRevEdge_mapsTo _ _ M (kmswPastCode_rev W M) heb
  have hm : kmswPastStageEdge W M e ∈
      (kmswStage (shiftedStream W M) M).UL ++
        (kmswStage (shiftedStream W M) M).UR := by
    have hh' : kmswWindowEdgeMapInf (shiftedStream W M) M f =
        kmswPastStageEdge W M e := by
      simpa only [wholePlaneEdgeTrans, Nat.sub_zero] using hh
    rw [← hh']
    exact kmswWindowEdgeMapInf_old_mem_upper _ M f (hh'.symm ▸ hb)
  exact ⟨M, (kmswPastStageEdge_mem_upper_iff W M e heb).mp hm⟩





theorem kmswWindowEdgeMapInf_range_upper_lower (w : ℕ → Fin 3) (s : ℕ)
    (h : BoundaryHitWitnesses (fun i => w (s + i))) (e : ℕ)
    (he : e ∈ (kmswStage w s).UL ++ (kmswStage w s).UR) :
    ∃ f m, f ∈ (kmswStage (fun i => w (s + i)) m).LL ++
      (kmswStage (fun i => w (s + i)) m).LR ∧ kmswWindowEdgeMapInf w s f = e := by
  let u := fun i => w (s + i)
  let G0 := kmswStage w s
  obtain ⟨l, hl⟩ := h.leftHit (-((G0.UL.length : ℤ) + 1)) (by omega)
  obtain ⟨r, hr⟩ := h.rightHit ((G0.UR.length : ℤ) + 2) (by omega)
  let m := max l r
  let F := kmswStage u m
  let d := kmswWindowPatchData w s m
  have hrel := kmswWindowPatchData_rel w s m
  change KMSWWindowPatchRel G0 _ F d.φ d.A d.B d.YL d.YR d.XL d.XR at hrel
  have hllen := kmswStage_LL_length u m
  have hlmin := runningMin_le (L u) m l (Nat.le_max_left _ _)
  have hrlen := kmswStage_LR_length u m
  have hrmin := runningMin_le (R u) m r (Nat.le_max_right _ _)
  change minL u m ≤ L u l at hlmin
  change minR u m ≤ R u r at hrmin
  change L u l = _ at hl
  change R u r = _ at hr
  have hA : d.A = [] := by
    by_contra ha
    have hxl := hrel.xl_nil ha
    have hs := congrArg List.length hrel.ll_split
    have ht := congrArg List.length hrel.left_residual
    simp only [List.length_append, List.length_map, List.length_dropLast] at ht hs
    rw [hxl] at hs
    simp only [List.length_nil] at hs
    change ((F.LL.length : ℤ)) = _ at hllen
    omega
  have hB : d.B = [] := by
    by_contra hb
    have hxr := hrel.xr_nil hb
    have hs := congrArg List.length hrel.lr_split
    have ht := congrArg List.length hrel.right_residual
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil] at ht hs
    rw [hxr] at hs
    simp only [List.length_nil] at hs
    change ((F.LR.length : ℤ)) = _ at hrlen
    omega
  have hpre : ∃ f, f ∈ F.LL ++ F.LR ∧ d.φ f = e := by
    rcases List.mem_append.mp he with heUL | heUR
    · obtain ⟨es, hes⟩ := kmswStage_UL_last w s
      rw [hes] at heUL
      rcases List.mem_append.mp heUL with hedrop | heact
      · have hd : e ∈ G0.UL.dropLast := by
          change e ∈ (kmswStage w s).UL.dropLast
          rw [hes, List.dropLast_concat]
          exact hedrop
        rw [hrel.left_residual, hA, List.nil_append] at hd
        obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hd
        refine ⟨f, List.mem_append_left _ ?_, hfe⟩
        rw [hrel.ll_split]
        exact List.mem_append_right _ hf
      · have heq : e = G0.active := List.mem_singleton.mp heact
        refine ⟨0, List.mem_append_right _ ?_, hrel.root.trans heq.symm⟩
        rw [hrel.lr_split]
        simp only [List.mem_append, List.mem_singleton, true_or]
    · change e ∈ G0.UR at heUR
      rw [hrel.right_residual, hB, List.append_nil] at heUR
      obtain ⟨f, hf, hfe⟩ := List.mem_map.mp heUR
      refine ⟨f, List.mem_append_right _ ?_, hfe⟩
      rw [hrel.lr_split]
      simp only [List.mem_append, List.mem_singleton]
      exact Or.inl (Or.inr hf)
  obtain ⟨f, hf, hfe⟩ := hpre
  have hfb : f < F.nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge u m).2
    simp only [List.mem_append] at hf ⊢
    tauto
  exact ⟨f, m, hf, (kmswWindowEdgeMapInf_eq_stage w s m f hfb).trans hfe⟩




theorem kmswWindowEdgeMapInf_range_upper (w : ℕ → Fin 3) (s : ℕ)
    (h : BoundaryHitWitnesses (fun i => w (s + i))) (e : ℕ)
    (he : e ∈ (kmswStage w s).UL ++ (kmswStage w s).UR) :
    e ∈ Set.range (kmswWindowEdgeMapInf w s) := by
  obtain ⟨f, _, _, hf⟩ := kmswWindowEdgeMapInf_range_upper_lower w s h e he
  exact ⟨f, hf⟩




theorem kmswPastEdge_inter_converse (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ)
    (he : kmswPastSeamEdge W e) :
    kmswPastEdge W e ∈ Set.range (wholePlaneEdgeι W 0) := by
  obtain ⟨N, heN⟩ := he
  have heb : e < (kmswStage (kmswPastCode W) N).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge _ N).2
    simp only [List.mem_append] at heN ⊢
    tauto
  have hs : (fun i => shiftedStream W N (N + i)) = shiftedStream W 0 := by
    simpa only [Nat.sub_zero] using shiftedStream_shift W 0 N (Nat.zero_le N)
  obtain ⟨f, hf⟩ := kmswWindowEdgeMapInf_range_upper (shiftedStream W N) N
    (hs.symm ▸ h) (kmswPastStageEdge W N e)
    ((kmswPastStageEdge_mem_upper_iff W N e heb).mpr heN)
  refine ⟨f, ?_⟩
  rw [kmswPastEdge_eq_stage W N e heb, ← hf]
  exact (congrFun (wholePlaneEdgeι_trans W 0 N (Nat.zero_le N)) f).symm





theorem kmswPastSeamEdge_image_boundary (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ)
    (he : kmswPastSeamEdge W e) :
    ∃ j : ℤ, kmswPastEdge W e =
      wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h j) := by
  obtain ⟨N, heN⟩ := he
  have heb : e < (kmswStage (kmswPastCode W) N).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge _ N).2
    simp only [List.mem_append] at heN ⊢
    tauto
  have hs : (fun i => shiftedStream W N (N + i)) = shiftedStream W 0 := by
    simpa only [Nat.sub_zero] using shiftedStream_shift W 0 N (Nat.zero_le N)
  obtain ⟨f, m, hm, hf⟩ :=
    kmswWindowEdgeMapInf_range_upper_lower (shiftedStream W N) N (hs.symm ▸ h)
      (kmswPastStageEdge W N e)
      ((kmswPastStageEdge_mem_upper_iff W N e heb).mpr heN)
  rw [hs] at hm
  have hb : f ∈ boundaryOuterEdgeSet (shiftedStream W 0) h := by
    apply m0Cut_lower_mem_boundary (shiftedStream W 0) h m f
    simp only [List.mem_append] at hm
    exact hm.symm
  rw [← boundaryOuterEdge_range] at hb
  obtain ⟨j, hj⟩ := hb
  refine ⟨j, ?_⟩
  rw [kmswPastEdge_eq_stage W N e heb, ← hf, hj]
  exact congrFun (wholePlaneEdgeι_trans W 0 N (Nat.zero_le N)) f




private theorem seam_past_adjacent (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (kmswPastCode W)) (k : ℤ) :
    wholePlaneEdgeWest W (kmswPastEdge W (boundaryOuterEdge (kmswPastCode W) h k)) =
      wholePlaneEdgeEast W
        (kmswPastEdge W (boundaryOuterEdge (kmswPastCode W) h (k + 1))) := by
  rw [kmswPastEdge_west, kmswPastEdge_east,
    (boundaryOuterEdge_endpoints (kmswPastCode W) h k).2.1,
    (boundaryOuterEdge_endpoints (kmswPastCode W) h (k + 1)).1]




private theorem seam_image_index_step (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (k j l : ℤ)
    (hk : kmswPastEdge W (boundaryOuterEdge (kmswPastCode W) hp k) =
      wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h j))
    (hl : kmswPastEdge W (boundaryOuterEdge (kmswPastCode W) hp (k + 1)) =
      wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h l)) :
    j = l + 1 := by
  have ha := seam_past_adjacent W hp k
  rw [hk, hl, wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι,
    (boundaryOuterEdge_endpoints (shiftedStream W 0) h j).1,
    (boundaryOuterEdge_endpoints (shiftedStream W 0) h l).2.1] at ha
  exact boundaryVertex_injective _ h (wholePlaneVertexι_injective W 0 ha)




theorem kmswPastEdge_seam_match_neg (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (k : ℤ) :
    kmswPastEdge W (boundaryOuterEdge (kmswPastCode W) hp k) =
      wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h (-k)) := by
  have hex (j : ℤ) : ∃ l : ℤ,
      kmswPastEdge W (boundaryOuterEdge (kmswPastCode W) hp j) =
        wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h l) := by
    obtain ⟨N, hN⟩ := boundaryOuterEdge_mem_finite_LL_LR (kmswPastCode W) hp j
    exact kmswPastSeamEdge_image_boundary W h _ ⟨N, List.mem_append.mpr hN⟩
  induction k using Int.induction_on with
  | zero =>
    rw [neg_zero, boundaryOuterEdge_zero, boundaryOuterEdge_zero, kmswPastEdge_root]
  | succ n ih =>
    obtain ⟨j, hj⟩ := hex ((n : ℤ) + 1)
    have hi := seam_image_index_step W h hp (n : ℤ) (-(n : ℤ)) j ih hj
    have hj' : j = -((n : ℤ) + 1) := by omega
    rw [hj'] at hj
    exact hj
  | pred n ih =>
    obtain ⟨j, hj⟩ := hex (-(n : ℤ) - 1)
    have hnext : kmswPastEdge W
        (boundaryOuterEdge (kmswPastCode W) hp ((-(n : ℤ) - 1) + 1)) =
        wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h (-(-(n : ℤ)))) := by
      simpa only [sub_add_cancel] using ih
    have hi := seam_image_index_step W h hp (-(n : ℤ) - 1) j (-(-(n : ℤ))) hj hnext
    have hj' : j = -(-(n : ℤ) - 1) := by omega
    rw [hj'] at hj
    exact hj




theorem kmswPastDart_seam_match_neg (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (k : ℤ) :
    kmswPastDart W (boundaryOuterEdge (kmswPastCode W) hp k, false) =
      (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h (-k)), true) := by
  change (kmswPastEdge W (boundaryOuterEdge (kmswPastCode W) hp k), true) = _
  rw [kmswPastEdge_seam_match_neg W h hp k]





theorem kmswPastEdge_mem_runZero_iff (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (e : ℕ) :
    kmswPastEdge W e ∈ Set.range (wholePlaneEdgeι W 0) ↔ kmswPastSeamEdge W e :=
  ⟨kmswPastEdge_inter W e, kmswPastEdge_inter_converse W h e⟩




theorem kmswPastEdge_root_eq_active (W : ℤ → Fin 3) (N : ℕ) :
    kmswPastEdge W 0 = wholePlaneEdgeι W N (kmswStage (shiftedStream W N) N).active := by
  have hb : 0 < (kmswStage (kmswPastCode W) N).nextEdge :=
    (kmswStage_active_lt (kmswPastCode W) 0).trans_le
      (kmswStage_nextEdge_mono _ (Nat.zero_le N))
  rw [kmswPastEdge_eq_stage W N 0 hb]
  change wholePlaneEdgeι W N
    (kmswRevEdge (shiftedStream W N) (kmswPastCode W) N
      (kmswStage (kmswPastCode W) 0).active) = _
  rw [kmswRevEdge_active _ _ N 0 (Nat.zero_le N), Nat.sub_zero]

end DirectedDistances.KMSW
