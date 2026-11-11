module

public import DirectedDistances.KMSW.StageReversalRotation
public import DirectedDistances.KMSW.KMSWWholePlaneColimit
public import DirectedDistances.KMSW.KMSWWholePlaneFaces

import all DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import all DirectedDistances.KMSW.StageReversalRotation
import all DirectedDistances.KMSW.StageReversalEdges

public section
namespace DirectedDistances.KMSW




@[expose] def kmswPastCode (W : ℤ → Fin 3) : ℕ → Fin 3 :=
  fun i => Equiv.swap (0 : Fin 3) 1 (W (-1 - (i : ℤ)))




theorem kmswPastCode_rev (W : ℤ → Fin 3) (N : ℕ) :
    ∀ i < N, kmswPastCode W i =
      Equiv.swap (0 : Fin 3) 1 (shiftedStream W N (N - 1 - i)) := by
  intro i hi
  unfold kmswPastCode shiftedStream
  congr 2
  omega




@[expose] noncomputable def kmswPastStageEdge (W : ℤ → Fin 3) (N : ℕ) : ℕ → ℕ :=
  kmswRevEdge (shiftedStream W N) (kmswPastCode W) N




@[expose] noncomputable def kmswPastStageVertex (W : ℤ → Fin 3) (N : ℕ) : ℕ → ℕ :=
  kmswReversalPhi (kmswPastCode W) (shiftedStream W N) N




theorem kmswWindowEdgeMapInf_active (w : ℕ → Fin 3) (s t : ℕ) :
    kmswWindowEdgeMapInf w s (kmswStage (fun i => w (s + i)) t).active =
      (kmswStage w (s + t)).active := by
  rw [kmswWindowEdgeMapInf_eq_stage w s t _ (kmswStage_active_lt _ t)]
  exact (kmswWindowPatchData_rel w s t).active




theorem kmswPast_active_trans (W : ℤ → Fin 3) (N M t : ℕ) (hNM : N ≤ M) :
    wholePlaneEdgeTrans W N M hNM (kmswStage (shiftedStream W N) t).active =
      (kmswStage (shiftedStream W M) (M - N + t)).active := by
  unfold wholePlaneEdgeTrans
  rw [← shiftedStream_shift W N M hNM]
  exact kmswWindowEdgeMapInf_active _ _ _




theorem kmswPastStageEdge_trans_present (W : ℤ → Fin 3) (N M e : ℕ)
    (hNM : N ≤ M) (he : e < (kmswStage (kmswPastCode W) N).nextEdge)
    (hp : (kmswStage (kmswPastCode W) N).present e = true) :
    wholePlaneEdgeTrans W N M hNM (kmswPastStageEdge W N e) =
      kmswPastStageEdge W M e := by
  obtain ⟨t, ht, rfl⟩ := kmswStage_present_eq_active (kmswPastCode W) N e he hp
  unfold kmswPastStageEdge
  rw [kmswRevEdge_active _ _ N t ht, kmswRevEdge_active _ _ M t (ht.trans hNM),
    kmswPast_active_trans W N M (N - t) hNM]
  rw [show M - N + (N - t) = M - t by omega]




theorem kmswPastStageEdge_colimit_present (W : ℤ → Fin 3) (N M e : ℕ)
    (hNM : N ≤ M) (he : e < (kmswStage (kmswPastCode W) N).nextEdge)
    (hp : (kmswStage (kmswPastCode W) N).present e = true) :
    wholePlaneEdgeι W N (kmswPastStageEdge W N e) =
      wholePlaneEdgeι W M (kmswPastStageEdge W M e) := by
  rw [← kmswPastStageEdge_trans_present W N M e hNM he hp]
  exact (congrFun (wholePlaneEdgeι_trans W N M hNM) _).symm




theorem kmswPast_slot_trans (W : ℤ → Fin 3) (N M t : ℕ) (hNM : N ≤ M) :
    wholePlaneVertexTrans W N M hNM (kmswSlotVertex (shiftedStream W N) (.west t)) =
        kmswSlotVertex (shiftedStream W M) (.west (M - N + t)) ∧
      wholePlaneVertexTrans W N M hNM (kmswSlotVertex (shiftedStream W N) (.east t)) =
        kmswSlotVertex (shiftedStream W M) (.east (M - N + t)) := by
  have hw := wholePlaneEdgeTrans_west W N M hNM (kmswStage (shiftedStream W N) t).active
  have he := wholePlaneEdgeTrans_east W N M hNM (kmswStage (shiftedStream W N) t).active
  rw [kmswPast_active_trans W N M t hNM,
    ← (edge_endpoints_eq _ (kmswStage_active_lt _ _)).1,
    ← (edge_endpoints_eq _ (kmswStage_active_lt _ _)).1] at hw
  rw [kmswPast_active_trans W N M t hNM,
    ← (edge_endpoints_eq _ (kmswStage_active_lt _ _)).2,
    ← (edge_endpoints_eq _ (kmswStage_active_lt _ _)).2] at he
  exact ⟨hw.symm, he.symm⟩




theorem kmswPastStageVertex_trans (W : ℤ → Fin 3) (N M v : ℕ) (hNM : N ≤ M)
    (hv : v < (kmswStage (kmswPastCode W) N).nextVertex) :
    wholePlaneVertexTrans W N M hNM (kmswPastStageVertex W N v) =
      kmswPastStageVertex W M v := by
  obtain ⟨S, hS, rfl⟩ := kmswSlotVertex_surjective (kmswPastCode W) N v hv
  unfold kmswPastStageVertex
  rw [kmswReversalPhi_slot _ _ N (kmswPastCode_rev W N) S hS,
    kmswReversalPhi_slot _ _ M (kmswPastCode_rev W M) S (hS.trans hNM)]
  cases S with
  | west t =>
    change t ≤ N at hS
    simpa only [KMSWSlot.mirror, show M - N + (N - t) = M - t by omega] using
      (kmswPast_slot_trans W N M (N - t) hNM).2
  | east t =>
    change t ≤ N at hS
    simpa only [KMSWSlot.mirror, show M - N + (N - t) = M - t by omega] using
      (kmswPast_slot_trans W N M (N - t) hNM).1




theorem kmswPastStageVertex_colimit (W : ℤ → Fin 3) (N M v : ℕ) (hNM : N ≤ M)
    (hv : v < (kmswStage (kmswPastCode W) N).nextVertex) :
    wholePlaneVertexι W N (kmswPastStageVertex W N v) =
      wholePlaneVertexι W M (kmswPastStageVertex W M v) := by
  rw [← kmswPastStageVertex_trans W N M v hNM hv]
  exact (congrFun (wholePlaneVertexι_trans W N M hNM) _).symm




theorem kmswWindowEdgeMapInf_up_missing (w : ℕ → Fin 3) (s t : ℕ)
    (hc : w (s + t) = 1) :
    kmswWindowEdgeMapInf w s
        ((kmswStage (fun i => w (s + i)) t).nextEdge + 1) =
      (kmswStage w (s + t)).nextEdge + 1 := by
  have hb := (kmswSlot_up_missing_endpoints (fun i => w (s + i)) t hc).2.2
  rw [kmswWindowEdgeMapInf_eq_stage w s (t + 1) _ hb]
  simp [kmswWindowPatchData, KMSWWindowPatchData.step, kmswCodeStep, hc]




theorem kmswPastStageEdge_trans_LL (W : ℤ → Fin 3) (N M e : ℕ) (hNM : N ≤ M)
    (he : e ∈ (kmswStage (kmswPastCode W) N).LL) :
    wholePlaneEdgeTrans W N M hNM (kmswPastStageEdge W N e) =
      kmswPastStageEdge W M e := by
  obtain ⟨t, ht⟩ := kmswStage_LL_exists_revLeftRecord (kmswPastCode W) N e he
  have htM : kmswRevLeftRecord (kmswPastCode W) M e t :=
    ⟨ht.1.trans_le hNM, ht.2⟩
  have hc := (kmswRevLeftRecord_reverse (kmswPastCode W) (shiftedStream W N)
    N e t (kmswPastCode_rev W N) ht).2.1
  unfold kmswPastStageEdge
  rw [kmswRevEdge_left _ _ N e t ht, kmswRevEdge_left _ _ M e t htM]
  unfold wholePlaneEdgeTrans
  rw [← shiftedStream_shift W N M hNM]
  rw [kmswWindowEdgeMapInf_up_missing _ (M - N) (N - 1 - t) (by
    exact (congrFun (shiftedStream_shift W N M hNM) (N - 1 - t)).trans hc)]
  rw [show M - N + (N - 1 - t) = M - 1 - t by have := ht.1; omega]




theorem kmswPastStageEdge_present_iff (W : ℤ → Fin 3) (N e : ℕ)
    (he : e < (kmswStage (kmswPastCode W) N).nextEdge) :
    (kmswStage (shiftedStream W N) N).present (kmswPastStageEdge W N e) = true ↔
      (kmswStage (kmswPastCode W) N).present e = true :=
  kmswRevEdge_present_iff _ _ N (kmswPastCode_rev W N) e he





theorem kmswPastStageEdge_endpoints (W : ℤ → Fin 3) (N e : ℕ)
    (he : e < (kmswStage (kmswPastCode W) N).nextEdge) :
    wholePlaneEdgeWest W (wholePlaneEdgeι W N (kmswPastStageEdge W N e)) =
        wholePlaneVertexι W N (kmswPastStageVertex W N
          ((kmswStage (kmswPastCode W) N).east e)) ∧
      wholePlaneEdgeEast W (wholePlaneEdgeι W N (kmswPastStageEdge W N e)) =
        wholePlaneVertexι W N (kmswPastStageVertex W N
          ((kmswStage (kmswPastCode W) N).west e)) := by
  have hb := kmswRevEdge_mapsTo _ _ N (kmswPastCode_rev W N) he
  have hh := kmswRevEdge_endpoints _ _ N (kmswPastCode_rev W N) e he
  unfold kmswPastStageEdge kmswPastStageVertex
  rw [wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι,
    ← (edge_endpoints_eq _ hb).1, ← (edge_endpoints_eq _ hb).2]
  exact ⟨congrArg (wholePlaneVertexι W N) hh.1,
    congrArg (wholePlaneVertexι W N) hh.2⟩





def KMSWPastMissingEdgeCompatibility (W : ℤ → Fin 3) : Prop :=
  ∀ N e, e < (kmswStage (kmswPastCode W) N).nextEdge →
    (kmswStage (kmswPastCode W) N).present e = false →
    wholePlaneEdgeTrans W N (N + 1) (Nat.le_succ N) (kmswPastStageEdge W N e) =
      kmswPastStageEdge W (N + 1) e




def KMSWPastURCompatibility (W : ℤ → Fin 3) : Prop :=
  ∀ N e, e ∈ (kmswStage (kmswPastCode W) N).UR →
    wholePlaneEdgeTrans W N (N + 1) (Nat.le_succ N) (kmswPastStageEdge W N e) =
      kmswPastStageEdge W (N + 1) e




theorem kmswPastMissingEdgeCompatibility_iff (W : ℤ → Fin 3) :
    KMSWPastMissingEdgeCompatibility W ↔ KMSWPastURCompatibility W := by
  constructor
  · intro h N e he
    have hb : e < (kmswStage (kmswPastCode W) N).nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge _ N).2 e (by
        simp only [List.mem_append]
        tauto)
    exact h N e hb ((kmswStage_missing_iff_UR_or_LL _ N e hb).mpr (Or.inl he))
  · intro h N e he hp
    rcases (kmswStage_missing_iff_UR_or_LL _ N e he).mp hp with hu | hl
    · exact h N e hu
    · exact kmswPastStageEdge_trans_LL W N (N + 1) e (Nat.le_succ N) hl





theorem kmswWindowTriangle_edge_sum (w : ℕ → Fin 3) (s j : ℕ)
    (hc : w (s + j) = 0 ∨ w (s + j) = 1) :
    ((stageTriangleDartList (fun i => w (s + i)) ⟨j, hc⟩).map
      (fun p => kmswWindowEdgeMapInf w s p.1)).sum =
      ((stageTriangleDartList w ⟨s + j, hc⟩).map Prod.fst).sum := by
  have h := (kmswWindowPatchData_triangle_rotated w s (j + 1) j
    (Nat.lt_succ_self j) hc).map Prod.fst
  have hh := h.perm.sum_eq
  simp only [List.map_map, Function.comp_def] at hh
  rw [← hh]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact kmswWindowEdgeMapInf_eq_stage w s (j + 1) p.1
    (stageTriangleDartList_lt _ _ _ (Nat.lt_succ_self j) p hp)




theorem kmswPastStageEdge_triangle_sum_trans (W : ℤ → Fin 3) (N : ℕ)
    (j : TriangleCreationTime (kmswPastCode W)) (hj : j.val < N) :
    ((stageTriangleDartList (kmswPastCode W) j).map (fun p =>
      wholePlaneEdgeTrans W N (N + 1) (Nat.le_succ N)
        (kmswPastStageEdge W N p.1))).sum =
      ((stageTriangleDartList (kmswPastCode W) j).map
        (fun p => kmswPastStageEdge W (N + 1) p.1)).sum := by
  obtain ⟨k, hk, hn⟩ := kmswRevDart_triangle_words (shiftedStream W N)
    (kmswPastCode W) N (kmswPastCode_rev W N) j hj
  obtain ⟨l, hl, hm⟩ := kmswRevDart_triangle_words (shiftedStream W (N + 1))
    (kmswPastCode W) (N + 1) (kmswPastCode_rev W (N + 1)) j (by omega)
  have hn' := (hn.map (fun p => wholePlaneEdgeTrans W N (N + 1)
    (Nat.le_succ N) p.1)).perm.sum_eq
  have hm' := (hm.map Prod.fst).perm.sum_eq
  simp only [List.map_map, Function.comp_def, reversalDartValMap] at hn' hm'
  change _ = ((stageTriangleDartList (shiftedStream W N) k).map
    (fun p => wholePlaneEdgeTrans W N (N + 1) (Nat.le_succ N) p.1)).sum at hn'
  change _ = ((stageTriangleDartList (shiftedStream W (N + 1)) l).map Prod.fst).sum
    at hm'
  change _ = _ at hn' hm'
  change _ = _
  rw [show ((stageTriangleDartList (kmswPastCode W) j).map (fun p =>
    wholePlaneEdgeTrans W N (N + 1) (Nat.le_succ N)
      (kmswPastStageEdge W N p.1))).sum = _ from hn']
  rw [show ((stageTriangleDartList (kmswPastCode W) j).map
    (fun p => kmswPastStageEdge W (N + 1) p.1)).sum = _ from hm']
  have hs := shiftedStream_shift W N (N + 1) (Nat.le_succ N)
  have hs' : (fun i => shiftedStream W (N + 1) (1 + i)) = shiftedStream W N := by
    simpa only [Nat.add_sub_cancel_left] using hs
  have hc : shiftedStream W (N + 1) (1 + k.val) = 0 ∨
      shiftedStream W (N + 1) (1 + k.val) = 1 := by
    rw [congrFun hs' k.val]
    exact k.property
  have hw := kmswWindowTriangle_edge_sum (shiftedStream W (N + 1)) 1 k.val hc
  have heq : (⟨1 + k.val, hc⟩ : TriangleCreationTime (shiftedStream W (N + 1))) =
      l := Subtype.ext (by change 1 + k.val = l.val; omega)
  rw [heq] at hw
  unfold wholePlaneEdgeTrans
  simp only [Nat.add_sub_cancel_left]
  simp only [stageTriangleDartList, stageTriangleDartTriple] at hw ⊢
  simpa only [hs', congrFun hs' k.val] using hw




theorem kmswPastURCompatibility_holds (W : ℤ → Fin 3) :
    KMSWPastURCompatibility W := by
  intro N e he
  obtain ⟨t, ht⟩ := kmswStage_UR_exists_revUpRecord (kmswPastCode W) N e he
  have hs := kmswPastStageEdge_triangle_sum_trans W N ⟨t, Or.inr ht.2.1⟩ ht.1
  have htn : t < N := ht.1
  have hact (r : ℕ) (hr : r ≤ N) :
      wholePlaneEdgeTrans W N (N + 1) (Nat.le_succ N)
        (kmswPastStageEdge W N (kmswStage (kmswPastCode W) r).active) =
      kmswPastStageEdge W (N + 1) (kmswStage (kmswPastCode W) r).active := by
    unfold kmswPastStageEdge
    rw [kmswRevEdge_active _ _ N r hr,
      kmswRevEdge_active _ _ (N + 1) r (by omega),
      kmswPast_active_trans W N (N + 1) (N - r) (Nat.le_succ N)]
    rw [show N + 1 - N + (N - r) = N + 1 - r by omega]
  have ha := hact t (by omega)
  have hb := reversal_triangle_active (kmswPastCode W) t (Or.inr ht.2.1)
  have hb' := hact (t + 1) (by omega)
  rw [hb] at hb'
  simp only [stageTriangleDartList, stageTriangleDartTriple, ht.2.1, show
    ¬(1 : Fin 3) = 0 by decide, ↓reduceIte, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero] at hs
  rw [ha, hb'] at hs
  rw [ht.2.2.2]
  omega




theorem kmswPastMissingEdgeCompatibility_holds (W : ℤ → Fin 3) :
    KMSWPastMissingEdgeCompatibility W :=
  (kmswPastMissingEdgeCompatibility_iff W).mpr (kmswPastURCompatibility_holds W)




theorem kmswPastStageEdge_trans (W : ℤ → Fin 3) (N M e : ℕ) (hNM : N ≤ M)
    (he : e < (kmswStage (kmswPastCode W) N).nextEdge) :
    wholePlaneEdgeTrans W N M hNM (kmswPastStageEdge W N e) =
      kmswPastStageEdge W M e := by
  induction M, hNM using Nat.le_induction with
  | base => rw [wholePlaneEdgeTrans_self]; rfl
  | succ M hNM ih =>
    rw [← congrFun (wholePlaneEdgeTrans_comp W N M (M + 1) hNM (Nat.le_succ M))
      (kmswPastStageEdge W N e)]
    change wholePlaneEdgeTrans W M (M + 1) (Nat.le_succ M)
      (wholePlaneEdgeTrans W N M hNM (kmswPastStageEdge W N e)) = _
    rw [ih]
    have hb := he.trans_le (kmswStage_nextEdge_mono (kmswPastCode W) hNM)
    cases hp : (kmswStage (kmswPastCode W) M).present e with
    | false => exact kmswPastMissingEdgeCompatibility_holds W M e hb hp
    | true =>
      exact kmswPastStageEdge_trans_present W M (M + 1) e (Nat.le_succ M) hb hp




theorem kmswPastStageEdge_colimit (W : ℤ → Fin 3) (N M e : ℕ) (hNM : N ≤ M)
    (he : e < (kmswStage (kmswPastCode W) N).nextEdge) :
    wholePlaneEdgeι W N (kmswPastStageEdge W N e) =
      wholePlaneEdgeι W M (kmswPastStageEdge W M e) := by
  rw [← kmswPastStageEdge_trans W N M e hNM he]
  exact (congrFun (wholePlaneEdgeι_trans W N M hNM) _).symm




@[expose] noncomputable def kmswPastEdge (W : ℤ → Fin 3) (e : ℕ) : WholePlaneEdge W :=
  wholePlaneEdgeι W e (kmswPastStageEdge W e e)




theorem kmswPastEdge_eq_stage (W : ℤ → Fin 3) (N e : ℕ)
    (he : e < (kmswStage (kmswPastCode W) N).nextEdge) :
    kmswPastEdge W e = wholePlaneEdgeι W N (kmswPastStageEdge W N e) := by
  unfold kmswPastEdge
  exact (kmswPastStageEdge_colimit W e (max e N) e (Nat.le_max_left _ _)
    (kmsw_edge_allocated_by_self _ e)).trans
      (kmswPastStageEdge_colimit W N (max e N) e (Nat.le_max_right _ _) he).symm




theorem kmswPastEdge_injective (W : ℤ → Fin 3) : Function.Injective (kmswPastEdge W) := by
  intro e f hef
  have he := kmsw_nextEdge_unbounded (kmswPastCode W) e (max e f) (Nat.le_max_left _ _)
  have hf := kmsw_nextEdge_unbounded (kmswPastCode W) f (max e f) (Nat.le_max_right _ _)
  rw [kmswPastEdge_eq_stage W (max e f) e he,
    kmswPastEdge_eq_stage W (max e f) f hf] at hef
  exact (kmswRevEdge_bijOn _ _ (max e f) (kmswPastCode_rev W (max e f))).injOn he hf
    (wholePlaneEdgeι_injective W (max e f) hef)




@[expose] noncomputable def kmswPastVertex (W : ℤ → Fin 3) (v : ℕ) : WholePlaneVertex W :=
  wholePlaneVertexι W (4 * v + 1) (kmswPastStageVertex W (4 * v + 1) v)




theorem kmswPastVertex_eq_stage (W : ℤ → Fin 3) (N v : ℕ)
    (hv : v < (kmswStage (kmswPastCode W) N).nextVertex) :
    kmswPastVertex W v = wholePlaneVertexι W N (kmswPastStageVertex W N v) := by
  unfold kmswPastVertex
  exact (kmswPastStageVertex_colimit W (4 * v + 1) (max (4 * v + 1) N) v
    (Nat.le_max_left _ _) (vertex_allocated_at _ v)).trans
      (kmswPastStageVertex_colimit W N (max (4 * v + 1) N) v
        (Nat.le_max_right _ _) hv).symm




theorem kmswPastEdge_endpoints (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgeWest W (kmswPastEdge W e) =
        kmswPastVertex W (edgeEast (kmswPastCode W) e) ∧
      wholePlaneEdgeEast W (kmswPastEdge W e) =
        kmswPastVertex W (edgeWest (kmswPastCode W) e) := by
  have he := kmsw_edge_allocated_by_self (kmswPastCode W) e
  have hv := kmswStage_endpoints_lt_nextVertex (kmswPastCode W) e e he
  have hh := kmswPastStageEdge_endpoints W e e he
  rw [(edge_endpoints_eq _ he).1, (edge_endpoints_eq _ he).2] at hv hh
  rw [kmswPastEdge_eq_stage W e e he,
    kmswPastVertex_eq_stage W e _ hv.2, kmswPastVertex_eq_stage W e _ hv.1]
  exact hh




@[expose] noncomputable def kmswPastDart (W : ℤ → Fin 3) (d : ℕ × Bool) :
    WholePlaneDart W := (kmswPastEdge W d.1, !d.2)




theorem kmswPastDart_eq_stage (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool)
    (hd : d.1 < (kmswStage (kmswPastCode W) N).nextEdge) :
    kmswPastDart W d = (wholePlaneEdgeι W N (kmswPastStageEdge W N d.1), !d.2) := by
  unfold kmswPastDart
  rw [kmswPastEdge_eq_stage W N d.1 hd]




theorem kmswPastDart_injective (W : ℤ → Fin 3) : Function.Injective (kmswPastDart W) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  have he := kmswPastEdge_injective W (congrArg Prod.fst h)
  have hb : (!b) = (!c) := congrArg Prod.snd h
  exact Prod.ext he (by cases b <;> cases c <;> simp_all)




theorem kmswPastEdge_present_iff (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgePresent W (kmswPastEdge W e) ↔
      ∃ M, e ≤ M ∧ ∀ L, M ≤ L →
        EdgePresent (shiftedStream W L) (kmswPastStageEdge W L e) := by
  rw [kmswPastEdge_eq_stage W e e (kmsw_edge_allocated_by_self _ e),
    wholePlaneEdgePresent_ι]
  constructor
  · rintro ⟨M, heM, hp⟩
    refine ⟨M, heM, fun L hML => ?_⟩
    have hh := hp L hML
    rwa [kmswPastStageEdge_trans W e L e (heM.trans hML)
      (kmsw_edge_allocated_by_self _ e)] at hh
  · rintro ⟨M, heM, hp⟩
    refine ⟨M, heM, fun L hML => ?_⟩
    rw [kmswPastStageEdge_trans W e L e (heM.trans hML)
      (kmsw_edge_allocated_by_self _ e)]
    exact hp L hML




theorem kmswPastEdge_present (W : ℤ → Fin 3) (e : ℕ)
    (hp : EdgePresent (kmswPastCode W) e) :
    wholePlaneEdgePresent W (kmswPastEdge W e) := by
  obtain ⟨N, hN⟩ := hp.eventually_present
  apply (kmswPastEdge_present_iff W e).mpr
  refine ⟨max e N, Nat.le_max_left _ _, fun L hL => ?_⟩
  have hh := hN L ((Nat.le_max_right _ _).trans hL)
  exact ⟨L, kmswRevEdge_mapsTo _ _ L (kmswPastCode_rev W L) hh.1,
    (kmswPastStageEdge_present_iff W L e hh.1).mpr hh.2⟩




private theorem past_window_present (w : ℕ → Fin 3) (s e : ℕ)
    (hp : EdgePresent (fun i => w (s + i)) e) :
    EdgePresent w (kmswWindowEdgeMapInf w s e) := by
  obtain ⟨n, he, hp⟩ := hp
  rw [kmswWindowEdgeMapInf_eq_stage w s n e he]
  exact ⟨s + n, (kmswWindowPatchData_rel w s n).edge_bound e he,
    (kmswWindowPatchData_rel w s n).present e he hp⟩




private theorem past_colimit_present (W : ℤ → Fin 3) (N e : ℕ)
    (hp : EdgePresent (shiftedStream W N) e) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := by
  rw [wholePlaneEdgePresent_ι]
  refine ⟨N, le_refl N, fun M hNM => ?_⟩
  unfold wholePlaneEdgeTrans
  apply past_window_present
  rwa [shiftedStream_shift W N M hNM]




theorem kmswPastEdge_present_iff_exists_stage (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgePresent W (kmswPastEdge W e) ↔
      ∃ N, e < (kmswStage (kmswPastCode W) N).nextEdge ∧
        EdgePresent (shiftedStream W N) (kmswPastStageEdge W N e) := by
  constructor
  · intro hp
    obtain ⟨M, heM, hp⟩ := (kmswPastEdge_present_iff W e).mp hp
    exact ⟨M, (kmsw_edge_allocated_by_self _ e).trans_le
      (kmswStage_nextEdge_mono _ heM), hp M le_rfl⟩
  · rintro ⟨N, he, hp⟩
    rw [kmswPastEdge_eq_stage W N e he]
    exact past_colimit_present W N _ hp




private theorem past_LL_not_present (w : ℕ → Fin 3) (N e : ℕ)
    (he : e ∈ (kmswStage w N).LL) : ¬ EdgePresent w e := by
  intro hp
  obtain ⟨t, ht⟩ := kmswStage_LL_exists_revLeftRecord w N e he
  obtain ⟨M, hM⟩ := hp.eventually_present
  have hrec : kmswRevLeftRecord w (max N M) e t :=
    ⟨ht.1.trans_le (Nat.le_max_left _ _), ht.2⟩
  exact kmswStage_UR_LL_not_present w (max N M) e
    (Or.inr (kmswRevLeftRecord_mem_LL w (max N M) e t hrec))
    (hM (max N M) (Nat.le_max_right _ _)).2




theorem kmswPastEdge_present_iff_present_or_LL (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgePresent W (kmswPastEdge W e) ↔
      EdgePresent (kmswPastCode W) e ∨
        ∃ N, e ∈ (kmswStage (kmswPastCode W) N).LL ∧
          EdgePresent (shiftedStream W N) (kmswPastStageEdge W N e) := by
  constructor
  · intro hp
    obtain ⟨N, he, hp⟩ := (kmswPastEdge_present_iff_exists_stage W e).mp hp
    cases hh : (kmswStage (kmswPastCode W) N).present e with
    | true => exact Or.inl ⟨N, he, hh⟩
    | false =>
      rcases (kmswStage_missing_iff_UR_or_LL _ N e he).mp hh with hu | hl
      · obtain ⟨t, ht⟩ := kmswStage_UR_exists_revUpRecord (kmswPastCode W) N e hu
        have hr := kmswRevUpRecord_reverse (kmswPastCode W) (shiftedStream W N)
          N e t (kmswPastCode_rev W N) ht
        have hm := kmswRevLeftRecord_mem_LL (shiftedStream W N) N _ _ hr
        have hv := kmswRevEdge_up (shiftedStream W N) (kmswPastCode W) N e t ht
        change kmswPastStageEdge W N e = _ at hv
        rw [← hv] at hm
        exact (past_LL_not_present _ N _ hm hp).elim
      · exact Or.inr ⟨N, hl, hp⟩
  · rintro (hp | ⟨N, he, hp⟩)
    · exact kmswPastEdge_present W e hp
    · apply (kmswPastEdge_present_iff_exists_stage W e).mpr
      refine ⟨N, ?_, hp⟩
      apply (kmswStage_boundary_ids_lt_nextEdge _ N).2
      simp only [List.mem_append]
      tauto




theorem kmswPastVertex_injective (W : ℤ → Fin 3) :
    Function.Injective (kmswPastVertex W) := by
  intro v z hvz
  let N := max (4 * v + 1) (4 * z + 1)
  have hv : v < (kmswStage (kmswPastCode W) N).nextVertex :=
    (vertex_allocated_at _ v).trans_le (CutConverse.nextVertex_mono _
      (Nat.le_max_left _ _))
  have hz : z < (kmswStage (kmswPastCode W) N).nextVertex :=
    (vertex_allocated_at _ z).trans_le (CutConverse.nextVertex_mono _
      (Nat.le_max_right _ _))
  rw [kmswPastVertex_eq_stage W N v hv, kmswPastVertex_eq_stage W N z hz] at hvz
  have hh := wholePlaneVertexι_injective W N hvz
  have hi := congrArg (kmswReversalPhi (shiftedStream W N) (kmswPastCode W) N) hh
  change kmswReversalPhi _ _ N (kmswReversalPhi _ _ N v) =
    kmswReversalPhi _ _ N (kmswReversalPhi _ _ N z) at hi
  rwa [kmswReversalPhi_inverse _ _ N (kmswPastCode_rev W N) v hv,
    kmswReversalPhi_inverse _ _ N (kmswPastCode_rev W N) z hz] at hi




theorem kmswPastEdge_west (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgeWest W (kmswPastEdge W e) =
      kmswPastVertex W (edgeEast (kmswPastCode W) e) :=
  (kmswPastEdge_endpoints W e).1




theorem kmswPastEdge_east (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgeEast W (kmswPastEdge W e) =
      kmswPastVertex W (edgeWest (kmswPastCode W) e) :=
  (kmswPastEdge_endpoints W e).2

end DirectedDistances.KMSW
