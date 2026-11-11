module

public import DirectedDistances.KMSW.StageInfiniteOutgoingOrderEq
public import DirectedDistances.KMSW.StageInfiniteOutgoingOrder

/-! infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result.

The upper-left head can change before the first permanent left record. Its
agreement with the infinite left boundary starts exactly at that record time.
The filtered infinite outgoing order nevertheless starts at the finite stage
head at every stage. The final theorem supplies the outgoing-order hypothesis
of `PastLeftmostEqGeodesicPrefix` at stage `t - 1`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open scoped Classical

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageULHeadDart_eventually_eq_leftBoundary (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) :
    ∃ N, ∀ n ≥ N, (stageULHeadDart w n).1.val = kmswLeftBoundaryEdge w 0 := by
  obtain ⟨N, hN⟩ := kmswStage_UL_getElem?_eventually w htrans 0
  refine ⟨N, fun n hn => ?_⟩
  have hh : (kmswStage w n).UL.head? = some (kmswLeftBoundaryEdge w 0) := by
    simpa only [List.head?_eq_getElem?] using hN n hn
  have he := List.head?_eq_some_head (kmswStage_UL_nonempty_active_last w n).1
  rw [hh] at he
  exact (Option.some.inj he).symm

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageULHeadDart_not_constant_of_first_up (w : ℕ → Fin 3) (hw : w 0 = 1) :
    ¬ ∀ n, (stageULHeadDart w n).1.val = kmswLeftBoundaryEdge w 0 := by
  intro h
  have he := (h 0).trans (h 1).symm
  have hzero : (stageULHeadDart w 0).1.val = 0 := rfl
  have hone : (stageULHeadDart w 1).1.val = 1 := by
    simp [stageULHeadDart, kmswStage, hw, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge]
  rw [hzero, hone] at he
  contradiction

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem first_left_record_level_zero (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) :
    L w (natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) 0) = 0 := by
  classical
  let Q := fun m => ∀ j, m < j → L w m + 1 ≤ L w j
  let m := natSelect Q 0
  obtain ⟨hm, hcount⟩ := natSelect_spec (left_record_infinite w htrans) 0
  change Q m at hm
  change Nat.count Q m = 0 at hcount
  have hzero : L w 0 = 0 := by simp only [L, Finset.range_zero, Finset.sum_empty]
  let r := Nat.findGreatest (fun j => L w j = 0) m
  have hr : L w r = 0 :=
    Nat.findGreatest_spec (P := fun j => L w j = 0) (Nat.zero_le m) hzero
  have hrm : r ≤ m := Nat.findGreatest_le m
  by_contra hne
  have hpos : 0 < L w m := lt_of_le_of_ne (hL m) (Ne.symm hne)
  have hrlt : r < m := by
    by_contra hn
    have he : r = m := by omega
    rw [he] at hr
    omega
  have hQr : Q r := by
    intro j hj
    rw [hr]
    by_cases hjm : j ≤ m
    · have hn : L w j ≠ 0 := Nat.findGreatest_is_greatest hj hjm
      have hnonneg := hL j
      omega
    · have hrec := hm j (by omega)
      omega
  have hmono : Nat.count Q (r + 1) ≤ Nat.count Q m :=
    Nat.count_monotone (p := Q) (by omega)
  rw [Nat.count_succ, ite_eq_left hQr, hcount] at hmono
  omega

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageULHeadDart_eq_leftBoundary_iff_first_record_le (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) (n : ℕ) :
    (stageULHeadDart w n).1.val = kmswLeftBoundaryEdge w 0 ↔
      natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) 0 ≤ n := by
  classical
  let Q := fun m => ∀ j, m < j → L w m + 1 ≤ L w j
  let m := natSelect Q 0
  have hm : Q m := (natSelect_spec (left_record_infinite w htrans) 0).1
  have hmzero : L w m = 0 := first_left_record_level_zero w hL htrans
  constructor
  · intro he
    have hmem : (stageULHeadDart w n).1.val ∈ (kmswStage w n).UL :=
      List.head_mem (kmswStage_UL_nonempty_active_last w n).1
    rw [he, kmswStage_UL_eq] at hmem
    obtain ⟨k, hk, heq⟩ := List.mem_map.mp hmem
    have hkn : k ≤ n := by
      have := List.mem_range.mp (List.mem_filter.mp hk).1
      omega
    have hkm : k = m := CutConverse.act_injective w heq
    change m ≤ n
    omega
  · intro hmn
    have hag (k : ℕ) (hkm : k ≤ m) :
        decide (∀ j, k < j → j ≤ n → L w k + 1 ≤ L w j) = true ↔ Q k := by
      rw [decide_eq_true_iff]
      constructor
      · intro hk
        by_cases heq : k = m
        · exact heq.symm ▸ hm
        · have hbad := hk m (by omega) hmn
          have hnonneg := hL k
          omega
      · intro hk j hj _
        exact hk j hj
    have hh := filter_range_getElem?_select (left_record_infinite w htrans)
      (fun k => decide (∀ j, k < j → j ≤ n → L w k + 1 ≤ L w j)) 0 n hmn hag
    have hu : (kmswStage w n).UL[0]? = some (kmswLeftBoundaryEdge w 0) := by
      rw [kmswStage_UL_eq, List.getElem?_map, hh]
      rfl
    have hhead := List.head?_eq_some_head (kmswStage_UL_nonempty_active_last w n).1
    rw [List.head?_eq_getElem?, hu] at hhead
    exact (Option.some.inj hhead).symm

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem stageLR_head_zero (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.head? = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.head? = _
    cases kmswCodeStep (w n) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w n).LR ++ [(kmswStage w n).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w n)] using ih

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem source_endpoint (w : ℕ → Fin 3) (hL : ∀ j, 0 ≤ L w j) (n : ℕ) :
    stageEndpoint (kmswStage w n) (stageULHeadDart w n) = 0 := by
  change (kmswStage w n).west ((kmswStage w n).UL.head _) = 0
  have hs := (kmswStage_boundary_chain_invariant w n).2.2.1
  have hUL := (kmswStage_UL_nonempty_active_last w n).1
  rw [kmswStage_LL_eq_nil w hL n, List.nil_append] at hs
  change (((kmswStage w n).UL ++ (kmswStage w n).UR).head?.map
    (kmswStage w n).west) = (kmswStage w n).LR.head?.map (kmswStage w n).west at hs
  rw [List.head?_append_of_ne_nil _ hUL, List.head?_eq_some_head hUL,
    stageLR_head_zero, Option.map_some, Option.map_some] at hs
  exact (Option.some.inj hs).trans (initial_edge_endpoints w n).1

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem source_outer_corner (w : ℕ → Fin 3) (hL : ∀ j, 0 ≤ L w j)
    (n : ℕ) :
    (stageRot w n (stageULHeadDart w n)).1.val = 0 ∧
      (stageRot w n (stageULHeadDart w n)).2 = false := by
  have hLL := kmswStage_LL_eq_nil w hL n
  have hu : (kmswStage w n).UL[0]? = some (stageULHeadDart w n).1.val := by
    simpa only [← List.head?_eq_getElem?, stageULHeadDart] using
      List.head?_eq_some_head (kmswStage_UL_nonempty_active_last w n).1
  have hr : (kmswStage w n).LR[0]? = some 0 := by
    simpa only [← List.head?_eq_getElem?] using stageLR_head_zero w n
  have v1 := outerWordVal_getElem?_UL w n 0 _ hu
  have v2 := outerWordVal_getElem?_LR w n 0 _ hLL hr
  have hlen := outerWordVal_length w n hLL
  have hp := (List.getElem?_eq_some_iff.mp v2).1
  obtain ⟨d, d', hd, hd', hf⟩ :=
    outer_faceSucc_exists w n (stageOuterWord_faceSucc w n) _ hp
  have hmod : ((kmswStage w n).UL.length + (kmswStage w n).UR.length +
      ((kmswStage w n).LR.length - 1 - 0) + 1) % (stageOuterWordVal w n).length = 0 := by
    have hpos := (List.getElem?_eq_some_iff.mp hr).1
    have he : (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        ((kmswStage w n).LR.length - 1 - 0) + 1 = (stageOuterWordVal w n).length := by
      omega
    rw [he, Nat.mod_self]
  rw [hmod, v1] at hd'
  rw [v2] at hd
  have hv := Option.some.inj hd
  have hv' := Option.some.inj hd'
  have he : d' = stageULHeadDart w n :=
    Prod.ext (Fin.ext (congrArg Prod.fst hv').symm) (congrArg Prod.snd hv').symm
  rw [he] at hf
  change (stageRot w n).symm (edgeFlip _ d) = stageULHeadDart w n at hf
  have hrot := (stageRot w n).symm_apply_eq.mp hf
  rw [← hrot]
  exact ⟨(congrArg Prod.fst hv).symm, by
    change Bool.not d.2 = false
    rw [← congrArg Prod.snd hv]
    rfl⟩

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem source_cut_head (w : ℕ → Fin 3) (hL : ∀ j, 0 ≤ L w j) (n : ℕ)
    (xs : List (ℕ × Bool)) (hnd : xs.Nodup)
    (hc : xs.IsChain (fun a b => ∃ da db : StageDart (kmswStage w n).nextEdge,
      (da.1.val, da.2) = a ∧ (db.1.val, db.2) = b ∧ (stageRot w n).symm da = db))
    (ht : xs.getLast? = some (0, false))
    (hm : ((stageULHeadDart w n).1.val, false) ∈ xs) :
    xs.head? = some ((stageULHeadDart w n).1.val, false) := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hm
  | cons a xs ih =>
    by_cases ha : a = ((stageULHeadDart w n).1.val, false)
    · simp only [List.head?_cons, ha]
    · have hmt : ((stageULHeadDart w n).1.val, false) ∈ xs :=
        (List.mem_cons.mp hm).resolve_left (fun h => ha h.symm)
      have hne : xs ≠ [] := List.ne_nil_of_mem hmt
      rw [List.getLast?_cons_of_ne_nil hne] at ht
      have hh := ih hnd.of_cons hc.tail ht hmt
      obtain ⟨da, db, hda, hdb, hrot⟩ := hc.rel_head? hh
      have heq : db = stageULHeadDart w n := Prod.ext
        (Fin.ext (congrArg (fun d : ℕ × Bool => d.1) hdb))
        (congrArg (fun d : ℕ × Bool => d.2) hdb)
      rw [heq] at hrot
      have hr : da = stageRot w n (stageULHeadDart w n) :=
        (stageRot w n).symm_apply_eq.mp hrot
      have haroot : a = (0, false) := by
        rw [← hda, hr]
        exact Prod.ext (source_outer_corner w hL n).1 (source_outer_corner w hL n).2
      exact ((List.nodup_cons.mp hnd).1 (haroot ▸ List.mem_of_getLast? ht)).elim

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem infinite_outgoing_old_head_source (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ) :
    ((kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
      (stageEndpoint (kmswStage w n) (stageULHeadDart w n))
      ⟨n, stageEndpoint_lt_nextVertex w n (stageULHeadDart w n)⟩).filter
        (fun e => decide (e < (kmswStage w n).nextEdge))).head? =
      some (stageULHeadDart w n).1.val := by
  let corner := stageULHeadDart w n
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
    (stageEndpoint (kmswStage w n) corner) ⟨n, stageEndpoint_lt_nextVertex w n corner⟩
  have hs : stageEndpoint (kmswStage w n) corner = 0 := source_endpoint w hL n
  have hnd : es.Nodup := by
    unfold es kmswOutgoingEdgesLeftToRight
    simp only [hs, ↓reduceDIte]
    exact List.nodup_reverse.mpr
      (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.1
  have hlast : es.getLast? = some 0 := by
    unfold es kmswOutgoingEdgesLeftToRight
    simp only [hs, ↓reduceDIte, List.getLast?_reverse]
    rw [(kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.2.1,
      kmswRightBoundaryEdge_zero]
  have hchain : (es.map (fun e => (e, false))).IsChain
      (fun a b => (kmswInfRot w hfin).symm a = b) := by
    rw [List.isChain_map]
    unfold es kmswOutgoingEdgesLeftToRight
    simp only [hs, ↓reduceDIte]
    rw [List.isChain_reverse]
    have hc := (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.2.2.2.2
    exact hc.imp (fun a b hab => (kmswInfRot w hfin).symm_apply_eq.mpr hab.symm)
  have hc := stage_inverse_filter_isChain w hfin n _ hchain
  have hxnd : ((es.map (fun e => (e, false))).filter
      (fun d => decide (d.1 < (kmswStage w n).nextEdge))).Nodup :=
    (hnd.map (by intro a b hab; exact congrArg Prod.fst hab)).filter _
  have hxt : ((es.map (fun e => (e, false))).filter
      (fun d => decide (d.1 < (kmswStage w n).nextEdge))).getLast? = some (0, false) := by
    obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [he, List.map_append, List.filter_append]
    simp only [List.map_cons, List.map_nil, List.filter_cons,
      decide_eq_true (initial_edge_present w n).1, ↓reduceIte, List.filter_nil]
    simp
  have hv : edgeWest w corner.1.val = stageEndpoint (kmswStage w n) corner := by
    simp only [stageEndpoint, show corner.2 = false from rfl,
      Bool.false_eq_true, ↓reduceIte, (edge_endpoints_eq w corner.1.isLt).1]
  have hem : corner.1.val ∈ es := (mem_kmswOutgoingEdgesLeftToRight w hfin hL
    htrans hR _ _ _).mpr ⟨edgePresent_of_nonneg_of_unbounded w hL hR _, hv⟩
  have hh := source_cut_head w hL n _ hxnd hc hxt (by
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨corner.1.val, hem, rfl⟩,
      decide_eq_true corner.1.isLt⟩)
  rw [List.filter_map, List.head?_map] at hh
  change Option.map (fun e => (e, false))
    ((es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head?) =
      some (corner.1.val, false) at hh
  change ((es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head?) = _
  cases he : (es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head? with
  | none => simp only [he, Option.map_none, reduceCtorEq] at hh
  | some e =>
    simp only [he, Option.map_some, Option.some.injEq] at hh
    exact congrArg some (congrArg (fun d : ℕ × Bool => d.1) hh)

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem infinite_outgoing_inverse_chain (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    ((kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv).map
      (fun e => (e, false))).IsChain (fun a b => (kmswInfRot w hfin).symm a = b) := by
  rw [List.isChain_map]
  unfold kmswOutgoingEdgesLeftToRight
  split
  · rw [List.isChain_reverse]
    have hc := (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.2.2.2.2
    exact hc.imp (fun a b hab => (kmswInfRot w hfin).symm_apply_eq.mpr hab.symm)
  · rename_i hn
    rw [List.isChain_reverse]
    have hen := kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv hn
    have hc := hen.choose_spec.choose_spec.choose_spec.2.2.2.2.1
    exact hc.imp (fun a b hab => (kmswInfRot w hfin).symm_apply_eq.mpr hab.symm)

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem old_outgoing_stage_list (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge) (hd : corner.2 = false)
    (hh : ((kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
      (stageEndpoint (kmswStage w n) corner)
      ⟨n, stageEndpoint_lt_nextVertex w n corner⟩).filter
        (fun e => decide (e < (kmswStage w n).nextEdge))).head? = some corner.1.val) :
    ∃ ys : List (StageDart (kmswStage w n).nextEdge), ys.Nodup ∧
      ys.head? = some corner ∧ ys.IsChain (fun a b => (stageRot w n).symm a = b) ∧
      (∀ d, d ∈ ys ↔ d.2 = false ∧
        stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) corner) ∧
      ys.map (fun d => d.1.val) =
        (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
          (stageEndpoint (kmswStage w n) corner)
          ⟨n, stageEndpoint_lt_nextVertex w n corner⟩).filter
            (fun e => decide (e < (kmswStage w n).nextEdge)) := by
  classical
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
    (stageEndpoint (kmswStage w n) corner) ⟨n, stageEndpoint_lt_nextVertex w n corner⟩
  let xs := (es.map (fun e => (e, false))).filter
    (fun d => decide (d.1 < (kmswStage w n).nextEdge))
  let C : (ℕ × Bool) → StageDart (kmswStage w n).nextEdge := fun d =>
    if h : d.1 < (kmswStage w n).nextEdge then (⟨d.1, h⟩, d.2) else corner
  have hC (d : StageDart (kmswStage w n).nextEdge) : C (d.1.val, d.2) = d := by
    simp only [C, dite_eq_left d.1.isLt]
  have hx (d : ℕ × Bool) (hm : d ∈ xs) : d.1 < (kmswStage w n).nextEdge :=
    of_decide_eq_true (List.mem_filter.mp hm).2
  have hCx (d : ℕ × Bool) (hm : d ∈ xs) : ((C d).1.val, (C d).2) = d := by
    simp only [C, dite_eq_left (hx d hm)]
  have hnd : es.Nodup := by
    unfold es kmswOutgoingEdgesLeftToRight
    split
    · exact List.nodup_reverse.mpr
        (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.1
    · rename_i hn
      have hen := kmsw_nonzero_outgoing_enumeration w hfin hL hR _
        ⟨n, stageEndpoint_lt_nextVertex w n corner⟩ hn
      exact List.nodup_reverse.mpr
        hen.choose_spec.choose_spec.choose_spec.1
  have hnx : xs.Nodup := (hnd.map (by
    intro a b hab
    exact congrArg (fun d : ℕ × Bool => d.1) hab)).filter _
  have hc := stage_inverse_filter_isChain w hfin n (es.map (fun e => (e, false)))
    (infinite_outgoing_inverse_chain w hfin hL htrans hR _ _)
  refine ⟨xs.map C, ?_, ?_, ?_, ?_, ?_⟩
  · apply hnx.map_on
    intro a ha b hb heq
    exact (hCx a ha).symm.trans ((congrArg (fun d => (d.1.val, d.2)) heq).trans
      (hCx b hb))
  · rw [List.head?_map]
    have hhead : xs.head? = some (corner.1.val, corner.2) := by
      change ((es.map (fun e => (e, false))).filter
        (fun d => decide (d.1 < (kmswStage w n).nextEdge))).head? = _
      rw [List.filter_map, List.head?_map]
      change Option.map (fun e => (e, false))
        ((es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head?) = _
      rw [hh, Option.map_some, hd]
    rw [hhead, Option.map_some, hC]
  · rw [List.isChain_map]
    exact hc.imp (by
      rintro a b ⟨da, db, hda, hdb, hrot⟩
      rw [← hda, ← hdb, hC, hC]
      exact hrot)
  · intro d
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_filter.mp ha).1
      have hav : edgeWest w a.1 = stageEndpoint (kmswStage w n) corner := by
        rw [← heq]
        exact ((mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR _ _ e).mp he).2
      have hab : a.2 = false := congrArg (fun d : ℕ × Bool => d.2) heq.symm
      have hb : (C a).2 = false :=
        (congrArg (fun d : ℕ × Bool => d.2) (hCx a ha)).trans hab
      have he : (C a).1.val = a.1 := congrArg (fun d : ℕ × Bool => d.1) (hCx a ha)
      refine ⟨hb, ?_⟩
      calc
        stageEndpoint (kmswStage w n) (C a) = edgeWest w a.1 := by
          simp only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte]
          rw [(edge_endpoints_eq w (C a).1.isLt).1, he]
        _ = _ := hav
    · rintro ⟨hb, hv⟩
      have hw : edgeWest w d.1.val = stageEndpoint (kmswStage w n) corner := by
        simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte,
          (edge_endpoints_eq w d.1.isLt).1] using hv
      refine ⟨(d.1.val, d.2), ?_, hC d⟩
      apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨d.1.val, ?_, Prod.ext rfl hb.symm⟩, ?_⟩
      · exact (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR _ _ _).mpr
          ⟨edgePresent_of_nonneg_of_unbounded w hL hR _, hw⟩
      · simpa only [decide_eq_true_eq] using d.1.isLt
  · rw [List.map_map]
    change xs.map (fun d => (C d).1.val) = _
    have heq : xs.map (fun d => (C d).1.val) = xs.map Prod.fst := by
      apply List.map_congr_left
      intro d hd
      exact congrArg (fun a : ℕ × Bool => a.1) (hCx d hd)
    rw [heq]
    simp [xs, List.filter_map, List.map_map, Function.comp_def, es]

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageOutgoingEdgeOrder_eq_infinite_filter_source (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ) :
    stageOutgoingEdgeOrder w n (stageULHeadDart w n) =
      (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
        (stageEndpoint (kmswStage w n) (stageULHeadDart w n))
        ⟨n, stageEndpoint_lt_nextVertex w n (stageULHeadDart w n)⟩).filter
          (fun e => decide (e < (kmswStage w n).nextEdge ∧
            (kmswStage w n).present e = true)) := by
  classical
  obtain ⟨ys, hnd, hh, hc, hm, he⟩ := old_outgoing_stage_list w hfin hL htrans hR n
    (stageULHeadDart w n) rfl (infinite_outgoing_old_head_source w hfin hL htrans hR n)
  let τ : Equiv.Perm (StageDart (kmswStage w n).nextEdge) := (stageRot w n).symm
  let N := orderOf τ
  let raw := List.iterate (τ : StageDart (kmswStage w n).nextEdge → _) (stageULHeadDart w n) N
  let P : StageDart (kmswStage w n).nextEdge → Bool := fun d =>
    decide (stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) (stageULHeadDart w n) ∧
      d.2 = false)
  let Q : StageDart (kmswStage w n).nextEdge → Bool := fun d =>
    decide ((kmswStage w n).present d.1.val = true)
  have hmem (d : StageDart (kmswStage w n).nextEdge) :
      d ∈ ys ↔ d ∈ raw ∧ P d = true := by
    rw [hm]
    constructor
    · rintro ⟨hb, hv⟩
      have hcycle := Equiv.Perm.sameCycle_inv.mpr
        ((stageRot_sameCycle_iff_endpoint_eq w n (stageULHeadDart w n) d).mpr hv.symm)
      obtain ⟨i, hi, hp⟩ := hcycle.exists_pow_eq'
      refine ⟨List.mem_iterate.mpr ⟨i, hi, ?_⟩, ?_⟩
      · simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_inv, τ] using hp.symm
      · exact decide_eq_true (And.intro hv hb)
    · rintro ⟨_, hp⟩
      exact ((of_decide_eq_true hp : _ ∧ _)).symm
  have hperiod : (τ : StageDart (kmswStage w n).nextEdge → _)^[N]
      (stageULHeadDart w n) = stageULHeadDart w n := by
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hnorm : (raw.filter P).eraseDups = ys :=
    scan_filter_eraseDups_eq_of_chain τ (stageULHeadDart w n) N (orderOf_pos τ)
      hperiod P ys hnd hc hh hmem
  have hraw : (List.ofFn fun i : Fin (orderOf (stageRot w n).symm) =>
      ((stageRot w n).symm ^ i.val) (stageULHeadDart w n)) = raw := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_iterate, raw, N, τ]
    · intro i hi hi'
      simp only [List.getElem_ofFn, List.getElem_iterate, raw, Equiv.Perm.coe_pow, τ]
  have hfilters : (raw.filter fun d =>
      decide (stageEndpoint (kmswStage w n) d =
        stageEndpoint (kmswStage w n) (stageULHeadDart w n) ∧
        (kmswStage w n).present d.1.val = true ∧ d.2 = false)) =
      (raw.filter P).filter Q := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro d _
    simp [P, Q, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  have hstage : stageOutgoingDartOrder w n (stageULHeadDart w n) = ys.filter Q := by
    unfold stageOutgoingDartOrder
    rw [hraw, hfilters, eraseDups_filter_eq, hnorm]
  unfold stageOutgoingEdgeOrder
  rw [hstage]
  have hefilter := congrArg
    (List.filter (fun e => decide ((kmswStage w n).present e = true))) he
  rw [List.filter_map, List.filter_filter] at hefilter
  simpa [Function.comp_def, Q, Bool.and_comm] using hefilter


/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageOutgoingEdgeOrder_eq_infinite_filter_of_kind (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge)
    (hkind : corner = stageULHeadDart w n ∨
      corner.2 = false ∧ (stageRot w n corner).2 = true) :
    stageOutgoingEdgeOrder w n corner =
      (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
        (stageEndpoint (kmswStage w n) corner)
        ⟨n, stageEndpoint_lt_nextVertex w n corner⟩).filter
          (fun e => decide (e < (kmswStage w n).nextEdge ∧
            (kmswStage w n).present e = true)) := by
  rcases hkind with rfl | ⟨hd, hi⟩
  · exact stageOutgoingEdgeOrder_eq_infinite_filter_source w hfin hL htrans hR n
  · exact stageOutgoingEdgeOrder_eq_infinite_filter_incomingCut w hfin hL htrans hR
      n corner hd hi

/-- infinite outgoing rotation order at the source in the KMSW code realization;
T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageOutgoingEdgeOrder_hord (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (t : ℕ)
    (P : InfinitePresentPath w ⟨0⟩) (j : ℕ) :
    ∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
      (d = stageULHeadDart w (t - 1) ∨
        d.2 = false ∧ (stageRot w (t - 1) d).2 = true) →
      (∃ k ≤ j, stageEndpoint (kmswStage w (t - 1)) d = (P.initial k).1.id) →
      stageOutgoingEdgeOrder w (t - 1) d =
        (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
          (stageEndpoint (kmswStage w (t - 1)) d)
          ⟨t - 1, stageEndpoint_lt_nextVertex w (t - 1) d⟩).filter
            (fun e => decide (e < (kmswStage w (t - 1)).nextEdge ∧
              (kmswStage w (t - 1)).present e = true)) := by
  intro d hkind _
  exact stageOutgoingEdgeOrder_eq_infinite_filter_of_kind w hfin hL htrans hR
    (t - 1) d hkind

end DirectedDistances.KMSW
