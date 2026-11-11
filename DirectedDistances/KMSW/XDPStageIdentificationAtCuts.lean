module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.ActiveTimeMonotone
import DirectedDistances.KMSW.KMSWShiftLateLift

/-! # Stage identification of directed distances to cut vertices

Helper toward lem-finite-ind / lem-filtration-mono
in the stage map, so infinite-map directed distances to cut vertices equal stage
not the paper result.

The invariant used here is strict increase of activation times along consecutive
present edges. Appending the active edge at time `t` bounds all preceding
activation times by `t`. Thus confinement to stage `t` holds even without record
barriers, for arbitrary initial vertices. All arrows retain their edge IDs. -/

public section
namespace DirectedDistances.KMSW

open Quiver

private theorem path_before_arrow {w : ℕ → Fin 3} {u v z : PresentVertex w}
    (p : Path u v) (e : v ⟶ z) :
    p.length ≤ actTime w e.val e.property.1 ∧
    ∀ f ∈ pathEdgeList p, ∃ hf : EdgePresent w f,
      actTime w f hf < actTime w e.val e.property.1 := by
  induction p generalizing z with
  | nil => exact ⟨Nat.zero_le _, by simp only [pathEdgeList, List.not_mem_nil,
      false_implies, implies_true]⟩
  | @cons a b p f ih =>
    have hlt := actTime_lt_of_consecutive w f.property.1 e.property.1
      (f.property.2.2.trans e.property.2.1.symm)
    obtain ⟨hlen, hmem⟩ := ih f
    refine ⟨by simp only [Path.length_cons]; omega, ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨hg, hgt⟩ := hmem g hg
      exact ⟨hg, hgt.trans hlt⟩
    · have hgf := List.mem_singleton.mp hg
      subst g
      exact ⟨f.property.1, hlt⟩

private theorem active_present (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).present (act w t) = true := by
  apply (kmswStage_status w t).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private def activeArrow (w : ℕ → Fin 3) (t : ℕ) :
    recordVertex w t ⟶ (⟨edgeEast w (act w t)⟩ : PresentVertex w) :=
  ⟨act w t, ⟨t, act_lt_nextEdge w le_rfl, active_present w t⟩,
    (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl t))).1.symm, rfl⟩

/-- Helper toward lem-finite-ind / lem-filtration-mono
in the stage map, so infinite-map directed distances to cut vertices equal stage
not the paper result. The stronger bound holds at every time and for every start. -/
theorem presentPath_to_record_edges_before {w : ℕ → Fin 3} {t : ℕ}
    {a : PresentVertex w} (p : Path a (recordVertex w t)) :
    p.length ≤ t ∧ ∀ e ∈ pathEdgeList p, ∃ k < t, e = act w k := by
  obtain ⟨hlen, he⟩ := path_before_arrow p (activeArrow w t)
  have ht : actTime w (activeArrow w t).val (activeArrow w t).property.1 = t :=
    (actTime_eq_iff w _ _ t).2 rfl
  rw [ht] at hlen he
  exact ⟨hlen, fun e hm => by
    obtain ⟨hp, hk⟩ := he e hm
    exact ⟨actTime w e hp, hk, actTime_spec w e hp⟩⟩

private theorem stagePath_lift {w : ℕ → Fin 3} {t : ℕ}
    {a b : PresentVertex w} (p : Path a b)
    (hp : ∀ e ∈ pathEdgeList p, ∃ k ≤ t, e = act w k) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w t) ⟨b.id⟩,
      (stageToLimit w t).mapPath q = p := by
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons a b p e ih =>
    have hp' : ∀ f ∈ pathEdgeList p, ∃ k ≤ t, f = act w k := by
      intro f hf
      exact hp f (List.mem_append_left _ hf)
    obtain ⟨q, hq⟩ := ih hp'
    obtain ⟨k, hk, he⟩ := hp e.val (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have halloc : e.val < (kmswStage w t).nextEdge := by
      rw [he]
      exact act_lt_nextEdge w hk
    have hpres : (kmswStage w t).present e.val = true := by
      rw [he]
      exact (present_mono w (act_lt_nextEdge w (Nat.le_refl k))
        (active_present w k) t hk).2
    let f : (⟨a.id⟩ : StagePresentVertex w t) ⟶ ⟨b.id⟩ :=
      ⟨e.val, halloc, hpres,
        (edge_endpoints_eq w halloc).1.trans e.property.2.1,
        (edge_endpoints_eq w halloc).2.trans e.property.2.2⟩
    refine ⟨q.cons f, ?_⟩
    rw [Prefunctor.mapPath_cons, hq]
    have hf : (stageToLimit w t).map f = e := Subtype.ext rfl
    exact congrArg (Path.cons p) hf

/-- Helper toward lem-finite-ind / lem-filtration-mono
in the stage map, so infinite-map directed distances to cut vertices equal stage
not the paper result. This lift preserves the entire arrow-valued path. -/
theorem presentPath_to_record_lifts {w : ℕ → Fin 3} {t : ℕ}
    {a : PresentVertex w} (p : Path a (recordVertex w t)) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w t) ⟨(recordVertex w t).id⟩,
      (stageToLimit w t).mapPath q = p := by
  apply stagePath_lift p
  intro e he
  obtain ⟨k, hk, hke⟩ := (presentPath_to_record_edges_before p).2 e he
  exact ⟨k, hk.le, hke⟩

/-- Helper toward lem-finite-ind / lem-filtration-mono
in the stage map, so infinite-map directed distances to cut vertices equal stage
not the paper result. Every traversed edge is allocated and present at stage `t`. -/
theorem presentPath_to_record_stage_edges {w : ℕ → Fin 3} {t : ℕ}
    {a : PresentVertex w} (p : Path a (recordVertex w t)) :
    ∀ e ∈ pathEdgeList p, e < (kmswStage w t).nextEdge ∧
      (kmswStage w t).present e = true := by
  intro e he
  obtain ⟨k, hk, rfl⟩ := (presentPath_to_record_edges_before p).2 e he
  exact present_mono w (act_lt_nextEdge w (Nat.le_refl k))
    (active_present w k) t hk.le

private theorem ldpSup_eq_length {V : Type*} [Quiver V] {a b : V}
    {p : Path a b} (hp : IsLongest p) : ldpSup a b = (p.length : WithBot ℕ) := by
  have hmem : (p.length : WithBot ℕ) ∈
      (fun n : ℕ => (n : WithBot ℕ)) '' pathLengths a b :=
    ⟨p.length, ⟨p, rfl⟩, rfl⟩
  have hub : ∀ n ∈ (fun n : ℕ => (n : WithBot ℕ)) '' pathLengths a b,
      n ≤ (p.length : WithBot ℕ) := by
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    exact WithBot.coe_le_coe.mpr (hp q)
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

/-- Helper toward lem-finite-ind / lem-filtration-mono
in the stage map, so infinite-map directed distances to cut vertices equal stage
not the paper result. The natural stage LDP is embedded into the extended limit
carrier; unreachable LDP and SDP retain bottom and top respectively. -/
theorem presentDistances_to_record_eq_stage (w : ℕ → Fin 3) (t : ℕ)
    (a : PresentVertex w) :
    presentLdp a (recordVertex w t) =
      WithBot.map (fun n : ℕ => (n : ℕ∞))
        (ldpSup (⟨a.id⟩ : StagePresentVertex w t) ⟨(recordVertex w t).id⟩) ∧
    sdp a (recordVertex w t) =
      sdp (⟨a.id⟩ : StagePresentVertex w t) ⟨(recordVertex w t).id⟩ := by
  constructor
  · by_cases hr : Reachable a (recordVertex w t)
    · have hb : BddAbove (pathLengths a (recordVertex w t)) := by
        refine ⟨t, ?_⟩
        rintro _ ⟨p, rfl⟩
        exact (presentPath_to_record_edges_before p).1
      obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove hb hr
      obtain ⟨q, hq⟩ := presentPath_to_record_lifts p
      have hlen : q.length = p.length := by
        exact (stageToLimit_length w t q).symm.trans (congrArg Path.length hq)
      have hlong : IsLongest q := by
        intro r
        rw [← stageToLimit_length w t r, hlen]
        exact hp ((stageToLimit w t).mapPath r)
      rw [presentLdp_eq_length hp, ldpSup_eq_length hlong, hlen]
      rfl
    · have hs : ¬ Reachable (⟨a.id⟩ : StagePresentVertex w t)
          ⟨(recordVertex w t).id⟩ := by
        intro h
        exact hr (stageToLimit_reachable w t h)
      rw [ldpSup_eq_bot_of_not_reachable hs, WithBot.map_bot]
      let : IsEmpty (Path a (recordVertex w t)) := ⟨fun p => hr ⟨p⟩⟩
      exact iSup_of_empty _
  · apply le_antisymm
    · exact sdp_limit_le_sdp_stage w t ⟨a.id⟩ ⟨(recordVertex w t).id⟩
    · change _ ≤ ⨅ p : Path a (recordVertex w t), (p.length : ℕ∞)
      apply le_iInf
      intro p
      obtain ⟨q, hq⟩ := presentPath_to_record_lifts p
      have hlen : q.length = p.length := by
        exact (stageToLimit_length w t q).symm.trans (congrArg Path.length hq)
      exact (sdp_le_length q).trans_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hlen)

private theorem record_outgoing_activation_ge (w : ℕ → Fin 3) (m : ℕ)
    (hAm : ∀ j < m, R w m ≤ R w j - 1) {e : ℕ} (he : EdgePresent w e)
    (hw : edgeWest w e = (recordVertex w m).id) : m ≤ actTime w e he := by
  by_contra h
  have ht : actTime w e he < m := by omega
  apply activeInitial_ne_of_right_record w m hAm (actTime w e he) ht
  change edgeWest w (act w (actTime w e he)) = edgeWest w (act w m)
  rw [← actTime_spec w e he, hw]
  exact (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl m))).1

private theorem record_path_activation_ge {w : ℕ → Fin 3} {m : ℕ}
    (hAm : ∀ j < m, R w m ≤ R w j - 1) {b : PresentVertex w}
    (p : Path (recordVertex w m) b) :
    ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, m ≤ actTime w e he := by
  induction p with
  | nil => simp only [pathEdgeList, List.not_mem_nil, false_implies, implies_true]
  | @cons a b p e ih =>
    have ht : m ≤ actTime w e.val e.property.1 := by
      cases p with
      | nil => exact record_outgoing_activation_ge w m hAm e.property.1 e.property.2.1
      | cons q f =>
        have hf := ih f.val (List.mem_append_right _ (List.mem_singleton.mpr rfl))
          f.property.1
        have hlt := actTime_lt_of_consecutive w f.property.1 e.property.1
          (f.property.2.2.trans e.property.2.1.symm)
        exact hf.trans hlt.le
    intro f hf hfp
    rcases List.mem_append.mp hf with hf | hf
    · exact ih f hf hfp
    · have hfe := List.mem_singleton.mp hf
      subst f
      exact ht

/-- Helper toward lem-finite-ind / lem-filtration-mono
in the stage map, so infinite-map directed distances to cut vertices equal stage
not the paper result. Between records the activation indices lie in `[m,n)`.
This is an activation statement: allocation can occur before activation. -/
theorem presentPath_between_records_activation_interval (w : ℕ → Fin 3) {m n : ℕ}
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (p : Path (recordVertex w m) (recordVertex w n)) :
    ∀ e ∈ pathEdgeList p, ∃ k, m ≤ k ∧ k < n ∧ e = act w k := by
  intro e he
  obtain ⟨k, hk, hke⟩ := (presentPath_to_record_edges_before p).2 e he
  have hep : EdgePresent w e := by
    rw [hke]
    exact ⟨k, act_lt_nextEdge w le_rfl, active_present w k⟩
  have htime : actTime w e hep = k := (actTime_eq_iff w e hep k).2 hke
  have hlow := record_path_activation_ge hAm p e he hep
  exact ⟨k, htime ▸ hlow, hk, hke⟩

private theorem shift_record_vertex (w : ℕ → Fin 3) (m n : ℕ) :
    shiftLimitVertex w m (recordVertex (fun i => w (m + i)) n) =
      recordVertex w (m + n) := by
  let u := fun i => w (m + i)
  have ha : (recordVertex u n).id < (kmswStage u n).nextVertex :=
    (kmswStage_endpoints_lt_nextVertex u n (act u n) (act_lt_nextEdge u le_rfl)).1
  rw [shiftLimitVertex_eq w m n (recordVertex u n) ha]
  apply congrArg PresentVertex.mk
  have hs := (kmswShift_sim2_all w m n).sim
  have hi := (hs.incidence (act u n) (act_lt_nextEdge u le_rfl)).1
  rw [show act u n = (kmswStage u n).active from rfl, hs.active] at hi
  exact hi.symm

private theorem record_segment_pathLengths (w : ℕ → Fin 3) (m n : ℕ)
    (hAm : ∀ j < m, R w m ≤ R w j - 1) :
    pathLengths (recordVertex w m) (recordVertex w (m + n)) =
      pathLengths (⟨0⟩ : StagePresentVertex (fun i => w (m + i)) n)
        ⟨(recordVertex (fun i => w (m + i)) n).id⟩ := by
  let u := fun i => w (m + i)
  have hroot : shiftLimitVertex w m (⟨0⟩ : PresentVertex u) = recordVertex w m :=
    shiftLimitVertex_root w m
  have hr : shiftLimitVertex w m (recordVertex u n) = recordVertex w (m + n) :=
    shift_record_vertex w m n
  have ha : kmswVertexAllocated u (⟨0⟩ : PresentVertex u) := ⟨0, by change 0 < 2; omega⟩
  have hb : (recordVertex u n).id < (kmswStage u n).nextVertex :=
    (kmswStage_endpoints_lt_nextVertex u n (act u n) (act_lt_nextEdge u le_rfl)).1
  have hzero : 0 < (kmswStage u n).nextVertex := by
    have hmono := CutConverse.nextVertex_mono u (Nat.zero_le n)
    change 2 ≤ (kmswStage u n).nextVertex at hmono
    omega
  have hobj0 : (kmswShiftStageToLimit w m n).obj
      (⟨0⟩ : StagePresentVertex u n) = shiftLimitVertex w m ⟨0⟩ :=
    (shiftLimitVertex_eq w m n ⟨0⟩ hzero).symm
  have hobjn : (kmswShiftStageToLimit w m n).obj
      (⟨(recordVertex u n).id⟩ : StagePresentVertex u n) =
      shiftLimitVertex w m (recordVertex u n) :=
    (shiftLimitVertex_eq w m n (recordVertex u n) hb).symm
  rw [← hroot, ← hr]
  have hlate : ∀ p : Path (shiftLimitVertex w m (⟨0⟩ : PresentVertex u))
      (shiftLimitVertex w m (recordVertex u n)),
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, m ≤ actTime w e he := by
    rw [hroot]
    exact fun p => record_path_activation_ge hAm p
  ext l
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨b, hb', r, hr', hlen, _⟩ :=
      shiftLimitVertex_late_path_lift w m ⟨0⟩ ha p (hlate p)
    have heq : b = recordVertex u n :=
      shiftLimitVertex_injective w m hb' ⟨n, hb⟩ hr'
    subst b
    obtain ⟨q, hq⟩ := presentPath_to_record_lifts r
    exact ⟨q, (stageToLimit_length u n q).symm.trans
      ((congrArg Path.length hq).trans (hlen.trans hp))⟩
  · rintro ⟨q, hq⟩
    have hmem : l ∈ pathLengths
        ((kmswShiftStageToLimit w m n).obj (⟨0⟩ : StagePresentVertex u n))
        ((kmswShiftStageToLimit w m n).obj
          (⟨(recordVertex u n).id⟩ : StagePresentVertex u n)) :=
      ⟨(kmswShiftStageToLimit w m n).mapPath q,
        (kmswShiftStageToLimit_length w m n q).trans hq⟩
    rwa [hobj0, hobjn] at hmem

/-- Helper toward lem-finite-ind / lem-filtration-mono
in the stage map, so infinite-map directed distances to cut vertices equal stage
not the paper result. Distances across a record segment equal distances in the
finite shifted stage, whose construction uses the code on `[m,m+n)` only. -/
theorem recordSegment_distances_eq_shift_stage (w : ℕ → Fin 3) (m n : ℕ)
    (hAm : ∀ j < m, R w m ≤ R w j - 1) :
    presentLdp (recordVertex w m) (recordVertex w (m + n)) =
      WithBot.map (fun k : ℕ => (k : ℕ∞))
        (ldpSup (⟨0⟩ : StagePresentVertex (fun i => w (m + i)) n)
          ⟨(recordVertex (fun i => w (m + i)) n).id⟩) ∧
    sdp (recordVertex w m) (recordVertex w (m + n)) =
      sdp (⟨0⟩ : StagePresentVertex (fun i => w (m + i)) n)
        ⟨(recordVertex (fun i => w (m + i)) n).id⟩ := by
  let u := fun i => w (m + i)
  let a : StagePresentVertex u n := ⟨0⟩
  let b : StagePresentVertex u n := ⟨(recordVertex u n).id⟩
  have hsets := record_segment_pathLengths w m n hAm
  constructor
  · by_cases hr : Reachable (recordVertex w m) (recordVertex w (m + n))
    · have hbnd : BddAbove
          (pathLengths (recordVertex w m) (recordVertex w (m + n))) := by
        refine ⟨m + n, ?_⟩
        rintro _ ⟨p, rfl⟩
        exact (presentPath_to_record_edges_before p).1
      obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove hbnd hr
      obtain ⟨q, hq⟩ := hsets ▸ (show p.length ∈
        pathLengths (recordVertex w m) (recordVertex w (m + n)) from ⟨p, rfl⟩)
      change q.length = p.length at hq
      have hlong : IsLongest q := by
        intro r
        obtain ⟨s, hs⟩ := hsets.symm ▸ (show r.length ∈ pathLengths a b from ⟨r, rfl⟩)
        change s.length = r.length at hs
        exact hs ▸ (hq.symm ▸ hp s)
      rw [presentLdp_eq_length hp, ldpSup_eq_length hlong, hq]
      rfl
    · have hs : ¬ Reachable a b := by
        rintro ⟨q⟩
        obtain ⟨p, _⟩ := hsets.symm ▸ (show q.length ∈ pathLengths a b from ⟨q, rfl⟩)
        exact hr ⟨p⟩
      rw [ldpSup_eq_bot_of_not_reachable hs, WithBot.map_bot]
      let : IsEmpty (Path (recordVertex w m) (recordVertex w (m + n))) :=
        ⟨fun p => hr ⟨p⟩⟩
      exact iSup_of_empty _
  · apply le_antisymm
    · change _ ≤ ⨅ q : Path a b, (q.length : ℕ∞)
      apply le_iInf
      intro q
      obtain ⟨p, hp⟩ := hsets.symm ▸ (show q.length ∈ pathLengths a b from ⟨q, rfl⟩)
      exact (sdp_le_length p).trans_eq (congrArg (fun k : ℕ => (k : ℕ∞)) hp)
    · change _ ≤ ⨅ p : Path (recordVertex w m) (recordVertex w (m + n)),
        (p.length : ℕ∞)
      apply le_iInf
      intro p
      obtain ⟨q, hq⟩ := hsets ▸ (show p.length ∈
        pathLengths (recordVertex w m) (recordVertex w (m + n)) from ⟨p, rfl⟩)
      exact (sdp_le_length q).trans_eq (congrArg (fun k : ℕ => (k : ℕ∞)) hq)

end DirectedDistances.KMSW
