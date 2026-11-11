module

public import DirectedDistances.KMSW.StageLeftmostXDPIdentification
public import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
public import DirectedDistances.KMSW.StageMapCongr
public import DirectedDistances.KMSW.StoppedWalkLaw
import DirectedDistances.KMSW.HatInducedExit










public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem vertex_complete_exists (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : ℕ) : ∃ N, kmswVertexComplete w N v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hm : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hm).trans_lt (kmsw_edge_allocated_by_self w B)

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem stageEndpoint_cast (w : ℕ → Fin 3) {n m : ℕ} (h : n ≤ m)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w m)
        (outerSucc_castDart (kmswStage_nextEdge_mono w h) d) =
      stageEndpoint (kmswStage w n) d := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  obtain ⟨hw', he'⟩ := edge_endpoints_eq w
    (d.1.isLt.trans_le (kmswStage_nextEdge_mono w h))
  cases hb : d.2 <;>
    simp only [stageEndpoint, outerSucc_castDart, hb, Bool.false_eq_true, ↓reduceIte,
      Fin.val_castLE, hw, he, hw', he']

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. The first positive return to the old
geometric darts is exactly the old rotation successor, even at boundary vertices. -/
theorem kmswInfRot_firstReturn_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    ∃ k : ℕ, 0 < k ∧
      (kmswInfRot w hfin ^ k) (d.1.val, d.2) =
        ((stageRot w n d).1.val, (stageRot w n d).2) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswStage w n).nextEdge ≤ ((kmswInfRot w hfin ^ j) (d.1.val, d.2)).1 := by
  obtain ⟨B, hB⟩ := vertex_complete_exists w hfin (stageEndpoint (kmswStage w n) d)
  let m := max n B
  have hnm : n ≤ m := le_max_left _ _
  let D := outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d
  have hc : kmswVertexComplete w m (stageEndpoint (kmswStage w m) D) := by
    rw [stageEndpoint_cast w hnm d]
    intro e he
    exact (hB e he).trans_le (kmswStage_nextEdge_mono w (le_max_right _ _))
  obtain ⟨k, hk, hret, hbefore⟩ := hatExit_ambient_rotation_induced w n m hnm d
  rw [← Equiv.Perm.coe_pow] at hret
  simp only [← Equiv.Perm.coe_pow] at hbefore
  refine ⟨k, hk, ?_, ?_⟩
  · have hp := kmswInfRot_pow_eq_stage w hfin m D hc k
    rw [hret] at hp
    exact hp
  · intro j hj hjk
    have hp := kmswInfRot_pow_eq_stage w hfin m D hc j
    change (kmswInfRot w hfin ^ j) (d.1.val, d.2) = _ at hp
    rw [hp]
    by_contra hn
    have hlt : ((stageRot w m ^ j) D).1.val <
        (kmswStage w n).nextEdge := Nat.lt_of_not_ge hn
    apply hbefore j hj hjk
    refine ⟨(⟨_, hlt⟩, ((stageRot w m ^ j) D).2), ?_⟩
    rfl

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. The reverse scan also has the finite
stage rotation as its first return to the old geometric darts. -/
theorem kmswInfRot_symm_firstReturn_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    ∃ k : ℕ, 0 < k ∧
      ((kmswInfRot w hfin).symm ^ k) (d.1.val, d.2) =
        (((stageRot w n).symm d).1.val, ((stageRot w n).symm d).2) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswStage w n).nextEdge ≤
          (((kmswInfRot w hfin).symm ^ j) (d.1.val, d.2)).1 := by
  let σ := kmswInfRot w hfin
  let e := (stageRot w n).symm d
  obtain ⟨k, hk, hret, hgap⟩ := kmswInfRot_firstReturn_stage w hfin n e
  have he : stageRot w n e = d := (stageRot w n).apply_symm_apply d
  rw [he] at hret
  have hinv (i : ℕ) : σ.symm ^ i = (σ ^ i).symm := inv_pow σ i
  have hback : (σ.symm ^ k) (d.1.val, d.2) = (e.1.val, e.2) := by
    rw [hinv, ← hret, Equiv.symm_apply_apply]
  refine ⟨k, hk, hback, ?_⟩
  intro j hj hjk
  have hshift : (σ.symm ^ j) (d.1.val, d.2) =
      (σ ^ (k - j)) (e.1.val, e.2) := by
    apply (σ ^ j).injective
    rw [hinv, Equiv.apply_symm_apply, ← Equiv.Perm.mul_apply, ← pow_add,
      Nat.add_sub_cancel' hjk.le]
    exact hret.symm
  rw [hshift]
  exact hgap (k - j) (by omega) (by omega)

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem incomingCut_arc_eq (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (n : ℕ) (d e : StageDart (kmswStage w n).nextEdge)
    (hi : (stageRot w n d).2 = true)
    (ha : RotationArc (kmswInfRot w hfin)
      (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
      (d.1.val, d.2) (e.1.val, e.2)) : d = e := by
  obtain ⟨l, hl, hm⟩ := ha
  obtain ⟨k, hk, hret, hgap⟩ := kmswInfRot_firstReturn_stage w hfin n d
  by_cases hz : l = 0
  · subst l
    have he : (d.1.val, d.2) = (e.1.val, e.2) := hl
    apply Prod.ext
    · exact Fin.ext (congrArg (fun x : ℕ × Bool => x.1) he)
    · exact congrArg (fun x : ℕ × Bool => x.2) he
  · have hlpos : 0 < l := Nat.pos_of_ne_zero hz
    by_cases hlt : l < k
    · have hge := hgap l hlpos hlt
      rw [hl] at hge
      have := e.1.isLt
      omega
    · have hb := (hm k (by omega)).1
      rw [hret, hi] at hb
      exact Bool.noConfusion hb

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. At the incoming-block cut, every old
outgoing geometric dart precedes the corner in the infinite outgoing interval.
No completeness condition or restriction on later allocations is needed. -/
theorem stage_incomingCut_infinite_outgoing_arc (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge)
    (hd : d.2 = false) (hi : (stageRot w n d).2 = true) (he : e.2 = false)
    (hv : stageEndpoint (kmswStage w n) e = stageEndpoint (kmswStage w n) d) :
    RotationArc (kmswInfRot w hfin)
      (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
      (e.1.val, e.2) (d.1.val, d.2) := by
  have hw : edgeWest w e.1.val = edgeWest w d.1.val := by
    simpa only [stageEndpoint, he, hd, Bool.false_eq_true, ↓reduceIte,
      (edge_endpoints_eq w e.1.isLt).1, (edge_endpoints_eq w d.1.isLt).1] using hv
  have hep := edgePresent_of_nonneg_of_unbounded w hL hR e.1.val
  have hdp := edgePresent_of_nonneg_of_unbounded w hL hR d.1.val
  obtain ha | ha := kmswInfRot_outgoing_interval w hL hfin e.1.val d.1.val hw hep hdp
  · simpa only [he, hd] using ha
  · have ha' : RotationArc (kmswInfRot w hfin)
        (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
        (d.1.val, d.2) (e.1.val, e.2) := by
      simpa only [he, hd] using ha
    have hde := incomingCut_arc_eq w hfin n d e hi ha'
    subst e
    exact RotationArc.refl _ _ _ ⟨hd, hdp⟩

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. Membership retains the allocated edge
identity, its presence flag, and its west endpoint. -/
theorem mem_stageOutgoingEdgeOrder (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (e : ℕ) :
    e ∈ stageOutgoingEdgeOrder w n d ↔
      e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true ∧
        (kmswStage w n).west e = stageEndpoint (kmswStage w n) d := by
  classical
  unfold stageOutgoingEdgeOrder stageOutgoingDartOrder
  simp only [List.mem_map, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨_, ha, hp, hb⟩, rfl⟩
    refine ⟨a.1.isLt, hp, ?_⟩
    simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using ha
  · rintro ⟨he, hp, hv⟩
    let a : StageDart (kmswStage w n).nextEdge := (⟨e, he⟩, false)
    have ha : stageEndpoint (kmswStage w n) a = stageEndpoint (kmswStage w n) d := hv
    have hcycle : (stageRot w n).SameCycle d a :=
      (stageRot_sameCycle_iff_endpoint_eq w n d a).2 ha.symm
    have hinv : Equiv.Perm.SameCycle (stageRot w n).symm d a :=
      Equiv.Perm.sameCycle_inv.mpr hcycle
    obtain ⟨i, hi, hpow⟩ := hinv.exists_pow_eq'
    refine ⟨a, ⟨?_, ha, hp, rfl⟩, rfl⟩
    exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, hpow⟩

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. The two lists have exactly the same
members at every stage and every corner; this does not assert equality of order. -/
theorem mem_stageOutgoingEdgeOrder_iff_infinite_filter (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (e : ℕ) :
    e ∈ stageOutgoingEdgeOrder w n d ↔
      e ∈ (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
        (stageEndpoint (kmswStage w n) d) ⟨n, stageEndpoint_lt_nextVertex w n d⟩).filter
          (fun f => decide (f < (kmswStage w n).nextEdge ∧
            (kmswStage w n).present f = true)) := by
  classical
  rw [mem_stageOutgoingEdgeOrder, List.mem_filter, decide_eq_true_eq,
    mem_kmswOutgoingEdgesLeftToRight]
  constructor
  · rintro ⟨he, hp, hv⟩
    exact ⟨⟨⟨n, he, hp⟩, (edge_endpoints_eq w he).1.symm.trans hv⟩, he, hp⟩
  · rintro ⟨⟨_, hv⟩, he, hp⟩
    exact ⟨he, hp, (edge_endpoints_eq w he).1.trans hv⟩

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem nodup_eraseDups {α : Type*} [BEq α] [LawfulBEq α]
    (l : List α) : l.eraseDups.Nodup := by
  suffices h : ∀ n : ℕ, ∀ l : List α, l.length = n → l.eraseDups.Nodup by
    exact h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl
    cases l with
    | nil => simp only [List.eraseDups_nil, List.nodup_nil]
    | cons a t =>
      simp only [List.length_cons] at hl
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro ha
        obtain ⟨_, hneq⟩ := List.mem_filter.mp (List.mem_eraseDups.mp ha)
        simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true] at hneq
      · apply ih (t.filter (fun b => !(b == a))).length
        · have := List.length_filter_le (fun b => !(b == a)) t
          omega
        · rfl

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem stageOutgoingEdgeOrder_nodup (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (stageOutgoingEdgeOrder w n d).Nodup := by
  classical
  unfold stageOutgoingEdgeOrder
  apply (nodup_eraseDups _).map_on
  intro a ha b hb he
  have hside (x : StageDart (kmswStage w n).nextEdge)
      (hx : x ∈ stageOutgoingDartOrder w n d) : x.2 = false := by
    simp only [stageOutgoingDartOrder, List.mem_eraseDups, List.mem_filter,
      decide_eq_true_eq] at hx
    exact hx.2.2.2
  exact Prod.ext (Fin.ext he) ((hside a ha).trans (hside b hb).symm)

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. Equality up to permutation holds at every
corner, without asserting the still needed agreement of the linear cuts. -/
theorem stageOutgoingEdgeOrder_perm_infinite_filter (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (stageOutgoingEdgeOrder w n d).Perm
      ((kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
        (stageEndpoint (kmswStage w n) d) ⟨n, stageEndpoint_lt_nextVertex w n d⟩).filter
          (fun f => decide (f < (kmswStage w n).nextEdge ∧
            (kmswStage w n).present f = true))) := by
  classical
  have hn : (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
      (stageEndpoint (kmswStage w n) d) ⟨n, stageEndpoint_lt_nextVertex w n d⟩).Nodup := by
    unfold kmswOutgoingEdgesLeftToRight
    split
    · rw [List.nodup_reverse]
      exact (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.1
    · rename_i h
      rw [List.nodup_reverse]
      have henum := kmsw_nonzero_outgoing_enumeration w hfin hL hR _
        ⟨n, stageEndpoint_lt_nextVertex w n d⟩ h
      exact henum.choose_spec.choose_spec.choose_spec.1
  apply (List.perm_ext_iff_of_nodup (stageOutgoingEdgeOrder_nodup w n d)
    (hn.filter _)).2
  exact mem_stageOutgoingEdgeOrder_iff_infinite_filter w hfin hL htrans hR n d

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private def prefixDartEquiv {s t : State} (h : s = t) :
    StageDart s.nextEdge ≃ StageDart t.nextEdge :=
  Equiv.prodCongr (finCongr (congrArg State.nextEdge h)) (Equiv.refl Bool)

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private noncomputable def outgoingEdgeScan (s : State)
    (σ : Equiv.Perm (StageDart s.nextEdge)) (d : StageDart s.nextEdge) : List ℕ := by
  classical
  exact (((List.ofFn fun i : Fin (orderOf σ.symm) => (σ.symm ^ i.val) d).filter
    fun e => stageEndpoint s e = stageEndpoint s d ∧
      s.present e.1.val = true ∧ e.2 = false).eraseDups).map (fun e => e.1.val)

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem outgoingEdgeScan_congr {s t : State} (h : s = t)
    (σ : Equiv.Perm (StageDart s.nextEdge)) (τ : Equiv.Perm (StageDart t.nextEdge))
    (hr : ∀ d, prefixDartEquiv h (σ d) = τ (prefixDartEquiv h d))
    (d : StageDart s.nextEdge) :
    outgoingEdgeScan s σ d = outgoingEdgeScan t τ (prefixDartEquiv h d) := by
  cases h
  have heq : σ = τ := by
    apply Equiv.ext
    intro x
    exact hr x
  subst τ
  rfl

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. A common code prefix preserves the entire
outgoing list and its corner under the existing directed stage isomorphism. -/
theorem stageOutgoingEdgeOrder_eq_of_prefix (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) (d : StageDart (kmswStage w n).nextEdge) :
    stageOutgoingEdgeOrder w n d =
      stageOutgoingEdgeOrder w' n ((kmswStageDirectedMapIsoOfPrefix w w' n h).toEquiv d) := by
  let hs := kmswStage_eq_of_prefix w w' n h
  let I := kmswStageDirectedMapIsoOfPrefix w w' n h
  have hI (e : StageDart (kmswStage w n).nextEdge) :
      I.toEquiv e = prefixDartEquiv hs e := by
    apply Prod.ext
    · apply Fin.ext
      exact (kmswStageDirectedMapIsoOfPrefix_val w w' n h e).1
    · exact (kmswStageDirectedMapIsoOfPrefix_val w w' n h e).2
  have hr (e : StageDart (kmswStage w n).nextEdge) :
      prefixDartEquiv hs (stageRot w n e) = stageRot w' n (prefixDartEquiv hs e) := by
    rw [← hI, ← hI]
    exact I.rot_comm e
  change outgoingEdgeScan _ _ d = outgoingEdgeScan _ _ (I.toEquiv d)
  rw [hI]
  exact outgoingEdgeScan_congr hs _ _ hr d

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. The finite walk-class word has N - 1
codes, and its padded extension has exactly the same outgoing order as w. -/
theorem stageOutgoingEdgeOrder_codeExtend {ℓ r N : ℕ} (c : KMSWWalkClass ℓ r N)
    (w : ℕ → Fin 3) (hc : ∀ i : Fin (N - 1), c.val i = w i.val)
    (d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) :
    stageOutgoingEdgeOrder (codeExtend c) (N - 1) d =
      stageOutgoingEdgeOrder w (N - 1)
        ((kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (N - 1)
          (fun i hi => (codeExtend_of_lt c i hi).trans (hc ⟨i, hi⟩))).toEquiv d) := by
  exact stageOutgoingEdgeOrder_eq_of_prefix (codeExtend c) w (N - 1)
    (fun i hi => (codeExtend_of_lt c i hi).trans (hc ⟨i, hi⟩)) d

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. In particular a stopped walk word has
the same outgoing order as its actual Boltzmann stream through the last code. -/
theorem stageOutgoingEdgeOrder_stoppedWord (r : ℕ) (ω : ℕ → Fin 3)
    {ℓ : ℕ} (c : KMSWWalkClass ℓ r (boltzmannTau r ω))
    (hc : c.val = stoppedWord r ω)
    (d : StageDart (kmswStage (codeExtend c) (boltzmannTau r ω - 1)).nextEdge) :
    stageOutgoingEdgeOrder (codeExtend c) (boltzmannTau r ω - 1) d =
      stageOutgoingEdgeOrder (boltzmannKMSWStream ω) (boltzmannTau r ω - 1)
        ((kmswStageDirectedMapIsoOfPrefix (codeExtend c) (boltzmannKMSWStream ω)
          (boltzmannTau r ω - 1) (fun i hi =>
            (codeExtend_of_lt c i hi).trans (congrFun hc ⟨i, hi⟩))).toEquiv d) := by
  exact stageOutgoingEdgeOrder_codeExtend c (boltzmannKMSWStream ω)
    (fun i => congrFun hc i) d

end DirectedDistances.KMSW
