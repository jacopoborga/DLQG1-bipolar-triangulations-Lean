module

public import DirectedDistances.KMSW.ShiftInfRotFirstReturn
public import DirectedDistances.KMSW.RawHatOutgoingOrder
public import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
import DirectedDistances.KMSW.OutgoingIntervalFreshLeft

/-! Supporting lemmas for paper labels `lem-geo-infty` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.KMSW

private theorem shift_limit_incidence (w : ℕ → Fin 3) (t e : ℕ) :
    let u := fun i => w (t + i)
    let E := kmswShiftEdgeMapAll w t e e
    let V := limitVertexMap (kmswShiftVertexMapAll w t) u
    edgeWest w E = V (edgeWest u e) ∧ edgeEast w E = V (edgeEast u e) := by
  let u := fun i => w (t + i)
  have he := kmsw_edge_allocated_by_self u e
  have S := (kmswShift_sim2_all w t e).sim
  have hW := edge_endpoints_eq w (S.edge_bound e he)
  have hU := edge_endpoints_eq u he
  have hi := S.incidence e he
  have hb := kmswStage_endpoints_lt_nextVertex u e e he
  have hvW := limitVertexMap_eq_of_allocated (kmswShiftVertexMapAll w t)
    (kmswShiftVertexMapAll_extend w t) e _ hb.1
  have hvE := limitVertexMap_eq_of_allocated (kmswShiftVertexMapAll w t)
    (kmswShiftVertexMapAll_extend w t) e _ hb.2
  dsimp only
  constructor
  · rw [← hW.1, hi.1, ← hU.1, hvW]
  · rw [← hW.2, hi.2, ← hU.2, hvE]

private theorem shift_limit_present (w : ℕ → Fin 3) (t e : ℕ)
    (hp : EdgePresent (fun i => w (t + i)) e) :
    EdgePresent w (kmswShiftEdgeMapAll w t e e) := by
  obtain ⟨m, he, hp⟩ := hp
  have h := (kmswShift_present_edge_maps w t m e he hp).1
  have hmap : kmswShiftEdgeMapAll w t e e = kmswShiftEdgeMapAll w t m e := by
    by_cases hm : m ≤ e
    · exact kmswShiftEdgeMapAll_eq_of_le w t m e e hm he
    · exact (kmswShiftEdgeMapAll_eq_of_le w t e m e (by omega)
        (kmsw_edge_allocated_by_self _ e)).symm
  rw [hmap]
  exact h





theorem shiftHat_edge_incidence (w : ℕ → Fin 3) (t : ℕ)
    (h : HasFlowLineHits (fun i => w (t + i))) (e : ℕ) :
    let u := fun i => w (t + i)
    let φ := fun f => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h f)
      (hatLimitEdgeMap u h f)
    let φv := fun a => limitVertexMap (kmswShiftVertexMapAll w t) u
      (hatLimitVertexMap u h a)
    edgeWest w (φ e) = φv (edgeWest (hatCodes u h) e) ∧
      edgeEast w (φ e) = φv (edgeEast (hatCodes u h) e) ∧
      (EdgePresent (hatCodes u h) e → EdgePresent w (φ e)) := by
  let u := fun i => w (t + i)
  have he := kmsw_edge_allocated_by_self (hatCodes u h) e
  have S := (hatLimitExplicitInput u h).stage_sim e
  have hW := edge_endpoints_eq u (S.edge_bound e he)
  have hU := edge_endpoints_eq (hatCodes u h) he
  have hi := S.incidence e he
  have hwest : edgeWest u (hatLimitEdgeMap u h e) =
      hatLimitVertexMap u h (edgeWest (hatCodes u h) e) := by
    rw [← hW.1, hi.1, hU.1]
  have heast : edgeEast u (hatLimitEdgeMap u h e) =
      hatLimitVertexMap u h (edgeEast (hatCodes u h) e) := by
    rw [← hW.2, hi.2, hU.2]
  have hs := shift_limit_incidence w t (hatLimitEdgeMap u h e)
  dsimp only at hs ⊢
  refine ⟨?_, ?_, fun hp => ?_⟩
  · exact hs.1.trans (congrArg _ hwest)
  · exact hs.2.trans (congrArg _ heast)
  · exact shift_limit_present w t _
      (hatLimit_edge_incidence (hatLimitExplicitInput u h) hp).1

private theorem arc_iff_positions {α : Type*} [DecidableEq α]
    (σ : Equiv.Perm α) (s : Finset α) (hs : σ.IsCycleOn (s : Set α))
    (p : α → Prop) (d e f : α) (hd : d ∈ s) (hpd : ¬p d)
    (_he : e ∈ s) (_hf : f ∈ s) (hpe : p e) (hpf : p f)
    (hc : RotationArc σ p e f ∨ RotationArc σ p f e)
    (i j : ℕ) (hi : i < s.card) (hj : j < s.card)
    (hei : (σ ^ i) d = e) (hfj : (σ ^ j) d = f) :
    RotationArc σ p e f ↔ i ≤ j := by
  have bound (a b : α) (_ha : p a) (n m : ℕ)
      (hn : n < s.card) (hm : m < s.card)
      (hna : (σ ^ n) d = a) (hmb : (σ ^ m) d = b)
      (harc : RotationArc σ p a b) : n ≤ m := by
    obtain ⟨k, hk, hp⟩ := harc
    have hreturn : (σ ^ (s.card - n)) a = d := by
      rw [← hna, ← Equiv.Perm.mul_apply, ← pow_add,
        Nat.sub_add_cancel hn.le, hs.pow_card_apply hd]
    have hkn : k < s.card - n := by
      by_contra h
      exact hpd (hreturn ▸ hp (s.card - n) (by omega))
    have hsum : n + k < s.card := by omega
    have heq : (σ ^ (n + k)) d = (σ ^ m) d := by
      rw [Nat.add_comm, pow_add, Equiv.Perm.mul_apply, hna, hk, hmb]
    have heq' := hs.injOn_pow_apply hd hsum hm heq
    omega
  constructor
  · exact bound e f hpe i j hi hj hei hfj
  · intro hij
    rcases hc with h | h
    · exact h
    · have hji := bound f e hpf j i hj hi hfj hei h
      have heq : e = f := by
        have hij' : i = j := by omega
        rw [← hei, ← hfj, hij']
      rw [heq]
      exact RotationArc.refl σ p f hpf

private theorem cyclic_iff_arc {α : Type*} [DecidableEq α]
    (σ : Equiv.Perm α) (s : Finset α) (hs : σ.IsCycleOn (s : Set α))
    (p : α → Prop) (d e f : α) (hd : d ∈ s) (hpd : ¬p d)
    (he : e ∈ s) (hf : f ∈ s) (hpe : p e) (hpf : p f)
    (hc : RotationArc σ p e f ∨ RotationArc σ p f e) (hne : e ≠ f) :
    (∃ i j : ℕ, 0 < i ∧ i < j ∧
      (σ : _ → _)^[i] d = e ∧ (σ : _ → _)^[j] d = f ∧
      ∀ k : ℕ, 0 < k → k ≤ j → (σ : _ → _)^[k] d ≠ d) ↔
      RotationArc σ p e f := by
  constructor
  · rintro ⟨i, j, hi, hij, hei, hfj, hno⟩
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨d, hd⟩
    have hj : j < s.card := by
      by_contra h
      exact hno s.card hpos (by omega) (hs.pow_card_apply hd)
    exact (arc_iff_positions σ s hs p d e f hd hpd he hf hpe hpf hc
      i j (by omega) hj hei hfj).mpr hij.le
  · intro harc
    obtain ⟨i, hi, hei⟩ := hs.exists_pow_eq hd he
    obtain ⟨j, hj, hfj⟩ := hs.exists_pow_eq hd hf
    have hij := (arc_iff_positions σ s hs p d e f hd hpd he hf hpe hpf hc
      i j hi hj hei hfj).mp harc
    have hip : 0 < i := by
      by_contra h
      have hz : i = 0 := by omega
      subst i
      have heq : d = e := hei
      exact hpd (heq.symm ▸ hpe)
    have hlt : i < j := by
      by_contra h
      have heq : i = j := by omega
      exact hne (hei.symm.trans (heq ▸ hfj))
    refine ⟨i, j, hip, hlt, hei, hfj, ?_⟩
    intro k hk hkj heq
    have heq' : (σ ^ k) d = (σ ^ 0) d := heq
    have := hs.injOn_pow_apply hd (by omega : k < s.card) (by omega : 0 < s.card)
      heq'
    omega

private theorem shift_edge_injective (w : ℕ → Fin 3) (t : ℕ) :
    Function.Injective (fun e => kmswShiftEdgeMapAll w t e e) := by
  intro e f hef
  let n := max e f
  have he := kmsw_edge_allocated_by_self (fun i => w (t + i)) e
  have hf := kmsw_edge_allocated_by_self (fun i => w (t + i)) f
  have heN := kmswShiftEdgeMapAll_eq_of_le w t e n e (Nat.le_max_left _ _) he
  have hfN := kmswShiftEdgeMapAll_eq_of_le w t f n f (Nat.le_max_right _ _) hf
  apply (kmswShift_sim2_all w t n).sim.edge_injective e f
    (he.trans_le (kmswStage_nextEdge_mono _ (Nat.le_max_left _ _)))
    (hf.trans_le (kmswStage_nextEdge_mono _ (Nat.le_max_right _ _)))
  exact heN.trans (hef.trans hfN.symm)





theorem shiftHat_nonzero_outgoingArc_iff (w : ℕ → Fin 3) (t : ℕ)
    (h : HasFlowLineHits (fun i => w (t + i)))
    (hfinS : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => w (t + i)) n).nextEdge ∧
        ((kmswStage (fun i => w (t + i)) n).west e = v ∨
          (kmswStage (fun i => w (t + i)) n).east e = v)}.Finite)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) (a e f : ℕ)
    (ha : ∃ n, a < (kmswStage (hatCodes (fun i => w (t + i)) h) n).nextVertex)
    (ha0 : a ≠ 0)
    (he : EdgePresent (hatCodes (fun i => w (t + i)) h) e)
    (hf : EdgePresent (hatCodes (fun i => w (t + i)) h) f)
    (hev : edgeWest (hatCodes (fun i => w (t + i)) h) e = a)
    (hfv : edgeWest (hatCodes (fun i => w (t + i)) h) f = a) :
    let u := fun i => w (t + i)
    let φ := fun b => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h b)
      (hatLimitEdgeMap u h b)
    RotationArc (kmswInfRot (hatCodes u h) (hatCodes_inducedFiniteIncidence u h hfinS))
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent (hatCodes u h) d.1)
      (e, false) (f, false) ↔
    RotationArc (kmswInfRot w hfinW)
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
      (φ e, false) (φ f, false) := by
  classical
  let u := fun i => w (t + i)
  let z := hatCodes u h
  let φ := fun b => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h b)
    (hatLimitEdgeMap u h b)
  let V := fun b => limitVertexMap (kmswShiftVertexMapAll w t) u
    (hatLimitVertexMap u h b)
  let hfinH := hatCodes_inducedFiniteIncidence u h hfinS
  have hE := shiftHat_edge_incidence w t h e
  have hF := shiftHat_edge_incidence w t h f
  have hew : edgeWest w (φ e) = V a := hE.1.trans (congrArg V hev)
  have hfw : edgeWest w (φ f) = V a := hF.1.trans (congrArg V hfv)
  have hep : EdgePresent w (φ e) := hE.2.2 he
  have hfp : EdgePresent w (φ f) := hF.2.2 hf
  by_cases hef : e = f
  · subst f
    exact ⟨fun _ => RotationArc.refl _ _ _ ⟨rfl, hep⟩,
      fun _ => RotationArc.refl _ _ _ ⟨rfl, he⟩⟩
  have hinj : Function.Injective φ := by
    intro b c hbc
    have hh := shift_edge_injective w t hbc
    exact congrArg Prod.fst
      (@hatLimitDart_injective u h (b, false) (c, false) (Prod.ext hh rfl))
  obtain ⟨i, _, hiv, _, _⟩ :=
    allocated_nonroot_east_reachable_of_noFreshLeftSource z
      (noFreshLeftSource_hatCodes u h) ⟨a⟩ ha ha0
  have hiw : edgeEast w (φ i) = V a :=
    (shiftHat_edge_incidence w t h i).2.1.trans (congrArg V hiv)
  let SH := {d : ℕ × Bool | (if d.2 then edgeEast z d.1 else edgeWest z d.1) = a}
  let SW := {d : ℕ × Bool | (if d.2 then edgeEast w d.1 else edgeWest w d.1) = V a}
  have hSH := kmsw_darts_at_vertex_finite z hfinH a
  have hSW := kmsw_darts_at_vertex_finite w hfinW (V a)
  have hCH := kmswInfRot_isCycleOn_vertex z hfinH a
  have hCW := kmswInfRot_isCycleOn_vertex w hfinW (V a)
  have hch := cyclic_iff_arc (kmswInfRot z hfinH) hSH.toFinset
    (by simpa only [Set.Finite.coe_toFinset] using hCH)
    (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent z d.1)
    (i, true) (e, false) (f, false)
    (hSH.mem_toFinset.mpr hiv) (by simp only [Bool.true_eq_false, false_and, not_false_eq_true])
    (hSH.mem_toFinset.mpr hev) (hSH.mem_toFinset.mpr hfv) ⟨rfl, he⟩ ⟨rfl, hf⟩
    (kmswInfRot_outgoing_interval_all z hfinH e f (hev.trans hfv.symm) he hf)
    (fun heq => hef (congrArg Prod.fst heq))
  have hcw := cyclic_iff_arc (kmswInfRot w hfinW) hSW.toFinset
    (by simpa only [Set.Finite.coe_toFinset] using hCW)
    (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
    (φ i, true) (φ e, false) (φ f, false)
    (hSW.mem_toFinset.mpr hiw) (by simp only [Bool.true_eq_false, false_and, not_false_eq_true])
    (hSW.mem_toFinset.mpr hew) (hSW.mem_toFinset.mpr hfw) ⟨rfl, hep⟩ ⟨rfl, hfp⟩
    (kmswInfRot_outgoing_interval_all w hfinW _ _ (hew.trans hfw.symm) hep hfp)
    (fun heq => hef (hinj (congrArg Prod.fst heq)))
  exact hch.symm.trans
    ((shiftHatInfRot_cyclicOrder_iff w t h hfinS hfinW
      (i, true) (e, false) (f, false)).trans hcw)

private theorem inverse_chain_arc {α : Type*} (σ : Equiv.Perm α)
    (p : α → Prop) (xs : List α)
    (hc : xs.IsChain (fun a b => σ b = a)) (hm : ∀ a ∈ xs, p a)
    (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length) (hij : i ≤ j) :
    RotationArc σ p xs[j] xs[i] := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    exact RotationArc.refl _ _ _ (hm _ (List.getElem_mem hj))
  | succ j ih =>
    by_cases heq : i = j + 1
    · subst i
      exact RotationArc.refl _ _ _ (hm _ (List.getElem_mem hj))
    have hj' : j < xs.length := by omega
    have hs := (List.isChain_iff_getElem.mp hc) j hj
    have ha : RotationArc σ p xs[j + 1] xs[j] := by
      refine ⟨1, ?_, ?_⟩
      · simpa only [pow_one] using hs
      · intro k hk
        have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl
        · exact hm _ (List.getElem_mem hj)
        · simpa only [pow_one, hs] using hm _ (List.getElem_mem hj')
    exact ha.trans (ih hj' (by omega))

private theorem outgoing_idxOf_le_iff_arc (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ b : ℤ, ∃ n, R w n ≤ b) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) (hv0 : v ≠ 0)
    (e f : ℕ) (he : EdgePresent w e ∧ edgeWest w e = v)
    (hf : EdgePresent w f ∧ edgeWest w f = v) :
    let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv
    es.idxOf e ≤ es.idxOf f ↔
      RotationArc (kmswInfRot w hfin)
        (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
        (f, false) (e, false) := by
  classical
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv
  let σ := kmswInfRot w hfin
  let p := fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1
  have hem : e ∈ es := (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv e).mpr he
  have hfm : f ∈ es := (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv f).mpr hf
  have hchain : es.IsChain (fun a b => σ (b, false) = (a, false)) := by
    unfold es kmswOutgoingEdgesLeftToRight
    rw [dite_eq_right hv0, List.isChain_reverse]
    have hen := kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv hv0
    exact hen.choose_spec.choose_spec.choose_spec.2.2.2.2.1
  have hmark : ∀ d ∈ es.map (fun a => (a, false)), p d := by
    rintro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact ⟨rfl, ((mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv a).mp ha).1⟩
  have hidx (a b : ℕ) (ha : a ∈ es) (hb : b ∈ es)
      (hab : es.idxOf a ≤ es.idxOf b) : RotationArc σ p (b, false) (a, false) := by
    have hc : (es.map (fun c => (c, false))).IsChain (fun d q => σ q = d) :=
      (List.isChain_map _).mpr hchain
    have h := inverse_chain_arc σ p _ hc hmark (es.idxOf a) (es.idxOf b)
      (by simpa only [List.length_map] using List.idxOf_lt_length_iff.mpr ha)
      (by simpa only [List.length_map] using List.idxOf_lt_length_iff.mpr hb) hab
    simpa only [List.getElem_map, List.getElem_idxOf] using h
  change es.idxOf e ≤ es.idxOf f ↔ RotationArc σ p (f, false) (e, false)
  constructor
  · exact hidx e f hem hfm
  · intro harc
    by_contra hle
    have hrev := hidx f e hfm hem (by omega)
    obtain ⟨i, _, hiv⟩ := allocated_vertex_has_incoming_present_edge w hL v hv hv0
    have hS := kmsw_darts_at_vertex_finite w hfin v
    have hC : σ.IsCycleOn (hS.toFinset : Set (ℕ × Bool)) := by
      simpa only [Set.Finite.coe_toFinset] using kmswInfRot_isCycleOn_vertex w hfin v
    obtain ⟨a, ha, hea⟩ := hC.exists_pow_eq
      (show (i, true) ∈ hS.toFinset from hS.mem_toFinset.mpr hiv)
      (show (e, false) ∈ hS.toFinset from hS.mem_toFinset.mpr he.2)
    obtain ⟨b, hb, hfb⟩ := hC.exists_pow_eq
      (show (i, true) ∈ hS.toFinset from hS.mem_toFinset.mpr hiv)
      (show (f, false) ∈ hS.toFinset from hS.mem_toFinset.mpr hf.2)
    have hpos := arc_iff_positions σ hS.toFinset
      (by simpa only [Set.Finite.coe_toFinset] using hC) p
      (i, true) (e, false) (f, false) (hS.mem_toFinset.mpr hiv)
      (by simp only [p, Bool.true_eq_false, false_and, not_false_eq_true])
      (hS.mem_toFinset.mpr he.2) (hS.mem_toFinset.mpr hf.2) ⟨rfl, he.1⟩ ⟨rfl, hf.1⟩
      (Or.inl hrev) a b ha hb hea hfb
    have hneg := arc_iff_positions σ hS.toFinset
      (by simpa only [Set.Finite.coe_toFinset] using hC) p
      (i, true) (f, false) (e, false) (hS.mem_toFinset.mpr hiv)
      (by simp only [p, Bool.true_eq_false, false_and, not_false_eq_true])
      (hS.mem_toFinset.mpr hf.2) (hS.mem_toFinset.mpr he.2) ⟨rfl, hf.1⟩ ⟨rfl, he.1⟩
      (Or.inl harc) b a hb ha hfb hea
    have hab : a = b := by have := hpos.mp hrev; have := hneg.mp harc; omega
    have hef : e = f := congrArg Prod.fst (hea.symm.trans (hab ▸ hfb))
    exact hle (hef ▸ le_refl _)











theorem shiftHat_nonzero_outgoing_idxOf_lt_iff (w : ℕ → Fin 3) (t : ℕ)
    (h : HasFlowLineHits (fun i => w (t + i)))
    (hfinS : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => w (t + i)) n).nextEdge ∧
        ((kmswStage (fun i => w (t + i)) n).west e = v ∨
          (kmswStage (fun i => w (t + i)) n).east e = v)}.Finite)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hLH : ∀ j, 0 ≤ L (hatCodes (fun i => w (t + i)) h) j)
    (hTH : Filter.Tendsto (L (hatCodes (fun i => w (t + i)) h))
      Filter.atTop Filter.atTop)
    (hRH : ∀ b : ℤ, ∃ n, R (hatCodes (fun i => w (t + i)) h) n ≤ b)
    (hLW : ∀ j, 0 ≤ L w j)
    (hTW : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hRW : ∀ b : ℤ, ∃ n, R w n ≤ b)
    (a e f : ℕ) (ha0 : a ≠ 0)
    (he : EdgePresent (hatCodes (fun i => w (t + i)) h) e)
    (hf : EdgePresent (hatCodes (fun i => w (t + i)) h) f)
    (hev : edgeWest (hatCodes (fun i => w (t + i)) h) e = a)
    (hfv : edgeWest (hatCodes (fun i => w (t + i)) h) f = a) :
    let u := fun i => w (t + i)
    let z := hatCodes u h
    let hfinH := hatCodes_inducedFiniteIncidence u h hfinS
    let φ := fun b => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h b)
      (hatLimitEdgeMap u h b)
    let φv := fun b => limitVertexMap (kmswShiftVertexMapAll w t) u
      (hatLimitVertexMap u h b)
    let es := kmswOutgoingEdgesLeftToRight z hfinH hLH hTH hRH a
      (kmsw_vertex_allocated_of_finite_incidence z hfinH a)
    let fs := kmswOutgoingEdgesLeftToRight w hfinW hLW hTW hRW (φv a)
      (kmsw_vertex_allocated_of_finite_incidence w hfinW (φv a))
    es.idxOf e < es.idxOf f ↔ fs.idxOf (φ e) < fs.idxOf (φ f) := by
  classical
  let u := fun i => w (t + i)
  let z := hatCodes u h
  let hfinH := hatCodes_inducedFiniteIncidence u h hfinS
  let φ := fun b => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h b)
    (hatLimitEdgeMap u h b)
  let V := fun b => limitVertexMap (kmswShiftVertexMapAll w t) u
    (hatLimitVertexMap u h b)
  let ha := kmsw_vertex_allocated_of_finite_incidence z hfinH a
  let hv := kmsw_vertex_allocated_of_finite_incidence w hfinW (V a)
  have hE := shiftHat_edge_incidence w t h e
  have hF := shiftHat_edge_incidence w t h f
  have hep : EdgePresent w (φ e) := hE.2.2 he
  have hfp : EdgePresent w (φ f) := hF.2.2 hf
  have hew : edgeWest w (φ e) = V a := hE.1.trans (congrArg V hev)
  have hfw : edgeWest w (φ f) = V a := hF.1.trans (congrArg V hfv)
  obtain ⟨i, hip, hiv⟩ := allocated_vertex_has_incoming_present_edge z hLH a ha ha0
  have hi := shiftHat_edge_incidence w t h i
  have hv0 : V a ≠ 0 := by
    have hine := zero_no_incoming_present_edge w hLW (φ i) (hi.2.2 hip)
    exact fun hz => hine (hi.2.1.trans ((congrArg V hiv).trans hz))
  have hord := (outgoing_idxOf_le_iff_arc z hfinH hLH hTH hRH a ha ha0
    f e ⟨hf, hfv⟩ ⟨he, hev⟩).trans
    ((shiftHat_nonzero_outgoingArc_iff w t h hfinS hfinW a e f ha ha0
      he hf hev hfv).trans
      (outgoing_idxOf_le_iff_arc w hfinW hLW hTW hRW (V a) hv hv0
        (φ f) (φ e) ⟨hfp, hfw⟩ ⟨hep, hew⟩).symm)
  exact (lt_iff_not_ge.trans (not_congr hord)).trans lt_iff_not_ge.symm





theorem shiftHat_source_rightBoundary (w : ℕ → Fin 3) (t : ℕ)
    (h : HasFlowLineHits (fun i => w (t + i))) :
    let u := fun i => w (t + i)
    let φ := fun b => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h b)
      (hatLimitEdgeMap u h b)
    let φv := fun b => limitVertexMap (kmswShiftVertexMapAll w t) u
      (hatLimitVertexMap u h b)
    φ (kmswRightBoundaryEdge (hatCodes u h) 0) = act w t ∧
      φv 0 = activeInitial w t := by
  let u := fun i => w (t + i)
  let φ := fun b => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h b)
    (hatLimitEdgeMap u h b)
  have hroot : φ 0 = act w t := by
    dsimp only [φ]
    rw [(hat_root_correspondence u h).2.2.2]
    rfl
  refine ⟨?_, ?_⟩
  · rw [kmswRightBoundaryEdge_zero]
    exact hroot
  · have hi := (shiftHat_edge_incidence w t h 0).1
    have hz : edgeWest (hatCodes u h) 0 = 0 := rfl
    rw [hz] at hi
    exact hi.symm.trans (congrArg (edgeWest w) hroot)







theorem shiftHat_sourceCut_obstruction_first_up (w : ℕ → Fin 3) (hw : w 0 = 1)
    (h : HasFlowLineHits (fun i => w (1 + i))) :
    let u := fun i => w (1 + i)
    let φ := fun b => kmswShiftEdgeMapAll w 1 (hatLimitEdgeMap u h b)
      (hatLimitEdgeMap u h b)
    let φv := fun b => limitVertexMap (kmswShiftVertexMapAll w 1) u
      (hatLimitVertexMap u h b)
    φv 0 = 0 ∧
      φ (kmswRightBoundaryEdge (hatCodes u h) 0) ≠ kmswRightBoundaryEdge w 0 := by
  have hroot := shiftHat_source_rightBoundary w 1 h
  have hact : act w 1 = 1 := by
    change (kmswStep kmswInit (w 0)).active = 1
    rw [hw]
    rfl
  have hwest : activeInitial w 1 = 0 := by
    have he := (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl 1))).1.symm
    have hstage : (kmswStage w 1).west (act w 1) = 0 := by
      change (kmswStep kmswInit (w 0)).west (kmswStep kmswInit (w 0)).active = 0
      rw [hw]
      rfl
    exact he.trans hstage
  refine ⟨hroot.2.trans hwest, ?_⟩
  intro heq
  have hc := hroot.1.symm.trans (heq.trans (kmswRightBoundaryEdge_zero w))
  rw [hact] at hc
  exact Nat.one_ne_zero hc

end DirectedDistances.KMSW
