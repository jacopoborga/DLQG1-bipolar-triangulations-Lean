module

public import DirectedDistances.KMSW.WholePlaneCrossRunRotation
import DirectedDistances.KMSW.KMSWWindowPatchInjective

/-! Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. -/

public section
namespace DirectedDistances.KMSW


open DirectedDistances.PlanarMap

private def value {n : ℕ} (d : StageDart n) : ℕ × Bool := (d.1.val, d.2)

private theorem value_injective (n : ℕ) : Function.Injective (@value n) := by
  intro a b h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (congrArg (fun z : ℕ × Bool => z.2) h)

private theorem chain_ranks (G : State) (r : ℕ → ℚ) (e : ℕ)
    (es : List ℕ) (hc : WestEastChain G (e :: es))
    (hr : ∀ a ∈ e :: es, r (G.west a) < r (G.east a)) :
    (r (G.west e) :: (e :: es).map (fun a => r (G.east a))).Pairwise (· < ·) := by
  induction es generalizing e with
  | nil => simpa using hr e (by simp)
  | cons f fs ih =>
    have hchain := List.isChain_cons_cons.mp hc
    have hf := ih f hchain.2 (fun a ha => hr a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons, List.pairwise_cons_cons_iff_of_trans]
    refine ⟨hr e (by simp), ?_⟩
    rw [hchain.1]
    simpa only [List.map_cons, List.pairwise_cons_cons_iff_of_trans] using hf

private theorem boundary_at_one (u : ℕ → Fin 3) (m : ℕ) :
    (∀ a es, (kmswStage u m).UL ++ (kmswStage u m).UR = a :: es →
      (kmswStage u m).west a ≠ 1) ∧
    (∀ e ∈ (kmswStage u m).LL ++ (kmswStage u m).LR,
      (kmswStage u m).east e = 1 → e = 0) := by
  let F := kmswStage u m
  have hroot : 0 ∈ F.LL ++ F.LR := by
    apply List.mem_append_right
    rw [kmswStage_LR_eq]
    exact List.mem_map.mpr ⟨0, List.mem_filter.mpr
      ⟨List.mem_range.mpr (by omega), by simp⟩, rfl⟩
  have hlow : F.LL ++ F.LR ≠ [] := by
    intro h
    rw [h] at hroot
    exact List.not_mem_nil hroot
  obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hlow
  have hc := (kmswStage_boundary_chain_invariant u m).2.1
  have hpr := chain_ranks F (kmswStageRank u m) b bs (hb ▸ hc) (by
    intro a ha
    exact kmswStageRank_strict u m a
      ((kmswStage_boundary_ids_lt_nextEdge u m).2 a (by
        change a ∈ F.UL ++ F.UR ++ F.LL ++ F.LR
        have hm : a ∈ F.LL ++ F.LR := hb.symm ▸ ha
        simp only [List.mem_append] at hm ⊢
        tauto)))
  have hn : (F.west b :: (b :: bs).map F.east).Nodup := by
    have hp : ((F.west b :: (b :: bs).map F.east).map
        (kmswStageRank u m)).Pairwise (· < ·) := by
      simpa only [List.map_cons, List.map_map, Function.comp_def] using hpr
    have hv := List.pairwise_map.mp hp
    exact hv.imp (fun h heq => (ne_of_lt h) (congrArg (kmswStageRank u m) heq))
  have h1 : (1 : ℕ) ∈ (b :: bs).map F.east := by
    exact List.mem_map.mpr ⟨0, hb ▸ hroot, (initial_edge_endpoints u m).2⟩
  constructor
  · intro a es ha heq
    have hs := (kmswStage_boundary_chain_invariant u m).2.2.1
    change boundaryStart F (F.UL ++ F.UR) = boundaryStart F (F.LL ++ F.LR) at hs
    rw [ha, hb] at hs
    have hab : F.west a = F.west b := Option.some.inj hs
    exact (List.nodup_cons.mp hn).1 (hab ▸ heq.symm ▸ h1)
  · intro e he heast
    apply List.inj_on_of_nodup_map (List.nodup_cons.mp hn).2
      (hb ▸ he) (hb ▸ hroot)
    exact heast.trans (initial_edge_endpoints u m).2.symm

private theorem formPerm_adjacent {α : Type*} [DecidableEq α]
    (a b : List α) (x y : α) (hn : (a ++ x :: y :: b).Nodup) :
    (a ++ x :: y :: b).formPerm x = y := by
  have hr := List.isRotated_append (l := a) (l' := x :: y :: b)
  rw [List.formPerm_eq_of_isRotated hn hr]
  exact List.formPerm_apply_head x y (b ++ a) (by
    simpa only [List.cons_append] using hr.nodup_iff.mp hn)

private theorem formPerm_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have him : i < (l.map f).length := by simpa only [List.length_map] using hi
  have hget : (l.map f)[i]'him = f l[i] := List.getElem_map f
  rw [← hget, List.formPerm_apply_getElem _ (hl.map hf),
    List.formPerm_apply_getElem _ hl]
  simp only [List.length_map, List.getElem_map]

private theorem face_of_adjacent (u : ℕ → Fin 3) (m : ℕ)
    (x y : StageDart (kmswStage u m).nextEdge) (a b : List (ℕ × Bool))
    (hw : stageOuterWordVal u m = a ++ value x :: value y :: b) :
    (kmswMap u m).faceSucc x = y := by
  have hx : x ∈ stageOuterWord u m := by
    have hm : value x ∈ (stageOuterWord u m).map value := by
      change value x ∈ stageOuterWordVal u m
      rw [hw]
      simp only [List.mem_append, List.mem_cons]
      tauto
    obtain ⟨z, hz, he⟩ := List.mem_map.mp hm
    exact value_injective _ he ▸ hz
  apply value_injective _
  rw [stageOuterWord_faceSucc u m x hx,
    ← formPerm_map value (value_injective _) _ (stageOuterWord_nodup u m) x hx]
  change (stageOuterWordVal u m).formPerm (value x) = value y
  rw [hw]
  apply formPerm_adjacent
  rw [← hw]
  exact (stageOuterWord_nodup u m).map (value_injective _)

private theorem predecessor_split {α : Type*} (l : List α) (x : α)
    (hx : x ∈ l) (hh : ∀ b, l ≠ x :: b) :
    ∃ a p b, l = a ++ p :: x :: b := by
  obtain ⟨a, b, ha⟩ := List.mem_iff_append.mp hx
  have hne : a ≠ [] := by
    intro he
    apply hh b
    simpa only [he, List.nil_append] using ha
  refine ⟨a.dropLast, a.getLast hne, b, ?_⟩
  exact ha.trans (by
    simpa only [List.append_assoc, List.singleton_append] using
      congrArg (fun t => t ++ x :: b) (List.dropLast_append_getLast hne).symm)

private theorem rot_face (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage u m).nextEdge) :
    stageRot u m ((kmswMap u m).faceSucc d) = edgeFlip _ d := by
  exact (stageRot u m).apply_symm_apply _

private theorem upper_rot_map (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = 1)
    (hb : d.2 = false)
    (he : d.1.val ∈ (kmswStage (fun i => w (s + i)) m).UL ++
      (kmswStage (fun i => w (s + i)) m).UR) :
    stageRot w (s + m) (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m (stageRot (fun i => w (s + i)) m d) := by
  let u := fun i => w (s + i)
  let F := kmswStage u m
  let G := kmswStage w (s + m)
  let data := kmswWindowPatchData w s m
  let f := fun e : ℕ => (e, false)
  obtain ⟨a, p, b, hl⟩ := predecessor_split (F.UL ++ F.UR) d.1.val he (by
    intro b hh
    exact (boundary_at_one u m).1 d.1.val b hh (by
      simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hd))
  have hp : p < F.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u m).2 p (by
    have hm : p ∈ F.UL ++ F.UR := by rw [hl]; simp
    simp only [List.mem_append] at hm ⊢
    tauto)
  let x : StageDart F.nextEdge := (⟨p, hp⟩, false)
  have hw : stageOuterWordVal u m = a.map f ++ value x :: value d ::
      (b.map f ++ F.LR.reverse.map (fun e => (e, true)) ++
        F.LL.reverse.map (fun e => (e, true))) := by
    rw [stageOuterWordVal_eq_runs]
    rw [← List.map_append, hl]
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
      value, x, f, hb, F]
  have hf := face_of_adjacent u m x d _ _ hw
  have hrel := kmswWindowPatchData_rel w s m
  have hupper : G.UL ++ G.UR = data.A ++ (F.UL ++ F.UR).map data.φ ++ data.B := by
    rw [hrel.ul, hrel.ur, List.map_append]
    simp only [List.append_assoc, data, F, u]
  have hwG : stageOuterWordVal w (s + m) =
      (data.A.map f ++ (a.map data.φ).map f) ++
        value (kmswWindowDartMap w s m x) :: value (kmswWindowDartMap w s m d) ::
          ((b.map data.φ).map f ++ data.B.map f ++
            G.LR.reverse.map (fun e => (e, true)) ++
              G.LL.reverse.map (fun e => (e, true))) := by
    rw [stageOuterWordVal_eq_runs, ← List.map_append, hupper, hl]
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
      value, kmswWindowDartMap, data, x, f, hb, G]
  have hg := face_of_adjacent w (s + m) (kmswWindowDartMap w s m x)
    (kmswWindowDartMap w s m d) _ _ hwG
  have hloc := rot_face u m x
  have hglob := rot_face w (s + m) (kmswWindowDartMap w s m x)
  rw [hf] at hloc
  rw [hg] at hglob
  rw [hloc, hglob]
  exact kmswWindowDartMap_edgeFlip w s m x


private theorem rot_map_except_root (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = 1)
    (hne : value d ≠ (0, true)) :
    stageRot w (s + m) (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m (stageRot (fun i => w (s + i)) m d) := by
  let u := fun i => w (s + i)
  rcases stage_dart_partition u m d with ho | ⟨j, ⟨hj, hmem⟩, _⟩
  · rcases (stageOuterWord_mem_iff u m d).mp ho with ⟨hb, he⟩ | ⟨hb, he⟩
    · exact upper_rot_map w s m d hd hb (List.mem_append.mpr he)
    · have hlow : d.1.val ∈ (kmswStage u m).LL ++ (kmswStage u m).LR :=
        List.mem_append.mpr he.symm
      have hend : (kmswStage u m).east d.1.val = 1 := by
        simpa only [stageEndpoint, hb, ↓reduceIte] using hd
      exact (hne (Prod.ext ((boundary_at_one u m).2 _ hlow hend) hb)).elim
  · exact kmswWindowDartMap_rot w s m d
      (List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes u m j).mpr hj, hmem⟩)

private theorem rot_endpoint (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) :
    stageEndpoint (kmswStage w m) (stageRot w m d) =
      stageEndpoint (kmswStage w m) d := by
  exact ((stageRot_sameCycle_iff_endpoint_eq w m _ _).mp ⟨1, rfl⟩).symm

private theorem symm_endpoint (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) :
    stageEndpoint (kmswStage w m) ((stageRot w m).symm d) =
      stageEndpoint (kmswStage w m) d := by
  exact (stageRot_sameCycle_iff_endpoint_eq w m _ _).mp
    ⟨1, (stageRot w m).apply_symm_apply d⟩

private theorem symm_pow_endpoint (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) (k : ℕ) :
    stageEndpoint (kmswStage w m) (((stageRot w m).symm ^ k) d) =
      stageEndpoint (kmswStage w m) d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, symm_endpoint, ih]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Finite first return identifies the inverse successor at vertex 1,
including all geometric darts of missing edges. No completeness assumption is needed. -/
theorem kmswWindowDartMap_symm_firstReturn_at_one (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = 1) :
    ∃ k : ℕ, 0 < k ∧
      ((stageRot w (s + m)).symm ^ k) (kmswWindowDartMap w s m d) =
        kmswWindowDartMap w s m ((stageRot (fun i => w (s + i)) m).symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((stageRot w (s + m)).symm ^ j) (kmswWindowDartMap w s m d) ∉
          Set.range (kmswWindowDartMap w s m) := by
  classical
  let u := fun i => w (s + i)
  let I := kmswWindowDartMap w s m
  let ρ := stageRot u m
  let τ := stageRot w (s + m)
  let e₀ := ρ.symm d
  have he₀ : stageEndpoint (kmswStage u m) e₀ = 1 :=
    (symm_endpoint u m d).trans hd
  by_cases hroot : value e₀ ≠ (0, true)
  · have hc := rot_map_except_root w s m e₀ he₀ hroot
    have heq : τ.symm (I d) = I e₀ := by
      apply τ.injective
      exact (τ.apply_symm_apply _).trans
        (hc.trans (congrArg I (ρ.apply_symm_apply d))).symm
    refine ⟨1, by omega, ?_, ?_⟩
    · simpa only [pow_one] using heq
    · intro j hj hjk
      omega
  · have hroot : value e₀ = (0, true) := not_ne_iff.mp hroot
    obtain ⟨n, hn, _, hperiod⟩ := (Equiv.Perm.SameCycle.refl τ.symm (I d)).exists_pow_eq''
    have hex : ∃ k : ℕ, 0 < k ∧ (τ.symm ^ k) (I d) ∈ Set.range I :=
      ⟨n, hn, d, hperiod.symm⟩
    let k := Nat.find hex
    obtain ⟨hk, e, he⟩ := Nat.find_spec hex
    have hgap : ∀ j : ℕ, 0 < j → j < k → (τ.symm ^ j) (I d) ∉ Set.range I := by
      intro j hj hjk hmem
      exact Nat.find_min hex hjk ⟨hj, hmem⟩
    have hvertex : stageEndpoint (kmswStage u m) e = 1 := by
      have hmap (z : StageDart (kmswStage u m).nextEdge) :
          stageEndpoint (kmswStage w (s + m)) (I z) =
            kmswWindowPatchVertexMap w s m (stageEndpoint (kmswStage u m) z) :=
        kmswWindowDartMap_vertex w s m z
      have hv := symm_pow_endpoint w (s + m) (I d) k
      rw [← he, hmap, hmap] at hv
      have heq := kmswWindowPatchVertexMap_injOn w s m
        (stageEndpoint_lt_nextVertex u m e) (stageEndpoint_lt_nextVertex u m d) hv
      exact heq.trans hd
    have hee : e = e₀ := by
      by_contra hne
      have heroot : value e ≠ (0, true) := by
        intro hr
        exact hne (value_injective _ (hr.trans hroot.symm))
      have hc := rot_map_except_root w s m e hvertex heroot
      have hprev : (τ.symm ^ (k - 1)) (I d) = I (ρ e) := by
        have hstep : τ ((τ.symm ^ k) (I d)) = (τ.symm ^ (k - 1)) (I d) := by
          conv_lhs =>
            rw [show k = (k - 1) + 1 by omega, pow_succ',
              Equiv.Perm.mul_apply, τ.apply_symm_apply]
        rw [← he, hc] at hstep
        exact hstep.symm
      have hk1 : k = 1 := by
        by_contra hnot
        exact hgap (k - 1) (by omega) (by omega) ⟨ρ e, hprev.symm⟩
      have hedge : d = ρ e := by
        apply kmswWindowDartMap_injective w s m
        simpa only [hk1, Nat.sub_self, pow_zero, Equiv.Perm.one_apply] using hprev
      apply hne
      exact (ρ.symm_apply_apply e).symm.trans (congrArg ρ.symm hedge).symm
    exact ⟨k, hk, by simpa only [hee] using he.symm, hgap⟩


private def base (u : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast u d.1 else edgeWest u d.1

private theorem stage_base (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage u m).nextEdge) :
    stageEndpoint (kmswStage u m) d = base u (value d) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq u d.1.isLt
  cases hb : d.2 <;> simp only [stageEndpoint, base, value, hb,
    Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem complete_exists (u : ℕ → Fin 3) (hfin : KMSWFiniteIncidence u)
    (v : ℕ) : ∃ m, kmswVertexComplete u m v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  exact (hB ⟨e, kmsw_edge_allocated_by_self u e, he⟩).trans_lt
    (kmsw_edge_allocated_by_self u B)

private theorem complete_mono (u : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (hc : kmswVertexComplete u n v) : kmswVertexComplete u m v := by
  intro e he
  exact (hc e he).trans_le (kmswStage_nextEdge_mono u hnm)

private theorem inf_pow_stage (u : ℕ → Fin 3) (hfin : KMSWFiniteIncidence u)
    (m : ℕ) (d : StageDart (kmswStage u m).nextEdge)
    (hc : kmswVertexComplete u m (stageEndpoint (kmswStage u m) d)) (k : ℕ) :
    ((kmswInfRot u hfin).symm ^ k) (value d) =
      value (((stageRot u m).symm ^ k) d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact kmswInfRot_symm_eq_stage u hfin m _ (by
      rw [symm_pow_endpoint]
      exact hc)

private theorem trans_base (W : ℤ → Fin 3) (N M : ℕ) (hNM : N ≤ M)
    (d : ℕ × Bool) :
    base (shiftedStream W M) (wholePlaneDartTrans W N M hNM d) =
      wholePlaneVertexTrans W N M hNM (base (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [base, wholePlaneDartTrans, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeTrans_west W N M hNM d.1
  · exact wholePlaneEdgeTrans_east W N M hNM d.1

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Cross-run inverse first return at the root terminal vertex. -/
theorem wholePlaneInfRot_symm_firstReturn_at_one (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M)
    (hN : KMSWFiniteIncidence (shiftedStream W N))
    (hM : KMSWFiniteIncidence (shiftedStream W M)) (d : ℕ × Bool)
    (hd : (if d.2 then edgeEast (shiftedStream W N) d.1
      else edgeWest (shiftedStream W N) d.1) = 1) :
    ∃ k : ℕ, 0 < k ∧
      ((kmswInfRot (shiftedStream W M) hM).symm ^ k)
        (wholePlaneDartTrans W N M hNM d) =
          wholePlaneDartTrans W N M hNM
            ((kmswInfRot (shiftedStream W N) hN).symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswInfRot (shiftedStream W M) hM).symm ^ j)
          (wholePlaneDartTrans W N M hNM d) ∉
            Set.range (wholePlaneDartTrans W N M hNM) := by
  let w := shiftedStream W M
  let s := M - N
  let u := fun i => w (s + i)
  have hu : u = shiftedStream W N := shiftedStream_shift W N M hNM
  let hU : KMSWFiniteIncidence u := hu.symm ▸ hN
  let I := wholePlaneDartTrans W N M hNM
  obtain ⟨n, hn⟩ := complete_exists u hU 1
  obtain ⟨q, hq⟩ := complete_exists w hM (wholePlaneVertexTrans W N M hNM 1)
  let m := max n (max q d.1)
  have hnm : n ≤ m := Nat.le_max_left _ _
  have hqm : q ≤ s + m := by
    have := (Nat.le_max_left q d.1).trans (Nat.le_max_right n (max q d.1))
    omega
  have hdm : d.1 ≤ m :=
    (Nat.le_max_right q d.1).trans (Nat.le_max_right n (max q d.1))
  have hcs := complete_mono u hnm hn
  have hcw := complete_mono w hqm hq
  have halloc : d.1 < (kmswStage u m).nextEdge :=
    (kmsw_edge_allocated_by_self u d.1).trans_le (kmswStage_nextEdge_mono u hdm)
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, halloc⟩, d.2)
  let y := kmswWindowDartMap w s m x
  have hmap (z : StageDart (kmswStage u m).nextEdge) :
      value (kmswWindowDartMap w s m z) = I (value z) := by
    apply Prod.ext
    · change (kmswWindowPatchData w s m).φ z.1.val = kmswWindowEdgeMapInf w s z.1.val
      exact (kmswWindowEdgeMapInf_eq_stage w s m z.1.val z.1.isLt).symm
    · rfl
  have hx : stageEndpoint (kmswStage u m) x = 1 := by
    rw [stage_base]
    change base u d = 1
    rw [hu]
    exact hd
  have hcx : kmswVertexComplete u m (stageEndpoint (kmswStage u m) x) := hx ▸ hcs
  have hy : value y = I d := hmap x
  have hybase : stageEndpoint (kmswStage w (s + m)) y =
      wholePlaneVertexTrans W N M hNM 1 := by
    calc
      stageEndpoint (kmswStage w (s + m)) y = base w (value y) := stage_base w _ y
      _ = base w (I d) := congrArg (base w) hy
      _ = wholePlaneVertexTrans W N M hNM (base (shiftedStream W N) d) :=
        trans_base W N M hNM d
      _ = wholePlaneVertexTrans W N M hNM 1 := congrArg _ hd
  have hcy : kmswVertexComplete w (s + m) (stageEndpoint (kmswStage w (s + m)) y) := by
    rw [hybase]
    exact hcw
  have hiter (j : ℕ) : ((kmswInfRot w hM).symm ^ j) (I d) =
      value (((stageRot w (s + m)).symm ^ j) y) := by
    calc
      ((kmswInfRot w hM).symm ^ j) (I d) =
          ((kmswInfRot w hM).symm ^ j) (value y) := congrArg _ hy.symm
      _ = value (((stageRot w (s + m)).symm ^ j) y) :=
        inf_pow_stage w hM (s + m) y hcy j
  obtain ⟨k, hk, hreturn, hgap⟩ :=
    kmswWindowDartMap_symm_firstReturn_at_one w s m x hx
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hiter, hreturn, hmap]
    have he : (kmswInfRot u hU).symm d = value ((stageRot u m).symm x) :=
      kmswInfRot_symm_eq_stage u hU m x hcx
    have he' : (kmswInfRot (shiftedStream W N) hN).symm d =
        value ((stageRot u m).symm x) := by
      simpa only [hu] using he
    exact congrArg I he'.symm
  · intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    have he' : I e = ((kmswInfRot w hM).symm ^ j) (I d) := he
    have hep : base w (I e) = base w (I d) := by
      calc
        base w (I e) = base w (value (((stageRot w (s + m)).symm ^ j) y)) :=
          congrArg (base w) (he'.trans (hiter j))
        _ = stageEndpoint (kmswStage w (s + m))
            (((stageRot w (s + m)).symm ^ j) y) := (stage_base w _ _).symm
        _ = stageEndpoint (kmswStage w (s + m)) y := symm_pow_endpoint w _ y j
        _ = base w (I d) := (stage_base w _ y).trans (congrArg (base w) hy)
    have heone : base (shiftedStream W N) e = 1 := by
      change base (shiftedStream W M) (wholePlaneDartTrans W N M hNM e) =
        base (shiftedStream W M) (wholePlaneDartTrans W N M hNM d) at hep
      rw [trans_base, trans_base] at hep
      exact (wholePlaneVertexTrans_injective W N M hNM hep).trans hd
    have heb : e.1 < (kmswStage u m).nextEdge := by
      apply hcs e.1
      have heu : base u e = 1 := by rw [hu]; exact heone
      cases hb : e.2
      · exact Or.inl (by simpa only [base, hb, Bool.false_eq_true, ↓reduceIte] using heu)
      · exact Or.inr (by simpa only [base, hb, ↓reduceIte] using heu)
    let z : StageDart (kmswStage u m).nextEdge := (⟨e.1, heb⟩, e.2)
    apply hgap j hj hjk
    refine ⟨z, value_injective _ ?_⟩
    exact (hmap z).trans (he.trans (hiter j))

open MeasureTheory RandomWalk

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Simultaneous all-run ambient rightmostness at the root terminal. -/
theorem wholePlaneIID_ae_rightmost_at_root_terminal :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∃ H : WholePlaneRotationHypothesis W,
      ∀ N : ℕ, wholePlaneRightmostOutgoingAt W H (wholePlaneVertexι W N 1)
        (wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) 1)) := by
  filter_upwards [wholePlaneIID_ae_rightmost_of_cross_run_induced_rotation] with W h
  obtain ⟨H, hH⟩ := h
  refine ⟨H, hH ?_⟩
  intro N M hNM d hd
  exact wholePlaneInfRot_symm_firstReturn_at_one W N M hNM (H.1 N) (H.1 M) d hd

end DirectedDistances.KMSW
