module

public import DirectedDistances.KMSW.WholePlaneCrossRunReturnId
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

private theorem boundary_at_lower_edge (u : ℕ → Fin 3) (m r : ℕ)
    (hr : r ∈ (kmswStage u m).LL ++ (kmswStage u m).LR) :
    (∀ a es, (kmswStage u m).UL ++ (kmswStage u m).UR = a :: es →
      (kmswStage u m).west a ≠ (kmswStage u m).east r) ∧
    (∀ e ∈ (kmswStage u m).LL ++ (kmswStage u m).LR,
      (kmswStage u m).east e = (kmswStage u m).east r → e = r) := by
  let F := kmswStage u m
  have hroot : r ∈ F.LL ++ F.LR := hr
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
  have h1 : F.east r ∈ (b :: bs).map F.east := by
    exact List.mem_map.mpr ⟨r, hb ▸ hroot, rfl⟩
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
    exact heast

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

private theorem upper_rot_map (w : ℕ → Fin 3) (s m r : ℕ)
    (hr : r ∈ (kmswStage (fun i => w (s + i)) m).LL ++
      (kmswStage (fun i => w (s + i)) m).LR)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d =
      (kmswStage (fun i => w (s + i)) m).east r)
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
    exact (boundary_at_lower_edge u m r hr).1 d.1.val b hh (by
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

private theorem rot_map_except_lower (w : ℕ → Fin 3) (s m r : ℕ)
    (hr : r ∈ (kmswStage (fun i => w (s + i)) m).LL ++
      (kmswStage (fun i => w (s + i)) m).LR)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d =
      (kmswStage (fun i => w (s + i)) m).east r)
    (hne : value d ≠ (r, true)) :
    stageRot w (s + m) (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m (stageRot (fun i => w (s + i)) m d) := by
  let u := fun i => w (s + i)
  rcases stage_dart_partition u m d with ho | ⟨j, ⟨hj, hmem⟩, _⟩
  · rcases (stageOuterWord_mem_iff u m d).mp ho with ⟨hb, he⟩ | ⟨hb, he⟩
    · exact upper_rot_map w s m r hr d hd hb (List.mem_append.mpr he)
    · have hlow : d.1.val ∈ (kmswStage u m).LL ++ (kmswStage u m).LR :=
        List.mem_append.mpr he.symm
      have hend : (kmswStage u m).east d.1.val = (kmswStage u m).east r := by
        simpa only [stageEndpoint, hb, ↓reduceIte] using hd
      exact (hne (Prod.ext ((boundary_at_lower_edge u m r hr).2 _ hlow hend) hb)).elim
  · exact kmswWindowDartMap_rot w s m d
      (List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes u m j).mpr hj, hmem⟩)

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
not the paper result. Finite first return at every lower-boundary terminal vertex.
The lower chain has distinct vertices; rotation commutes except at its unique incoming
lower-boundary dart. Geometric darts of missing edges remain included. -/
theorem kmswWindowDartMap_symm_firstReturn_at_lower_edge (w : ℕ → Fin 3) (s m r : ℕ)
    (hr : r ∈ (kmswStage (fun i => w (s + i)) m).LL ++
      (kmswStage (fun i => w (s + i)) m).LR)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d =
      (kmswStage (fun i => w (s + i)) m).east r) :
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
  have he₀ : stageEndpoint (kmswStage u m) e₀ = (kmswStage u m).east r :=
    (symm_endpoint u m d).trans hd
  by_cases hroot : value e₀ ≠ (r, true)
  · have hc := rot_map_except_lower w s m r hr e₀ he₀ hroot
    have heq : τ.symm (I d) = I e₀ := by
      apply τ.injective
      exact (τ.apply_symm_apply _).trans
        (hc.trans (congrArg I (ρ.apply_symm_apply d))).symm
    refine ⟨1, by omega, ?_, ?_⟩
    · simpa only [pow_one] using heq
    · intro j hj hjk
      omega
  · have hroot : value e₀ = (r, true) := not_ne_iff.mp hroot
    obtain ⟨n, hn, _, hperiod⟩ := (Equiv.Perm.SameCycle.refl τ.symm (I d)).exists_pow_eq''
    have hex : ∃ k : ℕ, 0 < k ∧ (τ.symm ^ k) (I d) ∈ Set.range I :=
      ⟨n, hn, d, hperiod.symm⟩
    let k := Nat.find hex
    obtain ⟨hk, e, he⟩ := Nat.find_spec hex
    have hgap : ∀ j : ℕ, 0 < j → j < k → (τ.symm ^ j) (I d) ∉ Set.range I := by
      intro j hj hjk hmem
      exact Nat.find_min hex hjk ⟨hj, hmem⟩
    have hvertex : stageEndpoint (kmswStage u m) e = (kmswStage u m).east r := by
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
      have heroot : value e ≠ (r, true) := by
        intro hr
        exact hne (value_injective _ (hr.trans hroot.symm))
      have hc := rot_map_except_lower w s m r hr e hvertex heroot
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
not the paper result. Cross-run inverse first return at every right-boundary terminal.
Unboundedness supplies the record edges; both finite-incidence hypotheses are explicit. -/
theorem wholePlaneInfRot_symm_firstReturn_at_right_boundary (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M)
    (hN : KMSWFiniteIncidence (shiftedStream W N))
    (hM : KMSWFiniteIncidence (shiftedStream W M))
    (hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a) (i : ℕ) (d : ℕ × Bool)
    (hd : (if d.2 then edgeEast (shiftedStream W N) d.1
      else edgeWest (shiftedStream W N) d.1) =
        edgeEast (shiftedStream W N) (kmswRightBoundaryEdge (shiftedStream W N) i)) :
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
  let r := kmswRightBoundaryEdge u i
  let v := edgeEast u r
  have hRu : ∀ a : ℤ, ∃ n, R u n ≤ a := by rw [hu]; exact hR
  obtain ⟨B, hB⟩ := kmswStage_LR_getElem?_eventually u hRu i
  obtain ⟨n, hn⟩ := complete_exists u hU v
  obtain ⟨q, hq⟩ := complete_exists w hM (wholePlaneVertexTrans W N M hNM v)
  let m := max (max n (max q d.1)) B
  have hnm : n ≤ m := (Nat.le_max_left n (max q d.1)).trans (Nat.le_max_left _ _)
  have hqm : q ≤ s + m := by
    have := (Nat.le_max_left q d.1).trans (Nat.le_max_right n (max q d.1))
    have := Nat.le_max_left (max n (max q d.1)) B
    omega
  have hdm : d.1 ≤ m :=
    (Nat.le_max_right q d.1).trans ((Nat.le_max_right n (max q d.1)).trans
      (Nat.le_max_left _ _))
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
  have hr : r ∈ (kmswStage u m).LL ++ (kmswStage u m).LR := by
    apply List.mem_append_right
    obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp (hB m (Nat.le_max_right _ _))
    change kmswRightBoundaryEdge u i ∈ (kmswStage u m).LR
    rw [← he]
    exact List.getElem_mem hb
  have hrb : r < (kmswStage u m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u m).2 r (by
      simp only [List.mem_append] at hr ⊢
      tauto)
  have hrv : (kmswStage u m).east r = v := (edge_endpoints_eq u hrb).2
  have hx : stageEndpoint (kmswStage u m) x = v := by
    rw [stage_base]
    change base u d = v
    simpa only [v, r, hu, base] using hd
  have hcx : kmswVertexComplete u m (stageEndpoint (kmswStage u m) x) := hx ▸ hcs
  have hy : value y = I d := hmap x
  have hybase : stageEndpoint (kmswStage w (s + m)) y =
      wholePlaneVertexTrans W N M hNM v := by
    calc
      stageEndpoint (kmswStage w (s + m)) y = base w (value y) := stage_base w _ y
      _ = base w (I d) := congrArg (base w) hy
      _ = wholePlaneVertexTrans W N M hNM (base (shiftedStream W N) d) :=
        trans_base W N M hNM d
      _ = wholePlaneVertexTrans W N M hNM v := by
        apply congrArg
        simpa only [base, v, r, hu] using hd
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
    kmswWindowDartMap_symm_firstReturn_at_lower_edge w s m r hr x (hx.trans hrv.symm)
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
    have heone : base (shiftedStream W N) e = v := by
      change base (shiftedStream W M) (wholePlaneDartTrans W N M hNM e) =
        base (shiftedStream W M) (wholePlaneDartTrans W N M hNM d) at hep
      rw [trans_base, trans_base] at hep
      have hvd : base (shiftedStream W N) d = v := by
        simpa only [base, v, r, hu] using hd
      exact (wholePlaneVertexTrans_injective W N M hNM hep).trans hvd
    have heb : e.1 < (kmswStage u m).nextEdge := by
      apply hcs e.1
      have heu : base u e = v := by rw [hu]; exact heone
      cases hb : e.2
      · exact Or.inl (by simpa only [base, hb, Bool.false_eq_true, ↓reduceIte] using heu)
      · exact Or.inr (by simpa only [base, hb, ↓reduceIte] using heu)
    let z : StageDart (kmswStage u m).nextEdge := (⟨e.1, heb⟩, e.2)
    apply hgap j hj hjk
    refine ⟨z, value_injective _ ?_⟩
    exact (hmap z).trans (he.trans (hiter j))

private theorem active_present (w : ℕ → Fin 3) (m : ℕ) :
    (kmswStage w m).present (act w m) = true := by
  apply (kmswStage_status w m).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem window_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem trans_act (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    window_act (shiftedStream W M) (M - N) k

private theorem active_terminal_outgoing_lift (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N t : ℕ) (e : WholePlaneEdge W)
    (hp : wholePlaneEdgePresent W e)
    (hw : wholePlaneEdgeWest W e = wholePlaneVertexι W N
      (edgeEast (shiftedStream W N) (act (shiftedStream W N) t))) :
    ∃ f : ℕ, EdgePresent (shiftedStream W N) f ∧
      edgeWest (shiftedStream W N) f =
        edgeEast (shiftedStream W N) (act (shiftedStream W N) t) ∧ wholePlaneEdgeι W N f = e := by
  let v := edgeEast (shiftedStream W N) (act (shiftedStream W N) t)
  change wholePlaneEdgeWest W e = wholePlaneVertexι W N v at hw

  obtain ⟨⟨K, g⟩, he⟩ := Quotient.exists_rep e
  change wholePlaneEdgeι W K g = e at he
  obtain ⟨A, hKA, hA⟩ := wholePlaneEdgePresent_eventually W H K g
  let M := max N A
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hAM : A ≤ M := Nat.le_max_right _ _
  let f := wholePlaneEdgeTrans W K M (hKA.trans hAM) g
  have hfp : EdgePresent (shiftedStream W M) f :=
    (hA M hAM).mpr (he.symm ▸ hp)
  have hfι : wholePlaneEdgeι W M f = e :=
    (congrFun (wholePlaneEdgeι_trans W K M (hKA.trans hAM)) g).trans he
  have hfw : wholePlaneEdgeWest W (wholePlaneEdgeι W M f) =
      wholePlaneVertexι W N v := hfι ▸ hw
  obtain ⟨n, hft, hpt⟩ := hfp
  obtain ⟨m, _, hfm⟩ := stagePresent_exists_active (shiftedStream W M) n f hft hpt
  have hmb : f < (kmswStage (shiftedStream W M) m).nextEdge := by
    rw [hfm]
    exact act_lt_nextEdge _ le_rfl
  have hmp : (kmswStage (shiftedStream W M) m).present f = true := by
    rw [hfm]
    exact active_present _ _
  have hs : M - N ≤ m := by
    by_contra hn
    have hms : m ≤ M - N + t := by omega
    obtain ⟨hb, hpast⟩ := present_mono (shiftedStream W M) hmb hmp (M - N + t) hms
    have hfront := stageOutgoing_active_east_empty (shiftedStream W M) (M - N + t)
      (⟨⟨f, hb⟩, false⟩) ⟨rfl, hpast⟩
    apply hfront
    change (kmswStage (shiftedStream W M) (M - N + t)).west f = _
    rw [(edge_endpoints_eq (shiftedStream W M) hb).1]
    have hv : edgeWest (shiftedStream W M) f = wholePlaneVertexTrans W N M hNM v := by
      apply wholePlaneVertexι_injective W M
      rw [← wholePlaneEdgeWest_ι]
      exact hfw.trans (congrFun (wholePlaneVertexι_trans W N M hNM) v).symm
    rw [hv]
    have ht := trans_act W N M hNM t
    have he := wholePlaneEdgeTrans_east W N M hNM (act (shiftedStream W N) t)
    rw [ht] at he
    exact he.symm.trans
      (edge_endpoints_eq (shiftedStream W M) (act_lt_nextEdge _ le_rfl)).2.symm
  let q := act (shiftedStream W N) (m - (M - N))
  have hq : wholePlaneEdgeTrans W N M hNM q = f := by
    dsimp only [q]
    rw [trans_act, show M - N + (m - (M - N)) = m by omega]
    exact hfm.symm
  have hv : edgeWest (shiftedStream W M) f = wholePlaneVertexTrans W N M hNM v := by
    apply wholePlaneVertexι_injective W M
    rw [← wholePlaneEdgeWest_ι]
    exact hfw.trans (congrFun (wholePlaneVertexι_trans W N M hNM) v).symm
  have hqw : edgeWest (shiftedStream W N) q = v := by
    apply wholePlaneVertexTrans_injective W N M hNM
    rw [← wholePlaneEdgeTrans_west, hq, hv]
  refine ⟨q, ⟨m - (M - N), act_lt_nextEdge _ le_rfl, active_present _ _⟩, hqw, ?_⟩
  calc
    wholePlaneEdgeι W N q =
        wholePlaneEdgeι W M (wholePlaneEdgeTrans W N M hNM q) :=
      (congrFun (wholePlaneEdgeι_trans W N M hNM) q).symm
    _ = e := by rw [hq]; exact hfι

private def ambientBase (W : ℤ → Fin 3) (d : WholePlaneDart W) : WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1

private theorem base_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    ambientBase W (wholePlaneDartι W N d) =
      wholePlaneVertexι W N (base (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [ambientBase, base, wholePlaneDartι, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeWest_ι W N d.1
  · exact wholePlaneEdgeEast_ι W N d.1

private theorem symm_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) :
    base w ((kmswInfRot w hfin).symm d) = base w d := by
  obtain ⟨n, hn⟩ := kmswInfRot_symm_eventually_eq_stage w hfin d
  obtain ⟨hd, he⟩ := hn n le_rfl
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  have hb (z : StageDart (kmswStage w n).nextEdge) :
      stageEndpoint (kmswStage w n) z = base w (z.1.val, z.2) := by
    obtain ⟨hw, he⟩ := edge_endpoints_eq w z.1.isLt
    cases hs : z.2 <;> simp only [stageEndpoint, base, hs,
      Bool.false_eq_true, ↓reduceIte, hw, he]
  have hr := ((stageRot_sameCycle_iff_endpoint_eq w n
    ((stageRot w n).symm x) x).mp
      ⟨1, (stageRot w n).apply_symm_apply x⟩)
  rw [he, ← hb ((stageRot w n).symm x), ← hb x]
  exact hr

private theorem symm_pow_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    base w (((kmswInfRot w hfin).symm ^ k) d) = base w d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, symm_base, ih]

private theorem ambient_symm_pow_base (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) (k : ℕ) :
    ambientBase W (((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N d)) =
      ambientBase W (wholePlaneDartι W N d) := by
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N d
  rw [hpow k, base_ι, symm_pow_base, ← base_ι]
  exact congrArg (ambientBase W) (congrFun (wholePlaneDartι_trans W N M hNM) d)

private theorem rightmost_of_firstReturn (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N t e g : ℕ)
    (hp : EdgePresent (shiftedStream W N) e)
    (hw : edgeWest (shiftedStream W N) e =
      edgeEast (shiftedStream W N) (act (shiftedStream W N) t))
    (hg : EdgePresent (shiftedStream W N) g)
    (hret : ∃ k : ℕ, 0 < k ∧
      ((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N (e, false)) =
        wholePlaneDartι W N (g, true) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((wholePlaneRotation W H).symm ^ j) (wholePlaneDartι W N (e, false)) ∉
          Set.range (wholePlaneDartι W N)) :
    wholePlaneRightmostOutgoingAt W H (wholePlaneVertexι W N
      (edgeEast (shiftedStream W N) (act (shiftedStream W N) t)))
      (wholePlaneEdgeι W N e) := by
  let v := edgeEast (shiftedStream W N) (act (shiftedStream W N) t)
  change edgeWest (shiftedStream W N) e = v at hw
  change wholePlaneRightmostOutgoingAt W H (wholePlaneVertexι W N v)
    (wholePlaneEdgeι W N e)

  classical
  obtain ⟨k, hk, hret, hgap⟩ := hret
  let Q := fun j : ℕ => 0 < j ∧ wholePlaneEdgePresent W
    (((wholePlaneRotation W H).symm ^ j) (wholePlaneDartι W N (e, false))).1
  have hex : ∃ j, Q j := ⟨k, hk, by
    rw [hret]
    exact wholePlaneEdgePresent_ι_of_run_present W N g hg⟩
  let m := Nat.find hex
  have hm : Q m := Nat.find_spec hex
  have hmk : m ≤ k := Nat.find_min' hex (by
    exact ⟨hk, by rw [hret]; exact wholePlaneEdgePresent_ι_of_run_present W N g hg⟩)
  have hside : (((wholePlaneRotation W H).symm ^ m)
      (wholePlaneDartι W N (e, false))).2 = true := by
    by_cases hme : m = k
    · rw [hme, hret]
      rfl
    · let z := ((wholePlaneRotation W H).symm ^ m) (wholePlaneDartι W N (e, false))
      have hb := ambient_symm_pow_base W H N (e, false) m
      have hzw : z.2 = false → wholePlaneEdgeWest W z.1 = wholePlaneVertexι W N v := by
        intro hz
        change ambientBase W z = _ at hb
        simpa only [ambientBase, hz, wholePlaneDartι, Bool.false_eq_true,
          ↓reduceIte, wholePlaneEdgeWest_ι, hw] using hb
      cases hs : z.2 with
      | true => rfl
      | false =>
        obtain ⟨f, _, _, hf⟩ := active_terminal_outgoing_lift W H N t z.1
          hm.2 (hzw hs)
        apply False.elim
        apply hgap m hm.1 (by omega)
        exact ⟨(f, false), Prod.ext hf hs.symm⟩
  refine ⟨wholePlaneEdgePresent_ι_of_run_present W N e hp, ?_, m, hm.1, hside, hm.2, ?_⟩
  · rw [wholePlaneEdgeWest_ι, hw]
  · intro j hj hjm hpj
    exact Nat.find_min hex hjm ⟨hj, hpj⟩

open MeasureTheory RandomWalk

private theorem boundary_present (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (i : ℕ) :
    EdgePresent w (kmswRightBoundaryEdge w i) := by
  obtain ⟨B, hB⟩ := kmswStage_LR_getElem?_eventually w hR i
  obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp (hB B le_rfl)
  have hm : kmswRightBoundaryEdge w i ∈ (kmswStage w B).LR := by
    rw [← he]
    exact List.getElem_mem hb
  refine ⟨B, (kmswStage_boundary_ids_lt_nextEdge w B).2 _ ?_,
    (kmswStage_status w B).2.2.1 _ hm⟩
  simp only [List.mem_append]
  tauto

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Every positive right-boundary record edge is ambient rightmost.
The vertex is its source, the hit-indexed vertex x_k; r_k joins x_k to x_(k+1). -/
theorem wholePlaneRightBoundaryEdge_rightmost (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a)
    (k : ℕ) (hk : 1 ≤ k) :
    wholePlaneRightmostOutgoingAt W H
      (wholePlaneVertexι W N
        (edgeWest (shiftedStream W N) (kmswRightBoundaryEdge (shiftedStream W N) k)))
      (wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) k)) := by
  let w := shiftedStream W N
  let e := kmswRightBoundaryEdge w k
  let g := kmswRightBoundaryEdge w (k - 1)
  let t := natSelect (fun m => ∀ j, j < m → R w m < R w j) (k - 1)
  have hgt : act w t = g := rfl
  have hface := kmswInfFaceSucc_right_of_unbounded_below w (H.1 N) hR (k - 1)
  have hpred : (kmswInfRot w (H.1 N)).symm (e, false) = (g, true) := by
    change (kmswInfRot w (H.1 N)).symm
      (kmswRightBoundaryEdge w ((k - 1) + 1), false) =
        (kmswRightBoundaryEdge w (k - 1), true) at hface
    simpa only [Nat.sub_add_cancel hk, e, g] using hface
  have hw : edgeWest w e = edgeEast w g := by
    have hb := symm_base w (H.1 N) (e, false)
    rw [hpred] at hb
    exact hb.symm
  rw [hw]
  apply rightmost_of_firstReturn W H N t e g (boundary_present w hR k)
    (by rw [hgt]; exact hw) (boundary_present w hR (k - 1))
  have hr := wholePlaneRotation_symm_firstReturn_of_cross_run W H N (e, false)
    (fun M hNM => wholePlaneInfRot_symm_firstReturn_at_right_boundary W N M hNM
      (H.1 N) (H.1 M) hR (k - 1) (e, false) hw)
  obtain ⟨j, hj, hreturn, hgap⟩ := hr
  exact ⟨j, hj, hreturn.trans (congrArg (wholePlaneDartι W N) hpred), hgap⟩

private theorem ae_run_hits :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      BoundaryHitWitnesses (shiftedStream W N) := by
  apply ae_all_iff.2
  intro N
  have hf := iidCodes_ae_boundaryHitWitnesses
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath N] at hf
  have hp := ae_of_ae_map (measurable_shiftedCodePath N).aemeasurable hf
  simpa [shiftedCodePath, insertDummy] using hp

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. A single rotation witness works simultaneously at all positive
right-boundary vertices of every run. The k-th outgoing edge is r_k, joining x_k
and x_(k+1); r_0 is the root edge. -/
theorem wholePlaneIID_ae_rightBoundary_rightmost :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∃ H : WholePlaneRotationHypothesis W,
      ∀ N k : ℕ, 1 ≤ k → wholePlaneRightmostOutgoingAt W H
        (wholePlaneVertexι W N
          (edgeWest (shiftedStream W N) (kmswRightBoundaryEdge (shiftedStream W N) k)))
        (wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) k)) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis, ae_run_hits] with W H hh
  refine ⟨H, fun N k hk => ?_⟩
  apply wholePlaneRightBoundaryEdge_rightmost W H N _ k hk
  intro a
  obtain ⟨n, hn⟩ := (hh N).rightHit (max 1 (-a)) (le_max_left _ _)
  change R (shiftedStream W N) n = -max 1 (-a) at hn
  have hm : -a ≤ max (1 : ℤ) (-a) := le_max_right _ _
  exact ⟨n, by omega⟩

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. An infinite chain starts at the root terminal, uses exactly
r_(j+1) at step j, and is ambient rightmost at every step. The vertices are x_(j+1).
This constructs the chain explicitly; uniqueness of a global path selector is separate. -/
theorem wholePlaneRightBoundary_rightmost_chain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) :
    ∃ (v : ℕ → WholePlaneVertex W) (e : ℕ → WholePlaneEdge W),
      v 0 = wholePlaneVertexι W N 1 ∧
      (∀ j : ℕ, e j =
        wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) (j + 1))) ∧
      (∀ j : ℕ, wholePlaneRightmostOutgoingAt W H (v j) (e j) ∧
        wholePlaneEdgeEast W (e j) = v (j + 1)) := by
  let w := shiftedStream W N
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max 1 (-a)) (le_max_left _ _)
    change R w n = -max 1 (-a) at hn
    have hm : -a ≤ max (1 : ℤ) (-a) := le_max_right _ _
    exact ⟨n, by omega⟩
  refine ⟨(fun j => wholePlaneVertexι W N (boundaryVertex w h ((j + 1 : ℕ) : ℤ))),
    (fun j => wholePlaneEdgeι W N (kmswRightBoundaryEdge w (j + 1))), ?_,
    (fun _ => rfl), ?_⟩
  · change wholePlaneVertexι W N (boundaryVertex w h 1) = wholePlaneVertexι W N 1
    rw [boundaryVertex_one]
  · intro j
    have hp := boundaryVertex_right_edge_present_source w h (k := j + 1) (by omega)
    constructor
    · have hr := wholePlaneRightBoundaryEdge_rightmost W H N hR (j + 1) (by omega)
      rw [hp.2.1] at hr
      exact hr
    · rw [wholePlaneEdgeEast_ι]
      apply congrArg (wholePlaneVertexι W N)
      simpa only [Nat.cast_add, Nat.cast_one] using hp.2.2

end DirectedDistances.KMSW
