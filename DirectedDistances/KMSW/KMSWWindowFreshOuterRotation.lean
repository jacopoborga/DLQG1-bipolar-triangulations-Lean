module

public import DirectedDistances.KMSW.KMSWWindowFreshRotation
public import DirectedDistances.KMSW.KMSWWindowFreshVertexStar
public import DirectedDistances.KMSW.KMSWWindowFreshPresence





public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem kmswStageRot_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) ((kmswMap w n).rot d) =
      stageEndpoint (kmswStage w n) d := by
  have hsame : (stageRot w n).SameCycle d ((stageRot w n) d) :=
    ⟨1, by simp⟩
  simpa only [kmswMap_rot] using
    ((stageRot_sameCycle_iff_endpoint_eq w n d ((stageRot w n) d)).mp hsame).symm

private theorem rot_faceSucc {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (d : D) :
    M.rot (M.faceSucc d) = M.edgeInv d := by
  change M.rot (M.rot.symm (M.edgeInv d)) = M.edgeInv d
  exact M.rot.apply_symm_apply _



theorem stageOuterWord_predecessor_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : d ∈ stageOuterWord w n) :
    stageEndpoint (kmswStage w n)
        (edgeFlip _ ((stageOuterWord w n).formPerm.symm d)) =
      stageEndpoint (kmswStage w n) d := by
  let p := (stageOuterWord w n).formPerm.symm d
  have hp : p ∈ stageOuterWord w n := by
    have hform : (stageOuterWord w n).formPerm p = d := by
      simp [p]
    exact List.mem_of_formPerm_apply_mem
      (hform ▸ hd)
  have hface : (kmswMap w n).faceSucc p = d := by
    rw [stageOuterWord_faceSucc w n p hp]
    exact (stageOuterWord w n).formPerm.apply_symm_apply d
  have hrot : (kmswMap w n).rot d = edgeFlip _ p := by
    have h := rot_faceSucc (kmswMap w n) p
    rw [hface] at h
    simpa only [kmswMap_edgeInv] using h
  rw [← hrot]
  exact kmswStageRot_endpoint w n d

private theorem old_dart_endpoint_lt (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage w (s + m)).nextEdge)
    (hd : d.1.val < (kmswStage w s).nextEdge) :
    stageEndpoint (kmswStage w (s + m)) d < (kmswStage w s).nextVertex := by
  have hs := kmswStage_endpoints_stable w (Nat.le_add_right s m) hd
  have hb := kmswStage_endpoints_lt_nextVertex w s d.1.val hd
  cases d with
  | mk e b =>
    cases b
    · simpa [stageEndpoint, hs.1] using hb.1
    · simpa [stageEndpoint, hs.2] using hb.2

private theorem window_map_vertex_lt_of_old_edge (w : ℕ → Fin 3) (s m v : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (he : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v)
    (hold : (kmswWindowDartMap w s m d).1.val < (kmswStage w s).nextEdge) :
    kmswWindowPatchVertexMap w s m v < (kmswStage w s).nextVertex := by
  have hlt := old_dart_endpoint_lt w s m (kmswWindowDartMap w s m d) hold
  have hvtx : stageEndpoint (kmswStage w (s + m))
      (kmswWindowDartMap w s m d) = kmswWindowPatchVertexMap w s m
        (stageEndpoint (kmswStage (fun i => w (s + i)) m) d) := by
    simpa only [stageEndpoint] using kmswWindowDartMap_vertex w s m d
  rw [hvtx, he] at hlt
  exact hlt




theorem kmswWindowDartMap_outer_of_fresh (w : ℕ → Fin 3) (s m v : ℕ)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : d ∈ stageOuterWord (fun i => w (s + i)) m)
    (he : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v) :
    kmswWindowDartMap w s m d ∈ stageOuterWord w (s + m) := by
  let u := fun i => w (s + i)
  let F := kmswStage u m
  let G₀ := kmswStage w s
  let G := kmswStage w (s + m)
  let data := kmswWindowPatchData w s m
  have hrel := kmswWindowPatchData_rel w s m
  change KMSWWindowPatchRel G₀ G F data.φ data.A data.B data.YL data.YR
    data.XL data.XR at hrel
  have hold (e : ℕ) (hφ : data.φ e < G₀.nextEdge)
      (hedge : e = d.1.val) : False := by
    have hmaplt : (kmswWindowDartMap w s m d).1.val < G₀.nextEdge := by
      simpa only [kmswWindowDartMap, data, hedge] using hφ
    have hvertex := window_map_vertex_lt_of_old_edge w s m v d he hmaplt
    omega
  rcases (stageOuterWord_mem_iff u m d).mp hd with hupper | hlower
  · rcases hupper.2 with hUL | hUR
    · apply (stageOuterWord_mem_iff w (s + m) _).2
      refine Or.inl ⟨hupper.1, Or.inl ?_⟩
      change data.φ d.1.val ∈ G.UL
      rw [hrel.ul]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨d.1.val, hUL, rfl⟩)
    · apply (stageOuterWord_mem_iff w (s + m) _).2
      refine Or.inl ⟨hupper.1, Or.inr ?_⟩
      change data.φ d.1.val ∈ G.UR
      rw [hrel.ur]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨d.1.val, hUR, rfl⟩)
  · rcases hlower.2 with hLR | hLL
    · have hsplit : d.1.val = 0 ∨ d.1.val ∈ data.YR ∨
        d.1.val ∈ data.XR := by
        change d.1.val ∈ F.LR at hLR
        rw [hrel.lr_split] at hLR
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at hLR
        tauto
      rcases hsplit with hzero | hYR | hXR
      · have hφ : data.φ d.1.val < G₀.nextEdge := by
          rw [hzero, hrel.root]
          exact (kmswStage_boundary_ids_lt_nextEdge w s).1
        exact (hold d.1.val hφ rfl).elim
      · have hUR : data.φ d.1.val ∈ G₀.UR := by
          rw [hrel.right_residual]
          exact List.mem_append_left _ (List.mem_map.mpr ⟨d.1.val, hYR, rfl⟩)
        have hφ : data.φ d.1.val < G₀.nextEdge :=
          (kmswStage_boundary_ids_lt_nextEdge w s).2 _ (by
            change data.φ d.1.val ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inr hUR)))
        exact (hold d.1.val hφ rfl).elim
      · apply (stageOuterWord_mem_iff w (s + m) _).2
        refine Or.inr ⟨hlower.1, Or.inl ?_⟩
        change data.φ d.1.val ∈ G.LR
        rw [hrel.lr]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨d.1.val, hXR, rfl⟩)
    · have hsplit : d.1.val ∈ data.XL ∨ d.1.val ∈ data.YL := by
        change d.1.val ∈ F.LL at hLL
        rw [hrel.ll_split] at hLL
        simpa only [List.mem_append] using hLL
      rcases hsplit with hXL | hYL
      · apply (stageOuterWord_mem_iff w (s + m) _).2
        refine Or.inr ⟨hlower.1, Or.inr ?_⟩
        change data.φ d.1.val ∈ G.LL
        rw [hrel.ll]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨d.1.val, hXL, rfl⟩)
      · have hdrop : data.φ d.1.val ∈ G₀.UL.dropLast := by
          rw [hrel.left_residual]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨d.1.val, hYL, rfl⟩)
        have hUL : data.φ d.1.val ∈ G₀.UL :=
          (List.dropLast_sublist _).subset hdrop
        have hφ : data.φ d.1.val < G₀.nextEdge :=
          (kmswStage_boundary_ids_lt_nextEdge w s).2 _ (by
            change data.φ d.1.val ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inl hUL)))
        exact (hold d.1.val hφ rfl).elim




theorem kmswWindowDartMap_outer_predecessor_not_old (w : ℕ → Fin 3) (s m v : ℕ)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : d ∈ stageOuterWord (fun i => w (s + i)) m)
    (he : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v)
    (q : StageDart (kmswStage w (s + m)).nextEdge)
    (hq : q = (stageOuterWord w (s + m)).formPerm.symm
      (kmswWindowDartMap w s m d))
    (hold : q.1.val < (kmswStage w s).nextEdge) : False := by
  have hglobal := kmswWindowDartMap_outer_of_fresh w s m v hnew d hd he
  have hpred := stageOuterWord_predecessor_endpoint w (s + m)
    (kmswWindowDartMap w s m d) hglobal
  have holdflip := old_dart_endpoint_lt w s m (edgeFlip _ q) (by
    simpa [edgeFlip] using hold)
  have hmapped : stageEndpoint (kmswStage w (s + m))
      (kmswWindowDartMap w s m d) = kmswWindowPatchVertexMap w s m v := by
    have hvtx : stageEndpoint (kmswStage w (s + m))
        (kmswWindowDartMap w s m d) = kmswWindowPatchVertexMap w s m
          (stageEndpoint (kmswStage (fun i => w (s + i)) m) d) := by
      simpa only [stageEndpoint] using kmswWindowDartMap_vertex w s m d
    rw [hvtx, he]
  have hcommon := hpred
  rw [← hq] at hcommon
  have hlarge : (kmswStage w s).nextVertex ≤
      stageEndpoint (kmswStage w (s + m)) (edgeFlip _ q) := by
    rw [hcommon, hmapped]
    exact hnew
  omega

private theorem outer_map_formPerm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have him : i < (l.map f).length := by simpa only [List.length_map] using hi
  have hget : (l.map f)[i]'him = f l[i] := List.getElem_map f
  rw [← hget, List.formPerm_apply_getElem _ (hl.map hf),
    List.formPerm_apply_getElem _ hl]
  simp only [List.length_map, List.getElem_map]

private theorem outer_filter_formPerm {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (p : α → Bool) (x : α) (hx : x ∈ l)
    (hpx : p x = true) (hpy : p (l.formPerm x) = true) :
    (l.filter p).formPerm x = l.formPerm x := by
  obtain ⟨a, b, rfl⟩ := List.mem_iff_append.mp hx
  have hr := List.isRotated_append (l := a) (l' := x :: b)
  have he := List.formPerm_eq_of_isRotated hl hr
  have hn : (x :: (b ++ a)).Nodup := by
    simpa only [List.cons_append] using hr.nodup_iff.mp hl
  have hlf : (a.filter p ++ (x :: b).filter p).Nodup := by
    simpa only [List.filter_append] using hl.filter p
  have hf := List.formPerm_eq_of_isRotated hlf
    (List.isRotated_append (l := a.filter p) (l' := (x :: b).filter p))
  simp only [List.filter_append]
  rw [he] at hpy ⊢
  rw [hf]
  simp only [List.filter_cons, hpx, ↓reduceIte, List.cons_append]
  rw [← List.filter_append]
  change (x :: ((b ++ a).filter p)).formPerm x = (x :: (b ++ a)).formPerm x
  cases hba : b ++ a with
  | nil => simp only [List.filter_nil, List.formPerm_singleton]
  | cons y r =>
    rw [hba] at hn
    simp only [List.cons_append, hba] at hpy
    have hy : p y = true := by
      simpa only [List.cons_append, hba, List.formPerm_apply_head x y r hn] using hpy
    simp only [List.filter_cons, hy, ↓reduceIte]
    have hnf : (x :: y :: r.filter p).Nodup := by
      simpa only [List.filter_cons, hpx, hy, ↓reduceIte] using hn.filter p
    rw [List.formPerm_apply_head _ _ _ hnf, List.formPerm_apply_head _ _ _ hn]

private theorem outer_value_injective (n : ℕ) :
    Function.Injective (fun d : StageDart n => (d.1.val, d.2)) := by
  intro a b h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact congrArg (fun x : ℕ × Bool => x.2) h

private theorem outer_filtered_words (w : ℕ → Fin 3) (s m : ℕ) :
    let keep : ℕ × Bool → Bool := fun d => decide ((kmswStage w s).nextEdge ≤ d.1)
    (stageOuterWordVal w (s + m)).filter keep =
      ((stageOuterWordVal (fun i => w (s + i)) m).map
        (fun d => ((kmswWindowPatchData w s m).φ d.1, d.2))).filter keep := by
  intro keep
  let u := fun i => w (s + i)
  let F := kmswStage u m
  let G₀ := kmswStage w s
  let G := kmswStage w (s + m)
  let data := kmswWindowPatchData w s m
  have hrel := kmswWindowPatchData_rel w s m
  change KMSWWindowPatchRel G₀ G F data.φ data.A data.B data.YL data.YR
    data.XL data.XR at hrel
  have clear (l : List ℕ) (b : Bool) (hb : ∀ e ∈ l, e < G₀.nextEdge) :
      (l.map (fun e => (e, b))).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    have hlt := hb e he
    simp only [keep, decide_eq_true_eq, Nat.not_le]
    exact hlt
  have oldbound (e) (he : e ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR) :
      e < G₀.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w s).2 e he
  have hA (e) (he : e ∈ data.A) : e < G₀.nextEdge := by
    apply oldbound
    have hm : e ∈ G₀.UL.dropLast := by
      rw [hrel.left_residual]
      exact List.mem_append_left _ he
    have hUL : e ∈ G₀.UL := (List.dropLast_sublist _).subset hm
    simp only [List.mem_append]
    tauto
  have hB (e) (he : e ∈ data.B) : e < G₀.nextEdge := by
    apply oldbound
    have hm : e ∈ G₀.UR := by
      rw [hrel.right_residual]
      exact List.mem_append_right _ he
    simp only [List.mem_append]
    tauto
  have hYL (e) (he : e ∈ data.YL.map data.φ) : e < G₀.nextEdge := by
    apply oldbound
    have hm : e ∈ G₀.UL.dropLast := by
      rw [hrel.left_residual]
      exact List.mem_append_right _ he
    have hUL : e ∈ G₀.UL := (List.dropLast_sublist _).subset hm
    simp only [List.mem_append]
    tauto
  have hYR (e) (he : e ∈ data.YR.map data.φ) : e < G₀.nextEdge := by
    apply oldbound
    have hm : e ∈ G₀.UR := by
      rw [hrel.right_residual]
      exact List.mem_append_left _ he
    simp only [List.mem_append]
    tauto
  have hLL (e) (he : e ∈ G₀.LL) : e < G₀.nextEdge := by
    apply oldbound
    simp only [List.mem_append]
    tauto
  have hLR (e) (he : e ∈ G₀.LR) : e < G₀.nextEdge := by
    apply oldbound
    simp only [List.mem_append]
    tauto
  have hroot : data.φ 0 < G₀.nextEdge := by
    rw [hrel.root]
    exact (kmswStage_boundary_ids_lt_nextEdge w s).1
  have hz : keep (data.φ 0, true) = false := by
    simp only [keep, decide_eq_false_iff_not, Nat.not_le]
    exact hroot
  have hclearYR : (data.YR.map (fun e => (data.φ e, true))).filter keep = [] := by
    simpa only [List.map_map, Function.comp_def] using clear (data.YR.map data.φ) true hYR
  have hclearYL : (data.YL.map (fun e => (data.φ e, true))).filter keep = [] := by
    simpa only [List.map_map, Function.comp_def] using clear (data.YL.map data.φ) true hYL
  rw [stageOuterWordVal_eq_runs, stageOuterWordVal_eq_runs]
  change (((G.UL.map fun e => (e, false)) ++
    (G.UR.map fun e => (e, false)) ++ (G.LR.reverse.map fun e => (e, true)) ++
    (G.LL.reverse.map fun e => (e, true))).filter keep) = _
  rw [hrel.ul, hrel.ur, hrel.lr, hrel.ll]
  change _ = (((F.UL.map fun e => (e, false)) ++
    (F.UR.map fun e => (e, false)) ++ (F.LR.reverse.map fun e => (e, true)) ++
    (F.LL.reverse.map fun e => (e, true))).map
    (fun d => (data.φ d.1, d.2))).filter keep
  rw [hrel.lr_split, hrel.ll_split]
  simp only [List.map_append, List.reverse_append, List.map_reverse,
    List.filter_append, List.filter_reverse, List.map_map, Function.comp_def]
  simp only [clear data.A false hA,
    clear data.B false hB, clear G₀.LR true hLR, clear G₀.LL true hLL,
    hclearYR, hclearYL,
    List.map_cons, List.map_nil, List.filter_cons, List.filter_nil,
    hz,
    Bool.false_eq_true, ↓reduceIte, List.reverse_nil, List.nil_append,
    List.append_nil, List.append_assoc]




theorem kmswWindowDartMap_outer_predecessor_of_fresh (w : ℕ → Fin 3) (s m v : ℕ)
    (_hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (he : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v)
    (hd : d ∈ stageOuterWord (fun i => w (s + i)) m) :
    (stageOuterWord w (s + m)).formPerm.symm (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m
        ((stageOuterWord (fun i => w (s + i)) m).formPerm.symm d) := by
  let u := fun i => w (s + i)
  let F := kmswStage u m
  let G := kmswStage w (s + m)
  let V : StageDart G.nextEdge → ℕ × Bool := fun e => (e.1.val, e.2)
  let f : StageDart F.nextEdge → ℕ × Bool := fun e => V (kmswWindowDartMap w s m e)
  let keep : ℕ × Bool → Bool := fun e => decide ((kmswStage w s).nextEdge ≤ e.1)
  let p := (stageOuterWord u m).formPerm.symm d
  let q := (stageOuterWord w (s + m)).formPerm.symm (kmswWindowDartMap w s m d)
  have hglobal := kmswWindowDartMap_outer_of_fresh w s m v hnew d hd he
  have hp : p ∈ stageOuterWord u m := by
    apply List.mem_of_formPerm_apply_mem
    simpa only [p, Equiv.apply_symm_apply] using hd
  have hq : q ∈ stageOuterWord w (s + m) := by
    apply List.mem_of_formPerm_apply_mem
    simpa only [q, Equiv.apply_symm_apply] using hglobal
  have hkeepd : keep (f d) = true := by
    change decide ((kmswStage w s).nextEdge ≤
      (kmswWindowDartMap w s m d).1.val) = true
    apply decide_eq_true
    by_contra hn
    have hlt : (kmswWindowDartMap w s m d).1.val < (kmswStage w s).nextEdge := by
      exact Nat.lt_of_not_ge hn
    have hvlt := window_map_vertex_lt_of_old_edge w s m v d he hlt
    omega
  have hkeepp : keep (f p) = true := by
    change decide ((kmswStage w s).nextEdge ≤
      (kmswWindowDartMap w s m p).1.val) = true
    apply decide_eq_true
    by_contra hn
    have hlt : (kmswWindowDartMap w s m (edgeFlip _ p)).1.val <
        (kmswStage w s).nextEdge := Nat.lt_of_not_ge hn
    have hpe : stageEndpoint F (edgeFlip _ p) = v :=
      (stageOuterWord_predecessor_endpoint u m d hd).trans he
    have hvlt := window_map_vertex_lt_of_old_edge w s m v (edgeFlip _ p) hpe hlt
    omega
  have hkeepq : keep (V q) = true := by
    change decide ((kmswStage w s).nextEdge ≤ q.1.val) = true
    apply decide_eq_true
    by_contra hn
    exact kmswWindowDartMap_outer_predecessor_not_old w s m v hnew d hd he q rfl
      (Nat.lt_of_not_ge hn)
  have hf : Function.Injective f :=
    (outer_value_injective G.nextEdge).comp (kmswWindowDartMap_injective w s m)
  have hfilter : ((stageOuterWord w (s + m)).map V).filter keep =
      ((stageOuterWord u m).map f).filter keep := by
    simpa only [stageOuterWordVal, List.map_map, Function.comp_def,
      kmswWindowDartMap, V, f, u] using outer_filtered_words w s m
  have hfg : ((stageOuterWord w (s + m)).map V).formPerm (V q) = f d := by
    rw [outer_map_formPerm V (outer_value_injective _) _ (stageOuterWord_nodup w _) q hq]
    exact congrArg V ((stageOuterWord w (s + m)).formPerm.apply_symm_apply _)
  have hff : ((stageOuterWord u m).map f).formPerm (f p) = f d := by
    rw [outer_map_formPerm f hf _ (stageOuterWord_nodup u m) p hp]
    exact congrArg f ((stageOuterWord u m).formPerm.apply_symm_apply d)
  have hfg' := outer_filter_formPerm _
    ((stageOuterWord_nodup w (s + m)).map (outer_value_injective _)) keep (V q)
    (List.mem_map.mpr ⟨q, hq, rfl⟩) hkeepq (by rw [hfg]; exact hkeepd)
  have hff' := outer_filter_formPerm _ ((stageOuterWord_nodup u m).map hf) keep (f p)
    (List.mem_map.mpr ⟨p, hp, rfl⟩) hkeepp (by rw [hff]; exact hkeepd)
  rw [hfg] at hfg'
  rw [hff] at hff'
  rw [hfilter] at hfg'
  apply outer_value_injective G.nextEdge
  exact (((stageOuterWord u m).map f).filter keep).formPerm.injective
    (hfg'.trans hff'.symm)

private theorem outer_rotation (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (hd : d ∈ stageOuterWord w n) :
    (kmswMap w n).rot d = edgeFlip _ ((stageOuterWord w n).formPerm.symm d) := by
  let p := (stageOuterWord w n).formPerm.symm d
  have hp : p ∈ stageOuterWord w n := by
    apply List.mem_of_formPerm_apply_mem
    simpa only [p, Equiv.apply_symm_apply] using hd
  have hface : (kmswMap w n).faceSucc p = d := by
    rw [stageOuterWord_faceSucc w n p hp]
    exact (stageOuterWord w n).formPerm.apply_symm_apply d
  have h := rot_faceSucc (kmswMap w n) p
  rw [hface] at h
  simpa only [kmswMap_edgeInv] using h




theorem kmswWindowDartMap_rot_of_fresh (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (he : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v) :
    (kmswMap w (s + m)).rot (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).rot d) := by
  by_cases hd : d ∈ stageOuterWord (fun i => w (s + i)) m
  · have hglobal := kmswWindowDartMap_outer_of_fresh w s m v hnew d hd he
    rw [outer_rotation w (s + m) _ hglobal,
      kmswWindowDartMap_outer_predecessor_of_fresh w s m v hv hnew d he hd,
      outer_rotation (fun i => w (s + i)) m d hd]
    exact kmswWindowDartMap_edgeFlip w s m _
  · exact kmswWindowDartMap_rot_of_nonouter w s m d hd




theorem kmswWindowDartMap_rot_symm_of_fresh (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (he : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v) :
    (kmswMap w (s + m)).rot.symm (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).rot.symm d) := by
  have hi := kmswStageRot_endpoint (fun i => w (s + i)) m
    ((kmswMap (fun i => w (s + i)) m).rot.symm d)
  rw [Equiv.apply_symm_apply] at hi
  apply (kmswMap w (s + m)).rot.injective
  rw [Equiv.apply_symm_apply,
    kmswWindowDartMap_rot_of_fresh w s m v hv hnew _ (hi.symm.trans he),
    Equiv.apply_symm_apply]

end DirectedDistances.KMSW
