module

public import DirectedDistances.KMSW.KMSWShift
import DirectedDistances.KMSW.FlowLineReachability
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! The active edge is the last entry of `UL`, and the entire fresh `UL` is mapped.
Residual `A` is ordered west to east. Thus its next consumed edge is its last edge:
the left seam case has `A = A' ++ [q]`, rather than `A = q :: A'`.
No lower-boundary membership preservation or missing-edge status equality is asserted. -/

public section
namespace DirectedDistances.KMSW

 
structure KMSWWindowPatchRel (G₀ G F : State) (φ : ℕ → ℕ)
    (A B YL YR XL XR : List ℕ) : Prop where
  xr_nil : B ≠ [] → XR = []
  xl_nil : A ≠ [] → XL = []
  residual_bound : ∀ e ∈ A ++ B, e < G.nextEdge
  residual_nodup : (A ++ B).Nodup
  fresh_image : ∀ e < F.nextEdge, φ e ∉ A ∧ φ e ∉ B
  ll_split : F.LL = XL ++ YL
  lr_split : F.LR = [0] ++ YR ++ XR
  ul : G.UL = A ++ F.UL.map φ
  ur : G.UR = F.UR.map φ ++ B
  left_residual : G₀.UL.dropLast = A ++ YL.map φ
  ll : G.LL = XL.map φ ++ G₀.LL
  right_residual : G₀.UR = YR.map φ ++ B
  lr : G.LR = G₀.LR ++ XR.map φ
  root : φ 0 = G₀.active
  active : φ F.active = G.active
  edge_bound : ∀ e < F.nextEdge, φ e < G.nextEdge
  edge_injective : ∀ e < F.nextEdge, ∀ f < F.nextEdge, φ e = φ f → e = f
  present : ∀ e < F.nextEdge, F.present e = true → G.present (φ e) = true

 
theorem kmswWindowPatchRel_init (w : ℕ → Fin 3) (s : ℕ) :
    KMSWWindowPatchRel (kmswStage w s) (kmswStage w s) kmswInit
      (fun _ => (kmswStage w s).active)
      (kmswStage w s).UL.dropLast (kmswStage w s).UR [] [] [] [] := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w s
  have hactive := (kmswStage_boundary_ids_lt_nextEdge w s).1
  have hpresent := kmswStage_active_present w s
  have hULnd : (kmswStage w s).UL.Nodup := by
    rw [kmswStage_UL_eq]
    exact (List.Nodup.filter _ List.nodup_range).map (CutConverse.act_injective w)
  have hAnd : (kmswStage w s).UL.dropLast.Nodup :=
    (List.dropLast_sublist _).nodup hULnd
  have hmem (e) (he : e ∈ (kmswStage w s).UL.dropLast) :
      e ∈ (kmswStage w s).UL := (List.dropLast_sublist _).subset he
  have hdis : List.Disjoint (kmswStage w s).UL.dropLast (kmswStage w s).UR := by
    intro e heA heB
    have hb := (kmswStage_boundary_ids_lt_nextEdge w s).2 e (by
      simp only [List.mem_append]; tauto)
    have hp := (kmswStage_status w s).2.1 e (hmem e heA)
    have hm := ((kmswStage_status w s).1 e hb).mpr (Or.inl heB)
    rw [hp] at hm
    cases hm
  refine ⟨(fun _ => rfl), (fun _ => rfl), ?_, ?_, ?_,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w s).2
    rcases List.mem_append.mp he with he | he
    · have := hmem e he
      simp only [List.mem_append]; tauto
    · simp only [List.mem_append]; tauto
  · exact List.nodup_append'.mpr ⟨hAnd, (kmswStage_status w s).2.2.2.1, hdis⟩
  · intro e _
    constructor
    · have hn := hULnd
      rw [hes, List.nodup_append'] at hn
      simpa only [hes, List.dropLast_concat] using
        (fun hm => hn.2.2 hm (by simp) : (kmswStage w s).active ∉ es)
    · intro hm
      have hb := (kmswStage_boundary_ids_lt_nextEdge w s).1
      have hf := ((kmswStage_status w s).1 _ hb).mpr (Or.inl hm)
      change (kmswStage w s).present (act w s) = false at hf
      rw [hpresent] at hf
      cases hf
  · simp only [kmswInit, List.map_cons, List.map_nil, hes, List.dropLast_concat]
  · simp only [kmswInit, List.map_nil, List.nil_append]
  · simp only [List.map_nil, List.append_nil]
  · simp only [List.map_nil, List.nil_append]
  · simp only [List.map_nil, List.nil_append]
  · simp only [List.map_nil, List.append_nil]
  · intro e _
    exact hactive
  · intro e he f hf _
    change e < 1 at he
    change f < 1 at hf
    omega
  · intro e _ _
    exact hpresent

private theorem relabel {G₀ G F : State} {φ φ' : ℕ → ℕ}
    {A B YL YR XL XR : List ℕ} (h : KMSWWindowPatchRel G₀ G F φ A B YL YR XL XR)
    (hb : ∀ e ∈ F.UL ++ F.UR ++ F.LL ++ F.LR, e < F.nextEdge)
    (ha : F.active < F.nextEdge) (hφ : ∀ e < F.nextEdge, φ' e = φ e) :
    KMSWWindowPatchRel G₀ G F φ' A B YL YR XL XR := by
  have hUL (e) (he : e ∈ F.UL) := hb e (by simp only [List.mem_append]; tauto)
  have hUR (e) (he : e ∈ F.UR) := hb e (by simp only [List.mem_append]; tauto)
  have hLL (e) (he : e ∈ XL ++ YL) : e < F.nextEdge := by
    apply hb e
    rw [← h.ll_split] at he
    simp only [List.mem_append]
    tauto
  have hLR (e) (he : e ∈ [0] ++ YR ++ XR) : e < F.nextEdge := by
    apply hb e
    rw [← h.lr_split] at he
    simp only [List.mem_append]
    tauto
  have hm (l : List ℕ) (hl : ∀ e ∈ l, e < F.nextEdge) : l.map φ' = l.map φ :=
    List.map_congr_left (fun e he => hφ e (hl e he))
  have hmYL := hm YL (fun e he => hLL e (by simp only [List.mem_append]; tauto))
  have hmXL := hm XL (fun e he => hLL e (by simp only [List.mem_append]; tauto))
  have hmYR := hm YR (fun e he => hLR e (by simp only [List.mem_append]; tauto))
  have hmXR := hm XR (fun e he => hLR e (by simp only [List.mem_append]; tauto))
  refine { h with
    ul := by rw [hm F.UL hUL]; exact h.ul
    ur := by rw [hm F.UR hUR]; exact h.ur
    left_residual := by rw [hmYL]; exact h.left_residual
    ll := by rw [hmXL]; exact h.ll
    right_residual := by rw [hmYR]; exact h.right_residual
    lr := by rw [hmXR]; exact h.lr
    root := by rw [hφ 0 (hLR 0 (by simp))]; exact h.root
    active := by rw [hφ F.active ha]; exact h.active
    edge_bound := ?_
    edge_injective := ?_
    fresh_image := ?_
    present := ?_ }
  · intro e he
    rw [hφ e he]
    exact h.fresh_image e he
  · intro e he
    rw [hφ e he]
    exact h.edge_bound e he
  · intro e he f hf hef
    rw [hφ e he, hφ f hf] at hef
    exact h.edge_injective e he f hf hef
  · intro e he hp
    rw [hφ e he]
    exact h.present e he hp

 
theorem kmswWindowPatchRel_down_existing {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {A B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A B YL YR XL XR)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage u j).UR = e :: es) :
    KMSWWindowPatchRel G₀ (kmswStepOfStep G .down)
      (kmswStepOfStep (kmswStage u j) .down) φ A B YL YR XL XR := by
  have hGUR : G.UR = φ e :: (es.map φ ++ B) := by
    rw [h.ur, hUR, List.map_cons, List.cons_append]
  have he : e < (kmswStage u j).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge u j).2
    simp only [List.mem_append]
    have : e ∈ (kmswStage u j).UR := by rw [hUR]; simp
    tauto
  simp only [kmswStepOfStep, hUR, hGUR]
  refine { h with
    ul := ?_
    ur := rfl
    active := rfl
    present := ?_ }
  · simp only [h.ul, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  · intro f hf hp
    change (if f = e then true else (kmswStage u j).present f) = true at hp
    change (if φ f = φ e then true else G.present (φ f)) = true
    by_cases hfe : f = e
    · simp only [hfe, ite_true]
    · have hne : φ f ≠ φ e := fun hh => hfe (h.edge_injective f hf e he hh)
      rw [ite_eq_right hne]
      rw [ite_eq_right hfe] at hp
      exact h.present f hf hp

private theorem extend_alloc {n N : ℕ} {φ : ℕ → ℕ}
    (hb : ∀ e < n, φ e < N)
    (hi : ∀ e < n, ∀ f < n, φ e = φ f → e = f) (k : ℕ) :
    let φ' := fun e => if e < n then φ e else N + (e - n)
    (∀ e < n + k, φ' e < N + k) ∧
    (∀ e < n + k, ∀ f < n + k, φ' e = φ' f → e = f) := by
  dsimp only
  constructor
  · intro e he
    by_cases hen : e < n
    · rw [ite_eq_left hen]
      have := hb e hen
      omega
    · rw [ite_eq_right hen]
      omega
  · intro e he f hf hef
    by_cases hen : e < n <;> by_cases hfn : f < n
    · simp only [ite_eq_left hen, ite_eq_left hfn] at hef
      exact hi e hen f hfn hef
    · simp only [ite_eq_left hen, ite_eq_right hfn] at hef
      have := hb e hen
      omega
    · simp only [ite_eq_right hen, ite_eq_left hfn] at hef
      have := hb f hfn
      omega
    · simp only [ite_eq_right hen, ite_eq_right hfn] at hef
      omega

private theorem extend_avoids {n N k : ℕ} {φ : ℕ → ℕ} {A B : List ℕ}
    (hb : ∀ e ∈ A ++ B, e < N)
    (hi : ∀ e < n, φ e ∉ A ∧ φ e ∉ B) :
    ∀ e < n + k,
      (if e < n then φ e else N + (e - n)) ∉ A ∧
      (if e < n then φ e else N + (e - n)) ∉ B := by
  intro e _
  by_cases he : e < n
  · simpa only [ite_eq_left he] using hi e he
  · simp only [ite_eq_right he]
    constructor <;> intro hm
    · have := hb _ (List.mem_append_left B hm)
      omega
    · have := hb _ (List.mem_append_right A hm)
      omega

 
theorem kmswWindowPatchRel_down_fresh {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {A YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A [] YL YR XL XR)
    (hUR : (kmswStage u j).UR = []) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else G.nextEdge + (e - F.nextEdge)
    KMSWWindowPatchRel G₀ (kmswStepOfStep G .down) (kmswStepOfStep F .down)
      φ' A [] YL YR XL (XR ++ [F.nextEdge]) := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else G.nextEdge + (e - F.nextEdge)
  have ho (e) (he : e < F.nextEdge) : φ' e = φ e := by
    exact ite_eq_left he
  have hn : φ' F.nextEdge = G.nextEdge := by simp [φ']
  have h' := relabel h (kmswStage_boundary_ids_lt_nextEdge u j).2
    (kmswStage_boundary_ids_lt_nextEdge u j).1 ho
  have hGUR : G.UR = [] := by simp only [h.ur, hUR, List.map_nil, List.append_nil]
  dsimp only [F] at hn
  have hext := extend_alloc h.edge_bound h.edge_injective 1
  change KMSWWindowPatchRel G₀ _ _ φ' _ _ _ _ _ _
  simp only [kmswStepOfStep, hUR, hGUR, State.addEdge]
  refine {
    xr_nil := fun hn => (hn rfl).elim
    xl_nil := h.xl_nil
    residual_bound := fun e he => lt_of_lt_of_le (h.residual_bound e he) (by dsimp only; omega)
    residual_nodup := h.residual_nodup
    fresh_image := extend_avoids (k := 1) h.residual_bound h.fresh_image
    ll_split := h.ll_split
    lr_split := ?_
    ul := ?_
    ur := by simp only [List.map_nil, List.append_nil]
    left_residual := h'.left_residual
    ll := h'.ll
    right_residual := h'.right_residual
    lr := ?_
    root := h'.root
    active := hn
    edge_bound := hext.1
    edge_injective := hext.2
    present := ?_ }
  · simp only [h.lr_split, List.append_assoc]
  · simp only [h'.ul, List.map_append, List.map_cons, List.map_nil, hn,
      List.append_assoc]
  · simp only [h'.lr, List.map_append, List.map_cons, List.map_nil, hn,
      List.append_assoc]
  · intro e he hp
    change e < F.nextEdge + 1 at he
    change (if e = F.nextEdge then true else F.present e) = true at hp
    change (if φ' e = G.nextEdge then true else G.present (φ' e)) = true
    by_cases hen : e < F.nextEdge
    · have hb := h'.edge_bound e hen
      have hne : e ≠ F.nextEdge := by omega
      have hgne : φ' e ≠ G.nextEdge := by omega
      rw [ite_eq_right hgne]
      rw [ite_eq_right hne] at hp
      exact h'.present e hen hp
    · have heq : e = F.nextEdge := by omega
      rw [heq, show φ' F.nextEdge = G.nextEdge from hn]
      exact ite_eq_left rfl

 
theorem kmswWindowPatchRel_up {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {A B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A B YL YR XL XR) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else G.nextEdge + (e - F.nextEdge)
    KMSWWindowPatchRel G₀ (kmswStepOfStep G .up) (kmswStepOfStep F .up)
      φ' A B YL YR XL XR := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else G.nextEdge + (e - F.nextEdge)
  have ho (e) (he : e < F.nextEdge) : φ' e = φ e := ite_eq_left he
  have hn : φ' F.nextEdge = G.nextEdge := by simp [φ']
  have hn' : φ' (F.nextEdge + 1) = G.nextEdge + 1 := by simp [φ']
  have h' := relabel h (kmswStage_boundary_ids_lt_nextEdge u j).2
    (kmswStage_boundary_ids_lt_nextEdge u j).1 ho
  have hne : F.UL.map φ' ≠ [] := by
    change (kmswStage u j).UL.map φ' ≠ []
    intro hz
    exact (kmswStage_UL_nonempty_active_last u j).1 (List.map_eq_nil_iff.mp hz)
  have hdrop : G.UL.dropLast = A ++ F.UL.dropLast.map φ' := by
    rw [h'.ul, List.dropLast_append_of_ne_nil hne, List.map_dropLast]
  dsimp only [F] at hn hn' hdrop
  have hext := extend_alloc h.edge_bound h.edge_injective 2
  change KMSWWindowPatchRel G₀ _ _ φ' _ _ _ _ _ _
  simp only [kmswStepOfStep, State.addEdge]
  refine {
    xr_nil := h.xr_nil
    xl_nil := h.xl_nil
    residual_bound := fun e he => lt_of_lt_of_le (h.residual_bound e he) (by dsimp only; omega)
    residual_nodup := h.residual_nodup
    fresh_image := extend_avoids (k := 2) h.residual_bound h.fresh_image
    ll_split := h.ll_split
    lr_split := h.lr_split
    ul := ?_
    ur := ?_
    left_residual := h'.left_residual
    ll := h'.ll
    right_residual := h'.right_residual
    lr := h'.lr
    root := h'.root
    active := hn
    edge_bound := hext.1
    edge_injective := hext.2
    present := ?_ }
  · simp only [hdrop, List.map_append, List.map_cons, List.map_nil, hn,
      List.append_assoc]
  · simp only [h'.ur, List.map_cons, hn', List.cons_append]
  · intro e he hp
    change e < F.nextEdge + 2 at he
    change (if e = F.nextEdge + 1 then false else
      if e = F.nextEdge then true else F.present e) = true at hp
    change (if φ' e = G.nextEdge + 1 then false else
      if φ' e = G.nextEdge then true else G.present (φ' e)) = true
    by_cases hen : e < F.nextEdge
    · have hb := h'.edge_bound e hen
      have hne₁ : e ≠ F.nextEdge := by omega
      have hne₂ : e ≠ F.nextEdge + 1 := by omega
      have hgne₁ : φ' e ≠ G.nextEdge := by omega
      have hgne₂ : φ' e ≠ G.nextEdge + 1 := by omega
      rw [ite_eq_right hgne₂, ite_eq_right hgne₁]
      rw [ite_eq_right hne₂, ite_eq_right hne₁] at hp
      exact h'.present e hen hp
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · rw [heq, show φ' F.nextEdge = G.nextEdge from hn]
        simp only [Nat.ne_add_one, ite_false, ite_true]
      · simp only [heq, ite_true, Bool.false_eq_true] at hp

 
theorem kmswWindowPatchRel_left_existing {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {A B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A B YL YR XL XR)
    (e : ℕ) (es : List ℕ) (hstack : (kmswStage u j).UL.dropLast.reverse = e :: es) :
    let F := kmswStage u j
    let φ' := fun f => if f < F.nextEdge then φ f else G.nextEdge + (f - F.nextEdge)
    KMSWWindowPatchRel G₀ (kmswStepOfStep G .left) (kmswStepOfStep F .left)
      φ' A B YL YR XL XR := by
  let F := kmswStage u j
  let φ' := fun f => if f < F.nextEdge then φ f else G.nextEdge + (f - F.nextEdge)
  have ho (f) (hf : f < F.nextEdge) : φ' f = φ f := ite_eq_left hf
  have hn : φ' F.nextEdge = G.nextEdge := by simp [φ']
  have h' := relabel h (kmswStage_boundary_ids_lt_nextEdge u j).2
    (kmswStage_boundary_ids_lt_nextEdge u j).1 ho
  have hne : (kmswStage u j).UL.map φ' ≠ [] := by
    intro hz
    exact (kmswStage_UL_nonempty_active_last u j).1 (List.map_eq_nil_iff.mp hz)
  have hGstack : G.UL.dropLast.reverse = φ' e :: (A ++ es.reverse.map φ').reverse := by
    rw [h'.ul, List.dropLast_append_of_ne_nil hne, ← List.map_dropLast]
    have hd : (kmswStage u j).UL.dropLast = (e :: es).reverse := by
      rw [← hstack, List.reverse_reverse]
    rw [hd]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_nil, List.nil_append, List.cons_append]
  have hext := extend_alloc h.edge_bound h.edge_injective 1
  dsimp only [F] at hn
  change KMSWWindowPatchRel G₀ _ _ φ' _ _ _ _ _ _
  simp only [kmswStepOfStep, hstack, hGstack, List.reverse_reverse, State.addEdge]
  refine {
    xr_nil := h.xr_nil
    xl_nil := h.xl_nil
    residual_bound := fun e he => lt_of_lt_of_le (h.residual_bound e he) (by dsimp only; omega)
    residual_nodup := h.residual_nodup
    fresh_image := extend_avoids (k := 1) h.residual_bound h.fresh_image
    ll_split := h.ll_split
    lr_split := h.lr_split
    ul := ?_
    ur := h'.ur
    left_residual := h'.left_residual
    ll := h'.ll
    right_residual := h'.right_residual
    lr := h'.lr
    root := h'.root
    active := hn
    edge_bound := hext.1
    edge_injective := hext.2
    present := ?_ }
  · simp only [List.map_append, List.map_cons, List.map_nil, hn, List.append_assoc]
  · intro f hf hp
    change f < F.nextEdge + 1 at hf
    change (if f = F.nextEdge then true else F.present f) = true at hp
    change (if φ' f = G.nextEdge then true else G.present (φ' f)) = true
    by_cases hfn : f < F.nextEdge
    · have hb := h'.edge_bound f hfn
      have hnf : f ≠ F.nextEdge := by omega
      have hng : φ' f ≠ G.nextEdge := by omega
      rw [ite_eq_right hng]
      rw [ite_eq_right hnf] at hp
      exact h'.present f hfn hp
    · have heq : f = F.nextEdge := by omega
      rw [heq, show φ' F.nextEdge = G.nextEdge from hn]
      exact ite_eq_left rfl

 
theorem kmswWindowPatchRel_left_fresh {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ [] B YL YR XL XR)
    (hstack : (kmswStage u j).UL.dropLast = []) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else G.nextEdge + (e - F.nextEdge)
    KMSWWindowPatchRel G₀ (kmswStepOfStep G .left) (kmswStepOfStep F .left)
      φ' [] B YL YR ((F.nextEdge + 1) :: XL) XR := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else G.nextEdge + (e - F.nextEdge)
  have ho (e) (he : e < F.nextEdge) : φ' e = φ e := ite_eq_left he
  have hn : φ' F.nextEdge = G.nextEdge := by simp [φ']
  have hn' : φ' (F.nextEdge + 1) = G.nextEdge + 1 := by simp [φ']
  have h' := relabel h (kmswStage_boundary_ids_lt_nextEdge u j).2
    (kmswStage_boundary_ids_lt_nextEdge u j).1 ho
  have hGstack : G.UL.dropLast.reverse = [] := by
    rw [h'.ul, List.nil_append, ← List.map_dropLast, hstack]
    rfl
  have hFstack : (kmswStage u j).UL.dropLast.reverse = [] := by rw [hstack]; rfl
  have hext := extend_alloc h.edge_bound h.edge_injective 2
  dsimp only [F] at hn hn'
  change KMSWWindowPatchRel G₀ _ _ φ' _ _ _ _ _ _
  simp only [kmswStepOfStep, hFstack, hGstack, State.addEdge]
  refine {
    xr_nil := h.xr_nil
    xl_nil := fun hn => (hn rfl).elim
    residual_bound := fun e he => lt_of_lt_of_le (h.residual_bound e he) (by dsimp only; omega)
    residual_nodup := h.residual_nodup
    fresh_image := extend_avoids (k := 2) h.residual_bound h.fresh_image
    ll_split := ?_
    lr_split := h.lr_split
    ul := ?_
    ur := h'.ur
    left_residual := h'.left_residual
    ll := ?_
    right_residual := h'.right_residual
    lr := h'.lr
    root := h'.root
    active := hn
    edge_bound := hext.1
    edge_injective := hext.2
    present := ?_ }
  · simp only [h.ll_split, List.cons_append]
  · simp only [List.map_cons, List.map_nil, hn, List.nil_append]
  · simp only [h'.ll, List.map_cons, hn', List.cons_append]
  · intro e he hp
    change e < F.nextEdge + 2 at he
    change (if e = F.nextEdge + 1 then false else
      if e = F.nextEdge then true else F.present e) = true at hp
    change (if φ' e = G.nextEdge + 1 then false else
      if φ' e = G.nextEdge then true else G.present (φ' e)) = true
    by_cases hen : e < F.nextEdge
    · have hb := h'.edge_bound e hen
      have hne₁ : e ≠ F.nextEdge := by omega
      have hne₂ : e ≠ F.nextEdge + 1 := by omega
      have hgne₁ : φ' e ≠ G.nextEdge := by omega
      have hgne₂ : φ' e ≠ G.nextEdge + 1 := by omega
      rw [ite_eq_right hgne₂, ite_eq_right hgne₁]
      rw [ite_eq_right hne₂, ite_eq_right hne₁] at hp
      exact h'.present e hen hp
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · rw [heq, show φ' F.nextEdge = G.nextEdge from hn]
        simp only [Nat.ne_add_one, ite_false, ite_true]
      · simp only [heq, ite_true, Bool.false_eq_true] at hp


 
theorem kmswWindowPatchRel_down_seam {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {A B YL YR XL XR : List ℕ} {q : ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A (q :: B) YL YR XL XR)
    (hUR : (kmswStage u j).UR = []) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else q
    KMSWWindowPatchRel G₀ (kmswStepOfStep G .down) (kmswStepOfStep F .down)
      φ' A B YL (YR ++ [F.nextEdge]) XL XR := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else q
  have ho (e) (he : e < F.nextEdge) : φ' e = φ e := ite_eq_left he
  have hn : φ' F.nextEdge = q := by simp [φ']
  have h' := relabel h (kmswStage_boundary_ids_lt_nextEdge u j).2
    (kmswStage_boundary_ids_lt_nextEdge u j).1 ho
  have hGUR : G.UR = q :: B := by
    simp only [h.ur, hUR, List.map_nil, List.nil_append]
  have hXR : XR = [] := h.xr_nil (by simp)
  have hqb : q < G.nextEdge := h.residual_bound q (by simp)
  have hnd := List.nodup_append'.mp h.residual_nodup
  have hqA : q ∉ A := fun hm => hnd.2.2 hm (by simp)
  have hqB : q ∉ B := (List.nodup_cons.mp hnd.2.1).1
  have hqold (e) (he : e < F.nextEdge) : φ e ≠ q := by
    intro heq
    exact (h.fresh_image e he).2 (by simp [heq])
  dsimp only [F] at hn
  change KMSWWindowPatchRel G₀ _ _ φ' _ _ _ _ _ _
  simp only [kmswStepOfStep, hUR, hGUR, State.addEdge]
  refine {
    xr_nil := fun _ => hXR
    xl_nil := h.xl_nil
    residual_bound := ?_
    residual_nodup := ?_
    fresh_image := ?_
    ll_split := h.ll_split
    lr_split := ?_
    ul := ?_
    ur := by simp only [List.map_nil, List.nil_append]
    left_residual := h'.left_residual
    ll := h'.ll
    right_residual := ?_
    lr := h'.lr
    root := h'.root
    active := hn
    edge_bound := ?_
    edge_injective := ?_
    present := ?_ }
  · intro e he
    exact h.residual_bound e (by
      simp only [List.mem_append, List.mem_cons] at he ⊢; tauto)
  · exact List.nodup_append'.mpr ⟨hnd.1, (List.nodup_cons.mp hnd.2.1).2,
      fun e heA heB => hnd.2.2 heA (by simp only [List.mem_cons]; tauto)⟩
  · intro e he
    change e < F.nextEdge + 1 at he
    by_cases heo : e < F.nextEdge
    · rw [ho e heo]
      have hh := h.fresh_image e heo
      exact ⟨hh.1, fun hm => hh.2 (by simp only [List.mem_cons]; tauto)⟩
    · have heq : e = F.nextEdge := by omega
      rw [heq, hn]
      exact ⟨hqA, hqB⟩
  · simp only [h.lr_split, hXR, List.append_nil, List.append_assoc]
  · simp only [h'.ul, List.map_append, List.map_cons, List.map_nil, hn,
      List.append_assoc]
  · simp only [h'.right_residual, List.map_append, List.map_cons, List.map_nil, hn,
      List.append_assoc, List.cons_append, List.nil_append]
  · intro e he
    change e < F.nextEdge + 1 at he
    by_cases heo : e < F.nextEdge
    · rw [ho e heo]
      exact h.edge_bound e heo
    · have heq : e = F.nextEdge := by omega
      rw [heq, hn]
      exact hqb
  · intro e he f hf hef
    change e < F.nextEdge + 1 at he
    change f < F.nextEdge + 1 at hf
    by_cases heo : e < F.nextEdge <;> by_cases hfo : f < F.nextEdge
    · rw [ho e heo, ho f hfo] at hef
      exact h.edge_injective e heo f hfo hef
    · have hfeq : f = F.nextEdge := by omega
      rw [ho e heo, hfeq, hn] at hef
      exact (hqold e heo hef).elim
    · have heeq : e = F.nextEdge := by omega
      rw [heeq, hn, ho f hfo] at hef
      exact (hqold f hfo hef.symm).elim
    · omega
  · intro e he hp
    change e < F.nextEdge + 1 at he
    change (if e = F.nextEdge then true else F.present e) = true at hp
    change (if φ' e = q then true else G.present (φ' e)) = true
    by_cases heo : e < F.nextEdge
    · rw [ho e heo, ite_eq_right (hqold e heo)]
      have hne : e ≠ F.nextEdge := by omega
      rw [ite_eq_right hne] at hp
      exact h.present e heo hp
    · have heq : e = F.nextEdge := by omega
      rw [heq, hn]
      exact ite_eq_left rfl

 
theorem kmswWindowPatchRel_left_seam {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {A B YL YR XL XR : List ℕ} {q : ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ (A ++ [q]) B YL YR XL XR)
    (hstack : (kmswStage u j).UL.dropLast = []) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else
      if e = F.nextEdge then G.nextEdge else q
    KMSWWindowPatchRel G₀ (kmswStepOfStep G .left) (kmswStepOfStep F .left)
      φ' A B ((F.nextEdge + 1) :: YL) YR XL XR := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else
    if e = F.nextEdge then G.nextEdge else q
  have ho (e) (he : e < F.nextEdge) : φ' e = φ e := ite_eq_left he
  have hn : φ' F.nextEdge = G.nextEdge := by simp [φ']
  have hp : φ' (F.nextEdge + 1) = q := by simp [φ']
  have h' := relabel h (kmswStage_boundary_ids_lt_nextEdge u j).2
    (kmswStage_boundary_ids_lt_nextEdge u j).1 ho
  have hne : (kmswStage u j).UL.map φ' ≠ [] := by
    intro hz
    exact (kmswStage_UL_nonempty_active_last u j).1 (List.map_eq_nil_iff.mp hz)
  have hGstack : G.UL.dropLast.reverse = q :: A.reverse := by
    rw [h'.ul, List.dropLast_append_of_ne_nil hne, ← List.map_dropLast, hstack]
    simp only [List.map_nil, List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append]
  have hFstack : (kmswStage u j).UL.dropLast.reverse = [] := by rw [hstack]; rfl
  have hXL : XL = [] := h.xl_nil (by simp)
  have hqb : q < G.nextEdge := h.residual_bound q (by simp)
  have hnd := List.nodup_append'.mp h.residual_nodup
  have hAnd := List.nodup_append'.mp hnd.1
  have hqA : q ∉ A := fun hm => hAnd.2.2 hm (by simp)
  have hqB : q ∉ B := fun hm => hnd.2.2 (by simp) hm
  have hqold (e) (he : e < F.nextEdge) : φ e ≠ q := by
    intro heq
    exact (h.fresh_image e he).1 (by simp [heq])
  dsimp only [F] at hn hp
  change KMSWWindowPatchRel G₀ _ _ φ' _ _ _ _ _ _
  simp only [kmswStepOfStep, hFstack, hGstack, State.addEdge, List.reverse_reverse]
  refine {
    xr_nil := h.xr_nil
    xl_nil := fun _ => hXL
    residual_bound := ?_
    residual_nodup := ?_
    fresh_image := ?_
    ll_split := ?_
    lr_split := h.lr_split
    ul := ?_
    ur := h'.ur
    left_residual := ?_
    ll := h'.ll
    right_residual := h'.right_residual
    lr := h'.lr
    root := h'.root
    active := hn
    edge_bound := ?_
    edge_injective := ?_
    present := ?_ }
  · intro e he
    have hb := h.residual_bound e (by
      simp only [List.mem_append, List.mem_singleton] at he ⊢; tauto)
    dsimp only
    omega
  · exact List.nodup_append'.mpr ⟨hAnd.1, hnd.2.1,
      fun e heA heB => hnd.2.2 (List.mem_append_left _ heA) heB⟩
  · intro e he
    change e < F.nextEdge + 1 + 1 at he
    by_cases heo : e < F.nextEdge
    · rw [ho e heo]
      have hh := h.fresh_image e heo
      exact ⟨fun hm => hh.1 (List.mem_append_left _ hm), hh.2⟩
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · rw [heq, show φ' F.nextEdge = G.nextEdge from hn]
        constructor <;> intro hm
        · have hb := h.residual_bound _ (by
            simp only [List.mem_append]; exact Or.inl (Or.inl hm))
          omega
        · have hb := h.residual_bound _ (List.mem_append_right _ hm)
          omega
      · rw [heq, show φ' (F.nextEdge + 1) = q from hp]
        exact ⟨hqA, hqB⟩
  · simp only [h.ll_split, hXL, List.nil_append]
  · simp only [List.map_cons, List.map_nil, hn]
  · simp only [h'.left_residual, List.map_cons, hp, List.append_assoc,
      List.cons_append, List.nil_append]
  · intro e he
    change e < F.nextEdge + 1 + 1 at he
    change φ' e < G.nextEdge + 1
    by_cases heo : e < F.nextEdge
    · rw [ho e heo]
      have := h.edge_bound e heo
      omega
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · rw [heq, show φ' F.nextEdge = G.nextEdge from hn]
        omega
      · rw [heq, show φ' (F.nextEdge + 1) = q from hp]
        omega
  · intro e he f hf hef
    change e < F.nextEdge + 1 + 1 at he
    change f < F.nextEdge + 1 + 1 at hf
    by_cases heo : e < F.nextEdge <;> by_cases hfo : f < F.nextEdge
    · rw [ho e heo, ho f hfo] at hef
      exact h.edge_injective e heo f hfo hef
    · rw [ho e heo] at hef
      have hfq : f = F.nextEdge ∨ f = F.nextEdge + 1 := by omega
      rcases hfq with hfq | hfq
      · rw [hfq, show φ' F.nextEdge = G.nextEdge from hn] at hef
        have := h.edge_bound e heo
        omega
      · rw [hfq, show φ' (F.nextEdge + 1) = q from hp] at hef
        exact (hqold e heo hef).elim
    · rw [ho f hfo] at hef
      have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · rw [heq, show φ' F.nextEdge = G.nextEdge from hn] at hef
        have := h.edge_bound f hfo
        omega
      · rw [heq, show φ' (F.nextEdge + 1) = q from hp] at hef
        exact (hqold f hfo hef.symm).elim
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      have hfq : f = F.nextEdge ∨ f = F.nextEdge + 1 := by omega
      rcases heq with heq | heq <;> rcases hfq with hfq | hfq
      · omega
      · rw [heq, hfq, show φ' F.nextEdge = G.nextEdge from hn,
          show φ' (F.nextEdge + 1) = q from hp] at hef
        omega
      · rw [heq, hfq, show φ' F.nextEdge = G.nextEdge from hn,
          show φ' (F.nextEdge + 1) = q from hp] at hef
        omega
      · omega
  · intro e he hpr
    change e < F.nextEdge + 1 + 1 at he
    change (if e = F.nextEdge + 1 then false else
      if e = F.nextEdge then true else F.present e) = true at hpr
    change (if φ' e = G.nextEdge then true else G.present (φ' e)) = true
    by_cases heo : e < F.nextEdge
    · rw [ho e heo]
      have hb := h.edge_bound e heo
      have hgn : φ e ≠ G.nextEdge := by omega
      have hne₁ : e ≠ F.nextEdge := by omega
      have hne₂ : e ≠ F.nextEdge + 1 := by omega
      rw [ite_eq_right hgn]
      rw [ite_eq_right hne₂, ite_eq_right hne₁] at hpr
      exact h.present e heo hpr
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · rw [heq, show φ' F.nextEdge = G.nextEdge from hn]
        exact ite_eq_left rfl
      · simp only [heq, ite_true, Bool.false_eq_true] at hpr

private theorem window_step {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {φ : ℕ → ℕ} {A B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A B YL YR XL XR) :
    ∃ φ' A' B' YL' YR' XL' XR',
      KMSWWindowPatchRel G₀ (kmswStep G (u j)) (kmswStage u (j + 1))
        φ' A' B' YL' YR' XL' XR' := by
  change ∃ φ' A' B' YL' YR' XL' XR',
    KMSWWindowPatchRel G₀ (kmswStepOfStep G (kmswCodeStep (u j)))
      (kmswStepOfStep (kmswStage u j) (kmswCodeStep (u j)))
      φ' A' B' YL' YR' XL' XR'
  cases hc : kmswCodeStep (u j) with
  | down =>
    cases hu : (kmswStage u j).UR with
    | cons e es =>
      exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_down_existing h e es hu⟩
    | nil =>
      cases B with
      | nil => exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_down_fresh h hu⟩
      | cons q B => exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_down_seam h hu⟩
  | up => exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_up h⟩
  | left =>
    cases hs : (kmswStage u j).UL.dropLast.reverse with
    | cons e es =>
      exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_left_existing h e es hs⟩
    | nil =>
      have hs' : (kmswStage u j).UL.dropLast = [] := by
        have hh := congrArg List.reverse hs
        simpa only [List.reverse_reverse, List.reverse_nil] using hh
      cases ha : A.reverse with
      | nil =>
        have ha' : A = [] := by
          have hh := congrArg List.reverse ha
          simpa only [List.reverse_reverse, List.reverse_nil] using hh
        subst A
        exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_left_fresh h hs'⟩
      | cons q es =>
        have ha' : A = es.reverse ++ [q] := by
          have hh := congrArg List.reverse ha
          simpa only [List.reverse_reverse, List.reverse_cons] using hh
        rw [ha'] at h
        exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_left_seam h hs'⟩

 
@[expose] def KMSWWindowPatchRel.edgeEmbedding {G₀ G F : State} {φ : ℕ → ℕ}
    {A B YL YR XL XR : List ℕ} (h : KMSWWindowPatchRel G₀ G F φ A B YL YR XL XR) :
    Fin F.nextEdge ↪ Fin G.nextEdge where
  toFun e := ⟨φ e.val, h.edge_bound e.val e.isLt⟩
  inj' := by
    intro e f hef
    apply Fin.ext
    exact h.edge_injective e.val e.isLt f.val f.isLt (congrArg Fin.val hef)

 
theorem kmswWindowPatchRel_run (w : ℕ → Fin 3) (s m : ℕ) :
    let u := fun i => w (s + i)
    ∀ j ≤ m, ∃ φ A B YL YR XL XR,
      KMSWWindowPatchRel (kmswStage w s) (kmswStage w (s + j)) (kmswStage u j)
        φ A B YL YR XL XR := by
  intro u
  have hrun : ∀ j, ∃ φ A B YL YR XL XR,
      KMSWWindowPatchRel (kmswStage w s) (kmswRun (kmswStage w s) u j)
        (kmswStage u j) φ A B YL YR XL XR := by
    intro j
    induction j with
    | zero =>
      exact ⟨_, _, _, _, _, _, _, kmswWindowPatchRel_init w s⟩
    | succ j ih =>
      obtain ⟨φ, A, B, YL, YR, XL, XR, h⟩ := ih
      exact window_step h
  intro j _
  obtain ⟨φ, A, B, YL, YR, XL, XR, h⟩ := hrun j
  rw [kmswRun_shift_eq_stage] at h
  exact ⟨φ, A, B, YL, YR, XL, XR, h⟩

 
@[expose] noncomputable def kmswWindowEdgeEmbedding (w : ℕ → Fin 3) (s m : ℕ) :
    Fin (kmswStage (fun i => w (s + i)) m).nextEdge ↪
      Fin (kmswStage w (s + m)).nextEdge :=
  Classical.choice (by
    obtain ⟨φ, A, B, YL, YR, XL, XR, h⟩ := kmswWindowPatchRel_run w s m m (le_refl m)
    exact ⟨h.edgeEmbedding⟩)

end DirectedDistances.KMSW
