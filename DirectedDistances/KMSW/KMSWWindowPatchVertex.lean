/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWWindowPatchTriangles
public import DirectedDistances.KMSW.KMSWWindowPatchRotation
import DirectedDistances.KMSW.StageIncidenceChains






public section
namespace DirectedDistances.KMSW



structure KMSWWindowPatchVertexRel (G F : State) (φ ψ : ℕ → ℕ) : Prop where
  vertex_bound : ∀ v < F.nextVertex, ψ v < G.nextVertex
  west_endpoint : ∀ e < F.nextEdge, ψ (F.west e) = G.west (φ e)
  east_endpoint : ∀ e < F.nextEdge, ψ (F.east e) = G.east (φ e)

/-- initial vertex map for a shifted window, with the two root endpoints sent to
the global active edge endpoints; this is not the paper result. -/
theorem kmswWindowPatchVertexRel_init (w : ℕ → Fin 3) (s : ℕ) :
    KMSWWindowPatchVertexRel (kmswStage w s) kmswInit
      (fun _ => (kmswStage w s).active)
      (fun v => if v = 0 then (kmswStage w s).west (kmswStage w s).active
        else (kmswStage w s).east (kmswStage w s).active) := by
  let G₀ := kmswStage w s
  let ψ₀ := fun v => if v = 0 then G₀.west G₀.active else G₀.east G₀.active
  have ha := (kmswStage_boundary_ids_lt_nextEdge w s).1
  have hv := kmswStage_endpoints_lt_nextVertex w s G₀.active ha
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    change v < 2 at hv'
    change ψ₀ v < G₀.nextVertex
    by_cases hzero : v = 0
    · simp only [ψ₀, hzero]
      exact hv.1
    · have hone : v = 1 := by omega
      simp only [ψ₀, hone]
      exact hv.2
  · intro e he
    change e < 1 at he
    have he0 : e = 0 := by omega
    subst e
    change ψ₀ (kmswInit.west 0) = G₀.west G₀.active
    simp [ψ₀, kmswInit]
  · intro e he
    change e < 1 at he
    have he0 : e = 0 := by omega
    subst e
    change ψ₀ (kmswInit.east 0) = G₀.east G₀.active
    simp [ψ₀, kmswInit]

/-- The vertex relation is preserved when down activates an existing upper
right edge. -/
theorem kmswWindowPatchVertexRel_down_existing {G₀ G : State}
    {u : ℕ → Fin 3} {j : ℕ} {φ ψ : ℕ → ℕ}
    {A B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A B YL YR XL XR)
    (hv : KMSWWindowPatchVertexRel G (kmswStage u j) φ ψ)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage u j).UR = e :: es) :
    KMSWWindowPatchVertexRel (kmswStepOfStep G .down)
      (kmswStepOfStep (kmswStage u j) .down) φ ψ := by
  have hGUR : G.UR = φ e :: (es.map φ ++ B) := by
    rw [h.ur, hUR, List.map_cons, List.cons_append]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    have hvold : v < (kmswStage u j).nextVertex := by
      simpa only [kmswStepOfStep, hUR] using hv'
    simpa only [kmswStepOfStep, hGUR] using hv.vertex_bound v hvold
  · intro f hf
    have hfold : f < (kmswStage u j).nextEdge := by
      simpa only [kmswStepOfStep, hUR] using hf
    simpa only [kmswStepOfStep, hUR, hGUR] using hv.west_endpoint f hfold
  · intro f hf
    have hfold : f < (kmswStage u j).nextEdge := by
      simpa only [kmswStepOfStep, hUR] using hf
    simpa only [kmswStepOfStep, hUR, hGUR] using hv.east_endpoint f hfold

/-- A fresh down step extends the vertex map to the new terminal vertex. -/
theorem kmswWindowPatchVertexRel_down_fresh {G₀ G : State}
    {u : ℕ → Fin 3} {j : ℕ} {φ ψ : ℕ → ℕ}
    {A YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A [] YL YR XL XR)
    (hv : KMSWWindowPatchVertexRel G (kmswStage u j) φ ψ)
    (hUR : (kmswStage u j).UR = []) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else
      G.nextEdge + (e - F.nextEdge)
    let ψ' := fun v => if v < F.nextVertex then ψ v else G.nextVertex
    KMSWWindowPatchVertexRel (kmswStepOfStep G .down)
      (kmswStepOfStep F .down) φ' ψ' := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else
    G.nextEdge + (e - F.nextEdge)
  let ψ' := fun v => if v < F.nextVertex then ψ v else G.nextVertex
  have hGUR : G.UR = [] := by
    simp only [h.ur, hUR, List.map_nil, List.nil_append]
  have hactive := (kmswStage_boundary_ids_lt_nextEdge u j).1
  have hnew : φ' F.nextEdge = G.nextEdge := by simp [φ']
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    simp only [kmswStepOfStep, hUR, hGUR, State.addEdge] at hv' ⊢
    change v < F.nextVertex + 1 at hv'
    change ψ' v < G.nextVertex + 1
    by_cases hold : v < F.nextVertex
    · rw [show ψ' v = ψ v by simp [ψ', hold]]
      exact Nat.lt_succ_of_lt (hv.vertex_bound v hold)
    · have heq : v = F.nextVertex := by omega
      subst v
      simp only [ψ', Nat.lt_irrefl, ite_false]
      exact Nat.lt_succ_self _
  · intro e he
    simp only [kmswStepOfStep, hUR] at he
    change e < F.nextEdge + 1 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne : φ e ≠ G.nextEdge := by omega
      simp only [kmswStepOfStep, hUR, hGUR, State.addEdge]
      rw [ite_eq_right (Nat.ne_of_lt hold)]
      change ψ' (F.west e) =
        (if φ' e = G.nextEdge then G.east G.active else G.west (φ' e))
      rw [show ψ' (F.west e) = ψ (F.west e) by simp [F, ψ', hends.1]]
      rw [show φ' e = φ e by simp [φ', hold], ite_eq_right hφne]
      exact hv.west_endpoint e hold
    · have heq : e = F.nextEdge := by omega
      subst e
      have hends := hv.east_endpoint F.active hactive
      have hvbound := kmswStage_endpoints_lt_nextVertex u j F.active hactive
      simp [F, kmswStepOfStep, hUR, hGUR, State.addEdge, h.active,
        hends, hvbound.2]
  · intro e he
    simp only [kmswStepOfStep, hUR] at he
    change e < F.nextEdge + 1 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne : φ e ≠ G.nextEdge := by omega
      simp only [kmswStepOfStep, hUR, hGUR, State.addEdge]
      rw [ite_eq_right (Nat.ne_of_lt hold)]
      change ψ' (F.east e) =
        (if φ' e = G.nextEdge then G.nextVertex else G.east (φ' e))
      rw [show ψ' (F.east e) = ψ (F.east e) by simp [F, ψ', hends.2]]
      rw [show φ' e = φ e by simp [φ', hold], ite_eq_right hφne]
      exact hv.east_endpoint e hold
    · have heq : e = F.nextEdge := by omega
      subst e
      simp [F, kmswStepOfStep, hUR, hGUR, State.addEdge]

/-- A down seam extends the vertex map to the endpoint of the consumed global
boundary edge. -/
theorem kmswWindowPatchVertexRel_down_seam {G₀ : State} {w : ℕ → Fin 3}
    {n : ℕ} {u : ℕ → Fin 3} {j : ℕ} {φ ψ : ℕ → ℕ}
    {A B YL YR XL XR : List ℕ} {q : ℕ}
    (h : KMSWWindowPatchRel G₀ (kmswStage w n) (kmswStage u j) φ A
      (q :: B) YL YR XL XR)
    (hv : KMSWWindowPatchVertexRel (kmswStage w n) (kmswStage u j) φ ψ)
    (hUR : (kmswStage u j).UR = []) :
    let G := kmswStage w n
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else q
    let ψ' := fun v => if v < F.nextVertex then ψ v else G.east q
    KMSWWindowPatchVertexRel (kmswStepOfStep G .down)
      (kmswStepOfStep F .down) φ' ψ' := by
  let G := kmswStage w n
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else q
  let ψ' := fun v => if v < F.nextVertex then ψ v else G.east q
  have hGUR : G.UR = q :: B := by
    change (kmswStage w n).UR = q :: B
    rw [h.ur, hUR]
    simp
  have hhead : G.west q = G.east G.active :=
    (kmswStage_boundary_chain_invariant w n).2.2.2.2.2.1 q B hGUR
  have hqb : q < G.nextEdge := h.residual_bound q (by simp)
  have hGlobalEnd := kmswStage_endpoints_lt_nextVertex w n q hqb
  have hactive := (kmswStage_boundary_ids_lt_nextEdge u j).1
  have hLocalEnd := kmswStage_endpoints_lt_nextVertex u j F.active hactive
  have hnew : φ' F.nextEdge = q := by simp [φ']
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    simp only [G, kmswStepOfStep, hUR, hGUR, State.addEdge] at hv' ⊢
    change v < F.nextVertex + 1 at hv'
    change ψ' v < G.nextVertex
    by_cases hold : v < F.nextVertex
    · rw [show ψ' v = ψ v by simp [ψ', hold]]
      exact hv.vertex_bound v hold
    · have heq : v = F.nextVertex := by omega
      subst v
      simpa only [ψ', Nat.lt_irrefl, ite_false, G] using hGlobalEnd.2
  · intro e he
    simp only [kmswStepOfStep, hUR] at he
    change e < F.nextEdge + 1 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      simp only [G, kmswStepOfStep, hUR, hGUR, State.addEdge]
      rw [ite_eq_right (Nat.ne_of_lt hold)]
      change ψ' (F.west e) = G.west (φ' e)
      rw [show ψ' (F.west e) = ψ (F.west e) by simp [F, ψ', hends.1]]
      rw [show φ' e = φ e by simp [φ', hold]]
      exact hv.west_endpoint e hold
    · have heq : e = F.nextEdge := by omega
      subst e
      have hends := hv.east_endpoint F.active hactive
      simp [F, G, kmswStepOfStep, hUR, hGUR, State.addEdge, h.active,
        hhead, hends, hLocalEnd.2]
  · intro e he
    simp only [kmswStepOfStep, hUR] at he
    change e < F.nextEdge + 1 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      simp only [G, kmswStepOfStep, hUR, hGUR, State.addEdge]
      rw [ite_eq_right (Nat.ne_of_lt hold)]
      change ψ' (F.east e) = G.east (φ' e)
      rw [show ψ' (F.east e) = ψ (F.east e) by simp [F, ψ', hends.2]]
      rw [show φ' e = φ e by simp [φ', hold]]
      exact hv.east_endpoint e hold
    · have heq : e = F.nextEdge := by omega
      subst e
      simp [F, G, kmswStepOfStep, hUR, hGUR, State.addEdge]

/-- An up step extends the vertex map by the new top vertex. -/
theorem kmswWindowPatchVertexRel_up {G₀ G : State} {u : ℕ → Fin 3}
    {j : ℕ} {φ ψ : ℕ → ℕ} {A B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A B YL YR XL XR)
    (hv : KMSWWindowPatchVertexRel G (kmswStage u j) φ ψ) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else
      G.nextEdge + (e - F.nextEdge)
    let ψ' := fun v => if v < F.nextVertex then ψ v else G.nextVertex
    KMSWWindowPatchVertexRel (kmswStepOfStep G .up)
      (kmswStepOfStep F .up) φ' ψ' := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else
    G.nextEdge + (e - F.nextEdge)
  let ψ' := fun v => if v < F.nextVertex then ψ v else G.nextVertex
  have hactive := (kmswStage_boundary_ids_lt_nextEdge u j).1
  have hLocalEnd := kmswStage_endpoints_lt_nextVertex u j F.active hactive
  have hnew₀ : φ' F.nextEdge = G.nextEdge := by simp [φ']
  have hnew₁ : φ' (F.nextEdge + 1) = G.nextEdge + 1 := by simp [φ']
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    simp only [kmswStepOfStep, State.addEdge] at hv' ⊢
    change v < F.nextVertex + 1 at hv'
    change ψ' v < G.nextVertex + 1
    by_cases hold : v < F.nextVertex
    · rw [show ψ' v = ψ v by simp [ψ', hold]]
      exact Nat.lt_succ_of_lt (hv.vertex_bound v hold)
    · have heq : v = F.nextVertex := by omega
      subst v
      simp [ψ']
  · intro e he
    simp only [kmswStepOfStep, State.addEdge] at he
    change e < F.nextEdge + 2 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne₀ : φ e ≠ G.nextEdge := by omega
      have hφne₁ : φ e ≠ G.nextEdge + 1 := by omega
      have heq₀ : e ≠ F.nextEdge := by omega
      have heq₁ : e ≠ F.nextEdge + 1 := by omega
      simpa [F, kmswStepOfStep, State.addEdge, φ', ψ', hold, heq₀, heq₁,
        hends.1, hφne₀, hφne₁] using hv.west_endpoint e hold
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · subst e
        have hends := hv.west_endpoint F.active hactive
        simp [F, kmswStepOfStep, State.addEdge, h.active,
          hends, hLocalEnd.1]
      · subst e
        have hends := hv.east_endpoint F.active hactive
        simp [F, kmswStepOfStep, State.addEdge]
  · intro e he
    simp only [kmswStepOfStep, State.addEdge] at he
    change e < F.nextEdge + 2 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne₀ : φ e ≠ G.nextEdge := by omega
      have hφne₁ : φ e ≠ G.nextEdge + 1 := by omega
      have heq₀ : e ≠ F.nextEdge := by omega
      have heq₁ : e ≠ F.nextEdge + 1 := by omega
      simpa [F, kmswStepOfStep, State.addEdge, φ', ψ', hold, heq₀, heq₁,
        hends.2, hφne₀, hφne₁] using hv.east_endpoint e hold
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · subst e
        simp [F, kmswStepOfStep, State.addEdge]
      · subst e
        have hends := hv.east_endpoint F.active hactive
        simp [F, kmswStepOfStep, State.addEdge, h.active,
          hends, hLocalEnd.2]

/-- A left step using an existing predecessor preserves the vertex map. -/
theorem kmswWindowPatchVertexRel_left_existing {G₀ G : State}
    {u : ℕ → Fin 3} {j : ℕ} {φ ψ : ℕ → ℕ}
    {A B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ A B YL YR XL XR)
    (hv : KMSWWindowPatchVertexRel G (kmswStage u j) φ ψ)
    (e : ℕ) (es : List ℕ)
    (hstack : (kmswStage u j).UL.dropLast.reverse = e :: es) :
    let F := kmswStage u j
    let φ' := fun f => if f < F.nextEdge then φ f else
      G.nextEdge + (f - F.nextEdge)
    KMSWWindowPatchVertexRel (kmswStepOfStep G .left)
      (kmswStepOfStep F .left) φ' ψ := by
  let F := kmswStage u j
  let φ' := fun f => if f < F.nextEdge then φ f else
    G.nextEdge + (f - F.nextEdge)
  have ho (f : ℕ) (hf : f < F.nextEdge) : φ' f = φ f := by
    simp [φ', hf]
  have hφmap : F.UL.map φ' = F.UL.map φ := by
    apply List.map_congr_left
    intro f hf
    have hb := (kmswStage_boundary_ids_lt_nextEdge u j).2 f (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hf)))
    exact ho f hb
  have hUL : G.UL = A ++ F.UL.map φ' := by
    calc
      G.UL = A ++ F.UL.map φ := h.ul
      _ = A ++ F.UL.map φ' := by rw [← hφmap]
  have hne : F.UL.map φ' ≠ [] := by
    intro hz
    have hz' : F.UL = [] := List.map_eq_nil_iff.mp hz
    exact (kmswStage_UL_nonempty_active_last u j).1 hz'
  have hGstack : G.UL.dropLast.reverse = φ' e ::
      (A ++ es.reverse.map φ').reverse := by
    rw [hUL, List.dropLast_append_of_ne_nil hne, ← List.map_dropLast]
    have hd : F.UL.dropLast = (e :: es).reverse := by
      rw [← hstack, List.reverse_reverse]
    rw [hd]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_nil, List.nil_append, List.cons_append]
  have he : e < F.nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge u j).2
    have hem : e ∈ F.UL.dropLast.reverse := by rw [hstack]; simp
    have heUL : e ∈ F.UL := by
      rw [List.mem_reverse] at hem
      exact List.dropLast_subset _ hem
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl heUL))
  have hactive := (kmswStage_boundary_ids_lt_nextEdge u j).1
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    have hvold : v < F.nextVertex := by
      simpa only [kmswStepOfStep, hstack, hGstack, State.addEdge] using hv'
    simpa only [kmswStepOfStep, hstack, hGstack, State.addEdge] using
      hv.vertex_bound v hvold
  · intro f hf
    simp only [kmswStepOfStep, hstack, hGstack, State.addEdge] at hf ⊢
    change f < F.nextEdge + 1 at hf
    by_cases hold : f < F.nextEdge
    · have hfne : f ≠ F.nextEdge := by omega
      have hφbound := h.edge_bound f hold
      have hφne : φ f ≠ G.nextEdge := by omega
      rw [ite_eq_right hfne]
      have hφold : (if f < F.nextEdge then φ f else
          G.nextEdge + (f - F.nextEdge)) = φ f := by simp [hold]
      rw [hφold, ite_eq_right hφne]
      exact hv.west_endpoint f hold
    · have heq : f = F.nextEdge := by omega
      subst f
      simpa [F, φ', he] using hv.west_endpoint e he
  · intro f hf
    simp only [kmswStepOfStep, hstack, hGstack, State.addEdge] at hf ⊢
    change f < F.nextEdge + 1 at hf
    by_cases hold : f < F.nextEdge
    · have hfne : f ≠ F.nextEdge := by omega
      have hφbound := h.edge_bound f hold
      have hφne : φ f ≠ G.nextEdge := by omega
      rw [ite_eq_right hfne]
      have hφold : (if f < F.nextEdge then φ f else
          G.nextEdge + (f - F.nextEdge)) = φ f := by simp [hold]
      rw [hφold, ite_eq_right hφne]
      exact hv.east_endpoint f hold
    · have heq : f = F.nextEdge := by omega
      subst f
      simpa [F, φ', h.active] using hv.east_endpoint F.active hactive


 
theorem kmswWindowPatchVertexRel_left_fresh {G₀ G : State} {u : ℕ → Fin 3}
    {j : ℕ} {φ ψ : ℕ → ℕ} {B YL YR XL XR : List ℕ}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) φ [] B YL YR XL XR)
    (hv : KMSWWindowPatchVertexRel G (kmswStage u j) φ ψ)
    (hstack : (kmswStage u j).UL.dropLast = []) :
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else
      G.nextEdge + (e - F.nextEdge)
    let ψ' := fun v => if v < F.nextVertex then ψ v else G.nextVertex
    KMSWWindowPatchVertexRel (kmswStepOfStep G .left)
      (kmswStepOfStep F .left) φ' ψ' := by
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else
    G.nextEdge + (e - F.nextEdge)
  let ψ' := fun v => if v < F.nextVertex then ψ v else G.nextVertex
  have hFstack : (kmswStage u j).UL.dropLast.reverse = [] := by rw [hstack]; rfl
  have hGstack : G.UL.dropLast.reverse = [] := by
    rw [h.ul, List.nil_append, ← List.map_dropLast, hstack]
    rfl
  have hactive := (kmswStage_boundary_ids_lt_nextEdge u j).1
  have hLocalEnd := kmswStage_endpoints_lt_nextVertex u j F.active hactive
  have hnew₀ : φ' F.nextEdge = G.nextEdge := by simp [φ']
  have hnew₁ : φ' (F.nextEdge + 1) = G.nextEdge + 1 := by simp [φ']
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    simp only [kmswStepOfStep, hFstack, hGstack, State.addEdge] at hv' ⊢
    change v < F.nextVertex + 1 at hv'
    change ψ' v < G.nextVertex + 1
    by_cases hold : v < F.nextVertex
    · rw [show ψ' v = ψ v by simp [ψ', hold]]
      exact Nat.lt_succ_of_lt (hv.vertex_bound v hold)
    · have heq : v = F.nextVertex := by omega
      subst v
      simp [ψ']
  · intro e he
    simp only [kmswStepOfStep, hFstack, State.addEdge] at he
    change e < F.nextEdge + 2 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne₀ : φ e ≠ G.nextEdge := by omega
      have hφne₁ : φ e ≠ G.nextEdge + 1 := by omega
      have heq₀ : e ≠ F.nextEdge := by omega
      have heq₁ : e ≠ F.nextEdge + 1 := by omega
      simpa [F, kmswStepOfStep, hFstack, hGstack, State.addEdge, φ', ψ', hold, heq₀, heq₁,
        hends.1, hφne₀, hφne₁] using hv.west_endpoint e hold
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · subst e
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge]
      · subst e
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge]
  · intro e he
    simp only [kmswStepOfStep, hFstack, State.addEdge] at he
    change e < F.nextEdge + 2 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne₀ : φ e ≠ G.nextEdge := by omega
      have hφne₁ : φ e ≠ G.nextEdge + 1 := by omega
      have heq₀ : e ≠ F.nextEdge := by omega
      have heq₁ : e ≠ F.nextEdge + 1 := by omega
      simpa [F, kmswStepOfStep, hFstack, hGstack, State.addEdge, φ', ψ', hold, heq₀, heq₁,
        hends.2, hφne₀, hφne₁] using hv.east_endpoint e hold
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · subst e
        have hends := hv.east_endpoint F.active hactive
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge, h.active,
          hends, hLocalEnd.2]
      · subst e
        have hends := hv.west_endpoint F.active hactive
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge, h.active,
          hends, hLocalEnd.1]


 
theorem kmswWindowPatchVertexRel_left_seam {G₀ : State} {w : ℕ → Fin 3}
    {n : ℕ} {u : ℕ → Fin 3} {j : ℕ} {φ ψ : ℕ → ℕ}
    {A B YL YR XL XR : List ℕ} {q : ℕ}
    (h : KMSWWindowPatchRel G₀ (kmswStage w n) (kmswStage u j) φ
      (A ++ [q]) B YL YR XL XR)
    (hv : KMSWWindowPatchVertexRel (kmswStage w n) (kmswStage u j) φ ψ)
    (hstack : (kmswStage u j).UL.dropLast = []) :
    let G := kmswStage w n
    let F := kmswStage u j
    let φ' := fun e => if e < F.nextEdge then φ e else
      if e = F.nextEdge then G.nextEdge else q
    let ψ' := fun v => if v < F.nextVertex then ψ v else G.west q
    KMSWWindowPatchVertexRel (kmswStepOfStep G .left)
      (kmswStepOfStep F .left) φ' ψ' := by
  let G := kmswStage w n
  let F := kmswStage u j
  let φ' := fun e => if e < F.nextEdge then φ e else
    if e = F.nextEdge then G.nextEdge else q
  let ψ' := fun v => if v < F.nextVertex then ψ v else G.west q
  have hFstack : (kmswStage u j).UL.dropLast.reverse = [] := by rw [hstack]; rfl
  have hFUL : F.UL = [F.active] := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last u j
    have hz : es = [] := by simpa only [hes, List.dropLast_concat] using hstack
    simpa only [hz, List.nil_append] using hes
  have hGUL : G.UL = A ++ [q, G.active] := by
    rw [h.ul, hFUL, List.map_cons, List.map_nil, h.active]
    simp only [List.append_assoc, List.singleton_append]
    rfl
  have hGstack : (kmswStage w n).UL.dropLast.reverse = q :: A.reverse := by
    change G.UL.dropLast.reverse = q :: A.reverse
    rw [hGUL]
    simp
  have hhead : (kmswStage w n).east q =
      (kmswStage w n).west (kmswStage w n).active := by
    have hc := (kmswStage_boundary_chain_invariant w n).1
    change List.IsChain (fun e f => G.east e = G.west f) (G.UL ++ G.UR) at hc
    rw [hGUL, List.append_assoc] at hc
    exact (List.isChain_append_cons_cons.mp hc).2.1
  have hqb : q < G.nextEdge := h.residual_bound q (by simp)
  have hqne : q ≠ (kmswStage w n).nextEdge := Nat.ne_of_lt hqb
  have hGlobalEnd := kmswStage_endpoints_lt_nextVertex w n q hqb
  have hactive := (kmswStage_boundary_ids_lt_nextEdge u j).1
  have hLocalEnd := kmswStage_endpoints_lt_nextVertex u j F.active hactive
  refine ⟨?_, ?_, ?_⟩
  · intro v hv'
    simp only [kmswStepOfStep, hFstack, hGstack, State.addEdge] at hv' ⊢
    change v < F.nextVertex + 1 at hv'
    change ψ' v < G.nextVertex
    by_cases hold : v < F.nextVertex
    · rw [show ψ' v = ψ v by simp [ψ', hold]]
      exact hv.vertex_bound v hold
    · have heq : v = F.nextVertex := by omega
      subst v
      simpa only [ψ', Nat.lt_irrefl, ite_false, G] using hGlobalEnd.1
  · intro e he
    simp only [kmswStepOfStep, hFstack, State.addEdge] at he
    change e < F.nextEdge + 2 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne : φ e ≠ G.nextEdge := Nat.ne_of_lt hφbound
      have heq₀ : e ≠ F.nextEdge := by omega
      have heq₁ : e ≠ F.nextEdge + 1 := by omega
      simpa [F, G, kmswStepOfStep, hFstack, hGstack, State.addEdge, φ', ψ',
        hold, heq₀, heq₁, hends.1, hφne] using hv.west_endpoint e hold
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · subst e
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge]
      · subst e
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge, hqne]
  · intro e he
    simp only [kmswStepOfStep, hFstack, State.addEdge] at he
    change e < F.nextEdge + 2 at he
    by_cases hold : e < F.nextEdge
    · have hends := kmswStage_endpoints_lt_nextVertex u j e hold
      have hφbound := h.edge_bound e hold
      have hφne : φ e ≠ G.nextEdge := Nat.ne_of_lt hφbound
      have heq₀ : e ≠ F.nextEdge := by omega
      have heq₁ : e ≠ F.nextEdge + 1 := by omega
      simpa [F, G, kmswStepOfStep, hFstack, hGstack, State.addEdge, φ', ψ',
        hold, heq₀, heq₁, hends.2, hφne] using hv.east_endpoint e hold
    · have heq : e = F.nextEdge ∨ e = F.nextEdge + 1 := by omega
      rcases heq with heq | heq
      · subst e
        have hends := hv.east_endpoint F.active hactive
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge, h.active,
          hends, hLocalEnd.2]
      · subst e
        have hends := hv.west_endpoint F.active hactive
        simp [F, kmswStepOfStep, hFstack, hGstack, State.addEdge, h.active,
          hends, hLocalEnd.1, hqne, hhead]

 
@[expose] def kmswWindowPatchVertexMap (w : ℕ → Fin 3) (s : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun v => if v = 0 then (kmswStage w s).west (kmswStage w s).active
      else (kmswStage w s).east (kmswStage w s).active
  | j + 1 =>
      let G := kmswStage w (s + j)
      let F := kmswStage (fun i => w (s + i)) j
      let d := kmswWindowPatchData w s j
      let ψ := kmswWindowPatchVertexMap w s j
      let extend := fun z v => if v < F.nextVertex then ψ v else z
      match kmswCodeStep (w (s + j)) with
      | .down => match F.UR with
        | _ :: _ => ψ
        | [] => match d.B with
          | [] => extend G.nextVertex
          | q :: _ => extend (G.east q)
      | .up => extend G.nextVertex
      | .left => match F.UL.dropLast.reverse with
        | _ :: _ => ψ
        | [] => match d.A.reverse with
          | [] => extend G.nextVertex
          | q :: _ => extend (G.west q)

 
theorem kmswWindowPatchVertexMap_rel (w : ℕ → Fin 3) (s j : ℕ) :
    KMSWWindowPatchVertexRel (kmswStage w (s + j))
      (kmswStage (fun i => w (s + i)) j) (kmswWindowPatchData w s j).φ
      (kmswWindowPatchVertexMap w s j) := by
  induction j with
  | zero => exact kmswWindowPatchVertexRel_init w s
  | succ j ih =>
    let G := kmswStage w (s + j)
    let u := fun i => w (s + i)
    let F := kmswStage u j
    let d := kmswWindowPatchData w s j
    let ψ := kmswWindowPatchVertexMap w s j
    have h := kmswWindowPatchData_rel w s j
    change KMSWWindowPatchRel (kmswStage w s) G F d.φ d.A d.B d.YL d.YR
      d.XL d.XR at h
    rw [show s + (j + 1) = (s + j) + 1 from Nat.add_assoc s j 1]
    change KMSWWindowPatchVertexRel
      (kmswStepOfStep G (kmswCodeStep (w (s + j))))
      (kmswStepOfStep F (kmswCodeStep (w (s + j))))
      (d.step G F (kmswCodeStep (w (s + j)))).φ
      (match kmswCodeStep (w (s + j)) with
      | .down => match F.UR with
        | _ :: _ => ψ
        | [] => match d.B with
          | [] => fun v => if v < F.nextVertex then ψ v else G.nextVertex
          | q :: _ => fun v => if v < F.nextVertex then ψ v else G.east q
      | .up => fun v => if v < F.nextVertex then ψ v else G.nextVertex
      | .left => match F.UL.dropLast.reverse with
        | _ :: _ => ψ
        | [] => match d.A.reverse with
          | [] => fun v => if v < F.nextVertex then ψ v else G.nextVertex
          | q :: _ => fun v => if v < F.nextVertex then ψ v else G.west q)
    cases hc : kmswCodeStep (w (s + j)) with
    | down =>
      cases hu : F.UR with
      | cons e es =>
        simpa only [KMSWWindowPatchData.step, hu] using
          kmswWindowPatchVertexRel_down_existing h ih e es hu
      | nil =>
        cases hb : d.B with
        | nil =>
          have h' := h
          rw [hb] at h'
          simpa only [KMSWWindowPatchData.step, hu, hb] using
            kmswWindowPatchVertexRel_down_fresh h' ih hu
        | cons q bs =>
          have h' := h
          rw [hb] at h'
          simpa only [KMSWWindowPatchData.step, hu, hb] using
            kmswWindowPatchVertexRel_down_seam h' ih hu
    | up => exact kmswWindowPatchVertexRel_up h ih
    | left =>
      cases hs : F.UL.dropLast.reverse with
      | cons e es =>
        simpa only [KMSWWindowPatchData.step, hs] using
          kmswWindowPatchVertexRel_left_existing h ih e es hs
      | nil =>
        have hs' : F.UL.dropLast = [] := List.reverse_eq_nil_iff.mp hs
        cases ha : d.A.reverse with
        | nil =>
          have ha' : d.A = [] := List.reverse_eq_nil_iff.mp ha
          have h' := h
          rw [ha'] at h'
          simpa only [KMSWWindowPatchData.step, hs, ha] using
            kmswWindowPatchVertexRel_left_fresh h' ih hs'
        | cons q es =>
          have ha' : d.A = es.reverse ++ [q] := by
            have hh := congrArg List.reverse ha
            simpa only [List.reverse_reverse, List.reverse_cons] using hh
          have h' := h
          rw [ha'] at h'
          simpa only [KMSWWindowPatchData.step, hs, ha] using
            kmswWindowPatchVertexRel_left_seam h' ih hs'

 
theorem kmswWindowPatchVertexMap_extends (w : ℕ → Fin 3) (s j v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) j).nextVertex) :
    kmswWindowPatchVertexMap w s (j + 1) v = kmswWindowPatchVertexMap w s j v := by
  rw [kmswWindowPatchVertexMap]
  dsimp only
  cases hc : kmswCodeStep (w (s + j)) with
  | up => exact ite_eq_left hv
  | down =>
    cases hu : (kmswStage (fun i => w (s + i)) j).UR with
    | cons e es => rfl
    | nil =>
      cases hb : (kmswWindowPatchData w s j).B <;> exact ite_eq_left hv
  | left =>
    cases hs : (kmswStage (fun i => w (s + i)) j).UL.dropLast.reverse with
    | cons e es => rfl
    | nil =>
      cases ha : (kmswWindowPatchData w s j).A.reverse <;> exact ite_eq_left hv

 
theorem kmswWindowPatchVertexMap_extends_le (w : ℕ → Fin 3) (s j k : ℕ)
    (hjk : j ≤ k) (v : ℕ) (hv : v < (kmswStage (fun i => w (s + i)) j).nextVertex) :
    kmswWindowPatchVertexMap w s k v = kmswWindowPatchVertexMap w s j v := by
  have hm : Monotone (fun t => (kmswStage (fun i => w (s + i)) t).nextVertex) := by
    apply monotone_nat_of_le_succ
    intro t
    change (kmswStage (fun i => w (s + i)) t).nextVertex ≤
      (kmswStepOfStep (kmswStage (fun i => w (s + i)) t)
        (kmswCodeStep (w (s + t)))).nextVertex
    cases hc : kmswCodeStep (w (s + t)) with
    | down =>
      cases hu : (kmswStage (fun i => w (s + i)) t).UR <;>
        simp only [kmswStepOfStep, hu, State.addEdge] <;> omega
    | up => simp only [kmswStepOfStep, State.addEdge]; omega
    | left =>
      cases hs : (kmswStage (fun i => w (s + i)) t).UL.dropLast.reverse <;>
        simp only [kmswStepOfStep, hs, State.addEdge] <;> omega
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    rw [kmswWindowPatchVertexMap_extends w s k v (hv.trans_le (hm hjk)), ih]

 
theorem kmswWindowDartMap_vertex (w : ℕ → Fin 3) (s m : ℕ)
    (x : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    (if (kmswWindowDartMap w s m x).2 then
      (kmswStage w (s + m)).east (kmswWindowDartMap w s m x).1.val
    else (kmswStage w (s + m)).west (kmswWindowDartMap w s m x).1.val) =
      kmswWindowPatchVertexMap w s m
        (if x.2 then (kmswStage (fun i => w (s + i)) m).east x.1.val
        else (kmswStage (fun i => w (s + i)) m).west x.1.val) := by
  obtain ⟨e, b⟩ := x
  cases b with
  | false => exact ((kmswWindowPatchVertexMap_rel w s m).west_endpoint e.val e.isLt).symm
  | true => exact ((kmswWindowPatchVertexMap_rel w s m).east_endpoint e.val e.isLt).symm

end DirectedDistances.KMSW
