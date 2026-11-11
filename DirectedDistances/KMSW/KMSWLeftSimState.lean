module

public import DirectedDistances.KMSW.KMSWBoundaryPrefix




public section
namespace DirectedDistances.KMSW


/-- result. -/
@[expose] def kmswLeftPrefixed (r : ℕ) (u : ℕ → Fin 3) (i : ℕ) : Fin 3 :=
  if i < r - 1 then 2 else u (i - (r - 1))

/-- result. -/
@[expose] def kmswLeftExtEdge (S : State) (c : Fin 3) (j : ℕ)
    (φ : ℕ → ℕ) (f : ℕ) : ℕ :=
  if f < S.nextEdge then φ f
  else if kmswCodeStep c = .left ∧ S.UL.dropLast = [] ∧ f = S.nextEdge + 1
    then j - 1 else f + j

/-- result. -/
@[expose] def kmswLeftExtVertex (S : State) (c : Fin 3) (j : ℕ)
    (ψ : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v < S.nextVertex then ψ v
  else if kmswCodeStep c = .left ∧ S.UL.dropLast = [] then j - 1 else v + j

/-- result. -/
@[expose] def kmswLeftSimEdge (r : ℕ) (u : ℕ → Fin 3) : ℕ → ℕ → ℕ
  | 0 => fun e => e + (r - 1)
  | m + 1 => kmswLeftExtEdge (kmswStage u m) (u m)
      (r - 1 - (kmswStage u m).LL.length) (kmswLeftSimEdge r u m)

/-- result. -/
@[expose] def kmswLeftSimVertex (r : ℕ) (u : ℕ → Fin 3) : ℕ → ℕ → ℕ
  | 0 => fun v => v + (r - 1)
  | m + 1 => kmswLeftExtVertex (kmswStage u m) (u m)
      (r - 1 - (kmswStage u m).LL.length) (kmswLeftSimVertex r u m)

/-- result. -/
structure KMSWLeftSim (r : ℕ) (S T : State) (φ ψ : ℕ → ℕ) : Prop where
  ll_length : S.LL.length ≤ r - 1
  ul : T.UL = List.range (r - 1 - S.LL.length) ++ S.UL.map φ
  ur : T.UR = S.UR.map φ
  ll : T.LL = []
  lr : T.LR = List.range (r - 1) ++ S.LR.map φ
  ll_map : S.LL.map φ = List.range' (r - 1 - S.LL.length) S.LL.length
  active : T.active = φ S.active
  nextEdge : T.nextEdge = S.nextEdge + (r - 1 - S.LL.length)
  nextVertex : T.nextVertex = S.nextVertex + (r - 1 - S.LL.length)
  edge_bound : ∀ e < S.nextEdge, φ e < T.nextEdge
  edge_lower : ∀ e < S.nextEdge, r - 1 - S.LL.length ≤ φ e
  west : ∀ e < S.nextEdge, T.west (φ e) = ψ (S.west e)
  east : ∀ e < S.nextEdge, T.east (φ e) = ψ (S.east e)
  present : ∀ e < S.nextEdge,
    T.present (φ e) = (S.present e || decide (e ∈ S.LL))
  edge_injective : ∀ e < S.nextEdge, ∀ f < S.nextEdge, φ e = φ f → e = f
  edge_cover : ∀ f < T.nextEdge,
    f < r - 1 - S.LL.length ∨ ∃ e < S.nextEdge, φ e = f
  vertex_bound : ∀ v < S.nextVertex, ψ v < T.nextVertex
  vertex_lower : ∀ v < S.nextVertex, r - 1 - S.LL.length ≤ ψ v
  vertex_injective : ∀ v < S.nextVertex, ∀ x < S.nextVertex, ψ v = ψ x → v = x
  vertex_cover : ∀ v < T.nextVertex,
    v < r - 1 - S.LL.length ∨ ∃ x < S.nextVertex, ψ x = v
  chain : ∀ i < r - 1 - S.LL.length,
    T.west i = i ∧ T.east i = i + 1 ∧ T.present i = true
  junction : ∀ a ∈ S.UL.head?, ψ (S.west a) = r - 1 - S.LL.length

/-- result. -/
theorem kmswLeftPrefixed_suffix (r : ℕ) (u : ℕ → Fin 3) (m : ℕ) :
    kmswLeftPrefixed r u (r - 1 + m) = u m := by
  simp [kmswLeftPrefixed]

/-- result. -/
theorem kmswLeftPrefixed_stage_succ (r : ℕ) (u : ℕ → Fin 3) (m : ℕ) :
    kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)) =
      kmswStep (kmswStage (kmswLeftPrefixed r u) (r - 1 + m)) (u m) := by
  rw [show r - 1 + (m + 1) = (r - 1 + m) + 1 by omega]
  simp only [kmswStage, kmswLeftPrefixed_suffix]

/-- result. -/
theorem kmswLeftSimEdge_succ_agree (r : ℕ) (u : ℕ → Fin 3) (m e : ℕ)
    (he : e < (kmswStage u m).nextEdge) :
    kmswLeftSimEdge r u (m + 1) e = kmswLeftSimEdge r u m e := by
  simp only [kmswLeftSimEdge, kmswLeftExtEdge, ite_eq_left he]

/-- result. -/
theorem kmswLeftSimVertex_succ_agree (r : ℕ) (u : ℕ → Fin 3) (m v : ℕ)
    (hv : v < (kmswStage u m).nextVertex) :
    kmswLeftSimVertex r u (m + 1) v = kmswLeftSimVertex r u m v := by
  simp only [kmswLeftSimVertex, kmswLeftExtVertex, ite_eq_left hv]

/-- result. -/
theorem kmswLeftSim_zero (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) :
    KMSWLeftSim r (kmswStage u 0)
      (kmswStage (kmswLeftPrefixed r u) (r - 1))
      (kmswLeftSimEdge r u 0) (kmswLeftSimVertex r u 0) := by
  obtain ⟨hE, hV, ha, hUL, hLR, hUR, hLL, hedges⟩ :=
    kmswStage_allDown_prefix_exactLR (kmswLeftPrefixed r u) (r - 1)
      (fun i hi => by simp only [kmswLeftPrefixed, ite_eq_left hi])
  have hwest : ∀ e < r, (kmswStage (kmswLeftPrefixed r u) (r - 1)).west e = e :=
    fun e he => (hedges e (by omega)).2.1
  have heast : ∀ e < r, (kmswStage (kmswLeftPrefixed r u) (r - 1)).east e = e + 1 :=
    fun e he => (hedges e (by omega)).2.2.1
  have hpresent : ∀ e < r,
      (kmswStage (kmswLeftPrefixed r u) (r - 1)).present e = true :=
    fun e he => (hedges e (by omega)).2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [kmswStage, kmswInit]
  · simpa [kmswStage, kmswInit, kmswLeftSimEdge, List.range_succ] using hUL
  · simpa [kmswStage, kmswInit] using hUR
  · exact hLL
  · simpa [kmswStage, kmswInit, kmswLeftSimEdge, List.range_succ] using hLR
  · simp [kmswStage, kmswInit]
  · simpa [kmswStage, kmswInit, kmswLeftSimEdge] using ha
  · simpa [kmswStage, kmswInit, Nat.add_comm] using hE
  · simpa [kmswStage, kmswInit, Nat.add_comm] using hV
  · intro e he
    simp only [kmswStage, kmswInit] at he
    simp only [kmswLeftSimEdge, hE]
    omega
  · intro e _
    simp only [kmswStage, kmswInit, kmswLeftSimEdge, List.length_nil, Nat.sub_zero]
    omega
  · intro e he
    have he0 : e = 0 := by simpa [kmswStage, kmswInit] using he
    subst e
    simpa [kmswStage, kmswInit, kmswLeftSimEdge, kmswLeftSimVertex] using
      hwest (r - 1) (by omega)
  · intro e he
    have he0 : e = 0 := by simpa [kmswStage, kmswInit] using he
    subst e
    simpa [kmswStage, kmswInit, kmswLeftSimEdge, kmswLeftSimVertex, Nat.add_comm] using
      heast (r - 1) (by omega)
  · intro e he
    have he0 : e = 0 := by simpa [kmswStage, kmswInit] using he
    subst e
    simpa [kmswStage, kmswInit, kmswLeftSimEdge] using hpresent (r - 1) (by omega)
  · intro e _ f _ hef
    simp only [kmswLeftSimEdge] at hef
    omega
  · intro f hf
    simp only [kmswStage, kmswInit, List.length_nil, Nat.sub_zero]
    rw [hE] at hf
    by_cases hfj : f < r - 1
    · exact Or.inl hfj
    · right
      refine ⟨0, by decide, ?_⟩
      simp only [kmswLeftSimEdge, zero_add]
      omega
  · intro v hv
    simp only [kmswStage, kmswInit] at hv
    simp only [kmswLeftSimVertex, hV]
    omega
  · intro v _
    simp [kmswStage, kmswInit, kmswLeftSimVertex]
  · intro v _ x _ hvx
    simp only [kmswLeftSimVertex] at hvx
    omega
  · intro v hv
    simp only [kmswStage, kmswInit, List.length_nil, Nat.sub_zero]
    rw [hV] at hv
    by_cases hvj : v < r - 1
    · exact Or.inl hvj
    · right
      refine ⟨v - (r - 1), ?_, ?_⟩
      · omega
      · simp only [kmswLeftSimVertex]
        omega
  · intro i hi
    simp only [kmswStage, kmswInit, List.length_nil, Nat.sub_zero] at hi
    exact ⟨hwest i (by omega), heast i (by omega), hpresent i (by omega)⟩
  · intro a ha'
    simp only [kmswStage, kmswInit, List.head?_cons, Option.mem_some_iff] at ha'
    subst a
    simp [kmswStage, kmswInit, kmswLeftSimVertex]

private theorem sim_relabel_congr {r : ℕ} {S T : State} {φ ψ φ' ψ' : ℕ → ℕ}
    (h : KMSWLeftSim r S T φ ψ)
    (hφ : ∀ e < S.nextEdge, φ' e = φ e)
    (hψ : ∀ v < S.nextVertex, ψ' v = ψ v)
    (hb : ∀ e ∈ S.UL ++ S.UR ++ S.LL ++ S.LR, e < S.nextEdge)
    (ha : S.active < S.nextEdge)
    (hv : ∀ e < S.nextEdge, S.west e < S.nextVertex ∧ S.east e < S.nextVertex) :
    KMSWLeftSim r S T φ' ψ' := by
  have hmap (l : List ℕ) (hl : ∀ e ∈ l, e < S.nextEdge) :
      l.map φ' = l.map φ := List.map_congr_left (fun e he => hφ e (hl e he))
  have hul := hmap S.UL (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hur := hmap S.UR (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hll := hmap S.LL (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hlr := hmap S.LR (fun e he => hb e (by simp only [List.mem_append]; tauto))
  refine {
    ll_length := h.ll_length
    ul := ?_
    ur := ?_
    ll := h.ll
    lr := ?_
    ll_map := ?_
    active := ?_
    nextEdge := h.nextEdge
    nextVertex := h.nextVertex
    edge_bound := ?_
    edge_lower := ?_
    west := ?_
    east := ?_
    present := ?_
    edge_injective := ?_
    edge_cover := ?_
    vertex_bound := ?_
    vertex_lower := ?_
    vertex_injective := ?_
    vertex_cover := ?_
    chain := h.chain
    junction := ?_ }
  · rw [hul]; exact h.ul
  · rw [hur]; exact h.ur
  · rw [hlr]; exact h.lr
  · rw [hll]; exact h.ll_map
  · rw [hφ _ ha]; exact h.active
  · intro e he; rw [hφ e he]; exact h.edge_bound e he
  · intro e he; rw [hφ e he]; exact h.edge_lower e he
  · intro e he; rw [hφ e he, hψ _ (hv e he).1]; exact h.west e he
  · intro e he; rw [hφ e he, hψ _ (hv e he).2]; exact h.east e he
  · intro e he; rw [hφ e he]; exact h.present e he
  · intro e he f hf hef
    rw [hφ e he, hφ f hf] at hef
    exact h.edge_injective e he f hf hef
  · intro f hf
    rcases h.edge_cover f hf with hj | ⟨e, he, hef⟩
    · exact Or.inl hj
    · exact Or.inr ⟨e, he, (hφ e he).trans hef⟩
  · intro v hv; rw [hψ v hv]; exact h.vertex_bound v hv
  · intro v hv; rw [hψ v hv]; exact h.vertex_lower v hv
  · intro v hv x hx hvx
    rw [hψ v hv, hψ x hx] at hvx
    exact h.vertex_injective v hv x hx hvx
  · intro v hv
    rcases h.vertex_cover v hv with hj | ⟨x, hx, hxv⟩
    · exact Or.inl hj
    · exact Or.inr ⟨x, hx, (hψ x hx).trans hxv⟩
  · intro a ha'
    have hamem : a ∈ S.UL := List.mem_of_mem_head? ha'
    have hab : a < S.nextEdge := hb a (by simp only [List.mem_append]; tauto)
    rw [hψ _ (hv a hab).1]
    exact h.junction a ha'

private theorem sim_down_existing {r : ℕ} {S T : State} {φ ψ : ℕ → ℕ}
    (h : KMSWLeftSim r S T φ ψ) (e : ℕ) (es : List ℕ)
    (hUR : S.UR = e :: es) (he : e < S.nextEdge) (hne : S.UL ≠ []) :
    KMSWLeftSim r (kmswStepOfStep S .down) (kmswStepOfStep T .down) φ ψ := by
  have hTUR : T.UR = φ e :: es.map φ := by rw [h.ur, hUR, List.map_cons]
  have hUL : (S.UL ++ [e]).map φ = S.UL.map φ ++ [φ e] := by
    simp only [List.map_append, List.map_cons, List.map_nil]
  simp only [kmswStepOfStep, hUR, hTUR]
  refine {
    ll_length := h.ll_length
    ul := ?_
    ur := rfl
    ll := h.ll
    lr := h.lr
    ll_map := h.ll_map
    active := rfl
    nextEdge := h.nextEdge
    nextVertex := h.nextVertex
    edge_bound := h.edge_bound
    edge_lower := h.edge_lower
    west := h.west
    east := h.east
    present := ?_
    edge_injective := h.edge_injective
    edge_cover := h.edge_cover
    vertex_bound := h.vertex_bound
    vertex_lower := h.vertex_lower
    vertex_injective := h.vertex_injective
    vertex_cover := h.vertex_cover
    chain := ?_
    junction := ?_ }
  · simp only [h.ul, hUL, List.append_assoc]
  · intro f hf
    change (if φ f = φ e then true else T.present (φ f)) =
      ((if f = e then true else S.present f) || decide (f ∈ S.LL))
    by_cases hfe : f = e
    · subst f; simp
    · have hφfe : φ f ≠ φ e := fun hh => hfe (h.edge_injective f hf e he hh)
      simp only [ite_eq_right hφfe, ite_eq_right hfe]
      exact h.present f hf
  · intro i hi
    change i < r - 1 - S.LL.length at hi
    have hie : i ≠ φ e := by have := h.edge_lower e he; omega
    change T.west i = i ∧ T.east i = i + 1 ∧
      (if i = φ e then true else T.present i) = true
    simpa only [ite_eq_right hie] using h.chain i hi
  · intro a ha
    change ψ (S.west a) = r - 1 - S.LL.length
    apply h.junction a
    simpa only [List.head?_append_of_ne_nil S.UL hne] using ha

/-- result. -/
theorem kmswLeftSim_succ_down_existing (r : ℕ) (u : ℕ → Fin 3) (m : ℕ)
    (h : KMSWLeftSim r (kmswStage u m)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + m))
      (kmswLeftSimEdge r u m) (kmswLeftSimVertex r u m))
    (hc : u m = 2) (hne : (kmswStage u m).UR ≠ []) :
    KMSWLeftSim r (kmswStage u (m + 1))
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)))
      (kmswLeftSimEdge r u (m + 1)) (kmswLeftSimVertex r u (m + 1)) := by
  obtain ⟨e, es, hUR⟩ := List.exists_cons_of_ne_nil hne
  have he : e < (kmswStage u m).nextEdge :=
    stageRun_edge_bound u m e (Or.inl (Or.inl (Or.inr (by rw [hUR]; simp))))
  have hs := sim_down_existing h e es hUR he
    (kmswStage_UL_nonempty_active_last u m).1
  have hcode : kmswCodeStep (u m) = .down := by rw [hc]; rfl
  have hstage : kmswStage u (m + 1) = kmswStepOfStep (kmswStage u m) .down := by
    simp only [kmswStage, kmswStep, hcode]
  have htstage : kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)) =
      kmswStepOfStep (kmswStage (kmswLeftPrefixed r u) (r - 1 + m)) .down := by
    rw [kmswLeftPrefixed_stage_succ]; simp only [kmswStep, hcode]
  rw [← hstage, ← htstage] at hs
  apply sim_relabel_congr hs
  · intro f hf
    apply kmswLeftSimEdge_succ_agree
    simpa only [hstage, kmswStepOfStep, hUR] using hf
  · intro v hv
    apply kmswLeftSimVertex_succ_agree
    simpa only [hstage, kmswStepOfStep, hUR] using hv
  · exact (kmswStage_boundary_ids_lt_nextEdge u (m + 1)).2
  · exact (kmswStage_boundary_ids_lt_nextEdge u (m + 1)).1
  · exact kmswStage_endpoints_lt_nextVertex u (m + 1)

/-- result. -/
theorem kmswLeftSim_LL_bound (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k) :
    (kmswStage u n).LL.length ≤ r - 1 := by
  obtain ⟨k, hk, hmin⟩ := runningMin_attained (L u) n
  have hq := hquad k hk
  have hlen := kmswStage_LL_length u n
  change ((kmswStage u n).LL.length : ℤ) = -runningMin (L u) n at hlen
  rw [hmin] at hlen
  omega

private theorem extend_shift {n N j a : ℕ} {φ : ℕ → ℕ}
    (hN : N = n + j) (hb : ∀ e < n, φ e < N)
    (hl : ∀ e < n, j ≤ φ e)
    (hinj : ∀ e < n, ∀ f < n, φ e = φ f → e = f)
    (hc : ∀ f < N, f < j ∨ ∃ e < n, φ e = f) :
    let φ' := fun e => if e < n then φ e else e + j
    (∀ e < n + a, φ' e < N + a) ∧
    (∀ e < n + a, j ≤ φ' e) ∧
    (∀ e < n + a, ∀ f < n + a, φ' e = φ' f → e = f) ∧
    (∀ f < N + a, f < j ∨ ∃ e < n + a, φ' e = f) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    split
    · have := hb e (by assumption); omega
    · omega
  · intro e _
    split
    · exact hl e (by assumption)
    · omega
  · intro e he f hf hef
    by_cases hen : e < n <;> by_cases hfn : f < n
    · simp only [ite_eq_left hen, ite_eq_left hfn] at hef
      exact hinj e hen f hfn hef
    · simp only [ite_eq_left hen, ite_eq_right hfn] at hef
      have := hb e hen
      omega
    · simp only [ite_eq_right hen, ite_eq_left hfn] at hef
      have := hb f hfn
      omega
    · simp only [ite_eq_right hen, ite_eq_right hfn] at hef
      omega
  · intro f hf
    by_cases hfN : f < N
    · rcases hc f hfN with hfj | ⟨e, he, hef⟩
      · exact Or.inl hfj
      · exact Or.inr ⟨e, by omega, by simp only [ite_eq_left he]; exact hef⟩
    · right
      refine ⟨f - j, by omega, ?_⟩
      rw [ite_eq_right (by omega)]
      omega

private theorem sim_down_fresh {r : ℕ} {S T : State} {φ ψ : ℕ → ℕ}
    (h : KMSWLeftSim r S T φ ψ) (hUR : S.UR = [])
    (hb : ∀ e ∈ S.UL ++ S.UR ++ S.LL ++ S.LR, e < S.nextEdge)
    (ha : S.active < S.nextEdge)
    (hv : ∀ e < S.nextEdge, S.west e < S.nextVertex ∧ S.east e < S.nextVertex)
    (hne : S.UL ≠ []) :
    KMSWLeftSim r (kmswStepOfStep S .down) (kmswStepOfStep T .down)
      (kmswLeftExtEdge S 2 (r - 1 - S.LL.length) φ)
      (kmswLeftExtVertex S 2 (r - 1 - S.LL.length) ψ) := by
  let j := r - 1 - S.LL.length
  let F := kmswLeftExtEdge S 2 j φ
  let G := kmswLeftExtVertex S 2 j ψ
  have hF (e : ℕ) : F e = if e < S.nextEdge then φ e else e + j := by
    simp [F, kmswLeftExtEdge, kmswCodeStep]
  have hG (v : ℕ) : G v = if v < S.nextVertex then ψ v else v + j := by
    simp [G, kmswLeftExtVertex, kmswCodeStep]
  have hFold (e : ℕ) (he : e < S.nextEdge) : F e = φ e := by rw [hF, ite_eq_left he]
  have hGold (v : ℕ) (hv' : v < S.nextVertex) : G v = ψ v := by rw [hG, ite_eq_left hv']
  have hFnew : F S.nextEdge = T.nextEdge := by
    rw [hF]; simp only [lt_self_iff_false]; exact h.nextEdge.symm
  have hGnew : G S.nextVertex = T.nextVertex := by
    rw [hG]; simp only [lt_self_iff_false]; exact h.nextVertex.symm
  have hmap (l : List ℕ) (hl : ∀ e ∈ l, e < S.nextEdge) : l.map F = l.map φ :=
    List.map_congr_left (fun e he => hFold e (hl e he))
  have hUL := hmap S.UL (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hLL := hmap S.LL (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hLR := hmap S.LR (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hTUR : T.UR = [] := by rw [h.ur, hUR, List.map_nil]
  have hE := extend_shift (a := 1) h.nextEdge h.edge_bound h.edge_lower
    h.edge_injective h.edge_cover
  have hV := extend_shift (a := 1) h.nextVertex h.vertex_bound h.vertex_lower
    h.vertex_injective h.vertex_cover
  change KMSWLeftSim r (kmswStepOfStep S .down) (kmswStepOfStep T .down) F G
  simp only [kmswStepOfStep, hUR, hTUR, State.addEdge]
  refine {
    ll_length := h.ll_length
    ul := ?_
    ur := by simp only [List.map_nil]
    ll := h.ll
    lr := ?_
    ll_map := ?_
    active := hFnew.symm
    nextEdge := ?_
    nextVertex := ?_
    edge_bound := ?_
    edge_lower := ?_
    west := ?_
    east := ?_
    present := ?_
    edge_injective := ?_
    edge_cover := ?_
    vertex_bound := ?_
    vertex_lower := ?_
    vertex_injective := ?_
    vertex_cover := ?_
    chain := ?_
    junction := ?_ }
  · change T.UL ++ [T.nextEdge] = List.range j ++ (S.UL ++ [S.nextEdge]).map F
    simp only [List.map_append, List.map_cons, List.map_nil, hUL, hFnew, h.ul, List.append_assoc]
    rfl
  · change T.LR ++ [T.nextEdge] = List.range (r - 1) ++ (S.LR ++ [S.nextEdge]).map F
    simp only [List.map_append, List.map_cons, List.map_nil, hLR, hFnew, h.lr, List.append_assoc]
  · change S.LL.map F = _
    rw [hLL]; exact h.ll_map
  · change T.nextEdge + 1 = S.nextEdge + 1 + j
    have := h.nextEdge; omega
  · change T.nextVertex + 1 = S.nextVertex + 1 + j
    have := h.nextVertex; omega
  · intro e he
    change F e < T.nextEdge + 1
    rw [hF]; exact hE.1 e he
  · intro e he
    change j ≤ F e
    rw [hF]; exact hE.2.1 e he
  · intro e he
    change (if F e = T.nextEdge then T.east T.active else T.west (F e)) =
      G (if e = S.nextEdge then S.east S.active else S.west e)
    by_cases heold : e < S.nextEdge
    · rw [hFold e heold, ite_eq_right (by have := h.edge_bound e heold; omega),
        ite_eq_right (by omega), hGold _ (hv e heold).1]
      exact h.west e heold
    · have heq : e = S.nextEdge := by change e < S.nextEdge + 1 at he; omega
      subst e
      simp only [hFnew, ite_eq_left, hGold _ (hv S.active ha).2, h.active]
      exact h.east S.active ha
  · intro e he
    change (if F e = T.nextEdge then T.nextVertex else T.east (F e)) =
      G (if e = S.nextEdge then S.nextVertex else S.east e)
    by_cases heold : e < S.nextEdge
    · rw [hFold e heold, ite_eq_right (by have := h.edge_bound e heold; omega),
        ite_eq_right (by omega), hGold _ (hv e heold).2]
      exact h.east e heold
    · have heq : e = S.nextEdge := by change e < S.nextEdge + 1 at he; omega
      subst e
      simp only [hFnew, ite_eq_left, hGnew]
  · intro e he
    change (if F e = T.nextEdge then true else T.present (F e)) =
      ((if e = S.nextEdge then true else S.present e) || decide (e ∈ S.LL))
    by_cases heold : e < S.nextEdge
    · rw [hFold e heold, ite_eq_right (by have := h.edge_bound e heold; omega),
        ite_eq_right (by omega)]
      exact h.present e heold
    · have heq : e = S.nextEdge := by change e < S.nextEdge + 1 at he; omega
      subst e
      simp only [hFnew, ite_eq_left, Bool.true_or]
  · intro e he f hf hef
    apply hE.2.2.1 e he f hf
    simpa only [hF, j] using hef
  · intro f hf
    rcases hE.2.2.2 f hf with hj | ⟨e, he, hef⟩
    · exact Or.inl hj
    · exact Or.inr ⟨e, he, by simpa only [hF, j] using hef⟩
  · intro v hv'
    change G v < T.nextVertex + 1
    rw [hG]; exact hV.1 v hv'
  · intro v hv'
    change j ≤ G v
    rw [hG]; exact hV.2.1 v hv'
  · intro v hv' x hx hvx
    apply hV.2.2.1 v hv' x hx
    simpa only [hG, j] using hvx
  · intro v hv'
    rcases hV.2.2.2 v hv' with hj | ⟨x, hx, hxv⟩
    · exact Or.inl hj
    · exact Or.inr ⟨x, hx, by simpa only [hG, j] using hxv⟩
  · intro i hi
    change i < j at hi
    have hiT : i ≠ T.nextEdge := by have := h.nextEdge; omega
    change (if i = T.nextEdge then T.east T.active else T.west i) = i ∧
      (if i = T.nextEdge then T.nextVertex else T.east i) = i + 1 ∧
      (if i = T.nextEdge then true else T.present i) = true
    simpa only [ite_eq_right hiT] using h.chain i hi
  · intro a hamem
    change a ∈ (S.UL ++ [S.nextEdge]).head? at hamem
    rw [List.head?_append_of_ne_nil S.UL hne] at hamem
    have hab := hb a (by have := List.mem_of_mem_head? hamem; simp only [List.mem_append]; tauto)
    change G (if a = S.nextEdge then S.east S.active else S.west a) = j
    rw [ite_eq_right (by omega), hGold _ (hv a hab).1]
    exact h.junction a hamem

/-- result. -/
theorem kmswLeftSim_succ_down_fresh (r : ℕ) (u : ℕ → Fin 3) (m : ℕ)
    (h : KMSWLeftSim r (kmswStage u m)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + m))
      (kmswLeftSimEdge r u m) (kmswLeftSimVertex r u m))
    (hc : u m = 2) (hUR : (kmswStage u m).UR = []) :
    KMSWLeftSim r (kmswStage u (m + 1))
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)))
      (kmswLeftSimEdge r u (m + 1)) (kmswLeftSimVertex r u (m + 1)) := by
  have hs := sim_down_fresh h hUR
    (kmswStage_boundary_ids_lt_nextEdge u m).2
    (kmswStage_boundary_ids_lt_nextEdge u m).1
    (kmswStage_endpoints_lt_nextVertex u m)
    (kmswStage_UL_nonempty_active_last u m).1
  rw [kmswLeftPrefixed_stage_succ]
  have hcode : kmswCodeStep (2 : Fin 3) = .down := rfl
  simpa only [kmswStage, kmswStep, hc, hcode,
    kmswLeftSimEdge, kmswLeftSimVertex] using hs

/-- result. -/
theorem KMSWLeftSim.terminal_bijective {r : ℕ} {S T : State} {φ ψ : ℕ → ℕ}
    (h : KMSWLeftSim r S T φ ψ) (hterminal : S.LL.length = r - 1) :
    (∀ e < S.nextEdge, φ e < T.nextEdge) ∧
    (∀ e < S.nextEdge, ∀ f < S.nextEdge, φ e = φ f → e = f) ∧
    (∀ f < T.nextEdge, ∃ e < S.nextEdge, φ e = f) ∧
    (∀ v < S.nextVertex, ψ v < T.nextVertex) ∧
    (∀ v < S.nextVertex, ∀ x < S.nextVertex, ψ v = ψ x → v = x) ∧
    (∀ v < T.nextVertex, ∃ x < S.nextVertex, ψ x = v) ∧
    S.LL.map φ = List.range (r - 1) ∧
    T.LR = S.LL.map φ ++ S.LR.map φ ∧
    T.UL = S.UL.map φ ∧ T.UR = S.UR.map φ ∧ T.LL = [] := by
  have hj : r - 1 - S.LL.length = 0 := by omega
  have hLL : S.LL.map φ = List.range (r - 1) := by
    simpa only [hterminal, Nat.sub_self, ← List.range_eq_range'] using h.ll_map
  refine ⟨h.edge_bound, h.edge_injective, ?_, h.vertex_bound, h.vertex_injective,
    ?_, hLL, ?_, ?_, h.ur, h.ll⟩
  · intro f hf
    rcases h.edge_cover f hf with hfj | hpre
    · omega
    · exact hpre
  · intro v hv
    rcases h.vertex_cover v hv with hvj | hpre
    · omega
    · exact hpre
  · rw [hLL]; exact h.lr
  · simpa only [hj, List.range_zero, List.nil_append] using h.ul

private theorem sim_up {r : ℕ} {S T : State} {φ ψ : ℕ → ℕ}
    (h : KMSWLeftSim r S T φ ψ)
    (hb : ∀ e ∈ S.UL ++ S.UR ++ S.LL ++ S.LR, e < S.nextEdge)
    (ha : S.active < S.nextEdge)
    (hv : ∀ e < S.nextEdge, S.west e < S.nextVertex ∧ S.east e < S.nextVertex)
    (hlast : ∃ es, S.UL = es ++ [S.active]) :
    KMSWLeftSim r (kmswStepOfStep S .up) (kmswStepOfStep T .up)
      (kmswLeftExtEdge S 1 (r - 1 - S.LL.length) φ)
      (kmswLeftExtVertex S 1 (r - 1 - S.LL.length) ψ) := by
  let j := r - 1 - S.LL.length
  let F := kmswLeftExtEdge S 1 j φ
  let G := kmswLeftExtVertex S 1 j ψ
  have hF (e : ℕ) : F e = if e < S.nextEdge then φ e else e + j := by
    simp [F, kmswLeftExtEdge, kmswCodeStep]
  have hG (v : ℕ) : G v = if v < S.nextVertex then ψ v else v + j := by
    simp [G, kmswLeftExtVertex, kmswCodeStep]
  have hFold (e : ℕ) (he : e < S.nextEdge) : F e = φ e := by rw [hF, ite_eq_left he]
  have hGold (v : ℕ) (hv' : v < S.nextVertex) : G v = ψ v := by rw [hG, ite_eq_left hv']
  have hFnew : F S.nextEdge = T.nextEdge := by
    rw [hF]; simp only [lt_self_iff_false]; exact h.nextEdge.symm
  have hFnew1 : F (S.nextEdge + 1) = T.nextEdge + 1 := by
    rw [hF, ite_eq_right (by omega)]
    have := h.nextEdge; omega
  have hGnew : G S.nextVertex = T.nextVertex := by
    rw [hG]; simp only [lt_self_iff_false]; exact h.nextVertex.symm
  have hmap (l : List ℕ) (hl : ∀ e ∈ l, e < S.nextEdge) : l.map F = l.map φ :=
    List.map_congr_left (fun e he => hFold e (hl e he))
  have hUR := hmap S.UR (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hLL := hmap S.LL (fun e he => hb e (by simp only [List.mem_append]; tauto))
  have hLR := hmap S.LR (fun e he => hb e (by simp only [List.mem_append]; tauto))
  obtain ⟨xs, hxs⟩ := hlast
  have hxsmap := hmap xs (fun e he => hb e (by rw [hxs]; simp only [List.mem_append]; tauto))
  have hTUL : T.UL = (List.range j ++ xs.map φ) ++ [φ S.active] := by
    rw [h.ul, hxs, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  have hE := extend_shift (a := 2) h.nextEdge h.edge_bound h.edge_lower
    h.edge_injective h.edge_cover
  have hV := extend_shift (a := 1) h.nextVertex h.vertex_bound h.vertex_lower
    h.vertex_injective h.vertex_cover
  change KMSWLeftSim r (kmswStepOfStep S .up) (kmswStepOfStep T .up) F G
  simp only [kmswStepOfStep, State.addEdge]
  refine {
    ll_length := h.ll_length
    ul := ?_
    ur := ?_
    ll := h.ll
    lr := ?_
    ll_map := ?_
    active := hFnew.symm
    nextEdge := ?_
    nextVertex := ?_
    edge_bound := ?_
    edge_lower := ?_
    west := ?_
    east := ?_
    present := ?_
    edge_injective := ?_
    edge_cover := ?_
    vertex_bound := ?_
    vertex_lower := ?_
    vertex_injective := ?_
    vertex_cover := ?_
    chain := ?_
    junction := ?_ }
  · change T.UL.dropLast ++ [T.nextEdge] = List.range j ++ (S.UL.dropLast ++ [S.nextEdge]).map F
    rw [hTUL, hxs, List.dropLast_concat, List.dropLast_concat]
    simp only [ List.map_append, List.map_cons, List.map_nil,
      hFnew, hxsmap, List.append_assoc]
  · change (T.nextEdge + 1) :: T.UR = ((S.nextEdge + 1) :: S.UR).map F
    simp only [List.map_cons, hFnew1, hUR, h.ur]
  · change T.LR = List.range (r - 1) ++ S.LR.map F
    rw [hLR]; exact h.lr
  · change S.LL.map F = _
    rw [hLL]; exact h.ll_map
  · change T.nextEdge + 1 + 1 = S.nextEdge + 1 + 1 + j
    have := h.nextEdge; omega
  · change T.nextVertex + 1 = S.nextVertex + 1 + j
    have := h.nextVertex; omega
  · intro e he
    change F e < T.nextEdge + 1 + 1
    rw [hF]; exact hE.1 e he
  · intro e he
    change j ≤ F e
    rw [hF]; exact hE.2.1 e he
  · intro e he
    change (if F e = T.nextEdge + 1 then T.nextVertex else
      if F e = T.nextEdge then T.west T.active else T.west (F e)) =
      G (if e = S.nextEdge + 1 then S.nextVertex else
        if e = S.nextEdge then S.west S.active else S.west e)
    by_cases heold : e < S.nextEdge
    · have hbound := h.edge_bound e heold
      rw [hFold e heold, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), hGold _ (hv e heold).1]
      exact h.west e heold
    · by_cases he0 : e = S.nextEdge
      · subst e
        simp only [hFnew, Nat.ne_add_one, ↓reduceIte,
          hGold _ (hv S.active ha).1, h.active]
        exact h.west S.active ha
      · have he1 : e = S.nextEdge + 1 := by change e < S.nextEdge + 1 + 1 at he; omega
        subst e
        simp only [hFnew1, ite_eq_left, hGnew]
  · intro e he
    change (if F e = T.nextEdge + 1 then T.east T.active else
      if F e = T.nextEdge then T.nextVertex else T.east (F e)) =
      G (if e = S.nextEdge + 1 then S.east S.active else
        if e = S.nextEdge then S.nextVertex else S.east e)
    by_cases heold : e < S.nextEdge
    · have hbound := h.edge_bound e heold
      rw [hFold e heold, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), hGold _ (hv e heold).2]
      exact h.east e heold
    · by_cases he0 : e = S.nextEdge
      · subst e
        simp only [hFnew, Nat.ne_add_one, ↓reduceIte, hGnew]
      · have he1 : e = S.nextEdge + 1 := by change e < S.nextEdge + 1 + 1 at he; omega
        subst e
        simp only [hFnew1, ite_eq_left, hGold _ (hv S.active ha).2, h.active]
        exact h.east S.active ha
  · intro e he
    change (if F e = T.nextEdge + 1 then false else
      if F e = T.nextEdge then true else T.present (F e)) =
      ((if e = S.nextEdge + 1 then false else
        if e = S.nextEdge then true else S.present e) || decide (e ∈ S.LL))
    by_cases heold : e < S.nextEdge
    · have hbound := h.edge_bound e heold
      rw [hFold e heold, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
      exact h.present e heold
    · by_cases he0 : e = S.nextEdge
      · subst e
        simp only [hFnew, Nat.ne_add_one, ↓reduceIte, Bool.true_or]
      · have he1 : e = S.nextEdge + 1 := by change e < S.nextEdge + 1 + 1 at he; omega
        subst e
        have hnot : S.nextEdge + 1 ∉ S.LL := by
          intro hm
          have := hb _ (by simp only [List.mem_append]; tauto)
          omega
        simp only [hFnew1, ite_eq_left, hnot, decide_false, Bool.false_or]
  · intro e he f hf hef
    apply hE.2.2.1 e he f hf
    simpa only [hF, j] using hef
  · intro f hf
    rcases hE.2.2.2 f hf with hj | ⟨e, he, hef⟩
    · exact Or.inl hj
    · exact Or.inr ⟨e, he, by simpa only [hF, j] using hef⟩
  · intro v hv'
    change G v < T.nextVertex + 1
    rw [hG]; exact hV.1 v hv'
  · intro v hv'
    change j ≤ G v
    rw [hG]; exact hV.2.1 v hv'
  · intro v hv' x hx hvx
    apply hV.2.2.1 v hv' x hx
    simpa only [hG, j] using hvx
  · intro v hv'
    rcases hV.2.2.2 v hv' with hj | ⟨x, hx, hxv⟩
    · exact Or.inl hj
    · exact Or.inr ⟨x, hx, by simpa only [hG, j] using hxv⟩
  · intro i hi
    change i < j at hi
    have hiT : i ≠ T.nextEdge := by have := h.nextEdge; omega
    have hiT1 : i ≠ T.nextEdge + 1 := by have := h.nextEdge; omega
    change (if i = T.nextEdge + 1 then T.nextVertex else
      if i = T.nextEdge then T.west T.active else T.west i) = i ∧
      (if i = T.nextEdge + 1 then T.east T.active else
        if i = T.nextEdge then T.nextVertex else T.east i) = i + 1 ∧
      (if i = T.nextEdge + 1 then false else
        if i = T.nextEdge then true else T.present i) = true
    simpa only [ite_eq_right hiT, ite_eq_right hiT1] using h.chain i hi
  · intro a hamem
    change a ∈ (S.UL.dropLast ++ [S.nextEdge]).head? at hamem
    rw [hxs, List.dropLast_concat] at hamem
    change G (if a = S.nextEdge + 1 then S.nextVertex else
      if a = S.nextEdge then S.west S.active else S.west a) = j
    cases hxs' : xs with
    | nil =>
      have haeq : S.nextEdge = a := by
        simpa only [hxs', List.nil_append, List.head?_cons, Option.mem_some_iff] using hamem
      subst a
      simp only [Nat.ne_add_one, ↓reduceIte, hGold _ (hv S.active ha).1]
      apply h.junction
      simp only [hxs, hxs', List.nil_append, List.head?_cons, Option.mem_some_iff]
    | cons b bs =>
      have haeq : b = a := by
        simpa only [hxs', List.cons_append, List.head?_cons, Option.mem_some_iff] using hamem
      subst a
      have hbmem : b ∈ S.UL := by rw [hxs, hxs']; simp
      have hab := hb b (by simp only [List.mem_append]; tauto)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hGold _ (hv b hab).1]
      apply h.junction
      simp only [hxs, hxs', List.cons_append, List.head?_cons, Option.mem_some_iff]

/-- result. -/
theorem kmswLeftSim_succ_up (r : ℕ) (u : ℕ → Fin 3) (m : ℕ)
    (h : KMSWLeftSim r (kmswStage u m)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + m))
      (kmswLeftSimEdge r u m) (kmswLeftSimVertex r u m))
    (hc : u m = 1) :
    KMSWLeftSim r (kmswStage u (m + 1))
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)))
      (kmswLeftSimEdge r u (m + 1)) (kmswLeftSimVertex r u (m + 1)) := by
  have hs := sim_up h
    (kmswStage_boundary_ids_lt_nextEdge u m).2
    (kmswStage_boundary_ids_lt_nextEdge u m).1
    (kmswStage_endpoints_lt_nextVertex u m) (kmswStage_UL_last u m)
  rw [kmswLeftPrefixed_stage_succ]
  have hcode : kmswCodeStep (1 : Fin 3) = .up := rfl
  simpa only [kmswStage, kmswStep, hc, hcode,
    kmswLeftSimEdge, kmswLeftSimVertex] using hs

private theorem sim_left_existing {r : ℕ} {S T : State} {φ ψ : ℕ → ℕ}
    (h : KMSWLeftSim r S T φ ψ)
    (hb : ∀ e ∈ S.UL ++ S.UR ++ S.LL ++ S.LR, e < S.nextEdge)
    (ha : S.active < S.nextEdge) (xs : List ℕ) (e : ℕ)
    (hSUL : S.UL = xs ++ [e, S.active]) :
    KMSWLeftSim r (kmswStepOfStep S .left) (kmswStepOfStep T .left)
      (kmswLeftExtEdge S 0 (r - 1 - S.LL.length) φ) ψ := by
  let j := r - 1 - S.LL.length
  let F := kmswLeftExtEdge S 0 j φ
  have hdrop : S.UL.dropLast ≠ [] := by
    rw [hSUL, List.dropLast_append_cons]
    simp only [List.dropLast_cons_cons, List.dropLast_singleton]
    exact List.append_ne_nil_of_right_ne_nil xs (by simp)
  have hF (f : ℕ) : F f = if f < S.nextEdge then φ f else f + j := by
    simp [F, kmswLeftExtEdge, hdrop]
  have hFold (f : ℕ) (hf : f < S.nextEdge) : F f = φ f := by rw [hF, ite_eq_left hf]
  have hFnew : F S.nextEdge = T.nextEdge := by
    rw [hF]; simp only [lt_self_iff_false]; exact h.nextEdge.symm
  have hmap (l : List ℕ) (hl : ∀ f ∈ l, f < S.nextEdge) : l.map F = l.map φ :=
    List.map_congr_left (fun f hf => hFold f (hl f hf))
  have hUR := hmap S.UR (fun f hf => hb f (by simp only [List.mem_append]; tauto))
  have hLL := hmap S.LL (fun f hf => hb f (by simp only [List.mem_append]; tauto))
  have hLR := hmap S.LR (fun f hf => hb f (by simp only [List.mem_append]; tauto))
  have hxsmap := hmap xs (fun f hf => hb f (by rw [hSUL]; simp only [List.mem_append]; tauto))
  have he : e < S.nextEdge := hb e (by rw [hSUL]; simp)
  have hTUL : T.UL = ((List.range j ++ xs.map φ) ++ [φ e]) ++ [φ S.active] := by
    rw [h.ul, hSUL]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    rfl
  have hSstack : S.UL.dropLast.reverse = e :: xs.reverse := by
    rw [hSUL, List.dropLast_append_cons]
    simp only [List.dropLast_cons_cons, List.dropLast_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append]
  have hTstack : T.UL.dropLast.reverse = φ e :: (List.range j ++ xs.map φ).reverse := by
    rw [hTUL, List.dropLast_concat]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
  have hE := extend_shift (a := 1) h.nextEdge h.edge_bound h.edge_lower
    h.edge_injective h.edge_cover
  change KMSWLeftSim r (kmswStepOfStep S .left) (kmswStepOfStep T .left) F ψ
  simp only [kmswStepOfStep, hSstack, hTstack, List.reverse_reverse, State.addEdge]
  refine {
    ll_length := h.ll_length
    ul := ?_
    ur := ?_
    ll := h.ll
    lr := ?_
    ll_map := ?_
    active := hFnew.symm
    nextEdge := ?_
    nextVertex := h.nextVertex
    edge_bound := ?_
    edge_lower := ?_
    west := ?_
    east := ?_
    present := ?_
    edge_injective := ?_
    edge_cover := ?_
    vertex_bound := h.vertex_bound
    vertex_lower := h.vertex_lower
    vertex_injective := h.vertex_injective
    vertex_cover := h.vertex_cover
    chain := ?_
    junction := ?_ }
  · change (List.range j ++ xs.map φ) ++ [T.nextEdge] = List.range j ++ (xs ++ [S.nextEdge]).map F
    simp only [List.map_append, List.map_cons, List.map_nil, hFnew, hxsmap, List.append_assoc]
  · change T.UR = S.UR.map F
    rw [hUR]; exact h.ur
  · change T.LR = List.range (r - 1) ++ S.LR.map F
    rw [hLR]; exact h.lr
  · change S.LL.map F = _
    rw [hLL]; exact h.ll_map
  · change T.nextEdge + 1 = S.nextEdge + 1 + j
    have := h.nextEdge; omega
  · intro f hf
    change F f < T.nextEdge + 1
    rw [hF]; exact hE.1 f hf
  · intro f hf
    change j ≤ F f
    rw [hF]; exact hE.2.1 f hf
  · intro f hf
    change (if F f = T.nextEdge then T.west (φ e) else T.west (F f)) =
      ψ (if f = S.nextEdge then S.west e else S.west f)
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold, ite_eq_right (by have := h.edge_bound f hfold; omega),
        ite_eq_right (by omega)]
      exact h.west f hfold
    · have hfE : f = S.nextEdge := by change f < S.nextEdge + 1 at hf; omega
      subst f
      simp only [hFnew, ite_eq_left]
      exact h.west e he
  · intro f hf
    change (if F f = T.nextEdge then T.east T.active else T.east (F f)) =
      ψ (if f = S.nextEdge then S.east S.active else S.east f)
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold, ite_eq_right (by have := h.edge_bound f hfold; omega),
        ite_eq_right (by omega)]
      exact h.east f hfold
    · have hfE : f = S.nextEdge := by change f < S.nextEdge + 1 at hf; omega
      subst f
      simp only [hFnew, ite_eq_left, h.active]
      exact h.east S.active ha
  · intro f hf
    change (if F f = T.nextEdge then true else T.present (F f)) =
      ((if f = S.nextEdge then true else S.present f) || decide (f ∈ S.LL))
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold, ite_eq_right (by have := h.edge_bound f hfold; omega),
        ite_eq_right (by omega)]
      exact h.present f hfold
    · have hfE : f = S.nextEdge := by change f < S.nextEdge + 1 at hf; omega
      subst f
      simp only [hFnew, ite_eq_left, Bool.true_or]
  · intro f hf g hg hfg
    apply hE.2.2.1 f hf g hg
    simpa only [hF, j] using hfg
  · intro f hf
    rcases hE.2.2.2 f hf with hj | ⟨g, hg, hgf⟩
    · exact Or.inl hj
    · exact Or.inr ⟨g, hg, by simpa only [hF, j] using hgf⟩
  · intro i hi
    change i < j at hi
    have hiT : i ≠ T.nextEdge := by have := h.nextEdge; omega
    change (if i = T.nextEdge then T.west (φ e) else T.west i) = i ∧
      (if i = T.nextEdge then T.east T.active else T.east i) = i + 1 ∧
      (if i = T.nextEdge then true else T.present i) = true
    simpa only [ite_eq_right hiT] using h.chain i hi
  · intro a hamem
    change a ∈ (xs ++ [S.nextEdge]).head? at hamem
    change ψ (if a = S.nextEdge then S.west e else S.west a) = j
    cases hxs : xs with
    | nil =>
      have haeq : S.nextEdge = a := by
        simpa only [hxs, List.nil_append, List.head?_cons, Option.mem_some_iff] using hamem
      subst a
      rw [ite_eq_left rfl]
      apply h.junction
      simp only [hSUL, hxs, List.nil_append, List.head?_cons, Option.mem_some_iff]
    | cons b bs =>
      have haeq : b = a := by
        simpa only [hxs, List.cons_append, List.head?_cons, Option.mem_some_iff] using hamem
      subst a
      have hbmem : b ∈ S.UL := by rw [hSUL, hxs]; simp
      have hab := hb b (by simp only [List.mem_append]; tauto)
      rw [ite_eq_right (by omega)]
      apply h.junction
      simp only [hSUL, hxs, List.cons_append, List.head?_cons, Option.mem_some_iff]

/-- result. -/
theorem kmswLeftSim_succ_left_existing (r : ℕ) (u : ℕ → Fin 3) (m : ℕ)
    (h : KMSWLeftSim r (kmswStage u m)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + m))
      (kmswLeftSimEdge r u m) (kmswLeftSimVertex r u m))
    (hc : u m = 0) (hne : (kmswStage u m).UL.dropLast ≠ []) :
    KMSWLeftSim r (kmswStage u (m + 1))
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)))
      (kmswLeftSimEdge r u (m + 1)) (kmswLeftSimVertex r u (m + 1)) := by
  obtain ⟨ys, hys⟩ := kmswStage_UL_last u m
  have hysne : ys ≠ [] := by simpa only [hys, List.dropLast_concat] using hne
  let e := ys.getLast hysne
  let xs := ys.dropLast
  have hys' : xs ++ [e] = ys := List.dropLast_append_getLast hysne
  have hSUL : (kmswStage u m).UL = xs ++ [e, (kmswStage u m).active] := by
    rw [hys, ← hys', List.append_assoc]
    rfl
  have hs := sim_left_existing h (kmswStage_boundary_ids_lt_nextEdge u m).2
    (kmswStage_boundary_ids_lt_nextEdge u m).1 xs e hSUL
  have hcode : kmswCodeStep (u m) = .left := by rw [hc]; rfl
  have hstage : kmswStage u (m + 1) = kmswStepOfStep (kmswStage u m) .left := by
    simp only [kmswStage, kmswStep, hcode]
  have htstage : kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)) =
      kmswStepOfStep (kmswStage (kmswLeftPrefixed r u) (r - 1 + m)) .left := by
    rw [kmswLeftPrefixed_stage_succ]; simp only [kmswStep, hcode]
  rw [← hstage, ← htstage] at hs
  apply sim_relabel_congr hs
  · intro f _
    simp only [kmswLeftSimEdge, hc]
  · intro v hv
    have hstack : (kmswStage u m).UL.dropLast.reverse = e :: xs.reverse := by
      rw [hSUL, List.dropLast_append_cons]
      simp only [List.dropLast_cons_cons, List.dropLast_singleton,
        List.reverse_append, List.reverse_singleton, List.singleton_append]
    have hvold : v < (kmswStage u m).nextVertex := by
      simpa only [hstage, kmswStepOfStep, hstack, State.addEdge] using hv
    exact kmswLeftSimVertex_succ_agree r u m v hvold
  · exact (kmswStage_boundary_ids_lt_nextEdge u (m + 1)).2
  · exact (kmswStage_boundary_ids_lt_nextEdge u (m + 1)).1
  · exact kmswStage_endpoints_lt_nextVertex u (m + 1)

private theorem sim_left_fresh {r : ℕ} {S T : State} {φ ψ : ℕ → ℕ}
    (h : KMSWLeftSim r S T φ ψ)
    (hb : ∀ e ∈ S.UL ++ S.UR ++ S.LL ++ S.LR, e < S.nextEdge)
    (ha : S.active < S.nextEdge)
    (hv : ∀ e < S.nextEdge, S.west e < S.nextVertex ∧ S.east e < S.nextVertex)
    (hSUL : S.UL = [S.active]) (hLL : S.LL.length + 1 ≤ r - 1) :
    KMSWLeftSim r (kmswStepOfStep S .left) (kmswStepOfStep T .left)
      (kmswLeftExtEdge S 0 (r - 1 - S.LL.length) φ)
      (kmswLeftExtVertex S 0 (r - 1 - S.LL.length) ψ) := by
  let j := r - 1 - S.LL.length
  let F := kmswLeftExtEdge S 0 j φ
  let G := kmswLeftExtVertex S 0 j ψ
  have hjpos : 0 < j := by dsimp only [j]; omega
  have hjnext : r - 1 - (S.LL.length + 1) = j - 1 := by dsimp only [j]; omega
  have hjstep : j - 1 + 1 = j := by omega
  have hdrop : S.UL.dropLast = [] := by rw [hSUL]; rfl
  have hF (f : ℕ) : F f = if f < S.nextEdge then φ f else
      if f = S.nextEdge + 1 then j - 1 else f + j := by
    simp only [F, kmswLeftExtEdge, kmswCodeStep, ↓reduceIte, hdrop, true_and]
  have hG (v : ℕ) : G v = if v < S.nextVertex then ψ v else j - 1 := by
    simp only [G, kmswLeftExtVertex, kmswCodeStep, ↓reduceIte, hdrop, true_and]
  have hFold (f : ℕ) (hf : f < S.nextEdge) : F f = φ f := by rw [hF, ite_eq_left hf]
  have hGold (v : ℕ) (hv' : v < S.nextVertex) : G v = ψ v := by rw [hG, ite_eq_left hv']
  have hFnew : F S.nextEdge = T.nextEdge := by
    rw [hF, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact h.nextEdge.symm
  have hFnew1 : F (S.nextEdge + 1) = j - 1 := by
    rw [hF, ite_eq_right (by omega), ite_eq_left rfl]
  have hGnew : G S.nextVertex = j - 1 := by rw [hG, ite_eq_right (by omega)]
  have hmap (l : List ℕ) (hl : ∀ f ∈ l, f < S.nextEdge) : l.map F = l.map φ :=
    List.map_congr_left (fun f hf => hFold f (hl f hf))
  have hUR := hmap S.UR (fun f hf => hb f (by simp only [List.mem_append]; tauto))
  have hLLmap := hmap S.LL (fun f hf => hb f (by simp only [List.mem_append]; tauto))
  have hLR := hmap S.LR (fun f hf => hb f (by simp only [List.mem_append]; tauto))
  have hTUL : T.UL = List.range j ++ [φ S.active] := by
    simpa only [hSUL, List.map_cons, List.map_nil] using h.ul
  have hSstack : S.UL.dropLast.reverse = [] := by rw [hdrop]; rfl
  have hTstack : T.UL.dropLast.reverse = (j - 1) :: (List.range (j - 1)).reverse := by
    rw [hTUL, List.dropLast_concat, ← hjstep, List.range_succ]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      Nat.add_sub_cancel]
  have hchain := h.chain (j - 1) (by change j - 1 < j; omega)
  have hjunction : ψ (S.west S.active) = j := by
    apply h.junction
    simp only [hSUL, List.head?_cons, Option.mem_some_iff]
  change KMSWLeftSim r (kmswStepOfStep S .left) (kmswStepOfStep T .left) F G
  simp only [kmswStepOfStep, hSstack, hTstack, List.reverse_reverse, State.addEdge]
  refine {
    ll_length := hLL
    ul := ?_
    ur := ?_
    ll := h.ll
    lr := ?_
    ll_map := ?_
    active := hFnew.symm
    nextEdge := ?_
    nextVertex := ?_
    edge_bound := ?_
    edge_lower := ?_
    west := ?_
    east := ?_
    present := ?_
    edge_injective := ?_
    edge_cover := ?_
    vertex_bound := ?_
    vertex_lower := ?_
    vertex_injective := ?_
    vertex_cover := ?_
    chain := ?_
    junction := ?_ }
  · change List.range (j - 1) ++ [T.nextEdge] =
      List.range (r - 1 - ((S.nextEdge + 1) :: S.LL).length) ++ [S.nextEdge].map F
    simp only [List.length_cons, hjnext, List.map_cons, List.map_nil, hFnew]
  · change T.UR = S.UR.map F
    rw [hUR]; exact h.ur
  · change T.LR = List.range (r - 1) ++ S.LR.map F
    rw [hLR]; exact h.lr
  · change ((S.nextEdge + 1) :: S.LL).map F =
      List.range' (r - 1 - (S.LL.length + 1)) (S.LL.length + 1)
    rw [List.map_cons, hFnew1, hLLmap, h.ll_map, hjnext, List.range'_succ, hjstep]
  · change T.nextEdge + 1 = S.nextEdge + 1 + 1 + (r - 1 - (S.LL.length + 1))
    have := h.nextEdge
    dsimp only [j] at hjpos
    omega
  · change T.nextVertex = S.nextVertex + 1 + (r - 1 - (S.LL.length + 1))
    have := h.nextVertex
    dsimp only [j] at hjpos
    omega
  · intro f hf
    change F f < T.nextEdge + 1
    change f < S.nextEdge + 1 + 1 at hf
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold]; have := h.edge_bound f hfold; omega
    · by_cases hf0 : f = S.nextEdge
      · subst f; rw [hFnew]; omega
      · have hf1 : f = S.nextEdge + 1 := by omega
        subst f; rw [hFnew1]; have := h.nextEdge; omega
  · intro f hf
    change r - 1 - (S.LL.length + 1) ≤ F f
    rw [hjnext]
    change f < S.nextEdge + 1 + 1 at hf
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold]; have := h.edge_lower f hfold; change j ≤ φ f at this; omega
    · by_cases hf0 : f = S.nextEdge
      · subst f; rw [hFnew]; have := h.nextEdge; omega
      · have hf1 : f = S.nextEdge + 1 := by omega
        subst f; rw [hFnew1]
  · intro f hf
    change (if F f = T.nextEdge then T.west (j - 1) else T.west (F f)) =
      G (if f = S.nextEdge + 1 then S.nextVertex else
        if f = S.nextEdge then S.nextVertex else S.west f)
    change f < S.nextEdge + 1 + 1 at hf
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold, ite_eq_right (by have := h.edge_bound f hfold; omega),
        ite_eq_right (by omega), ite_eq_right (by omega), hGold _ (hv f hfold).1]
      exact h.west f hfold
    · by_cases hf0 : f = S.nextEdge
      · subst f
        rw [hFnew, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl, hGnew]
        exact hchain.1
      · have hf1 : f = S.nextEdge + 1 := by omega
        subst f
        rw [hFnew1, ite_eq_right (by have := h.nextEdge; omega), ite_eq_left rfl, hGnew]
        exact hchain.1
  · intro f hf
    change (if F f = T.nextEdge then T.east T.active else T.east (F f)) =
      G (if f = S.nextEdge + 1 then S.west S.active else
        if f = S.nextEdge then S.east S.active else S.east f)
    change f < S.nextEdge + 1 + 1 at hf
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold, ite_eq_right (by have := h.edge_bound f hfold; omega),
        ite_eq_right (by omega), ite_eq_right (by omega), hGold _ (hv f hfold).2]
      exact h.east f hfold
    · by_cases hf0 : f = S.nextEdge
      · subst f
        rw [hFnew, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl,
          hGold _ (hv S.active ha).2, h.active]
        exact h.east S.active ha
      · have hf1 : f = S.nextEdge + 1 := by omega
        subst f
        rw [hFnew1, ite_eq_right (by have := h.nextEdge; omega), ite_eq_left rfl,
          hGold _ (hv S.active ha).1, hjunction, hchain.2.1]
        exact hjstep
  · intro f hf
    change (if F f = T.nextEdge then true else T.present (F f)) =
      ((if f = S.nextEdge + 1 then false else
        if f = S.nextEdge then true else S.present f) || decide (f ∈ (S.nextEdge + 1) :: S.LL))
    change f < S.nextEdge + 1 + 1 at hf
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold, ite_eq_right (by have := h.edge_bound f hfold; omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
      have hneq : f ≠ S.nextEdge + 1 := by omega
      simpa only [List.mem_cons, hneq, false_or] using h.present f hfold
    · by_cases hf0 : f = S.nextEdge
      · subst f
        simp only [hFnew, Nat.ne_add_one, ↓reduceIte, Bool.true_or]
      · have hf1 : f = S.nextEdge + 1 := by omega
        subst f
        rw [hFnew1, ite_eq_right (by have := h.nextEdge; omega), ite_eq_left rfl]
        simp only [List.mem_cons, true_or, decide_true, Bool.or_true]
        exact hchain.2.2
  · intro f hf g hg hfg
    change f < S.nextEdge + 1 + 1 at hf
    change g < S.nextEdge + 1 + 1 at hg
    by_cases hfold : f < S.nextEdge
    · rw [hFold f hfold] at hfg
      by_cases hgold : g < S.nextEdge
      · rw [hFold g hgold] at hfg
        exact h.edge_injective f hfold g hgold hfg
      · by_cases hg0 : g = S.nextEdge
        · subst g; rw [hFnew] at hfg; have := h.edge_bound f hfold; omega
        · have hg1 : g = S.nextEdge + 1 := by omega
          subst g; rw [hFnew1] at hfg
          have := h.edge_lower f hfold; change j ≤ φ f at this; omega
    · by_cases hgold : g < S.nextEdge
      · rw [hFold g hgold] at hfg
        by_cases hf0 : f = S.nextEdge
        · subst f; rw [hFnew] at hfg; have := h.edge_bound g hgold; omega
        · have hf1 : f = S.nextEdge + 1 := by omega
          subst f; rw [hFnew1] at hfg
          have := h.edge_lower g hgold; change j ≤ φ g at this; omega
      · by_cases hf0 : f = S.nextEdge <;> by_cases hg0 : g = S.nextEdge
        · omega
        · have hg1 : g = S.nextEdge + 1 := by omega
          subst f; subst g; rw [hFnew, hFnew1] at hfg; have := h.nextEdge; omega
        · have hf1 : f = S.nextEdge + 1 := by omega
          subst f; subst g; rw [hFnew1, hFnew] at hfg; have := h.nextEdge; omega
        · omega
  · intro f hf
    change f < T.nextEdge + 1 at hf
    change f < r - 1 - (S.LL.length + 1) ∨ ∃ e < S.nextEdge + 1 + 1, F e = f
    rw [hjnext]
    by_cases hfj : f < j - 1
    · exact Or.inl hfj
    · right
      by_cases hfT : f < T.nextEdge
      · rcases h.edge_cover f hfT with hfchain | ⟨e, he, hef⟩
        · refine ⟨S.nextEdge + 1, by omega, ?_⟩
          rw [hFnew1]
          change f < j at hfchain
          omega
        · exact ⟨e, by omega, (hFold e he).trans hef⟩
      · refine ⟨S.nextEdge, by omega, ?_⟩
        rw [hFnew]; omega
  · intro v hv'
    change v < S.nextVertex + 1 at hv'
    change G v < T.nextVertex
    by_cases hvold : v < S.nextVertex
    · rw [hGold v hvold]; exact h.vertex_bound v hvold
    · have hveq : v = S.nextVertex := by omega
      subst v; rw [hGnew]; have := h.nextVertex; omega
  · intro v hv'
    change v < S.nextVertex + 1 at hv'
    change r - 1 - (S.LL.length + 1) ≤ G v
    rw [hjnext]
    by_cases hvold : v < S.nextVertex
    · rw [hGold v hvold]; have := h.vertex_lower v hvold; change j ≤ ψ v at this; omega
    · have hveq : v = S.nextVertex := by omega
      subst v; rw [hGnew]
  · intro v hv' x hx hvx
    change v < S.nextVertex + 1 at hv'
    change x < S.nextVertex + 1 at hx
    by_cases hvold : v < S.nextVertex
    · rw [hGold v hvold] at hvx
      by_cases hxold : x < S.nextVertex
      · rw [hGold x hxold] at hvx
        exact h.vertex_injective v hvold x hxold hvx
      · have hxeq : x = S.nextVertex := by omega
        subst x; rw [hGnew] at hvx
        have := h.vertex_lower v hvold; change j ≤ ψ v at this; omega
    · have hveq : v = S.nextVertex := by omega
      subst v; rw [hGnew] at hvx
      by_cases hxold : x < S.nextVertex
      · rw [hGold x hxold] at hvx
        have := h.vertex_lower x hxold; change j ≤ ψ x at this; omega
      · omega
  · intro v hv'
    change v < T.nextVertex at hv'
    change v < r - 1 - (S.LL.length + 1) ∨ ∃ x < S.nextVertex + 1, G x = v
    rw [hjnext]
    by_cases hvj : v < j - 1
    · exact Or.inl hvj
    · right
      rcases h.vertex_cover v hv' with hvchain | ⟨x, hx, hxv⟩
      · refine ⟨S.nextVertex, by omega, ?_⟩
        rw [hGnew]
        change v < j at hvchain
        omega
      · exact ⟨x, by omega, (hGold x hx).trans hxv⟩
  · intro i hi
    change i < r - 1 - (S.LL.length + 1) at hi
    rw [hjnext] at hi
    have hiT : i ≠ T.nextEdge := by have := h.nextEdge; omega
    change (if i = T.nextEdge then T.west (j - 1) else T.west i) = i ∧
      (if i = T.nextEdge then T.east T.active else T.east i) = i + 1 ∧
      (if i = T.nextEdge then true else T.present i) = true
    simpa only [ite_eq_right hiT] using h.chain i (by change i < j; omega)
  · intro a hamem
    change a ∈ [S.nextEdge].head? at hamem
    have haeq : S.nextEdge = a := by simpa only [List.head?_cons, Option.mem_some_iff] using hamem
    subst a
    change G (if S.nextEdge = S.nextEdge + 1 then S.nextVertex else
      if S.nextEdge = S.nextEdge then S.nextVertex else S.west S.nextEdge) =
        r - 1 - (S.LL.length + 1)
    simp only [Nat.ne_add_one, ↓reduceIte, hGnew, hjnext]

/-- result. -/
theorem kmswLeftSim_succ_left_fresh (r : ℕ) (u : ℕ → Fin 3) (m : ℕ)
    (h : KMSWLeftSim r (kmswStage u m)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + m))
      (kmswLeftSimEdge r u m) (kmswLeftSimVertex r u m))
    (hc : u m = 0) (hempty : (kmswStage u m).UL.dropLast = [])
    (hLL : (kmswStage u (m + 1)).LL.length ≤ r - 1) :
    KMSWLeftSim r (kmswStage u (m + 1))
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)))
      (kmswLeftSimEdge r u (m + 1)) (kmswLeftSimVertex r u (m + 1)) := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
  have hxs0 : xs = [] := by simpa only [hxs, List.dropLast_concat] using hempty
  have hSUL : (kmswStage u m).UL = [(kmswStage u m).active] := by
    rw [hxs, hxs0]; rfl
  have hcode : kmswCodeStep (u m) = .left := by rw [hc]; rfl
  have hstack : (kmswStage u m).UL.dropLast.reverse = [] := by rw [hempty]; rfl
  have hLL' : (kmswStage u m).LL.length + 1 ≤ r - 1 := by
    simpa only [kmswStage, kmswStep, hcode, kmswStepOfStep, hstack,
      State.addEdge, List.length_cons] using hLL
  have hs := sim_left_fresh h
    (kmswStage_boundary_ids_lt_nextEdge u m).2
    (kmswStage_boundary_ids_lt_nextEdge u m).1
    (kmswStage_endpoints_lt_nextVertex u m) hSUL hLL'
  rw [kmswLeftPrefixed_stage_succ]
  have hcode0 : kmswCodeStep (0 : Fin 3) = .left := rfl
  simpa only [kmswStage, kmswStep, hc, hcode0,
    kmswLeftSimEdge, kmswLeftSimVertex] using hs

/-- result. -/
theorem kmswLeftSim_succ (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (m : ℕ)
    (h : KMSWLeftSim r (kmswStage u m)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + m))
      (kmswLeftSimEdge r u m) (kmswLeftSimVertex r u m))
    (hLL : (kmswStage u (m + 1)).LL.length ≤ r - 1) :
    KMSWLeftSim r (kmswStage u (m + 1))
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + (m + 1)))
      (kmswLeftSimEdge r u (m + 1)) (kmswLeftSimVertex r u (m + 1)) := by
  have _hr := hr
  have hcases : u m = 0 ∨ u m = 1 ∨ u m = 2 := by omega
  rcases hcases with hc | hc | hc
  · by_cases hempty : (kmswStage u m).UL.dropLast = []
    · exact kmswLeftSim_succ_left_fresh r u m h hc hempty hLL
    · exact kmswLeftSim_succ_left_existing r u m h hc hempty
  · exact kmswLeftSim_succ_up r u m h hc
  · by_cases hempty : (kmswStage u m).UR = []
    · exact kmswLeftSim_succ_down_fresh r u m h hc hempty
    · exact kmswLeftSim_succ_down_existing r u m h hc hempty

/-- result. -/
theorem kmswLeftSim_of_quadrant (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k) :
    KMSWLeftSim r (kmswStage u n)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + n))
      (kmswLeftSimEdge r u n) (kmswLeftSimVertex r u n) := by
  induction n with
  | zero => simpa only [Nat.add_zero] using kmswLeftSim_zero r u hr
  | succ n ih =>
    apply kmswLeftSim_succ r u hr n
    · exact ih (fun k hk => hquad k (by omega))
    · exact kmswLeftSim_LL_bound r u hr (n + 1) hquad

/-- result. -/
theorem kmswLeftSim_terminal_bijective (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (hterminal : (kmswStage u n).LL.length = r - 1) :
    let S := kmswStage u n
    let T := kmswStage (kmswLeftPrefixed r u) (r - 1 + n)
    let φ := kmswLeftSimEdge r u n
    let ψ := kmswLeftSimVertex r u n
    (∀ e < S.nextEdge, φ e < T.nextEdge) ∧
    (∀ e < S.nextEdge, ∀ f < S.nextEdge, φ e = φ f → e = f) ∧
    (∀ f < T.nextEdge, ∃ e < S.nextEdge, φ e = f) ∧
    (∀ v < S.nextVertex, ψ v < T.nextVertex) ∧
    (∀ v < S.nextVertex, ∀ x < S.nextVertex, ψ v = ψ x → v = x) ∧
    (∀ v < T.nextVertex, ∃ x < S.nextVertex, ψ x = v) ∧
    S.LL.map φ = List.range (r - 1) ∧
    T.LR = S.LL.map φ ++ S.LR.map φ ∧
    T.UL = S.UL.map φ ∧ T.UR = S.UR.map φ ∧ T.LL = [] := by
  exact (kmswLeftSim_of_quadrant r u hr n hquad).terminal_bijective hterminal

/-- result. -/
theorem kmswLeftSim_missing_iff_ur (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (e : ℕ) (he : e < (kmswStage u n).nextEdge) :
    (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).present
        (kmswLeftSimEdge r u n e) = false ↔ e ∈ (kmswStage u n).UR := by
  have h := kmswLeftSim_of_quadrant r u hr n hquad
  rw [h.present e he]
  have hstatus := (kmswStage_status u n).1 e he
  have hdisj := (kmswStage_status u n).2.2.2.2.2
  constructor
  · intro hp
    have hfalse : (kmswStage u n).present e = false := by
      cases hpe : (kmswStage u n).present e <;> simp_all
    have hnot : e ∉ (kmswStage u n).LL := by
      intro hmem
      simp only [hmem, decide_true, Bool.or_true] at hp
      cases hp
    exact (hstatus.mp hfalse).resolve_right hnot
  · intro hUR
    have hfalse := hstatus.mpr (Or.inl hUR)
    have hnot : e ∉ (kmswStage u n).LL := fun hLL => hdisj e hUR hLL
    simp only [hfalse, hnot, decide_false, Bool.false_or]

end DirectedDistances.KMSW
