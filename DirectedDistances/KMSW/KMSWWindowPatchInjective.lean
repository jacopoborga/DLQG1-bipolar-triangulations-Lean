module

public import DirectedDistances.KMSW.KMSWWindowPatchVertex
import DirectedDistances.KMSW.StageIncidenceChains
import DirectedDistances.KMSW.CutEquivalenceConverse

 

public section
namespace DirectedDistances.KMSW

private theorem chain_rank_vertices (G : State) (r : ℕ → ℚ) (e : ℕ)
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

private theorem chain_cut_rank_vertices (G : State) (r : ℕ → ℚ)
    (A : List ℕ) (e : ℕ) (B : List ℕ)
    (hc : WestEastChain G (A ++ e :: B))
    (hr : ∀ a ∈ A ++ e :: B, r (G.west a) < r (G.east a)) :
    ((A.map G.west ++ G.west e :: G.east e :: B.map G.east).map r).Pairwise
      (· < ·) := by
  induction A with
  | nil => simpa only [List.map_nil, List.nil_append, List.map_cons,
      List.map_map, Function.comp_def] using chain_rank_vertices G r e B hc hr
  | cons a A ih =>
    have hchain := List.isChain_cons.mp hc
    have hi := ih hchain.2 (fun b hb => hr b (List.mem_cons_of_mem _ hb))
    have ha := hr a (by simp)
    cases A with
    | nil =>
      have hj := (List.isChain_cons_cons.mp hc).1
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.pairwise_cons_cons_iff_of_trans]
      refine ⟨by simpa only [hj] using ha, ?_⟩
      simpa only [List.map_nil, List.nil_append, List.map_cons,
        List.pairwise_cons_cons_iff_of_trans] using hi
    | cons b A =>
      have hj := (List.isChain_cons_cons.mp hc).1
      simp only [List.map_cons, List.cons_append,
        List.pairwise_cons_cons_iff_of_trans] at hi ⊢
      exact ⟨by simpa only [hj] using ha, hi⟩

 
theorem kmswStage_upperBoundary_vertices_nodup (w : ℕ → Fin 3) (s : ℕ) :
    (((kmswStage w s).UL.dropLast.map (kmswStage w s).west) ++
      (kmswStage w s).west (kmswStage w s).active ::
      (kmswStage w s).east (kmswStage w s).active ::
      (kmswStage w s).UR.map (kmswStage w s).east).Nodup := by
  let G := kmswStage w s
  obtain ⟨A, hA⟩ := kmswStage_UL_last w s
  have hc := (kmswStage_boundary_chain_invariant w s).1
  have hdrop : G.UL.dropLast = A := by simp only [G, hA, List.dropLast_concat]
  have hUL : G.UL = A ++ [G.active] := hA
  rw [hUL, List.append_assoc, List.singleton_append] at hc
  have hp := chain_cut_rank_vertices G (kmswStageRank w s) A G.active G.UR hc
    (fun a ha => kmswStageRank_strict w s a
      ((kmswStage_boundary_ids_lt_nextEdge w s).2 a (by
        change a ∈ G.UL ++ G.UR ++ G.LL ++ G.LR
        rw [hUL]
        simp only [List.mem_append, List.mem_cons] at ha ⊢
        tauto)))
  change (G.UL.dropLast.map G.west ++ G.west G.active ::
    G.east G.active :: G.UR.map G.east).Nodup
  rw [hdrop]
  have hv := List.pairwise_map.mp hp
  exact hv.imp (fun h heq => (ne_of_lt h) (congrArg (kmswStageRank w s) heq))

private structure WindowVertexInvariant (G₀ : State) (n : ℕ) (ψ : ℕ → ℕ)
    (A B : List ℕ) : Prop where
  injective : Set.InjOn ψ {v | v < n}
  left : ∀ v < n, ∀ a ∈ A, ψ v ≠ G₀.west a
  right : ∀ v < n, ∀ b ∈ B, ψ v ≠ G₀.east b

private theorem extend_vertex_invariant {G₀ : State} {n : ℕ} {ψ : ℕ → ℕ}
    {A B : List ℕ} (h : WindowVertexInvariant G₀ n ψ A B)
    (z : ℕ) (A' B' : List ℕ)
    (hA : ∀ a ∈ A', a ∈ A) (hB : ∀ b ∈ B', b ∈ B)
    (hz : ∀ v < n, ψ v ≠ z)
    (hleft : ∀ a ∈ A', z ≠ G₀.west a)
    (hright : ∀ b ∈ B', z ≠ G₀.east b) :
    WindowVertexInvariant G₀ (n + 1) (fun v => if v < n then ψ v else z) A' B' := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv t ht heq
    change v < n + 1 at hv
    change t < n + 1 at ht
    by_cases hvn : v < n <;> by_cases htn : t < n
    · simp only [hvn, htn, ite_true] at heq
      exact h.injective hvn htn heq
    · simp only [hvn, htn, ite_true, ite_false] at heq
      exact (hz v hvn heq).elim
    · simp only [hvn, htn, ite_true, ite_false] at heq
      exact (hz t htn heq.symm).elim
    · omega
  · intro v hv a ha
    by_cases hvn : v < n
    · simpa only [hvn, ite_true] using h.left v hvn a (hA a ha)
    · simpa only [hvn, ite_false] using hleft a ha
  · intro v hv b hb
    by_cases hvn : v < n
    · simpa only [hvn, ite_true] using h.right v hvn b (hB b hb)
    · simpa only [hvn, ite_false] using hright b hb

private theorem initial_vertex_invariant (w : ℕ → Fin 3) (s : ℕ) :
    WindowVertexInvariant (kmswStage w s) 2 (kmswWindowPatchVertexMap w s 0)
      (kmswStage w s).UL.dropLast (kmswStage w s).UR := by
  let G := kmswStage w s
  have hn := kmswStage_upperBoundary_vertices_nodup w s
  have hs := List.nodup_append'.mp hn
  have hroot := List.nodup_cons.mp hs.2.1
  have hright := List.nodup_cons.mp hroot.2
  have hends : G.west G.active ≠ G.east G.active := by
    intro heq
    exact hroot.1 (by simp only [List.mem_cons]; exact Or.inl heq)
  have hzero (v : ℕ) : kmswWindowPatchVertexMap w s 0 v =
      if v = 0 then G.west G.active else G.east G.active := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro v hv t ht heq
    change v < 2 at hv
    change t < 2 at ht
    rw [hzero, hzero] at heq
    by_cases hv0 : v = 0 <;> by_cases ht0 : t = 0
    · omega
    · simp only [hv0, ht0, ite_true, ite_false] at heq
      exact (hends heq).elim
    · simp only [hv0, ht0, ite_true, ite_false] at heq
      exact (hends heq.symm).elim
    · omega
  · intro v hv a ha heq
    have ham : G.west a ∈ G.UL.dropLast.map G.west :=
      List.mem_map.mpr ⟨a, ha, rfl⟩
    apply hs.2.2 ham
    rw [← heq, hzero]
    split <;> simp [G]
  · intro v hv b hb heq
    have hbm : G.east b ∈ G.UR.map G.east := List.mem_map.mpr ⟨b, hb, rfl⟩
    rw [hzero] at heq
    split at heq
    · exact hroot.1 (List.mem_cons_of_mem _ (heq ▸ hbm))
    · exact hright.1 (heq ▸ hbm)

 
theorem kmswWindowPatchVertexMap_zero_invariant (w : ℕ → Fin 3) (s : ℕ) :
    Set.InjOn (kmswWindowPatchVertexMap w s 0) {v | v < 2} ∧
      (∀ v < 2, ∀ a ∈ (kmswStage w s).UL.dropLast,
        kmswWindowPatchVertexMap w s 0 v ≠ (kmswStage w s).west a) ∧
      (∀ v < 2, ∀ b ∈ (kmswStage w s).UR,
        kmswWindowPatchVertexMap w s 0 v ≠ (kmswStage w s).east b) := by
  have h := initial_vertex_invariant w s
  exact ⟨h.injective, h.left, h.right⟩

private theorem window_vertex_invariant (w : ℕ → Fin 3) (s j : ℕ) :
    WindowVertexInvariant (kmswStage w s)
      (kmswStage (fun i => w (s + i)) j).nextVertex
      (kmswWindowPatchVertexMap w s j)
      (kmswWindowPatchData w s j).A (kmswWindowPatchData w s j).B := by
  induction j with
  | zero => exact initial_vertex_invariant w s
  | succ j ih =>
    let G₀ := kmswStage w s
    let G := kmswStage w (s + j)
    let u := fun i => w (s + i)
    let F := kmswStage u j
    let d := kmswWindowPatchData w s j
    let ψ := kmswWindowPatchVertexMap w s j
    change WindowVertexInvariant G₀ F.nextVertex ψ d.A d.B at ih
    have h := kmswWindowPatchData_rel w s j
    change KMSWWindowPatchRel G₀ G F d.φ d.A d.B d.YL d.YR d.XL d.XR at h
    have hv := kmswWindowPatchVertexMap_rel w s j
    change KMSWWindowPatchVertexRel G F d.φ ψ at hv
    have hsj : s ≤ s + j := by omega
    have hA (a : ℕ) (ha : a ∈ d.A) : a ∈ G₀.UL.dropLast := by
      rw [h.left_residual]
      exact List.mem_append_left _ ha
    have hB (b : ℕ) (hb : b ∈ d.B) : b ∈ G₀.UR := by
      rw [h.right_residual]
      exact List.mem_append_right _ hb
    have hAbound (a : ℕ) (ha : a ∈ d.A) : a < G₀.nextEdge := by
      apply (kmswStage_boundary_ids_lt_nextEdge w s).2
      have hm := (List.dropLast_sublist G₀.UL).subset (hA a ha)
      change a ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
      simp only [List.mem_append]
      tauto
    have hBbound (b : ℕ) (hb : b ∈ d.B) : b < G₀.nextEdge := by
      apply (kmswStage_boundary_ids_lt_nextEdge w s).2
      have hm := hB b hb
      change b ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
      simp only [List.mem_append]
      tauto
    have hstableA (a : ℕ) (ha : a ∈ d.A) : G.west a = G₀.west a :=
      (kmswStage_endpoints_stable w hsj (hAbound a ha)).1
    have hstableB (b : ℕ) (hb : b ∈ d.B) : G.east b = G₀.east b :=
      (kmswStage_endpoints_stable w hsj (hBbound b hb)).2
    have hallocA (a : ℕ) (ha : a ∈ d.A) : G.nextVertex ≠ G₀.west a := by
      have he := (kmswStage_endpoints_lt_nextVertex w s a (hAbound a ha)).1
      change G₀.west a < G₀.nextVertex at he
      have hm := CutConverse.nextVertex_mono w hsj
      change G₀.nextVertex ≤ G.nextVertex at hm
      omega
    have hallocB (b : ℕ) (hb : b ∈ d.B) : G.nextVertex ≠ G₀.east b := by
      have he := (kmswStage_endpoints_lt_nextVertex w s b (hBbound b hb)).2
      change G₀.east b < G₀.nextVertex at he
      have hm := CutConverse.nextVertex_mono w hsj
      change G₀.nextVertex ≤ G.nextVertex at hm
      omega
    have halloc (v : ℕ) (ht : v < F.nextVertex) : ψ v ≠ G.nextVertex :=
      Nat.ne_of_lt (hv.vertex_bound v ht)
    have hn := kmswStage_upperBoundary_vertices_nodup w s
    change (G₀.UL.dropLast.map G₀.west ++ G₀.west G₀.active ::
      G₀.east G₀.active :: G₀.UR.map G₀.east).Nodup at hn
    have hp := List.nodup_append'.mp hn
    have hiA := List.inj_on_of_nodup_map hp.1
    have hiB := List.inj_on_of_nodup_map
      (List.nodup_cons.mp (List.nodup_cons.mp hp.2.1).2).2
    have hcross (a : ℕ) (ha : a ∈ d.A) (b : ℕ) (hb : b ∈ d.B) :
        G₀.west a ≠ G₀.east b := by
      intro heq
      apply hp.2.2 (List.mem_map.mpr ⟨a, hA a ha, rfl⟩)
      rw [heq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨b, hB b hb, rfl⟩))
    change WindowVertexInvariant G₀
      (kmswStepOfStep F (kmswCodeStep (w (s + j)))).nextVertex
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
      (d.step G F (kmswCodeStep (w (s + j)))).A
      (d.step G F (kmswCodeStep (w (s + j)))).B
    cases hc : kmswCodeStep (w (s + j)) with
    | up =>
      simpa only [kmswStepOfStep, State.addEdge, KMSWWindowPatchData.step] using
        extend_vertex_invariant ih G.nextVertex d.A d.B
          (fun _ ha => ha) (fun _ hb => hb) halloc hallocA hallocB
    | down =>
      cases hu : F.UR with
      | cons e es =>
        simpa only [kmswStepOfStep, hu, KMSWWindowPatchData.step] using ih
      | nil =>
        cases hb : d.B with
        | nil =>
          simpa only [kmswStepOfStep, hu, State.addEdge,
            KMSWWindowPatchData.step, hb] using
            extend_vertex_invariant ih G.nextVertex d.A d.B
              (fun _ ha => ha) (fun _ ht => ht) halloc hallocA hallocB
        | cons q bs =>
          have hq : q ∈ d.B := by rw [hb]; exact List.mem_cons_self
          have hsub (b : ℕ) (ht : b ∈ bs) : b ∈ d.B := by
            rw [hb]
            exact List.mem_cons_of_mem _ ht
          have hqnot : q ∉ bs := by
            have hh := (List.nodup_append'.mp h.residual_nodup).2.1
            rw [hb] at hh
            exact (List.nodup_cons.mp hh).1
          have hnew (v : ℕ) (ht : v < F.nextVertex) : ψ v ≠ G.east q := by
            rw [hstableB q hq]
            exact ih.right v ht q hq
          have hnewA (a : ℕ) (ha : a ∈ d.A) : G.east q ≠ G₀.west a := by
            rw [hstableB q hq]
            exact (hcross a ha q hq).symm
          have hnewB (b : ℕ) (ht : b ∈ bs) : G.east q ≠ G₀.east b := by
            rw [hstableB q hq]
            intro heq
            have hqb := hiB (hB q hq) (hB b (hsub b ht)) heq
            exact hqnot (hqb.symm ▸ ht)
          simpa only [kmswStepOfStep, hu, State.addEdge,
            KMSWWindowPatchData.step, hb] using
            extend_vertex_invariant ih (G.east q) d.A bs
              (fun _ ha => ha) hsub hnew hnewA hnewB
    | left =>
      cases hs : F.UL.dropLast.reverse with
      | cons e es =>
        simpa only [kmswStepOfStep, hs, State.addEdge,
          KMSWWindowPatchData.step] using ih
      | nil =>
        cases ha : d.A.reverse with
        | nil =>
          simpa only [kmswStepOfStep, hs, State.addEdge,
            KMSWWindowPatchData.step, ha] using
            extend_vertex_invariant ih G.nextVertex d.A d.B
              (fun _ ht => ht) (fun _ hb => hb) halloc hallocA hallocB
        | cons q es =>
          have hAsplit : d.A = es.reverse ++ [q] := by
            have hh := congrArg List.reverse ha
            simpa only [List.reverse_reverse, List.reverse_cons] using hh
          have hq : q ∈ d.A := by rw [hAsplit]; simp
          have hsub (a : ℕ) (ht : a ∈ es.reverse) : a ∈ d.A := by
            rw [hAsplit]
            exact List.mem_append_left _ ht
          have hqnot : q ∉ es.reverse := by
            have hh := (List.nodup_append'.mp h.residual_nodup).1
            rw [hAsplit] at hh
            intro hm
            exact (List.nodup_append'.mp hh).2.2 hm (by simp)
          have hnew (v : ℕ) (ht : v < F.nextVertex) : ψ v ≠ G.west q := by
            rw [hstableA q hq]
            exact ih.left v ht q hq
          have hnewA (a : ℕ) (ht : a ∈ es.reverse) : G.west q ≠ G₀.west a := by
            rw [hstableA q hq]
            intro heq
            have hqa := hiA (hA q hq) (hA a (hsub a ht)) heq
            exact hqnot (hqa.symm ▸ ht)
          have hnewB (b : ℕ) (hb : b ∈ d.B) : G.west q ≠ G₀.east b := by
            rw [hstableA q hq]
            exact hcross q hq b hb
          simpa only [kmswStepOfStep, hs, State.addEdge,
            KMSWWindowPatchData.step, ha] using
            extend_vertex_invariant ih (G.west q) es.reverse d.B
              hsub (fun _ hb => hb) hnew hnewA hnewB

 
theorem kmswWindowPatchVertexMap_injOn (w : ℕ → Fin 3) (s j : ℕ) :
    Set.InjOn (kmswWindowPatchVertexMap w s j)
      {v | v < (kmswStage (fun i => w (s + i)) j).nextVertex} :=
  (window_vertex_invariant w s j).injective

end DirectedDistances.KMSW
