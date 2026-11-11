module

public import DirectedDistances.KMSW.KMSWWholePlaneRotationTransport

/-! 206–213): exact characterization of the window vertices identified with already-present
global vertices (the seam), toward the cofinal-freshness conjunct of
WholePlaneRotationHypothesis; its identification with the source left boundary of
M_{n,∞} (Lemma 3.10) and the almost-sure discharge are not treated; not the paper result. -/

public section
namespace DirectedDistances.KMSW

private def windowVertexSeamAt (w : ℕ → Fin 3) (s k v : ℕ) : Prop :=
  v = (kmswStage (fun i => w (s + i)) k).nextVertex ∧
    ((kmswCodeStep (w (s + k)) = .down ∧
        (kmswStage (fun i => w (s + i)) k).UR = [] ∧
        (kmswWindowPatchData w s k).B ≠ []) ∨
      (kmswCodeStep (w (s + k)) = .left ∧
        (kmswStage (fun i => w (s + i)) k).UL.dropLast.reverse = [] ∧
        (kmswWindowPatchData w s k).A.reverse ≠ []))

private theorem windowVertexSeamAt_allocates (w : ℕ → Fin 3) (s k v : ℕ)
    (h : windowVertexSeamAt w s k v) :
    (kmswStage (fun i => w (s + i)) k).nextVertex <
      (kmswStage (fun i => w (s + i)) (k + 1)).nextVertex := by
  rcases h with ⟨hv, hstep | hstep⟩
  · rcases hstep with ⟨hc, hu, _⟩
    have halloc : (kmswStage (fun i => w (s + i)) k).nextVertex <
        (kmswStage (fun i => w (s + i)) (k + 1)).nextVertex := by
      simp [kmswStage, kmswStep, hc, kmswStepOfStep, hu]
    exact halloc
  · rcases hstep with ⟨hc, hs, _⟩
    have hs' : (kmswStage (fun i => w (s + i)) k).UL.dropLast = [] :=
      List.reverse_eq_nil_iff.mp hs
    have halloc : (kmswStage (fun i => w (s + i)) k).nextVertex <
        (kmswStage (fun i => w (s + i)) (k + 1)).nextVertex := by
      simp [kmswStage, kmswStep, hc, kmswStepOfStep, hs']
    exact halloc

private theorem windowVertexSeamAt_before (w : ℕ → Fin 3) (s j k v : ℕ)
    (hkj : k < j) (hseam : windowVertexSeamAt w s k v) :
    v < (kmswStage (fun i => w (s + i)) j).nextVertex := by
  have halloc := windowVertexSeamAt_allocates w s k v hseam
  have hmono := CutConverse.nextVertex_mono (fun i => w (s + i))
    (Nat.succ_le_of_lt hkj)
  calc
    v < (kmswStage (fun i => w (s + i)) (k + 1)).nextVertex := by
      rw [hseam.1]
      exact halloc
    _ ≤ (kmswStage (fun i => w (s + i)) j).nextVertex := hmono

private theorem windowVertexSeamBefore_succ_old (w : ℕ → Fin 3)
    (s j v : ℕ) (hv : v < (kmswStage (fun i => w (s + i)) j).nextVertex) :
    (v < 2 ∨ ∃ k < j + 1, windowVertexSeamAt w s k v) ↔
      (v < 2 ∨ ∃ k < j, windowVertexSeamAt w s k v) := by
  constructor
  · rintro (hsmall | ⟨k, hkj, hseam⟩)
    · exact Or.inl hsmall
    · have hlt : k < j ∨ k = j := by omega
      rcases hlt with hlt | rfl
      · exact Or.inr ⟨k, hlt, hseam⟩
      · exact False.elim (by have := hseam.1; omega)
  · rintro (hsmall | ⟨k, hkj, hseam⟩)
    · exact Or.inl hsmall
    · exact Or.inr ⟨k, by omega, hseam⟩

private theorem windowVertexSeamBefore_succ_new (w : ℕ → Fin 3)
    (s j v : ℕ) (hv : v = (kmswStage (fun i => w (s + i)) j).nextVertex) :
    (v < 2 ∨ ∃ k < j + 1, windowVertexSeamAt w s k v) ↔
      windowVertexSeamAt w s j v := by
  have hbase : 2 ≤ (kmswStage (fun i => w (s + i)) j).nextVertex := by
    have hm := CutConverse.nextVertex_mono (fun i => w (s + i))
      (m := 0) (n := j) (Nat.zero_le j)
    simpa only [kmswStage, kmswInit] using hm
  constructor
  · rintro (hsmall | ⟨k, hkj, hseam⟩)
    · omega
    · have hk : k < j ∨ k = j := by omega
      rcases hk with hk | rfl
      · have hlt := windowVertexSeamAt_before w s j k v hk hseam
        have hbad : v < v := by rw [← hv] at hlt; exact hlt
        exact False.elim (Nat.lt_irrefl _ hbad)
      · exact hseam
  · intro hseam
    exact Or.inr ⟨j, by omega, hseam⟩

private theorem windowVertexSeamAt_east_old (w : ℕ → Fin 3) (s j q : ℕ)
    (hq : q ∈ (kmswWindowPatchData w s j).B) :
    (kmswStage w (s + j)).east q < (kmswStage w s).nextVertex := by
  have hrel := kmswWindowPatchData_rel w s j
  have hbaseMem : q ∈ (kmswStage w s).UR := by
    rw [hrel.right_residual]
    simp only [List.mem_append]
    exact Or.inr hq
  have hnowMem : q ∈ (kmswStage w (s + j)).UR := by
    rw [hrel.ur]
    simp only [List.mem_append]
    exact Or.inr hq
  have hbaseEdge := ((kmswStage_boundary_ids_lt_nextEdge w s).2 q (by
    simp only [List.mem_append]
    tauto))
  have hnowEdge := ((kmswStage_boundary_ids_lt_nextEdge w (s + j)).2 q (by
    simp only [List.mem_append]
    tauto))
  have hstable := edge_endpoints_eq w hbaseEdge
  have hnow := edge_endpoints_eq w hnowEdge
  have hend := (kmswStage_endpoints_lt_nextVertex w s q hbaseEdge).2
  calc
    (kmswStage w (s + j)).east q = edgeEast w q := hnow.2
    _ = (kmswStage w s).east q := hstable.2.symm
    _ < (kmswStage w s).nextVertex := hend

private theorem windowVertexSeamAt_west_old (w : ℕ → Fin 3) (s j q : ℕ)
    (hq : q ∈ (kmswWindowPatchData w s j).A) :
    (kmswStage w (s + j)).west q < (kmswStage w s).nextVertex := by
  have hrel := kmswWindowPatchData_rel w s j
  have hbaseMem : q ∈ (kmswStage w s).UL := by
    have hdrop : q ∈ (kmswStage w s).UL.dropLast := by
      rw [hrel.left_residual]
      simp only [List.mem_append]
      exact Or.inl hq
    exact List.dropLast_subset _ hdrop
  have hnowMem : q ∈ (kmswStage w (s + j)).UL := by
    rw [hrel.ul]
    simp only [List.mem_append]
    exact Or.inl hq
  have hbaseEdge := ((kmswStage_boundary_ids_lt_nextEdge w s).2 q (by
    simp only [List.mem_append]
    tauto))
  have hnowEdge := ((kmswStage_boundary_ids_lt_nextEdge w (s + j)).2 q (by
    simp only [List.mem_append]
    tauto))
  have hstable := edge_endpoints_eq w hbaseEdge
  have hnow := edge_endpoints_eq w hnowEdge
  have hend := (kmswStage_endpoints_lt_nextVertex w s q hbaseEdge).1
  calc
    (kmswStage w (s + j)).west q = edgeWest w q := hnow.1
    _ = (kmswStage w s).west q := hstable.1.symm
    _ < (kmswStage w s).nextVertex := hend

private theorem windowVertexSeamMap_lt_start (w : ℕ → Fin 3) (s j : ℕ) :
    ∀ v, v < (kmswStage (fun i => w (s + i)) j).nextVertex →
      (kmswWindowPatchVertexMap w s j v < (kmswStage w s).nextVertex ↔
        (v < 2 ∨ ∃ k < j, windowVertexSeamAt w s k v)) := by
  intro v
  induction j generalizing v with
  | zero =>
      intro halloc
      have hactive := (kmswStage_boundary_ids_lt_nextEdge w s).1
      have hend := kmswStage_endpoints_lt_nextVertex w s
        (kmswStage w s).active hactive
      constructor
      · intro _
        left
        change v < 2 at halloc
        exact halloc
      · rintro (hsmall | ⟨k, hk, _⟩)
        · have hv0 : v = 0 ∨ v = 1 := by omega
          rcases hv0 with hv0 | hv1
          · simpa [kmswWindowPatchVertexMap, hv0] using hend.1
          · simpa [kmswWindowPatchVertexMap, hv1] using hend.2
        · omega
  | succ j ih =>
      refine fun hv => ?_
      let u := fun i => w (s + i)
      let F := kmswStage u j
      let G := kmswStage w (s + j)
      let d := kmswWindowPatchData w s j
      have hGbase : (kmswStage w s).nextVertex ≤ G.nextVertex := by
        exact CutConverse.nextVertex_mono w (by omega)
      have hnext : (kmswStage u (j + 1)).nextVertex ≤ F.nextVertex + 1 := by
        cases hc : kmswCodeStep (w (s + j)) with
        | down =>
          simp [u, F, kmswStage, kmswStep, hc, kmswStepOfStep]
          split <;> simp
        | up => simp [u, F, kmswStage, kmswStep, hc, kmswStepOfStep]
        | left =>
          simp [u, F, kmswStage, kmswStep, hc, kmswStepOfStep]
          split <;> simp [State.addEdge]
      by_cases hold : v < F.nextVertex
      · have hvold : v < F.nextVertex := hold
        have hext := kmswWindowPatchVertexMap_extends w s j v hvold
        have hvj : v < (kmswStage u j).nextVertex := hvold
        rw [hext]
        exact (ih v hvj).trans
          (windowVertexSeamBefore_succ_old w s j v hvold).symm
      · have hnew : v = F.nextVertex := by
          have hvstep : v < F.nextVertex + 1 := by
            calc
              v < (kmswStage u (j + 1)).nextVertex := by simpa only [u] using hv
              _ ≤ F.nextVertex + 1 := hnext
          have hbound : v ≤ F.nextVertex := by omega
          omega
        have hvj : v < (kmswStage u (j + 1)).nextVertex := hv
        have hbefore := windowVertexSeamBefore_succ_new w s j v hnew
        have hseamEquiv :
            (kmswWindowPatchVertexMap w s (j + 1) v < (kmswStage w s).nextVertex) ↔
              windowVertexSeamAt w s j v := by
          cases hc : kmswCodeStep (w (s + j)) with
          | down =>
            cases hu : F.UR with
            | cons e es =>
              have hv' : v < F.nextVertex := by
                simpa [u, F, kmswStage, kmswStep, hc, kmswStepOfStep, hu] using hv
              have : False := by
                rw [hnew] at hv'
                exact Nat.lt_irrefl _ hv'
              exact this.elim
            | nil =>
              cases hb : d.B with
              | nil =>
                have hnot : ¬ windowVertexSeamAt w s j v := by
                  intro hseam
                  rcases hseam with ⟨_, hcase⟩
                  rcases hcase with hdown | hleft
                  · rcases hdown with ⟨_, _, hB⟩
                    have hb' : (kmswWindowPatchData w s j).B = [] := by
                      simpa only [d] using hb
                    rw [hb'] at hB
                    exact hB rfl
                  · simp [hc] at hleft
                have hnew' : v = (kmswStage u j).nextVertex := by
                  simpa only [F] using hnew
                have hvnot' : ¬ v < (kmswStage u j).nextVertex := by
                  intro h
                  rw [hnew'] at h
                  exact Nat.lt_irrefl _ h
                have hvnot : ¬ v < (kmswStage (fun i => w (s + i)) j).nextVertex := by
                  simpa only [u] using hvnot'
                have hu' : (kmswStage (fun i => w (s + i)) j).UR = [] := by
                  simpa only [F] using hu
                have hb' : (kmswWindowPatchData w s j).B = [] := by
                  simpa only [d] using hb
                have hmap : kmswWindowPatchVertexMap w s (j + 1) v = G.nextVertex := by
                  simp only [kmswWindowPatchVertexMap, hc, hu', hb',
                    ite_eq_right hvnot]; rfl
                rw [hmap]
                constructor
                · intro hlt
                  exact False.elim (Nat.not_lt_of_ge hGbase hlt)
                · intro hseam
                  exact False.elim (hnot hseam)
              | cons q qs =>
                have hyes : windowVertexSeamAt w s j v := by
                  simp [windowVertexSeamAt, u, F, d, hnew, hc, hu, hb]
                have hq : q ∈ d.B := by rw [hb]; simp
                have hold' := windowVertexSeamAt_east_old w s j q hq
                have hmapq : kmswWindowPatchVertexMap w s (j + 1) v = G.east q := by
                  simp [kmswWindowPatchVertexMap, u, F, G, d, hnew, hc, hu, hb]
                rw [hmapq]
                exact ⟨fun _ => hyes, fun _ => hold'⟩
          | up =>
            have hnot : ¬ windowVertexSeamAt w s j v := by
              simp [windowVertexSeamAt, hc]
            have hnew' : v = (kmswStage u j).nextVertex := by
              simpa only [F] using hnew
            have hvnot' : ¬ v < (kmswStage u j).nextVertex := by
              intro h
              rw [hnew'] at h
              exact Nat.lt_irrefl _ h
            have hvnot : ¬ v < (kmswStage (fun i => w (s + i)) j).nextVertex := by
              simpa only [u] using hvnot'
            have hmap : kmswWindowPatchVertexMap w s (j + 1) v = G.nextVertex := by
              simp only [kmswWindowPatchVertexMap, hc, ite_eq_right hvnot]; rfl
            rw [hmap]
            constructor
            · intro hlt
              exact False.elim (Nat.not_lt_of_ge hGbase hlt)
            · intro hseam
              exact False.elim (hnot hseam)
          | left =>
            cases hs : F.UL.dropLast.reverse with
            | cons e es =>
              have hv' : v < F.nextVertex := by
                simpa [u, F, kmswStage, kmswStep, hc, kmswStepOfStep, hs,
                  State.addEdge] using hv
              have : False := by
                rw [hnew] at hv'
                exact Nat.lt_irrefl _ hv'
              exact this.elim
            | nil =>
              cases ha : d.A.reverse with
              | nil =>
                have hnot : ¬ windowVertexSeamAt w s j v := by
                  intro hseam
                  rcases hseam with ⟨_, hcase⟩
                  rcases hcase with hdown | hleft
                  · simp [hc] at hdown
                  · rcases hleft with ⟨_, _, hA⟩
                    have ha' : (kmswWindowPatchData w s j).A.reverse = [] := by
                      simpa only [d] using ha
                    rw [ha'] at hA
                    exact hA rfl
                have hnew' : v = (kmswStage u j).nextVertex := by
                  simpa only [F] using hnew
                have hvnot' : ¬ v < (kmswStage u j).nextVertex := by
                  intro h
                  rw [hnew'] at h
                  exact Nat.lt_irrefl _ h
                have hvnot : ¬ v < (kmswStage (fun i => w (s + i)) j).nextVertex := by
                  simpa only [u] using hvnot'
                have hs' : (kmswStage (fun i => w (s + i)) j).UL.dropLast.reverse = [] := by
                  simpa only [F] using hs
                have ha' : (kmswWindowPatchData w s j).A.reverse = [] := by
                  simpa only [d] using ha
                have hmap : kmswWindowPatchVertexMap w s (j + 1) v = G.nextVertex := by
                  simp only [kmswWindowPatchVertexMap, hc, hs', ha',
                    ite_eq_right hvnot]; rfl
                rw [hmap]
                constructor
                · intro hlt
                  exact False.elim (Nat.not_lt_of_ge hGbase hlt)
                · intro hseam
                  exact False.elim (hnot hseam)
              | cons q qs =>
                have hyes : windowVertexSeamAt w s j v := by
                  simp [windowVertexSeamAt, u, F, d, hnew, hc, hs, ha]
                have hq : q ∈ d.A := by
                  have hrev := congrArg List.reverse ha
                  have hA : d.A = qs.reverse ++ [q] := by
                    simpa only [List.reverse_reverse, List.reverse_cons] using hrev
                  rw [hA]
                  simp
                have hold' := windowVertexSeamAt_west_old w s j q hq
                have hmapq : kmswWindowPatchVertexMap w s (j + 1) v = G.west q := by
                  simp [kmswWindowPatchVertexMap, u, F, G, d, hnew, hc, hs, ha]
                rw [hmapq]
                exact ⟨fun _ => hyes, fun _ => hold'⟩
        rw [hseamEquiv, hbefore]

/-- 206–213): exact characterization of the window vertices identified with already-present
global vertices (the seam), toward the cofinal-freshness conjunct of
WholePlaneRotationHypothesis; its identification with the source left boundary of
M_{n,∞} (Lemma 3.10) and the almost-sure discharge are not treated; not the paper result. -/
theorem kmswWindowPatchVertexMap_lt_start_iff_seam
    (w : ℕ → Fin 3) (s j v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) j).nextVertex) :
    kmswWindowPatchVertexMap w s j v < (kmswStage w s).nextVertex ↔
      v < 2 ∨ ∃ k < j, v = (kmswStage (fun i => w (s + i)) k).nextVertex ∧
        ((kmswCodeStep (w (s + k)) = .down ∧
            (kmswStage (fun i => w (s + i)) k).UR = [] ∧
            (kmswWindowPatchData w s k).B ≠ []) ∨
          (kmswCodeStep (w (s + k)) = .left ∧
            (kmswStage (fun i => w (s + i)) k).UL.dropLast.reverse = [] ∧
            (kmswWindowPatchData w s k).A.reverse ≠ [])) := by
  simpa only [windowVertexSeamAt] using
    (windowVertexSeamMap_lt_start (w := w) (s := s) (j := j) v hv)

private theorem freshness_vertex_potential_step (F : State) (c : Fin 3) (n : ℕ)
    (h : n + F.UL.length + 2 * F.UR.length ≤ 4 * F.nextVertex) :
    n + 1 + (kmswStep F c).UL.length + 2 * (kmswStep F c).UR.length ≤
      4 * (kmswStep F c).nextVertex := by
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
    cases hUR : F.UR with
    | nil =>
      have hlen := congrArg List.length hUR
      simp only [List.length_nil] at hlen
      simp only [kmswStepOfStep, hUR, State.addEdge, List.length_append,
        List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUR
      simp only [List.length_cons] at hlen
      simp only [kmswStepOfStep, hUR, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | left =>
    cases hUL : F.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hUL, State.addEdge,
        List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUL
      simp only [List.length_reverse, List.length_dropLast, List.length_cons] at hlen
      simp only [kmswStepOfStep, hUL, State.addEdge, List.length_append,
        List.length_reverse, List.length_cons, List.length_nil]
      omega
  | up =>
    simp only [kmswStepOfStep, State.addEdge, List.length_append,
      List.length_dropLast, List.length_cons, List.length_nil]
    omega

private theorem freshness_vertex_potential (u : ℕ → Fin 3) (n : ℕ) :
    n + (kmswStage u n).UL.length + 2 * (kmswStage u n).UR.length ≤
      4 * (kmswStage u n).nextVertex := by
  induction n with
  | zero =>
    change 1 ≤ 8
    decide
  | succ n ih => exact freshness_vertex_potential_step (kmswStage u n) (u n) n ih

private theorem freshness_vertex_allocated_at (u : ℕ → Fin 3) (v : ℕ) :
    v < (kmswStage u (4 * v + 1)).nextVertex := by
  have h := freshness_vertex_potential u (4 * v + 1)
  omega

/-- Helper toward F4c / the whole-plane KMSW carrier
condition in the run-N' window, transported to the run-N stream using `shiftedStream_shift`;
the source-boundary identification (Lemma 3.10) and almost-sure discharge are not treated;
not the paper result. -/
theorem wholePlaneFresh_iff_windowSeam
    (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') (v : ℕ) :
    let w := shiftedStream W N'
    let s := N' - N
    ¬ wholePlaneFresh W N N' h v ↔
      v < 2 ∨ ∃ k < 4 * v + 1,
        v = (kmswStage (shiftedStream W N) k).nextVertex ∧
          ((kmswCodeStep (shiftedStream W N k) = .down ∧
              (kmswStage (shiftedStream W N) k).UR = [] ∧
              (kmswWindowPatchData w s k).B ≠ []) ∨
            (kmswCodeStep (shiftedStream W N k) = .left ∧
              (kmswStage (shiftedStream W N) k).UL.dropLast.reverse = [] ∧
              (kmswWindowPatchData w s k).A.reverse ≠ [])) := by
  let w := shiftedStream W N'
  let s := N' - N
  let u := fun i => w (s + i)
  have hu : (fun i => shiftedStream W N' ((N' - N) + i)) =
      shiftedStream W N := shiftedStream_shift W N N' h
  have halloc := freshness_vertex_allocated_at u v
  have hmap := kmswWindowVertexMapInf_eq_stage w s (4 * v + 1) v halloc
  have hchar := kmswWindowPatchVertexMap_lt_start_iff_seam w s
    (4 * v + 1) v halloc
  have hchar' := hchar
  simp only [w, s] at hchar'
  simp only [hu] at hchar'
  have hcharCode (k : ℕ) : shiftedStream W N' ((N' - N) + k) =
      shiftedStream W N k := congrFun hu k
  simp only [hcharCode] at hchar'
  change ¬ ((kmswStage w s).nextVertex ≤ kmswWindowVertexMapInf w s v) ↔ _
  rw [hmap]
  constructor
  · intro hnot
    exact hchar'.mp (Nat.lt_of_not_ge hnot)
  · intro hseam
    have hlt := hchar'.mpr hseam
    exact Nat.not_le_of_gt hlt

end DirectedDistances.KMSW
