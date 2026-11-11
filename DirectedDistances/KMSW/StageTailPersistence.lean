module

public import DirectedDistances.KMSW.StageTailHeightBound

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW




private theorem west_map_stable (w : ℕ → Fin 3) (n : ℕ) (es : List ℕ)
    (hes : ∀ e ∈ es, e ∈ (kmswStage w n).UL) :
    es.map (kmswStage w (n + 1)).west = es.map (kmswStage w n).west := by
  apply List.map_congr_left
  intro e he
  have hb := (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (hes e he))))
  exact (kmswStage_endpoints_stable w (Nat.le_succ n) hb).1





private theorem prefix_step (w : ℕ → Fin 3) (n q : ℕ)
    (hmin : minL w (n + 1) = minL w n)
    (hq : (q : ℤ) ≤ L w n - minL w n)
    (hnext : (q : ℤ) ≤ L w (n + 1) - minL w (n + 1)) :
    (kmswStage w (n + 1)).UL.take q = (kmswStage w n).UL.take q ∧
      ((kmswStage w (n + 1)).UL.map (kmswStage w (n + 1)).west).take (q + 1) =
        ((kmswStage w n).UL.map (kmswStage w n).west).take (q + 1) := by
  have hlen := kmswStage_UL_length_height w n
  have hL := kmswL_succ w n
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  by_cases h0 : w n = 0
  · have hlevel : L w (n + 1) = L w n - 1 := by
      simpa [h0, sub_eq_add_neg] using hL
    have hsize : q + 1 ≤ xs.length := by
      rw [hxs, List.length_append, List.length_singleton] at hlen
      omega
    cases hs : xs.reverse with
    | nil =>
      have := congrArg List.length hs
      simp only [List.length_reverse, List.length_nil] at this
      omega
    | cons e es =>
      have hxs' : xs = es.reverse ++ [e] := by
        have hh := congrArg List.reverse hs
        simpa only [List.reverse_reverse, List.reverse_cons] using hh
      have hdrop : (kmswStage w n).UL.dropLast.reverse = e :: es := by
        simp only [hxs, List.dropLast_concat, hs]
      have hUL : (kmswStage w (n + 1)).UL =
          es.reverse ++ [(kmswStage w n).nextEdge] := by
        simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep, hdrop,
          State.addEdge]
      have hwest := (kmswStage_left_UL_cons_endpoints w n e es h0 hdrop).1
      have hactive : (kmswStage w (n + 1)).active = (kmswStage w n).nextEdge := by
        simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep, hdrop,
          State.addEdge]
      rw [hactive] at hwest
      have hmap := west_map_stable w n es.reverse (by
        intro f hf
        rw [hxs, hxs']
        exact List.mem_append_left _ (List.mem_append_left _ hf))
      have hqes : q ≤ es.length := by
        rw [hxs', List.length_append, List.length_reverse, List.length_singleton] at hsize
        omega
      constructor
      · rw [hUL, hxs, hxs', List.append_assoc]
        rw [List.take_append_of_le_length (by simpa using hqes)]
        rw [List.take_append_of_le_length (by simpa using hqes)]
      · rw [hUL, List.map_append, List.map_singleton, hmap, hwest]
        rw [hxs, hxs', List.map_append, List.map_append, List.map_singleton]
        exact (List.take_append_of_le_length (by
          simp only [List.length_append, List.length_map, List.length_reverse,
            List.length_singleton]
          omega)).symm
  · by_cases h1 : w n = 1
    · have hUL : (kmswStage w (n + 1)).UL = xs ++ [(kmswStage w n).nextEdge] := by
        simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, hxs,
          State.addEdge]
      have hactive : (kmswStage w (n + 1)).active = (kmswStage w n).nextEdge := by
        simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
      have hwest := (kmswStage_up_active_endpoints w n h1).1
      rw [hactive] at hwest
      have hmap := west_map_stable w n xs (by
        intro e he
        rw [hxs]
        exact List.mem_append_left _ he)
      have hqx : q ≤ xs.length := by
        rw [hxs, List.length_append, List.length_singleton] at hlen
        omega
      constructor
      · rw [hUL, hxs, List.take_append_of_le_length hqx,
          List.take_append_of_le_length hqx]
      · rw [hUL, hxs, List.map_append, List.map_append, List.map_singleton,
          List.map_singleton, hmap, hwest]
    · have h2 : w n = 2 := by
        apply Fin.ext
        have := (w n).isLt
        have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
        have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
        omega
      have hUL : ∃ e, (kmswStage w (n + 1)).UL = (kmswStage w n).UL ++ [e] := by
        cases hs : (kmswStage w n).UR with
        | nil =>
          exact ⟨(kmswStage w n).nextEdge, by
            simp [kmswStage, kmswStep, kmswCodeStep, h2,
            kmswStepOfStep, hs, State.addEdge]⟩
        | cons e es =>
          exact ⟨e, by simp [kmswStage, kmswStep, kmswCodeStep, h2,
            kmswStepOfStep, hs]⟩
      obtain ⟨e, he⟩ := hUL
      have hmap := west_map_stable w n (kmswStage w n).UL (by
        intro f hf
        exact hf)
      have hbound : q + 1 ≤ (kmswStage w n).UL.length := by omega
      constructor
      · rw [he, List.take_append_of_le_length (by omega)]
      · rw [he, List.map_append, List.map_singleton, hmap,
          List.take_append_of_le_length (by simpa only [List.length_map] using hbound)]





theorem kmswStage_UL_prefix_persistence (w : ℕ → Fin 3) {N m : ℕ} (hNm : N ≤ m)
    (hmin : minL w m = minL w N) (q : ℕ)
    (hq : ∀ k, N ≤ k → k ≤ m → (q : ℤ) ≤ L w k - minL w N) :
    (kmswStage w m).UL.take q = (kmswStage w N).UL.take q ∧
      ((((kmswStage w m).UL.map (kmswStage w m).west) ++
        [(kmswStage w m).east (kmswStage w m).active]).take (q + 1)) =
      ((((kmswStage w N).UL.map (kmswStage w N).west) ++
        [(kmswStage w N).east (kmswStage w N).active]).take (q + 1)) := by
  have hmins (k : ℕ) (hNk : N ≤ k) (hkm : k ≤ m) : minL w k = minL w N := by
    apply kmswStage_minL_eq_of_interval_lower_bound w hNk
    intro j hNj hjk
    have h := runningMin_le (L w) m j (hjk.trans hkm)
    change minL w m ≤ L w j at h
    omega
  have hp : ∀ n, N ≤ n → n ≤ m →
      (kmswStage w n).UL.take q = (kmswStage w N).UL.take q ∧
        ((kmswStage w n).UL.map (kmswStage w n).west).take (q + 1) =
          ((kmswStage w N).UL.map (kmswStage w N).west).take (q + 1) := by
    intro n hNn
    induction n, hNn using Nat.le_induction with
    | base => intro _; exact ⟨rfl, rfl⟩
    | succ n hNn ih =>
      intro hnm
      have hi := ih (by omega)
      have hmn := hmins n hNn (by omega)
      have hmn' := hmins (n + 1) (by omega) hnm
      have hs := prefix_step w n q (hmn'.trans hmn.symm)
        (by rw [hmn]; exact hq n hNn (by omega))
        (by rw [hmn']; exact hq (n + 1) (by omega) hnm)
      exact ⟨hs.1.trans hi.1, hs.2.trans hi.2⟩
  have hbound (n : ℕ) (hNn : N ≤ n) (hnm : n ≤ m) :
      q + 1 ≤ ((kmswStage w n).UL.map (kmswStage w n).west).length := by
    rw [List.length_map, kmswStage_UL_length_height, hmins n hNn hnm]
    have := hq n hNn hnm
    omega
  refine ⟨(hp m hNm le_rfl).1, ?_⟩
  rw [List.take_append_of_le_length (hbound m hNm le_rfl),
    List.take_append_of_le_length (hbound N le_rfl hNm)]
  exact (hp m hNm le_rfl).2




theorem kmswStage_UL_vertex_list_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (((kmswStage w n).UL.map (kmswStage w n).west) ++
      [(kmswStage w n).east (kmswStage w n).active]).Nodup := by
  have h := CutConverse.ul_path_vertices_nodup w n
  apply List.nodup_reverse.mp
  simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.map_reverse, CutConverse.westStack,
    act] using h





theorem kmswStage_old_tail_index_lower_bound (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N ≤ m) (hmin : minL w m = minL w N) (q i : ℕ)
    (hq : ∀ k, N ≤ k → k ≤ m → (q : ℤ) ≤ L w k - minL w N)
    (hi : (((kmswStage w N).UL.map (kmswStage w N).west) ++
      [(kmswStage w N).east (kmswStage w N).active])[i]? =
        some ((kmswStage w m).west (kmswStage w m).active)) : q ≤ i := by
  by_contra hbad
  have hiq : i < q + 1 := by omega
  have hp := (kmswStage_UL_prefix_persistence w hNm hmin q hq).2
  have heq := congrArg (fun xs : List ℕ => xs[i]?) hp
  rw [List.getElem?_take_of_lt hiq, List.getElem?_take_of_lt hiq, hi] at heq
  have hcurrent := kmswStage_active_tail_UL_height_index w m
  have hlen := kmswStage_UL_length_height w m
  have hibound : i < (((kmswStage w m).UL.map (kmswStage w m).west) ++
      [(kmswStage w m).east (kmswStage w m).active]).length := by
    simp only [List.length_append, List.length_map, List.length_singleton]
    have h := hq m hNm le_rfl
    omega
  have hindices := (List.Nodup.getElem?_inj hibound
    (kmswStage_UL_vertex_list_nodup w m)).mp (heq.trans hcurrent.symm)
  have h := hq m hNm le_rfl
  omega




theorem kmswStage_tail_UL_suffix (w : ℕ → Fin 3) {N m : ℕ} (hNm : N ≤ m)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex)
    (hUR : (kmswStage w N).UR = []) (hmin : minL w m = minL w N) (q : ℕ)
    (hq : ∀ k, N ≤ k → k ≤ m → (q : ℤ) ≤ L w k - minL w N) :
    ∃ i, q ≤ i ∧
      (((kmswStage w N).UL.map (kmswStage w N).west) ++
        [(kmswStage w N).east (kmswStage w N).active])[i]? =
          some ((kmswStage w m).west (kmswStage w m).active) := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp
    (kmswStage_tail_mem_UL_vertex_list w hNm hOld hUR)
  have hget := (List.getElem?_eq_getElem hi).trans (congrArg some he)
  exact ⟨i, kmswStage_old_tail_index_lower_bound w hNm hmin q i hq hget, hget⟩




theorem kmswStage_tail_UL_quadrant_suffix (w : ℕ → Fin 3) {N m : ℕ} (hNm : N ≤ m)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex)
    (hUR : (kmswStage w N).UR = [])
    (hL : ∀ k, k ≤ m → 0 ≤ L w k) (c : ℕ)
    (hc : ∀ k, N ≤ k → k ≤ m → (c : ℤ) ≤ L w k) :
    ∃ i, c ≤ i ∧
      (((kmswStage w N).UL.map (kmswStage w N).west) ++
        [(kmswStage w N).east (kmswStage w N).active])[i]? =
          some ((kmswStage w m).west (kmswStage w m).active) := by
  have hzero (n : ℕ) (hn : n ≤ m) : minL w n = 0 := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
    have hle := runningMin_le (L w) n 0 (Nat.zero_le _)
    have hz : L w 0 = 0 := by simp only [L, Finset.range_zero, Finset.sum_empty]
    change minL w n = L w j at he
    change minL w n ≤ L w 0 at hle
    have hnonneg := hL j (hj.trans hn)
    omega
  apply kmswStage_tail_UL_suffix w hNm hOld hUR
    ((hzero m le_rfl).trans (hzero N hNm).symm) c
  intro k hNk hkm
  rw [hzero N hNm, sub_zero]
  exact hc k hNk hkm





private theorem interval_min_cutoff (w : ℕ → Fin 3) {N m : ℕ} (hNm : N ≤ m)
    (hmin : minL w m = minL w N) :
    ∀ k, N ≤ k → k ≤ m →
      ((runningMin (fun j => L w (N + j)) (m - N) - minL w N).toNat : ℤ) ≤
        L w k - minL w N := by
  obtain ⟨j, hj, he⟩ := runningMin_attained (fun j => L w (N + j)) (m - N)
  have hglobal := runningMin_le (L w) m (N + j) (by omega)
  change minL w m ≤ L w (N + j) at hglobal
  intro k hNk hkm
  have hlocal := runningMin_le (fun j => L w (N + j)) (m - N) (k - N) (by omega)
  have hk : N + (k - N) = k := by omega
  rw [hk] at hlocal
  omega





theorem kmswStage_UL_interval_min_persistence (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N ≤ m) (hmin : minL w m = minL w N) :
    let mu := runningMin (fun j => L w (N + j)) (m - N)
    let q := (mu - minL w N).toNat
    ∀ n, N ≤ n → n ≤ m →
      (kmswStage w n).UL.take q = (kmswStage w N).UL.take q ∧
        ((((kmswStage w n).UL.map (kmswStage w n).west) ++
          [(kmswStage w n).east (kmswStage w n).active]).take (q + 1)) =
        ((((kmswStage w N).UL.map (kmswStage w N).west) ++
          [(kmswStage w N).east (kmswStage w N).active]).take (q + 1)) := by
  dsimp only
  intro n hNn hnm
  have hminn : minL w n = minL w N := by
    apply kmswStage_minL_eq_of_interval_lower_bound w hNn
    intro k hNk hkn
    have h := runningMin_le (L w) m k (hkn.trans hnm)
    change minL w m ≤ L w k at h
    omega
  apply kmswStage_UL_prefix_persistence w hNn hminn
  intro k hNk hkn
  exact interval_min_cutoff w hNm hmin k hNk (hkn.trans hnm)





theorem kmswStage_tail_UL_interval_min_suffix (w : ℕ → Fin 3) {N m : ℕ}
    (hNm : N ≤ m)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex)
    (hUR : (kmswStage w N).UR = []) (hmin : minL w m = minL w N) :
    let mu := runningMin (fun j => L w (N + j)) (m - N)
    ∃ i, (mu - minL w N).toNat ≤ i ∧
      (((kmswStage w N).UL.map (kmswStage w N).west) ++
        [(kmswStage w N).east (kmswStage w N).active])[i]? =
          some ((kmswStage w m).west (kmswStage w m).active) := by
  dsimp only
  exact kmswStage_tail_UL_suffix w hNm hOld hUR hmin _
    (interval_min_cutoff w hNm hmin)

end DirectedDistances.KMSW
