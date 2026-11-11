/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWBdy

/-! Supporting lemmas for paper labels `lem-kmsw-bdy` (see CORRESPONDENCE.md). -/

/-! # Indexed activation and creation times for KMSW boundary records

Add the indexed “added at the k-th record time” clauses for (iii) and (iv) of
completed paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped Classical



@[expose] noncomputable def recUL (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun m => decide
    (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j))

/-- The increasing list of positive upper-right creation times in clause (iv) -/
@[expose] noncomputable def recUR (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun m => decide
    (0 < m ∧ m ≤ n ∧ ∀ j, m ≤ j → j ≤ n → R w (m - 1) + 1 ≤ R w j))





theorem kmsw_bdy_upper_left_indexed_record (w : ℕ → Fin 3) (n : ℕ) :
    ∀ k, ∀ hk : k < (recUL w n).length,
    let m := (recUL w n)[k]'hk
    (kmswStage w n).UL.length = (recUL w n).length ∧
    ∃ h : k < (kmswStage w n).UL.length,
      (kmswStage w n).UL[k]'h = act w m ∧
      (kmswStage w m).present (act w m) = true ∧
      (m = 0 → act w m = 0) ∧
      (0 < m → ¬ (act w m < (kmswStage w (m - 1)).nextEdge ∧
        (kmswStage w (m - 1)).present (act w m) = true)) ∧
      (kmswStage w n).present (act w m) = true := by
  intro k hk
  let p : ℕ → Bool := fun r => decide
    (∀ j, r < j → j ≤ n → L w r + 1 ≤ L w j)
  let m : ℕ := (recUL w n)[k]'hk
  have hmem : m ∈ recUL w n := List.getElem_mem hk
  have hmem' : m ∈ (List.range (n + 1)).filter p := by
    simp [recUL, p, m]
  obtain ⟨hrange, hp⟩ := List.mem_filter.mp hmem'
  have hmn : m ≤ n := by
    simp only [List.mem_range] at hrange
    omega
  have hrec : ∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j := of_decide_eq_true hp
  obtain ⟨hprefix, hprefixget⟩ :=
    kmsw_bdy_range_filter_getElem_at_rank (p := p) hmn hp
  have hprefixget' :
      (recUL w n)[((List.range m).filter p).length]'hprefix = m := by
    simpa [recUL, p] using hprefixget
  have hgetm : (recUL w n)[k]'hk = m := rfl
  have hnodup : (recUL w n).Nodup := by
    simpa [recUL, p] using (List.Nodup.filter p List.nodup_range)
  have hrank : ((List.range m).filter p).length = k := by
    exact hnodup.getElem_inj_iff.mp (hprefixget'.trans hgetm.symm)
  have hlist : (kmswStage w n).UL = (recUL w n).map (act w) := by
    simpa [recUL] using (kmsw_bdy_source_ordered_boundary_lists w n).1
  have hlen : (kmswStage w n).UL.length = (recUL w n).length := by
    rw [hlist, List.length_map]
  obtain ⟨hbound, hedge, hpresent, hzero, hactivation⟩ :=
    kmsw_bdy_upper_left_ranked_record w n m hmn hrec
  have hboundk : k < (kmswStage w n).UL.length := by
    rw [hlen]
    exact hk
  have hedgeK : (kmswStage w n).UL[k]'hboundk = act w m := by
    simpa only [← hrank] using hedge
  have hmemUL : act w m ∈ (kmswStage w n).UL := by
    rw [← hedgeK]
    exact List.getElem_mem hboundk
  have hpresentN : (kmswStage w n).present (act w m) = true :=
    (kmswStage_status w n).2.1 _ hmemUL
  exact ⟨hlen, hboundk, hedgeK, hpresent, (fun hm0 => (hzero hm0).1),
    hactivation, hpresentN⟩




theorem kmsw_bdy_upper_right_indexed_record (w : ℕ → Fin 3) (n : ℕ) :
    ∀ k, ∀ hk : k < (recUR w n).length,
    let m := (recUR w n)[k]'hk
    ((kmswStage w n).UR.reverse).length = (recUR w n).length ∧
    ∃ h : k < (kmswStage w n).UR.reverse.length,
      (kmswStage w n).UR.reverse[k]'h = kmswURCreatedEdge w m ∧
      (kmswStage w (m - 1)).nextEdge ≤ kmswURCreatedEdge w m ∧
      kmswURCreatedEdge w m < (kmswStage w m).nextEdge ∧
      (kmswStage w n).present (kmswURCreatedEdge w m) = false := by
  intro k hk
  let p : ℕ → Bool := fun r => decide
    (0 < r ∧ r ≤ n ∧ ∀ j, r ≤ j → j ≤ n → R w (r - 1) + 1 ≤ R w j)
  let m : ℕ := (recUR w n)[k]'hk
  have hmem : m ∈ recUR w n := List.getElem_mem hk
  have hmem' : m ∈ (List.range (n + 1)).filter p := by
    simp [recUR, p, m]
  obtain ⟨hrange, hp⟩ := List.mem_filter.mp hmem'
  have hmn : m ≤ n := by
    simp only [List.mem_range] at hrange
    omega
  have hp' : 0 < m ∧ m ≤ n ∧
      ∀ j, m ≤ j → j ≤ n → R w (m - 1) + 1 ≤ R w j := of_decide_eq_true hp
  have hm : 0 < m := hp'.1
  have hrec := hp'.2.2
  obtain ⟨hprefix, hprefixget⟩ :=
    kmsw_bdy_range_filter_getElem_at_rank (p := p) hmn hp
  have hprefixget' :
      (recUR w n)[((List.range m).filter p).length]'hprefix = m := by
    simpa [recUR, p] using hprefixget
  have hgetm : (recUR w n)[k]'hk = m := rfl
  have hnodup : (recUR w n).Nodup := by
    simpa [recUR, p] using (List.Nodup.filter p List.nodup_range)
  have hrank : ((List.range m).filter p).length = k := by
    exact hnodup.getElem_inj_iff.mp (hprefixget'.trans hgetm.symm)
  have hlist : (kmswStage w n).UR.reverse = (recUR w n).map (kmswURCreatedEdge w) := by
    simpa [recUR] using (kmsw_bdy_source_ordered_boundary_lists w n).2.2.2
  have hlen : ((kmswStage w n).UR.reverse).length = (recUR w n).length := by
    rw [hlist, List.length_map]
  obtain ⟨hbound, hedge, _, hallocL, hallocR, hmissing⟩ :=
    kmsw_bdy_upper_right_ranked_record w n m hm hmn hrec
  have hboundk : k < (kmswStage w n).UR.reverse.length := by
    rw [hlen]
    exact hk
  have hedgeK : (kmswStage w n).UR.reverse[k]'hboundk = kmswURCreatedEdge w m := by
    simpa only [← hrank] using hedge
  exact ⟨hlen, hboundk, hedgeK, hallocL, hallocR, hmissing⟩

/-- The indexed “added at the k-th record time” clauses for (iii) and (iv),
bundled with the existing candidate for `lem-kmsw-bdy` -/
theorem kmsw_bdy_candidate_full (w : ℕ → Fin 3) (n : ℕ) :
    ((∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minL w n),
      ∃ hhit : ∃ t, L w t = -(k : ℤ),
        Nat.find hhit ≤ n ∧
        ∃ h : k - 1 < ((kmswStage w n).LL.reverse).length,
          ((kmswStage w n).LL.reverse)[k - 1]'h =
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          (kmswStage w (Nat.find hhit - 1)).nextEdge ≤
              kmswLLCreatedEdge w (Nat.find hhit) ∧
          kmswLLCreatedEdge w (Nat.find hhit) <
              (kmswStage w (Nat.find hhit)).nextEdge ∧
          (kmswStage w (Nat.find hhit)).present
              (kmswLLCreatedEdge w (Nat.find hhit)) = false ∧
          (kmswStage w (Nat.find hhit)).west (act w (Nat.find hhit)) =
              (kmswStage w (Nat.find hhit)).west
                (kmswLLCreatedEdge w (Nat.find hhit)) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).west (act w m) =
                (kmswStage w (Nat.find hhit)).west
                  (kmswLLCreatedEdge w (Nat.find hhit)) ↔
              L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j)) ∧
          IsLeast {m | (kmswStage w m).west (act w m) =
            (kmswStage w (Nat.find hhit)).west
              (kmswLLCreatedEdge w (Nat.find hhit))} (Nat.find hhit)) ∧
    (∀ (k : ℕ), ∀ (_hk : 1 ≤ k), ∀ (_hkmin : (k : ℤ) ≤ -minR w n),
      ∃ hhit : ∃ t, R w t = -(k : ℤ),
        Nat.find hhit ≤ n ∧
        (kmswStage w n).LR[0]? = some 0 ∧
        ∃ h : k < (kmswStage w n).LR.length,
          (kmswStage w n).LR[k]'h = act w (Nat.find hhit) ∧
          (kmswStage w (Nat.find hhit)).present (act w (Nat.find hhit)) = true ∧
          (0 < Nat.find hhit →
            ¬ ((act w (Nat.find hhit) <
                (kmswStage w (Nat.find hhit - 1)).nextEdge) ∧
              (kmswStage w (Nat.find hhit - 1)).present
                (act w (Nat.find hhit)) = true)) ∧
          (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) =
            (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ∧
          (∀ m, m ≤ n →
            ((kmswStage w m).east (act w m) =
                (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ↔
              R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j)) ∧
          IsLeast {m | (kmswStage w m).east (act w m) =
            (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit))}
            (Nat.find hhit)) ∧
    ((kmswStage w n).UL = (recUL w n).map (act w)) ∧
    (∀ m' m, m' ≤ m → m ≤ n → L w m' = L w m →
      (∀ j, m' ≤ j → j ≤ m → L w m' ≤ L w j) →
      (kmswStage w m).west (act w m') = (kmswStage w m).west (act w m)) ∧
    (((kmswStage w n).UR).reverse = (recUR w n).map (kmswURCreatedEdge w)) ∧
    ((Finset.card (kmswStageULDartsFinset w n) : ℤ) =
        L w n - minL w n + 1) ∧
      ((Finset.card (kmswStageURDartsFinset w n) : ℤ) = R w n - minR w n) ∧
      ((Finset.card (kmswStageLLDartsFinset w n) : ℤ) = -minL w n) ∧
    ((Finset.card (kmswStageLRDartsFinset w n) : ℤ) = -minR w n + 1)) ∧
    (∀ k, ∀ hk : k < (recUL w n).length,
      let m := (recUL w n)[k]'hk
      (kmswStage w n).UL.length = (recUL w n).length ∧
      ∃ h : k < (kmswStage w n).UL.length,
        (kmswStage w n).UL[k]'h = act w m ∧
        (kmswStage w m).present (act w m) = true ∧
        (m = 0 → act w m = 0) ∧
        (0 < m → ¬ (act w m < (kmswStage w (m - 1)).nextEdge ∧
          (kmswStage w (m - 1)).present (act w m) = true)) ∧
        (kmswStage w n).present (act w m) = true) ∧
    (∀ k, ∀ hk : k < (recUR w n).length,
      let m := (recUR w n)[k]'hk
      ((kmswStage w n).UR.reverse).length = (recUR w n).length ∧
      ∃ h : k < (kmswStage w n).UR.reverse.length,
        (kmswStage w n).UR.reverse[k]'h = kmswURCreatedEdge w m ∧
        (kmswStage w (m - 1)).nextEdge ≤ kmswURCreatedEdge w m ∧
        kmswURCreatedEdge w m < (kmswStage w m).nextEdge ∧
        (kmswStage w n).present (kmswURCreatedEdge w m) = false) := by
  refine ⟨?_, kmsw_bdy_upper_left_indexed_record w n,
    kmsw_bdy_upper_right_indexed_record w n⟩
  simpa only [recUL, recUR] using kmsw_bdy_candidate w n

end DirectedDistances.PaperProofs.Section3
