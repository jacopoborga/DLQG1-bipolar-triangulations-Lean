module

public import DirectedDistances.KMSW.KMSWLeftWalkCut
public import DirectedDistances.KMSW.BoundaryDynamics
import DirectedDistances.KMSW.BoundaryRecordsUL
import DirectedDistances.KMSW.StoppedStageMap

/-! Supporting lemmas for paper labels `lem-kmsw-left` (see CORRESPONDENCE.md). -/

/-! # Direct KMSW run on a left walk

430–433`): stage shape of the direct KMSW run on `Z^bc_ℓ`; procedure reading -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem kmswLeft_runningMinR_zero (w : ℕ → Fin 3) (m : ℕ)
    (hR : ∀ k ≤ m, 0 ≤ R w k) : minR w m = 0 := by
  induction m with
  | zero => simp [minR, runningMin, R]
  | succ m ih =>
    rw [show minR w (m + 1) = min (minR w m) (R w (m + 1)) by rfl,
      ih (fun k hk => hR k (by omega))]
    exact min_eq_left (hR (m + 1) le_rfl)

private theorem kmswLeftRun_LR_singleton (w : ℕ → Fin 3) (m : ℕ)
    (hR : ∀ k ≤ m, 0 ≤ R w k) : (kmswStage w m).LR = [0] := by
  have hfilter : (List.range (m + 1)).filter
      (fun j => decide (∀ k, k < j → R w j < R w k)) = [0] := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.filter_append,
        ih (fun k hk => hR k (by omega))]
      have hnew : ¬ (∀ k, k < m + 1 → R w (m + 1) < R w k) := by
        intro hstrict
        have h0 := hstrict 0 (by omega)
        have hzero : R w 0 = 0 := by simp [R]
        have hnonneg := hR (m + 1) le_rfl
        omega
      simp only [List.filter_cons, List.filter_nil]
      rw [decide_eq_false_iff_not.mpr hnew]
      simp
  rw [kmswStage_LR_eq, hfilter]
  simp [act, kmswStage, kmswInit]

/-- Stage lengths at every prefix of a quadrant walk, with coordinates
integrated from `(ℓ - 1, 0)`. The horizontal lengths retain the running
minimum explicitly. Helper toward `lem-kmsw-left` -/
theorem kmswLeftRun_quadrant_prefix (ℓ n m : ℕ) (w : ℕ → Fin 3)
    (hm : m ≤ n)
    (hquad : ∀ k ≤ n,
      0 ≤ (ℓ : ℤ) - 1 + L w k ∧ 0 ≤ R w k) :
    ((kmswStage w m).UR.length : ℤ) = R w m ∧
      (kmswStage w m).LR = [0] ∧
      ((kmswStage w m).UL.length : ℤ) = L w m - minL w m + 1 ∧
      ((kmswStage w m).LL.length : ℤ) = -minL w m := by
  have hminR : minR w m = 0 :=
    kmswLeft_runningMinR_zero w m (fun k hk => (hquad k (by omega)).2)
  have hUR := kmswStage_UR_length w m
  have hLR := kmswLeftRun_LR_singleton w m (fun k hk => (hquad k (by omega)).2)
  have hUL := kmswStage_UL_length w m
  have hLL := kmswStage_LL_length w m
  constructor
  · rw [hUR, hminR]
    ring
  constructor
  · exact hLR
  exact ⟨hUL, hLL⟩

/-- The allocation counter is the initial edge plus the elapsed steps and the
currently missing upper-right and lower-left boundary edges. Helper toward -/
theorem kmswLeftRun_nextEdge_count (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).nextEdge =
      n + (kmswStage w n).UR.length + (kmswStage w n).LL.length + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStep (kmswStage w n) (w n)).nextEdge =
      n + 1 + (kmswStep (kmswStage w n) (w n)).UR.length +
        (kmswStep (kmswStage w n) (w n)).LL.length + 1
    unfold kmswStep
    cases kmswCodeStep (w n) with
    | down =>
      cases hs : (kmswStage w n).UR <;>
        simp only [kmswStepOfStep, hs, State.addEdge, List.length_cons,
          List.length_nil] at * <;> omega
    | left =>
      cases hs : (kmswStage w n).UL.dropLast.reverse <;>
        simp only [kmswStepOfStep, hs, State.addEdge, List.length_cons] at * <;> omega
    | up =>
      simp only [kmswStepOfStep, State.addEdge, List.length_cons]
      omega

private theorem kmswLeft_admissible_coordinates (ℓ n : ℕ)
    (c : Fin n → Fin 3) (hc : KMSWLeftWalkAdmissible ℓ n c) :
    (∀ k ≤ n, 0 ≤ (ℓ : ℤ) - 1 + L (finiteCodeExtend (n := n + 1) c) k ∧
      0 ≤ R (finiteCodeExtend (n := n + 1) c) k) ∧
      L (finiteCodeExtend (n := n + 1) c) n = 1 - (ℓ : ℤ) ∧
      R (finiteCodeExtend (n := n + 1) c) n = 0 := by
  let w : ℕ → Fin 3 := finiteCodeExtend (n := n + 1) c
  have hcc := hc
  change (((ℓ : ℤ) - 1, 0) + integrateCodes w n = (0, 0)) ∧
    ∀ k ∈ Finset.range (n + 1),
      0 ≤ (((ℓ : ℤ) - 1, 0) + integrateCodes w k).1 ∧
      0 ≤ (((ℓ : ℤ) - 1, 0) + integrateCodes w k).2 at hcc
  constructor
  · intro k hk
    have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have h := hcc.2 k hmem
    have hL : L w k = (integrateCodes w k).1 := kmsw_L_eq w k
    have hR : R w k = (integrateCodes w k).2 := kmsw_R_eq w k
    constructor
    · have hh : 0 ≤ (ℓ : ℤ) - 1 + (integrateCodes w k).1 := by
        simpa only [Prod.fst_add] using h.1
      simpa only [← hL] using hh
    · have hh : 0 ≤ (integrateCodes w k).2 := by
        simpa only [Prod.snd_add, zero_add] using h.2
      simpa only [← hR] using hh
  · have hfst := congrArg Prod.fst hcc.1
    have hsnd := congrArg Prod.snd hcc.1
    have hL : L w n = (integrateCodes w n).1 := kmsw_L_eq w n
    have hR : R w n = (integrateCodes w n).2 := kmsw_R_eq w n
    have hfst' : (ℓ : ℤ) - 1 + L w n = 0 := by
      simpa only [Prod.fst_add, ← hL] using hfst
    have hsnd' : R w n = 0 := by
      simpa only [Prod.snd_add, zero_add, ← hR] using hsnd
    constructor
    · linear_combination hfst'
    · exact hsnd'

/-- The direct KMSW stage at the end of an admissible left walk has the
terminal boundary lengths prescribed by its source and sink. Helper toward -/
theorem kmswLeftRun_admissible_lengths (ℓ n : ℕ) (c : Fin n → Fin 3)
    (hc : KMSWLeftWalkAdmissible ℓ n c) :
    let w := finiteCodeExtend (n := n + 1) c
    (kmswStage w n).UR.length = 0 ∧
      (kmswStage w n).LR = [0] ∧
      (kmswStage w n).LL.length = ℓ - 1 ∧
      (kmswStage w n).UL.length = 1 ∧
      (kmswStage w n).nextEdge = n + ℓ := by
  let w : ℕ → Fin 3 := finiteCodeExtend (n := n + 1) c
  obtain ⟨hquad', hLend', hRend'⟩ := kmswLeft_admissible_coordinates ℓ n c hc
  have hquad : ∀ k ≤ n, 0 ≤ (ℓ : ℤ) - 1 + L w k ∧ 0 ≤ R w k := by
    simpa only [w] using hquad'
  have hLend : L w n = 1 - (ℓ : ℤ) := by simpa only [w] using hLend'
  have hRend : R w n = 0 := by simpa only [w] using hRend'
  have hℓ : 1 ≤ ℓ := by
    have hzero := (hquad 0 (by omega)).1
    simp only [L, Finset.range_zero, Finset.sum_empty, add_zero] at hzero
    omega
  have hminR : minR w n = 0 :=
    kmswLeft_runningMinR_zero w n (fun k hk => (hquad k hk).2)
  have hminLlow : (1 : ℤ) - ℓ ≤ minL w n := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
    have hcoord := (hquad j hj).1
    change minL w n = L w j at he
    omega
  have hminLupper : minL w n ≤ L w n := by
    have h := runningMin_le (L w) n n le_rfl
    change minL w n ≤ L w n at h
    exact h
  have hminL : minL w n = (1 : ℤ) - ℓ := by omega
  have hs := kmswLeftRun_quadrant_prefix ℓ n n w le_rfl hquad
  obtain ⟨hUR, hLR, hUL, hLL⟩ := hs
  have hURnat : (kmswStage w n).UR.length = 0 := by exact_mod_cast (show ((kmswStage w n).UR.length : ℤ) = 0 by rw [hUR, hRend])
  have hLLnat : (kmswStage w n).LL.length = ℓ - 1 := by
    have hcast : ((kmswStage w n).LL.length : ℤ) = (ℓ : ℤ) - 1 := by
      rw [hLL, hminL]
      omega
    have hnat : (kmswStage w n).LL.length = ℓ - 1 := by
      exact_mod_cast hcast
    simpa [Nat.cast_sub hℓ] using hnat
  constructor
  · exact hURnat
  constructor
  · exact hLR
  constructor
  · exact hLLnat
  constructor
  · have hcast : ((kmswStage w n).UL.length : ℤ) = 1 := by
      rw [hUL, hLend, hminL]
      omega
    exact_mod_cast hcast
  · rw [kmswLeftRun_nextEdge_count, hURnat, hLLnat]
    omega



theorem kmswLeftRun_admissible_missing_iff (ℓ n : ℕ) (c : Fin n → Fin 3)
    (hc : KMSWLeftWalkAdmissible ℓ n c) :
    let w := finiteCodeExtend (n := n + 1) c
    ∀ e < (kmswStage w n).nextEdge,
      ((kmswStage w n).present e = false ↔ e ∈ (kmswStage w n).LL) := by
  dsimp only
  intro e he
  obtain ⟨hUR, _, _, _, _⟩ := kmswLeftRun_admissible_lengths ℓ n c hc
  have hURnil : (kmswStage (finiteCodeExtend (n := n + 1) c) n).UR = [] :=
    List.length_eq_zero_iff.mp hUR
  have hmissing :=
    kmswStage_missing_edges_exactly_UR_append_LL (finiteCodeExtend (n := n + 1) c) n e he
  rw [hURnil] at hmissing
  simpa using hmissing




theorem kmswLeftRun_admissible_edge_counts (ℓ n : ℕ) (c : Fin n → Fin 3)
    (hc : KMSWLeftWalkAdmissible ℓ n c) :
    let w := finiteCodeExtend (n := n + 1) c
    Finset.card (Finset.filter
        (fun e => (kmswStage w n).present e = false) (Finset.range (n + ℓ))) = ℓ - 1 ∧
      Finset.card (Finset.filter
        (fun e => (kmswStage w n).present e = true) (Finset.range (n + ℓ))) = n + 1 := by
  classical
  dsimp only
  let w : ℕ → Fin 3 := finiteCodeExtend (n := n + 1) c
  let s := kmswStage w n
  obtain ⟨_, _, hLL, _, hnext⟩ := kmswLeftRun_admissible_lengths ℓ n c hc
  have hnext' : s.nextEdge = n + ℓ := by simpa [s, w] using hnext
  have hℓ : 1 ≤ ℓ := by
    have hcoords := kmswLeft_admissible_coordinates ℓ n c hc
    have hzero := (hcoords.1 0 (by omega)).1
    simp only [L, Finset.range_zero, Finset.sum_empty, add_zero] at hzero
    omega
  have hmissing : ∀ e < s.nextEdge,
      (s.present e = false ↔ e ∈ s.LL) := by
    simpa only [s, w] using kmswLeftRun_admissible_missing_iff ℓ n c hc
  have hbound : ∀ e ∈ s.LL, e < s.nextEdge := by
    intro e he
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    simp only [List.mem_append]
    exact Or.inl (Or.inr he)
  have hmissSet :
      (Finset.range (n + ℓ)).filter (fun e => s.present e = false) = s.LL.toFinset := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    constructor
    · rintro ⟨he, hp⟩
      have he' : e < s.nextEdge := by rw [hnext']; exact he
      have hs := hmissing e he'
      exact hs.mp hp
    · intro he
      constructor
      · have hb := hbound e he
        simpa [hnext'] using hb
      · have hb := hbound e he
        exact (hmissing e hb).mpr he
  have hmissCard :
      Finset.card ((Finset.range (n + ℓ)).filter (fun e => s.present e = false)) = ℓ - 1 := by
    rw [hmissSet, List.toFinset_card_of_nodup (kmswStage_status w n).2.2.2.2.1, hLL]
  have hpresentSet :
      (Finset.range (n + ℓ)).filter (fun e => s.present e = true) =
        (Finset.range (n + ℓ)).filter (fun e => ¬ s.present e = false) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hp⟩
      exact ⟨he, by simp [hp]⟩
    · rintro ⟨he, hp⟩
      have hp' : s.present e = true := by
        cases h : s.present e <;> simp_all
      exact ⟨he, hp'⟩
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.range (n + ℓ)) (fun e => s.present e = false)
  rw [← hpresentSet, hmissCard, Finset.card_range] at hpartition
  have hpresentCard :
      Finset.card ((Finset.range (n + ℓ)).filter (fun e => s.present e = true)) = n + 1 := by
    omega
  exact ⟨hmissCard, hpresentCard⟩

end DirectedDistances.KMSW
