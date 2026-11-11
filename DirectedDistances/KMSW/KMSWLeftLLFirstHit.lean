module

public import DirectedDistances.KMSW.BoundaryRecordsMissing
public import DirectedDistances.KMSW.WalkRecordCounts
public import DirectedDistances.KMSW.StageTrianglePersistence
import DirectedDistances.KMSW.StageOuterCycle

/-! Supporting lemmas for paper labels `lem-kmsw-bdy` (see CORRESPONDENCE.md). -/

/-! # Lower-left missing edges in first-hit order

The source orders the lower-left edges from the lower-right end, hence in
`LL.reverse` order. Source time `T` is the stage after step `T - 1`:
`kmswLLCreatedEdge w T` is allocated by that step, whose zero-based triangle
creation index is `T - 1`. These are helpers, not Proposition 5.16. -/

public section
namespace DirectedDistances.KMSW

open scoped Classical

private abbrev llRecordTimes (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter
    (fun m => decide (0 < m ∧ ∀ j < m, L w m < L w j))

private theorem llRecordTimes_length (w : ℕ → Fin 3) (n : ℕ) :
    (llRecordTimes w n).length = (kmswStage w n).LL.length := by
  have h := congrArg List.length (kmswStage_LL_eq w n)
  simpa only [List.length_map, List.length_reverse] using h.symm

private theorem ll_L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + ((w n : ℤ) - 1) :=
  Finset.sum_range_succ _ _

private theorem ll_L_step (w : ℕ → Fin 3) (n : ℕ) :
    |L w (n + 1) - L w n| ≤ 1 := by
  rw [ll_L_succ]
  have h := (w n).isLt
  apply abs_le.mpr
  constructor <;> omega

private theorem llRecordTimes_get_level (w : ℕ → Fin 3) (n i : ℕ)
    (hi : i < (llRecordTimes w n).length) :
    L w (llRecordTimes w n)[i] = -((i : ℤ) + 1) := by
  induction n generalizing i with
  | zero => simp [llRecordTimes] at hi
  | succ n ih =>
    by_cases hr : ∀ j < n + 1, L w (n + 1) < L w j
    · have he : llRecordTimes w (n + 1) = llRecordTimes w n ++ [n + 1] := by
        change (List.range (n + 1 + 1)).filter _ = _
        rw [List.range_succ, List.filter_append]
        have hb : decide (0 < n + 1 ∧
            ∀ j < n + 1, L w (n + 1) < L w j) = true :=
          decide_eq_true ⟨by omega, hr⟩
        simp only [List.filter_cons, List.filter_nil, hb, ite_true]
      simp only [he] at hi ⊢
      by_cases hiold : i < (llRecordTimes w n).length
      · rw [List.getElem_append_left hiold]
        exact ih i hiold
      · have hieq : i = (llRecordTimes w n).length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hi
          omega
        have hlast := hr n (by omega)
        have hstep := (abs_le.mp (ll_L_step w n)).1
        obtain ⟨j, hj, hmin⟩ := runningMin_attained (L w) n
        have hjrec := hr j (by omega)
        have hminle := runningMin_le (L w) n n le_rfl
        have hlen := kmswStage_LL_length w n
        have hrecLen := llRecordTimes_length w n
        change minL w n = L w j at hmin
        change minL w n ≤ L w n at hminle
        have hval : L w (n + 1) = -((i : ℤ) + 1) := by omega
        simpa [hieq] using hval
    · have he : llRecordTimes w (n + 1) = llRecordTimes w n := by
        change (List.range (n + 1 + 1)).filter _ = _
        rw [List.range_succ, List.filter_append]
        have hb : decide (0 < n + 1 ∧
            ∀ j < n + 1, L w (n + 1) < L w j) = false :=
          decide_eq_false (by rintro ⟨_, h⟩; exact hr h)
        simp only [List.filter_cons, List.filter_nil, hb, Bool.false_eq_true,
          ite_false, List.append_nil]
      simp only [he] at hi ⊢
      exact ih i hi





theorem kmswLL_level_hit (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ (kmswStage w n).LL.length) :
    ∃ m, L w m = -(k : ℤ) := by
  have hi : k - 1 < (llRecordTimes w n).length := by
    rw [llRecordTimes_length]
    omega
  refine ⟨(llRecordTimes w n)[k - 1], ?_⟩
  have h := llRecordTimes_get_level w n (k - 1) hi
  have he : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by omega
  rwa [he] at h






theorem kmswLL_reverse_get_first_hit (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ (kmswStage w n).LL.length) :
    let hhit := kmswLL_level_hit w n k hk hkn
    0 < Nat.find hhit ∧ Nat.find hhit ≤ n ∧
      (kmswStage w n).LL.reverse.get
        ⟨k - 1, by simpa only [List.length_reverse] using
          (show k - 1 < (kmswStage w n).LL.length by omega)⟩ =
        kmswLLCreatedEdge w (Nat.find hhit) := by
  dsimp only
  let hhit := kmswLL_level_hit w n k hk hkn
  have hi : k - 1 < (llRecordTimes w n).length := by
    rw [llRecordTimes_length]
    omega
  let m := (llRecordTimes w n)[k - 1]
  have hm : m ∈ llRecordTimes w n := List.getElem_mem hi
  have hmdata := List.mem_filter.mp hm
  have hmn : m ≤ n := by
    have h := List.mem_range.mp hmdata.1
    omega
  have hrec : 0 < m ∧ ∀ j < m, L w m < L w j := of_decide_eq_true hmdata.2
  have hlevel : L w m = -(k : ℤ) := by
    have h := llRecordTimes_get_level w n (k - 1) hi
    have he : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by omega
    rwa [he] at h
  have hfin : m ∈ ((Finset.Icc 1 n).filter
      (fun m => ∀ j, j < m → L w m < L w j)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrec.1, hmn⟩, hrec.2⟩
  have hfirst := (strict_running_minimum_iff_first_hit (L w) (by simp [L])
    (ll_L_step w) n m (-(k : ℤ)) (by omega) hhit).mp ⟨hfin, hlevel⟩
  have hmeq : m = Nat.find hhit := hfirst.2.2
  refine ⟨by omega, by omega, ?_⟩
  have he : (kmswStage w n).LL.reverse =
      (llRecordTimes w n).map (kmswLLCreatedEdge w) := by
    rw [kmswStage_LL_eq, List.map_reverse, List.reverse_reverse]
  have hiLL : k - 1 < (kmswStage w n).LL.reverse.length := by
    simp only [List.length_reverse]
    omega
  change (kmswStage w n).LL.reverse[k - 1]'hiLL = _
  simp only [he, List.getElem_map]
  exact congrArg (kmswLLCreatedEdge w) hmeq

private theorem ll_find_record (w : ℕ → Fin 3) (k : ℕ) (hk : 1 ≤ k)
    (hhit : ∃ m, L w m = -(k : ℤ)) :
    0 < Nat.find hhit ∧ ∀ j < Nat.find hhit, L w (Nat.find hhit) < L w j := by
  have h := (strict_running_minimum_iff_first_hit (L w) (by simp [L])
    (ll_L_step w) (Nat.find hhit) (Nat.find hhit) (-(k : ℤ))
    (by omega) hhit).mpr ⟨le_rfl, Nat.find_spec hhit, rfl⟩
  have hm := Finset.mem_filter.mp h.1
  exact ⟨(Finset.mem_Icc.mp hm.1).1, hm.2⟩

private theorem ll_record_fresh_left (w : ℕ → Fin 3) (T : ℕ)
    (hT : 0 < T) (hrec : ∀ j < T, L w T < L w j) :
    w (T - 1) = 0 ∧ (kmswStage w (T - 1)).UL.dropLast = [] ∧
      kmswLLCreatedEdge w T = (kmswStage w (T - 1)).nextEdge + 1 := by
  have hprev : T - 1 + 1 = T := by omega
  have hlast := hrec (T - 1) (by omega)
  have hstep := ll_L_succ w (T - 1)
  rw [hprev] at hstep
  have hc : w (T - 1) = 0 := by
    apply Fin.ext
    have hv := (w (T - 1)).isLt
    omega
  have hstep' : L w T = L w (T - 1) - 1 := by simpa [hc, sub_eq_add_neg] using hstep
  obtain ⟨q, hq, hqval⟩ := runningMin_attained (L w) (T - 1)
  have hqrec := hrec q (by omega)
  have hqle := runningMin_le (L w) (T - 1) (T - 1) le_rfl
  change minL w (T - 1) = L w q at hqval
  change minL w (T - 1) ≤ L w (T - 1) at hqle
  have hlen := kmswStage_UL_length w (T - 1)
  have hlenOne : (kmswStage w (T - 1)).UL.length = 1 := by omega
  have hdrop : (kmswStage w (T - 1)).UL.dropLast = [] := by
    apply List.length_eq_zero_iff.mp
    rw [List.length_dropLast, hlenOne]
  refine ⟨hc, hdrop, ?_⟩
  conv_lhs => rw [← hprev]
  simp [kmswLLCreatedEdge, kmswStage, hc, kmswCodeStep, kmswStep,
    kmswStepOfStep, hdrop, State.addEdge]







theorem kmswLL_first_hit_triangle (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ (kmswStage w n).LL.length) :
    let T := Nat.find (kmswLL_level_hit w n k hk hkn)
    ∃ j : TriangleCreationTime w,
      j.val = T - 1 ∧ j.val < n ∧ w j.val = 0 ∧
      (kmswStage w j.val).UL.dropLast = [] ∧
      stageTriangleDartTriple w j =
        (((kmswStage w j.val).active, false),
         ((kmswStage w j.val).nextEdge, true), (kmswLLCreatedEdge w T, false)) ∧
      (kmswLLCreatedEdge w T, false) ∈ stageTriangleDartList w j ∧
      (kmswStage w T).present (kmswLLCreatedEdge w T) = false ∧
      ∀ (r : ℕ) (hjr : j.val < r),
        FaceSucc3Cycle (kmswMap w r).faceSucc
          (stageTriangleDart₁ w r j hjr) (stageTriangleDart₂ w r j hjr)
          (stageTriangleDart₃ w r j hjr) := by
  dsimp only
  let hhit := kmswLL_level_hit w n k hk hkn
  let T := Nat.find hhit
  have hA := kmswLL_reverse_get_first_hit w n k hk hkn
  obtain ⟨hT, hrec⟩ := ll_find_record w k hk hhit
  obtain ⟨hc, hdrop, hid⟩ := ll_record_fresh_left w T hT hrec
  let j : TriangleCreationTime w := ⟨T - 1, Or.inl hc⟩
  have ht := stageTriangleDartTriple_left_fresh w j hc
    (by change (kmswStage w (T - 1)).UL.dropLast.reverse = []; rw [hdrop]; rfl)
  have ht' : stageTriangleDartTriple w j =
      (((kmswStage w j.val).active, false),
       ((kmswStage w j.val).nextEdge, true), (kmswLLCreatedEdge w T, false)) := by
    rw [ht, hid]
  refine ⟨j, rfl, ?_, hc, hdrop, ht', ?_,
    kmswLLCreatedEdge_missing w hT hrec, ?_⟩
  · have hTn : T ≤ n := hA.2.1
    change T - 1 < n
    omega
  · simp only [stageTriangleDartList, ht', List.mem_cons]
    exact Or.inr (Or.inr (Or.inl rfl))
  · exact fun r hjr => stageTriangle_isFace w j r hjr

private theorem ll_record_mem_LL (w : ℕ → Fin 3) (T r : ℕ)
    (hT : 0 < T) (hrec : ∀ j < T, L w T < L w j) (hTr : T ≤ r) :
    kmswLLCreatedEdge w T ∈ (kmswStage w r).LL := by
  rw [kmswStage_LL_eq]
  apply List.mem_map.mpr
  refine ⟨T, List.mem_reverse.mpr ?_, rfl⟩
  exact List.mem_filter.mpr
    ⟨List.mem_range.mpr (by omega), decide_eq_true ⟨hT, hrec⟩⟩





theorem kmswLL_first_hit_east_outer (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ (kmswStage w n).LL.length)
    (r : ℕ) (hr : Nat.find (kmswLL_level_hit w n k hk hkn) ≤ r) :
    (kmswLLCreatedEdge w (Nat.find (kmswLL_level_hit w n k hk hkn)), true) ∈
      stageOuterWordVal w r := by
  obtain ⟨hT, hrec⟩ := ll_find_record w k hk (kmswLL_level_hit w n k hk hkn)
  have he := ll_record_mem_LL w _ r hT hrec hr
  rw [stageOuterWordVal_eq_runs]
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨_, List.mem_reverse.mpr he, rfl⟩





theorem kmswLL_first_hit_unique_triangle (w : ℕ → Fin 3) (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ (kmswStage w n).LL.length) :
    let T := Nat.find (kmswLL_level_hit w n k hk hkn)
    ∃! j : TriangleCreationTime w,
      j.val < n ∧ ∃ b : Bool, (kmswLLCreatedEdge w T, b) ∈ stageTriangleDartList w j := by
  dsimp only
  let T := Nat.find (kmswLL_level_hit w n k hk hkn)
  obtain ⟨j, _, hjn, _, _, _, hjmem, _, _⟩ := kmswLL_first_hit_triangle w n k hk hkn
  have hTn := (kmswLL_reverse_get_first_hit w n k hk hkn).2.1
  have houter := kmswLL_first_hit_east_outer w n k hk hkn n hTn
  refine ⟨j, ⟨hjn, ⟨false, hjmem⟩⟩, ?_⟩
  rintro i ⟨hin, b, hb⟩
  have hbfalse : b = false := by
    cases b with
    | false => rfl
    | true =>
      have hmem : (kmswLLCreatedEdge w T, true) ∈ stageTriangleDartsVal w n :=
        List.mem_flatMap.mpr ⟨i, (mem_stageTriangleTimes w n i).mpr hin, hb⟩
      exact False.elim
        (List.disjoint_left.mp (stage_outer_triangle_disjoint w n) houter hmem)
  subst b
  by_contra hij
  exact List.disjoint_left.mp
    (stageTriangleDartLists_disjoint w n i j hin hjn hij) hb hjmem

end DirectedDistances.KMSW
