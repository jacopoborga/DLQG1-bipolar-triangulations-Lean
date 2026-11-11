module

public import DirectedDistances.KMSW.InfiniteRotation
public import DirectedDistances.KMSW.CutEquivalence
public import DirectedDistances.KMSW.StageOuterWord
public import DirectedDistances.KMSW.BoundaryDynamics
import Mathlib.Order.Interval.Set.Infinite

/-! # Left and right boundary edges of the limiting KMSW map

Helpers for the left and right boundary of the infinite map

The upper-left prefixes stabilise (a position below the horizontal record level is
never touched again), the lower-right list only grows by appending, and the outer
word of a large stage places consecutive boundary edges next to each other.
`Nat.nth` is not available in the built dependency cache, so the `i`-th element of
a predicate is selected through `Nat.count`. -/

public section
namespace DirectedDistances.KMSW

open Filter
open scoped Classical

/-! ### Selecting the `i`-th element of a set of naturals -/

/-- The `i`-th element (counting from `0`) of `{m | P m}`; the value is irrelevant
when the set has at most `i` elements. -/
@[expose] noncomputable def natSelect (P : ℕ → Prop) [DecidablePred P] (i : ℕ) : ℕ :=
  if h : ∃ m, i < Nat.count P (m + 1) then Nat.find h else 0

theorem natSelect_count {P : ℕ → Prop} [DecidablePred P] {m : ℕ} (hm : P m) :
    natSelect P (Nat.count P m) = m := by
  have hs : Nat.count P m < Nat.count P (m + 1) := by
    rw [Nat.count_succ]
    simp only [hm, ↓reduceIte]
    omega
  have h : ∃ k, Nat.count P m < Nat.count P (k + 1) := ⟨m, hs⟩
  unfold natSelect
  simp only [h, ↓reduceDIte]
  apply le_antisymm
  · exact Nat.find_min' h hs
  · by_contra hlt'
    have hlt := not_le.1 hlt'
    have h1 := Nat.find_spec h
    have h2 : Nat.count P (Nat.find h + 1) ≤ Nat.count P m :=
      Nat.count_monotone (p := P) (by omega)
    omega

theorem natCount_congr {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] (s : ℕ)
    (h : ∀ m < s, P m ↔ Q m) : Nat.count P s = Nat.count Q s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.count_succ, Nat.count_succ, ih (fun m hm => h m (by omega))]
    have hs := h s (by omega)
    by_cases hp : P s
    · have hq := hs.1 hp
      simp [hp, hq]
    · have hq : ¬ Q s := fun hq => hp (hs.2 hq)
      simp [hp, hq]

theorem natSelect_eq_of_agree {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    {i s : ℕ} (hQ : Q s) (hc : Nat.count Q s = i) (hag : ∀ m ≤ s, P m ↔ Q m) :
    natSelect P i = s := by
  have hP : P s := (hag s le_rfl).2 hQ
  have hc' : Nat.count P s = i := by
    rw [natCount_congr s (fun m hm => hag m hm.le)]
    exact hc
  rw [← hc']
  exact natSelect_count hP

theorem exists_le_count_of_infinite {P : ℕ → Prop} [DecidablePred P]
    (hP : {m | P m}.Infinite) (i : ℕ) : ∃ N, i ≤ Nat.count P N := by
  induction i with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ i ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨m, hm, hNm⟩ := hP.exists_gt N
    have hm' : P m := hm
    refine ⟨m + 1, ?_⟩
    have h1 : Nat.count P N ≤ Nat.count P m := Nat.count_monotone (p := P) hNm.le
    rw [Nat.count_succ]
    simp only [hm', ↓reduceIte]
    omega

theorem natSelect_spec {P : ℕ → Prop} [DecidablePred P] (hP : {m | P m}.Infinite)
    (i : ℕ) : P (natSelect P i) ∧ Nat.count P (natSelect P i) = i := by
  obtain ⟨N, hN⟩ := exists_le_count_of_infinite hP (i + 1)
  have hex : ∃ k, i < Nat.count P (k + 1) := by
    cases N with
    | zero => simp at hN
    | succ k => exact ⟨k, hN⟩
  obtain ⟨m, hm_spec, hm_min⟩ : ∃ m, i < Nat.count P (m + 1) ∧
      ∀ m' < m, ¬ i < Nat.count P (m' + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m' h => Nat.find_min hex h⟩
  have hle : Nat.count P m ≤ i := by
    cases m with
    | zero => simp
    | succ m' => exact Nat.not_lt.1 (hm_min m' (Nat.lt_succ_self m'))
  have hPm : P m := by
    by_contra hn
    rw [Nat.count_succ] at hm_spec
    simp only [hn, ↓reduceIte] at hm_spec
    omega
  have hcm : Nat.count P m = i := by
    rw [Nat.count_succ] at hm_spec
    simp only [hPm, ↓reduceIte] at hm_spec
    omega
  have hsel : natSelect P i = m := by
    have := natSelect_count hPm
    rwa [hcm] at this
  rw [hsel]
  exact ⟨hPm, hcm⟩

/-! ### Filtered initial segments of the naturals -/

theorem length_filter_range (p : ℕ → Bool) (N : ℕ) :
    ((List.range N).filter p).length = Nat.count (fun m => p m = true) N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Nat.count_succ]
    by_cases hp : p N = true <;> simp [hp]

theorem filter_range_getElem?_eq (p : ℕ → Bool) (N i : ℕ)
    (h : i < ((List.range N).filter p).length) :
    ((List.range N).filter p)[i]? = some (natSelect (fun m => p m = true) i) := by
  induction N generalizing i with
  | zero => simp at h
  | succ N ih =>
    rw [List.range_succ, List.filter_append] at h ⊢
    by_cases hp : p N = true
    · have hs : List.filter p [N] = [N] := by simp [hp]
      rw [hs] at h ⊢
      by_cases hi : i < ((List.range N).filter p).length
      · rw [List.getElem?_append_left hi]
        exact ih i hi
      · have hi' : i = ((List.range N).filter p).length := by
          rw [List.length_append] at h
          simp only [List.length_singleton] at h
          omega
        rw [List.getElem?_append_right (by omega), hi', length_filter_range,
          natSelect_count (P := fun m => p m = true) hp]
        simp
    · have hs : List.filter p [N] = [] := by simp [hp]
      rw [hs, List.append_nil] at h ⊢
      exact ih i h

/-- A selected element of a predicate with a matching boolean test, read off from the
filtered initial segment once the segment is long enough. -/
theorem filter_range_getElem?_select {Q : ℕ → Prop} [DecidablePred Q]
    (hQ : {m | Q m}.Infinite) (p : ℕ → Bool) (i n : ℕ)
    (hn : natSelect Q i ≤ n)
    (hag : ∀ m ≤ natSelect Q i, p m = true ↔ Q m) :
    ((List.range (n + 1)).filter p)[i]? = some (natSelect Q i) := by
  obtain ⟨hQs, hc⟩ := natSelect_spec hQ i
  have hPs : p (natSelect Q i) = true := (hag _ le_rfl).2 hQs
  have hcP : Nat.count (fun m => p m = true) (natSelect Q i) = i :=
    (natCount_congr (natSelect Q i) (fun m hm => hag m hm.le)).trans hc
  have hlen : i < ((List.range (n + 1)).filter p).length := by
    rw [length_filter_range]
    have h1 : Nat.count (fun m => p m = true) (natSelect Q i + 1) = i + 1 := by
      rw [Nat.count_succ, hcP]
      simp [hPs]
    have h2 : Nat.count (fun m => p m = true) (natSelect Q i + 1) ≤
        Nat.count (fun m => p m = true) (n + 1) :=
      Nat.count_monotone (p := fun m => p m = true) (by omega)
    omega
  rw [filter_range_getElem?_eq p (n + 1) i hlen,
    natSelect_eq_of_agree (P := fun m => p m = true) hQs hc hag]

/-! ### The boundary edge sequences -/

theorem exists_upper_bound (f : ℕ → ℤ) (s : ℕ) : ∃ c, ∀ j ≤ s, f j ≤ c := by
  obtain ⟨c, hc⟩ := ((Set.finite_le_nat s).image f).bddAbove
  exact ⟨c, fun j hj => hc ⟨j, hj, rfl⟩⟩

/-- The `i`-th left boundary edge `l_i`: the active edge of the `i`-th time at which the
horizontal coordinate has strictly smaller value than at every later time -/
@[expose] noncomputable def kmswLeftBoundaryEdge (w : ℕ → Fin 3) (i : ℕ) : ℕ :=
  act w (natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) i)

/-- The `i`-th right boundary edge `r_i`: the active edge of the `i`-th time at which
the vertical coordinate is strictly smaller than at every earlier time -/
@[expose] noncomputable def kmswRightBoundaryEdge (w : ℕ → Fin 3) (i : ℕ) : ℕ :=
  act w (natSelect (fun m => ∀ j, j < m → R w m < R w j) i)

theorem left_record_infinite (w : ℕ → Fin 3) (htrans : Tendsto (L w) atTop atTop) :
    {m | ∀ j, m < j → L w m + 1 ≤ L w j}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨c, hc⟩ := exists_upper_bound (L w) (M + 1)
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp htrans (c + 1)
  have hM1 : L w (M + 1) ≤ c := hc _ le_rfl
  have hK : M + 1 ≤ max N (M + 1) := le_max_right _ _
  have hge : M + 1 ≤ Nat.findGreatest (fun j => L w j ≤ c) (max N (M + 1)) :=
    Nat.le_findGreatest hK hM1
  have hspec : L w (Nat.findGreatest (fun j => L w j ≤ c) (max N (M + 1))) ≤ c :=
    Nat.findGreatest_spec (P := fun j => L w j ≤ c) hK hM1
  refine ⟨Nat.findGreatest (fun j => L w j ≤ c) (max N (M + 1)), ?_, by omega⟩
  intro j hj
  by_cases hjK : j ≤ max N (M + 1)
  · have hnot := Nat.findGreatest_is_greatest hj hjK
    have : c < L w j := by
      by_contra hcon
      exact hnot (not_lt.1 hcon)
    omega
  · have := hN j (by
      have : N ≤ max N (M + 1) := le_max_left _ _
      omega)
    omega

theorem right_record_infinite (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    {m | ∀ j, j < m → R w m < R w j}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨c, hc⟩ := exists_upper_bound (fun j => - R w j) M
  have hex : ∃ n, R w n ≤ -c - 1 := hR _
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro j hj
    have hspec := Nat.find_spec hex
    have hmin := Nat.find_min hex hj
    omega
  · by_contra hcon
    have hle : Nat.find hex ≤ M := not_lt.1 hcon
    have := hc _ hle
    have := Nat.find_spec hex
    omega

/-- Left-boundary stabilisation at the level of the closed-form record list: the `i`-th
entry stops changing once the horizontal coordinate stays above its level at the `i`-th
record. -/
theorem left_filter_eventually (w : ℕ → Fin 3) (htrans : Tendsto (L w) atTop atTop)
    (i : ℕ) :
    ∃ N, ∀ n ≥ N,
      ((List.range (n + 1)).filter
        (fun m => decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j)))[i]? =
      some (natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) i) := by
  have hinf := left_record_infinite w htrans
  obtain ⟨hQs, _⟩ := natSelect_spec hinf i
  obtain ⟨c, hc⟩ := exists_upper_bound (L w) (natSelect (fun m => ∀ j, m < j →
    L w m + 1 ≤ L w j) i)
  obtain ⟨N1, hN1⟩ := Filter.tendsto_atTop_atTop.mp htrans (c + 1)
  refine ⟨max N1 (natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) i), fun n hn => ?_⟩
  have hs : natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) i ≤ n :=
    le_trans (le_max_right _ _) hn
  have h1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  refine filter_range_getElem?_select hinf _ i n hs ?_
  intro m hm
  rw [decide_eq_true_iff]
  constructor
  · intro hP j hj
    by_cases hjn : j ≤ n
    · exact hP j hj hjn
    · have := hN1 j (by omega)
      have := hc m hm
      omega
  · intro hQ j hj _
    exact hQ j hj

theorem right_filter_eventually (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (i : ℕ) :
    ∃ N, ∀ n ≥ N,
      ((List.range (n + 1)).filter
        (fun m => decide (∀ j, j < m → R w m < R w j)))[i]? =
      some (natSelect (fun m => ∀ j, j < m → R w m < R w j) i) := by
  refine ⟨natSelect (fun m => ∀ j, j < m → R w m < R w j) i, fun n hn => ?_⟩
  refine filter_range_getElem?_select (right_record_infinite w hR) _ i n hn ?_
  intro m _
  rw [decide_eq_true_iff]

/-- Stabilisation of the upper-left prefixes: from some stage on, the `i`-th entry of
the upper-left list is the `i`-th left boundary edge `l_i` -/
theorem kmswStage_UL_getElem?_eventually (w : ℕ → Fin 3)
    (htrans : Tendsto (L w) atTop atTop) (i : ℕ) :
    ∃ N, ∀ n ≥ N, (kmswStage w n).UL[i]? = some (kmswLeftBoundaryEdge w i) := by
  obtain ⟨N, hN⟩ := left_filter_eventually w htrans i
  refine ⟨N, fun n hn => ?_⟩
  rw [kmswStage_UL_eq, List.getElem?_map, hN n hn]
  rfl

/-- The `i`-th lower-right entry is the `i`-th right boundary edge `r_i` from the stage -/
theorem kmswStage_LR_getElem?_eventually (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (i : ℕ) :
    ∃ N, ∀ n ≥ N, (kmswStage w n).LR[i]? = some (kmswRightBoundaryEdge w i) := by
  obtain ⟨N, hN⟩ := right_filter_eventually w hR i
  refine ⟨N, fun n hn => ?_⟩
  rw [kmswStage_LR_eq, List.getElem?_map, hN n hn]
  rfl

/-- The lower-right list only grows by appending (`def-kmsw`, -/
theorem kmswStage_LR_succ_eq_append (w : ℕ → Fin 3) (n : ℕ) :
    ∃ t, (kmswStage w (n + 1)).LR = (kmswStage w n).LR ++ t := by
  refine ⟨(List.filter (fun m => decide (∀ j, j < m → R w m < R w j)) [n + 1]).map (act w),
    ?_⟩
  rw [kmswStage_LR_eq, kmswStage_LR_eq, List.range_succ (n := n + 1), List.filter_append,
    List.map_append]

/-- Infinite upper-left membership is exactly being a left boundary edge `l_i` -/
theorem isLeftBoundaryEdge_iff (w : ℕ → Fin 3) (htrans : Tendsto (L w) atTop atTop)
    (e : ℕ) : IsLeftBoundaryEdge w e ↔ ∃ i, e = kmswLeftBoundaryEdge w i := by
  constructor
  · intro hinf
    obtain ⟨j0, hj0, _⟩ := Set.Infinite.exists_gt hinf 0
    have hj0' : e ∈ (kmswStage w j0).UL := hj0
    rw [kmswStage_UL_eq] at hj0'
    obtain ⟨m, _, hme⟩ := List.mem_map.1 hj0'
    have hQm : ∀ j', m < j' → L w m + 1 ≤ L w j' := by
      intro j' hj'
      obtain ⟨j, hj, hjj'⟩ := Set.Infinite.exists_gt hinf j'
      have hj' : e ∈ (kmswStage w j).UL := hj
      rw [kmswStage_UL_eq] at hj'
      obtain ⟨m', hm', hm'e⟩ := List.mem_map.1 hj'
      have hmm : m' = m := CutConverse.act_injective w (hm'e.trans hme.symm)
      subst hmm
      have := of_decide_eq_true (List.mem_filter.1 hm').2
      exact this j' hj' hjj'.le
    refine ⟨Nat.count (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) m, ?_⟩
    unfold kmswLeftBoundaryEdge
    rw [natSelect_count (P := fun m => ∀ j, m < j → L w m + 1 ≤ L w j) hQm]
    exact hme.symm
  · rintro ⟨i, rfl⟩
    obtain ⟨hQs, _⟩ := natSelect_spec (left_record_infinite w htrans) i
    refine Set.Infinite.mono (s := Set.Ici (natSelect (fun m => ∀ j, m < j →
      L w m + 1 ≤ L w j) i)) ?_ (Set.Ici_infinite _)
    intro j hj
    have hj' := Set.mem_Ici.1 hj
    show act w _ ∈ (kmswStage w j).UL
    rw [kmswStage_UL_eq]
    exact List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.mem_range.2 (by omega),
      decide_eq_true (fun j' h1 _ => hQs j' h1)⟩, rfl⟩

/-- Infinite lower-right membership is exactly being a right boundary edge `r_i` -/
theorem isRightBoundaryEdge_iff (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (e : ℕ) : IsRightBoundaryEdge w e ↔ ∃ i, e = kmswRightBoundaryEdge w i := by
  constructor
  · intro hinf
    obtain ⟨j0, hj0⟩ := hinf.nonempty
    have hj0' : e ∈ (kmswStage w j0).LR := hj0
    rw [kmswStage_LR_eq] at hj0'
    obtain ⟨m, hm, hme⟩ := List.mem_map.1 hj0'
    have hQm : ∀ j, j < m → R w m < R w j :=
      of_decide_eq_true (List.mem_filter.1 hm).2
    refine ⟨Nat.count (fun m => ∀ j, j < m → R w m < R w j) m, ?_⟩
    unfold kmswRightBoundaryEdge
    rw [natSelect_count (P := fun m => ∀ j, j < m → R w m < R w j) hQm]
    exact hme.symm
  · rintro ⟨i, rfl⟩
    obtain ⟨hQs, _⟩ := natSelect_spec (right_record_infinite w hR) i
    refine Set.Infinite.mono (s := Set.Ici (natSelect (fun m => ∀ j, j < m →
      R w m < R w j) i)) ?_ (Set.Ici_infinite _)
    intro j hj
    have hj' := Set.mem_Ici.1 hj
    show act w _ ∈ (kmswStage w j).LR
    rw [kmswStage_LR_eq]
    exact List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.mem_range.2 (by omega),
      decide_eq_true hQs⟩, rfl⟩

/-- With nonnegative horizontal coordinate the lower-left list stays empty -/
theorem kmswStage_LL_eq_nil (w : ℕ → Fin 3) (hL0 : ∀ j, 0 ≤ L w j) (n : ℕ) :
    (kmswStage w n).LL = [] := by
  have hlen := kmswStage_LL_length w n
  have hL00 : L w 0 = 0 := by simp [L]
  have h0 : minL w n ≤ 0 := by
    have := runningMin_le (L w) n 0 (Nat.zero_le n)
    have h' : minL w n ≤ L w 0 := this
    omega
  obtain ⟨j, _, he⟩ := runningMin_attained (L w) n
  have he' : minL w n = L w j := he
  have := hL0 j
  have hz : (kmswStage w n).LL.length = 0 := by omega
  exact List.length_eq_zero_iff.1 hz

/-- The first right boundary edge is the initial edge (`def-kmsw`, -/
theorem kmswRightBoundaryEdge_zero (w : ℕ → Fin 3) : kmswRightBoundaryEdge w 0 = 0 := by
  have h := natSelect_count (P := fun m => ∀ j, j < m → R w m < R w j) (m := 0)
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  rw [Nat.count_zero] at h
  unfold kmswRightBoundaryEdge
  rw [h]
  rfl

/-- If the horizontal coordinate stays strictly above its initial value, the first left
boundary edge is the initial edge as well (`def-kmsw`, -/
theorem kmswLeftBoundaryEdge_zero_of (w : ℕ → Fin 3) (h : ∀ j, 0 < j → 1 ≤ L w j) :
    kmswLeftBoundaryEdge w 0 = 0 := by
  have hL00 : L w 0 = 0 := by simp [L]
  have h' := natSelect_count (P := fun m => ∀ j, m < j → L w m + 1 ≤ L w j) (m := 0)
    (fun j hj => by rw [hL00]; exact h j hj)
  rw [Nat.count_zero] at h'
  unfold kmswLeftBoundaryEdge
  rw [h']
  rfl

/-! ### The outer word at a large stage -/

theorem outerWordVal_getElem?_UL (w : ℕ → Fin 3) (n i e : ℕ)
    (he : (kmswStage w n).UL[i]? = some e) :
    (stageOuterWordVal w n)[i]? = some (e, false) := by
  have hi := (List.getElem?_eq_some_iff.1 he).1
  have h1 : i < ((kmswStage w n).UL.map fun e => (e, false)).length := by simpa using hi
  have h2 : i < (((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false))).length := by
    simp only [List.length_append, List.length_map]; omega
  have h3 : i < (((kmswStage w n).UL.map fun e => (e, false)) ++
      ((kmswStage w n).UR.map fun e => (e, false)) ++
      ((kmswStage w n).LR.reverse.map fun e => (e, true))).length := by
    simp only [List.length_append, List.length_map]; omega
  rw [stageOuterWordVal_eq_runs, List.getElem?_append_left h3, List.getElem?_append_left h2,
    List.getElem?_append_left h1, List.getElem?_map, he]
  rfl

theorem outerWordVal_length (w : ℕ → Fin 3) (n : ℕ) (hLL : (kmswStage w n).LL = []) :
    (stageOuterWordVal w n).length =
      (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        (kmswStage w n).LR.length := by
  rw [stageOuterWordVal_eq_runs, hLL]
  simp only [List.reverse_nil, List.map_nil, List.append_nil, List.length_append,
    List.length_map, List.length_reverse]

theorem outerWordVal_getElem?_LR (w : ℕ → Fin 3) (n j e : ℕ)
    (hLL : (kmswStage w n).LL = [])
    (he : (kmswStage w n).LR[j]? = some e) :
    (stageOuterWordVal w n)[(kmswStage w n).UL.length + (kmswStage w n).UR.length +
        ((kmswStage w n).LR.length - 1 - j)]? = some (e, true) := by
  have hj := (List.getElem?_eq_some_iff.1 he).1
  rw [stageOuterWordVal_eq_runs, hLL]
  simp only [List.reverse_nil, List.map_nil, List.append_nil]
  rw [List.getElem?_append_right (by simp)]
  have hsub : (kmswStage w n).UL.length + (kmswStage w n).UR.length +
      ((kmswStage w n).LR.length - 1 - j) -
      (((kmswStage w n).UL.map fun e => (e, false)) ++
        ((kmswStage w n).UR.map fun e => (e, false))).length =
      (kmswStage w n).LR.length - 1 - j := by
    simp
  rw [hsub, List.getElem?_map, List.getElem?_reverse (by omega)]
  have hidx : (kmswStage w n).LR.length - 1 - ((kmswStage w n).LR.length - 1 - j) = j := by
    omega
  rw [hidx, he]
  rfl

theorem outer_faceSucc_exists (w : ℕ → Fin 3) (n : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (k : ℕ) (hk : k < (stageOuterWordVal w n).length) :
    ∃ d d' : StageDart (kmswStage w n).nextEdge,
      (stageOuterWordVal w n)[k]? = some (d.1.val, d.2) ∧
      (stageOuterWordVal w n)[(k + 1) % (stageOuterWordVal w n).length]? =
        some (d'.1.val, d'.2) ∧
      (kmswMap w n).faceSucc d = d' := by
  have hlen : (stageOuterWordVal w n).length = (stageOuterWord w n).length := by
    simp [stageOuterWordVal]
  have hk' : k < (stageOuterWord w n).length := by omega
  have hm : (k + 1) % (stageOuterWord w n).length < (stageOuterWord w n).length :=
    Nat.mod_lt _ (by omega)
  refine ⟨(stageOuterWord w n)[k], (stageOuterWord w n)[(k + 1) % (stageOuterWord w n).length],
    ?_, ?_, ?_⟩
  · simp only [stageOuterWordVal, List.getElem?_map, List.getElem?_eq_getElem hk']
    rfl
  · rw [hlen]
    simp only [stageOuterWordVal, List.getElem?_map, List.getElem?_eq_getElem hm]
    rfl
  · rw [hcycle _ (List.getElem_mem hk')]
    exact List.formPerm_apply_getElem _ (stageOuterWord_nodup w n) k hk'

/-- Two darts whose values are `a`, `b` and which are joined by the finite face
successor at all large stages force the limiting face successor to join `a` and `b`. -/
theorem kmswInfFaceSucc_eq_of_stages (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (a b : ℕ × Bool)
    (h : ∃ N, ∀ n ≥ N, ∃ d d' : StageDart (kmswStage w n).nextEdge,
      (d.1.val, d.2) = a ∧ (d'.1.val, d'.2) = b ∧ (kmswMap w n).faceSucc d = d') :
    kmswInfFaceSucc w hfin a = b := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨N0, hN0⟩ := kmswInfFaceSucc_eventually_eq_stage w hfin a
  obtain ⟨hd, heq⟩ := hN0 (max N N0) (le_max_right _ _)
  obtain ⟨d, d', ha, hb, hf⟩ := hN (max N N0) (le_max_left _ _)
  have hdeq : d = (⟨a.1, hd⟩, a.2) := by
    obtain ⟨⟨x, hx⟩, y⟩ := d
    have h1 : x = a.1 := congrArg Prod.fst ha
    have h2 : y = a.2 := congrArg Prod.snd ha
    subst h1 h2
    rfl
  rw [heq, ← hdeq, hf]
  exact hb

/-- On the outer face, `l_i` is followed by `l_{i+1}` (the left boundary of the UIQBOT,
property at every stage. -/
theorem kmswInfFaceSucc_left (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hcycle : ∀ n, ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (htrans : Tendsto (L w) atTop atTop) (i : ℕ) :
    kmswInfFaceSucc w hfin (kmswLeftBoundaryEdge w i, false) =
      (kmswLeftBoundaryEdge w (i + 1), false) := by
  obtain ⟨N1, h1⟩ := kmswStage_UL_getElem?_eventually w htrans i
  obtain ⟨N2, h2⟩ := kmswStage_UL_getElem?_eventually w htrans (i + 1)
  refine kmswInfFaceSucc_eq_of_stages w hfin _ _ ⟨max N1 N2, fun n hn => ?_⟩
  have v1 := outerWordVal_getElem?_UL w n i _ (h1 n (le_trans (le_max_left _ _) hn))
  have v2 := outerWordVal_getElem?_UL w n (i + 1) _ (h2 n (le_trans (le_max_right _ _) hn))
  have hk := (List.getElem?_eq_some_iff.1 v1).1
  have hk2 := (List.getElem?_eq_some_iff.1 v2).1
  obtain ⟨d, d', hd, hd', hf⟩ := outer_faceSucc_exists w n (hcycle n) i hk
  rw [Nat.mod_eq_of_lt (by omega)] at hd'
  refine ⟨d, d', ?_, ?_, hf⟩
  · rw [v1] at hd
    exact (Option.some.inj hd).symm
  · rw [v2] at hd'
    exact (Option.some.inj hd').symm

/-- On the outer face, `r_{i+1}` is followed by `r_i` (the right boundary of the UIQBOT, -/
theorem kmswInfFaceSucc_right (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hcycle : ∀ n, ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (hL0 : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (i : ℕ) :
    kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w (i + 1), true) =
      (kmswRightBoundaryEdge w i, true) := by
  obtain ⟨N1, h1⟩ := kmswStage_LR_getElem?_eventually w hR i
  obtain ⟨N2, h2⟩ := kmswStage_LR_getElem?_eventually w hR (i + 1)
  refine kmswInfFaceSucc_eq_of_stages w hfin _ _ ⟨max N1 N2, fun n hn => ?_⟩
  have hLL := kmswStage_LL_eq_nil w hL0 n
  have e1 := h1 n (le_trans (le_max_left _ _) hn)
  have e2 := h2 n (le_trans (le_max_right _ _) hn)
  have v1 := outerWordVal_getElem?_LR w n i _ hLL e1
  have v2 := outerWordVal_getElem?_LR w n (i + 1) _ hLL e2
  have hk2 : i + 1 < (kmswStage w n).LR.length := (List.getElem?_eq_some_iff.1 e2).1
  have hlen := outerWordVal_length w n hLL
  have hp := (List.getElem?_eq_some_iff.1 v2).1
  obtain ⟨d, d', hd, hd', hf⟩ := outer_faceSucc_exists w n (hcycle n) _ hp
  have hmod : ((kmswStage w n).UL.length + (kmswStage w n).UR.length +
      ((kmswStage w n).LR.length - 1 - (i + 1)) + 1) % (stageOuterWordVal w n).length =
      (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        ((kmswStage w n).LR.length - 1 - i) := by
    have : (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        ((kmswStage w n).LR.length - 1 - (i + 1)) + 1 =
        (kmswStage w n).UL.length + (kmswStage w n).UR.length +
          ((kmswStage w n).LR.length - 1 - i) := by omega
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hd'
  refine ⟨d, d', ?_, ?_, hf⟩
  · rw [v2] at hd
    exact (Option.some.inj hd).symm
  · rw [v1] at hd'
    exact (Option.some.inj hd').symm

/-- The junction of the outer face: the first right boundary edge is followed by the first -/
theorem kmswInfFaceSucc_junction (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hcycle : ∀ n, ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (hL0 : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
      (kmswLeftBoundaryEdge w 0, false) := by
  obtain ⟨N1, h1⟩ := kmswStage_UL_getElem?_eventually w htrans 0
  obtain ⟨N2, h2⟩ := kmswStage_LR_getElem?_eventually w hR 0
  refine kmswInfFaceSucc_eq_of_stages w hfin _ _ ⟨max N1 N2, fun n hn => ?_⟩
  have hLL := kmswStage_LL_eq_nil w hL0 n
  have e2 := h2 n (le_trans (le_max_right _ _) hn)
  have v1 := outerWordVal_getElem?_UL w n 0 _ (h1 n (le_trans (le_max_left _ _) hn))
  have v2 := outerWordVal_getElem?_LR w n 0 _ hLL e2
  have hk : 0 < (kmswStage w n).LR.length := (List.getElem?_eq_some_iff.1 e2).1
  have hlen := outerWordVal_length w n hLL
  have hp := (List.getElem?_eq_some_iff.1 v2).1
  obtain ⟨d, d', hd, hd', hf⟩ := outer_faceSucc_exists w n (hcycle n) _ hp
  have hmod : ((kmswStage w n).UL.length + (kmswStage w n).UR.length +
      ((kmswStage w n).LR.length - 1 - 0) + 1) % (stageOuterWordVal w n).length = 0 := by
    have : (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        ((kmswStage w n).LR.length - 1 - 0) + 1 = (stageOuterWordVal w n).length := by
      omega
    rw [this]
    exact Nat.mod_self _
  rw [hmod] at hd'
  refine ⟨d, d', ?_, ?_, hf⟩
  · rw [v2] at hd
    exact (Option.some.inj hd).symm
  · rw [v1] at hd'
    exact (Option.some.inj hd').symm

end DirectedDistances.KMSW
