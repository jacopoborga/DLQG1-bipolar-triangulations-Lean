module

public import DirectedDistances.KMSW.StageIncidenceChains
public import DirectedDistances.KMSW.CutEquivalenceConverse
import Mathlib.Data.List.Basic

/-! # Finite cut separation from walk records

Bookkeeping for the path-separation use of `def-cut-vertex` -/

public section
namespace DirectedDistances.KMSW

private theorem record_forces_pendant (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) (hn : 0 < n) :
    w (n - 1) = 2 ∧ (kmswStage w (n - 1)).UR = [] := by
  let k := n - 1
  have hnk : n = k + 1 := by dsimp [k]; omega
  have hpast (j : ℕ) (hj : j < n) : R w n ≤ R w j - 1 := hA j hj
  have hR : R w (k + 1) = R w k + (RandomWalk.lazyTwoDimensionalStep (w k)).2 :=
    Finset.sum_range_succ _ _
  have hdown : w k = 2 := by
    have hstrict := hpast k (by omega)
    rw [hnk, hR] at hstrict
    by_cases h2 : (w k).val = 2
    · exact Fin.ext h2
    · have hval : (w k).val = 0 ∨ (w k).val = 1 := by
        have hlt := (w k).isLt
        omega
      rcases hval with h0 | h1
      · have hc : w k = 0 := Fin.ext h0
        rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hstrict
        omega
      · have hc : w k = 1 := Fin.ext h1
        rw [hc, RandomWalk.lazyTwoDimensionalStep_one] at hstrict
        omega
  have hRstep : R w (k + 1) = R w k - 1 := by
    rw [hR, hdown, RandomWalk.lazyTwoDimensionalStep_two]
    ring
  have hmin : minR w k = R w k := by
    obtain ⟨i, hik, hmin⟩ := runningMin_attained (R w) k
    change minR w k = R w i at hmin
    have hlow : R w k ≤ R w i := by
      have hi := hpast i (by omega)
      rw [hnk, hRstep] at hi
      omega
    have hle := runningMin_le (R w) k k (le_refl k)
    change minR w k ≤ R w k at hle
    omega
  have hlen := kmswStage_UR_length w k
  have hURlen : ((kmswStage w k).UR.length : ℤ) = 0 := by
    rw [hlen, hmin]
    ring
  have hUR : (kmswStage w k).UR.length = 0 := by omega
  simpa [k] using And.intro hdown (List.length_eq_zero_iff.mp hUR)

private theorem minL_frozen (w : ℕ → Fin 3) (n : ℕ)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) {m : ℕ} (hnm : n ≤ m) :
    minL w m = minL w n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    change min (minL w m) (L w (m + 1)) = minL w n
    rw [ih]
    have hmin := runningMin_le (L w) n n (le_refl n)
    change minL w n ≤ L w n at hmin
    have hfuture := hB (m + 1) (by omega)
    exact min_eq_left (hmin.trans hfuture)

private theorem left_step_increases_UL_lower_bound (w : ℕ → Fin 3) (n m : ℕ)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) (hnm : n ≤ m)
    (hleft : w m = 0) :
    (kmswStage w m).UL.length > (kmswStage w n).UL.length := by
  have hLnext := hB (m + 1) (by omega)
  have hLs : L w (m + 1) = L w m - 1 := by
    rw [show L w (m + 1) = L w m + (RandomWalk.lazyTwoDimensionalStep (w m)).1 from
      Finset.sum_range_succ _ _]
    rw [hleft, RandomWalk.lazyTwoDimensionalStep_zero]
    ring
  have hLfrozen := minL_frozen w n hB hnm
  have hM := minL_frozen w n hB (by omega : n ≤ m + 1)
  have hlenN := kmswStage_UL_length w n
  have hlenM := kmswStage_UL_length w m
  have hstepL : L w m ≥ L w n + 1 := by omega
  rw [hLfrozen] at hlenM
  have hcast : ((kmswStage w m).UL.length : ℤ) >
      ((kmswStage w n).UL.length : ℤ) := by
    rw [hlenM, hlenN]
    omega
  omega

private def sectorPoint (v a x : ℕ) : Prop := x = v ∨ a ≤ x

private def sectorEdge (w : ℕ → Fin 3) (v a e : ℕ) : Prop :=
  sectorPoint v a (edgeWest w e) ∧ sectorPoint v a (edgeEast w e)

private theorem sectorEdge_of_stage (w : ℕ → Fin 3) (v a m e : ℕ)
    (he : e < (kmswStage w m).nextEdge)
    (hw : sectorPoint v a ((kmswStage w m).west e))
    (hh : sectorPoint v a ((kmswStage w m).east e)) :
    sectorEdge w v a e := by
  rcases edge_endpoints_eq w he with ⟨hW, hE⟩
  constructor
  · rw [← hW]
    exact hw
  · rw [← hE]
    exact hh

private theorem sectorEdge_at_stage (w : ℕ → Fin 3) (v a m e : ℕ)
    (he : e < (kmswStage w m).nextEdge) (h : sectorEdge w v a e) :
    sectorPoint v a ((kmswStage w m).west e) ∧
      sectorPoint v a ((kmswStage w m).east e) := by
  rcases edge_endpoints_eq w he with ⟨hW, hE⟩
  exact ⟨hW ▸ h.1, hE ▸ h.2⟩

private theorem left_predecessor_suffix (p q : List ℕ) (e : ℕ)
    (es : List ℕ) (x : ℕ) (hq : 2 ≤ q.length) (hqne : q ≠ [])
    (hstack : (p ++ q).dropLast.reverse = e :: es) :
    ∃ r, q = r ++ [e, q.getLast hqne] ∧ es.reverse ++ [x] = p ++ r ++ [x] := by
  have hqdropne : q.dropLast ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_dropLast, List.length_nil] at hlen
    omega
  let r := q.dropLast.dropLast
  let e' := q.dropLast.getLast hqdropne
  let last := q.getLast hqne
  have hqdrop : q.dropLast = r ++ [e'] := by
    simpa [r, e'] using (List.dropLast_append_getLast hqdropne).symm
  have hqeq : q = r ++ [e', last] := by
    calc
      q = q.dropLast ++ [last] := (List.dropLast_append_getLast hqne).symm
      _ = r ++ [e', last] := by rw [hqdrop]; simp [List.append_assoc]
  have hform : (p ++ q).dropLast.reverse = e' :: (r.reverse ++ p.reverse) := by
    rw [hqeq]
    simp
  have heq : e = e' := (List.cons.inj (hstack.symm.trans hform)).1
  have hes : es = r.reverse ++ p.reverse := (List.cons.inj (hstack.symm.trans hform)).2
  refine ⟨r, ?_, ?_⟩
  · simpa [heq] using hqeq
  · rw [hes]
    simp [List.reverse_append, List.append_assoc]

private theorem dropLast_append_suffix {α : Type} (p q : List α) (hq : q ≠ []) :
    (p ++ q).dropLast = p ++ q.dropLast := by
  rw [← List.dropLast_append_getLast hq]
  simp

private theorem sector_stage_invariant (w : ℕ → Fin 3) (n v a : ℕ)
    (p : List ℕ) (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (ha0 : a + 1 = (kmswStage w n).nextVertex)
    (hUL0 : (kmswStage w n).UL = p ++ [act w n])
    (hUR0 : (kmswStage w n).UR = [])
    (hact0 : sectorEdge w v a (act w n)) :
    ∀ m, n ≤ m → ∃ q,
      (kmswStage w m).UL = p ++ q ∧ q ≠ [] ∧
      (∀ e ∈ q, sectorEdge w v a e) ∧
      (∀ e ∈ (kmswStage w m).UR, sectorEdge w v a e) ∧
      sectorEdge w v a (act w m) ∧
      (∀ e, (kmswStage w n).nextEdge ≤ e → e < (kmswStage w m).nextEdge →
        sectorEdge w v a e) := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base =>
    refine ⟨[act w n], ?_, by simp, ?_, ?_, hact0, ?_⟩
    · simpa using hUL0
    · intro e he
      simp only [List.mem_singleton] at he
      simpa [he] using hact0
    · simp [hUR0]
    · intro e helo hehi
      omega
  | succ j hj ih =>
    obtain ⟨q, hUL, hqne, hqgood, hURgood, hactgood, hcreated⟩ := ih
    let s := kmswStage w j
    have hULs : s.UL = p ++ q := by simpa [s] using hUL
    have hvertex : a ≤ s.nextVertex := by
      have hmono := CutConverse.nextVertex_mono w hj
      have hbase : a ≤ (kmswStage w n).nextVertex := by omega
      dsimp [s]
      exact hbase.trans hmono
    have hactStage : sectorPoint v a (s.west s.active) ∧
        sectorPoint v a (s.east s.active) := by
      have hh := sectorEdge_at_stage w v a j (act w j)
        (act_lt_nextEdge w (le_refl j)) hactgood
      simpa [s, act] using hh
    have hcodes : w j = 0 ∨ w j = 1 ∨ w j = 2 := by
      have hv := (w j).isLt
      by_cases h0 : (w j).val = 0
      · exact Or.inl (Fin.ext h0)
      · by_cases h1 : (w j).val = 1
        · exact Or.inr (Or.inl (Fin.ext h1))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases hcodes with hleft | hup | hdown
    ·  
      have hgrow := left_step_increases_UL_lower_bound w n j hB hj hleft
      have hNext : kmswStage w (j + 1) = kmswStepOfStep s .left := by
        simp [s, kmswStage, kmswStep, kmswCodeStep, hleft]
      by_cases hnil : s.UL.dropLast.reverse = []
      · have hlen : (s.UL.length : ℕ) ≤ 1 := by
          have hh := congrArg List.length hnil
          simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hh
          omega
        have hpos : 0 < (kmswStage w n).UL.length :=
          List.length_pos_iff.mpr (kmswStage_UL_nonempty_active_last w n).1
        have hULlen : s.UL.length > (kmswStage w n).UL.length := by
          simpa [s] using hgrow
        omega
      · cases hpred : s.UL.dropLast.reverse with
        | nil => exact (hnil hpred).elim
        | cons e es =>
          have hplen : p.length + 1 = (kmswStage w n).UL.length := by
            rw [hUL0]
            simp
          have hq2 : 2 ≤ q.length := by
            have hlen : s.UL.length = p.length + q.length := by
              rw [hUL]
              simp
            have hULlen : s.UL.length > (kmswStage w n).UL.length := by
              simpa [s] using hgrow
            omega
          obtain ⟨r, hqsplit, hULnext⟩ := left_predecessor_suffix p q e es s.nextEdge hq2 hqne (by
            simpa [s, hUL] using hpred)
          have heUL : e ∈ s.UL := by
            apply List.dropLast_subset _
            apply List.mem_reverse.mp
            rw [hpred]
            simp
          have healloc : e < s.nextEdge := by
            apply (kmswStage_boundary_ids_lt_nextEdge w j).2 e
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inl heUL))
          have hqmem : e ∈ q := by rw [hqsplit]; simp
          have hgoodEStage := sectorEdge_at_stage w v a j e (by simpa [s] using healloc)
            (hqgood e hqmem)
          have hnew : sectorEdge w v a s.nextEdge := by
            apply sectorEdge_of_stage w v a (j + 1) s.nextEdge
            · simp [hNext, kmswStepOfStep, hpred, State.addEdge]
            · simpa [hNext, kmswStepOfStep, hpred, State.addEdge] using hgoodEStage.1
            · simpa [hNext, kmswStepOfStep, hpred, State.addEdge] using
                (hactStage.2)
          have hULnext' : (kmswStage w (j + 1)).UL = p ++ (r ++ [s.nextEdge]) := by
            rw [hNext]
            simpa [kmswStepOfStep, hpred, State.addEdge] using hULnext
          have hnextcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
              f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
            intro f hlo hf
            by_cases hold : f < s.nextEdge
            · exact hcreated f hlo (by simpa [s] using hold)
            · have hf' : f = s.nextEdge := by
                have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge + 1 := by
                  simp [hNext, kmswStepOfStep, hpred, State.addEdge]
                omega
              subst f
              exact hnew
          refine ⟨r ++ [s.nextEdge], hULnext', by simp, ?_, ?_, ?_, hnextcreated⟩
          · intro f hf
            simp only [List.mem_append, List.mem_singleton] at hf
            rcases hf with hf | hf
            · have hfq : f ∈ q := by
                rw [hqsplit]
                exact List.mem_append_left _ hf
              exact hqgood f hfq
            · subst f
              exact hnew
          · intro f hf
            have hf' : f ∈ s.UR := by
              simpa [hNext, s, kmswStepOfStep, hpred, State.addEdge] using hf
            exact hURgood f (by simpa [s] using hf')
          · simpa [act, hNext, kmswStepOfStep, hpred, State.addEdge] using hnew
    · -- Up steps replace the active edge and prepend the new missing side.
      have hNext : kmswStage w (j + 1) = kmswStepOfStep s .up := by
        simp [s, kmswStage, kmswStep, kmswCodeStep, hup]
      have hdrop : (p ++ q).dropLast = p ++ q.dropLast := dropLast_append_suffix p q hqne
      have hnew₁ : sectorEdge w v a s.nextEdge := by
        apply sectorEdge_of_stage w v a (j + 1) s.nextEdge
        · simp [hNext, kmswStepOfStep, State.addEdge]
        · simpa [hNext, kmswStepOfStep, State.addEdge] using hactStage.1
        · have hnewv : sectorPoint v a s.nextVertex := by
            unfold sectorPoint
            exact Or.inr hvertex
          simpa [hNext, kmswStepOfStep, State.addEdge] using hnewv
      have hnew₂ : sectorEdge w v a (s.nextEdge + 1) := by
        apply sectorEdge_of_stage w v a (j + 1) (s.nextEdge + 1)
        · simp [hNext, kmswStepOfStep, State.addEdge]
        · have hnewv : sectorPoint v a s.nextVertex := by
            unfold sectorPoint
            exact Or.inr hvertex
          simpa [hNext, kmswStepOfStep, State.addEdge] using hnewv
        · simpa [hNext, kmswStepOfStep, State.addEdge] using hactStage.2
      have hULnext : (kmswStage w (j + 1)).UL = p ++ (q.dropLast ++ [s.nextEdge]) := by
        rw [hNext]
        simp only [kmswStepOfStep]
        rw [hULs]
        simp [hdrop, List.append_assoc]
      have hnewcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
          f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
        intro f hlo hf
        by_cases hold : f < s.nextEdge
        · exact hcreated f hlo (by simpa [s] using hold)
        · have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge + 2 := by
            simp [hNext, kmswStepOfStep, State.addEdge]
          rcases (show f = s.nextEdge ∨ f = s.nextEdge + 1 by omega) with he | he
          · simpa [he] using hnew₁
          · simpa [he] using hnew₂
      refine ⟨q.dropLast ++ [s.nextEdge], hULnext, by simp, ?_, ?_, ?_, hnewcreated⟩
      · intro f hf
        simp only [List.mem_append, List.mem_singleton] at hf
        rcases hf with hf | hf
        · exact hqgood f (List.mem_of_mem_dropLast hf)
        · subst f
          exact hnew₁
      · intro f hf
        simp only [hNext, kmswStepOfStep, List.mem_cons] at hf
        rcases hf with hf | hf
        · subst f
          exact hnew₂
        · exact hURgood f hf
      · simpa [act, hNext, kmswStepOfStep, State.addEdge] using hnew₁
    · -- Down steps either activate UR or create a pendant edge.
      have hNext : kmswStage w (j + 1) = kmswStepOfStep s .down := by
        simp [s, kmswStage, kmswStep, kmswCodeStep, hdown]
      cases hur : s.UR with
      | nil =>
        have hnew : sectorEdge w v a s.nextEdge := by
          apply sectorEdge_of_stage w v a (j + 1) s.nextEdge
          · simp [hNext, kmswStepOfStep, hur, State.addEdge]
          · simpa [hNext, kmswStepOfStep, hur, State.addEdge] using hactStage.2
          · have hnewv : sectorPoint v a s.nextVertex := by
              unfold sectorPoint
              exact Or.inr hvertex
            simpa [hNext, kmswStepOfStep, hur, State.addEdge] using hnewv
        have hULnext : (kmswStage w (j + 1)).UL = p ++ (q ++ [s.nextEdge]) := by
          rw [hNext]
          simp only [kmswStepOfStep, hur]
          rw [hULs]
          simp [List.append_assoc]
        have hnewcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
            f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
          intro f hlo hf
          by_cases hold : f < s.nextEdge
          · exact hcreated f hlo (by simpa [s] using hold)
          · have heq : f = s.nextEdge := by
              have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge + 1 := by
                simp [hNext, kmswStepOfStep, hur, State.addEdge]
              omega
            subst f
            exact hnew
        refine ⟨q ++ [s.nextEdge], hULnext, by simp, ?_, ?_, ?_, hnewcreated⟩
        · intro f hf
          simp only [List.mem_append, List.mem_singleton] at hf
          rcases hf with hf | hf
          · exact hqgood f hf
          · subst f
            exact hnew
        · intro f hf
          have hmem : f ∈ ([] : List ℕ) := by
            simp [hNext, s, kmswStepOfStep, hur, State.addEdge] at hf
          simp at hmem
        · simpa [act, hNext, kmswStepOfStep, hur, State.addEdge] using hnew
      | cons e es =>
        have hgoodE : sectorEdge w v a e := by
          exact hURgood e (by rw [hur]; simp)
        have hULnext : (kmswStage w (j + 1)).UL = p ++ (q ++ [e]) := by
          rw [hNext]
          simp only [kmswStepOfStep, hur]
          rw [hULs]
          simp [List.append_assoc]
        have hnewcreated : ∀ f, (kmswStage w n).nextEdge ≤ f →
            f < (kmswStage w (j + 1)).nextEdge → sectorEdge w v a f := by
          intro f hlo hf
          have hne : (kmswStage w (j + 1)).nextEdge = s.nextEdge := by
            simp [hNext, kmswStepOfStep, hur]
          rw [hne] at hf
          exact hcreated f hlo (by simpa [s] using hf)
        refine ⟨q ++ [e], hULnext, by simp [hqne], ?_, ?_, ?_, hnewcreated⟩
        · intro f hf
          simp only [List.mem_append, List.mem_singleton] at hf
          rcases hf with hf | hf
          · exact hqgood f hf
          · subst f
            exact hgoodE
        · intro f hf
          have hf' : f ∈ es := by
            simpa [hNext, s, kmswStepOfStep, hur] using hf
          have hfUR : f ∈ s.UR := by rw [hur]; exact List.mem_cons_of_mem e hf'
          exact hURgood f (by simpa [s] using hfUR)
        · simpa [act, hNext, kmswStepOfStep, hur] using hgoodE

private theorem no_crossing_of_before_or_v (Before : Set ℕ) (v x y : ℕ)
    (hx : x ∈ Before ∨ x = v) (hy : y ∈ Before ∨ y = v) :
    ¬ (x ∈ Before ∧ y ∉ Before ∧ y ≠ v) ∧
    ¬ (y ∈ Before ∧ x ∉ Before ∧ x ≠ v) := by
  constructor
  · rintro ⟨hxb, hyout, hyv⟩
    rcases hy with hyb | rfl
    · exact hyout hyb
    · exact hyv rfl
  · rintro ⟨hyb, hxout, hxv⟩
    rcases hx with hxb | rfl
    · exact hxout hxb
    · exact hxv rfl

private theorem lt_a_before_or_v (v a nextVertex x : ℕ)
    (ha : a + 1 = nextVertex) (hx : x < a) :
    (x < nextVertex ∧ x ≠ v ∧ x ≠ a) ∨ x = v := by
  by_cases hv : x = v
  · exact Or.inr hv
  · left
    exact ⟨by omega, hv, by omega⟩

private theorem sectorPoint_not_before' (v a nextVertex x : ℕ)
    (ha : a + 1 = nextVertex) (hsector : sectorPoint v a x)
    (hneqV : x ≠ v) : ¬ (x < nextVertex ∧ x ≠ v ∧ x ≠ a) := by
  rintro ⟨hx, hxv, hxa⟩
  rcases hsector with hxv | hxa
  · exact hneqV hxv
  ·
    omega

/-- Edges cannot cross the record vertex between the old and newly allocated
vertex ranges. The hypotheses are the explicit coordinate barriers at `n`. -/
theorem kmswFiniteStage_cutSeparation (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) :
    ∀ m, n ≤ m → ∀ e, e < (kmswStage w m).nextEdge →
      let v := (kmswStage w n).west (act w n)
      let a := (kmswStage w n).east (act w n)
      let Before := {u | u < (kmswStage w n).nextVertex ∧ u ≠ v ∧ u ≠ a}
      (¬ ((kmswStage w m).west e ∈ Before ∧
          (kmswStage w m).east e ∉ Before ∧ (kmswStage w m).east e ≠ v) ∧
       ¬ ((kmswStage w m).east e ∈ Before ∧
          (kmswStage w m).west e ∉ Before ∧ (kmswStage w m).west e ≠ v)) := by
  intro m hnm e he
  dsimp only
  by_cases hn : n = 0
  · subst n
    have hBefore :
        ({u | u < (kmswStage w 0).nextVertex ∧
          u ≠ (kmswStage w 0).west (act w 0) ∧
          u ≠ (kmswStage w 0).east (act w 0)} : Set ℕ) = ∅ := by
      ext u
      simp [kmswStage, kmswInit, act]; omega
    rw [hBefore]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨hdown, hURprev⟩ := record_forces_pendant w n hA hnpos
    let k := n - 1
    have hnk : n = k + 1 := by dsimp [k]; omega
    have hkdown : w k = 2 := by simpa [k] using hdown
    let s₀ := kmswStage w k
    have hURprev' : s₀.UR = [] := by simpa [s₀, k] using hURprev
    let sN := kmswStage w n
    let v := sN.west (act w n)
    let a := sN.east (act w n)
    let Before : Set ℕ := {u | u < sN.nextVertex ∧ u ≠ v ∧ u ≠ a}
    have hStageN : sN = kmswStepOfStep s₀ .down := by
      dsimp [sN, s₀]
      rw [hnk]
      simp [kmswStage, kmswStep, kmswCodeStep, hkdown]
    have hactN : act w n = s₀.nextEdge := by
      change sN.active = s₀.nextEdge
      rw [hStageN]
      simp [kmswStepOfStep, hURprev', State.addEdge]
    have haN : a = s₀.nextVertex := by
      change sN.east (act w n) = s₀.nextVertex
      rw [hStageN, hactN]
      simp [kmswStepOfStep, hURprev', State.addEdge]
    have hnextVertexN : sN.nextVertex = s₀.nextVertex + 1 := by
      rw [hStageN]
      simp [kmswStepOfStep, hURprev', State.addEdge]
    have haSucc : a + 1 = sN.nextVertex := by omega
    have hULlast := kmswStage_UL_last w n
    obtain ⟨xs, hxs⟩ := hULlast
    let p := sN.UL.dropLast
    have hxsN : sN.UL = xs ++ [sN.active] := by simpa [sN] using hxs
    have hactID : sN.active = act w n := rfl
    have hp : p = xs := by
      dsimp [p]
      rw [hxsN]
      simp
    have hUL0 : sN.UL = p ++ [act w n] := by
      rw [hp, hxsN, hactID]
    have hUR0 : sN.UR = [] := by
      rw [hStageN]
      simp [kmswStepOfStep, hURprev', State.addEdge]
    have hact0 : sectorEdge w v a (act w n) := by
      apply sectorEdge_of_stage w v a n (act w n)
      · exact act_lt_nextEdge w (le_refl n)
      · unfold sectorPoint
        exact Or.inl rfl
      · unfold sectorPoint
        exact Or.inr (le_refl _)
    obtain ⟨q, hqUL, hqne, hqgood, hURgood, hactgood, hcreated⟩ :=
      sector_stage_invariant w n v a p hB haSucc hUL0 hUR0 hact0 m hnm
    have holdClassification : ∀ f, f < sN.nextEdge →
        (f = act w n ∨ (sN.west f < a ∧ sN.east f < a)) := by
      intro f hf
      by_cases hfold : f < s₀.nextEdge
      · have hstable := kmswStage_endpoints_stable w (by omega : k ≤ n) hfold
        have hbound := CutConverse.endpoint_bound w k f hfold
        have hwa : sN.west f = s₀.west f := by
          simpa [sN, s₀] using hstable.1
        have hea : sN.east f = s₀.east f := by
          simpa [sN, s₀] using hstable.2
        right
        rw [hwa, hea, haN]
        exact hbound
      · left
        have hnew : sN.nextEdge = s₀.nextEdge + 1 := by
          rw [hStageN]
          simp [kmswStepOfStep, hURprev', State.addEdge]
        have hfEq : f = s₀.nextEdge := by omega
        exact hfEq.trans hactN.symm
    by_cases hold : e < sN.nextEdge
    · have hclass := holdClassification e hold
      have hstable := kmswStage_endpoints_stable w hnm hold
      have hwest : (kmswStage w m).west e = sN.west e := hstable.1
      have heast : (kmswStage w m).east e = sN.east e := hstable.2
      rcases hclass with heq | ⟨hwlt, helt⟩
      · subst e
        have hwestV : (kmswStage w m).west (act w n) = v := by
          rw [hwest]
        have heastA : (kmswStage w m).east (act w n) = a := by
          rw [heast]
        have hvnot : v ∉ Before := by
          intro hv
          exact hv.2.1 rfl
        have hanot : a ∉ Before := by
          intro ha
          exact ha.2.2 rfl
        rw [hwestV, heastA]
        exact ⟨by
          intro h
          exact hvnot h.1,
          by
          intro h
          exact hanot h.1⟩
      · have hwestClass : (kmswStage w m).west e ∈ Before ∨
            (kmswStage w m).west e = v := by
          rw [hwest]
          exact lt_a_before_or_v v a sN.nextVertex (sN.west e) haSucc hwlt
        have heastClass : (kmswStage w m).east e ∈ Before ∨
            (kmswStage w m).east e = v := by
          rw [heast]
          exact lt_a_before_or_v v a sN.nextVertex (sN.east e) haSucc helt
        exact no_crossing_of_before_or_v Before v _ _ hwestClass heastClass
    · have hpost : sectorEdge w v a e := by
        have hlo : sN.nextEdge ≤ e := Nat.le_of_not_gt hold
        apply hcreated e hlo
        exact he
      have hnow : (kmswStage w m).west e = edgeWest w e ∧
          (kmswStage w m).east e = edgeEast w e := edge_endpoints_eq w he
      have hnowGood : sectorPoint v a ((kmswStage w m).west e) ∧
          sectorPoint v a ((kmswStage w m).east e) := by
        constructor
        · rw [hnow.1]
          exact hpost.1
        · rw [hnow.2]
          exact hpost.2
      have hvnot : (kmswStage w m).west e ∉ Before := by
        intro hbefore
        change (kmswStage w m).west e < sN.nextVertex ∧
          (kmswStage w m).west e ≠ v ∧ (kmswStage w m).west e ≠ a at hbefore
        exact (sectorPoint_not_before' v a sN.nextVertex _ haSucc hnowGood.1
          hbefore.2.1) hbefore
      have henot : (kmswStage w m).east e ∉ Before := by
        intro hbefore
        change (kmswStage w m).east e < sN.nextVertex ∧
          (kmswStage w m).east e ≠ v ∧ (kmswStage w m).east e ≠ a at hbefore
        exact (sectorPoint_not_before' v a sN.nextVertex _ haSucc hnowGood.2
          hbefore.2.1) hbefore
      exact ⟨by intro h; exact hvnot h.1, by intro h; exact henot h.1⟩

private theorem stable_edge_no_crossing (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j) (e : ℕ) :
    let v := (kmswStage w n).west (act w n)
    let a := (kmswStage w n).east (act w n)
    let Before := {u | u < (kmswStage w n).nextVertex ∧ u ≠ v ∧ u ≠ a}
    (¬ (edgeWest w e ∈ Before ∧ edgeEast w e ∉ Before ∧ edgeEast w e ≠ v) ∧
     ¬ (edgeEast w e ∈ Before ∧ edgeWest w e ∉ Before ∧ edgeWest w e ≠ v)) := by
  dsimp only
  let m := max n e
  have hself : e < (kmswStage w e).nextEdge := by
    have hcount := CutConverse.allocation_count w e
    omega
  have halloc : e < (kmswStage w m).nextEdge := by
    have hmono := kmswStage_nextEdge_mono w (Nat.le_max_right n e)
    exact hself.trans_le (by simpa [m] using hmono)
  have hsep := kmswFiniteStage_cutSeparation w n hA hB m (Nat.le_max_left n e) e halloc
  have hends := edge_endpoints_eq w halloc
  rw [hends.1, hends.2] at hsep
  exact hsep

private theorem active_east_successor (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) :
    (kmswStage w n).east (act w n) + 1 = (kmswStage w n).nextVertex := by
  by_cases hn : n = 0
  · subst n
    simp [kmswStage, kmswInit, act]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨hdown, hURprev⟩ := record_forces_pendant w n hA hnpos
    let k := n - 1
    have hnk : n = k + 1 := by dsimp [k]; omega
    have hkdown : w k = 2 := by simpa [k] using hdown
    let s₀ := kmswStage w k
    have hURprev' : s₀.UR = [] := by simpa [s₀, k] using hURprev
    have hStageN : kmswStage w n = kmswStepOfStep s₀ .down := by
      rw [hnk]
      rw [kmswStage]
      rw [hkdown]
      rfl
    have hact : act w n = s₀.nextEdge := by
      change (kmswStage w n).active = s₀.nextEdge
      rw [hStageN]
      simp [kmswStepOfStep, hURprev', State.addEdge]
    rw [hStageN, hact]
    simp [kmswStepOfStep, hURprev', State.addEdge]

private theorem chain_endpoints_before (w : ℕ → Fin 3) (Before : Set ℕ) (v : ℕ)
    (es : List ℕ)
    (hchain : List.IsChain (fun e f => edgeEast w e = edgeWest w f) es)
    (hnoV : ∀ e ∈ es, edgeWest w e ≠ v ∧ edgeEast w e ≠ v)
    (hseparate : ∀ e, ¬ (edgeWest w e ∈ Before ∧
      edgeEast w e ∉ Before ∧ edgeEast w e ≠ v))
    (hstart : ∀ hne : es ≠ [], edgeWest w (es.head hne) ∈ Before) :
    ∀ e ∈ es, edgeWest w e ∈ Before ∧ edgeEast w e ∈ Before := by
  induction es with
  | nil =>
    intro e he
    simp at he
  | cons e es ih =>
    intro f hf
    have hfirst : edgeWest w e ∈ Before := by
      simpa using hstart (by simp)
    have hheadNoV := hnoV e (by simp)
    have hlast : edgeEast w e ∈ Before := by
      by_contra hout
      exact hseparate e ⟨hfirst, hout, hheadNoV.2⟩
    rcases List.mem_cons.mp hf with rfl | hft
    · exact ⟨hfirst, hlast⟩
    · have hchainTail : List.IsChain (fun e f => edgeEast w e = edgeWest w f) es :=
        hchain.tail
      have hnoVTail : ∀ f ∈ es, edgeWest w f ≠ v ∧ edgeEast w f ≠ v := by
        intro f hf
        exact hnoV f (List.mem_cons_of_mem e hf)
      have hstartTail : ∀ hne : es ≠ [], edgeWest w (es.head hne) ∈ Before := by
        intro hne
        have hrel : edgeEast w e = edgeWest w (es.head hne) := by
          cases es with
          | nil => exact (hne rfl).elim
          | cons g gs =>
            simpa using hchain.rel_head? (by simp)
        rw [← hrel]
        exact hlast
      exact ih hchainTail hnoVTail hstartTail f hft

/-- A finite directed edge chain starting before the record vertex and reaching
the fresh-vertex range must contain an edge incident to that record vertex.
This is the finite path consequence used in the path-separation argument for -/
theorem kmswFinitePath_meets_recordVertex (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (es : List ℕ) (hne : es ≠ [])
    (hchain : List.IsChain (fun e f => edgeEast w e = edgeWest w f) es)
    (hstart : edgeWest w (es.head hne) ∈
        {u | u < (kmswStage w n).nextVertex ∧
          u ≠ (kmswStage w n).west (act w n) ∧
          u ≠ (kmswStage w n).east (act w n)} ∨
      edgeWest w (es.head hne) = (kmswStage w n).west (act w n))
    (hafter : ∃ e ∈ es,
      (kmswStage w n).east (act w n) ≤ edgeWest w e ∨
      (kmswStage w n).east (act w n) ≤ edgeEast w e) :
    ∃ e ∈ es,
      edgeWest w e = (kmswStage w n).west (act w n) ∨
      edgeEast w e = (kmswStage w n).west (act w n) := by
  let v := (kmswStage w n).west (act w n)
  let a := (kmswStage w n).east (act w n)
  let Before : Set ℕ := {u | u < (kmswStage w n).nextVertex ∧ u ≠ v ∧ u ≠ a}
  have haSucc : a + 1 = (kmswStage w n).nextVertex := by
    dsimp [a]
    exact active_east_successor w n hA
  by_contra hmiss
  have hnoV : ∀ e ∈ es, edgeWest w e ≠ v ∧ edgeEast w e ≠ v := by
    intro e he
    constructor
    · intro hW
      apply hmiss
      exact ⟨e, he, Or.inl hW⟩
    · intro hE
      apply hmiss
      exact ⟨e, he, Or.inr hE⟩
  have hstartBefore : edgeWest w (es.head hne) ∈ Before := by
    rcases hstart with hbefore | hv
    · simpa [Before, v, a] using hbefore
    · exact False.elim ((hnoV _ (List.head_mem hne)).1 hv)
  have hseparate : ∀ e, ¬ (edgeWest w e ∈ Before ∧
      edgeEast w e ∉ Before ∧ edgeEast w e ≠ v) := by
    intro e
    exact (stable_edge_no_crossing w n hA hB e).1
  have hall := chain_endpoints_before w Before v es hchain hnoV hseparate
    (fun _ => hstartBefore)
  obtain ⟨e, he, hor⟩ := hafter
  have hWbefore : edgeWest w e ∈ Before := (hall e he).1
  have hEbefore : edgeEast w e ∈ Before := (hall e he).2
  change edgeWest w e < (kmswStage w n).nextVertex ∧
    edgeWest w e ≠ (kmswStage w n).west (act w n) ∧
    edgeWest w e ≠ (kmswStage w n).east (act w n) at hWbefore
  change edgeEast w e < (kmswStage w n).nextVertex ∧
    edgeEast w e ≠ (kmswStage w n).west (act w n) ∧
    edgeEast w e ≠ (kmswStage w n).east (act w n) at hEbefore
  change (kmswStage w n).east (act w n) + 1 =
    (kmswStage w n).nextVertex at haSucc
  rcases hor with hor | hor
  · change (kmswStage w n).east (act w n) ≤ edgeWest w e at hor
    omega
  · change (kmswStage w n).east (act w n) ≤ edgeEast w e at hor
    omega

end DirectedDistances.KMSW
