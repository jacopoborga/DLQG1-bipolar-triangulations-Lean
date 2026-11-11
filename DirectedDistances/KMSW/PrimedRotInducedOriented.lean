module

public import DirectedDistances.KMSW.PrimedDartMapOriented
import DirectedDistances.KMSW.HatInducedExit

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap



theorem primedDartMapOriented_present (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hd : ¬ (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present
      d.1.val = false) :
    ¬ (kmswRootedStage w (primedStageTime w h m)).map.missing
      (primedDartMapOriented w h m d) := by
  rw [primedDartMapOriented_eq_of_present w h m d (Bool.eq_true_of_not_eq_false hd)]
  exact primedDartMap_present w h m d hd



theorem primedDartMapOriented_tail (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hd : ¬ (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present
      d.1.val = false) :
    ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).present
        d.1.val = true ∧ d.2 = false) ↔
      (kmswRootedStage w (primedStageTime w h m)).map.tail
        (primedDartMapOriented w h m d) := by
  rw [primedDartMapOriented_eq_of_present w h m d (Bool.eq_true_of_not_eq_false hd)]
  exact primedDartMap_tail w h m d hd




theorem primedDartMapOriented_root (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : 1 ≤ m) :
    primedDartMapOriented w h m
      (⟨(kmswMissingRootStage (primedCode (primedSimInput w) h) m).active, by
        have ha := (kmswStage_boundary_ids_lt_nextEdge
          (primedCode (primedSimInput w) h) m).1
        obtain ⟨_, he, _, _, _, _, ha', _⟩ :=
          kmswMissingRootStage_agree (primedCode (primedSimInput w) h) m
        rw [he, ha']
        exact ha⟩, false) =
      (kmswRootedStage w (primedStageTime w h m)).root := by
  rw [primedDartMapOriented_eq_of_present w h m _ (primed_active_present w h m hm)]
  exact primedDartMap_root w h m hm

private theorem oriented_index_bounds (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0) :
    let k := primedIntervalIndex (primedSimInput w) h (m - 1)
    primedIntervalBase (primedSimInput w) h k < m ∧
      m ≤ primedIntervalBase (primedSimInput w) h (k + 1) := by
  dsimp only
  constructor
  · cases hk : primedIntervalIndex (primedSimInput w) h (m - 1) with
    | zero => rw [primedIntervalBase_zero]; omega
    | succ j =>
      have hn := Nat.find_min (primedIntervalIndex_exists (primedSimInput w) h (m - 1))
        (show j < Nat.find (primedIntervalIndex_exists (primedSimInput w) h (m - 1)) by
          change j < primedIntervalIndex (primedSimInput w) h (m - 1)
          omega)
      omega
  · have hi := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
    omega

private theorem oriented_ordinary_alignment (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)) :
    primedStageTime w h (m + 1) = primedStageTime w h m + 1 ∧
      primedCode (primedSimInput w) h m = w (primedStageTime w h m) := by
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  obtain ⟨hl, hr⟩ := oriented_index_bounds w h m hm
  change primedIntervalBase (primedSimInput w) h k < m at hl
  change m ≤ primedIntervalBase (primedSimInput w) h (k + 1) at hr
  change m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
  have ht0 := primedStageTime_block w h k m hl hr
  have ht1 := primedStageTime_block w h k (m + 1) (by omega) (by omega)
  constructor
  · rw [ht1, ht0]
    omega
  · have hc := primedCode_positive_offset (primedSimInput w) h k
      (m - primedIntervalBase (primedSimInput w) h k) (by omega) (by
        rw [primedIntervalBase_succ] at ho
        omega)
    have hsum : primedIntervalBase (primedSimInput w) h k +
        (m - primedIntervalBase (primedSimInput w) h k) = m := by omega
    rw [hsum] at hc
    change primedCode (primedSimInput w) h m =
      w (walkNL w h k + (m - primedIntervalBase (primedSimInput w) h k) - 1) at hc
    rw [← ht0] at hc
    exact hc

private theorem oriented_present_no_flip (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hp : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e.val = true) :
    primedSideFlip w h m e = false := by
  cases hf : primedSideFlip w h m e with
  | false => rfl
  | true =>
    have hh := primedSideFlip_true_missing w h m e hf
    rw [hp] at hh
    cases hh

private theorem oriented_ordinary_new (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1)).nextEdge)
    (he : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ≤ e.val) :
    primedSideFlip w h (m + 1) e = false := by
  let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) m
  let gl := kmswStage w (primedStageTime w h m)
  change sh.nextEdge ≤ e.val at he
  obtain ⟨ht, hcode⟩ := oriented_ordinary_alignment w h m hm ho
  obtain ⟨k, hs, _⟩ := primedAll_sim w h m (by omega)
  have hb := e.isLt
  generalize hc : primedCode (primedSimInput w) h m = c
  have hl : kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1) =
      kmswStepOfStep sh (kmswCodeStep c) := by
    change kmswStep sh (primedCode (primedSimInput w) h m) = _
    rw [hc]
    rfl
  have hg : kmswStage w (primedStageTime w h (m + 1)) =
      kmswStepOfStep gl (kmswCodeStep c) := by
    rw [ht]
    change kmswStep gl (w (primedStageTime w h m)) = _
    rw [← hcode, hc]
    rfl
  fin_cases c
  · change kmswMissingRootStage _ (m + 1) = kmswStepOfStep sh .left at hl
    change kmswStage w _ = kmswStepOfStep gl .left at hg
    cases hp : sh.UL.dropLast.reverse with
    | nil =>
      have hgp : gl.UL.dropLast.reverse = [] := by
        have hh := hs.forget.left_predecessors
        change sh.UL.dropLast.reverse.map _ = gl.UL.dropLast.reverse at hh
        rw [hp, List.map_nil] at hh
        exact hh.symm
      simp only [hl, kmswStepOfStep, hp, State.addEdge] at hb
      rcases (show e.val = sh.nextEdge ∨ e.val = sh.nextEdge + 1 by omega) with heq | heq
      · apply oriented_present_no_flip
        simp [hl, kmswStepOfStep, hp, State.addEdge, heq]
      · simp [primedSideFlip, primedAllVertexMap, primedAllEdgeMap, hm, ho,
          hc, primedOrdinaryStepVertexMap, primedOrdinaryStepEdgeMap,
          primedOrdinaryLeftVertexMap, primedOrdinaryLeftEdgeMap,
          show (kmswMissingRootStage (primedCode (primedSimInput w) h) m) = sh from rfl,
          show kmswStage w (primedStageTime w h m) = gl from rfl,
          hl, hg, hp, hgp, kmswStepOfStep, State.addEdge, heq,
          kmswShiftUpVertexMap, kmswShiftUpEdgeMap]
    | cons a as =>
      simp only [hl, kmswStepOfStep, hp, State.addEdge] at hb
      have heq : e.val = sh.nextEdge := by omega
      apply oriented_present_no_flip
      simp [hl, kmswStepOfStep, hp, State.addEdge, heq]
  · change kmswMissingRootStage _ (m + 1) = kmswStepOfStep sh .up at hl
    change kmswStage w _ = kmswStepOfStep gl .up at hg
    simp only [hl, kmswStepOfStep, State.addEdge] at hb
    rcases (show e.val = sh.nextEdge ∨ e.val = sh.nextEdge + 1 by omega) with heq | heq
    · apply oriented_present_no_flip
      simp [hl, kmswStepOfStep, State.addEdge, heq]
    · simp [primedSideFlip, primedAllVertexMap, primedAllEdgeMap, hm, ho,
        hc, primedOrdinaryStepVertexMap, primedOrdinaryStepEdgeMap,
        show (kmswMissingRootStage (primedCode (primedSimInput w) h) m) = sh from rfl,
        show kmswStage w (primedStageTime w h m) = gl from rfl,
        hl, hg, kmswStepOfStep, State.addEdge, heq,
        kmswShiftUpVertexMap, kmswShiftUpEdgeMap]
  · change kmswMissingRootStage _ (m + 1) = kmswStepOfStep sh .down at hl
    cases hp : sh.UR with
    | nil =>
      simp only [hl, kmswStepOfStep, hp, State.addEdge] at hb
      have heq : e.val = sh.nextEdge := by omega
      apply oriented_present_no_flip
      simp [hl, kmswStepOfStep, hp, State.addEdge, heq]
    | cons a as =>
      simp only [hl, kmswStepOfStep, hp] at hb
      omega

private theorem oriented_crossing_new (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : ¬ m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1)).nextEdge)
    (he : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ≤ e.val) :
    primedSideFlip w h (m + 1) e =
      decide (e.val = (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge + 1) := by
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  obtain ⟨_, hr⟩ := oriented_index_bounds w h m hm
  have hB : m = primedIntervalBase (primedSimInput w) h (k + 1) := by
    change m = primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)
    omega
  have hc : primedCode (primedSimInput w) h m = 1 := by
    rw [hB]
    exact (primedCrossing_codes w h k).1
  have ht : primedStageTime w h (m + 1) = walkNL w h (k + 1) := by
    rw [hB]
    exact primedStageTime_after_crossing w h (k + 1)
  have hl : kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1) =
      kmswStepOfStep sh .up := by
    change kmswStep sh (primedCode (primedSimInput w) h m) = _
    rw [hc]
    rfl
  have hn := walkNL_spec w h (k + 1)
  have hg : kmswStage w (primedStageTime w h (m + 1)) =
      kmswStepOfStep gl .left := by
    rw [ht]
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ walkNL w h (k + 1) by omega)]
    change kmswStep gl (w (walkNL w h (k + 1) - 1)) = _
    rw [walkNL_previous_code w h (k + 1)]
    rfl
  obtain ⟨a, as, hp⟩ := List.exists_cons_of_ne_nil
    (primedCrossing_exit_predecessor_nonempty w h (k + 1) (by omega))
  change gl.UL.dropLast.reverse = a :: as at hp
  have ha : gl.active < gl.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w (walkNL w h (k + 1) - 1)).1
  have hne : gl.east gl.active ≠ gl.west gl.active := by
    intro hh
    exact (activeEast_ne_activeInitial w
      (j := walkNL w h (k + 1) - 1) (n := walkNL w h (k + 1) - 1) le_rfl)
      (hh.trans (edge_endpoints_eq w ha).1)
  change sh.nextEdge ≤ e.val at he
  have hb : e.val < sh.nextEdge + 2 := by
    simpa only [hl, kmswStepOfStep, State.addEdge] using e.isLt
  rcases (show e.val = sh.nextEdge ∨ e.val = sh.nextEdge + 1 by omega) with heq | heq
  · rw [oriented_present_no_flip w h (m + 1) e (by
      simp [hl, kmswStepOfStep, State.addEdge, heq])]
    simp only [heq, show (kmswMissingRootStage (primedCode (primedSimInput w) h) m) = sh from rfl,
      show sh.nextEdge ≠ sh.nextEdge + 1 from by omega, decide_false]
  · change primedSideFlip w h (m + 1) e = decide (e.val = sh.nextEdge + 1)
    simp [primedSideFlip, primedAllVertexMap, primedAllEdgeMap, hm, ho,
      show (kmswMissingRootStage (primedCode (primedSimInput w) h) m) = sh from rfl,
      show kmswStage w (walkNL w h
        (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) - 1) = gl from rfl,
      hl, hg, kmswStepOfStep, hp, State.addEdge, heq,
      primedCrossingVertexMap, primedCrossingEdgeMap, ne_of_lt ha, hne]




theorem primedSideFlip_eq_true_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedSideFlip w h m e = true ↔
      ∃ k, primedIntervalBase (primedSimInput w) h k < m ∧
        e.val = (kmswMissingRootStage (primedCode (primedSimInput w) h)
          (primedIntervalBase (primedSimInput w) h k)).nextEdge + 1 := by
  have mono {a b : ℕ} (hab : a ≤ b) :
      (kmswMissingRootStage (primedCode (primedSimInput w) h) a).nextEdge ≤
        (kmswMissingRootStage (primedCode (primedSimInput w) h) b).nextEdge := by
    rw [(kmswMissingRootStage_agree (primedCode (primedSimInput w) h) a).2.1,
      (kmswMissingRootStage_agree (primedCode (primedSimInput w) h) b).2.1]
    exact kmswStage_nextEdge_mono _ hab
  have born (k : ℕ) :
      (kmswMissingRootStage (primedCode (primedSimInput w) h)
        (primedIntervalBase (primedSimInput w) h k)).nextEdge + 1 <
      (kmswMissingRootStage (primedCode (primedSimInput w) h)
        (primedIntervalBase (primedSimInput w) h k + 1)).nextEdge := by
    have hc : primedCode (primedSimInput w) h
        (primedIntervalBase (primedSimInput w) h k) = 1 := by
      cases k with
      | zero => rw [primedIntervalBase_zero]; exact primedCode_zero _ h
      | succ k => exact (primedCrossing_codes w h k).1
    simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  induction m with
  | zero =>
    rw [primedSideFlip_zero]
    constructor
    · intro hh; cases hh
    · rintro ⟨k, hk, _⟩; omega
  | succ m ih =>
    by_cases hold : e.val < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge
    · let e0 : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge :=
        ⟨e.val, hold⟩
      have hf : primedSideFlip w h (m + 1) e = primedSideFlip w h m e0 :=
        primedSideFlip_compatible w h m e0
      rw [hf]
      apply (ih e0).trans
      constructor
      · rintro ⟨k, hk, he⟩
        exact ⟨k, by omega, he⟩
      · rintro ⟨k, hk, he⟩
        have hkm : primedIntervalBase (primedSimInput w) h k < m := by
          by_contra hn
          have hb : primedIntervalBase (primedSimInput w) h k = m := by omega
          rw [hb] at he
          omega
        exact ⟨k, hkm, he⟩
    · have hnew : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ≤
          e.val := by omega
      have hrhs :
          (∃ k, primedIntervalBase (primedSimInput w) h k < m + 1 ∧
            e.val = (kmswMissingRootStage (primedCode (primedSimInput w) h)
              (primedIntervalBase (primedSimInput w) h k)).nextEdge + 1) ↔
          (∃ k, primedIntervalBase (primedSimInput w) h k = m ∧
            e.val = (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge + 1) := by
        constructor
        · rintro ⟨k, hk, he⟩
          have hb : primedIntervalBase (primedSimInput w) h k = m := by
            by_contra hn
            have hkm : primedIntervalBase (primedSimInput w) h k + 1 ≤ m := by omega
            have hb := born k
            have hm := mono hkm
            omega
          exact ⟨k, hb, by simpa only [hb] using he⟩
        · rintro ⟨k, hk, he⟩
          exact ⟨k, by omega, by simpa only [hk] using he⟩
      rw [hrhs]
      by_cases hm : m = 0
      · subst m
        rw [primedSideFlip_one]
        simp only [decide_eq_true_eq]
        constructor
        · intro he
          refine ⟨0, primedIntervalBase_zero _ h, ?_⟩
          exact he
        · rintro ⟨_, _, he⟩
          exact he
      · let k := primedIntervalIndex (primedSimInput w) h (m - 1)
        obtain ⟨hl, hr⟩ := oriented_index_bounds w h m hm
        change primedIntervalBase (primedSimInput w) h k < m at hl
        change m ≤ primedIntervalBase (primedSimInput w) h (k + 1) at hr
        by_cases ho : m < primedIntervalBase (primedSimInput w) h
            (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)
        · rw [oriented_ordinary_new w h m hm ho e hnew]
          constructor
          · intro hh; cases hh
          · rintro ⟨j, hj, _⟩
            by_cases hjk : j ≤ k
            · have hb := primedIntervalBase_mono (primedSimInput w) h hjk
              omega
            · have hb := primedIntervalBase_mono (primedSimInput w) h
                (show k + 1 ≤ j by omega)
              change m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
              omega
        · rw [oriented_crossing_new w h m hm ho e hnew, decide_eq_true_eq]
          have hB : primedIntervalBase (primedSimInput w) h (k + 1) = m := by
            change ¬ m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
            omega
          constructor
          · intro he
            exact ⟨k + 1, hB, he⟩
          · rintro ⟨_, _, he⟩
            exact he

private theorem oriented_canonical_sim (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0) :
    PrimedSimActiveRootLR (primedCode (primedSimInput w) h) w h
      (primedIntervalIndex (primedSimInput w) h (m - 1)) m
      (primedStageTime w h m) (primedAllEdgeMap w h m) (primedAllVertexMap w h m) := by
  have hshift : StrictMono (fun j : ℕ =>
      (walkNL w h j : ℤ) - (primedIntervalBase (primedSimInput w) h j : ℤ)) := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hb := primedIntervalBase_succ (primedSimInput w) h j
    change primedIntervalBase (primedSimInput w) h (j + 1) =
      primedIntervalBase (primedSimInput w) h j +
        (walkNR w h (j + 1) - walkNL w h j) at hb
    have hr := (walkNR_succ_spec w h j).1
    have hl := (walkNL_spec w h (j + 1)).1
    omega
  obtain ⟨k, hs, _⟩ := primedAll_sim w h m (by omega)
  let q := primedIntervalIndex (primedSimInput w) h (m - 1)
  have hb := hs.forget.after_base
  have ht := hs.forget.time_alignment
  change primedStageTime w h m = walkNL w h k +
    (m - primedIntervalBase (primedSimInput w) h k) - 1 at ht
  obtain ⟨hl, hr⟩ := oriented_index_bounds w h m hm
  have hq := primedStageTime_block w h q m hl hr
  have heq : (walkNL w h k : ℤ) - (primedIntervalBase (primedSimInput w) h k : ℤ) =
      (walkNL w h q : ℤ) - (primedIntervalBase (primedSimInput w) h q : ℤ) := by
    change primedIntervalBase (primedSimInput w) h q < m at hl
    omega
  have hk : k = q := hshift.injective heq
  simpa only [hk] using hs

private theorem oriented_transport_return {k k' l l' : ℕ}
    (hk : k' = k) (hl : l' = l)
    (σ : Equiv.Perm (StageDart k)) (σ' : Equiv.Perm (StageDart k'))
    (ρ : Equiv.Perm (StageDart l)) (ρ' : Equiv.Perm (StageDart l'))
    (i : StageDart k → StageDart l) (i' : StageDart k' → StageDart l')
    (hσ : StageRotation.resize hk σ' = σ)
    (hρ : StageRotation.resize hl ρ' = ρ)
    (hi : ∀ d, (Fin.cast hl (i' d).1, (i' d).2) = i (Fin.cast hk d.1, d.2))
    (ih : ∀ d, ∃ n : ℕ, 0 < n ∧ (ρ : _ → _)^[n] (i d) = i (σ d) ∧
      ∀ j : ℕ, 0 < j → j < n → (ρ : _ → _)^[j] (i d) ∉ Set.range i) :
    ∀ d, ∃ n : ℕ, 0 < n ∧ (ρ' : _ → _)^[n] (i' d) = i' (σ' d) ∧
      ∀ j : ℕ, 0 < j → j < n → (ρ' : _ → _)^[j] (i' d) ∉ Set.range i' := by
  cases hk
  cases hl
  change σ' = σ at hσ
  change ρ' = ρ at hρ
  subst σ'
  subst ρ'
  have he : i' = i := funext hi
  subst i'
  exact ih




theorem primedRotInducedOriented_step_down (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hc : primedCode (primedSimInput w) h m = 2)
    (ih : PrimedRotInducedOrientedAt w h m) :
    PrimedRotInducedOrientedAt w h (m + 1) := by
  let u := primedCode (primedSimInput w) h
  let n := primedStageTime w h m
  let q := primedIntervalIndex (primedSimInput w) h (m - 1)
  have hm : m ≠ 0 := by
    intro hz
    subst m
    rw [primedCode_zero] at hc
    cases hc
  obtain ⟨_, hb⟩ := oriented_index_bounds w h m hm
  have ho : m < primedIntervalBase (primedSimInput w) h (q + 1) := by
    change m ≤ primedIntervalBase (primedSimInput w) h (q + 1) at hb
    by_contra hn
    have he : m = primedIntervalBase (primedSimInput w) h (q + 1) := by omega
    have hh := (primedCrossing_codes w h q).1
    rw [← he, hc] at hh
    cases hh
  obtain ⟨ht, hcode⟩ := oriented_ordinary_alignment w h m hm ho
  have hw : w n = 2 := hcode.symm.trans hc
  have hcl : kmswCodeStep (u m) = .down := by
    change kmswCodeStep (primedCode (primedSimInput w) h m) = .down
    rw [hc]
    rfl
  have hcr : kmswCodeStep (w n) = .down := by rw [hw]; rfl
  have hs := oriented_canonical_sim w h m hm
  have ho' : m < primedIntervalBase (primedSimInput w) h q +
      primedIntervalWidth (primedSimInput w) h q := by
    rw [← primedIntervalBase_succ]
    exact ho
  obtain ⟨a, as, bs, hlocal, hglobal, _⟩ := hs.forget.down_heads ho' hw
  change (kmswStage w n).UR = primedAllEdgeMap w h m a :: bs at hglobal
  obtain ⟨_, he0, _, _, _, _, _, _, hur0, _, _⟩ := kmswMissingRootStage_agree u m
  have he1 := (kmswMissingRootStage_agree u (m + 1)).2.1
  have hlocal' : (kmswStage u m).UR = a :: as := by
    rw [← hur0]
    exact hlocal
  have hk0 : (kmswStage u (m + 1)).nextEdge = (kmswStage u m).nextEdge := by
    simp only [kmswStage, kmswStep, hcl, kmswStepOfStep, hlocal']
  have hk : (kmswMissingRootStage u (m + 1)).nextEdge =
      (kmswMissingRootStage u m).nextEdge := he1.trans (hk0.trans he0.symm)
  have hl : (kmswStage w (primedStageTime w h (m + 1))).nextEdge =
      (kmswStage w n).nextEdge := by
    rw [ht]
    change (kmswStep (kmswStage w n) (w n)).nextEdge = _
    simp only [kmswStep, hcr, kmswStepOfStep, hglobal]
  unfold PrimedRotInducedOrientedAt at ih ⊢
  apply oriented_transport_return hk hl
    (primedLocalRot u m) (primedLocalRot u (m + 1))
    (stageRot w n) (stageRot w (primedStageTime w h (m + 1)))
    (primedDartMapOriented w h m) (primedDartMapOriented w h (m + 1))
  · have hrot := StageRotation.step_activation (kmswStage u m)
      (act_lt_nextEdge u le_rfl) (stageRotation_UL_bound u m) (stageRot u m)
      (u m) hcl a as hlocal'
    have hrot' : StageRotation.resize hk0 (stageRot u (m + 1)) = stageRot u m := hrot
    have twice {a b c : ℕ} (hab : a = b) (hbc : b = c)
        (σ : Equiv.Perm (StageDart a)) :
        StageRotation.resize hbc (StageRotation.resize hab σ) =
          StageRotation.resize (hab.trans hbc) σ := by
      cases hab
      cases hbc
      rfl
    have hh := congrArg (StageRotation.resize he0.symm) hrot'
    simpa only [primedLocalRot, twice] using hh
  · have hr := StageRotation.step_activation (kmswStage w n)
      (act_lt_nextEdge w le_rfl) (stageRotation_UL_bound w n) (stageRot w n)
      (w n) hcr _ _ hglobal
    revert hl
    rw [ht]
    intro hl
    exact hr
  · intro d
    let d0 : StageDart (kmswMissingRootStage u m).nextEdge :=
      (Fin.cast hk d.1, d.2)
    have hh := primedDartMapOriented_compatible w h m d0
    have hd : outerSucc_castDart (primedLocal_nextEdge_succ_le u m) d0 = d := by
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    rw [hd] at hh
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z => z.1.val) hh)
    · exact congrArg (fun z : StageDart
        (kmswStage w (primedStageTime w h (m + 1))).nextEdge => z.2) hh
  · exact ih

 
private theorem oriented_pair_old {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F)
    (hx : τ x = x) (hxy : x ≠ y) (d : D) :
    StageRotation.pairSplice σ τ a b x y (.inl d) =
      if d = a then .inr x else if σ d = b then .inr y else .inl (σ d) := by
  by_cases hda : d = a
  · subst d
    simp [StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hx, hxy]
  · by_cases hdb : σ d = b <;>
      simp [StageRotation.pairSplice, insertBefore, insertAfter,
        Equiv.swap_apply_def, hda, hdb]

 
private theorem oriented_pair_path {D E F : Type*}
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (ρ : Equiv.Perm E) (τ : Equiv.Perm F) (i : D → E)
    (a b : D) (x y : F) (hx : τ x = x) (hxy : x ≠ y)
    (d : D) (k : ℕ) (_hk : 0 < k)
    (hgap : ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i)
    (z : E ⊕ F)
    (hz : StageRotation.pairSplice ρ τ (i a) (i b) x y z =
      if ρ (i d) = i b then .inr y else .inl (ρ (i d))) :
    ∀ j, 0 < j → j ≤ k →
      (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[j] z =
        if (ρ : E → E)^[j] (i d) = i b then .inr y
        else .inl ((ρ : E → E)^[j] (i d)) := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ih =>
    intro hj hjk
    cases j with
    | zero => exact hz
    | succ j =>
      have hlt : j + 1 < k := by omega
      have hn := hgap (j + 1) (by omega) hlt
      have hna : (ρ : E → E)^[j + 1] (i d) ≠ i a :=
        fun he => hn ⟨a, he.symm⟩
      have hnb : (ρ : E → E)^[j + 1] (i d) ≠ i b :=
        fun he => hn ⟨b, he.symm⟩
      rw [Function.iterate_succ_apply', ih (by omega) (by omega), ite_eq_right hnb,
        oriented_pair_old ρ τ (i a) (i b) x y hx hxy _, ite_eq_right hna]
      simp only [Function.iterate_succ_apply']

 
private theorem oriented_pair_induced {D E F : Type*}
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (τ : Equiv.Perm F)
    (i : D → E) (hi : Function.Injective i) (a b : D) (x y : F)
    (hx : τ x = x) (hy : τ y = y) (hxy : x ≠ y)
    (ih : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i (σ d) ∧
      ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i) :
    ∀ d : D ⊕ F, ∃ k : ℕ, 0 < k ∧
      (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[k]
        (Sum.map i id d) =
          Sum.map i id (StageRotation.pairSplice σ τ a b x y d) ∧
      ∀ j, 0 < j → j < k →
        (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[j]
          (Sum.map i id d) ∉ Set.range (Sum.map i (id : F → F)) := by
  have corridor (d : D) (z : E ⊕ F)
      (hz : StageRotation.pairSplice ρ τ (i a) (i b) x y z =
        if ρ (i d) = i b then .inr y else .inl (ρ (i d))) :
      ∃ k : ℕ, 0 < k ∧
        (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[k] z =
          (if σ d = b then .inr y else .inl (i (σ d))) ∧
        ∀ j, 0 < j → j < k →
          (StageRotation.pairSplice ρ τ (i a) (i b) x y : _ → _)^[j] z ∉
            Set.range (Sum.map i (id : F → F)) := by
    obtain ⟨k, hk, he, hg⟩ := ih d
    have hp := oriented_pair_path ρ τ i a b x y hx hxy d k hk hg z hz
    refine ⟨k, hk, ?_, ?_⟩
    · rw [hp k hk le_rfl, he]
      simp only [hi.eq_iff]
    · intro j hj hjk hm
      have hn := hg j hj hjk
      have hnb : (ρ : E → E)^[j] (i d) ≠ i b := fun he => hn ⟨b, he.symm⟩
      rw [hp j hj (by omega), ite_eq_right hnb] at hm
      obtain ⟨e, he⟩ := hm
      cases e with
      | inl e => exact hn ⟨e, Sum.inl.inj he⟩
      | inr e => cases he
  intro d
  cases d with
  | inl d =>
    by_cases hda : d = a
    · subst d
      refine ⟨1, by omega, ?_, ?_⟩
      · simp only [Function.iterate_one, Sum.map_inl, oriented_pair_old ρ τ (i a) (i b) x y hx hxy,
          oriented_pair_old σ τ a b x y hx hxy, ite_true, Sum.map_inr, id_eq]
      · intro j hj hjk; omega
    · have hia : i d ≠ i a := fun he => hda (hi he)
      obtain ⟨k, hk, he, hg⟩ := corridor d (.inl (i d)) (by
        rw [oriented_pair_old ρ τ (i a) (i b) x y hx hxy, ite_eq_right hia])
      refine ⟨k, hk, ?_, hg⟩
      rw [oriented_pair_old σ τ a b x y hx hxy, ite_eq_right hda]
      simpa only [Sum.map_inl, Sum.map_inr, id_eq, apply_ite] using he
  | inr z =>
    by_cases hzx : z = x
    · subst z
      have hxval (η : Equiv.Perm D) :
          StageRotation.pairSplice η τ a b x y (.inr x) =
            if η a = b then .inr y else .inl (η a) := by
        by_cases hab : η a = b <;>
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hab]
      have hxval' : StageRotation.pairSplice ρ τ (i a) (i b) x y (.inr x) =
          if ρ (i a) = i b then .inr y else .inl (ρ (i a)) := by
        by_cases hab : ρ (i a) = i b <;>
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hab]
      obtain ⟨k, hk, he, hg⟩ := corridor a (.inr x) hxval'
      refine ⟨k, hk, ?_, hg⟩
      rw [hxval]
      simpa only [Sum.map_inr, id_eq, Sum.map_inl, apply_ite] using he
    · refine ⟨1, by omega, ?_, ?_⟩
      · simp only [Function.iterate_one, Sum.map_inr, id_eq]
        by_cases hzy : z = y
        · subst z
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hy, hzx]
        · have hτzy : τ z ≠ y := fun he => hzy (τ.injective (he.trans hy.symm))
          simp [StageRotation.pairSplice, insertBefore, insertAfter,
            Equiv.swap_apply_def, hzx, hτzy]
      · intro j hj hjk; omega

 
private theorem oriented_congr_return {D E D' E' : Type*}
    (e : D ≃ D') (f : E ≃ E')
    (σ : Equiv.Perm D) (ρ : Equiv.Perm E)
    (σ' : Equiv.Perm D') (ρ' : Equiv.Perm E')
    (i : D → E) (i' : D' → E')
    (hs : ∀ d, σ' (e d) = e (σ d))
    (hr : ∀ d, ρ' (f d) = f (ρ d))
    (hi : ∀ d, i' (e d) = f (i d))
    (ih : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i (σ d) ∧
      ∀ j, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i) :
    ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ' : E' → E')^[k] (i' d) = i' (σ' d) ∧
      ∀ j, 0 < j → j < k → (ρ' : E' → E')^[j] (i' d) ∉ Set.range i' := by
  have ht (n : ℕ) (d : E) : (ρ' : E' → E')^[n] (f d) = f ((ρ : E → E)^[n] d) := by
    induction n with
    | zero => rfl
    | succ n hn => rw [Function.iterate_succ_apply', hn, hr, Function.iterate_succ_apply']
  intro d
  obtain ⟨d, rfl⟩ := e.surjective d
  obtain ⟨k, hk, he, hg⟩ := ih d
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hi, ht, he, hs, hi]
  · intro j hj hjk hm
    obtain ⟨z, hz⟩ := hm
    obtain ⟨z, rfl⟩ := e.surjective z
    rw [hi, hi, ht] at hz
    exact hg j hj hjk ⟨z, f.injective hz⟩


 
private theorem oriented_resize_twice {a b c : ℕ} (hab : a = b) (hbc : b = c)
    (σ : Equiv.Perm (StageDart a)) :
    StageRotation.resize hbc (StageRotation.resize hab σ) =
      StageRotation.resize (hab.trans hbc) σ := by
  cases hab
  cases hbc
  rfl

 
private theorem oriented_resize_up {a b : ℕ} (hab : a = b)
    (σ : Equiv.Perm (StageDart a)) (x y : StageDart a) :
    StageRotation.resize (congrArg (· + 2) hab) (StageRotation.up a σ x y) =
      StageRotation.up b (StageRotation.resize hab σ)
        (Fin.cast hab x.1, x.2) (Fin.cast hab y.1, y.2) := by
  cases hab
  rfl

 
private theorem oriented_local_up (u : ℕ → Fin 3) (m : ℕ) (hc : u m = 1)
    (ha : (kmswMissingRootStage u m).active < (kmswMissingRootStage u m).nextEdge)
    (hk : (kmswMissingRootStage u (m + 1)).nextEdge =
      (kmswMissingRootStage u m).nextEdge + 2) :
    StageRotation.resize hk (primedLocalRot u (m + 1)) =
      StageRotation.up (kmswMissingRootStage u m).nextEdge (primedLocalRot u m)
        (⟨(kmswMissingRootStage u m).active, ha⟩, false)
        (⟨(kmswMissingRootStage u m).active, ha⟩, true) := by
  have he0 := (kmswMissingRootStage_agree u m).2.1
  have he1 := (kmswMissingRootStage_agree u (m + 1)).2.1
  obtain ⟨_, _, _, _, _, _, ha0, _⟩ := kmswMissingRootStage_agree u m
  have hcl : kmswCodeStep (u m) = .up := by rw [hc]; rfl
  have hr := StageRotation.step_up (kmswStage u m) (act_lt_nextEdge u le_rfl)
    (stageRotation_UL_bound u m) (stageRot u m) (u m) hcl
  have hh := congrArg (StageRotation.resize (congrArg (· + 2) he0.symm)) hr
  rw [oriented_resize_up] at hh
  have hx : (Fin.cast he0.symm
      (⟨(kmswStage u m).active, act_lt_nextEdge u le_rfl⟩ : Fin _), false) =
      (⟨(kmswMissingRootStage u m).active, ha⟩, false) := by
    apply Prod.ext
    · exact Fin.ext ha0.symm
    · rfl
  have hy : (Fin.cast he0.symm
      (⟨(kmswStage u m).active, act_lt_nextEdge u le_rfl⟩ : Fin _), true) =
      (⟨(kmswMissingRootStage u m).active, ha⟩, true) := by
    apply Prod.ext
    · exact Fin.ext ha0.symm
    · rfl
  rw [hx, hy, oriented_resize_twice] at hh
  unfold primedLocalRot
  rw [oriented_resize_twice]
  exact hh



theorem primedRotInducedOriented_step_up (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (hc : primedCode (primedSimInput w) h m = 1)
    (ih : PrimedRotInducedOrientedAt w h m) :
    PrimedRotInducedOrientedAt w h (m + 1) := by
  classical
  let u := primedCode (primedSimInput w) h
  let n := primedStageTime w h m
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  obtain ⟨ht, hcode⟩ := oriented_ordinary_alignment w h m hm ho
  have hcl : kmswCodeStep (u m) = .up := by
    change kmswCodeStep (primedCode (primedSimInput w) h m) = .up
    rw [hc]
    rfl
  have hcr : kmswCodeStep (w n) = .up := by rw [← hcode, hc]; rfl
  have hk : (kmswMissingRootStage u (m + 1)).nextEdge = sh.nextEdge + 2 := by
    change (kmswStepOfStep sh (kmswCodeStep (u m))).nextEdge = _
    simp only [hcl, kmswStepOfStep, State.addEdge]
  have hl : (kmswStage w (primedStageTime w h (m + 1))).nextEdge = gl.nextEdge + 2 := by
    rw [ht]
    change (kmswStepOfStep gl (kmswCodeStep (w n))).nextEdge = _
    simp only [hcr, kmswStepOfStep, State.addEdge]
  have hs := oriented_canonical_sim w h m hm
  have ha : sh.active < sh.nextEdge := by
    obtain ⟨_, he, _, _, _, _, ha', _⟩ := kmswMissingRootStage_agree u m
    change (kmswMissingRootStage u m).active < (kmswMissingRootStage u m).nextEdge
    rw [he, ha']
    exact act_lt_nextEdge u le_rfl
  let i := primedDartMapOriented w h m
  let J : StageDart (sh.nextEdge + 2) → StageDart (gl.nextEdge + 2) :=
    fun d => StageRotation.allocation gl.nextEdge 2
      (Sum.map i id ((StageRotation.allocation sh.nextEdge 2).symm d))
  let a : StageDart sh.nextEdge := (⟨sh.active, ha⟩, false)
  let A : StageDart sh.nextEdge := (⟨sh.active, ha⟩, true)
  have hpa : sh.present sh.active = true := primed_active_present w h m (by omega)
  have hia : i a = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, false) := by
    rw [show i a = primedDartMap w h m a from
      primedDartMapOriented_eq_of_present w h m a hpa]
    apply Prod.ext
    · exact Fin.ext hs.active_alignment
    · rfl
  have hiA : i A = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, true) := by
    rw [show i A = primedDartMap w h m A from
      primedDartMapOriented_eq_of_present w h m A hpa]
    apply Prod.ext
    · exact Fin.ext hs.active_alignment
    · rfl
  unfold PrimedRotInducedOrientedAt at ih ⊢
  apply oriented_transport_return hk hl
    (StageRotation.up sh.nextEdge (primedLocalRot u m) a A)
    (primedLocalRot u (m + 1))
    (StageRotation.up gl.nextEdge (stageRot w n) (i a) (i A))
    (stageRot w (primedStageTime w h (m + 1))) J (primedDartMapOriented w h (m + 1))
  · exact oriented_local_up u m hc ha hk
  · rw [hia, hiA]
    have hr := StageRotation.step_up gl (act_lt_nextEdge w le_rfl)
      (stageRotation_UL_bound w n) (stageRot w n) (w n) hcr
    revert hl
    rw [ht]
    intro hl
    exact hr
  · intro d
    obtain ⟨z, hz⟩ := (StageRotation.allocation sh.nextEdge 2).surjective
      (Fin.cast hk d.1, d.2)
    cases z with
    | inl e =>
      have hd : outerSucc_castDart (primedLocal_nextEdge_succ_le u m) e = d := by
        apply Prod.ext
        · exact Fin.ext (congrArg (fun z => z.1.val) hz)
        · exact (show e.2 = d.2 from congrArg (fun z => z.2) hz)
      have hh := primedDartMapOriented_compatible w h m e
      rw [hd] at hh
      rw [hh]
      simp only [J, ← hz, Equiv.symm_apply_apply, Sum.map_inl]
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    | inr e =>
      have hv : d.1.val = sh.nextEdge + e.1.val :=
        (congrArg (fun z => z.1.val) hz).symm
      have hb : d.2 = e.2 := (congrArg Prod.snd hz).symm
      have hnew : sh.nextEdge ≤ d.1.val := by omega
      have hf := oriented_ordinary_new w h m hm ho d.1 hnew
      have hmap : primedAllEdgeMap w h (m + 1) =
          kmswShiftUpEdgeMap sh gl (primedAllEdgeMap w h m) := by
        simp only [primedAllEdgeMap, hm, ho, ↓reduceIte, hc,
          primedOrdinaryStepEdgeMap]
        rfl
      simp only [J, ← hz, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
      apply Prod.ext
      · apply Fin.ext
        change primedAllEdgeMap w h (m + 1) d.1.val = _
        rw [hmap]
        have he : e.1.val = 0 ∨ e.1.val = 1 := by have := e.1.isLt; omega
        rcases he with he | he <;>
          simp [hv, he, kmswShiftUpEdgeMap, StageRotation.allocation]
      · change (d.2 ^^ primedSideFlip w h (m + 1) d.1) = e.2
        rw [hf]
        simpa only [Bool.xor_false] using hb
  · apply oriented_congr_return (StageRotation.allocation sh.nextEdge 2)
      (StageRotation.allocation gl.nextEdge 2)
      (StageRotation.pairSplice (primedLocalRot u m)
        (Equiv.swap (0, true) (1, false)) a A (0, false) (1, true))
      (StageRotation.pairSplice (stageRot w n)
        (Equiv.swap (0, true) (1, false)) (i a) (i A) (0, false) (1, true))
      _ _ (Sum.map i id) J
    · intro d
      simp only [StageRotation.up, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [StageRotation.up, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    · intro d
      simp only [J, Equiv.symm_apply_apply]
    · exact oriented_pair_induced _ _ _ i (primedDartMapOriented_injective w h m)
        a A (0, false) (1, true) (by decide) (by decide) (by decide) ih

 
private theorem oriented_resize_leftFresh {a b : ℕ} (hab : a = b)
    (σ : Equiv.Perm (StageDart a)) (x y : StageDart a) :
    StageRotation.resize (congrArg (· + 2) hab) (StageRotation.leftFresh a σ x y) =
      StageRotation.leftFresh b (StageRotation.resize hab σ)
        (Fin.cast hab x.1, x.2) (Fin.cast hab y.1, y.2) := by
  cases hab
  rfl

 
private theorem oriented_local_leftFresh (u : ℕ → Fin 3) (m : ℕ) (hc : u m = 0)
    (hp : (kmswMissingRootStage u m).UL.dropLast.reverse = [])
    (ha : (kmswMissingRootStage u m).active < (kmswMissingRootStage u m).nextEdge)
    (hk : (kmswMissingRootStage u (m + 1)).nextEdge =
      (kmswMissingRootStage u m).nextEdge + 2) :
    StageRotation.resize hk (primedLocalRot u (m + 1)) =
      StageRotation.leftFresh (kmswMissingRootStage u m).nextEdge (primedLocalRot u m)
        (⟨(kmswMissingRootStage u m).active, ha⟩, false)
        (⟨(kmswMissingRootStage u m).active, ha⟩, true) := by
  have he0 := (kmswMissingRootStage_agree u m).2.1
  have he1 := (kmswMissingRootStage_agree u (m + 1)).2.1
  obtain ⟨_, _, _, _, _, _, ha0, _⟩ := kmswMissingRootStage_agree u m
  have hcl : kmswCodeStep (u m) = .left := by rw [hc]; rfl
  have hp0 : (kmswStage u m).UL.dropLast.reverse = [] := by
    rw [← (kmswMissingRootStage_agree u m).2.2.2.2.2.2.2.1]
    exact hp
  have hr := StageRotation.step_leftFresh (kmswStage u m) (act_lt_nextEdge u le_rfl)
    (stageRotation_UL_bound u m) (stageRot u m) (u m) hcl hp0
  have hh := congrArg (StageRotation.resize (congrArg (· + 2) he0.symm)) hr
  rw [oriented_resize_leftFresh] at hh
  have hx : (Fin.cast he0.symm
      (⟨(kmswStage u m).active, act_lt_nextEdge u le_rfl⟩ : Fin _), false) =
      (⟨(kmswMissingRootStage u m).active, ha⟩, false) := by
    apply Prod.ext
    · exact Fin.ext ha0.symm
    · rfl
  have hy : (Fin.cast he0.symm
      (⟨(kmswStage u m).active, act_lt_nextEdge u le_rfl⟩ : Fin _), true) =
      (⟨(kmswMissingRootStage u m).active, ha⟩, true) := by
    apply Prod.ext
    · exact Fin.ext ha0.symm
    · rfl
  rw [hx, hy, oriented_resize_twice] at hh
  unfold primedLocalRot
  rw [oriented_resize_twice]
  exact hh


 
private theorem oriented_resize_leftExisting {a b : ℕ} (hab : a = b)
    (σ : Equiv.Perm (StageDart a)) (x y : StageDart a) :
    StageRotation.resize (congrArg (· + 1) hab) (StageRotation.leftExisting a σ x y) =
      StageRotation.leftExisting b (StageRotation.resize hab σ)
        (Fin.cast hab x.1, x.2) (Fin.cast hab y.1, y.2) := by
  cases hab
  rfl

 
private theorem oriented_local_leftExisting (u : ℕ → Fin 3) (m : ℕ) (hc : u m = 0)
    (p : ℕ) (ps : List ℕ)
    (hp : (kmswMissingRootStage u m).UL.dropLast.reverse = p :: ps)
    (hb : p < (kmswMissingRootStage u m).nextEdge)
    (ha : (kmswMissingRootStage u m).active < (kmswMissingRootStage u m).nextEdge)
    (hk : (kmswMissingRootStage u (m + 1)).nextEdge =
      (kmswMissingRootStage u m).nextEdge + 1) :
    StageRotation.resize hk (primedLocalRot u (m + 1)) =
      StageRotation.leftExisting (kmswMissingRootStage u m).nextEdge (primedLocalRot u m)
        (⟨p, hb⟩, false)
        (⟨(kmswMissingRootStage u m).active, ha⟩, true) := by
  have he0 := (kmswMissingRootStage_agree u m).2.1
  have he1 := (kmswMissingRootStage_agree u (m + 1)).2.1
  obtain ⟨_, _, _, _, _, _, ha0, _⟩ := kmswMissingRootStage_agree u m
  have hcl : kmswCodeStep (u m) = .left := by rw [hc]; rfl
  have hp0 : (kmswStage u m).UL.dropLast.reverse = p :: ps := by
    rw [← (kmswMissingRootStage_agree u m).2.2.2.2.2.2.2.1]
    exact hp
  have hb0 : p < (kmswStage u m).nextEdge := he0 ▸ hb
  have hr := StageRotation.step_leftExisting (kmswStage u m) (act_lt_nextEdge u le_rfl)
    (stageRotation_UL_bound u m) (stageRot u m) (u m) hcl p ps hp0
  have hh := congrArg (StageRotation.resize (congrArg (· + 1) he0.symm)) hr
  rw [oriented_resize_leftExisting] at hh
  have hx : (Fin.cast he0.symm
      (⟨p, hb0⟩ : Fin _), false) =
      (⟨p, hb⟩, false) := by
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  have hy : (Fin.cast he0.symm
      (⟨(kmswStage u m).active, act_lt_nextEdge u le_rfl⟩ : Fin _), true) =
      (⟨(kmswMissingRootStage u m).active, ha⟩, true) := by
    apply Prod.ext
    · exact Fin.ext ha0.symm
    · rfl
  rw [hx, hy, oriented_resize_twice] at hh
  unfold primedLocalRot
  rw [oriented_resize_twice]
  exact hh



 
private theorem oriented_ordinary_allocation (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (r : ℕ)
    (hk : (kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1)).nextEdge =
      (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge + r)
    (hl : (kmswStage w (primedStageTime w h (m + 1))).nextEdge =
      (kmswStage w (primedStageTime w h m)).nextEdge + r)
    (hfresh : ∀ j : Fin r, primedAllEdgeMap w h (m + 1)
      ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge + j.val) =
        (kmswStage w (primedStageTime w h m)).nextEdge + j.val)
    (d : StageDart
      (kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1)).nextEdge) :
    (Fin.cast hl (primedDartMapOriented w h (m + 1) d).1,
      (primedDartMapOriented w h (m + 1) d).2) =
      StageRotation.allocation (kmswStage w (primedStageTime w h m)).nextEdge r
        (Sum.map (primedDartMapOriented w h m) id
          ((StageRotation.allocation
            (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge r).symm
              (Fin.cast hk d.1, d.2))) := by
  let u := primedCode (primedSimInput w) h
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (primedStageTime w h m)
  change (Fin.cast hl (primedDartMapOriented w h (m + 1) d).1,
      (primedDartMapOriented w h (m + 1) d).2) =
    StageRotation.allocation gl.nextEdge r
      (Sum.map (primedDartMapOriented w h m) id
        ((StageRotation.allocation sh.nextEdge r).symm (Fin.cast hk d.1, d.2)))
  obtain ⟨z, hz⟩ := (StageRotation.allocation sh.nextEdge r).surjective
    (Fin.cast hk d.1, d.2)
  cases z with
  | inl e =>
    have hd : outerSucc_castDart (primedLocal_nextEdge_succ_le u m) e = d := by
      apply Prod.ext
      · exact Fin.ext (congrArg (fun z => z.1.val) hz)
      · exact (show e.2 = d.2 from congrArg (fun z => z.2) hz)
    have hh := primedDartMapOriented_compatible w h m e
    rw [hd] at hh
    rw [hh]
    simp only [← hz, Equiv.symm_apply_apply, Sum.map_inl]
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  | inr e =>
    have hv : d.1.val = sh.nextEdge + e.1.val :=
      (congrArg (fun z => z.1.val) hz).symm
    have hb : d.2 = e.2 := (congrArg Prod.snd hz).symm
    have hnew : sh.nextEdge ≤ d.1.val := by omega
    have hf := oriented_ordinary_new w h m hm ho d.1 hnew
    simp only [← hz, Equiv.symm_apply_apply, Sum.map_inr, id_eq]
    apply Prod.ext
    · apply Fin.ext
      change primedAllEdgeMap w h (m + 1) d.1.val = _
      rw [hv]
      exact hfresh e.1
    · change (d.2 ^^ primedSideFlip w h (m + 1) d.1) = e.2
      rw [hf]
      simpa only [Bool.xor_false] using hb




theorem primedRotInducedOriented_step_left (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hc : primedCode (primedSimInput w) h m = 0)
    (ih : PrimedRotInducedOrientedAt w h m) :
    PrimedRotInducedOrientedAt w h (m + 1) := by
  classical
  let u := primedCode (primedSimInput w) h
  let n := primedStageTime w h m
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  let q := primedIntervalIndex (primedSimInput w) h (m - 1)
  have hm : m ≠ 0 := by
    intro hz
    subst m
    rw [primedCode_zero] at hc
    cases hc
  obtain ⟨_, hb⟩ := oriented_index_bounds w h m hm
  have ho : m < primedIntervalBase (primedSimInput w) h (q + 1) := by
    change m ≤ primedIntervalBase (primedSimInput w) h (q + 1) at hb
    by_contra hn
    have he : m = primedIntervalBase (primedSimInput w) h (q + 1) := by omega
    have hh := (primedCrossing_codes w h q).1
    rw [← he, hc] at hh
    cases hh
  dsimp only [q] at ho
  obtain ⟨ht, hcode⟩ := oriented_ordinary_alignment w h m hm ho
  have hcl : kmswCodeStep (u m) = .left := by
    change kmswCodeStep (primedCode (primedSimInput w) h m) = .left
    rw [hc]
    rfl
  have hcr : kmswCodeStep (w n) = .left := by rw [← hcode, hc]; rfl
  have hs := oriented_canonical_sim w h m hm
  have ha : sh.active < sh.nextEdge := by
    obtain ⟨_, he, _, _, _, _, ha', _⟩ := kmswMissingRootStage_agree u m
    change (kmswMissingRootStage u m).active < (kmswMissingRootStage u m).nextEdge
    rw [he, ha']
    exact act_lt_nextEdge u le_rfl
  let i := primedDartMapOriented w h m
  let A : StageDart sh.nextEdge := (⟨sh.active, ha⟩, true)
  have hpa : sh.present sh.active = true := primed_active_present w h m (by omega)
  have hiA : i A = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, true) := by
    rw [show i A = primedDartMap w h m A from
      primedDartMapOriented_eq_of_present w h m A hpa]
    apply Prod.ext
    · exact Fin.ext hs.active_alignment
    · rfl
  unfold PrimedRotInducedOrientedAt at ih ⊢
  cases hp : sh.UL.dropLast.reverse with
  | nil =>
    have hp' := hp
    dsimp only [sh, u] at hp
    have hgp : gl.UL.dropLast.reverse = [] := by
      have hh := hs.forget.left_predecessors
      change sh.UL.dropLast.reverse.map _ = gl.UL.dropLast.reverse at hh
      rw [hp, List.map_nil] at hh
      exact hh.symm
    have hk : (kmswMissingRootStage u (m + 1)).nextEdge = sh.nextEdge + 2 := by
      change (kmswStepOfStep sh (kmswCodeStep (u m))).nextEdge = _
      simp only [hcl, kmswStepOfStep, hp', State.addEdge]
    have hl : (kmswStage w (primedStageTime w h (m + 1))).nextEdge = gl.nextEdge + 2 := by
      rw [ht]
      change (kmswStepOfStep gl (kmswCodeStep (w n))).nextEdge = _
      simp only [hcr, kmswStepOfStep, hgp, State.addEdge]
    let a : StageDart sh.nextEdge := (⟨sh.active, ha⟩, false)
    have hia : i a = (⟨gl.active, act_lt_nextEdge w le_rfl⟩, false) := by
      rw [show i a = primedDartMap w h m a from
        primedDartMapOriented_eq_of_present w h m a hpa]
      apply Prod.ext
      · exact Fin.ext hs.active_alignment
      · rfl
    let J : StageDart (sh.nextEdge + 2) → StageDart (gl.nextEdge + 2) :=
      fun d => StageRotation.allocation gl.nextEdge 2
        (Sum.map i id ((StageRotation.allocation sh.nextEdge 2).symm d))
    apply oriented_transport_return hk hl
      (StageRotation.leftFresh sh.nextEdge (primedLocalRot u m) a A)
      (primedLocalRot u (m + 1))
      (StageRotation.leftFresh gl.nextEdge (stageRot w n) (i a) (i A))
      (stageRot w (primedStageTime w h (m + 1))) J (primedDartMapOriented w h (m + 1))
    · exact oriented_local_leftFresh u m hc hp ha hk
    · rw [hia, hiA]
      have hr := StageRotation.step_leftFresh gl (act_lt_nextEdge w le_rfl)
        (stageRotation_UL_bound w n) (stageRot w n) (w n) hcr hgp
      revert hl
      rw [ht]
      intro hl
      exact hr
    · apply oriented_ordinary_allocation w h m hm ho 2 hk hl
      intro j
      have hmap : primedAllEdgeMap w h (m + 1) =
          kmswShiftUpEdgeMap sh gl (primedAllEdgeMap w h m) := by
        simp only [primedAllEdgeMap, hm, ho, ↓reduceIte, hc,
          primedOrdinaryStepEdgeMap, primedOrdinaryLeftEdgeMap, hp]
        rfl
      change primedAllEdgeMap w h (m + 1) (sh.nextEdge + j.val) = gl.nextEdge + j.val
      rw [hmap]
      have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
      rcases hj with hj | hj <;> simp [hj, kmswShiftUpEdgeMap]
    · apply oriented_congr_return (StageRotation.allocation sh.nextEdge 2)
        (StageRotation.allocation gl.nextEdge 2)
        (StageRotation.pairSplice (primedLocalRot u m)
          (Equiv.swap (0, false) (1, false)) a A (1, true) (0, true))
        (StageRotation.pairSplice (stageRot w n)
          (Equiv.swap (0, false) (1, false)) (i a) (i A) (1, true) (0, true))
        _ _ (Sum.map i id) J
      · intro d
        simp only [StageRotation.leftFresh, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      · intro d
        simp only [StageRotation.leftFresh, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      · intro d
        simp only [J, Equiv.symm_apply_apply]
      · exact oriented_pair_induced _ _ _ i (primedDartMapOriented_injective w h m)
          a A (1, true) (0, true) (by decide) (by decide) (by decide) ih
  | cons p ps =>
    have hp' := hp
    dsimp only [sh, u] at hp
    have hgp : gl.UL.dropLast.reverse = primedAllEdgeMap w h m p ::
        ps.map (primedAllEdgeMap w h m) := (hs.forget.left_head_incidence hp).1
    have hmem : p ∈ sh.UL := List.dropLast_subset _
      (List.mem_reverse.mp (by rw [hp]; exact List.mem_cons_self))
    have hpb : p < sh.nextEdge := by
      obtain ⟨_, he, _, _, _, _, _, hul, _⟩ := kmswMissingRootStage_agree u m
      rw [he]
      exact stageRotation_UL_bound u m p (hul ▸ hmem)
    have hrb : primedAllEdgeMap w h m p < gl.nextEdge :=
      (primedDartMap w h m (⟨p, hpb⟩, false)).1.isLt
    have hk : (kmswMissingRootStage u (m + 1)).nextEdge = sh.nextEdge + 1 := by
      change (kmswStepOfStep sh (kmswCodeStep (u m))).nextEdge = _
      simp only [hcl, kmswStepOfStep, hp', State.addEdge]
    have hl : (kmswStage w (primedStageTime w h (m + 1))).nextEdge = gl.nextEdge + 1 := by
      rw [ht]
      change (kmswStepOfStep gl (kmswCodeStep (w n))).nextEdge = _
      simp only [hcr, kmswStepOfStep, hgp, State.addEdge]
    let a : StageDart sh.nextEdge := (⟨p, hpb⟩, false)
    have hia : i a = (⟨primedAllEdgeMap w h m p, hrb⟩, false) := by
      rw [show i a = primedDartMap w h m a from
        primedDartMapOriented_eq_of_present w h m a (hs.forget.UL_present p hmem)]
      rfl
    let J : StageDart (sh.nextEdge + 1) → StageDart (gl.nextEdge + 1) :=
      fun d => StageRotation.allocation gl.nextEdge 1
        (Sum.map i id ((StageRotation.allocation sh.nextEdge 1).symm d))
    apply oriented_transport_return hk hl
      (StageRotation.leftExisting sh.nextEdge (primedLocalRot u m) a A)
      (primedLocalRot u (m + 1))
      (StageRotation.leftExisting gl.nextEdge (stageRot w n) (i a) (i A))
      (stageRot w (primedStageTime w h (m + 1))) J (primedDartMapOriented w h (m + 1))
    · exact oriented_local_leftExisting u m hc p ps hp hpb ha hk
    · rw [hia, hiA]
      have hr := StageRotation.step_leftExisting gl (act_lt_nextEdge w le_rfl)
        (stageRotation_UL_bound w n) (stageRot w n) (w n) hcr _ _ hgp
      revert hl
      rw [ht]
      intro hl
      exact hr
    · apply oriented_ordinary_allocation w h m hm ho 1 hk hl
      intro j
      have hmap : primedAllEdgeMap w h (m + 1) =
          kmswShiftFreshEdgeMap sh gl (primedAllEdgeMap w h m) := by
        simp only [primedAllEdgeMap, hm, ho, ↓reduceIte, hc,
          primedOrdinaryStepEdgeMap, primedOrdinaryLeftEdgeMap, hp, List.cons_ne_nil]
        rfl
      change primedAllEdgeMap w h (m + 1) (sh.nextEdge + j.val) = gl.nextEdge + j.val
      rw [hmap]
      simp [kmswShiftFreshEdgeMap]
    · apply oriented_congr_return (StageRotation.allocation sh.nextEdge 1)
        (StageRotation.allocation gl.nextEdge 1)
        (StageRotation.pairSplice (primedLocalRot u m)
          (Equiv.refl (StageDart 1)) a A (0, false) (0, true))
        (StageRotation.pairSplice (stageRot w n)
          (Equiv.refl (StageDart 1)) (i a) (i A) (0, false) (0, true))
        _ _ (Sum.map i id) J
      · intro d
        simp only [StageRotation.leftExisting, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      · intro d
        simp only [StageRotation.leftExisting, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      · intro d
        simp only [J, Equiv.symm_apply_apply]
      · exact oriented_pair_induced _ _ _ i (primedDartMapOriented_injective w h m)
          a A (0, false) (0, true) (by decide) (by decide) (by decide) ih


 
private theorem oriented_triangle_extension {D E F : Type*}
    [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (σ' : Equiv.Perm (D ⊕ F)) (ρ : Equiv.Perm E)
    (i : D ⊕ F → E) (hi : Function.Injective i)
    (a b : D) (x y : F) (hab : σ a ≠ b)
    (old : ∀ d, σ' (.inl d) =
      if d = a then .inr x else if σ d = b then .inr y else .inl (σ d))
    (newx : σ' (.inr x) = .inl (σ a)) (newy : σ' (.inr y) = .inl b)
    (ha : ρ (i (.inl a)) = i (.inr x)) (hb : ρ (i (.inr y)) = i (.inl b))
    (sep : ∀ d z, z ≠ x → z ≠ y → ¬ ρ.SameCycle (i (.inl d)) (i (.inr z)))
    (other : ∀ z, z ≠ x → z ≠ y → ∃ n : ℕ, 0 < n ∧
      (ρ : E → E)^[n] (i (.inr z)) = i (σ' (.inr z)) ∧
      ∀ t : ℕ, 0 < t → t < n → (ρ : E → E)^[t] (i (.inr z)) ∉ Set.range i)
    (ih : ∀ d, ∃ n : ℕ, 0 < n ∧
      (ρ : E → E)^[n] (i (.inl d)) = i (.inl (σ d)) ∧
      ∀ t : ℕ, 0 < t → t < n →
        (ρ : E → E)^[t] (i (.inl d)) ∉ Set.range (fun e => i (.inl e))) :
    ∀ d, ∃ n : ℕ, 0 < n ∧ (ρ : E → E)^[n] (i d) = i (σ' d) ∧
      ∀ t : ℕ, 0 < t → t < n → (ρ : E → E)^[t] (i d) ∉ Set.range i := by
  have avoid (d : D) (n : ℕ)
      (hend : (ρ : E → E)^[n] (i (.inl d)) = i (.inl (σ d)))
      (hgap : ∀ t, 0 < t → t < n →
        (ρ : E → E)^[t] (i (.inl d)) ∉ Set.range (fun e => i (.inl e)))
      (t : ℕ) (ht : 0 < t) (htn : t < n)
      (hax : t = 1 → d ≠ a) (hby : t + 1 = n → σ d ≠ b) :
      (ρ : E → E)^[t] (i (.inl d)) ∉ Set.range i := by
    rintro ⟨z, hz⟩
    cases z with
    | inl e => exact hgap t ht htn ⟨e, hz⟩
    | inr z =>
      by_cases hzx : z = x
      · subst z
        have he : (ρ : E → E)^[t - 1] (i (.inl d)) = i (.inl a) := by
          apply ρ.injective
          rw [ha, ← Function.iterate_succ_apply' (ρ : E → E) (t - 1), show (t - 1).succ = t by omega, ← hz]
        by_cases ht1 : t = 1
        · have hda : d = a := by
            rw [ht1] at he
            exact Sum.inl.inj (hi he)
          exact hax ht1 hda
        · exact hgap (t - 1) (by omega) (by omega) ⟨a, he.symm⟩
      · by_cases hzy : z = y
        · subst z
          have he : (ρ : E → E)^[t + 1] (i (.inl d)) = i (.inl b) := by
            rw [Function.iterate_succ_apply', ← hz, hb]
          by_cases heq : t + 1 = n
          · rw [heq, hend] at he
            exact hby heq (Sum.inl.inj (hi he))
          · exact hgap (t + 1) (by omega) (by omega) ⟨b, he.symm⟩
        · apply sep d z hzx hzy
          have hc : ρ.SameCycle (i (.inl d)) ((ρ : E → E)^[t] (i (.inl d))) := by
            rw [← Equiv.Perm.coe_pow]
            exact ⟨t, rfl⟩
          simpa only [← hz] using hc
  intro d
  cases d with
  | inl d =>
    by_cases hda : d = a
    · subst d
      exact ⟨1, by omega, by simpa only [Function.iterate_one, old, ite_true] using ha,
        by intro t ht htn; omega⟩
    · obtain ⟨n, hn, he, hg⟩ := ih d
      by_cases hdb : σ d = b
      · have hn1 : 1 < n := by
          by_contra hn1
          have hn' : n = 1 := by omega
          rw [hn', Function.iterate_one, hdb] at he
          have hh := hi (ρ.injective (he.trans hb.symm))
          cases hh
        have hend : (ρ : E → E)^[n - 1] (i (.inl d)) = i (.inr y) := by
          apply ρ.injective
          rw [hb, ← Function.iterate_succ_apply' (ρ : E → E) (n - 1), show (n - 1).succ = n by omega, he, hdb]
        refine ⟨n - 1, by omega, ?_, ?_⟩
        · simpa only [old, ite_eq_right hda, ite_eq_left hdb] using hend
        · intro t ht htn
          exact avoid d n he hg t ht (by omega) (fun _ => hda) (by omega)
      · refine ⟨n, hn, ?_, ?_⟩
        · simpa only [old, ite_eq_right hda, ite_eq_right hdb] using he
        · intro t ht htn
          exact avoid d n he hg t ht htn (fun _ => hda) (fun _ => hdb)
  | inr z =>
    by_cases hzx : z = x
    · subst z
      obtain ⟨n, hn, he, hg⟩ := ih a
      have hn1 : 1 < n := by
        by_contra hn1
        have hn' : n = 1 := by omega
        rw [hn', Function.iterate_one, ha] at he
        have hh := hi he
        cases hh
      have path (t : ℕ) : (ρ : E → E)^[t] (i (.inr x)) =
          (ρ : E → E)^[t + 1] (i (.inl a)) := by
        rw [Function.iterate_succ_apply, ha]
      refine ⟨n - 1, by omega, ?_, ?_⟩
      · rw [path, show n - 1 + 1 = n by omega, he, newx]
      · intro t ht htn
        rw [path]
        exact avoid a n he hg (t + 1) (by omega) (by omega) (by omega) (fun _ => hab)
    · by_cases hzy : z = y
      · subst z
        exact ⟨1, by omega, by simpa only [Function.iterate_one, newy] using hb,
          by intro t ht htn; omega⟩
      · exact other z hzx hzy


 
private theorem oriented_old_induced (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (ih : PrimedRotInducedOrientedAt w h m) :
    let q := outerSucc_castDart
      (kmswStage_nextEdge_mono w (primedStageTime_succ_le w h m))
    ∀ d, ∃ n : ℕ, 0 < n ∧
      (stageRot w (primedStageTime w h (m + 1)) : _ → _)^[n]
          (q (primedDartMapOriented w h m d)) =
        q (primedDartMapOriented w h m
          (primedLocalRot (primedCode (primedSimInput w) h) m d)) ∧
      ∀ t : ℕ, 0 < t → t < n →
        (stageRot w (primedStageTime w h (m + 1)) : _ → _)^[t]
          (q (primedDartMapOriented w h m d)) ∉
            Set.range (q ∘ primedDartMapOriented w h m) := by
  dsimp only
  have hi : Function.Injective (outerSucc_castDart
      (kmswStage_nextEdge_mono w (primedStageTime_succ_le w h m))) := by
    intro d e he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z => z.1.val) he)
    · exact congrArg (fun z => z.2) he
  exact hatExit_induced_rotation_comp
    (primedLocalRot (primedCode (primedSimInput w) h) m)
    (stageRot w (primedStageTime w h m))
    (stageRot w (primedStageTime w h (m + 1)))
    (primedDartMapOriented w h m) _ hi ih
    (hatExit_ambient_rotation_induced w _ _ (primedStageTime_succ_le w h m))



/- Continuation status: ordinary positive-stage up steps and every left step
are proved, in addition to the existing down-activation step. The generic
triangle extension and ambient old-image transfer helpers are available above.
The crossing step, all-stage theorem, and positive-stage rooted embedding package
are toward Lemma 5.13 (primed half); they are not the paper result. The stage-zero
caveat is unchanged. -/

 
private theorem oriented_endpoint_bound (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswMissingRootStage u m).nextEdge) :
    stageEndpoint (kmswMissingRootStage u m) d < (kmswMissingRootStage u m).nextVertex := by
  obtain ⟨hv, he, hw, ht, _⟩ := kmswMissingRootStage_agree u m
  have hb := kmswStage_endpoints_lt_nextVertex u m d.1.val (by rw [← he]; exact d.1.isLt)
  cases hd : d.2 <;> simp only [stageEndpoint, hd, Bool.false_eq_true, ↓reduceIte, hv, hw, ht]
  · exact hb.1
  · exact hb.2

 
private theorem oriented_cycle_endpoint (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d e : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    (stageRot w (primedStageTime w h m)).SameCycle
      (primedDartMapOriented w h m d) (primedDartMapOriented w h m e) ↔
    stageEndpoint (kmswMissingRootStage (primedCode (primedSimInput w) h) m) d =
      stageEndpoint (kmswMissingRootStage (primedCode (primedSimInput w) h) m) e := by
  rw [stageRot_sameCycle_iff_endpoint_eq, primedDartMapOriented_endpoint,
    primedDartMapOriented_endpoint]
  constructor
  · intro he
    cases m with
    | zero =>
      exact (primedAll_sim_zero w h).1.vertex_injective _ _
        (oriented_endpoint_bound _ _ d) (oriented_endpoint_bound _ _ e) he
    | succ m =>
      obtain ⟨_, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.vertex_injective _ _
        (oriented_endpoint_bound _ _ d) (oriented_endpoint_bound _ _ e) he
  · exact congrArg _

 
private theorem oriented_two_fiber_return {D E : Type*} [Finite E]
    (ρ : Equiv.Perm E) (i : D → E) (d t : D)
    (ht : ρ.SameCycle (i d) (i t))
    (hf : ∀ e, ρ.SameCycle (i d) (i e) → e = d ∨ e = t) :
    ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i t ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i t := by
    obtain ⟨k, hk, _, he⟩ := ht.exists_pow_eq''
    exact ⟨k, hk, by simpa only [Equiv.Perm.coe_pow] using he⟩
  let k := Nat.find hex
  have hk0 : 0 < k := (Nat.find_spec hex).1
  have hk : (ρ : E → E)^[k] (i d) = i t := (Nat.find_spec hex).2
  refine ⟨k, hk0, hk, ?_⟩
  intro j hj hjk ⟨e, he⟩
  have hc : ρ.SameCycle (i d) (i e) := by
    rw [he, ← Equiv.Perm.coe_pow]
    exact ⟨(j : ℤ), by simp⟩
  rcases hf e hc with hed | het
  · rw [hed] at he
    have hr : (ρ : E → E)^[k - j] (i d) = i t := by
      calc
        _ = (ρ : E → E)^[k - j] ((ρ : E → E)^[j] (i d)) := congrArg _ he
        _ = (ρ : E → E)^[k] (i d) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hjk)]
        _ = i t := hk
    exact Nat.find_min hex (show k - j < k by omega) ⟨by omega, hr⟩
  · rw [het] at he
    exact Nat.find_min hex hjk ⟨hj, he.symm⟩

 
private theorem oriented_resize_eval {k l : ℕ} (hk : k = l)
    (σ : Equiv.Perm (StageDart k)) (d : StageDart k) :
    StageRotation.resize hk σ (Fin.cast hk d.1, d.2) =
      (Fin.cast hk (σ d).1, (σ d).2) := by
  cases hk
  rfl



theorem primedRotInducedOriented_step_crossing
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ)
    (ih : PrimedRotInducedOrientedAt w h
      (primedIntervalBase (primedSimInput w) h (k + 1))) :
    PrimedRotInducedOrientedAt w h
      (primedIntervalBase (primedSimInput w) h (k + 1) + 1) := by
  classical
  let u := primedCode (primedSimInput w) h
  let m := primedIntervalBase (primedSimInput w) h (k + 1)
  let n := walkNL w h (k + 1)
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (n - 1)
  have hm : m ≠ 0 := by
    have hb := primedIntervalBase_ge (primedSimInput w) h (k + 1)
    change k + 1 ≤ m at hb
    omega
  have hidx : primedIntervalIndex (primedSimInput w) h (m - 1) = k := by
    have hspec := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
    have hlo := primedIntervalWidth_pos (primedSimInput w) h k
    have hb := primedIntervalBase_succ (primedSimInput w) h k
    have hle : primedIntervalIndex (primedSimInput w) h (m - 1) ≤ k :=
      Nat.find_min' _ (by change m - 1 < m; omega)
    apply Nat.le_antisymm hle
    by_contra hn
    have hmono := primedIntervalBase_mono (primedSimInput w) h
      (show primedIntervalIndex (primedSimInput w) h (m - 1) + 1 ≤ k by omega)
    change m = primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k at hb
    omega
  have ho : ¬ m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) := by rw [hidx]; exact lt_irrefl _
  have hc : u m = 1 := (primedCrossing_codes w h k).1
  have ht : primedStageTime w h (m + 1) = n := primedStageTime_after_crossing w h (k + 1)
  have hn : 0 < n := by have := (walkNL_spec w h (k + 1)).1; dsimp [n]; omega
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    change kmswStep sh (u m) = _
    rw [hc]
    rfl
  have hk : (kmswMissingRootStage u (m + 1)).nextEdge = sh.nextEdge + 2 := by
    rw [hl]; rfl
  have hs := oriented_canonical_sim w h m hm
  have ha : sh.active < sh.nextEdge := by
    obtain ⟨_, he, _, _, _, _, ha, _⟩ := kmswMissingRootStage_agree u m
    rw [show sh.nextEdge = (kmswStage u m).nextEdge from he,
      show sh.active = (kmswStage u m).active from ha]
    exact act_lt_nextEdge u le_rfl
  let a : StageDart sh.nextEdge := (⟨sh.active, ha⟩, false)
  let A : StageDart sh.nextEdge := (⟨sh.active, ha⟩, true)
  let σ := primedLocalRot u m
  let ρ := stageRot w (primedStageTime w h (m + 1))
  let τ : Equiv.Perm (StageDart 2) := Equiv.swap (0, true) (1, false)
  let x : StageDart 2 := (0, false)
  let y : StageDart 2 := (1, true)
  let σ' := StageRotation.pairSplice σ τ a A x y
  let C : StageDart (sh.nextEdge + 2) ≃ StageDart
      (kmswMissingRootStage u (m + 1)).nextEdge :=
    Equiv.prodCongr (finCongr hk.symm) (Equiv.refl Bool)
  let L := (StageRotation.allocation sh.nextEdge 2).trans C
  let i := primedDartMapOriented w h (m + 1) ∘ L
  have hi : Function.Injective i :=
    (primedDartMapOriented_injective w h (m + 1)).comp L.injective
  have Lold (d : StageDart sh.nextEdge) : L (.inl d) =
      outerSucc_castDart (primedLocal_nextEdge_succ_le u m) d := by
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  have iold (d : StageDart sh.nextEdge) : i (.inl d) =
      outerSucc_castDart (kmswStage_nextEdge_mono w (primedStageTime_succ_le w h m))
        (primedDartMapOriented w h m d) := by
    change primedDartMapOriented w h (m + 1) (L (.inl d)) = _
    rw [Lold, primedDartMapOriented_compatible]
  have inew (z : StageDart 2) :
      (i (.inr z)).1.val = (if z.1.val = 0 then gl.nextEdge else gl.active) ∧
      (i (.inr z)).2 = (z.2 ^^ decide (z.1.val = 1)) := by
    have hz : z.1.val = 0 ∨ z.1.val = 1 := by have := z.1.isLt; omega
    have hmap : primedAllEdgeMap w h (m + 1) =
        primedCrossingEdgeMap sh gl (primedAllEdgeMap w h m) := by
      simp only [primedAllEdgeMap, hm, ↓reduceIte, ho]
      rw [hidx]
    have hf := oriented_crossing_new w h m hm ho (L (.inr z)).1
      (show sh.nextEdge ≤ (L (.inr z)).1.val by change sh.nextEdge ≤ sh.nextEdge + z.1.val; omega)
    constructor
    · change primedAllEdgeMap w h (m + 1) (sh.nextEdge + z.1.val) = _
      rw [hmap]
      rcases hz with hz | hz <;> simp [primedCrossingEdgeMap, hz]
    · change (z.2 ^^ primedSideFlip w h (m + 1) (L (.inr z)).1) = _
      rw [hf]
      congr 2
      change (sh.nextEdge + z.1.val = sh.nextEdge + 1) = (z.1.val = 1)
      simp only [Nat.add_left_cancel_iff]
  have hloc := oriented_local_up u m hc ha hk
  have hσ : ∀ d, primedLocalRot u (m + 1) (L d) = L (σ' d) := by
    intro d
    have he := oriented_resize_eval hk (primedLocalRot u (m + 1)) (L d)
    rw [hloc] at he
    have harg : (Fin.cast hk (L d).1, (L d).2) =
        StageRotation.allocation sh.nextEdge 2 d := by
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    rw [harg] at he
    have hup : StageRotation.up sh.nextEdge σ a A
        (StageRotation.allocation sh.nextEdge 2 d) =
        StageRotation.allocation sh.nextEdge 2 (σ' d) := by
      simp only [StageRotation.up, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      rfl
    rw [hup] at he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z => z.1.val) he).symm
    · exact (congrArg Prod.snd he).symm
  let p := fun d => stageEndpoint (kmswMissingRootStage u (m + 1)) (L d)
  have pold (d : StageDart sh.nextEdge) : p (.inl d) = stageEndpoint sh d := by
    have h0 : d.1.val ≠ sh.nextEdge := ne_of_lt d.1.isLt
    have h1 : d.1.val ≠ sh.nextEdge + 1 := by have := d.1.isLt; omega
    cases hb : d.2 <;>
      simp [p, L, C, StageRotation.allocation, stageEndpoint, hl, kmswStepOfStep, State.addEdge, hb, h0, h1]
  have pnew (z : StageDart 2) : p (.inr z) =
      if z = x then sh.west sh.active else if z = y then sh.east sh.active else sh.nextVertex := by
    rcases z with ⟨j, b⟩
    fin_cases j <;> cases b <;>
      simp [p, L, C, StageRotation.allocation, stageEndpoint, hl, kmswStepOfStep, State.addEdge, x, y]
  have hcycle (d e) : ρ.SameCycle (i d) (i e) ↔ p d = p e :=
    oriented_cycle_endpoint w h (m + 1) (L d) (L e)
  have hneq : sh.west sh.active ≠ sh.east sh.active := by
    obtain ⟨_, _, hw, he, _, _, ha', _⟩ := kmswMissingRootStage_agree u m
    change (kmswMissingRootStage u m).west (kmswMissingRootStage u m).active ≠
      (kmswMissingRootStage u m).east (kmswMissingRootStage u m).active
    rw [hw, he, ha']
    intro heq
    exact (activeEast_ne_activeInitial u (j := m) (n := m) le_rfl)
      (heq.symm.trans (edge_endpoints_eq u (act_lt_nextEdge u le_rfl)).1)
  have hab : σ a ≠ A := by
    intro heq
    obtain ⟨t, _, ht', _⟩ := ih a
    change (stageRot w (primedStageTime w h m) : _ → _)^[t]
      (primedDartMapOriented w h m a) = primedDartMapOriented w h m (σ a) at ht' 
    have hs' : (stageRot w (primedStageTime w h m)).SameCycle
        (primedDartMapOriented w h m a) (primedDartMapOriented w h m (σ a)) := by
      rw [← ht', ← Equiv.Perm.coe_pow]
      exact ⟨(t : ℤ), by simp⟩
    have he := (oriented_cycle_endpoint w h m a (σ a)).mp hs'
    rw [heq] at he
    exact hneq he
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
  have hUL : sh.UL = xs ++ [sh.active] := by
    obtain ⟨_, _, _, _, _, _, ha', hu, _⟩ := kmswMissingRootStage_agree u m
    change (kmswMissingRootStage u m).UL = _
    rw [hu, ha']
    exact hxs
  have hp : gl.UL.dropLast.reverse = primedAllEdgeMap w h m sh.active ::
      (xs.map (primedAllEdgeMap w h m)).reverse := by
    have he := primedCrossing_exit_predecessor_eq w h k
    rw [← primedStageTime_at_crossing w h k] at he
    change gl.UL.dropLast = (kmswStage w (primedStageTime w h m)).UL at he
    rw [he, ← hs.forget.UL_alignment, hUL]
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  let j : TriangleCreationTime w := ⟨n - 1, Or.inl (walkNL_previous_code w h (k + 1))⟩
  have hj : j.val < primedStageTime w h (m + 1) := by rw [ht]; dsimp [j]; omega
  have hjcode : w (n - 1) = 0 := walkNL_previous_code w h (k + 1)
  have htriple : stageTriangleDartTriple w j =
      ((primedAllEdgeMap w h m sh.active, false), (gl.active, false), (gl.nextEdge, true)) := by
    simp only [stageTriangleDartTriple, j, hjcode, ite_true]
    change (match gl.UL.dropLast.reverse with
      | e :: _ => ((e, false), (gl.active, false), (gl.nextEdge, true))
      | [] => ((gl.active, false), (gl.nextEdge, true), (gl.nextEdge + 1, false))) = _
    rw [hp]
  have face := stageTriangle_isFace w j (primedStageTime w h (m + 1)) hj
  have T1 : stageTriangleDart₁ w (primedStageTime w h (m + 1)) j hj = i (.inl a) := by
    rw [iold]
    rw [primedDartMapOriented_eq_of_present w h m a
      (primed_active_present w h m (by omega))]
    apply Prod.ext
    · apply Fin.ext
      change (stageTriangleDartTriple w j).1.1 = primedAllEdgeMap w h m sh.active
      rw [htriple]
    · change (stageTriangleDartTriple w j).1.2 = false
      rw [htriple]
  have T2 : stageTriangleDart₂ w (primedStageTime w h (m + 1)) j hj = i (.inr y) := by
    apply Prod.ext
    · apply Fin.ext
      rw [(inew y).1]
      change (stageTriangleDartTriple w j).2.1.1 = (if (1 : ℕ) = 0 then gl.nextEdge else gl.active)
      rw [htriple]
      rfl
    · rw [(inew y).2]
      change (stageTriangleDartTriple w j).2.1.2 = (true ^^ decide ((1 : ℕ) = 1))
      rw [htriple]
      rfl
  have T3 : stageTriangleDart₃ w (primedStageTime w h (m + 1)) j hj = edgeFlip _ (i (.inr x)) := by
    apply Prod.ext
    · apply Fin.ext
      change _ = (i (.inr x)).1.val
      rw [(inew x).1]
      change (stageTriangleDartTriple w j).2.2.1 = (if (0 : ℕ) = 0 then gl.nextEdge else gl.active)
      rw [htriple]
      rfl
    · change _ = !(i (.inr x)).2
      rw [(inew x).2]
      change (stageTriangleDartTriple w j).2.2.2 = !(false ^^ decide ((0 : ℕ) = 1))
      rw [htriple]
      rfl
  have face_rot {d e : StageDart (kmswStage w (primedStageTime w h (m + 1))).nextEdge}
      (he : (kmswMap w (primedStageTime w h (m + 1))).faceSucc d = e) :
      ρ e = edgeFlip _ d := by
    rw [← he]
    exact (kmswMap w (primedStageTime w h (m + 1))).rot.apply_symm_apply _
  have hiaA : edgeFlip _ (i (.inl a)) = i (.inl A) := by
    rw [iold, iold]
    apply Prod.ext
    · rfl
    · change (!(primedDartMapOriented w h m a).2) = (primedDartMapOriented w h m A).2
      exact congrArg (fun z : StageDart (kmswStage w (primedStageTime w h m)).nextEdge => z.2)
        (primedDartMapOriented_flip_comm w h m a).symm
  have hx : ρ (i (.inl a)) = i (.inr x) := by
    have he := face_rot face.2.2.1
    rw [T3, T1] at he
    exact he.trans ((kmswMap w (primedStageTime w h (m + 1))).edgeInv_invol _)
  have hy : ρ (i (.inr y)) = i (.inl A) := by
    have he := face_rot face.1
    rw [T1, T2, hiaA] at he
    exact he
  unfold PrimedRotInducedOrientedAt
  apply oriented_congr_return L (Equiv.refl _) σ' ρ
    (primedLocalRot u (m + 1)) ρ i (primedDartMapOriented w h (m + 1))
    hσ (fun _ => rfl) (fun _ => rfl)
  apply oriented_triangle_extension σ σ' ρ i hi a A x y hab
  · exact oriented_pair_old σ τ a A x y (by decide) (by decide)
  · simp [σ', StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, hab]
  · simp [σ', StageRotation.pairSplice, insertBefore, insertAfter, Equiv.swap_apply_def, τ, x, y]
  · exact hx
  · exact hy
  · intro d z hzx hzy he
    have hp' := (hcycle _ _).mp he
    rw [pold, pnew, ite_eq_right hzx, ite_eq_right hzy] at hp'
    have hb := oriented_endpoint_bound u m d
    change stageEndpoint sh d < sh.nextVertex at hb
    omega
  · intro z hzx hzy
    have hnew : σ' (.inr z) = .inr (τ z) := by
      have hτzy : τ z ≠ y := by
        intro he
        have hτy : τ y = y := by decide
        exact hzy (τ.injective (he.trans hτy.symm))
      simp [σ', StageRotation.pairSplice, insertBefore, insertAfter,
        Equiv.swap_apply_def, hzx, hτzy]
    rw [hnew]
    apply oriented_two_fiber_return ρ i (.inr z) (.inr (τ z))
    · apply (hcycle _ _).mpr
      have hτzx : τ z ≠ x := by
        intro he
        have hτx : τ x = x := by decide
        exact hzx (τ.injective (he.trans hτx.symm))
      have hτzy : τ z ≠ y := by
        intro he
        have hτy : τ y = y := by decide
        exact hzy (τ.injective (he.trans hτy.symm))
      simp only [pnew, ite_eq_right hzx, ite_eq_right hzy, ite_eq_right hτzx, ite_eq_right hτzy]
    · intro e he
      have hep := (hcycle _ _).mp he
      rw [pnew, ite_eq_right hzx, ite_eq_right hzy] at hep
      cases e with
      | inl e =>
        rw [pold] at hep
        have hb := oriented_endpoint_bound u m e
        change stageEndpoint sh e < sh.nextVertex at hb
        omega
      | inr e =>
        have hexy : e ≠ x ∧ e ≠ y := by
          constructor
          · intro he'; subst e
            rw [pnew, ite_eq_left rfl] at hep
            have hb := oriented_endpoint_bound u m a
            change sh.west sh.active < sh.nextVertex at hb
            omega
          · intro he'; subst e
            rw [pnew, ite_eq_right (by decide : y ≠ x), ite_eq_left rfl] at hep
            have hb := oriented_endpoint_bound u m A
            change sh.east sh.active < sh.nextVertex at hb
            omega
        have freshpair : ∀ z e : StageDart 2, z ≠ x → z ≠ y →
            e ≠ x → e ≠ y → e = z ∨ e = τ z := by decide
        have he := freshpair z e hzx hzy hexy.1 hexy.2
        rcases he with he | he
        · exact Or.inl (congrArg Sum.inr he)
        · exact Or.inr (congrArg Sum.inr he)
  · intro d
    have hh := oriented_old_induced w h m ih d
    have himap : (outerSucc_castDart
        (kmswStage_nextEdge_mono w (primedStageTime_succ_le w h m)) ∘
        primedDartMapOriented w h m) = (fun e => i (.inl e)) :=
      funext (fun e => (iold e).symm)
    rw [himap] at hh
    simpa only [← iold] using hh




theorem primedRotInducedOriented_all (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, PrimedRotInducedOrientedAt w h m := by
  intro m
  induction m with
  | zero => exact primedRotInducedOriented_zero w h
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      exact primedRotInducedOriented_one w h
    · by_cases ho : m < primedIntervalBase (primedSimInput w) h
          (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)
      · generalize hc : primedCode (primedSimInput w) h m = c
        fin_cases c
        · exact primedRotInducedOriented_step_left w h m hc ih
        · exact primedRotInducedOriented_step_up w h m hm ho hc ih
        · exact primedRotInducedOriented_step_down w h m hc ih
      · have hb := (oriented_index_bounds w h m hm).2
        have heq : primedIntervalBase (primedSimInput w) h
            (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) = m := by omega
        have hh := primedRotInducedOriented_step_crossing w h
          (primedIntervalIndex (primedSimInput w) h (m - 1))
        rw [heq] at hh
        exact hh ih

 
@[expose] noncomputable def oriented_missing_map_on_stage
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) (hm : 1 ≤ m) :
    DirectedMapWithMissing (StageDart (kmswStage (primedCode (primedSimInput w) h) m).nextEdge) := by
  let u := primedCode (primedSimInput w) h
  let sh := kmswMissingRootStage u m
  let M := kmswStageDirectedMap u m
  have hpres := (kmswMissingRootStage_agree u m).2.2.2.2.1
  have hLR : (kmswStage u m).LR = [0] := by
    obtain ⟨_, hs, _⟩ := primedAll_sim w h m hm
    have hlr := (kmswMissingRootStage_agree u m).2.2.2.2.2.2.2.2.2.2
    exact hlr.symm.trans hs.LR_root
  refine { M with
    missing := fun d => sh.present d.1.val = false
    tail := fun d => sh.present d.1.val = true ∧ d.2 = false
    missing_edgeInv := fun _ => Iff.rfl
    tail_iff := ?_
    tail_missing := ?_
    missing_outer := ?_ }
  · intro d hd
    change ¬ sh.present d.1.val = false at hd
    change (sh.present d.1.val = true ∧ d.2 = false) ↔
      ¬ (sh.present d.1.val = true ∧ (!d.2) = false)
    have hp := Bool.eq_true_of_not_eq_false hd
    cases d.2 <;> simp only [hp, Bool.not_false, Bool.not_true] <;> decide
  · intro d hd ht
    exact Bool.noConfusion (hd.symm.trans ht.1)
  · rintro ⟨e, b⟩ hd
    by_cases he : e.val = 0
    · have ho := ((kmswStageDirectedMap_LR_bridge u m e).mp (by rw [hLR, he]; simp)).2.2
      cases b
      · exact Or.inr ho
      · exact Or.inl ho
    · have hp := hpres e.val he
      have hd' : M.missing (e, b) := by
        change (kmswStage u m).present e.val = false
        rw [← hp]
        exact hd
      exact M.missing_outer (e, b) hd'

 
@[expose] noncomputable def oriented_missing_rooted_on_stage
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) (hm : 1 ≤ m) :
    RootedDirectedMapWithMissing (StageDart (kmswStage (primedCode (primedSimInput w) h) m).nextEdge) := by
  let u := primedCode (primedSimInput w) h
  let M := oriented_missing_map_on_stage w h m hm
  have ha := (kmswMissingRootStage_agree u m).2.2.2.2.2.2.1
  have hp : (kmswMissingRootStage u m).present (kmswStage u m).active = true := by
    rw [← ha]
    exact primed_active_present w h m hm
  exact { map := M
          root := (kmswRootedStage u m).root
          root_present := by change ¬ (kmswMissingRootStage u m).present (kmswStage u m).active = false; rw [hp]; decide
          root_tail := by change (kmswMissingRootStage u m).present (kmswStage u m).active = true ∧ false = false; exact ⟨hp, rfl⟩ }

 
@[expose] def oriented_cast_rooted {k l : ℕ} (hk : k = l)
    (M : RootedDirectedMapWithMissing (StageDart k)) :
    RootedDirectedMapWithMissing (StageDart l) := hk ▸ M




@[expose] noncomputable def primedRootedStage
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) (hm : 1 ≤ m) :
    RootedDirectedMapWithMissing
      (StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :=
  oriented_cast_rooted (kmswMissingRootStage_agree (primedCode (primedSimInput w) h) m).2.1.symm
    (oriented_missing_rooted_on_stage w h m hm)




@[expose] noncomputable def primedDartMapOriented_inducedEmbedding
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) (hm : 1 ≤ m) :
    RootedInducedEmbedding (primedRootedStage w h m hm)
      (kmswRootedStage w (primedStageTime w h m)) := by
  have cast_rot {k l : ℕ} (hk : k = l)
      (M : RootedDirectedMapWithMissing (StageDart k)) :
      (oriented_cast_rooted hk M).map.rot = StageRotation.resize hk M.map.rot := by
    cases hk
    rfl
  have cast_flip {k l : ℕ} (hk : k = l)
      (M : RootedDirectedMapWithMissing (StageDart k))
      (hf : M.map.edgeInv = edgeFlip k) :
      (oriented_cast_rooted hk M).map.edgeInv = edgeFlip l := by
    cases hk
    exact hf
  have cast_missing {k l : ℕ} (hk : k = l)
      (M : RootedDirectedMapWithMissing (StageDart k)) (d : StageDart l) :
      (oriented_cast_rooted hk M).map.missing d ↔
        M.map.missing (Fin.cast hk.symm d.1, d.2) := by
    cases hk
    rfl
  have cast_tail {k l : ℕ} (hk : k = l)
      (M : RootedDirectedMapWithMissing (StageDart k)) (d : StageDart l) :
      (oriented_cast_rooted hk M).map.tail d ↔
        M.map.tail (Fin.cast hk.symm d.1, d.2) := by
    cases hk
    rfl
  have cast_root {k l : ℕ} (hk : k = l)
      (M : RootedDirectedMapWithMissing (StageDart k)) :
      (oriented_cast_rooted hk M).root = (Fin.cast hk M.root.1, M.root.2) := by
    cases hk
    rfl
  let u := primedCode (primedSimInput w) h
  have hrot : (primedRootedStage w h m hm).map.rot = primedLocalRot u m :=
    cast_rot _ _
  have hflip : (primedRootedStage w h m hm).map.edgeInv =
      edgeFlip (kmswMissingRootStage u m).nextEdge :=
    cast_flip _ _ rfl
  have hmissing (d) : (primedRootedStage w h m hm).map.missing d ↔
      (kmswMissingRootStage u m).present d.1.val = false :=
    cast_missing _ _ d
  have htail (d) : (primedRootedStage w h m hm).map.tail d ↔
      (kmswMissingRootStage u m).present d.1.val = true ∧ d.2 = false :=
    cast_tail _ _ d
  refine { dartMap := primedDartMapOriented w h m
           injective := primedDartMapOriented_injective w h m
           flip_comm := ?_
           present := ?_
           tail_comm := ?_
           rot_induced := ?_
           root_comm := ?_ }
  · intro d
    rw [hflip]
    exact primedDartMapOriented_flip_comm w h m d
  · intro d hd
    exact primedDartMapOriented_present w h m d (fun he => hd ((hmissing d).mpr he))
  · intro d hd
    rw [htail]
    exact primedDartMapOriented_tail w h m d (fun he => hd ((hmissing d).mpr he))
  · rw [hrot]
    exact primedRotInducedOriented_all w h m
  · have hr := cast_root
      (kmswMissingRootStage_agree u m).2.1.symm
      (oriented_missing_rooted_on_stage w h m hm)
    change primedDartMapOriented w h m (primedRootedStage w h m hm).root = _
    rw [show (primedRootedStage w h m hm).root = _ from hr]
    have ha := (kmswMissingRootStage_agree u m).2.2.2.2.2.2.1
    have he := primedDartMapOriented_root w h m hm
    have harg : (Fin.cast (kmswMissingRootStage_agree u m).2.1.symm
        (oriented_missing_rooted_on_stage w h m hm).root.1,
        (oriented_missing_rooted_on_stage w h m hm).root.2) =
        (⟨(kmswMissingRootStage u m).active, by rw [(kmswMissingRootStage_agree u m).2.1, ha]; exact act_lt_nextEdge u le_rfl⟩, false) := by
      apply Prod.ext
      · exact Fin.ext ha.symm
      · rfl
    rw [harg]
    exact he



theorem primedDartMapOriented_inducedEmbedding_dartMap
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) (hm : 1 ≤ m) :
    (primedDartMapOriented_inducedEmbedding w h m hm).dartMap =
      primedDartMapOriented w h m := rfl

end DirectedDistances.KMSW
