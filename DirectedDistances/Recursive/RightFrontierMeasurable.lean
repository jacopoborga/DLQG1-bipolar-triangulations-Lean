module

public import DirectedDistances.Recursive.RightFrontierEnvelope
public import DirectedDistances.Recursive.IndependenceFromLR
public import DirectedDistances.Probability.FrontierIndependence
public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.Recursive.RightStationaryBusemann
import DirectedDistances.KMSW.RightHitFrontierEntries
import DirectedDistances.KMSW.WalkRecordCounts
import DirectedDistances.KMSW.LeftStationaryGeometry

/-! # Past-measurable right frontier envelopes

Past-measurable frontier decomposition of D₁ at τ₁, for the `hfrontR`
hypothesis in the `item-busemann-ind` reduction (plan B.2 in
paper results; F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Probability

/-- Indices of early-reachable vertices in the ordered cutoff west frontier -/
@[expose] def rightPastFrontierIndices (k : ℕ) (p : ℕ → Fin 3) : Set ℕ :=
  {j | ∃ u,
    ((kmswStage p k).UL.reverse.map (kmswStage p k).west)[j]? = some u ∧
    (earlyPathLengths p k 0 u).Nonempty}



@[expose] noncomputable def rightPastSdpCoefficient (k : ℕ) (p : ℕ → Fin 3)
    (j : ℕ) : ℤ :=
  ((earlySdp p k ⟨0⟩
    ⟨(((kmswStage p k).UL.reverse.map (kmswStage p k).west)[j]?).getD 0⟩).toNat : ℤ)

/-- The longest early coefficient at an ordered west entry. Its use on the
actual frontier is finite by `RightFrontierEnvelope`. Plan B.2; F1/F4 remain. -/
@[expose] noncomputable def rightPastLdpCoefficient (k : ℕ) (p : ℕ → Fin 3)
    (j : ℕ) : ℤ :=
  (((earlyLdp p k ⟨0⟩
    ⟨(((kmswStage p k).UL.reverse.map (kmswStage p k).west)[j]?).getD 0⟩).unbotD 0 : ℕ) : ℤ)



@[expose] noncomputable def rightPastSdpEnvelope (k : ℕ) (p : ℕ → Fin 3)
    (x : ℕ → ℤ) : ℤ :=
  -(sInf ((fun j => rightPastSdpCoefficient k p j + x j) '' rightPastFrontierIndices k p))



@[expose] noncomputable def rightPastLdpEnvelope (k : ℕ) (p : ℕ → Fin 3)
    (x : ℕ → ℤ) : ℤ :=
  -(sSup ((fun j => rightPastLdpCoefficient k p j + x j) '' rightPastFrontierIndices k p))

private theorem past_indices_congr {k : ℕ} {p q : ℕ → Fin 3}
    (hp : ∀ i, i < k → p i = q i) :
    rightPastFrontierIndices k p = rightPastFrontierIndices k q := by
  ext j
  simp only [rightPastFrontierIndices, Set.mem_ofPred_eq, kmswStage_congr hp,
    earlyPathLengths_congr k 0 _ hp]

private theorem past_sdp_congr {k : ℕ} {p q : ℕ → Fin 3}
    (hp : ∀ i, i < k → p i = q i) (j : ℕ) :
    rightPastSdpCoefficient k p j = rightPastSdpCoefficient k q j := by
  unfold rightPastSdpCoefficient
  rw [kmswStage_congr hp, earlySdp_congr k 0 _ hp]

private theorem past_ldp_congr {k : ℕ} {p q : ℕ → Fin 3}
    (hp : ∀ i, i < k → p i = q i) (j : ℕ) :
    rightPastLdpCoefficient k p j = rightPastLdpCoefficient k q j := by
  unfold rightPastLdpCoefficient
  rw [kmswStage_congr hp, earlyLdp_congr k 0 _ hp]

private def extendPast (k : ℕ) (p : Fin k → Fin 3) : ℕ → Fin 3 :=
  fun i => if hi : i < k then p ⟨i, hi⟩ else 0



theorem measurable_rightPastSdpEnvelope (k : ℕ) :
    Measurable (Function.uncurry (rightPastSdpEnvelope k)) := by
  have hm : ∀ q : Fin k → Fin 3,
      Measurable (fun z : (ℕ → Fin 3) × (ℕ → ℤ) =>
        rightPastSdpEnvelope k (extendPast k q) z.2) := by
    intro q
    exact (Measurable.sInf (Set.to_countable _) (fun j _ =>
      measurable_const.add ((measurable_pi_apply j).comp measurable_snd))).neg
  have hh : Measurable (fun z : ((ℕ → Fin 3) × (ℕ → ℤ)) × (Fin k → Fin 3) =>
      rightPastSdpEnvelope k (extendPast k z.2) z.1.2) :=
    measurable_from_prod_countable_left hm
  have hg : Measurable (fun z : (ℕ → Fin 3) × (ℕ → ℤ) =>
      (z, fun i : Fin k => z.1 i)) :=
    measurable_id.prodMk (measurable_pi_iff.mpr fun _ =>
      (measurable_pi_apply _).comp measurable_fst)
  convert hh.comp hg using 1
  funext z
  have hp : ∀ i, i < k → z.1 i = extendPast k (fun i : Fin k => z.1 i) i := by
    intro i hi
    simp only [extendPast, dite_eq_left hi]
  simp only [Function.uncurry, Function.comp_apply, rightPastSdpEnvelope,
    past_indices_congr hp, past_sdp_congr hp]



theorem measurable_rightPastLdpEnvelope (k : ℕ) :
    Measurable (Function.uncurry (rightPastLdpEnvelope k)) := by
  have hm : ∀ q : Fin k → Fin 3,
      Measurable (fun z : (ℕ → Fin 3) × (ℕ → ℤ) =>
        rightPastLdpEnvelope k (extendPast k q) z.2) := by
    intro q
    exact (Measurable.sSup (Set.to_countable _) (fun j _ =>
      measurable_const.add ((measurable_pi_apply j).comp measurable_snd))).neg
  have hh : Measurable (fun z : ((ℕ → Fin 3) × (ℕ → ℤ)) × (Fin k → Fin 3) =>
      rightPastLdpEnvelope k (extendPast k z.2) z.1.2) :=
    measurable_from_prod_countable_left hm
  have hg : Measurable (fun z : (ℕ → Fin 3) × (ℕ → ℤ) =>
      (z, fun i : Fin k => z.1 i)) :=
    measurable_id.prodMk (measurable_pi_iff.mpr fun _ =>
      (measurable_pi_apply _).comp measurable_fst)
  convert hh.comp hg using 1
  funext z
  have hp : ∀ i, i < k → z.1 i = extendPast k (fun i : Fin k => z.1 i) i := by
    intro i hi
    simp only [extendPast, dite_eq_left hi]
  simp only [Function.uncurry, Function.comp_apply, rightPastLdpEnvelope,
    past_indices_congr hp, past_ldp_congr hp]

-- Local stack facts supply the bounded converse to the ordered alternative.
private theorem shiftLimitVertex_activeInitial_rightHitEntries
    (w : ℕ → Fin 3) (t n : ℕ) :
    shiftLimitVertex w t ⟨activeInitial (fun i => w (t + i)) n⟩ =
      ⟨activeInitial w (t + n)⟩ := by
  let ws := fun i => w (t + i)
  let e : {e : ℕ // EdgePresent ws e} :=
    ⟨act ws n, kmswShift_active_edge_present_limit w t n⟩
  have htime : actTime ws e.val e.property = n :=
    (actTime_eq_iff ws _ _ n).2 rfl
  have hmap : shiftLimitEdge w t e = act w (t + n) := by
    change act w (t + actTime ws e.val e.property) = act w (t + n)
    rw [htime]
  have hinc := (shiftLimitEdge_incidence w t e).1
  rw [hmap] at hinc
  exact congrArg PresentVertex.mk hinc.symm

private theorem rightEntries_coord_L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem rightEntries_L_shift (w : ℕ → Fin 3) (t n : ℕ) :
    L w (t + n) = L w t + L (fun i => w (t + i)) n := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
    rw [Nat.add_succ, rightEntries_coord_L_succ w (t + n),
      rightEntries_coord_L_succ (fun i => w (t + i)) n, ih]
    omega

private theorem rightEntries_boundaryHitTime_left_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k,
      L w (boundaryHitTime w h k) < L w j := by
  have htime : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  have hzero : L w 0 = 0 := by simp [L]
  have hstep : ∀ n, |L w (n + 1) - L w n| ≤ 1 := by
    intro n
    have hsum : L w (n + 1) = L w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
    rw [hsum]
    have hcoord : |(RandomWalk.lazyTwoDimensionalStep (w n)).1| ≤ 1 := by
      have hc : w n = 0 ∨ w n = 1 ∨ w n = 2 := by
        have := (w n).isLt
        omega
      rcases hc with h0 | h1 | h2
      · rw [h0]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
      · rw [h1]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
      · rw [h2]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
    simpa only [add_sub_cancel_left] using hcoord
  have hchar := (strict_running_minimum_iff_first_hit (L w) hzero hstep
      (boundaryHitTime w h k) (boundaryHitTime w h k) k (by omega)
      (h.leftHit k hk)).2
      ⟨le_rfl, boundaryHitTime_left_spec w h hk, htime⟩
  intro j hj
  exact (Finset.mem_filter.mp hchar.1).2 j hj

private theorem rightEntries_ul_allocated (w : ℕ → Fin 3) {n e : ℕ}
    (he : e ∈ (kmswStage w n).UL) : e < (kmswStage w n).nextEdge := by
  rw [kmswStage_UL_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hmn := List.mem_range.mp (List.mem_filter.mp hm).1
  exact act_lt_nextEdge w (by omega)

private theorem rightEntries_reverse_dropLast (xs : List ℕ) :
    xs.dropLast.reverse = xs.reverse.tail := by
  simpa only [List.reverse_reverse] using
    congrArg List.reverse (List.dropLast_reverse (l := xs.reverse))

private theorem rightEntries_step_UL_reverse (s : State) (c : Fin 3) :
    (kmswStep s c).UL.reverse = (kmswStep s c).active ::
      (if c = 0 then s.UL.reverse.tail.tail
        else if c = 1 then s.UL.reverse.tail else s.UL.reverse) := by
  fin_cases c
  · change (kmswStepOfStep s .left).UL.reverse =
      (kmswStepOfStep s .left).active :: s.UL.reverse.tail.tail
    cases hs : s.UL.dropLast.reverse <;>
      simp only [kmswStepOfStep, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append,
        List.reverse_reverse, ← rightEntries_reverse_dropLast, hs,
        List.tail_cons, List.tail_nil]
  · change (kmswStepOfStep s .up).UL.reverse =
      (kmswStepOfStep s .up).active :: s.UL.reverse.tail
    simp only [kmswStepOfStep, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append,
      rightEntries_reverse_dropLast]
  · change (kmswStepOfStep s .down).UL.reverse =
      (kmswStepOfStep s .down).active :: s.UL.reverse
    cases hs : s.UR <;> simp [kmswStepOfStep, hs]

private theorem rightEntries_westStack_old_map (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.reverse.map (kmswStage w (n + 1)).west =
      CutConverse.westStack w n := by
  apply List.map_congr_left
  intro e he
  exact (kmswStage_endpoints_stable w (Nat.le_succ n)
    (rightEntries_ul_allocated w (List.mem_reverse.mp he))).1

private theorem rightEntries_westStack_down (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) :
    (CutConverse.westStack w (n + 1)).tail = CutConverse.westStack w n := by
  have hs := rightEntries_step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp only [hc, h0, h1, ↓reduceIte] at hs
  change ((kmswStage w (n + 1)).UL.reverse.map
    (kmswStage w (n + 1)).west).tail = _
  rw [hs]
  simp only [List.map_cons, List.tail_cons]
  exact rightEntries_westStack_old_map w n

private theorem rightEntries_westStack_up (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    CutConverse.westStack w (n + 1) = CutConverse.westStack w n := by
  have hs := rightEntries_step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (1 : Fin 3) ≠ 0 := by decide
  simp only [hc, h0, ↓reduceIte] at hs
  have ht := congrArg List.tail (rightEntries_westStack_old_map w n)
  simp only [← List.map_tail] at ht
  have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).west (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  unfold CutConverse.westStack
  rw [hs, List.map_cons]
  change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
  rw [ht, hw]
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  simp [CutConverse.westStack, hes, act]

private theorem rightEntries_westStack_left (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) (hlen : 2 ≤ (kmswStage w n).UL.length) :
    CutConverse.westStack w (n + 1) = (CutConverse.westStack w n).tail := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  have hnon : es.reverse ≠ [] := by
    intro he
    have hlen' := congrArg List.length he
    rw [hes] at hlen
    simp only [List.length_reverse, List.length_nil] at hlen'
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  cases he : es.reverse with
  | nil => exact (hnon he).elim
  | cons e rest =>
    have hrev : (kmswStage w n).UL.reverse = act w n :: e :: rest := by
      simp only [hes, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, he, act]
    have hdrop : (kmswStage w n).UL.dropLast.reverse = e :: rest := by
      rw [rightEntries_reverse_dropLast, hrev, List.tail_cons]
    have hs := rightEntries_step_UL_reverse (kmswStage w n) (w n)
    change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
    simp only [hc, ↓reduceIte, hrev, List.tail_cons] at hs
    have ht := congrArg (fun xs : List ℕ => xs.tail.tail)
      (rightEntries_westStack_old_map w n)
    simp only [← List.map_tail, hrev, List.tail_cons] at ht
    have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
        (kmswStage w n).west e := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
        hdrop, State.addEdge]
    unfold CutConverse.westStack
    rw [hs, List.map_cons]
    change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
    rw [hw, ht]
    simp [CutConverse.westStack, hrev]

private theorem rightEntries_westStack_left_short (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 0) (hlen : (kmswStage w n).UL.length < 2) :
    CutConverse.westStack w (n + 1) = [(kmswStage w n).nextVertex] := by
  have hd : (kmswStage w n).UL.dropLast.reverse = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [List.length_reverse, List.length_dropLast]
    omega
  simp [CutConverse.westStack, kmswStage, kmswStep, kmswCodeStep, hw,
    kmswStepOfStep, hd, State.addEdge]

private theorem rightEntries_westStack_head (w : ℕ → Fin 3) (n : ℕ) :
    CutConverse.westStack w n =
      activeInitial w n :: (CutConverse.westStack w n).tail := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  rw [CutConverse.activeInitial_eq]
  simp [CutConverse.westStack, hes, act]

private theorem rightEntries_westStack_excursion (w : ℕ → Fin 3)
    {a n : ℕ} (han : a ≤ n)
    (habove : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j) :
    (CutConverse.westStack w n).drop (L w n - L w a).toNat =
      CutConverse.westStack w a := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n han ih =>
    have hprior : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j :=
      fun j haj hjn => habove j haj (by omega)
    have hi := ih hprior
    have hn := habove n han (by omega)
    have hnext := habove (n + 1) (by omega) (le_refl _)
    have hc := rightEntries_coord_L_succ w n
    by_cases h0 : w n = 0
    · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hc
      change L w (n + 1) = L w n - 1 at hc
      have hlen := kmswStage_UL_length w n
      have hmin := runningMin_le (L w) n a han
      change minL w n ≤ L w a at hmin
      have hlen2 : 2 ≤ (kmswStage w n).UL.length := by omega
      rw [rightEntries_westStack_left w n h0 hlen2]
      have hidx : (L w n - L w a).toNat =
          (L w (n + 1) - L w a).toNat + 1 := by omega
      rw [hidx] at hi
      simpa only [List.drop_tail] using hi
    · by_cases h1 : w n = 1
      · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hc
        dsimp at hc
        rw [add_zero] at hc
        rw [rightEntries_westStack_up w n h1, hc]
        exact hi
      · have h2 : w n = 2 := by
          apply Fin.ext
          have := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
          omega
        rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hc
        dsimp at hc
        have hidx : (L w (n + 1) - L w a).toNat =
            (L w n - L w a).toNat + 1 := by omega
        rw [hidx, ← List.drop_tail, rightEntries_westStack_down w n h2]
        exact hi

private theorem rightEntries_shifted_left_hit_stack (w : ℕ → Fin 3) (t : ℕ)
    (hs : BoundaryHitWitnesses (fun i => w (t + i))) :
    let ws := fun i => w (t + i)
    let τ : ℕ → ℕ := fun j =>
      if j = 0 then 0 else boundaryHitTime ws hs (-(j : ℤ))
    let F := CutConverse.westStack w t
    ∀ j,
      (j < F.length ∧ CutConverse.westStack w (t + τ j) = F.drop j) ∨
      (F.length ≤ j ∧
        CutConverse.westStack w (t + τ j) =
          [activeInitial w (t + τ j)] ∧
        (kmswStage w t).nextVertex ≤ activeInitial w (t + τ j)) := by
  let ws := fun i => w (t + i)
  let τ : ℕ → ℕ := fun j =>
    if j = 0 then 0 else boundaryHitTime ws hs (-(j : ℤ))
  let F := CutConverse.westStack w t
  change ∀ j,
    (j < F.length ∧ CutConverse.westStack w (t + τ j) = F.drop j) ∨
    (F.length ≤ j ∧
      CutConverse.westStack w (t + τ j) =
        [activeInitial w (t + τ j)] ∧
      (kmswStage w t).nextVertex ≤ activeInitial w (t + τ j))
  have hlevel : ∀ j, L ws (τ j) = -(j : ℤ) := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [τ, L]
    · have hk : -(j : ℤ) ≤ -1 := by omega
      simp only [τ, ite_eq_right hj]
      exact boundaryHitTime_left_spec ws hs hk
  have hstackLen (n : ℕ) :
      (CutConverse.westStack w n).length = (kmswStage w n).UL.length := by
    simp [CutConverse.westStack]
  have hFpos : 0 < F.length := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last w t
    simp [F, CutConverse.westStack, hes]
  intro j
  induction j with
  | zero =>
    left
    constructor
    · exact hFpos
    · simp [F, τ]
  | succ j ih =>
    have hτle : τ j ≤ τ (j + 1) := by
      by_cases hj : j = 0
      · subst j
        simp [τ]
      · have hk : (-(j : ℤ)) ≤ -1 := by omega
        have hanti := boundaryHitTime_left_antitone ws hs
          (a := -((j + 1 : ℕ) : ℤ)) (b := -(j : ℤ))
          hk (by omega)
        simpa [τ, hj] using hanti
    have hτlt : τ j < τ (j + 1) := by
      by_contra hnot
      have heq : τ j = τ (j + 1) := by omega
      have hh := hlevel (j + 1)
      rw [← heq, hlevel j] at hh
      omega
    have hmpos : 0 < τ (j + 1) := by omega
    let r := τ (j + 1) - 1
    have hradd : r + 1 = τ (j + 1) := by dsimp [r]; omega
    have hrlt : r < τ (j + 1) := by omega
    have hk : -((j + 1 : ℕ) : ℤ) ≤ -1 := by omega
    have hrecord : ∀ q, q < τ (j + 1) →
        -((j + 1 : ℕ) : ℤ) < L ws q := by
      intro q hq
      have ht : τ (j + 1) = boundaryHitTime ws hs (-((j + 1 : ℕ) : ℤ)) := by
        simp [τ]
      have hq' : q < boundaryHitTime ws hs (-((j + 1 : ℕ) : ℤ)) := by
        rw [← ht]
        exact hq
      have hh := rightEntries_boundaryHitTime_left_record ws hs hk q hq'
      rw [← ht, hlevel (j + 1)] at hh
      exact hh
    have hsum : L ws (r + 1) = L ws r +
        (RandomWalk.lazyTwoDimensionalStep (ws r)).1 :=
      rightEntries_coord_L_succ ws r
    rw [hradd, hlevel (j + 1)] at hsum
    have hcoordLow : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (ws r)).1 := by
      have hc (c : Fin 3) :
          -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).1 := by
        fin_cases c <;> norm_num [RandomWalk.lazyTwoDimensionalStep]
      exact hc (ws r)
    have hrlevel : L ws r = -(j : ℤ) := by
      have hh := hrecord r hrlt
      omega
    have hleft : ws r = 0 := by
      have hdelta : (RandomWalk.lazyTwoDimensionalStep (ws r)).1 = -1 := by
        omega
      have hc (c : Fin 3) :
          (RandomWalk.lazyTwoDimensionalStep c).1 = -1 → c = 0 := by
        fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]
      exact hc (ws r) hdelta
    have hbase : τ j ≤ r := by omega
    have habove : ∀ q, t + τ j ≤ q → q ≤ t + r → L w (t + τ j) ≤ L w q := by
      intro q hqlo hqhi
      have hqshift : q = t + (q - t) := by omega
      have hqrange : τ j ≤ q - t ∧ q - t < τ (j + 1) := by omega
      have hh := hrecord (q - t) hqrange.2
      have hlevelq : -(j : ℤ) ≤ L ws (q - t) := by omega
      calc
        L w (t + τ j) = L w t + L ws (τ j) := rightEntries_L_shift w t (τ j)
        _ ≤ L w t + L ws (q - t) := by
          rw [hlevel j]
          omega
        _ = L w q := by
          rw [← rightEntries_L_shift w t (q - t), ← hqshift]
    have hexc := rightEntries_westStack_excursion w
      (by omega : t + τ j ≤ t + r) habove
    have hglobalLevel : L w (t + r) = L w (t + τ j) := by
      rw [rightEntries_L_shift w t r, rightEntries_L_shift w t (τ j),
        hrlevel, hlevel j]
    have hstackEq : CutConverse.westStack w (t + r) =
        CutConverse.westStack w (t + τ j) := by
      simpa only [hglobalLevel, sub_self, Int.toNat_zero, List.drop_zero] using hexc
    have hnextIndex : t + r + 1 = t + τ (j + 1) := by omega
    have hnextVertexMono : (kmswStage w t).nextVertex ≤
        (kmswStage w (t + r)).nextVertex :=
      CutConverse.nextVertex_mono w (by omega)
    have hstackHead (n : ℕ) :
        CutConverse.westStack w n =
          activeInitial w n :: (CutConverse.westStack w n).tail :=
      rightEntries_westStack_head w n
    rcases ih with ⟨hjlen, hJ⟩ | ⟨hJlen, hJ, hfresh⟩
    · by_cases hmore : j + 1 < F.length
      · left
        constructor
        · exact hmore
        · have hlong : 2 ≤ (kmswStage w (t + r)).UL.length := by
            rw [← hstackLen, hstackEq, hJ]
            simp only [List.length_drop]
            omega
          have hleftStack := rightEntries_westStack_left w (t + r) hleft hlong
          rw [← hnextIndex, hleftStack, hstackEq, hJ]
          rw [List.drop_eq_getElem_cons hjlen]
          rfl
      · have hlenEq : F.length = j + 1 := by omega
        right
        refine ⟨by omega, ?_, ?_⟩
        · have hshort : (kmswStage w (t + r)).UL.length < 2 := by
            rw [← hstackLen, hstackEq, hJ]
            simp only [List.length_drop]
            omega
          have hleftStack := rightEntries_westStack_left_short w (t + r)
            hleft hshort
          rw [← hnextIndex, hleftStack]
          have hAI : activeInitial w (t + r + 1) =
              (kmswStage w (t + r)).nextVertex := by
            have hh := (hstackHead (t + r + 1)).symm.trans hleftStack
            exact (List.cons.inj hh).1
          rw [hAI]
        · have hshort : (kmswStage w (t + r)).UL.length < 2 := by
            rw [← hstackLen, hstackEq, hJ]
            simp only [List.length_drop]
            omega
          have hleftStack := rightEntries_westStack_left_short w (t + r)
            hleft hshort
          have hAI : activeInitial w (t + r + 1) =
              (kmswStage w (t + r)).nextVertex := by
            have hh := (hstackHead (t + r + 1)).symm.trans hleftStack
            exact (List.cons.inj hh).1
          rw [← hnextIndex, hAI]
          exact hnextVertexMono
    · right
      refine ⟨by omega, ?_, ?_⟩
      · have hshort : (kmswStage w (t + r)).UL.length < 2 := by
          rw [← hstackLen, hstackEq, hJ]
          simp only [List.length_singleton]
          omega
        have hleftStack := rightEntries_westStack_left_short w (t + r) hleft hshort
        rw [← hnextIndex, hleftStack]
        have hAI : activeInitial w (t + r + 1) =
            (kmswStage w (t + r)).nextVertex := by
          have hh := (hstackHead (t + r + 1)).symm.trans hleftStack
          exact (List.cons.inj hh).1
        rw [hAI]
      · have hshort : (kmswStage w (t + r)).UL.length < 2 := by
          rw [← hstackLen, hstackEq, hJ]
          simp only [List.length_singleton]
          omega
        have hleftStack := rightEntries_westStack_left_short w (t + r) hleft hshort
        have hAI : activeInitial w (t + r + 1) =
            (kmswStage w (t + r)).nextVertex := by
          have hh := (hstackHead (t + r + 1)).symm.trans hleftStack
          exact (List.cons.inj hh).1
        rw [← hnextIndex, hAI]
        exact hnextVertexMono


private theorem ordered_entry_eq (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (j : ℕ)
    (hbound : j < ((kmswStage w (boundaryHitTime w h 1)).UL.reverse.map
      (kmswStage w (boundaryHitTime w h 1)).west).length) :
    ((kmswStage w (boundaryHitTime w h 1)).UL.reverse.map
      (kmswStage w (boundaryHitTime w h 1)).west)[j]? =
      some (shiftLimitVertex w (boundaryHitTime w h 1)
        ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩).id := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let F := (kmswStage w t).UL.reverse.map (kmswStage w t).west
  let τ : ℕ → ℕ := fun j =>
    if j = 0 then 0 else boundaryHitTime ws hs (-(j : ℤ))
  have hF : F = CutConverse.westStack w t := rfl
  have hcore := rightEntries_shifted_left_hit_stack w t hs j
  change
    (j < (CutConverse.westStack w t).length ∧
      CutConverse.westStack w (t + τ j) = (CutConverse.westStack w t).drop j) ∨
    ((CutConverse.westStack w t).length ≤ j ∧
      CutConverse.westStack w (t + τ j) = [activeInitial w (t + τ j)] ∧
      (kmswStage w t).nextVertex ≤ activeInitial w (t + τ j)) at hcore
  have hlabel : boundaryVertex ws hs (-(j : ℤ)) = activeInitial ws (τ j) := by
    by_cases hj : j = 0
    · subst j
      simp [τ, boundaryVertex_zero, activeInitial, act, edgeWest,
        kmswStage, kmswInit]
    · have hk : -(j : ℤ) ≤ -1 := by omega
      have ht : τ j = boundaryHitTime ws hs (-(j : ℤ)) := by simp [τ, hj]
      rw [ht]
      exact boundaryVertex_left_hit_eq ws hs hk
  have hvertex : shiftLimitVertex w t
      ⟨boundaryVertex ws hs (-(j : ℤ))⟩ =
        ⟨activeInitial w (t + τ j)⟩ := by
    calc
      shiftLimitVertex w t ⟨boundaryVertex ws hs (-(j : ℤ))⟩ =
          shiftLimitVertex w t ⟨activeInitial ws (τ j)⟩ := by
            rw [hlabel]
      _ = ⟨activeInitial w (t + τ j)⟩ :=
        shiftLimitVertex_activeInitial_rightHitEntries w t (τ j)
  obtain ⟨hj, hstack⟩ := hcore.resolve_right (by
    rintro ⟨hge, -, -⟩
    change j < (CutConverse.westStack w t).length at hbound
    omega)
  have hdrop : F.drop j =
      activeInitial w (t + τ j) :: (F.drop j).tail := by
    calc
      F.drop j = CutConverse.westStack w (t + τ j) := hstack.symm
      _ = activeInitial w (t + τ j) ::
          (CutConverse.westStack w (t + τ j)).tail :=
        rightEntries_westStack_head w (t + τ j)
      _ = activeInitial w (t + τ j) :: (F.drop j).tail := by
        congr 1
        rw [hF, hstack]
  have hgetval : F[j] = activeInitial w (t + τ j) := by
    have hjF : j < F.length := by simpa [hF] using hj
    have hh := List.drop_eq_getElem_cons hjF
    rw [hdrop] at hh
    exact (List.cons.inj hh).1.symm
  have hget : F[j]? = some (activeInitial w (t + τ j)) :=
    List.getElem?_eq_some_iff.mpr ⟨hj, hgetval⟩
  have hid : (shiftLimitVertex w t
      ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id =
      activeInitial w (t + τ j) := by
    simpa using congrArg PresentVertex.id hvertex
  rw [← hid] at hget
  exact hget
private theorem early_path_endpoint {w : ℕ → Fin 3} {t : ℕ}
    {a b : PresentVertex w} (q : Path a b)
    (hq : ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e, actTime w e he < t) :
    b = a ∨ ∃ e, ∃ he : EdgePresent w e, actTime w e he < t ∧ edgeEast w e = b.id := by
  cases q with
  | nil => exact Or.inl rfl
  | @cons c d q e =>
    exact Or.inr ⟨e.val, e.property.1,
      hq e.val (List.mem_append_right _ (List.mem_singleton.mpr rfl)) e.property.1,
      e.property.2.2⟩

private theorem reachable_ordered_entry (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    {j : ℕ} (hj : j ∈ rightFrontierIndices w h hs) :
    ((kmswStage w (boundaryHitTime w h 1)).UL.reverse.map
      (kmswStage w (boundaryHitTime w h 1)).west)[j]? =
      some (shiftLimitVertex w (boundaryHitTime w h 1)
        ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩).id := by
  rcases rightHit_shifted_negative_label_ordered_frontier_or_no_early_edge w h hs j
      with he | hn
  · exact he
  · obtain ⟨n, q, _, hq⟩ := hj
    rcases early_path_endpoint q hq with hz | ⟨e, he, het, heu⟩
    ·
      have hroot : EdgePresent w 0 :=
        EdgePresent.of_stage_present (n := 0) (by change 0 < 1; omega) (by rfl)
      have ht : 0 < boundaryHitTime w h 1 := by
        have hh := boundaryHitTime_right_spec w h (show (1 : ℤ) ≤ 1 by omega)
        by_contra hh'
        have hz : boundaryHitTime w h 1 = 0 := by omega
        rw [hz] at hh
        simp [R] at hh
      have htime : actTime w 0 hroot = 0 := (actTime_eq_iff w 0 hroot 0).mpr rfl
      have hne := (hn 0 hroot (by rw [htime]; exact ht)).1
      have hid := congrArg PresentVertex.id hz
      exact (hne (by rw [hid]; simp [edgeWest, kmswStage, kmswInit, boundaryVertex_zero])).elim
    · exact ((hn e he het).2 heu).elim

/-- Exact cutoff-prefix characterization of the right frontier indices
not counted as a paper result; F1/F4 remain. -/
theorem rightPastFrontierIndices_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h 1 → w i = p i) :
    rightPastFrontierIndices (boundaryHitTime w h 1) p =
      rightFrontierIndices w h hs := by
  rw [← past_indices_congr hp]
  ext j
  constructor
  · rintro ⟨u, hu, hr⟩
    have he := ordered_entry_eq w h hs j (List.getElem?_eq_some_iff.mp hu).1
    have hu' := Option.some.inj (hu.symm.trans he)
    rw [hu'] at hr
    simpa only [rightFrontierIndices, Set.mem_ofPred_eq, boundaryVertex_zero] using hr
  · intro hj
    refine ⟨_, reachable_ordered_entry w h hs hj, ?_⟩
    simpa only [rightFrontierIndices, Set.mem_ofPred_eq, boundaryVertex_zero] using hj

private theorem sdp_coefficient_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h 1 → w i = p i)
    {j : ℕ} (hj : j ∈ rightFrontierIndices w h hs) :
    rightPastSdpCoefficient (boundaryHitTime w h 1) p j =
      ((earlySdp w (boundaryHitTime w h 1) (boundaryPresentVertex w h 0)
        (shiftLimitVertex w (boundaryHitTime w h 1)
          ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩)).toNat : ℤ) := by
  rw [← past_sdp_congr hp]
  unfold rightPastSdpCoefficient
  rw [reachable_ordered_entry w h hs hj]
  simp only [Option.getD_some, boundaryPresentVertex, boundaryVertex_zero]

private theorem ldp_coefficient_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h 1 → w i = p i)
    {j : ℕ} (hj : j ∈ rightFrontierIndices w h hs) :
    rightPastLdpCoefficient (boundaryHitTime w h 1) p j =
      (((earlyLdp w (boundaryHitTime w h 1) (boundaryPresentVertex w h 0)
        (shiftLimitVertex w (boundaryHitTime w h 1)
          ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩)).unbotD 0 : ℕ) : ℤ) := by
  rw [← past_ldp_congr hp]
  unfold rightPastLdpCoefficient
  rw [reachable_ordered_entry w h hs hj]
  simp only [Option.getD_some, boundaryPresentVertex, boundaryVertex_zero]

/-- SDP Busemann difference from the cutoff prefix and shifted negative labels -/
theorem rightPastSdpEnvelope_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannSDP (boundaryPresentVertex _ hs) Xs)
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h 1 → w i = p i) :
    X 1 - X 0 = rightPastSdpEnvelope (boundaryHitTime w h 1) p
      (fun j => Xs (-(j : ℤ))) := by
  rw [rightFrontier_sdp_busemann w h hs
    (rightHit_crossing_eq_shifted_west_label w h hs) X Xs hX hXs]
  rw [Finset.inf'_eq_csInf_image, Set.Finite.coe_toFinset]
  unfold rightPastSdpEnvelope
  rw [rightPastFrontierIndices_eq w h hs p hp]
  congr 2
  exact Set.image_congr fun j hj => by
    rw [sdp_coefficient_eq w h hs p hp hj]
    rfl

/-- LDP Busemann difference from the cutoff prefix and shifted negative labels -/
theorem rightPastLdpEnvelope_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded (w := fun i => w (boundaryHitTime w h 1 + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannLDP hbs (boundaryPresentVertex _ hs) Xs)
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h 1 → w i = p i) :
    X 1 - X 0 = rightPastLdpEnvelope (boundaryHitTime w h 1) p
      (fun j => Xs (-(j : ℤ))) := by
  obtain ⟨A, hA, heq⟩ := rightFrontier_ldp_busemann w h hs
    (rightHit_crossing_eq_shifted_west_label w h hs) hb hbs X Xs hX hXs
  rw [heq, Finset.sup'_eq_csSup_image, Set.Finite.coe_toFinset]
  unfold rightPastLdpEnvelope
  rw [rightPastFrontierIndices_eq w h hs p hp]
  congr 2
  apply Set.image_congr
  intro j hj
  rw [ldp_coefficient_eq w h hs p hp hj]
  simp only [boundaryPresentVertex]
  rw [(hA j hj).2]
  rfl

private theorem ae_comp_right_frontier_hit {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂iidCodeMeasure, p (codeShift (codeSndFirstHit (-1) ω).toNat ω) := by
  apply ae_of_ae_map
    (measurable_codeShift_toNat _ (measurableSet_codePast_codeSndFirstHit_eq (-1))).aemeasurable
  rw [map_codeShift_codeSndFirstHit]
  exact hp

private theorem right_frontier_codeShift_future (ω : ℕ → Fin 3) (t : ℕ) :
    (fun i => codeShift t ω (i + 1)) = (fun i => ω ((t + i) + 1)) := by
  funext i
  change (if i + 1 = 0 then 0 else ω (t + (i + 1))) = ω ((t + i) + 1)
  rw [ite_eq_right (by omega : ¬ i + 1 = 0)]
  rfl

private theorem ae_right_frontier_ldp_data :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)),
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion ω) := by
  filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_eq,
    iidCodes_ae_existsUnique_eq_canonicalBusemannLDP] with ω heq hdata
  obtain ⟨hfin, h, X, hX, -, hcanon⟩ := hdata
  refine ⟨presentPathLengthsBounded_of_hfin _ hfin, h, ?_⟩
  rw [heq, ← hcanon]
  exact hX


/-- Past-measurable shortest frontier decomposition of D₁ at τ₁, exactly
`hfrontR` in `busemannSDPMeasurableVersion_ind_of_LR` (plan B.2;
is not counted as a paper result; F1/F4 remain. -/
theorem busemannSDPMeasurableVersion_right_frontier :
    ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂iidCodeMeasure,
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion 1 ω =
          F (codeSndFirstHit (-1) ω).toNat
            (codePastVector (codeSndFirstHit (-1)) ω)
            (fun j => busemannSDPMeasurableVersion
              (codeShift (codeSndFirstHit (-1) ω).toNat ω) (-(j : ℤ))) := by
  refine ⟨rightPastSdpEnvelope, measurable_rightPastSdpEnvelope, ?_⟩
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion,
    ae_comp_right_frontier_hit iidCodes_ae_busemannSDPMeasurableVersion] with ω hdata hsdata
  obtain ⟨h, hX⟩ := hdata
  have hhit := codeSndFirstHit_eq_boundaryHitTime ω h (by omega : (1 : ℤ) ≤ 1)
  have ht : (codeSndFirstHit (-1) ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h 1 := by
    rw [hhit, ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [right_frontier_codeShift_future] at hsdata
  obtain ⟨hs, hXs⟩ := hsdata
  apply rightPastSdpEnvelope_eq (fun i => ω (i + 1)) h hs _ _ hX hXs
  intro i hi
  simp only [codePastVector, hhit, ENat.natCast_lt_natCast, ite_eq_left hi]

/-- Past-measurable longest frontier decomposition of D₁ at τ₁, exactly
`hfrontR` in `busemannLDPMeasurableVersion_ind_of_LR` (plan B.2;
is not counted as a paper result; F1/F4 remain. -/
theorem busemannLDPMeasurableVersion_right_frontier :
    ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂iidCodeMeasure,
        ldpIncrement busemannLDPMeasurableVersion 1 ω =
          F (codeSndFirstHit (-1) ω).toNat
            (codePastVector (codeSndFirstHit (-1)) ω)
            (fun j => busemannLDPMeasurableVersion
              (codeShift (codeSndFirstHit (-1) ω).toNat ω) (-(j : ℤ))) := by
  refine ⟨rightPastLdpEnvelope, measurable_rightPastLdpEnvelope, ?_⟩
  filter_upwards [ae_right_frontier_ldp_data,
    ae_comp_right_frontier_hit ae_right_frontier_ldp_data] with ω hdata hsdata
  obtain ⟨hb, h, hX⟩ := hdata
  have hhit := codeSndFirstHit_eq_boundaryHitTime ω h (by omega : (1 : ℤ) ≤ 1)
  have ht : (codeSndFirstHit (-1) ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h 1 := by
    rw [hhit, ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [right_frontier_codeShift_future] at hsdata
  obtain ⟨hbs, hs, hXs⟩ := hsdata
  apply rightPastLdpEnvelope_eq (fun i => ω (i + 1)) h hs hb hbs _ _ hX hXs
  intro i hi
  simp only [codePastVector, hhit, ENat.natCast_lt_natCast, ite_eq_left hi]

end DirectedDistances.Recursive
