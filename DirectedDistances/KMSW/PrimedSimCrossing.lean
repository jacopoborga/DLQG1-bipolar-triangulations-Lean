module

public import DirectedDistances.KMSW.PrimedSimActiveLeft
public import DirectedDistances.KMSW.FlowLineItems
import DirectedDistances.KMSW.HatTriangleSim
import DirectedDistances.KMSW.OutgoingInterval
import DirectedDistances.KMSW.UIBOTBoundaryM0









public section
namespace DirectedDistances.KMSW

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
Every later exit has a nonempty predecessor stack. In particular the
first-exit empty-predecessor statement does not extend to positive indices. -/
theorem primedCrossing_exit_predecessor_nonempty (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (hk : 0 < k) :
    (kmswStage w (walkNL w h k - 1)).UL.dropLast.reverse ≠ [] := by
  have ht := flowLine_leftExit_triangle w h (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at ht
  obtain ⟨es, hes, _⟩ := ht.2.2.2
  rw [hes]
  exact List.cons_ne_nil _ _

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
`left, up, down, down, left`; its periodic tail is irrelevant to the finite
stage check below. -/
@[expose] def primedCrossingTestCode (n : ℕ) : Fin 3 :=
  ([0, 1, 2, 2, 0] : List (Fin 3)).getD n (if n % 3 = 0 then 2 else 0)

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
singleton UL before re-entry and empty UL predecessors before the later
exit: the successive level minima are `1, 4, 5`, while the stacks retain
the base edge `3`. All bounded first-hit tests and stage identities use
`decide`, without an evaluator trust extension. -/
theorem primedCrossingTestCode_stacks :
    (L primedCrossingTestCode 1 = L primedCrossingTestCode 0 - 1 ∧
      ∀ j ∈ Finset.range 1, 1 ≤ j →
        L primedCrossingTestCode j ≠ L primedCrossingTestCode 0 - 1) ∧
    (R primedCrossingTestCode 4 = R primedCrossingTestCode 1 - 1 ∧
      ∀ j ∈ Finset.range 4, 2 ≤ j →
        R primedCrossingTestCode j ≠ R primedCrossingTestCode 1 - 1) ∧
    (L primedCrossingTestCode 5 = L primedCrossingTestCode 4 - 1 ∧
      ∀ j ∈ Finset.range 5, 5 ≤ j →
        L primedCrossingTestCode j ≠ L primedCrossingTestCode 4 - 1) ∧
    (kmswStage primedCrossingTestCode 3).UL = [3, 4] ∧
    (kmswStage primedCrossingTestCode 4).UL.dropLast = [3, 4] ∧
    (kmswStage primedCrossingTestCode 5).UL = [3, 6] ∧
    (kmswStage primedCrossingTestCode 3).UL ≠
      [(kmswStage primedCrossingTestCode 3).active] ∧
    (kmswStage primedCrossingTestCode 4).UL.dropLast ≠ [] := by
  decide

private theorem UL_across_level_excursion (w : ℕ → Fin 3) {a n : ℕ}
    (han : a < n) (hlevel : L w n = L w a + 1)
    (habove : ∀ j, a < j → j ≤ n → L w a + 1 ≤ L w j) :
    (kmswStage w n).UL = (kmswStage w a).UL ++ [act w n] := by
  classical
  let p : ℕ → Bool := fun m =>
    decide (∀ j, m < j → j ≤ n → L w m + 1 ≤ L w j)
  let q : ℕ → Bool := fun m =>
    decide (∀ j, m < j → j ≤ a → L w m + 1 ≤ L w j)
  have hpq : (List.range (a + 1)).filter p = (List.range (a + 1)).filter q := by
    apply List.filter_congr
    intro m hm
    have hma : m ≤ a := by have := List.mem_range.mp hm; omega
    apply Bool.eq_iff_iff.mpr
    simp only [p, q, decide_eq_true_eq]
    constructor
    · intro h j hmj hja
      exact h j hmj (by omega)
    · intro h j hmj hjn
      by_cases hja : j ≤ a
      · exact h j hmj hja
      · have hj := habove j (by omega) hjn
        by_cases hma' : m = a
        · simpa only [hma'] using hj
        · have hm := h a (by omega) le_rfl
          omega
  have hmiddle : (List.range' (a + 1) (n - (a + 1))).filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hm
    have ham : a < m := by omega
    have hmn : m < n := by omega
    simp only [p, decide_eq_true_eq]
    intro hm
    have hlm := habove m ham (by omega)
    have hln := hm n hmn le_rfl
    omega
  have hrange : List.range (n + 1) =
      (List.range (a + 1) ++ List.range' (a + 1) (n - (a + 1))) ++ [n] := by
    rw [List.range_succ]
    congr 1
    rw [List.range_eq_range', List.range_eq_range']
    have hn : (a + 1) + (n - (a + 1)) = n := by omega
    simpa only [zero_add, hn] using
      (List.range'_append_1 (s := 0) (m := a + 1) (n := n - (a + 1))).symm
  have hpn : p n = true := by
    apply decide_eq_true
    intro j hnj hjn
    omega
  rw [kmswStage_UL_eq, kmswStage_UL_eq]
  change ((List.range (n + 1)).filter p).map (act w) =
    ((List.range (a + 1)).filter q).map (act w) ++ [act w n]
  rw [hrange, List.filter_append, List.filter_append, hpq, hmiddle]
  simp only [List.append_nil, List.filter_cons, hpn, ↓reduceIte,
    List.filter_nil, List.map_append, List.map_cons, List.map_nil]

private theorem before_left_hit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a j : ℕ) (haj : a ≤ j) (hj : j < firstFlowLHit w h a) :
    L w a ≤ L w j := by
  classical
  induction j, haj using Nat.le_induction with
  | base => exact le_rfl
  | succ j haj ih =>
    have hprior := ih (by omega)
    have hs : L w (j + 1) = L w j +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w j)).1 :=
      Finset.sum_range_succ _ _
    have hlow : -1 ≤
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
      have hb := (w j).isLt
      change -1 ≤ ((w j).val : ℤ) - 1
      omega
    have hnot : L w (j + 1) ≠ L w a - 1 := by
      intro heq
      exact (Nat.find_min (h.1 a) hj) ⟨by omega, heq⟩
    omega

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
The entire stack present before right re-entry survives as the predecessor
stack before the left exit. It need not be a singleton. -/
theorem primedCrossing_exit_predecessor_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage w (walkNL w h (k + 1) - 1)).UL.dropLast =
      (kmswStage w (walkNR w h (k + 1) - 1)).UL := by
  let r := walkNR w h (k + 1)
  let t := walkNL w h (k + 1)
  have hr := walkNR_succ_spec w h k
  have ht := walkNL_spec w h (k + 1)
  have hrpos : 0 < r := by dsimp [r]; omega
  have hrt : r ≤ t - 1 := by dsimp [r, t]; omega
  have hentry := congrArg Prod.fst (walkNR_succ_previous_step w h k)
  have hexit := congrArg Prod.fst (walkNL_previous_step w h (k + 1))
  have hlev : L w (t - 1) = L w (r - 1) + 1 := by
    dsimp [r, t] at *
    omega
  have hUL := UL_across_level_excursion w (a := r - 1) (n := t - 1)
    (by omega) hlev (by
      intro j hj hjt
      have hjhit : j < firstFlowLHit w h r := by
        have heq : t = firstFlowLHit w h r := rfl
        rw [← heq]
        omega
      have habove := before_left_hit w h r j (by omega) hjhit
      have he : L w r = L w (r - 1) + 1 := by
        dsimp [r] at *
        omega
      omega)
  simpa only [List.dropLast_concat] using congrArg List.dropLast hUL

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
global left exit, UL changes exactly as for a local up: drop the old active
edge and append the fresh global edge. No singleton-stack premise is needed. -/
theorem primedCrossing_UL (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage w (walkNL w h (k + 1))).UL =
      (kmswStage w (walkNR w h (k + 1) - 1)).UL.dropLast ++
        [(kmswStage w (walkNL w h (k + 1) - 1)).nextEdge] := by
  let r := walkNR w h (k + 1)
  let t := walkNL w h (k + 1)
  have ht := walkNL_spec w h (k + 1)
  have hidx : t - 1 + 1 = t := by dsimp [t]; omega
  have hstep : kmswStage w t = kmswStepOfStep (kmswStage w (t - 1)) .left := by
    conv_lhs => rw [← hidx]
    change kmswStep (kmswStage w (t - 1)) (w (t - 1)) = _
    rw [show w (t - 1) = 0 from walkNL_previous_code w h (k + 1)]
    rfl
  obtain ⟨es, hes⟩ := kmswStage_UL_last w (r - 1)
  have hpred : (kmswStage w (t - 1)).UL.dropLast.reverse =
      (kmswStage w (r - 1)).active :: es.reverse := by
    rw [primedCrossing_exit_predecessor_eq, hes]
    simp
  change (kmswStage w t).UL = _
  rw [hstep]
  simp only [kmswStepOfStep, hpred, List.reverse_reverse]
  rw [hes, List.dropLast_concat]

private theorem LL_mem_mono (w : ℕ → Fin 3) {a b e : ℕ}
    (hab : a ≤ b) (he : e ∈ (kmswStage w a).LL) :
    e ∈ (kmswStage w b).LL := by
  induction b, hab using Nat.le_induction with
  | base => exact he
  | succ b hab ih =>
    change e ∈ (kmswStep (kmswStage w b) (w b)).LL
    unfold kmswStep
    cases hc : kmswCodeStep (w b) with
    | down =>
      cases hs : (kmswStage w b).UR <;>
        simpa [kmswStepOfStep, hs, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w b).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil =>
        simpa only [kmswStepOfStep, hs, State.addEdge, List.mem_cons] using
          (Or.inr ih)

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
and in LL across arbitrary later stages. Its stored unordered geometry is
unchanged; no orientation is asserted for this missing edge. -/
theorem primedCrossing_LL_persistent (w : ℕ → Fin 3) {a b e : ℕ}
    (hab : a ≤ b) (he : e ∈ (kmswStage w a).LL) :
    e ∈ (kmswStage w b).LL ∧ (kmswStage w b).present e = false ∧
      ({(kmswStage w b).west e, (kmswStage w b).east e} : Multiset ℕ) =
        {(kmswStage w a).west e, (kmswStage w a).east e} := by
  have hb := (kmswStage_boundary_ids_lt_nextEdge w a).2 e (by
    simp only [List.mem_append]
    exact Or.inl (Or.inr he))
  have he' := LL_mem_mono w hab he
  have hb' := hb.trans_le (kmswStage_nextEdge_mono w hab)
  have hp := ((kmswStage_status w b).1 e hb').mpr (Or.inr he')
  have hs := kmswStage_endpoints_stable w hab hb
  exact ⟨he', hp, by rw [hs.1, hs.2]⟩

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
edge remains outside the reachable present-edge set at every later stage,
even while that set grows. Reachability is in the fixed global limit quiver. -/
theorem primedCrossing_present_complement_persistent (w : ℕ → Fin 3)
    {a b e : ℕ} (hab : a ≤ b) (he : e < (kmswStage w a).nextEdge)
    (hp : (kmswStage w a).present e = true)
    (hn : e ∉ stageReachablePresentEdges w a) :
    (kmswStage w b).present e = true ∧ e ∉ stageReachablePresentEdges w b := by
  refine ⟨(present_mono w he hp b hab).2, ?_⟩
  intro hr
  have hs := kmswStage_endpoints_stable w hab he
  apply hn
  refine ⟨he, hp, ?_, ?_⟩
  · simpa only [hs.1] using hr.2.2.1
  · simpa only [hs.2] using hr.2.2.2

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
present local edge maps to the new global active edge, and the new missing
local side maps to the old global active side of the actual exit triangle. -/
@[expose] def primedCrossingEdgeMap (sh gl : State) (eφ : ℕ → ℕ) (e : ℕ) : ℕ :=
  if e = sh.nextEdge then gl.nextEdge
  else if e = sh.nextEdge + 1 then gl.active else eφ e

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
endpoint of the old global active edge; old local vertex images are retained. -/
@[expose] def primedCrossingVertexMap (sh gl : State) (vφ : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v = sh.nextVertex then gl.east gl.active else vφ v

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
allocated local IDs. -/
theorem primedCrossing_maps_extend (sh gl : State) (eφ vφ : ℕ → ℕ) :
    (∀ e, e < sh.nextEdge → primedCrossingEdgeMap sh gl eφ e = eφ e) ∧
    (∀ v, v < sh.nextVertex → primedCrossingVertexMap sh gl vφ v = vφ v) := by
  constructor
  · intro e he
    simp only [primedCrossingEdgeMap, ite_eq_right (by omega : e ≠ sh.nextEdge),
      ite_eq_right (by omega : e ≠ sh.nextEdge + 1)]
  · intro v hv
    simp only [primedCrossingVertexMap, ite_eq_right (by omega : v ≠ sh.nextVertex)]

private theorem local_boundary_bounds (u : ℕ → Fin 3) (m : ℕ) :
    (kmswMissingRootStage u m).active < (kmswMissingRootStage u m).nextEdge ∧
      ∀ e ∈ (kmswMissingRootStage u m).UL ++ (kmswMissingRootStage u m).UR ++
        (kmswMissingRootStage u m).LL ++ (kmswMissingRootStage u m).LR,
        e < (kmswMissingRootStage u m).nextEdge := by
  obtain ⟨_, he, _, _, _, _, ha, hul, hur, hll, hlr⟩ :=
    kmswMissingRootStage_agree u m
  simpa only [he, ha, hul, hur, hll, hlr] using
    kmswStage_boundary_ids_lt_nextEdge u m

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
LR root unchanged, with no within-interval strict bound. -/
theorem PrimedSimActiveRootLR.crossing_LR_root
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ) (hu : u m = 1) :
    (kmswMissingRootStage u (m + 1)).LR = [0] := by
  simpa only [kmswMissingRootStage, hu, kmswStep, kmswCodeStep,
    show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, kmswStepOfStep,
    State.addEdge] using sim.LR_root

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
restarts empty. The unmatched local and global tails remain unrestricted,
as in the existing invariant. -/
theorem primedCrossing_UR_restart (u w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k m : ℕ) (eφ vφ : ℕ → ℕ) :
    ∃ xs ys zs : List ℕ, xs = [] ∧
      (kmswMissingRootStage u m).UR = xs ++ ys ∧
      (kmswStage w (walkNL w h (k + 1))).UR = xs.map eφ ++ zs ∧
      (xs.length : ℤ) = R w (walkNL w h (k + 1)) -
        R w (walkNL w h (k + 1)) ∧
      ∀ e ∈ xs,
        (kmswStage w (walkNL w h (k + 1))).west (eφ e) =
          vφ ((kmswMissingRootStage u m).west e) ∧
        (kmswStage w (walkNL w h (k + 1))).east (eφ e) =
          vφ ((kmswMissingRootStage u m).east e) := by
  exact ⟨[], _, _, rfl, rfl, rfl, by simp, by simp⟩

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
alignment survive the replacement crossing, including a nonsingleton base
stack. This proves only these two invariant fields. -/
theorem PrimedSimActive.crossing_active_UL
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    eψ (kmswMissingRootStage u (m + 1)).active =
        (kmswStage w (walkNL w h (k + 1))).active ∧
      (kmswMissingRootStage u (m + 1)).UL.map eψ =
        (kmswStage w (walkNL w h (k + 1))).UL := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  let eψ := primedCrossingEdgeMap sh gl eφ
  change eψ (kmswMissingRootStage u (m + 1)).active = _ ∧
    (kmswMissingRootStage u (m + 1)).UL.map eψ = _
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    change kmswStep sh (u m) = _
    rw [hu]
    rfl
  have ht := walkNL_spec w h (k + 1)
  have hidx : walkNL w h (k + 1) - 1 + 1 = walkNL w h (k + 1) := by omega
  have hg : kmswStage w (walkNL w h (k + 1)) = kmswStepOfStep gl .left := by
    conv_lhs => rw [← hidx]
    change kmswStep gl (w (walkNL w h (k + 1) - 1)) = _
    rw [walkNL_previous_code w h (k + 1)]
    rfl
  have hmap : sh.UL.dropLast.map eψ = sh.UL.dropLast.map eφ := by
    apply List.map_congr_left
    intro e he
    apply (primedCrossing_maps_extend sh gl eφ vφ).1 e
    apply (local_boundary_bounds u m).2 e
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (List.mem_of_mem_dropLast he)))
  have hdrop : sh.UL.dropLast.map eφ =
      (kmswStage w (walkNR w h (k + 1) - 1)).UL.dropLast := by
    simpa only [List.map_dropLast] using congrArg List.dropLast sim.UL_alignment
  constructor
  · rw [hl, hg]
    cases hp : gl.UL.dropLast.reverse <;>
      simp [kmswStepOfStep, hp, eψ, primedCrossingEdgeMap]
  · rw [hl]
    change (sh.UL.dropLast ++ [sh.nextEdge]).map eψ = _
    rw [List.map_append, hmap, hdrop, primedCrossing_UL]
    simp only [List.map_cons, List.map_nil]
    simp only [eψ, primedCrossingEdgeMap, ↓reduceIte]
    rfl

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
missing root in global LL across the skipped excursion and the exit. This
also establishes its missing status without imposing an orientation. -/
theorem PrimedSimActive.crossing_missing_root
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    (kmswMissingRootStage u (m + 1)).present 0 = false ∧
      (kmswStage w (walkNL w h (k + 1))).present (eψ 0) = false ∧
      eψ 0 ∈ (kmswStage w (walkNL w h (k + 1))).LL := by
  have hzero : 0 < (kmswMissingRootStage u m).nextEdge := by
    have ha := (local_boundary_bounds u m).1
    omega
  have hext := (primedCrossing_maps_extend (kmswMissingRootStage u m)
    (kmswStage w (walkNL w h (k + 1) - 1)) eφ vφ).1 0 hzero
  dsimp only
  rw [hext]
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) := by omega
  have hh := primedCrossing_LL_persistent w hle sim.missing_root.2.2
  exact ⟨kmswMissingRootStage_present_zero u (m + 1), hh.2.1, hh.1⟩

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
survives the crossing. Old present edges stay outside the grown reachable
set, and the fresh present edge is the unreachable-west active exit edge. -/
theorem PrimedSimActive.crossing_present_complement
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    ∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = true →
      (kmswStage w (walkNL w h (k + 1))).present (eψ e) = true ∧
        eψ e ∉ stageReachablePresentEdges w (walkNL w h (k + 1)) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  let eψ := primedCrossingEdgeMap sh gl eφ
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    change kmswStep sh (u m) = _
    rw [hu]
    rfl
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) := by omega
  have hactive : (kmswStage w (walkNL w h (k + 1))).active = gl.nextEdge := by
    have hi : walkNL w h (k + 1) - 1 + 1 = walkNL w h (k + 1) := by omega
    conv_lhs => rw [← hi]
    change (kmswStep gl (w (walkNL w h (k + 1) - 1))).active = gl.nextEdge
    rw [walkNL_previous_code w h (k + 1)]
    change (kmswStepOfStep gl .left).active = gl.nextEdge
    cases hp : gl.UL.dropLast.reverse <;> simp only [kmswStepOfStep, hp]
  dsimp only
  intro e he hp
  rw [hl] at he hp
  change e < sh.nextEdge + 2 at he
  have hc : e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 := by omega
  rcases hc with hold | rfl | rfl
  · have hpold : sh.present e = true := by
      simpa only [kmswStepOfStep, State.addEdge,
        ite_eq_right (by omega : e ≠ sh.nextEdge),
        ite_eq_right (by omega : e ≠ sh.nextEdge + 1)] using hp
    have hh := sim.present_complement e hold hpold
    have hbound := sim.edge_bound e hold
    have hpres := primedCrossing_present_complement_persistent w hle hbound hh.1 hh.2
    rw [(primedCrossing_maps_extend sh gl eφ vφ).1 e hold]
    exact hpres
  · have hnew : primedCrossingEdgeMap sh gl eφ sh.nextEdge =
        (kmswStage w (walkNL w h (k + 1))).active := by
      simp only [primedCrossingEdgeMap, ↓reduceIte, hactive]
    rw [hnew]
    refine ⟨kmswStage_active_present w _, ?_⟩
    intro hr
    exact walkNL_activeWest_unreachable w h (k + 1) hr.2.2.1
  · simp [kmswStepOfStep, State.addEdge] at hp

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
the local time is the next block's base. The replacement up then satisfies
the new block's strict base bound and time alignment. -/
theorem PrimedSimActive.crossing_time
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    m = primedIntervalBase (primedSimInput w) h (k + 1) ∧
      primedIntervalBase (primedSimInput w) h (k + 1) < m + 1 ∧
      walkNL w h (k + 1) = primedIntervalLeft (primedSimInput w) h (k + 1) +
        (m + 1 - primedIntervalBase (primedSimInput w) h (k + 1)) - 1 := by
  have ha := sim.after_base
  have ht := sim.time_alignment
  change walkNR w h (k + 1) - 1 = walkNL w h k +
    (m - primedIntervalBase (primedSimInput w) h k) - 1 at ht
  have hgap := (walkNR_succ_spec w h k).1
  have hb := primedIntervalBase_succ (primedSimInput w) h k
  change primedIntervalBase (primedSimInput w) h (k + 1) =
    primedIntervalBase (primedSimInput w) h k +
      (walkNR w h (k + 1) - walkNL w h k) at hb
  change m = _ ∧ _ ∧ walkNL w h (k + 1) = walkNL w h (k + 1) + _ - 1
  omega

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
block base is up, while the corresponding global exit code is left. -/
theorem primedCrossing_codes (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    primedCode (primedSimInput w) h
        (primedIntervalBase (primedSimInput w) h (k + 1)) = 1 ∧
      w (walkNL w h (k + 1) - 1) = 0 := by
  refine ⟨?_, walkNL_previous_code w h (k + 1)⟩
  have hw := primedIntervalWidth_pos (primedSimInput w) h (k + 1)
  simpa only [Nat.add_zero, ↓reduceIte] using
    primedCode_block (primedSimInput w) h (k + 1) 0 (by omega)

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
existing invariant survive crossing and use the actual global exit triangle.
This field does not establish correspondence of cyclic dart orders or the
interior face permutations; those stronger geometric obligations remain. -/
theorem PrimedSimActive.crossing_triangles
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    ∀ a b c, (a, b, c) ∈ (kmswMissingRootStage u (m + 1)).triangles →
      ∃ x y z, (x, y, z) ∈ (kmswStage w (walkNL w h (k + 1))).triangles ∧
        ({eψ a, eψ b, eψ c} : Multiset ℕ) = {x, y, z} := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  let eψ := primedCrossingEdgeMap sh gl eφ
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    change kmswStep sh (u m) = _
    rw [hu]
    rfl
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) := by omega
  have htriangle := flowLine_leftExit_triangle w h (k + 2) (by omega)
  simp only [show k + 2 - 1 = k + 1 from by omega] at htriangle
  obtain ⟨es, hpred, heast, htri, hact, _⟩ := htriangle.2.2.2
  dsimp only
  intro a b c ht
  rw [hl] at ht
  simp only [kmswStepOfStep, List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | ht
  · obtain ⟨x, y, z, hxyz, hi⟩ := sim.triangle_incidence a b c ht
    obtain ⟨_, he, _, _, _, hlocalTri, _⟩ := kmswMissingRootStage_agree u m
    have ht' : (a, b, c) ∈ (kmswStage u m).triangles := hlocalTri ▸ ht
    have hb := triBound_stage u m (a, b, c) ht'
    have hext := (primedCrossing_maps_extend sh gl eφ vφ).1
    refine ⟨x, y, z, triangles_sub_stage w hle _ hxyz, ?_⟩
    change ({primedCrossingEdgeMap sh gl eφ a, primedCrossingEdgeMap sh gl eφ b,
      primedCrossingEdgeMap sh gl eφ c} : Multiset ℕ) = {x, y, z}
    simpa only [hext a (he.symm ▸ hb.1), hext b (he.symm ▸ hb.2.1),
      hext c (he.symm ▸ hb.2.2)] using hi
  · cases ht
    refine ⟨gl.active, gl.nextEdge, act w (walkNR w h (k + 1) - 1), ?_, ?_⟩
    · rw [htri, hact]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · have hext := (primedCrossing_maps_extend sh gl eφ vφ).1 sh.active
        (local_boundary_bounds u m).1
      change ({primedCrossingEdgeMap sh gl eφ sh.active,
        primedCrossingEdgeMap sh gl eφ sh.nextEdge,
        primedCrossingEdgeMap sh gl eφ (sh.nextEdge + 1)} : Multiset ℕ) = _
      rw [hext]
      have ha : eφ sh.active = act w (walkNR w h (k + 1) - 1) := sim.active_alignment
      simp only [primedCrossingEdgeMap, ↓reduceIte,
        show sh.nextEdge + 1 ≠ sh.nextEdge from by omega,
        ha]
      change ({act w (walkNR w h (k + 1) - 1), gl.nextEdge, gl.active} : Multiset ℕ) =
        {gl.active, gl.nextEdge, act w (walkNR w h (k + 1) - 1)}
      simp [Multiset.cons_swap]
      exact Multiset.cons_swap _ _ _

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
to the terminal edge of the new cut. This is the fresh-side boundary
obligation only; transport of all old boundary images remains separate. -/
theorem primedCrossing_new_missing_mem_cut (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) (sh : State) (eφ : ℕ → ℕ) :
    primedCrossingEdgeMap sh (kmswStage w (walkNL w h (k + 1) - 1)) eφ
        (sh.nextEdge + 1) ∈ cutAtExit w h (k + 1) := by
  simp only [primedCrossingEdgeMap,
    ite_eq_right (by omega : sh.nextEdge + 1 ≠ sh.nextEdge), ↓reduceIte]
  exact active_mem_cutAtExit w h (k + 1)

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
allocation obstruction: the crossing vertex map is injective on the new
allocated range precisely when the new vertex image avoids every old
vertex image. Neither direction assumes this geometric freshness fact. -/
theorem PrimedSimActive.crossing_vertex_injective_iff
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let vψ := primedCrossingVertexMap sh gl vφ
    (∀ v z, v < sh.nextVertex + 1 → z < sh.nextVertex + 1 →
      vψ v = vψ z → v = z) ↔
      ∀ v, v < sh.nextVertex → vφ v ≠ gl.east gl.active := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  let vψ := primedCrossingVertexMap sh gl vφ
  change (∀ v z, v < sh.nextVertex + 1 → z < sh.nextVertex + 1 →
    vψ v = vψ z → v = z) ↔
    ∀ v, v < sh.nextVertex → vφ v ≠ gl.east gl.active
  constructor
  · intro hinj v hv heq
    have hm : vψ v = vψ sh.nextVertex := by
      simp only [vψ, primedCrossingVertexMap,
        ite_eq_right (by omega : v ≠ sh.nextVertex), ↓reduceIte, heq]
    have hh := hinj v sh.nextVertex (by omega) (by omega) hm
    omega
  · intro havoid v z hv hz heq
    by_cases hvnew : v = sh.nextVertex
    · subst v
      by_cases hznew : z = sh.nextVertex
      · exact hznew.symm
      · have hzold : z < sh.nextVertex := by omega
        have he : gl.east gl.active = vφ z := by
          simpa only [vψ, primedCrossingVertexMap,
            ite_eq_right hznew, ↓reduceIte] using heq
        exact (havoid z hzold he.symm).elim
    · have hvold : v < sh.nextVertex := by omega
      by_cases hznew : z = sh.nextVertex
      · subst z
        have he : vφ v = gl.east gl.active := by
          simpa only [vψ, primedCrossingVertexMap,
            ite_eq_right hvnew, ↓reduceIte] using heq
        exact (havoid v hvold he).elim
      · have hzold : z < sh.nextVertex := by omega
        apply sim.vertex_injective v z hvold hzold
        simpa only [vψ, primedCrossingVertexMap,
          ite_eq_right hvnew, ite_eq_right hznew] using heq

private theorem crossing_global_transition (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    kmswStage w (walkNL w h (k + 1)) =
      kmswStepOfStep (kmswStage w (walkNL w h (k + 1) - 1)) .left := by
  have ht := walkNL_spec w h (k + 1)
  have hi : walkNL w h (k + 1) - 1 + 1 = walkNL w h (k + 1) := by omega
  conv_lhs => rw [← hi]
  change kmswStep _ (w (walkNL w h (k + 1) - 1)) = _
  rw [walkNL_previous_code w h (k + 1)]
  rfl

private theorem crossing_local_transition (u : ℕ → Fin 3) (m : ℕ)
    (hu : u m = 1) :
    kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) .up := by
  change kmswStep _ (u m) = _
  rw [hu]
  rfl

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
local IDs to allocated global IDs, without any freshness premise. The
positive-index global exit allocates an edge but no vertex. -/
theorem PrimedSimActive.crossing_bounds
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    let vψ := primedCrossingVertexMap sh gl vφ
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      eψ e < (kmswStage w (walkNL w h (k + 1))).nextEdge) ∧
    (∀ v, v < (kmswMissingRootStage u (m + 1)).nextVertex →
      vψ v < (kmswStage w (walkNL w h (k + 1))).nextVertex) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) - 1 := by omega
  have hemono := kmswStage_nextEdge_mono w hle
  have hvmono := CutConverse.nextVertex_mono w hle
  obtain ⟨es, hpred, _⟩ := (flowLine_leftExit_triangle w h (k + 2) (by omega)).2.2.2
  simp only [show k + 2 - 1 = k + 1 from by omega] at hpred
  have hact : gl.active < gl.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w _).1
  have hend := (kmswStage_endpoints_lt_nextVertex w _ gl.active hact).2
  dsimp only
  rw [crossing_local_transition u m hu, crossing_global_transition w h k]
  change (∀ e, e < (kmswStepOfStep sh .up).nextEdge →
      primedCrossingEdgeMap sh gl eφ e < (kmswStepOfStep gl .left).nextEdge) ∧
    (∀ v, v < (kmswStepOfStep sh .up).nextVertex →
      primedCrossingVertexMap sh gl vφ v < (kmswStepOfStep gl .left).nextVertex)
  change gl.UL.dropLast.reverse = _ at hpred
  simp only [kmswStepOfStep, hpred, State.addEdge]
  constructor
  · intro e he
    rcases (show e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 by omega)
      with he | rfl | rfl
    · rw [(primedCrossing_maps_extend sh gl eφ vφ).1 e he]
      exact (sim.edge_bound e he).trans_le (hemono.trans (Nat.le_succ _))
    · simp only [primedCrossingEdgeMap, ↓reduceIte]
      omega
    · simp only [primedCrossingEdgeMap,
        ite_eq_right (by omega : sh.nextEdge + 1 ≠ sh.nextEdge), ↓reduceIte]
      omega
  · intro v hv
    by_cases hnew : v = sh.nextVertex
    · subst v
      simpa only [primedCrossingVertexMap, ↓reduceIte] using hend
    · have hold : v < sh.nextVertex := by omega
      rw [(primedCrossing_maps_extend sh gl eφ vφ).2 v hold]
      exact (sim.vertex_bound v hold).trans_le hvmono

private theorem crossing_local_endpoints (u : ℕ → Fin 3) (m e : ℕ)
    (he : e < (kmswMissingRootStage u m).nextEdge) :
    (kmswMissingRootStage u m).west e < (kmswMissingRootStage u m).nextVertex ∧
      (kmswMissingRootStage u m).east e < (kmswMissingRootStage u m).nextVertex := by
  obtain ⟨hv, hE, hw, ht, _⟩ := kmswMissingRootStage_agree u m
  rw [hv, hw, ht]
  exact kmswStage_endpoints_lt_nextVertex u m e (hE ▸ he)

private theorem crossing_local_active_present
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    (kmswMissingRootStage u m).present (kmswMissingRootStage u m).active = true := by
  have hne : (kmswMissingRootStage u m).active ≠ 0 := by
    intro hz
    have ha := sim.active_alignment
    rw [hz] at ha
    have hp := kmswStage_active_present w n
    change (kmswStage w n).present (kmswStage w n).active = true at hp
    rw [← ha, sim.missing_root.2.1] at hp
    cases hp
  obtain ⟨_, _, _, _, hp, _, ha, _⟩ := kmswMissingRootStage_agree u m
  rw [hp _ hne, ha]
  exact kmswStage_active_present u m

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
of present arrows and unordered geometric incidence of missing edges. This
uses the actual exit triangle and does not assume either freshness goal. -/
theorem PrimedSimActive.crossing_incidence
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    let vψ := primedCrossingVertexMap sh gl vφ
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = true →
      (kmswStage w (walkNL w h (k + 1))).west (eψ e) =
        vψ ((kmswMissingRootStage u (m + 1)).west e) ∧
      (kmswStage w (walkNL w h (k + 1))).east (eψ e) =
        vψ ((kmswMissingRootStage u (m + 1)).east e)) ∧
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = false →
      ({(kmswStage w (walkNL w h (k + 1))).west (eψ e),
        (kmswStage w (walkNL w h (k + 1))).east (eψ e)} : Multiset ℕ) =
        {vψ ((kmswMissingRootStage u (m + 1)).west e),
          vψ ((kmswMissingRootStage u (m + 1)).east e)}) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  let ga := kmswStage w (walkNR w h (k + 1) - 1)
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) - 1 := by omega
  have hemono := kmswStage_nextEdge_mono w hle
  have ha : sh.active < sh.nextEdge := (local_boundary_bounds u m).1
  have hact := crossing_local_endpoints u m sh.active ha
  change sh.west sh.active < sh.nextVertex ∧ sh.east sh.active < sh.nextVertex at hact
  have hi := sim.present_incidence sh.active ha (crossing_local_active_present sim)
  rw [sim.active_alignment] at hi
  have hsact := kmswStage_endpoints_stable w hle
    (kmswStage_boundary_ids_lt_nextEdge w (walkNR w h (k + 1) - 1)).1
  have hwest : gl.west ga.active = vφ (sh.west sh.active) := hsact.1.trans hi.1
  have heast : gl.east ga.active = vφ (sh.east sh.active) := hsact.2.trans hi.2
  obtain ⟨es, hpred, hjoin, _⟩ :=
    (flowLine_leftExit_triangle w h (k + 2) (by omega)).2.2.2
  simp only [show k + 2 - 1 = k + 1 from by omega] at hpred hjoin
  change gl.UL.dropLast.reverse = ga.active :: es at hpred
  change gl.east ga.active = gl.west gl.active at hjoin
  have hgact : gl.active < gl.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w _).1
  dsimp only
  rw [crossing_local_transition u m hu, crossing_global_transition w h k]
  change (∀ e, e < (kmswStepOfStep sh .up).nextEdge →
      (kmswStepOfStep sh .up).present e = true →
      (kmswStepOfStep gl .left).west (primedCrossingEdgeMap sh gl eφ e) =
        primedCrossingVertexMap sh gl vφ ((kmswStepOfStep sh .up).west e) ∧
      (kmswStepOfStep gl .left).east (primedCrossingEdgeMap sh gl eφ e) =
        primedCrossingVertexMap sh gl vφ ((kmswStepOfStep sh .up).east e)) ∧
    (∀ e, e < (kmswStepOfStep sh .up).nextEdge →
      (kmswStepOfStep sh .up).present e = false →
      ({(kmswStepOfStep gl .left).west (primedCrossingEdgeMap sh gl eφ e),
        (kmswStepOfStep gl .left).east (primedCrossingEdgeMap sh gl eφ e)} : Multiset ℕ) =
        {primedCrossingVertexMap sh gl vφ ((kmswStepOfStep sh .up).west e),
          primedCrossingVertexMap sh gl vφ ((kmswStepOfStep sh .up).east e)})
  constructor
  · intro e he hp
    change e < sh.nextEdge + 2 at he
    rcases (show e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 by omega)
      with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := (sim.edge_bound e he).trans_le hemono
      have hv := crossing_local_endpoints u m e he
      change sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex at hv
      have hpold : sh.present e = true := by
        simpa only [kmswStepOfStep, State.addEdge,
          ite_eq_right (by omega : e ≠ sh.nextEdge),
          ite_eq_right (by omega : e ≠ sh.nextEdge + 1)] using hp
      have hh := sim.present_incidence e he hpold
      have hs := kmswStage_endpoints_stable w hle (sim.edge_bound e he)
      have hw : gl.west (eφ e) = vφ (sh.west e) := hs.1.trans hh.1
      have ht : gl.east (eφ e) = vφ (sh.east e) := hs.2.trans hh.2
      simpa only [kmswStepOfStep, hpred, State.addEdge, primedCrossingEdgeMap,
        primedCrossingVertexMap, ite_eq_right (by omega : e ≠ sh.nextEdge),
        ite_eq_right (by omega : e ≠ sh.nextEdge + 1),
        ite_eq_right (ne_of_lt hb), ite_eq_right (ne_of_lt hv.1),
        ite_eq_right (ne_of_lt hv.2)] using And.intro hw ht
    · simpa only [kmswStepOfStep, hpred, State.addEdge, primedCrossingEdgeMap,
        primedCrossingVertexMap, ↓reduceIte,
        ite_eq_right (by omega : sh.nextEdge ≠ sh.nextEdge + 1),
        ite_eq_right (ne_of_lt hact.1)] using And.intro hwest
          (rfl : gl.east gl.active = gl.east gl.active)
    · simp [kmswStepOfStep, State.addEdge] at hp
  · intro e he hp
    change e < sh.nextEdge + 2 at he
    rcases (show e < sh.nextEdge ∨ e = sh.nextEdge ∨ e = sh.nextEdge + 1 by omega)
      with he | rfl | rfl
    · have hb : eφ e < gl.nextEdge := (sim.edge_bound e he).trans_le hemono
      have hv := crossing_local_endpoints u m e he
      change sh.west e < sh.nextVertex ∧ sh.east e < sh.nextVertex at hv
      have hpold : sh.present e = false := by
        simpa only [kmswStepOfStep, State.addEdge,
          ite_eq_right (by omega : e ≠ sh.nextEdge),
          ite_eq_right (by omega : e ≠ sh.nextEdge + 1)] using hp
      have hh := sim.missing_incidence e he hpold
      have hs := kmswStage_endpoints_stable w hle (sim.edge_bound e he)
      have hh' : ({gl.west (eφ e), gl.east (eφ e)} : Multiset ℕ) =
          {vφ (sh.west e), vφ (sh.east e)} := by
        rw [hs.1, hs.2]
        exact hh
      simpa only [kmswStepOfStep, hpred, State.addEdge, primedCrossingEdgeMap,
        primedCrossingVertexMap, ite_eq_right (by omega : e ≠ sh.nextEdge),
        ite_eq_right (by omega : e ≠ sh.nextEdge + 1),
        ite_eq_right (ne_of_lt hb), ite_eq_right (ne_of_lt hv.1),
        ite_eq_right (ne_of_lt hv.2)] using hh'
    · simp [kmswStepOfStep, State.addEdge] at hp
    · have hj : gl.west gl.active = vφ (sh.east sh.active) := hjoin.symm.trans heast
      simp only [kmswStepOfStep, hpred, State.addEdge, primedCrossingEdgeMap,
        primedCrossingVertexMap,
        ite_eq_right (by omega : sh.nextEdge + 1 ≠ sh.nextEdge),
        ite_eq_right (ne_of_lt hgact), ↓reduceIte,
        ite_eq_right (ne_of_lt hact.2), hj]
      exact Multiset.pair_comm _ _

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
all old present-edge images and the missing root image. Separation from
other old missing-edge images is still a separate geometric obligation. -/
theorem PrimedSimActive.crossing_present_root_separation
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    (∀ e, e < sh.nextEdge → sh.present e = true → eφ e ≠ gl.active) ∧
      eφ 0 ≠ gl.active := by
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) - 1 := by omega
  have hf := flowLine_leftExit_triangle w h (k + 2) (by omega)
  simp only [show k + 2 - 1 = k + 1 from by omega] at hf
  have hreach : gl.active ∈ stageReachablePresentEdges w (walkNL w h (k + 1) - 1) :=
    ⟨(kmswStage_boundary_ids_lt_nextEdge w _).1,
      kmswStage_active_present w _, hf.1, hf.2.1⟩
  dsimp only
  constructor
  · intro e he hp heq
    have hc := sim.present_complement e he hp
    have hn := primedCrossing_present_complement_persistent w hle
      (sim.edge_bound e he) hc.1 hc.2
    apply hn.2
    rw [heq]
    exact hreach
  · intro heq
    have hm := (primedCrossing_LL_persistent w hle sim.missing_root.2.2).2.1
    have hp : gl.present gl.active = true := kmswStage_active_present w _
    change gl.present (eφ 0) = false at hm
    rw [heq] at hm
    rw [hp] at hm
    cases hm

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
of every present local arrow is unreachable from the global root. This
uses its outgoing present arrow to rule out the possibility that only the
terminal endpoint is unreachable. No claim is made about missing edges. -/
theorem PrimedSimActive.present_west_unreachable
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    ∀ e, e < (kmswMissingRootStage u m).nextEdge →
      (kmswMissingRootStage u m).present e = true →
      ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
        ⟨vφ ((kmswMissingRootStage u m).west e)⟩ := by
  intro e he hp hr
  have hb := sim.edge_bound e he
  have hc := sim.present_complement e he hp
  have hi := sim.present_incidence e he hp
  have hs := edge_endpoints_eq w hb
  rw [← hi.1] at hr
  obtain ⟨p⟩ := hr
  let a : (⟨(kmswStage w n).west (eφ e)⟩ : PresentVertex w) ⟶
      ⟨(kmswStage w n).east (eφ e)⟩ :=
    ⟨eφ e, ⟨n, hb, hc.1⟩, hs.1.symm, hs.2.symm⟩
  exact hc.2 ⟨hb, hc.1, ⟨p⟩, ⟨p.cons a⟩⟩

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
initial endpoint of an old present local arrow. The remaining vertex
obligation concerns vertices with no outgoing present local arrow. -/
theorem PrimedSimActive.crossing_present_west_separation
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    ∀ e, e < sh.nextEdge → sh.present e = true →
      vφ (sh.west e) ≠ gl.east gl.active := by
  have hf := flowLine_leftExit_triangle w h (k + 2) (by omega)
  simp only [show k + 2 - 1 = k + 1 from by omega] at hf
  dsimp only
  intro e he hp heq
  apply sim.present_west_unreachable e he hp
  rw [heq]
  exact hf.2.1

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
has a reachable image at the first interval entry. Thus universal
non-reachability of all local vertex images cannot be an entry invariant. -/
theorem primedFirstStep_vertex_two_reachable
    (u w : ℕ → Fin 3) (h : HasFlowLineHits w) (hu : u 0 = 1) :
    2 < (kmswMissingRootStage u 1).nextVertex ∧
      Quiver.Reachable (⟨0⟩ : PresentVertex w)
        ⟨primedFirstStepVertexMap w (walkNL w h 0) 2⟩ := by
  constructor
  · rw [crossing_local_transition u 0 hu]
    change 2 < 3
    omega
  · simpa only [primedFirstStepVertexMap, show (2 : ℕ) ≠ 0 from by decide,
      show (2 : ℕ) ≠ 1 from by decide, ↓reduceIte] using
        (flowLine_firstLeftExit_triangle w h).2.2.1

private theorem crossing_LL_outgoing (u : ℕ → Fin 3) (m : ℕ) :
    ∀ e ∈ (kmswStage u m).LL,
      ∃ f, f < (kmswStage u m).nextEdge ∧ f ≠ 0 ∧
        (kmswStage u m).present f = true ∧
        (kmswStage u m).west f = (kmswStage u m).west e := by
  induction m with
  | zero => simp only [kmswStage, kmswInit, List.not_mem_nil, false_implies,
      implies_true]
  | succ m ih =>
    intro e he
    let s := kmswStage u m
    have hold (he : e ∈ s.LL) :
        ∃ f, f < (kmswStage u (m + 1)).nextEdge ∧ f ≠ 0 ∧
          (kmswStage u (m + 1)).present f = true ∧
          (kmswStage u (m + 1)).west f = (kmswStage u (m + 1)).west e := by
      obtain ⟨f, hf, hf0, hp, hw⟩ := ih e he
      have hb := (kmswStage_boundary_ids_lt_nextEdge u m).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inr he))
      have hfp := present_mono u hf hp (m + 1) (Nat.le_succ m)
      have hfs := (kmswStage_endpoints_stable u (Nat.le_succ m) hf).1
      have hes := (kmswStage_endpoints_stable u (Nat.le_succ m) hb).1
      exact ⟨f, hfp.1, hf0, hfp.2, by rw [hfs, hes]; exact hw⟩
    change e ∈ (kmswStep s (u m)).LL at he
    cases hc : kmswCodeStep (u m) with
    | down =>
      cases hur : s.UR <;>
        simp only [kmswStep, hc, kmswStepOfStep, hur, State.addEdge] at he
      · exact hold he
      · exact hold he
    | up =>
      simp only [kmswStep, hc, kmswStepOfStep, State.addEdge] at he
      exact hold he
    | left =>
      cases hpred : s.UL.dropLast.reverse with
      | cons a as =>
        simp only [kmswStep, hc, kmswStepOfStep, hpred, State.addEdge] at he
        exact hold he
      | nil =>
        simp only [kmswStep, hc, kmswStepOfStep, hpred, State.addEdge,
          List.mem_cons] at he
        rcases he with rfl | he
        · have ha := (kmswStage_boundary_ids_lt_nextEdge u m).1
          change s.active < s.nextEdge at ha
          refine ⟨s.nextEdge, ?_, by omega, ?_, ?_⟩ <;>
            simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hpred,
              State.addEdge, s, ↓reduceIte,
              ite_eq_right (by omega : s.nextEdge ≠ s.nextEdge + 1)]
          omega
        · exact hold he

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
initial endpoint of a present local arrow, so its global image is unreachable.
The missing root remains on LR and is not included in this assertion. -/
theorem PrimedSimActive.LL_west_unreachable
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    ∀ e ∈ (kmswMissingRootStage u m).LL,
      ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
        ⟨vφ ((kmswMissingRootStage u m).west e)⟩ := by
  obtain ⟨_, hE, hw, _, hp, _, _, _, _, hLL, _⟩ := kmswMissingRootStage_agree u m
  intro e he
  obtain ⟨f, hf, hf0, hfp, hfw⟩ := crossing_LL_outgoing u m e (hLL ▸ he)
  have hfl : f < (kmswMissingRootStage u m).nextEdge := by rw [hE]; exact hf
  have hpl : (kmswMissingRootStage u m).present f = true := by rw [hp f hf0]; exact hfp
  have hwl : (kmswMissingRootStage u m).west f =
      (kmswMissingRootStage u m).west e := by rw [hw, hw]; exact hfw
  rw [← hwl]
  exact sim.present_west_unreachable f hfl hpl

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
reachable old global active edge of the exit triangle. This also covers
missing LL edges using unordered incidence, without orienting them. -/
theorem PrimedSimActive.crossing_LL_separation
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    ∀ e ∈ sh.LL, eφ e ≠ gl.active := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) - 1 := by omega
  have hr := flowLine_leftExit_triangle w h (k + 2) (by omega)
  simp only [show k + 2 - 1 = k + 1 from by omega] at hr
  dsimp only
  intro e he heq
  have hb : e < sh.nextEdge := (local_boundary_bounds u m).2 e (by
    simp only [List.mem_append]
    exact Or.inl (Or.inr he))
  have hpres : sh.present e = false := by
    by_cases he0 : e = 0
    · subst e; exact kmswMissingRootStage_present_zero u m
    · obtain ⟨_, hE, _, _, hp, _, _, _, _, hLL, _⟩ := kmswMissingRootStage_agree u m
      rw [hp e he0]
      exact ((kmswStage_status u m).1 e (hE ▸ hb)).mpr (Or.inr (hLL ▸ he))
  have hi := sim.missing_incidence e hb hpres
  have hs := kmswStage_endpoints_stable w hle (sim.edge_bound e hb)
  have hm : vφ (sh.west e) ∈
      ({gl.west gl.active, gl.east gl.active} : Multiset ℕ) := by
    rw [← heq, hs.1, hs.2, hi]
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    exact Or.inl rfl
  have heither : vφ (sh.west e) = gl.west gl.active ∨
      vφ (sh.west e) = gl.east gl.active := by
    simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hm
  apply sim.LL_west_unreachable e he
  rcases heither with hw | he
  · rw [hw]; exact hr.1
  · rw [he]; exact hr.2.1

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
exit's old active edge must map a missing local UR edge to a globally
missing UR edge at the last kept stage. Present images and both LL
boundaries cannot cause this collision. This isolates the activation
hazard during the skipped excursion, rather than assuming it away. -/
theorem PrimedSimActive.crossing_collision_pending
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let sh := kmswMissingRootStage u m
    let ga := kmswStage w (walkNR w h (k + 1) - 1)
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    ∀ e, e < sh.nextEdge → eφ e = gl.active →
      sh.present e = false ∧ e ≠ 0 ∧ e ∈ sh.UR ∧
        ga.present (eφ e) = false ∧ eφ e ∈ ga.UR := by
  let sh := kmswMissingRootStage u m
  let ga := kmswStage w (walkNR w h (k + 1) - 1)
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have ht := walkNL_spec w h (k + 1)
  have hr := walkNR_succ_spec w h k
  have hlt : walkNR w h (k + 1) - 1 < walkNL w h (k + 1) - 1 := by omega
  dsimp only
  intro e he heq
  have hsep := sim.crossing_present_root_separation
  have he0 : e ≠ 0 := by intro hz; subst e; exact hsep.2 heq
  have hp : sh.present e = false := by
    cases hp : sh.present e with
    | false => rfl
    | true => exact (hsep.1 e he hp heq).elim
  have hlocal : e ∈ sh.UR := by
    obtain ⟨_, hE, _, _, hp', _, _, _, hUR, hLL, _⟩ := kmswMissingRootStage_agree u m
    have hm := ((kmswStage_status u m).1 e (hE ▸ he)).mp
      ((hp' e he0).symm.trans hp)
    rcases hm with hur | hll
    · exact hUR.symm ▸ hur
    · exact (sim.crossing_LL_separation e (hLL.symm ▸ hll) heq).elim
  have hglobal : ga.present (eφ e) = false := by
    cases hgp : ga.present (eφ e) with
    | false => rfl
    | true =>
      obtain ⟨j, hj, haj⟩ := stagePresent_exists_active w _ _ (sim.edge_bound e he) hgp
      have hji : j = walkNL w h (k + 1) - 1 :=
        CutConverse.act_injective w (haj.symm.trans heq)
      omega
  have hm := ((kmswStage_status w (walkNR w h (k + 1) - 1)).1 _
    (sim.edge_bound e he)).mp hglobal
  have hur : eφ e ∈ ga.UR := by
    rcases hm with hur | hll
    · exact hur
    · have hpLL := (primedCrossing_LL_persistent w hlt.le hll).2.1
      rw [heq] at hpLL
      have hact := kmswStage_active_present w (walkNL w h (k + 1) - 1)
      change (kmswStage w (walkNL w h (k + 1) - 1)).present
        (kmswStage w (walkNL w h (k + 1) - 1)).active = true at hact
      rw [hact] at hpLL
      cases hpLL
  exact ⟨hp, he0, hlocal, hglobal, hur⟩

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
maps into the global frontier after crossing. UL uses exact stack alignment;
LR is the missing root retained in global LL. The old UR and LL portions
of the boundary-image field remain separate obligations. -/
theorem PrimedSimActiveRootLR.crossing_UL_LR_boundary_image
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    ∀ e, e ∈ (kmswMissingRootStage u (m + 1)).UL ++
        (kmswMissingRootStage u (m + 1)).LR →
      eψ e ∈ primedGlobalFrontier (kmswStage w (walkNL w h (k + 1))) := by
  dsimp only
  intro e he
  rcases List.mem_append.mp he with he | he
  · have hm : primedCrossingEdgeMap (kmswMissingRootStage u m)
        (kmswStage w (walkNL w h (k + 1) - 1)) eφ e ∈
        (kmswMissingRootStage u (m + 1)).UL.map
          (primedCrossingEdgeMap (kmswMissingRootStage u m)
            (kmswStage w (walkNL w h (k + 1) - 1)) eφ) :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    rw [sim.forget.crossing_active_UL hu |>.2] at hm
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inl hm
  · rw [sim.crossing_LR_root hu] at he
    have he0 := List.mem_singleton.mp he
    subst e
    have hm := sim.forget.crossing_missing_root |>.2.2
    simp only [primedGlobalFrontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inl hm))

private theorem crossing_LR_root_prefix (w : ℕ → Fin 3) (n : ℕ) :
    ∃ es, (kmswStage w n).LR = 0 :: es := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨es, hes⟩ := ih
    change ∃ es, (kmswStep (kmswStage w n) (w n)).LR = 0 :: es
    cases hc : kmswCodeStep (w n) with
    | down =>
      cases hur : (kmswStage w n).UR with
      | nil =>
        refine ⟨es ++ [(kmswStage w n).nextEdge], ?_⟩
        simp only [kmswStep, hc, kmswStepOfStep, hur, State.addEdge, hes,
          List.cons_append]
      | cons a as =>
        exact ⟨es, by simp only [kmswStep, hc, kmswStepOfStep, hur, hes]⟩
    | up => exact ⟨es, by simp only [kmswStep, hc, kmswStepOfStep, State.addEdge, hes]⟩
    | left =>
      cases hpred : (kmswStage w n).UL.dropLast.reverse <;>
        exact ⟨es, by simp only [kmswStep, hc, kmswStepOfStep, hpred, State.addEdge, hes]⟩

private theorem crossing_lower_chain_successor (s : State) (xs ys : List ℕ)
    (hc : List.IsChain (fun e f => s.east e = s.west f) (xs ++ 0 :: ys)) :
    ∀ e ∈ xs, s.east e = s.west 0 ∨ ∃ f ∈ xs, s.east e = s.west f := by
  induction xs with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons a as ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · cases as with
      | nil => exact Or.inl ((List.isChain_cons_cons.mp hc).1)
      | cons b bs =>
        exact Or.inr ⟨b, List.mem_cons_of_mem e (List.mem_cons_self),
          (List.isChain_cons_cons.mp hc).1⟩
    · rcases ih hc.tail e he with h | ⟨f, hf, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨f, List.mem_cons_of_mem a hf, h⟩

private theorem crossing_LL_endpoints_no_incoming (w : ℕ → Fin 3)
    (n f : ℕ) (hf : f ∈ (kmswStage w n).LL) (e : ℕ) (he : EdgePresent w e) :
    edgeEast w e ≠ (kmswStage w n).west f ∧
      edgeEast w e ≠ (kmswStage w n).east f := by
  refine ⟨uibot_LL_west_no_incoming w n f hf e he, ?_⟩
  obtain ⟨es, hes⟩ := crossing_LR_root_prefix w n
  have hc := (kmswStage_boundary_chain_invariant w n).2.1
  rw [hes] at hc
  rcases crossing_lower_chain_successor _ _ es hc f hf with h | ⟨g, hg, h⟩
  · have hb : 0 < (kmswStage w 0).nextEdge := by change 0 < 1; decide
    have hw := (kmswStage_endpoints_stable w (Nat.zero_le n) hb).1
    change (kmswStage w n).west 0 = 0 at hw
    rw [h, hw]
    exact uibot_zero_no_incoming w e he
  · rw [h]
    exact uibot_LL_west_no_incoming w n g hg e he

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
root avoid the terminal vertex of the old global active exit edge. Their
images are endpoints of a global LL edge, hence have no incoming present
arrow. This proves freshness even for a root endpoint with reachable image. -/
theorem PrimedSimActive.crossing_root_vertex_separation
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    ∀ v, v < 2 → vφ v ≠ gl.east gl.active := by
  let ga := kmswStage w (walkNR w h (k + 1) - 1)
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have hzero : 0 < (kmswMissingRootStage u m).nextEdge := by
    have ha := (local_boundary_bounds u m).1
    omega
  have hi := sim.missing_incidence 0 hzero sim.missing_root.1
  obtain ⟨_, _, hw, ht, _⟩ := kmswMissingRootStage_agree u m
  have hz : 0 < (kmswStage u 0).nextEdge := by change 0 < 1; decide
  have hs := kmswStage_endpoints_stable u (Nat.zero_le m) hz
  rw [hw, ht, hs.1, hs.2] at hi
  change ({ga.west (eφ 0), ga.east (eφ 0)} : Multiset ℕ) = {vφ 0, vφ 1} at hi
  have hb : gl.active < gl.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w _).1
  have hp : gl.present gl.active = true := kmswStage_active_present w _
  have hep : EdgePresent w gl.active := ⟨_, hb, hp⟩
  have hno := crossing_LL_endpoints_no_incoming w _ _ sim.missing_root.2.2 _ hep
  have hend : gl.east gl.active = edgeEast w gl.active := (edge_endpoints_eq w hb).2
  dsimp only
  intro v hv heq
  have hm : vφ v ∈ ({ga.west (eφ 0), ga.east (eφ 0)} : Multiset ℕ) := by
    rw [hi]
    have hv01 : v = 0 ∨ v = 1 := by omega
    rcases hv01 with rfl | rfl <;>
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
        true_or, or_true]
  have hcases : vφ v = ga.west (eφ 0) ∨ vφ v = ga.east (eφ 0) := by
    simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hm
  rcases hcases with hwest | heast
  · exact hno.1 (hend.symm.trans (heq.symm.trans hwest))
  · exact hno.2 (hend.symm.trans (heq.symm.trans heast))

private theorem crossing_LR_step_mem (s : State) (c : Fin 3) {e : ℕ}
    (he : e ∈ s.LR) : e ∈ (kmswStep s c).LR := by
  unfold kmswStep
  cases hc : kmswCodeStep c with
  | down =>
    cases hur : s.UR with
    | nil =>
      simp only [kmswStepOfStep, hur, State.addEdge, List.mem_append]
      exact Or.inl he
    | cons a as => simpa only [kmswStepOfStep, hur] using he
  | up => simpa only [kmswStepOfStep, State.addEdge] using he
  | left =>
    cases hpred : s.UL.dropLast.reverse <;>
      simpa only [kmswStepOfStep, hpred, State.addEdge] using he

private theorem crossing_vertex_west_or_LR (u : ℕ → Fin 3) (m : ℕ) :
    ∀ v, v < (kmswStage u m).nextVertex → v < 2 ∨
      (∃ f, f < (kmswStage u m).nextEdge ∧ f ≠ 0 ∧ (kmswStage u m).west f = v) ∨
      (∃ f ∈ (kmswStage u m).LR, (kmswStage u m).east f = v) := by
  induction m with
  | zero => intro v hv; exact Or.inl hv
  | succ m ih =>
    intro v hv
    let s := kmswStage u m
    by_cases hold : v < s.nextVertex
    · rcases ih v hold with hvroot | ⟨f, hf, hf0, hfw⟩ | ⟨f, hf, hfe⟩
      · exact Or.inl hvroot
      · exact Or.inr (Or.inl ⟨f,
          hf.trans_le (kmswStage_nextEdge_mono u (Nat.le_succ m)), hf0,
          ((kmswStage_endpoints_stable u (Nat.le_succ m) hf).1).trans hfw⟩)
      · have hb := (kmswStage_boundary_ids_lt_nextEdge u m).2 f (by
          simp only [List.mem_append]
          exact Or.inr hf)
        exact Or.inr (Or.inr ⟨f, crossing_LR_step_mem s (u m) hf,
          ((kmswStage_endpoints_stable u (Nat.le_succ m) hb).2).trans hfe⟩)
    · have ha := (kmswStage_boundary_ids_lt_nextEdge u m).1
      change s.active < s.nextEdge at ha
      change v < (kmswStep s (u m)).nextVertex at hv
      change v < 2 ∨ (∃ f, f < (kmswStep s (u m)).nextEdge ∧ f ≠ 0 ∧
        (kmswStep s (u m)).west f = v) ∨
        (∃ f ∈ (kmswStep s (u m)).LR, (kmswStep s (u m)).east f = v)
      cases hc : kmswCodeStep (u m) with
      | down =>
        cases hur : s.UR with
        | cons a as =>
          simp only [kmswStep, hc, kmswStepOfStep, hur] at hv
          exact (hold hv).elim
        | nil =>
          simp only [kmswStep, hc, kmswStepOfStep, hur, State.addEdge] at hv
          have hvnew : v = s.nextVertex := by omega
          subst v
          right; right
          refine ⟨s.nextEdge, ?_, ?_⟩ <;>
            simp only [kmswStep, hc, kmswStepOfStep, hur, State.addEdge,
              List.mem_append, List.mem_singleton, ↓reduceIte, or_true]
      | up =>
        simp only [kmswStep, hc, kmswStepOfStep, State.addEdge] at hv
        have hvnew : v = s.nextVertex := by omega
        subst v
        right; left
        refine ⟨s.nextEdge + 1, ?_, by omega, ?_⟩ <;>
          simp only [kmswStep, hc, kmswStepOfStep, State.addEdge, ↓reduceIte]
        omega
      | left =>
        cases hpred : s.UL.dropLast.reverse with
        | cons a as =>
          simp only [kmswStep, hc, kmswStepOfStep, hpred, State.addEdge] at hv
          exact (hold hv).elim
        | nil =>
          simp only [kmswStep, hc, kmswStepOfStep, hpred, State.addEdge] at hv
          have hvnew : v = s.nextVertex := by omega
          subst v
          right; left
          refine ⟨s.nextEdge, ?_, by omega, ?_⟩ <;>
            simp only [kmswStep, hc, kmswStepOfStep, hpred, State.addEdge,
              ite_eq_right (by omega : s.nextEdge ≠ s.nextEdge + 1), ↓reduceIte]
          omega

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
vertex image with the new crossing vertex occurs at the west endpoint of a
local UR edge. Root vertices and every vertex with an outgoing present
local arrow are excluded without a universal non-reachability assumption. -/
theorem PrimedSimActiveRootLR.crossing_vertex_collision_pending
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    ∀ v, v < sh.nextVertex → vφ v = gl.east gl.active →
      ∃ e ∈ sh.UR, sh.west e = v := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  obtain ⟨hV, hE, hw, ht, hp, _, _, _, hUR, hLL, hLR⟩ := kmswMissingRootStage_agree u m
  dsimp only
  intro v hv heq
  rcases crossing_vertex_west_or_LR u m v (hV ▸ hv) with hvroot | ⟨f, hf, hf0, hfw⟩ |
      ⟨f, hf, hfe⟩
  · exact (sim.forget.crossing_root_vertex_separation v hvroot heq).elim
  · have hfl : f < sh.nextEdge := by rw [hE]; exact hf
    have hwl : sh.west f = v := by rw [hw]; exact hfw
    cases hpf : sh.present f with
    | true =>
      have hs := sim.forget.crossing_present_west_separation f hfl hpf
      rw [hwl] at hs
      exact (hs heq).elim
    | false =>
      have hm := ((kmswStage_status u m).1 f hf).mp ((hp f hf0).symm.trans hpf)
      rcases hm with hur | hll
      · exact ⟨f, hUR.symm ▸ hur, hwl⟩
      · have hn := sim.forget.LL_west_unreachable f (hLL.symm ▸ hll)
        have hr := flowLine_leftExit_triangle w h (k + 2) (by omega)
        simp only [show k + 2 - 1 = k + 1 from by omega] at hr
        rw [hwl, heq] at hn
        exact (hn hr.2.1).elim
  · have hfl : f ∈ sh.LR := hLR.symm ▸ hf
    rw [sim.LR_root] at hfl
    have hf0 := List.mem_singleton.mp hfl
    subst f
    have hz : 0 < (kmswStage u 0).nextEdge := by change 0 < 1; decide
    have hs := (kmswStage_endpoints_stable u (Nat.zero_le m) hz).2
    change (kmswStage u m).east 0 = 1 at hs
    have hv1 : v = 1 := hfe.symm.trans hs
    exact (sim.forget.crossing_root_vertex_separation v (by omega) heq).elim

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
at the last kept stage becomes the old active edge of the next exit.
Its terminal vertex `1` was already allocated at the last kept stage.
Thus global missing status at the kept stage, or freshness relative to that
stage's vertex bound, cannot alone discharge crossing separation. This
finite computation does not refute separation for the simulation maps. -/
theorem primedCrossing_pending_activation_example :
    let w : ℕ → Fin 3 := fun n =>
      ([1, 0, 2, 0] : List (Fin 3)).getD n (if n % 3 = 0 then 2 else 0)
    L w 0 = 0 ∧ L w 1 = 0 ∧ L w 2 = -1 ∧
      R w 2 = 1 ∧ R w 3 = 0 ∧ L w 3 = 0 ∧ L w 4 = -1 ∧
      (kmswStage w 2).present 2 = false ∧
      2 < (kmswStage w 2).nextEdge ∧
      (kmswStage w 3).active = 2 ∧
      (kmswStage w 3).present 2 = true ∧
      (kmswStage w 3).east (kmswStage w 3).active = 1 ∧
      1 < (kmswStage w 2).nextVertex := by
  decide

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
equivalent to separation of old local UR images from the old global active
exit edge. All other old-edge cases and both fresh-edge comparisons are
proved here; the UR separation condition is not asserted or assumed. -/
theorem PrimedSimActive.crossing_edge_injective_iff
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    (∀ e f, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      f < (kmswMissingRootStage u (m + 1)).nextEdge → eψ e = eψ f → e = f) ↔
      ∀ e ∈ sh.UR, eφ e ≠ gl.active := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  let eψ := primedCrossingEdgeMap sh gl eφ
  have ht := walkNL_spec w h (k + 1)
  have hle : walkNR w h (k + 1) - 1 ≤ walkNL w h (k + 1) - 1 := by omega
  have hbound (e : ℕ) (he : e < sh.nextEdge) : eφ e < gl.nextEdge :=
    (sim.edge_bound e he).trans_le (kmswStage_nextEdge_mono w hle)
  have hact : gl.active < gl.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w _).1
  have hmap (e : ℕ) (he : e < sh.nextEdge) : eψ e = eφ e :=
    (primedCrossing_maps_extend sh gl eφ vφ).1 e he
  have hnew : eψ sh.nextEdge = gl.nextEdge := by
    simp only [eψ, primedCrossingEdgeMap, ↓reduceIte]
  have hside : eψ (sh.nextEdge + 1) = gl.active := by
    simp only [eψ, primedCrossingEdgeMap,
      ite_eq_right (by omega : sh.nextEdge + 1 ≠ sh.nextEdge), ↓reduceIte]
  change (∀ e f, e < (kmswMissingRootStage u (m + 1)).nextEdge →
    f < (kmswMissingRootStage u (m + 1)).nextEdge → eψ e = eψ f → e = f) ↔
    ∀ e ∈ sh.UR, eφ e ≠ gl.active
  rw [crossing_local_transition u m hu]
  change (∀ e f, e < sh.nextEdge + 2 → f < sh.nextEdge + 2 →
    eψ e = eψ f → e = f) ↔ ∀ e ∈ sh.UR, eφ e ≠ gl.active
  constructor
  · intro hinj e he heq
    have hb : e < sh.nextEdge := (local_boundary_bounds u m).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he)))
    have hm : eψ e = eψ (sh.nextEdge + 1) := by rw [hmap e hb, hside, heq]
    have hh := hinj e (sh.nextEdge + 1) (by omega) (by omega) hm
    omega
  · intro hUR
    have havoid (e : ℕ) (he : e < sh.nextEdge) : eφ e ≠ gl.active := by
      intro heq
      exact hUR e (sim.crossing_collision_pending e he heq).2.2.1 heq
    intro e f he hf hef
    have hclass (x : ℕ) (hx : x < sh.nextEdge + 2) :
        x < sh.nextEdge ∨ x = sh.nextEdge ∨ x = sh.nextEdge + 1 := by omega
    rcases hclass e he with heold | rfl | rfl <;>
      rcases hclass f hf with hfold | rfl | rfl
    · rw [hmap e heold, hmap f hfold] at hef
      exact sim.edge_injective e f heold hfold hef
    · rw [hmap e heold, hnew] at hef
      have hb := hbound e heold
      omega
    · rw [hmap e heold, hside] at hef
      exact (havoid e heold hef).elim
    · rw [hnew, hmap f hfold] at hef
      have hb := hbound f hfold
      omega
    · rfl
    · rw [hnew, hside] at hef
      omega
    · rw [hside, hmap f hfold] at hef
      exact (havoid f hfold hef.symm).elim
    · rw [hside, hnew] at hef
      omega
    · rfl

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
post-crossing allocated range is equivalent to freshness at old local UR
west endpoints. Root vertices, LL sources, and all other vertices are
excluded by the existing incidence and root-LR invariant. The remaining
UR freshness condition is not asserted or assumed. -/
theorem PrimedSimActiveRootLR.crossing_vertex_injective_iff_UR
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let vψ := primedCrossingVertexMap sh gl vφ
    (∀ v z, v < (kmswMissingRootStage u (m + 1)).nextVertex →
      z < (kmswMissingRootStage u (m + 1)).nextVertex → vψ v = vψ z → v = z) ↔
      ∀ e ∈ sh.UR, vφ (sh.west e) ≠ gl.east gl.active := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  let vψ := primedCrossingVertexMap sh gl vφ
  change (∀ v z, v < (kmswMissingRootStage u (m + 1)).nextVertex →
    z < (kmswMissingRootStage u (m + 1)).nextVertex → vψ v = vψ z → v = z) ↔
    ∀ e ∈ sh.UR, vφ (sh.west e) ≠ gl.east gl.active
  rw [crossing_local_transition u m hu]
  change (∀ v z, v < sh.nextVertex + 1 → z < sh.nextVertex + 1 →
    vψ v = vψ z → v = z) ↔ ∀ e ∈ sh.UR, vφ (sh.west e) ≠ gl.east gl.active
  have hh := sim.forget.crossing_vertex_injective_iff
  dsimp only at hh
  rw [hh]
  constructor
  · intro havoid e he
    have hb : e < sh.nextEdge := (local_boundary_bounds u m).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he)))
    exact havoid _ (crossing_local_endpoints u m e hb).1
  · intro hUR v hv heq
    obtain ⟨e, he, hw⟩ := sim.crossing_vertex_collision_pending v hv heq
    apply hUR e he
    rw [hw]
    exact heq















































































end DirectedDistances.KMSW
