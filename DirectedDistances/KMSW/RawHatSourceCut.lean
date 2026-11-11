module

public import DirectedDistances.KMSW.RawHatLinearOrder
public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.RightBoundaryRightmost
import DirectedDistances.KMSW.HatBoundaryFacts
import DirectedDistances.KMSW.LLBoundaryPersistent
import DirectedDistances.KMSW.StageInfiniteOutgoingOrderSource

/-! Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.

Exact target, with `hb : BoundaryHitWitnesses w`, `k : ℤ`,
`t := boundaryHitTime w hb k`, `u := fun i => w (t + i)`,
`h : HasFlowLineHits u`, and geometric finite-incidence witnesses `hfinS` for `u`
and `hfinRaw` for `w`:

let z := hatCodes u h
let hfinHat := hatCodes_inducedFiniteIncidence u h hfinS
let hatOutgoing := fun d : ℕ × Bool => d.2 = false ∧ EdgePresent z d.1
let rawOutgoing := fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1
let φ := fun e => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h e)
  (hatLimitEdgeMap u h e)
∀ e, EdgePresent z e → edgeWest z e = 0 →
  (RotationArc (kmswInfRot z hfinHat) hatOutgoing
    (kmswRightBoundaryEdge z 0, false) (e, false) ↔
   RotationArc (kmswInfRot w hfinRaw) rawOutgoing (act w t, false) (φ e, false))

The selected-time outgoing cut, rather than arbitrary-shift cyclic order, is required. -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
At the selected boundary hit, the canonical source boundary edge maps to the active edge. -/
theorem shiftHat_boundaryHit_source_rightBoundary (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (k : ℤ)
    (h : HasFlowLineHits (fun i => w (boundaryHitTime w hb k + i))) :
    let t := boundaryHitTime w hb k
    let u := fun i => w (t + i)
    let φ := fun e => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h e)
      (hatLimitEdgeMap u h e)
    φ (kmswRightBoundaryEdge (hatCodes u h) 0) = act w t := by
  exact (shiftHat_source_rightBoundary w (boundaryHitTime w hb k) h).1

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
Every hatted source outgoing dart is reached from its right boundary within outgoing darts. -/
theorem hat_source_outgoing_arc (u : ℕ → Fin 3) (h : HasFlowLineHits u)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage (hatCodes u h) n).nextEdge ∧
      ((kmswStage (hatCodes u h) n).west e = v ∨
        (kmswStage (hatCodes u h) n).east e = v)}.Finite)
    (e : ℕ) (hv : edgeWest (hatCodes u h) e = 0) :
    RotationArc (kmswInfRot (hatCodes u h) hfin)
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent (hatCodes u h) d.1)
      (kmswRightBoundaryEdge (hatCodes u h) 0, false) (e, false) := by
  let z := hatCodes u h
  have hL : ∀ n, 0 ≤ L z n := by
    intro n
    have hlen := kmswStage_LL_length z n
    rw [hat_LL_nil u h n] at hlen
    have hmin : minL z n = 0 := by simpa only [List.length_nil, Nat.cast_zero] using
      (neg_eq_zero.mp hlen.symm)
    have hh := runningMin_le (L z) n n le_rfl
    change minL z n ≤ L z n at hh
    omega
  have hR := hat_R_unbounded_hatted u h
  rw [kmswRightBoundaryEdge_zero]
  obtain ⟨n, hn⟩ := (kmswInfRot_exists_pow_iff_endpoint z hfin
    (0, false) (e, false)).mpr (by
      change edgeWest z 0 = edgeWest z e
      exact hv.symm)
  refine ⟨n, hn, fun i _ => ?_⟩
  have hbase := (kmswInfRot_exists_pow_iff_endpoint z hfin
    (0, false) ((kmswInfRot z hfin ^ i) (0, false))).mp ⟨i, rfl⟩
  have hzero : edgeWest z 0 = 0 := rfl
  have hend : (if ((kmswInfRot z hfin ^ i) (0, false)).2 then
      edgeEast z ((kmswInfRot z hfin ^ i) (0, false)).1 else
      edgeWest z ((kmswInfRot z hfin ^ i) (0, false)).1) = 0 := by
    simpa only [Bool.false_eq_true, ↓reduceIte, hzero] using hbase.symm
  have hout := (source_dart_iff_outgoing z hL hR _).mp hend
  exact ⟨hout.1, hout.2.1⟩

private def dartVal {k : ℕ} (d : StageDart k) : ℕ × Bool := (d.1.val, d.2)

private theorem dartVal_injective (k : ℕ) :
    Function.Injective (@dartVal k) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  obtain ⟨he, hb⟩ := Prod.mk.inj h
  cases Fin.ext he
  cases hb
  rfl

private theorem resize_val {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) (e : ℕ) (he : e < k) (he' : e < l) (b : Bool) :
    dartVal (StageRotation.resize h σ (⟨e, he'⟩, b)) =
      dartVal (σ (⟨e, he⟩, b)) := by
  cases h
  rfl

private theorem unresize_old {k l r : ℕ} (h : l = k + r) (hm : k ≤ l)
    (σ : Equiv.Perm (StageDart k)) (τ : Equiv.Perm (StageDart l))
    (ρ : Equiv.Perm (StageDart (k + r)))
    (ht : StageRotation.resize h τ = ρ) (x : StageDart k)
    (hx : ρ (StageRotation.allocation k r (.inl x)) =
      StageRotation.allocation k r (.inl (σ x))) :
    τ (outerSucc_castDart hm x) = outerSucc_castDart hm (σ x) := by
  apply dartVal_injective
  have hv := congrArg (fun p => dartVal (p (StageRotation.allocation k r (.inl x)))) ht
  rw [hx] at hv
  rw [StageRotation.allocation_old] at hv
  rw [resize_val h τ x.1.val (by have := x.1.isLt; omega)] at hv
  exact hv


private theorem active_present (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).present (act w n) = true := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  apply (kmswStage_status w n).2.1
  rw [hes]
  exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem missing_step (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hmiss : (kmswStage w n).present d.1.val = false)
    (hside : (stageRot w n d).2 = false) :
    stageRot w (n + 1) (outerSucc_castDart
      (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) =
    outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) (stageRot w n d) := by
  let s := kmswStage w n
  let σ := stageRot w n
  let hm := kmswStage_nextEdge_mono w (Nat.le_succ n)
  have ha := act_lt_nextEdge w (le_refl n)
  have hA : σ d ≠ (⟨s.active, ha⟩, true) := by
    intro heq
    have he := congrArg Prod.snd heq
    rw [hside] at he
    cases he
  have hne (e : ℕ) (he : e < s.nextEdge) (hp : s.present e = true) :
      d ≠ (⟨e, he⟩, false) := by
    intro heq
    have hid := congrArg (fun x => x.1.val) heq
    rw [hid, hp] at hmiss
    cases hmiss
  have hactive : d ≠ (⟨s.active, ha⟩, false) :=
    hne s.active ha (active_present w n)
  change StageRotation.step s ha (stageRotation_UL_bound w n) σ (w n)
    (outerSucc_castDart hm d) = outerSucc_castDart hm (σ d)
  cases hc : kmswCodeStep (w n) with
  | up =>
    apply unresize_old _ hm σ _ _ (StageRotation.step_up s ha _ σ _ hc) d
    rw [StageRotation.up_old, ite_eq_right hactive, ite_eq_right hA]
  | down =>
    cases hr : s.UR with
    | nil =>
      apply unresize_old _ hm σ _ _ (StageRotation.step_pendant s ha _ σ _ hc hr) d
      rw [StageRotation.pendant_old, ite_eq_right hA]
    | cons e es =>
      have hs : (kmswStep s (w n)).nextEdge = s.nextEdge := by
        simp [kmswStep, hc, kmswStepOfStep, hr]
      have ht := StageRotation.step_activation s ha (stageRotation_UL_bound w n)
        σ (w n) hc e es hr
      apply unresize_old (r := 0) (hs.trans (Nat.add_zero _).symm) hm σ _
        (StageRotation.resize (Nat.add_zero _).symm σ) (by
          simpa only [StageRotation.resize] using ht) d
      rfl
  | left =>
    cases hl : s.UL.dropLast.reverse with
    | nil =>
      apply unresize_old _ hm σ _ _ (StageRotation.step_leftFresh s ha _ σ _ hc hl) d
      rw [StageRotation.leftFresh_old, ite_eq_right hactive, ite_eq_right hA]
    | cons e es =>
      have hUL : e ∈ s.UL := List.dropLast_subset _
        (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self))
      have he := stageRotation_UL_bound w n e hUL
      have hde := hne e he ((kmswStage_status w n).2.1 e hUL)
      apply unresize_old _ hm σ _ _
        (StageRotation.step_leftExisting s ha _ σ _ hc e es hl) d
      rw [StageRotation.leftExisting_old, ite_eq_right hde, ite_eq_right hA]

private theorem missing_successor_stable (w : ℕ → Fin 3) (t e f : ℕ) (b : Bool)
    (he : e < (kmswStage w t).nextEdge) (hmiss : ¬ EdgePresent w e)
    (hrot : dartVal (stageRot w t (⟨e, he⟩, b)) = (f, false)) :
    ∀ n, t ≤ n → ∀ hn : e < (kmswStage w n).nextEdge,
      dartVal (stageRot w n (⟨e, hn⟩, b)) = (f, false) := by
  intro n htn
  induction n, htn using Nat.le_induction with
  | base => intro _; exact hrot
  | @succ n htn ih =>
    intro hn
    have hen : e < (kmswStage w n).nextEdge :=
      he.trans_le (kmswStage_nextEdge_mono w htn)
    have hp : (kmswStage w n).present e = false := by
      cases hh : (kmswStage w n).present e with
      | false => rfl
      | true => exact (hmiss ⟨n, hen, hh⟩).elim
    have hs : (stageRot w n (⟨e, hen⟩, b)).2 = false := congrArg Prod.snd (ih hen)
    have hstep := missing_step w n (⟨e, hen⟩, b) hp hs
    have hv := congrArg dartVal hstep
    exact hv.trans (ih hen)

private theorem missing_successor_limit (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (t e f : ℕ) (b : Bool) (he : e < (kmswStage w t).nextEdge)
    (hmiss : ¬ EdgePresent w e)
    (hrot : dartVal (stageRot w t (⟨e, he⟩, b)) = (f, false)) :
    kmswInfRot w hfin (e, b) = (f, false) := by
  obtain ⟨N, hN⟩ := kmswInfRot_eventually_eq_stage w hfin (e, b)
  obtain ⟨hn, hrotN⟩ := hN (max t N) (le_max_right _ _)
  exact hrotN.trans (missing_successor_stable w t e f b he hmiss hrot
    (max t N) (le_max_left _ _) hn)

private theorem terminal_coordinate_succ_ge_L (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  have hL : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    exact Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    omega
  rw [hL]
  omega

private theorem terminal_exists_coordinate_eq_of_le (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  classical
  let m := Nat.find (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hma : f m ≤ a := Nat.find_spec (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hn⟩ : ∃ j, f j ≤ a) hn
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hma
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : a < f p := by
      have hnot := Nat.find_min (⟨n, hn⟩ : ∃ j, f j ≤ a) (by omega : p < m)
      omega
    refine ⟨m, hmn, ?_⟩
    rw [hp] at hma ⊢
    have hnext := hstep p
    omega

private theorem terminal_first_hit_strict_record (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) (h : ∃ n, f n = a) :
    ∀ j < Nat.find h, a < f j := by
  intro j hj
  by_contra hnot
  have hjle : f j ≤ a := by omega
  obtain ⟨m, hmj, hma⟩ := terminal_exists_coordinate_eq_of_le
    f hstep hzero ha hjle
  have hmn : m < Nat.find h := hmj.trans_lt hj
  exact (Nat.find_min h hmn) hma

private theorem terminal_L_first_hit_strict_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k, L w (boundaryHitTime w h k) < L w j := by
  have htime : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  have hspec := Nat.find_spec (h.leftHit k hk)
  have hstrict := terminal_first_hit_strict_record (L w)
    (terminal_coordinate_succ_ge_L w) (by simp [L]) (by omega : k < 0)
    (h.leftHit k hk)
  intro j hj
  rw [htime] at hj
  rw [htime, hspec]
  exact hstrict j hj

private theorem left_record_step (w : ℕ → Fin 3) (n : ℕ)
    (hr : ∀ j < n + 1, L w (n + 1) < L w j) :
    w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = [] := by
  have hs : L w (n + 1) = L w n + ((w n : ℤ) - 1) := Finset.sum_range_succ _ _
  have hn := hr n (by omega)
  have hc : w n = 0 := by
    apply Fin.ext
    have hb := (w n).isLt
    omega
  have hmin : L w n = minL w n := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
    change minL w n = L w j at he
    have hl := hr j (by omega)
    have hb := runningMin_le (L w) n n le_rfl
    change minL w n ≤ L w n at hb
    rw [hc] at hs
    norm_num at hs
    omega
  refine ⟨hc, ?_⟩
  apply List.length_eq_zero_iff.mp
  simp only [List.length_reverse, List.length_dropLast]
  have hlen := kmswStage_UL_length w n
  omega


private theorem fresh_missing_rotation (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .left)
    (hl : (kmswStage w n).UL.dropLast.reverse = []) :
    ∃ he : kmswLLCreatedEdge w (n + 1) < (kmswStage w (n + 1)).nextEdge,
      dartVal (stageRot w (n + 1) (⟨kmswLLCreatedEdge w (n + 1), he⟩, false)) =
        (act w (n + 1), false) := by
  let s := kmswStage w n
  have hsize : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
    simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge, s]
  have hid : kmswLLCreatedEdge w (n + 1) = s.nextEdge + 1 := by
    simp [kmswLLCreatedEdge, hsize]
  have hact : act w (n + 1) = s.nextEdge := by
    simp [act, kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge, s]
  have hb : kmswLLCreatedEdge w (n + 1) < (kmswStage w (n + 1)).nextEdge := by
    rw [hid, hsize]
    omega
  refine ⟨hb, ?_⟩
  let σ := stageRot w n
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
  let A : StageDart s.nextEdge := (a.1, true)
  have hupdate := StageRotation.step_leftFresh s a.1.isLt (stageRotation_UL_bound w n)
    σ (w n) hc hl
  have hupdate' : StageRotation.resize hsize (stageRot w (n + 1)) =
      StageRotation.leftFresh s.nextEdge σ a A := by
    exact hupdate
  have htable := congrArg dartVal (StageRotation.leftFresh_new s.nextEdge σ a A).2.2.2
  rw [← hupdate'] at htable
  simp only [StageRotation.allocation_new] at htable
  rw [resize_val (he := by simpa [hid] using hb)] at htable
  simpa [dartVal, hid, hact] using htable

private theorem stageLR_head_zero (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.head? = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.head? = _
    cases kmswCodeStep (w n) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w n).LR ++ [(kmswStage w n).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w n)] using ih


private theorem source_outer_corner (w : ℕ → Fin 3) (n : ℕ)
    (hLL : (kmswStage w n).LL = []) :
    (stageRot w n (stageULHeadDart w n)).1.val = 0 ∧
      (stageRot w n (stageULHeadDart w n)).2 = false := by
  have hu : (kmswStage w n).UL[0]? = some (stageULHeadDart w n).1.val := by
    simpa only [← List.head?_eq_getElem?, stageULHeadDart] using
      List.head?_eq_some_head (kmswStage_UL_nonempty_active_last w n).1
  have hr : (kmswStage w n).LR[0]? = some 0 := by
    simpa only [← List.head?_eq_getElem?] using stageLR_head_zero w n
  have v1 := outerWordVal_getElem?_UL w n 0 _ hu
  have v2 := outerWordVal_getElem?_LR w n 0 _ hLL hr
  have hlen := outerWordVal_length w n hLL
  have hp := (List.getElem?_eq_some_iff.mp v2).1
  obtain ⟨d, d', hd, hd', hf⟩ :=
    outer_faceSucc_exists w n (stageOuterWord_faceSucc w n) _ hp
  have hmod : ((kmswStage w n).UL.length + (kmswStage w n).UR.length +
      ((kmswStage w n).LR.length - 1 - 0) + 1) % (stageOuterWordVal w n).length = 0 := by
    have hpos := (List.getElem?_eq_some_iff.mp hr).1
    have he : (kmswStage w n).UL.length + (kmswStage w n).UR.length +
        ((kmswStage w n).LR.length - 1 - 0) + 1 = (stageOuterWordVal w n).length := by
      omega
    rw [he, Nat.mod_self]
  rw [hmod, v1] at hd'
  rw [v2] at hd
  have hv := Option.some.inj hd
  have hv' := Option.some.inj hd'
  have he : d' = stageULHeadDart w n :=
    Prod.ext (Fin.ext (congrArg Prod.fst hv').symm) (congrArg Prod.snd hv').symm
  rw [he] at hf
  change (stageRot w n).symm (edgeFlip _ d) = stageULHeadDart w n at hf
  have hrot := (stageRot w n).symm_apply_eq.mp hf
  rw [← hrot]
  exact ⟨(congrArg Prod.fst hv).symm, by
    change Bool.not d.2 = false
    rw [← congrArg Prod.snd hv]
    rfl⟩


private theorem fresh_missing_east_rotation (w : ℕ → Fin 3) (n : ℕ)
    (hc : kmswCodeStep (w n) = .left)
    (hl : (kmswStage w n).UL.dropLast.reverse = [])
    (houter : dartVal (stageRot w n
      (⟨act w n, act_lt_nextEdge w (le_refl n)⟩, false)) = (0, false)) :
    ∃ he : kmswLLCreatedEdge w (n + 1) < (kmswStage w (n + 1)).nextEdge,
      dartVal (stageRot w (n + 1) (⟨kmswLLCreatedEdge w (n + 1), he⟩, true)) =
        (0, false) := by
  let s := kmswStage w n
  have hsize : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
    simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge, s]
  have hid : kmswLLCreatedEdge w (n + 1) = s.nextEdge + 1 := by
    simp [kmswLLCreatedEdge, hsize]
  have hb : kmswLLCreatedEdge w (n + 1) < (kmswStage w (n + 1)).nextEdge := by
    rw [hid, hsize]
    omega
  refine ⟨hb, ?_⟩
  let σ := stageRot w n
  let a : StageDart s.nextEdge := (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
  let A : StageDart s.nextEdge := (a.1, true)
  have hA : σ a ≠ A := by
    intro heq
    have hh := congrArg Prod.snd heq
    have ho : (σ a).2 = false := congrArg Prod.snd houter
    change (σ a).2 = true at hh
    rw [ho] at hh
    cases hh
  have hupdate := StageRotation.step_leftFresh s a.1.isLt (stageRotation_UL_bound w n)
    σ (w n) hc hl
  have hupdate' : StageRotation.resize hsize (stageRot w (n + 1)) =
      StageRotation.leftFresh s.nextEdge σ a A := by
    exact hupdate
  have htable := congrArg dartVal (StageRotation.leftFresh_new s.nextEdge σ a A).1
  rw [ite_eq_right hA, ← hupdate'] at htable
  simp only [StageRotation.allocation_new] at htable
  rw [resize_val (he := by simpa [hid] using hb)] at htable
  have hnew : dartVal (stageRot w (n + 1)
      (⟨kmswLLCreatedEdge w (n + 1), hb⟩, true)) = dartVal (σ a) := by
    simpa [dartVal, hid, StageRotation.allocation] using htable
  exact hnew.trans houter

private theorem root_missing_predecessor (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    (kmswInfRot w hfin).symm (0, false) =
      (kmswLLCreatedEdge w (boundaryHitTime w hb (-1)), true) := by
  have hval := boundaryHitTime_left_spec w hb (by omega : (-1 : ℤ) ≤ -1)
  cases ht : boundaryHitTime w hb (-1) with
  | zero => rw [ht] at hval; simp only [L, Finset.sum_range_zero] at hval; omega
  | succ n =>
    have hr := terminal_L_first_hit_strict_record w hb (by omega : (-1 : ℤ) ≤ -1)
    rw [ht] at hr
    obtain ⟨hc, hl⟩ := left_record_step w n hr
    have hc' : kmswCodeStep (w n) = .left := by rw [hc]; rfl
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    have hesnil : es = [] := by
      simpa only [hes, List.dropLast_concat, List.reverse_eq_nil_iff] using hl
    have hUL : (kmswStage w n).UL = [act w n] := by
      simpa only [hesnil, List.nil_append, act] using hes
    have hmin : minL w n = 0 := by
      obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
      have hstrict := hr j (by omega)
      rw [ht] at hval
      have hbound := runningMin_le (L w) n 0 (Nat.zero_le n)
      change minL w n ≤ 0 at hbound
      change minL w n = L w j at he
      omega
    have hLL : (kmswStage w n).LL = [] := by
      apply List.length_eq_zero_iff.mp
      have hh := kmswStage_LL_length w n
      omega
    have hout := source_outer_corner w n hLL
    have hhead : stageULHeadDart w n =
        (⟨act w n, act_lt_nextEdge w (le_refl n)⟩, false) := by
      apply Prod.ext
      · apply Fin.ext
        simp [stageULHeadDart, hUL]
      · rfl
    rw [hhead] at hout
    obtain ⟨he, hrot⟩ := fresh_missing_east_rotation w n hc' hl (Prod.ext hout.1 hout.2)
    have hmiss := boundary_left_edge_not_present w hb (by omega : (-1 : ℤ) ≤ -1)
    rw [ht] at hmiss
    have hsucc := missing_successor_limit w hfin (n + 1) _ 0 true he hmiss hrot
    apply (kmswInfRot w hfin).injective
    rw [Equiv.apply_symm_apply, hsucc]

private theorem boundary_vertex_hit (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (k : ℤ) :
    boundaryVertex w hb k = activeInitial w (boundaryHitTime w hb k) := by
  by_cases hk : k = 0
  · subst k
    rw [boundaryVertex_zero, boundaryHitTime_zero]
    rfl
  · by_cases hp : 1 ≤ k
    · exact boundaryVertex_right_hit_eq w hb hp
    · exact boundaryVertex_left_hit_eq w hb (by omega)

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
Every present outgoing edge at the selected vertex activates after the selected hit. -/
theorem boundaryHit_outgoing_activation_ge (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (k : ℤ) (e : ℕ)
    (he : EdgePresent w e) (hv : edgeWest w e = boundaryVertex w hb k) :
    boundaryHitTime w hb k ≤ actTime w e he := by
  by_cases hk : k = 0
  · subst k
    rw [boundaryHitTime_zero]
    exact Nat.zero_le _
  · by_contra hle
    have ht : actTime w e he < boundaryHitTime w hb k := by omega
    have hv' : boundaryVertex w hb k = activeInitial w (actTime w e he) :=
      hv.symm.trans (congrArg (edgeWest w) (actTime_spec w e he))
    by_cases hp : 1 ≤ k
    · exact boundaryVertex_first_visit_right w hb hp _ ht hv'
    · exact boundaryVertex_first_visit_left w hb (by omega) _ ht hv'

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
At the selected finite stage the active edge is the sole present outgoing edge at its source. -/
theorem boundaryHit_stage_outgoing_unique (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (k : ℤ) (e : ℕ)
    (he : e < (kmswStage w (boundaryHitTime w hb k)).nextEdge)
    (hp : (kmswStage w (boundaryHitTime w hb k)).present e = true)
    (hv : (kmswStage w (boundaryHitTime w hb k)).west e = boundaryVertex w hb k) :
    e = act w (boundaryHitTime w hb k) := by
  obtain ⟨j, hj, hej⟩ := stagePresent_exists_active w _ e he hp
  have hep : EdgePresent w e := ⟨_, he, hp⟩
  have hev : edgeWest w e = boundaryVertex w hb k :=
    (edge_endpoints_eq w he).1.symm.trans hv
  have hlow := boundaryHit_outgoing_activation_ge w hb k e hep hev
  have hj' : actTime w e hep = j := (actTime_eq_iff w e hep j).mpr hej
  have heq : j = boundaryHitTime w hb k := by omega
  exact hej.trans (congrArg (act w) heq)

private theorem arc_start_of_unmarked_predecessor {D : Type*}
    (σ : Equiv.Perm D) (p : D → Prop) (r d : D)
    (hr : p r) (_hd : p d) (hprev : ¬p (σ.symm r))
    (hc : RotationArc σ p r d ∨ RotationArc σ p d r) : RotationArc σ p r d := by
  rcases hc with h | ⟨n, hn, hp⟩
  · exact h
  · cases n with
    | zero =>
      have heq : d = r := hn
      rw [heq]
      exact RotationArc.refl σ p r hr
    | succ n =>
      have hpred : (σ ^ n) d = σ.symm r := by
        apply σ.injective
        rw [Equiv.apply_symm_apply]
        simpa only [pow_succ', Equiv.Perm.mul_apply] using hn
      exact (hprev (hpred ▸ hp n (by omega))).elim

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
For positive boundary indices the raw outgoing interval starts at the selected active edge. -/
theorem boundaryHit_positive_outgoing_arc (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (k : ℕ) (hk : 1 ≤ k) (e : ℕ) (he : EdgePresent w e)
    (hv : edgeWest w e = boundaryVertex w hb (k : ℤ)) :
    RotationArc (kmswInfRot w hfin)
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
      (act w (boundaryHitTime w hb (k : ℤ)), false) (e, false) := by
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hb.rightHit (max 1 (-a)) (le_max_left _ _)
    exact ⟨n, by have := le_max_right (1 : ℤ) (-a); omega⟩
  rw [boundaryHitTime_right_edge_eq_rightBoundaryEdge w hb hk]
  have hr := boundaryVertex_right_edge_present_source w hb hk
  have hface := kmswInfFaceSucc_right_of_unbounded_below w hfin hR (k - 1)
  have hpred : (kmswInfRot w hfin).symm (kmswRightBoundaryEdge w k, false) =
      (kmswRightBoundaryEdge w (k - 1), true) := by
    simpa [kmswInfFaceSucc, Nat.sub_add_cancel hk] using hface
  apply arc_start_of_unmarked_predecessor _ _ _ _ ⟨rfl, hr.1⟩ ⟨rfl, he⟩
  · rw [hpred]
    simp only [Bool.true_eq_false, false_and, not_false_eq_true]
  · exact kmswInfRot_outgoing_interval_all w hfin _ e (hr.2.1.trans hv.symm) hr.1 he

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
At a negative hit, the missing outgoing boundary dart precedes the selected active dart. -/
theorem boundaryHit_negative_source_predecessor (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (k : ℤ) (hk : k ≤ -1) :
    (kmswInfRot w hfin).symm (act w (boundaryHitTime w hb k), false) =
      (kmswLLCreatedEdge w (boundaryHitTime w hb k), false) := by
  have hval := boundaryHitTime_left_spec w hb hk
  cases ht : boundaryHitTime w hb k with
  | zero => rw [ht] at hval; simp only [L, Finset.sum_range_zero] at hval; omega
  | succ n =>
    have hr := terminal_L_first_hit_strict_record w hb hk
    rw [ht] at hr
    obtain ⟨hc, hl⟩ := left_record_step w n hr
    have hc' : kmswCodeStep (w n) = .left := by rw [hc]; rfl
    obtain ⟨he, hrot⟩ := fresh_missing_rotation w n hc' hl
    have hmiss := boundary_left_edge_not_present w hb hk
    rw [ht] at hmiss
    have hsucc := missing_successor_limit w hfin (n + 1) _ _ false he hmiss hrot
    apply (kmswInfRot w hfin).injective
    rw [Equiv.apply_symm_apply, hsucc]

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
At every selected boundary hit the raw outgoing interval starts at the active edge. -/
theorem boundaryHit_outgoing_arc (w : ℕ → Fin 3) (hb : BoundaryHitWitnesses w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (k : ℤ) (e : ℕ) (he : EdgePresent w e)
    (hv : edgeWest w e = boundaryVertex w hb k) :
    RotationArc (kmswInfRot w hfin)
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
      (act w (boundaryHitTime w hb k), false) (e, false) := by
  by_cases hk : 1 ≤ k
  · have hkN : 1 ≤ k.toNat := by omega
    have hcast : (k.toNat : ℤ) = k := by omega
    have hvN : edgeWest w e = boundaryVertex w hb (k.toNat : ℤ) := by
      rw [hcast]
      exact hv
    simpa only [hcast] using boundaryHit_positive_outgoing_arc w hb hfin
      k.toNat hkN e he hvN
  · let t := boundaryHitTime w hb k
    have ha : EdgePresent w (act w t) :=
      ⟨t, act_lt_nextEdge w (le_refl t), active_present w t⟩
    have hw : edgeWest w (act w t) = edgeWest w e :=
      (boundary_vertex_hit w hb k).symm.trans hv.symm
    apply arc_start_of_unmarked_predecessor _ _ _ _ ⟨rfl, ha⟩ ⟨rfl, he⟩
    · by_cases hk0 : k = 0
      · subst k
        rw [boundaryHitTime_zero]
        change ¬ (((kmswInfRot w hfin).symm (0, false)).2 = false ∧ _)
        rw [root_missing_predecessor w hb hfin]
        simp only [Bool.true_eq_false, false_and, not_false_eq_true]
      · have hneg : k ≤ -1 := by omega
        change ¬ (((kmswInfRot w hfin).symm (act w (boundaryHitTime w hb k), false)).2 =
          false ∧ EdgePresent w
            ((kmswInfRot w hfin).symm (act w (boundaryHitTime w hb k), false)).1)
        rw [boundaryHit_negative_source_predecessor w hb hfin k hneg]
        exact fun hh => boundary_left_edge_not_present w hb hneg hh.2
    · exact kmswInfRot_outgoing_interval_all w hfin _ e hw ha he

/-- Helper toward Lemma 5.4 (lem-geo-infty); not a paper result.
The hatted source cut agrees with the raw cut at the selected boundary hit time.
This is a rotation-arc statement; the planar region transfer is a separate obligation. -/
theorem shiftHat_boundaryHit_sourceCut_iff (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (k : ℤ)
    (h : HasFlowLineHits (fun i => w (boundaryHitTime w hb k + i)))
    (hfinS : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => w (boundaryHitTime w hb k + i)) n).nextEdge ∧
      ((kmswStage (fun i => w (boundaryHitTime w hb k + i)) n).west e = v ∨
        (kmswStage (fun i => w (boundaryHitTime w hb k + i)) n).east e = v)}.Finite)
    (hfinRaw : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (e : ℕ) (he : EdgePresent (hatCodes (fun i => w (boundaryHitTime w hb k + i)) h) e)
    (hv : edgeWest (hatCodes (fun i => w (boundaryHitTime w hb k + i)) h) e = 0) :
    let t := boundaryHitTime w hb k
    let u := fun i => w (t + i)
    let z := hatCodes u h
    let φ := fun f => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h f)
      (hatLimitEdgeMap u h f)
    RotationArc (kmswInfRot z (hatCodes_inducedFiniteIncidence u h hfinS))
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent z d.1)
      (kmswRightBoundaryEdge z 0, false) (e, false) ↔
    RotationArc (kmswInfRot w hfinRaw)
      (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
      (act w t, false) (φ e, false) := by
  let t := boundaryHitTime w hb k
  let u := fun i => w (t + i)
  let z := hatCodes u h
  let φ := fun f => kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h f)
    (hatLimitEdgeMap u h f)
  let V := fun a => limitVertexMap (kmswShiftVertexMapAll w t) u
    (hatLimitVertexMap u h a)
  have hE := shiftHat_edge_incidence w t h e
  have hsource := shiftHat_source_rightBoundary w t h
  have hep : EdgePresent w (φ e) := hE.2.2 he
  have hew : edgeWest w (φ e) = boundaryVertex w hb k := by
    calc
      edgeWest w (φ e) = V (edgeWest z e) := hE.1
      _ = V 0 := congrArg V hv
      _ = activeInitial w t := hsource.2
      _ = boundaryVertex w hb k := (boundary_vertex_hit w hb k).symm
  exact ⟨fun _ => boundaryHit_outgoing_arc w hb hfinRaw k (φ e) hep hew,
    fun _ => hat_source_outgoing_arc u h (hatCodes_inducedFiniteIncidence u h hfinS) e hv⟩

end DirectedDistances.KMSW
