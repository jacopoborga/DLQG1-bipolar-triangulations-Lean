module

public import DirectedDistances.RandomWalk.ExcursionWords
public import DirectedDistances.RandomWalk.CappedLevelChunks

/-! # Windows around first-hit levels

This file relates a walk window centered at a first hit of a level to the
code-level UIBHBOT excursion window (`lem-disk-walk-conv`,
not additional paper claims. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory

/-- The code walk window centered at the first hit of level `-M`, with a zero
default when the finite hit time is less than `N` -/
@[expose] noncomputable def centeredWindowAtFirstHit (N M : ℕ)
    (ω : ℕ → Fin 3) : Fin (2 * N + 1) → ℤ × ℤ := by
  let σ := (codeFstFirstHit (-(M : ℤ)) ω).toNat
  exact if h : N ≤ σ then
    fun j => codeWalk ω (σ + j.val - N) - codeWalk ω σ
  else fun _ => (0, 0)

private theorem codeFstFirstHit_zero (ω : ℕ → Fin 3) :
    codeFstFirstHit 0 ω = 0 := by
  classical
  unfold codeFstFirstHit
  let h : ∃ n, (codeWalk ω n).1 = 0 := ⟨0, by simp [codeWalk_zero]⟩
  rw [dif_pos h]
  have hf : Nat.find h = 0 := by
    apply (Nat.find_eq_iff h).2
    constructor
    · simp [codeWalk_zero]
    · intro n hn
      omega
  simp [hf]

private theorem codeShift_comp (a b : ℕ) (ω : ℕ → Fin 3) :
    codeShift a (codeShift b ω) = codeShift (b + a) ω := by
  funext i
  by_cases hi : i = 0
  · simp [codeShift, hi]
  · simp [codeShift, hi, Nat.add_assoc]

/-- Almost surely, the `k`th iterated excursion code starts at the first hit
of level `-k` (`lem-disk-walk-conv`, -/
theorem ae_iteratedExcursionCode_eq_firstHit (k : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      iteratedExcursionCode k ω =
        codeShift (codeFstFirstHit (-(k : ℤ)) ω).toNat ω := by
  induction k with
  | zero =>
      have hstart : ∀ᵐ ω ∂iidCodeMeasure, ω 0 = 0 := by
        filter_upwards [DirectedDistances.Probability.markovTrajectory_ae_start
          (Kernel.const (Fin 3) uniformCodeMeasure) (0 : Fin 3)] with ω hω
        exact hω
      filter_upwards [hstart] with ω hω
      have hhit0 := codeFstFirstHit_zero ω
      have hshift : ω = codeShift 0 ω := by
        funext i
        by_cases hi : i = 0
        · simp [codeShift, hi, hω]
        · simp [codeShift, hi]
      simpa [iteratedExcursionCode, hhit0] using hshift
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        filter_upwards with ω
        simp [iteratedExcursionCode, excursionLength]
      · have hcodeIH := ih
        have hadd := ae_codeFstFirstHit_add k 1 (by omega)
        have hfin := ae_codeFstFirstHit_lt_top_int (-((k : ℕ) : ℤ))
        have hfinNext := ae_codeFstFirstHit_lt_top_int (-((k + 1 : ℕ) : ℤ))
        filter_upwards [hcodeIH, hadd, hfin, hfinNext] with ω hih haddω hcur hnext
        have hcur' : codeFstFirstHit (-(k : ℤ)) ω < ⊤ := by simpa using hcur
        cases hc : codeFstFirstHit (-(k : ℤ)) ω with
        | top => simp [hc] at hcur'
        | coe s =>
          have hnext' : codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω < ⊤ := by
            simpa using hnext
          have hadd' : codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω =
              (s : ℕ∞) + codeFstFirstHit (-1)
                (codeShift s ω) := by
            simpa [hc] using haddω
          cases ht : codeFstFirstHit (-1) (codeShift s ω) with
          | top =>
              rw [ht] at hadd'
              simp at hadd'
              simp [hadd'] at hnext'
          | coe t =>
              have hsum : codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω = ((s + t : ℕ) : ℕ∞) := by
                rw [hadd', ht]
                simp [Nat.cast_add]
              have hlenShift : excursionLength (codeShift s ω) = t := by
                simp [excursionLength, ht]
              have hshiftEq :
                  codeShift (codeFstFirstHit (-(k : ℤ)) ω).toNat ω =
                    codeShift s ω := by
                simp [hc]
              have htime :
                  (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat = s + t := by
                rw [hsum]
                rfl
              calc
                iteratedExcursionCode (k + 1) ω =
                    codeShift (excursionLength (iteratedExcursionCode k ω))
                      (iteratedExcursionCode k ω) := rfl
                _ = codeShift t (codeShift s ω) := by
                  rw [hih, hshiftEq, hlenShift]
                _ = codeShift (s + t) ω := codeShift_comp t s ω
                _ = codeShift (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat ω := by
                  rw [htime]

/-- Almost surely, each iterated excursion has the length between its
consecutive first-hit levels (`lem-disk-walk-conv`, -/
theorem ae_iteratedExcursionLength_eq_firstHit_gap (k : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      excursionLength (iteratedExcursionCode k ω) =
        (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat -
          (codeFstFirstHit (-(k : ℤ)) ω).toNat := by
  cases k with
  | zero =>
      simp [excursionLength, iteratedExcursionCode, codeFstFirstHit_zero]
  | succ k =>
    have hcode := ae_iteratedExcursionCode_eq_firstHit (k + 1)
    have hadd := ae_codeFstFirstHit_add (k + 1) 1 (by omega)
    have hfin := ae_codeFstFirstHit_lt_top_int (-((k + 1 : ℕ) : ℤ))
    have hfinNext := ae_codeFstFirstHit_lt_top_int (-((k + 2 : ℕ) : ℤ))
    filter_upwards [hcode, hadd, hfin, hfinNext] with ω hcodeω haddω hcur hnext
    cases hc : codeFstFirstHit (-1 + -(k : ℤ)) ω with
    | top => simp [hc] at hcur
    | coe s =>
      have hlev : -((k + 1 : ℕ) : ℤ) = -1 + -(k : ℤ) := by
        push_cast
        ring
      have hlevNext : -((k + 2 : ℕ) : ℤ) = -1 + (-1 + -(k : ℤ)) := by
        push_cast
        ring
      have hlevNext' : -((k + 1 + 1 : ℕ) : ℤ) =
          -1 + (-1 + -(k : ℤ)) := by
        push_cast
        ring
      have hc' : codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω = (s : ℕ∞) := by
        rw [hlev]
        exact hc
      have hadd' : codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω =
          (s : ℕ∞) + codeFstFirstHit (-1) (codeShift s ω) := by
        have htmp := haddω
        change codeFstFirstHit (-((k + 1 + 1 : ℕ) : ℤ)) ω =
          codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω +
            codeFstFirstHit (-1) (codeShift
              (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat ω) at htmp
        rw [hlev] at htmp
        rw [hc] at htmp
        rw [hlevNext'] at htmp
        simpa using htmp
      cases ht : codeFstFirstHit (-1) (codeShift s ω) with
      | top =>
          rw [ht] at hadd'
          simp at hadd'
          have hnextN : codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω < ⊤ := by
            rw [← hlevNext]
            exact hnext
          rw [hadd'] at hnextN
          simp at hnextN
      | coe t =>
        have hsumN : codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω =
            ((s + t : ℕ) : ℕ∞) := by
          rw [hadd', ht]
          simp [Nat.cast_add]
        have hsum : codeFstFirstHit (-((k + 1 + 1 : ℕ) : ℤ)) ω =
            ((s + t : ℕ) : ℕ∞) := by
          rw [hlevNext']
          exact hsumN
        have htime :
            (codeFstFirstHit (-((k + 1 + 1 : ℕ) : ℤ)) ω).toNat -
              (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat = t := by
          rw [hsum, hc']
          simp only [ENat.toNat_natCast]
          omega
        have hlen : excursionLength (iteratedExcursionCode (k + 1) ω) = t := by
          rw [hcodeω, hc']
          simp [excursionLength, ht]
        have hlevels : -((k + 1 + 1 : ℕ) : ℤ) = -((k + 2 : ℕ) : ℤ) := by
          push_cast
          omega
        have htime' :
            (codeFstFirstHit (-((k + 2 : ℕ) : ℤ)) ω).toNat -
              (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat = t := by
          rw [← hlevels]
          exact htime
        rw [hlen, htime']

/-- The iterated-code identity and the excursion length formula together -/
theorem ae_iteratedExcursionCode_segment (k : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      iteratedExcursionCode k ω =
          codeShift (codeFstFirstHit (-(k : ℤ)) ω).toNat ω ∧
        excursionLength (iteratedExcursionCode k ω) =
          (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat -
            (codeFstFirstHit (-(k : ℤ)) ω).toNat := by
  filter_upwards [ae_iteratedExcursionCode_eq_firstHit k,
    ae_iteratedExcursionLength_eq_firstHit_gap k] with ω hcode hlen
  exact ⟨hcode, hlen⟩

private noncomputable def levelHitTime (k : ℕ) (ω : ℕ → Fin 3) : ℕ :=
  (codeFstFirstHit (-(k : ℤ)) ω).toNat

private theorem iteratedExcursionWord_eq_codeRange (k : ℕ) (ω : ℕ → Fin 3)
    (t len : ℕ)
    (hcode : iteratedExcursionCode k ω = codeShift t ω)
    (hlen : excursionLength (iteratedExcursionCode k ω) = len) :
    iteratedExcursionWord k ω =
      (List.range len).map (fun i => ω (t + i + 1)) := by
  change (List.range (excursionLength (iteratedExcursionCode k ω))).map
      (fun i => iteratedExcursionCode k ω (i + 1)) = _
  rw [hcode] at hlen ⊢
  rw [hlen]
  simp [codeShift, Nat.add_assoc]

private theorem ae_levelHitTime_succ (k : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      levelHitTime (k + 1) ω =
        levelHitTime k ω + excursionLength (iteratedExcursionCode k ω) := by
  cases k with
  | zero =>
      filter_upwards with ω
      simp [levelHitTime, codeFstFirstHit_zero, iteratedExcursionCode, excursionLength]
  | succ k =>
      have hadd := ae_codeFstFirstHit_add (k + 1) 1 (by omega)
      have hcode := ae_iteratedExcursionCode_eq_firstHit (k + 1)
      have hcur := ae_codeFstFirstHit_lt_top_int (-((k + 1 : ℕ) : ℤ))
      have hnext := ae_codeFstFirstHit_lt_top_int (-((k + 2 : ℕ) : ℤ))
      filter_upwards [hadd, hcode, hcur, hnext] with ω haddω hcodeω hcur hnext
      have hlev : -((k + 1 : ℕ) : ℤ) = -1 + -(k : ℤ) := by
        push_cast
        ring
      have hlevNext : -((k + 2 : ℕ) : ℤ) = -1 + (-1 + -(k : ℤ)) := by
        push_cast
        ring
      have hcur' : codeFstFirstHit (-1 + -(k : ℤ)) ω ≠ ⊤ := by
        rw [← hlev]
        exact ne_of_lt hcur
      have hnext' : codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω ≠ ⊤ := by
        rw [← hlevNext]
        exact ne_of_lt hnext
      cases hc : codeFstFirstHit (-1 + -(k : ℤ)) ω with
      | top => simp [hc] at hcur'
      | coe t =>
        have hadd' : codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω =
            (t : ℕ∞) + codeFstFirstHit (-1) (codeShift t ω) := by
          have htmp := haddω
          change codeFstFirstHit (-((k + 1 + 1 : ℕ) : ℤ)) ω =
            codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω +
              codeFstFirstHit (-1) (codeShift
                (codeFstFirstHit (-((k + 1 : ℕ) : ℤ)) ω).toNat ω) at htmp
          rw [hlev, hc, hlevNext] at htmp
          simpa using htmp
        have hfutureTop : codeFstFirstHit (-1) (codeShift t ω) ≠ ⊤ := by
          intro hf
          have htop : codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω = ⊤ := by
            rw [hf] at hadd'
            calc
              codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω =
                  (t : ℕ∞) + ⊤ := hadd'
              _ = ⊤ := by simp
          exact hnext' htop
        cases hf : codeFstFirstHit (-1) (codeShift t ω) with
        | top => exact (hfutureTop hf).elim
        | coe d =>
          have hsum : codeFstFirstHit (-1 + (-1 + -(k : ℤ))) ω =
              ((t + d : ℕ) : ℕ∞) := by
            rw [hadd', hf]
            simp [Nat.cast_add]
          have htime : levelHitTime (k + 2) ω = t + d := by
            rw [levelHitTime, hlevNext, hsum]
            rfl
          have hwordlen : excursionLength (iteratedExcursionCode (k + 1) ω) = d := by
            rw [hcodeω, hlev, hc]
            simp [excursionLength, hf]
          have hcurtime : levelHitTime (k + 1) ω = t := by
            rw [levelHitTime, hlev, hc]
            rfl
          rw [htime, hcurtime, hwordlen]

private theorem map_range_add_aux {α : Type*} (f : ℕ → α) (a b : ℕ) :
    (List.range (a + b)).map f =
      (List.range a).map f ++ (List.range b).map (fun i => f (a + i)) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, List.range_succ, List.range_succ]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [ih]
      simp [Nat.add_assoc]

private def codeRange (ω : ℕ → Fin 3) (t d : ℕ) : List (Fin 3) :=
  (List.range d).map (fun i => ω (t + i + 1))

private theorem codeRange_take (ω : ℕ → Fin 3) (t d L : ℕ) (hd : d ≤ L) :
    (codeRange ω t L).take d = codeRange ω t d := by
  have hL : L = d + (L - d) := by omega
  rw [codeRange, hL, map_range_add_aux]
  simp [codeRange]

private theorem codeRange_drop (ω : ℕ → Fin 3) (t d L : ℕ) (hd : d ≤ L) :
    (codeRange ω t L).drop (L - d) = codeRange ω (t + (L - d)) d := by
  have hL : L = (L - d) + d := by omega
  rw [codeRange, hL, map_range_add_aux]
  rw [show L - d + d - d = L - d by omega]
  rw [List.drop_append_of_le_length (by simp)]
  have hfirst : (((List.range (L - d)).map (fun i => ω (t + i + 1))).length = L - d) := by
    simp
  have hdrop : ((List.range (L - d)).map (fun i => ω (t + i + 1))).drop (L - d) = [] := by
    simpa only [hfirst] using
      (List.drop_length (l := (List.range (L - d)).map (fun i => ω (t + i + 1))))
  rw [hdrop, List.nil_append]
  apply List.map_congr_left
  intro i hi
  congr 1
  omega

private theorem sum_codeRange (ω : ℕ → Fin 3) (t d : ℕ) :
    ((codeRange ω t d).map lazyTwoDimensionalStep).sum =
      codeWalk ω (t + d) - codeWalk ω t := by
  induction d with
  | zero => simp [codeRange]
  | succ d ih =>
      simp only [codeRange] at ih ⊢
      simp only [List.map_map, Function.comp_def] at ih ⊢
      change (((List.range (d + 1)).map (fun i =>
        lazyTwoDimensionalStep (ω (t + i + 1)))).sum) = _
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton, Nat.add_succ]
      rw [ih, ← codeWalk_succ_sub ω (t + d)]
      abel

private theorem forwardBlocks_eq_codeRange (N M : ℕ) (ω : ℕ → Fin 3)
    (t len : ℕ → ℕ)
    (hstep : ∀ r < N, t (M + r + 1) = t (M + r) + len (M + r))
    (hword : ∀ r < N,
      iteratedExcursionWord (M + r) ω = codeRange ω (t (M + r)) (len (M + r)))
    (hmono : ∀ r ≤ N, t M ≤ t (M + r)) :
    (List.range N).flatMap (fun r => iteratedExcursionWord (M + r) ω) =
      codeRange ω (t M) (t (M + N) - t M) := by
  induction N with
  | zero => simp [codeRange]
  | succ N ih =>
      have hstepN : t (M + N + 1) = t (M + N) + len (M + N) :=
        hstep N (by omega)
      have hwordN : iteratedExcursionWord (M + N) ω =
          codeRange ω (t (M + N)) (len (M + N)) := hword N (by omega)
      have hmonoN : t M ≤ t (M + N) := hmono N (by omega)
      have hprefix := ih
        (fun r hr => hstep r (by omega))
        (fun r hr => hword r (by omega))
        (fun r hr => hmono r (by omega))
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        hprefix, hwordN]
      let a := t (M + N) - t M
      let b := len (M + N)
      have hbase : t M + a = t (M + N) := by
        dsimp [a]
        omega
      rw [show M + (N + 1) = M + N + 1 by omega, hstepN]
      have htotal' : t (M + N) + len (M + N) - t M = a + b := by
        dsimp [a, b]
        omega
      rw [htotal']
      simp only [codeRange]
      rw [show t (M + N) - t M = a by rfl,
        show len (M + N) = b by rfl]
      have hsecond : (List.range b).map (fun i => ω (t (M + N) + i + 1)) =
          (List.range b).map (fun i => ω (t M + (a + i) + 1)) := by
        apply List.map_congr_left
        intro i hi
        congr 1
        omega
      rw [hsecond]
      rw [← map_range_add_aux (fun i => ω (t M + i + 1)) a b]

private theorem finRange_map_val (N : ℕ) :
    (List.finRange N).map Fin.val = List.range N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.finRange_succ, List.map_cons, List.map_map,
        List.range_succ_eq_map]
      simp only [Fin.val_zero, List.cons.injEq, true_and]
      rw [← ih]
      simp only [List.map_map, Function.comp_def, Fin.val_succ,
        Nat.succ_eq_add_one]

private theorem finRange_flatMap_val {α : Type*} (N : ℕ) (f : ℕ → List α) :
    (List.finRange N).flatMap (fun i => f i.val) = (List.range N).flatMap f := by
  rw [← finRange_map_val N]
  simp only [List.flatMap_map, Function.comp_def]

private theorem flatMap_map_right {α β γ : Type*} (xs : List α)
    (f : α → List β) (g : β → γ) :
    xs.flatMap (fun a => (f a).map g) = (xs.flatMap f).map g := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

private theorem backwardBlocks_eq_reverseChronological {α : Type*}
    (N M : ℕ) (f : ℕ → List α) (hNM : N ≤ M) :
    (List.range N).flatMap (fun r => (f (M - 1 - r)).reverse) =
      ((List.range N).flatMap (fun r => f (M - N + r))).reverse := by
  induction N generalizing M with
  | zero => simp
  | succ N ih =>
      have hNM' : N ≤ M := by omega
      have htail : (List.range N).flatMap
          (fun r => f (M - (N + 1) + (r + 1))) =
          (List.range N).flatMap (fun r => f (M - N + r)) := by
        apply List.flatMap_congr
        intro r hr
        apply congrArg f
        have hr' : r < N := by simpa using hr
        omega
      have hhead : (f (M - 1 - N)).reverse = (f (M - (N + 1))).reverse := by
        exact congrArg List.reverse (congrArg f (by omega))
      conv_lhs => rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      conv_rhs => rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        List.reverse_append]
      rw [ih M hNM', htail, hhead]
      simp

private theorem sum_map_neg_steps (xs : List (Fin 3)) :
    ((xs.map (fun c => -lazyTwoDimensionalStep c)).sum) =
      -((xs.map lazyTwoDimensionalStep).sum) := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      rw [neg_add]

private theorem sum_reverse_neg_steps (xs : List (Fin 3)) :
    ((xs.reverse.map (fun c => -lazyTwoDimensionalStep c)).sum) =
      -((xs.map lazyTwoDimensionalStep).sum) := by
  rw [List.map_reverse, List.sum_reverse, sum_map_neg_steps]

private theorem ae_iteratedExcursionLength_pos (k : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure, 1 ≤ excursionLength (iteratedExcursionCode k ω) := by
  have hword : ∀ᵐ w ∂excursionWordLaw, 1 ≤ w.length := by
    rw [excursionWordLaw,
      ae_map_iff measurable_excursionWord.aemeasurable (by measurability)]
    filter_upwards [ae_one_le_excursionLength] with ω hω
    simpa [excursionWord, List.length_map] using hω
  have hmap : ∀ᵐ w ∂iidCodeMeasure.map (iteratedExcursionWord k), 1 ≤ w.length := by
    rw [map_iteratedExcursionWord k]
    exact hword
  have h := (ae_map_iff (measurable_iteratedExcursionWord k).aemeasurable
    (by measurability)).1 hmap
  simpa [iteratedExcursionWord, excursionWord] using h

private theorem ae_all_iteratedExcursionLength_pos :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ k : ℕ, 1 ≤ excursionLength (iteratedExcursionCode k ω) := by
  apply ae_all_iff.mpr
  exact ae_iteratedExcursionLength_pos

/-- Almost surely, the first-hit-centered code window is the UIBHBOT window
formed from the forward excursions and the preceding excursions nearest first -/
theorem ae_centeredWindowAtFirstHit_eq_uibhbotWindowFromWords
    (N M : ℕ) (hNM : N ≤ M) :
    ∀ᵐ ω ∂iidCodeMeasure,
      centeredWindowAtFirstHit N M ω =
        uibhbotWindowFromWords N (fun i : Fin (2 * N) =>
          if hi : i.val < N then
            iteratedExcursionWord (M + i.val) ω
          else
            iteratedExcursionWord (M - 1 - (i.val - N)) ω) := by
  have hrecAll : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ k : ℕ, levelHitTime (k + 1) ω =
        levelHitTime k ω + excursionLength (iteratedExcursionCode k ω) :=
    ae_all_iff.mpr ae_levelHitTime_succ
  have hsegAll : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ k : ℕ, iteratedExcursionWord k ω =
        codeRange ω (levelHitTime k ω)
          (excursionLength (iteratedExcursionCode k ω)) := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [ae_iteratedExcursionCode_segment k] with ω hseg
    exact iteratedExcursionWord_eq_codeRange k ω (levelHitTime k ω)
      (excursionLength (iteratedExcursionCode k ω)) hseg.1 rfl
  filter_upwards [hrecAll, hsegAll, ae_all_iteratedExcursionLength_pos]
    with ω hrec hseg hpos
  let t : ℕ → ℕ := fun k => levelHitTime k ω
  let len : ℕ → ℕ := fun k => excursionLength (iteratedExcursionCode k ω)
  have hadvance : ∀ a r : ℕ, t (a + r) ≥ t a + r := by
    intro a r
    induction r with
    | zero => simp
    | succ r ih =>
        have hr := hrec (a + r)
        have hp := hpos (a + r)
        have hstep : t (a + (r + 1)) = t (a + r) + len (a + r) := by
          simpa [t, len, Nat.add_assoc] using hr
        have hlen : 1 ≤ len (a + r) := by simpa [len] using hp
        omega
  have ht0 : t 0 = 0 := by
    simp [t, levelHitTime, codeFstFirstHit_zero]
  have hfirst : N ≤ t M := by
    have h := hadvance 0 M
    have hM : M ≤ t M := by simpa [ht0] using h
    omega
  have hforwardStep : ∀ r < N,
      t (M + r + 1) = t (M + r) + len (M + r) := by
    intro r hr
    simpa [t, len, Nat.add_assoc] using hrec (M + r)
  have hforwardWord : ∀ r < N,
      iteratedExcursionWord (M + r) ω = codeRange ω (t (M + r)) (len (M + r)) := by
    intro r hr
    simpa [t, len] using hseg (M + r)
  have hforwardMono : ∀ r ≤ N, t M ≤ t (M + r) := by
    intro r hr
    have h := hadvance M r
    dsimp [t] at h ⊢
    omega
  have hforwardRange := forwardBlocks_eq_codeRange N M ω t len
    hforwardStep hforwardWord hforwardMono
  have hforwardWords :
      (List.finRange N).flatMap (fun i => iteratedExcursionWord (M + i.val) ω) =
        codeRange ω (t M) (t (M + N) - t M) := by
    calc
      _ = (List.range N).flatMap (fun r => iteratedExcursionWord (M + r) ω) := by
        exact finRange_flatMap_val N (fun r => iteratedExcursionWord (M + r) ω)
      _ = _ := hforwardRange
  let Q := M - N
  have hpastStep : ∀ r < N,
      t (Q + r + 1) = t (Q + r) + len (Q + r) := by
    intro r hr
    simpa [Q, t, len, Nat.add_assoc] using hrec (Q + r)
  have hpastWord : ∀ r < N,
      iteratedExcursionWord (Q + r) ω = codeRange ω (t (Q + r)) (len (Q + r)) := by
    intro r hr
    simpa [Q, t, len] using hseg (Q + r)
  have hpastMono : ∀ r ≤ N, t Q ≤ t (Q + r) := by
    intro r hr
    have h := hadvance Q r
    dsimp [t] at h ⊢
    omega
  have hpastRange := forwardBlocks_eq_codeRange N Q ω t len
    hpastStep hpastWord hpastMono
  have hpastChron :
      (List.range N).flatMap (fun r => iteratedExcursionWord (Q + r) ω) =
        codeRange ω (t Q) (t M - t Q) := by
    have hQN : Q + N = M := by dsimp [Q]; omega
    simpa [Q, hQN] using hpastRange
  have hpastReverse :
      (List.finRange N).flatMap
          (fun i => (iteratedExcursionWord (M - 1 - i.val) ω).reverse) =
        (codeRange ω (t Q) (t M - t Q)).reverse := by
    calc
      _ = (List.range N).flatMap
          (fun r => (iteratedExcursionWord (M - 1 - r) ω).reverse) := by
            exact finRange_flatMap_val N
              (fun r => (iteratedExcursionWord (M - 1 - r) ω).reverse)
      _ = ((List.range N).flatMap
          (fun r => iteratedExcursionWord (M - N + r) ω)).reverse :=
            backwardBlocks_eq_reverseChronological N M
              (fun k => iteratedExcursionWord k ω) hNM
      _ = (codeRange ω (t Q) (t M - t Q)).reverse := by
            simpa [Q] using congrArg List.reverse hpastChron
  have hpastWords :
      (List.finRange N).flatMap (fun i =>
        (iteratedExcursionWord (M - 1 - i.val) ω).reverse.map
          (fun c => -lazyTwoDimensionalStep c)) =
        (codeRange ω (t Q) (t M - t Q)).reverse.map
          (fun c => -lazyTwoDimensionalStep c) := by
    calc
      _ = ((List.finRange N).flatMap
          (fun i => (iteratedExcursionWord (M - 1 - i.val) ω).reverse)).map
            (fun c => -lazyTwoDimensionalStep c) := by
              rw [flatMap_map_right]
      _ = _ := by rw [hpastReverse]
  have hpastDuration : N ≤ t M - t Q := by
    have h := hadvance Q N
    have hQN : Q + N = M := by dsimp [Q]; omega
    rw [hQN] at h
    omega
  have hforwardDuration : N ≤ t (M + N) - t M := by
    have h := hadvance M N
    omega
  let words : Fin (2 * N) → List (Fin 3) := fun i =>
    if hi : i.val < N then iteratedExcursionWord (M + i.val) ω
    else iteratedExcursionWord (M - 1 - (i.val - N)) ω
  have hforwardWords' :
      (List.finRange N).flatMap (fun i => words ⟨i.val, by omega⟩) =
        codeRange ω (t M) (t (M + N) - t M) := by
    simpa [words] using hforwardWords
  have hpastWords' :
      (List.finRange N).flatMap (fun i =>
        (words ⟨N + i.val, by omega⟩).reverse.map
          (fun c => -lazyTwoDimensionalStep c)) =
        (codeRange ω (t Q) (t M - t Q)).reverse.map
          (fun c => -lazyTwoDimensionalStep c) := by
    simpa [words, Nat.add_sub_cancel_left] using hpastWords
  have hpastPrefix (d : ℕ) (hd : d ≤ N) :
      ((codeRange ω (t Q) (t M - t Q)).reverse).take d =
        (codeRange ω (t M - d) d).reverse := by
    rw [List.take_reverse]
    have hlen : (codeRange ω (t Q) (t M - t Q)).length = t M - t Q := by
      simp [codeRange]
    rw [hlen]
    have hduration : d ≤ t M - t Q := by omega
    rw [codeRange_drop ω (t Q) d (t M - t Q) hduration]
    have hQN : Q + N = M := by dsimp [Q]; omega
    have hadvancePast := hadvance Q N
    rw [hQN] at hadvancePast
    have hQle : t Q ≤ t M := by omega
    have hq : t Q + d ≤ t M := by omega
    have hstart : t Q + (t M - t Q - d) = t M - d := by
      omega
    rw [hstart]
  have hfirst' : N ≤ (codeFstFirstHit (-(M : ℤ)) ω).toNat := by
    simpa [t, levelHitTime] using hfirst
  funext j
  by_cases hj : j.val ≤ N
  · let d := N - j.val
    have hd : d ≤ N := by dsimp [d]; omega
    have hcenter : centeredWindowAtFirstHit N M ω j =
        codeWalk ω (t M + j.val - N) - codeWalk ω (t M) := by
      simp [centeredWindowAtFirstHit, t, levelHitTime, hfirst']
    have hprefix : (((codeRange ω (t Q) (t M - t Q)).reverse.map
        (fun c => -lazyTwoDimensionalStep c)).take d) =
        (codeRange ω (t M - d) d).reverse.map
          (fun c => -lazyTwoDimensionalStep c) := by
      rw [← List.map_take]
      rw [hpastPrefix d hd]
    have hsum : (((codeRange ω (t M - d) d).reverse.map
        (fun c => -lazyTwoDimensionalStep c)).sum) =
        codeWalk ω (t M - d) - codeWalk ω (t M) := by
      rw [sum_reverse_neg_steps, sum_codeRange]
      have htd : t M - d + d = t M := by dsimp [d]; omega
      rw [htd]
      abel
    rw [hcenter]
    simp only [uibhbotWindowFromWords, dif_pos hj, List.map_id]
    rw [show N - j.val = d by rfl, hpastWords', hprefix]
    have htime : t M + j.val - N = t M - d := by dsimp [d]; omega
    rw [htime]
    exact hsum.symm
  · let d := j.val - N
    have hd : d ≤ N := by
      have hjlt : j.val < 2 * N + 1 := j.isLt
      dsimp [d]
      omega
    have hcenter : centeredWindowAtFirstHit N M ω j =
        codeWalk ω (t M + j.val - N) - codeWalk ω (t M) := by
      simp [centeredWindowAtFirstHit, t, levelHitTime, hfirst']
    have hprefix : (codeRange ω (t M) (t (M + N) - t M)).take d =
        codeRange ω (t M) d := codeRange_take ω (t M) d
          (t (M + N) - t M) (by omega)
    have hsum : ((codeRange ω (t M) d).map lazyTwoDimensionalStep).sum =
        codeWalk ω (t M + d) - codeWalk ω (t M) := sum_codeRange ω (t M) d
    rw [hcenter]
    simp only [uibhbotWindowFromWords, dif_neg hj, List.map_id]
    rw [show j.val - N = d by rfl, hforwardWords', hprefix]
    have htime : t M + j.val - N = t M + d := by dsimp [d]; omega
    rw [htime]
    exact hsum.symm

private theorem pi_map_injective_reindex_excursionWords {n m : ℕ}
    (σ : Fin n → Fin m) (hσ : Function.Injective σ)
    (μ : Measure (List (Fin 3))) [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : Fin m => μ).map (fun x i => x (σ i)) =
      Measure.pi fun _ : Fin n => μ := by
  classical
  let f : (Fin m → List (Fin 3)) → (Fin n → List (Fin 3)) :=
    fun x i => x (σ i)
  have hf : Measurable f := measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
  refine (Measure.pi_eq ?_).symm
  intro s hs
  let q : Fin m → Set (List (Fin 3)) := fun j =>
    if h : ∃ i, σ i = j then s (Classical.choose h) else Set.univ
  have hqσ (i : Fin n) : q (σ i) = s i := by
    dsimp [q]
    have he : ∃ k : Fin n, σ k = σ i := ⟨i, rfl⟩
    rw [dif_pos he]
    have hc : Classical.choose he = i := hσ (Classical.choose_spec he)
    rw [hc]
  have hpre : f ⁻¹' Set.univ.pi s = Set.univ.pi q := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, f]
    constructor
    · intro hx j
      by_cases hj : ∃ i, σ i = j
      · rcases hj with ⟨i, hi⟩
        subst j
        rw [hqσ i]
        exact hx i
      · simp [q, hj]
    · intro hx i
      have hi := hx (σ i)
      rw [hqσ i] at hi
      exact hi
  have hprod : (∏ j : Fin m, μ (q j)) = ∏ i : Fin n, μ (s i) := by
    let A : Finset (Fin m) := Finset.univ.image σ
    have hA : A ⊆ Finset.univ := Finset.subset_univ _
    have hout : ∀ j ∈ Finset.univ, j ∉ A → μ (q j) = 1 := by
      intro j _ hj
      have hnot : ¬ ∃ i, σ i = j := by
        intro h
        apply hj
        rcases h with ⟨i, hi⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
      simp [q, hnot]
    rw [← Finset.prod_subset hA hout]
    change (∏ j ∈ Finset.univ.image σ, μ (q j)) = _
    rw [Finset.prod_image hσ.injOn]
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg μ (hqσ i)
  rw [Measure.map_apply hf (MeasurableSet.univ_pi hs), hpre,
    Measure.pi_pi, hprod]

/-- The law of the first-hit-centered window is the UIBHBOT excursion-window law -/
theorem firstHitWindow_law_eq_excursionWindow (N M : ℕ) (hNM : N ≤ M) :
    iidCodeMeasure.map (centeredWindowAtFirstHit N M) = uibhbotExcursionWindowLaw N := by
  classical
  let σ : Fin (2 * N) → Fin (M + N) := fun i =>
    if hi : i.val < N then ⟨M + i.val, by omega⟩
    else ⟨M - 1 - (i.val - N), by omega⟩
  have hσ : Function.Injective σ := by
    intro i j hij
    apply Fin.ext
    have hv : (σ i).val = (σ j).val := congrArg Fin.val hij
    by_cases hi : i.val < N <;> by_cases hj : j.val < N <;>
      simp [σ, hi, hj] at hv ⊢ <;> omega
  let F : (ℕ → Fin 3) → Fin (M + N) → List (Fin 3) :=
    fun ω i => iteratedExcursionWord i.val ω
  let R : (Fin (M + N) → List (Fin 3)) → Fin (2 * N) → List (Fin 3) :=
    fun x i => x (σ i)
  let D : (Fin (2 * N) → List (Fin 3)) → Fin (2 * N + 1) → ℤ × ℤ :=
    uibhbotWindowFromWords N
  have hF : Measurable F := measurable_pi_iff.mpr fun i =>
    measurable_iteratedExcursionWord i.val
  have hR : Measurable R := measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
  have hD : Measurable D := measurable_uibhbotWindowFromWords N
  have hW : Measurable (R ∘ F) := hR.comp hF
  have hwordlaw : iidCodeMeasure.map F = Measure.pi
      (fun _ : Fin (M + N) => excursionWordLaw) := by
    simpa [F] using map_iteratedExcursionWords (M + N)
  have hselected := pi_map_injective_reindex_excursionWords σ hσ excursionWordLaw
  have hAE : centeredWindowAtFirstHit N M =ᵐ[iidCodeMeasure] D ∘ R ∘ F := by
    filter_upwards [ae_centeredWindowAtFirstHit_eq_uibhbotWindowFromWords N M hNM]
      with ω hω
    rw [hω]
    congr 1
    funext i
    by_cases hi : i.val < N <;> simp [D, R, F, σ, hi]
  calc
    iidCodeMeasure.map (centeredWindowAtFirstHit N M) =
        iidCodeMeasure.map (D ∘ R ∘ F) := Measure.map_congr hAE
    _ = iidCodeMeasure.map (D ∘ (R ∘ F)) := by rfl
    _ = (iidCodeMeasure.map (R ∘ F)).map D := by
      rw [Measure.map_map hD hW]
    _ = ((iidCodeMeasure.map F).map R).map D := by
      rw [Measure.map_map hR hF]
    _ = ((Measure.pi (fun _ : Fin (M + N) => excursionWordLaw)).map R).map D := by
      rw [hwordlaw]
    _ = (Measure.pi (fun _ : Fin (2 * N) => excursionWordLaw)).map D := by
      rw [hselected]
    _ = uibhbotExcursionWindowLaw N := rfl

end DirectedDistances.RandomWalk
