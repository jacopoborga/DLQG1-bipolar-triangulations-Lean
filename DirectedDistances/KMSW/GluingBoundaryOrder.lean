module

public import DirectedDistances.KMSW.PrimedHattedGluingBoundary

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.

C13 replacement edges lie on the permanent upper-right boundary. The lower-right
selector `kmswRightBoundaryEdge` instead degenerates to the retained C18 root.
Code index `m` reads source time `S'_{m+1}` under positive-time counting convention. -/

public section
namespace DirectedDistances.KMSW

open scoped Classical

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
Every primed lower-right stage list consists only of the retained root. -/
theorem primedStage_LR_eq_root (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    (kmswStage (primedCode (primedSimInput w) h) m).LR = [0] := by
  cases m with
  | zero => rfl
  | succ m =>
    obtain ⟨_, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
    have ha := kmswMissingRootStage_agree (primedCode (primedSimInput w) h) (m + 1)
    exact ha.2.2.2.2.2.2.2.2.2.2.symm.trans hs.LR_root

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The primed vertical coordinate never drops below its initial level. -/
theorem primed_R_nonneg (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    0 ≤ R (primedCode (primedSimInput w) h) m := by
  have hl := kmswStage_LR_length (primedCode (primedSimInput w) h) m
  rw [primedStage_LR_eq_root, List.length_singleton] at hl
  have hm := runningMin_le (R (primedCode (primedSimInput w) h)) m m le_rfl
  change minR (primedCode (primedSimInput w) h) m ≤ _ at hm
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
There are no positive lower-right record times in the primed walk. -/
theorem primed_right_record_iff_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) :
    (∀ j, j < m → R (primedCode (primedSimInput w) h) m <
      R (primedCode (primedSimInput w) h) j) ↔ m = 0 := by
  constructor
  · intro hr
    by_contra hn
    have hh := hr 0 (by omega)
    have hp := primed_R_nonneg w h m
    have hz : R (primedCode (primedSimInput w) h) 0 = 0 := rfl
    omega
  · rintro rfl j hj
    omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The lower-right selector returns the root even beyond its finite record set.
This is its explicit fallback behavior, not an infinite boundary enumeration. -/
theorem primedRightBoundaryEdge_eq_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (i : ℕ) : kmswRightBoundaryEdge (primedCode (primedSimInput w) h) i = 0 := by
  let P := fun m => ∀ j, j < m → R (primedCode (primedSimInput w) h) m <
    R (primedCode (primedSimInput w) h) j
  have hc (n : ℕ) : Nat.count P (n + 1) = 1 := by
    induction n with
    | zero => simp only [Nat.count_succ, Nat.count_zero, P,
        primed_right_record_iff_zero, ↓reduceIte, zero_add]
    | succ n ih =>
      rw [Nat.count_succ, ih]
      have hn : ¬ P (n + 1) := by
        rw [show P (n + 1) ↔ n + 1 = 0 from primed_right_record_iff_zero w h _]
        omega
      simp only [hn, ↓reduceIte, add_zero]
  cases i with
  | zero => exact kmswRightBoundaryEdge_zero _
  | succ i =>
    have hn : ¬ ∃ m, i + 1 < Nat.count P (m + 1) := by
      rintro ⟨m, hm⟩
      rw [hc] at hm
      omega
    change act _ (natSelect P (i + 1)) = 0
    rw [natSelect, dite_eq_right hn]
    rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The first beta-zero preimage is edge ID two, created by the first C13 up step. -/
theorem primedBeta0EdgeIndex_zero_eq_two (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hrawfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    primedBeta0EdgeIndex w h hfin hb hrawfin 0 = 2 := by
  apply primedLimitEdgeMap_injective w h
  rw [primedBeta0EdgeIndex_maps_to_stream,
    beta0_westBoundary_stream_eq_left_exit,
    PaperProofs.Section5.sourceFlowNL_eq_walkNL]
  let u := primedCode (primedSimInput w) h
  have hc : u 0 = 1 := primedCode_zero (primedSimInput w) h
  have ha : 2 < (kmswMissingRootStage u 1).nextEdge := by
    simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit, State.addEdge]
  rw [(primedLimit_maps_eq_of_allocated w h 1).1 2 ha]
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The existing primed Prop uses the lower-right selector and is false already
at beta-zero index zero: that selector is zero and its required preimage is two. -/
theorem primedRightBoundaryBeta0IndexCorrespondence_false (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (hrawfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    ¬ PrimedRightBoundaryBeta0IndexCorrespondence w h hfin hb hrawfin := by
  intro hh
  obtain ⟨j, hj⟩ := hh 0
  rw [primedRightBoundaryEdge_eq_zero, primedBeta0EdgeIndex_zero_eq_two] at hj
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
Counting a predicate is constant across an interval containing no hits. -/
private theorem count_eq_of_no_hits (P : ℕ → Prop) [DecidablePred P]
    {a b : ℕ} (hab : a ≤ b) (hn : ∀ n, a ≤ n → n < b → ¬ P n) :
    Nat.count P b = Nat.count P a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [Nat.count_succ, ih (fun n hna hnb => hn n hna (by omega))]
    simp only [hn b hab (by omega), ↓reduceIte, add_zero]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
Source exits occur in strictly increasing compressed code order. -/
theorem hatExitIndex_strictMono (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    StrictMono (hatExitIndex w h) := by
  apply strictMono_nat_of_lt_succ
  intro k
  by_contra hn
  have hm := quadrantRStageTime_mono w h
    (show hatExitIndex w h (k + 1) ≤ hatExitIndex w h k by omega)
  rw [quadrantRStageTime_hatExitIndex, quadrantRStageTime_hatExitIndex] at hm
  have h0 := (walkNL_spec w h k).1
  have h1 := (walkNR_succ_spec w h k).1
  have h2 := (walkNL_spec w h (k + 1)).1
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The splitter depth is zero at each compressed exit. -/
private theorem gluing_depth_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    hatPhaseDepth w (quadrantRStageTime w h (hatExitIndex w h k)) = 0 := by
  rw [quadrantRStageTime_hatExitIndex]
  have hp := (quadrantRStageTime_spec w h (hatExitIndex w h k)).1
  rw [quadrantRStageTime_hatExitIndex] at hp
  apply (hatPhaseDepth_left_exit_iff w (walkNL w h k - 1) hp
    (walkNL_previous_code w h k)).1
  have hpos := (walkNL_spec w h k).1
  have ht : walkNL w h k - 1 + 1 = walkNL w h k := by omega
  rw [ht]
  exact (quadrantSplitState_at_walkNL (quadrantTrajectoryOfStageCodes w) h k).1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The hatted horizontal coordinate is the number of completed exits plus
the actual splitter depth. Thus it is not identified with the uncompressed coordinate. -/
theorem hat_L_eq_exitCount_add_depth (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) :
    L (hatCodes w h) m =
      (Nat.count (fun n => ∃ k, hatExitIndex w h k = n) m : ℤ) +
        (hatPhaseDepth w (quadrantRStageTime w h m) : ℤ) := by
  induction m with
  | zero =>
    have ht : quadrantRStageTime w h 0 = 0 := by
      apply quadrantRStageTime_eq_of_initial_R
      have hh := (walkNL_spec w h 0).1
      rw [walkNR_zero] at hh
      omega
    rw [ht]
    rfl
  | succ m ih =>
    have hs : L (hatCodes w h) (m + 1) = L (hatCodes w h) m +
        (RandomWalk.lazyTwoDimensionalStep (hatCodes w h m)).1 :=
      Finset.sum_range_succ _ _
    rw [hs, ih, Nat.count_succ]
    by_cases hex : ∃ k, hatExitIndex w h k = m
    · obtain ⟨k, rfl⟩ := hex
      have ht : quadrantRStageTime w h (hatExitIndex w h k + 1) =
          walkNR w h (k + 1) := by
        rw [← hatCodeTime_succ, hatCodeTime_at_exit]
        have hh := (walkNR_succ_spec w h k).1
        omega
      rw [gluing_depth_exit, ht, hatPhaseDepth_at_walkNR, hatCodes_at_exit]
      simp only [show (∃ j, hatExitIndex w h j = hatExitIndex w h k) from ⟨k, rfl⟩,
        ↓reduceIte, Nat.cast_add, Nat.cast_one]
      rfl
    · have ht : quadrantRStageTime w h (m + 1) = quadrantRStageTime w h m + 1 := by
        rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hex]
      have hc : hatCodes w h m = w (quadrantRStageTime w h m) := by
        rw [hatCodes, hatCodeTime_of_not_exit w h m hex]
      have hp := (quadrantRStageTime_spec w h m).1
      have hn := (quadrantRStageTime_spec w h (m + 1)).1
      rw [ht] at hn
      have hd := hatPhaseDepth_step w (quadrantRStageTime w h m) hp hn
      rw [ht, hd, hc]
      simp only [hex, ↓reduceIte, add_zero]
      generalize hw : w (quadrantRStageTime w h m) = c at *
      fin_cases c
      · have hpos : hatPhaseDepth w (quadrantRStageTime w h m) ≠ 0 := by
          intro hz
          have hh := (hatPhaseDepth_left_exit_iff w _ hp hw).2 hz
          rw [hn] at hh
          contradiction
        norm_num [RandomWalk.lazyTwoDimensionalStep]
        omega
      · norm_num [RandomWalk.lazyTwoDimensionalStep]
      · norm_num [RandomWalk.lazyTwoDimensionalStep]
        omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
A strictly increasing enumeration has exactly `k` hits before its `k`th value. -/
private theorem count_range_at (f : ℕ → ℕ) (hf : StrictMono f) (k : ℕ) :
    Nat.count (fun n => ∃ j, f j = n) (f k) = k := by
  induction k with
  | zero =>
    apply Nat.count_iff_forall_not.mpr
    rintro n hn ⟨j, rfl⟩
    have hh := hf.monotone (Nat.zero_le j)
    omega
  | succ k ih =>
    have hab : f k + 1 ≤ f (k + 1) := hf (by omega)
    have heq := count_eq_of_no_hits (fun n => ∃ j, f j = n) hab
      (by
        rintro n hna hnb ⟨j, rfl⟩
        by_cases hj : j ≤ k
        · have hh := hf.monotone hj
          omega
        · have hh := hf.monotone (show k + 1 ≤ j by omega)
          omega)
    rw [heq, Nat.count_succ, ih]
    simp only [show (∃ j, f j = f k) from ⟨k, rfl⟩, ↓reduceIte]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The strict future horizontal records are exactly the compressed exit times. -/
theorem hat_left_record_iff_exit (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    (∀ j, m < j → L (hatCodes w h) m + 1 ≤ L (hatCodes w h) j) ↔
      ∃ k, hatExitIndex w h k = m := by
  let P := fun n => ∃ k, hatExitIndex w h k = n
  have hf := hatExitIndex_strictMono w h
  constructor
  · intro hr
    by_contra hn
    have hle (k : ℕ) : k ≤ hatExitIndex w h k := by
      induction k with
      | zero => omega
      | succ k ih =>
        have hh : hatExitIndex w h k < hatExitIndex w h (k + 1) :=
          hf (Nat.lt_succ_self k)
        omega
    have hex : ∃ k, m ≤ hatExitIndex w h k := ⟨m, hle m⟩
    let k := Nat.find hex
    have hk : m ≤ hatExitIndex w h k := Nat.find_spec hex
    have hlt : m < hatExitIndex w h k := by
      by_contra hh
      exact hn ⟨k, by omega⟩
    have hc : Nat.count P (hatExitIndex w h k) = Nat.count P m := by
      apply count_eq_of_no_hits P hk
      rintro n hna hnb ⟨l, rfl⟩
      by_cases hl : l < k
      · have hh := Nat.find_min hex hl
        omega
      · have hh := hf.monotone (show k ≤ l by omega)
        omega
    have hh := hr (hatExitIndex w h k) hlt
    rw [hat_L_eq_exitCount_add_depth, hat_L_eq_exitCount_add_depth,
      gluing_depth_exit] at hh
    dsimp only [P] at hc
    omega
  · rintro ⟨k, rfl⟩ j hj
    have hc := Nat.count_strict_mono (p := P) (show P (hatExitIndex w h k) from ⟨k, rfl⟩) hj
    rw [hat_L_eq_exitCount_add_depth, hat_L_eq_exitCount_add_depth, gluing_depth_exit]
    dsimp only [P] at hc
    omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The `k`th selected left record is the `k`th exit, including index zero. -/
theorem hat_left_record_select (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    natSelect (fun m => ∀ j, m < j →
      L (hatCodes w h) m + 1 ≤ L (hatCodes w h) j) k = hatExitIndex w h k := by
  have hc : Nat.count (fun m => ∀ j, m < j →
      L (hatCodes w h) m + 1 ≤ L (hatCodes w h) j) (hatExitIndex w h k) = k := by
    rw [natCount_congr (hatExitIndex w h k)
      (fun m _ => hat_left_record_iff_exit w h m)]
    exact count_range_at _ (hatExitIndex_strictMono w h) k
  conv_lhs => rw [← hc]
  exact natSelect_count (P := fun m => ∀ j, m < j →
    L (hatCodes w h) m + 1 ≤ L (hatCodes w h) j)
    ((hat_left_record_iff_exit w h _).mpr ⟨k, rfl⟩)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The hatted left-boundary edges map to beta-zero edges in exactly the same order. -/
theorem hattedLeftBoundaryBeta0EdgeCorrespondence_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) : HattedLeftBoundaryBeta0EdgeCorrespondence w h hfin hb := by
  intro k
  rw [kmswLeftBoundaryEdge, hat_left_record_select]
  rw [hatLimitEdgeMap_eq_stage w h (hatExitIndex w h k) _
    (act_lt_nextEdge _ le_rfl)]
  have ha := (hatAll_sim w h (hatExitIndex w h k)).incidenceSim.active
  rw [quadrantRStageTime_hatExitIndex] at ha
  rw [beta0_westBoundary_stream_eq_left_exit,
    PaperProofs.Section5.sourceFlowNL_eq_walkNL]
  exact ha

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The C13 replacement at every block base is an up step. -/
private theorem gluing_primed_base_code (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) :
    primedCode (primedSimInput w) h (primedIntervalBase (primedSimInput w) h k) = 1 := by
  simpa only [add_zero, ↓reduceIte] using
    primedCode_block (primedSimInput w) h k 0 (primedIntervalWidth_pos _ h k)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The predecessor of block `k+1` is in block `k`, with no positive-time counting convention code-time shift omitted. -/
private theorem gluing_interval_predecessor (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    primedIntervalIndex (primedSimInput w) h
        (primedIntervalBase (primedSimInput w) h (k + 1) - 1) = k := by
  let b := primedIntervalBase (primedSimInput w) h (k + 1)
  have hw := primedIntervalWidth_pos (primedSimInput w) h k
  have hb := primedIntervalBase_succ (primedSimInput w) h k
  have hpos : 0 < b := by dsimp [b]; omega
  apply Nat.le_antisymm
  · exact Nat.find_min' _ (show b - 1 < b by omega)
  · by_contra hlt
    change ¬ k ≤ primedIntervalIndex (primedSimInput w) h (b - 1) at hlt
    have hs := primedIntervalIndex_spec (primedSimInput w) h (b - 1)
    have hm := primedIntervalBase_mono (primedSimInput w) h
      (show primedIntervalIndex (primedSimInput w) h (b - 1) + 1 ≤ k by omega)
    dsimp [b] at hs hm ⊢
    omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The missing side created at block base `k` maps to precisely source exit `k`. -/
theorem primed_boundary_creation_image (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) :
    primedLimitEdgeMap w h
        ((kmswMissingRootStage (primedCode (primedSimInput w) h)
          (primedIntervalBase (primedSimInput w) h k)).nextEdge + 1) =
      act w (walkNL w h k - 1) := by
  let u := primedCode (primedSimInput w) h
  cases k with
  | zero =>
    rw [primedIntervalBase_zero]
    change primedLimitEdgeMap w h 2 = _
    have hc : u 0 = 1 := primedCode_zero (primedSimInput w) h
    have ha : 2 < (kmswMissingRootStage u 1).nextEdge := by
      simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
        kmswMissingRootInit, kmswInit, State.addEdge]
    rw [(primedLimit_maps_eq_of_allocated w h 1).1 2 ha]
    rfl
  | succ k =>
    let m := primedIntervalBase (primedSimInput w) h (k + 1)
    let sh := kmswMissingRootStage u m
    have hm : m ≠ 0 := by
      have hb := primedIntervalBase_ge (primedSimInput w) h (k + 1)
      dsimp [m]
      omega
    have hi : primedIntervalIndex (primedSimInput w) h (m - 1) = k :=
      gluing_interval_predecessor w h k
    have hc : u m = 1 := (primedCrossing_codes w h k).1
    have ha : sh.nextEdge + 1 < (kmswMissingRootStage u (m + 1)).nextEdge := by
      simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
        State.addEdge, sh]
    change primedLimitEdgeMap w h (sh.nextEdge + 1) = _
    rw [(primedLimit_maps_eq_of_allocated w h (m + 1)).1 _ ha]
    have ho : ¬ m < primedIntervalBase (primedSimInput w) h (k + 1) := lt_irrefl m
    simp only [primedAllEdgeMap, hm, ↓reduceIte, hi, ho]
    change primedCrossingEdgeMap sh _ _ (sh.nextEdge + 1) = _
    simp only [primedCrossingEdgeMap, Nat.add_one_ne_self, ↓reduceIte]
    rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The exact beta-zero preimage is the newly created C13 missing side, not
its code-time index and not the retained C18 root. -/
theorem primedBeta0EdgeIndex_eq_creation (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hrawfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) (k : ℕ) :
    primedBeta0EdgeIndex w h hfin hb hrawfin k =
      (kmswMissingRootStage (primedCode (primedSimInput w) h)
        (primedIntervalBase (primedSimInput w) h k)).nextEdge + 1 := by
  apply primedLimitEdgeMap_injective w h
  rw [primedBeta0EdgeIndex_maps_to_stream, primed_boundary_creation_image,
    beta0_westBoundary_stream_eq_left_exit, PaperProofs.Section5.sourceFlowNL_eq_walkNL]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The primed edge-ID correspondence is strictly increasing in beta-zero order. -/
theorem primedBeta0EdgeIndex_strictMono (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hrawfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    StrictMono (primedBeta0EdgeIndex w h hfin hb hrawfin) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [primedBeta0EdgeIndex_eq_creation, primedBeta0EdgeIndex_eq_creation]
  let u := primedCode (primedSimInput w) h
  let b := primedIntervalBase (primedSimInput w) h k
  have hc : u b = 1 := gluing_primed_base_code w h k
  have hg : b + 1 ≤ primedIntervalBase (primedSimInput w) h (k + 1) := by
    have hw := primedIntervalWidth_pos (primedSimInput w) h k
    rw [primedIntervalBase_succ]
    dsimp only [b]
    omega
  have hm := kmswStage_nextEdge_mono u hg
  have ha := kmswMissingRootStage_agree u b
  have ha' := kmswMissingRootStage_agree u (primedIntervalBase (primedSimInput w) h (k + 1))
  have hs : (kmswStage u (b + 1)).nextEdge = (kmswStage u b).nextEdge + 2 := by
    rw [kmswStage, hc]
    rfl
  rw [hs] at hm
  change (kmswMissingRootStage u b).nextEdge + 1 <
    (kmswMissingRootStage u (primedIntervalBase (primedSimInput w) h (k + 1))).nextEdge + 1
  rw [ha.2.1, ha'.2.1]
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
An upper-right edge either survives on the stack or becomes present. -/
private theorem gluing_UR_or_present_later (u : ℕ → Fin 3) (a b e : ℕ)
    (hab : a ≤ b) (he : e ∈ (kmswStage u a).UR) :
    e ∈ (kmswStage u b).UR ∨ (kmswStage u b).present e = true := by
  have hbound := (kmswStage_boundary_ids_lt_nextEdge u a).2 e (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr he)))
  induction b, hab using Nat.le_induction with
  | base => exact Or.inl he
  | succ b hab ih =>
    rcases ih with hu | hp
    · generalize hc : u b = c
      fin_cases c
      · left
        cases hpred : (kmswStage u b).UL.dropLast.reverse <;>
          simpa [kmswStage, hc, kmswStep, kmswCodeStep,
            kmswStepOfStep, hpred, State.addEdge] using hu
      · left
        simpa [kmswStage, hc, kmswStep, kmswCodeStep,
          kmswStepOfStep, State.addEdge, List.mem_cons] using Or.inr hu
      · cases hur : (kmswStage u b).UR with
        | nil => rw [hur] at hu; cases hu
        | cons f fs =>
          rw [hur] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · right
            simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur]
          · left
            simpa [kmswStage, hc, kmswStep, kmswCodeStep,
              kmswStepOfStep, hur] using hu
    · right
      exact (present_mono u (hbound.trans_le (kmswStage_nextEdge_mono u hab))
        hp (b + 1) (Nat.le_succ b)).2

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
Every beta-zero preimage stays on the upper-right boundary from its creation
onward. This is the corrected boundary run; the lower-right selector is refuted above. -/
theorem primedBeta0EdgeIndex_mem_UR (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hrawfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (k n : ℕ) (hn : primedIntervalBase (primedSimInput w) h k + 1 ≤ n) :
    primedBeta0EdgeIndex w h hfin hb hrawfin k ∈
      (kmswStage (primedCode (primedSimInput w) h) n).UR := by
  let u := primedCode (primedSimInput w) h
  let b := primedIntervalBase (primedSimInput w) h k
  let e := primedBeta0EdgeIndex w h hfin hb hrawfin k
  have hc : u b = 1 := gluing_primed_base_code w h k
  have he : e = (kmswStage u b).nextEdge + 1 := by
    dsimp only [e]
    rw [primedBeta0EdgeIndex_eq_creation]
    exact congrArg (fun t => t + 1) (kmswMissingRootStage_agree u b).2.1
  have hnew : e ∈ (kmswStage u (b + 1)).UR := by
    rw [kmswStage, hc]
    change e ∈ ((kmswStage u b).nextEdge + 1) :: (kmswStage u b).UR
    exact List.mem_cons.mpr (Or.inl he)
  rcases gluing_UR_or_present_later u (b + 1) n e hn hnew with hu | hp
  · exact hu
  · have hepos : e ≠ 0 := by omega
    have ha : e < (kmswStage u (b + 1)).nextEdge := by
      rw [he, kmswStage, hc]
      change (kmswStage u b).nextEdge + 1 < (kmswStage u b).nextEdge + 2
      omega
    have han := ha.trans_le (kmswStage_nextEdge_mono u hn)
    have hag := kmswMissingRootStage_agree u n
    apply False.elim
    apply primedBeta0EdgeIndex_missing w h hfin hb hrawfin k
    exact ⟨n, hag.2.1.symm ▸ han, (hag.2.2.2.2.1 e hepos).trans hp⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
Inside a primed block, vertical displacement agrees with the original walk
after the initial C13 up step. -/
private theorem gluing_primed_R_block (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k j : ℕ) (hj : 1 ≤ j) (hwidth : j ≤ primedIntervalWidth (primedSimInput w) h k) :
    R (primedCode (primedSimInput w) h)
        (primedIntervalBase (primedSimInput w) h k + j) =
      R (primedCode (primedSimInput w) h) (primedIntervalBase (primedSimInput w) h k) +
        1 + R w (walkNL w h k + j - 1) - R w (walkNL w h k) := by
  let u := primedCode (primedSimInput w) h
  let b := primedIntervalBase (primedSimInput w) h k
  induction j, hj using Nat.le_induction with
  | base =>
    have hs : R u (b + 1) = R u b + 1 := by
      rw [R, Finset.sum_range_succ]
      have hc : u b = 1 := gluing_primed_base_code w h k
      rw [hc]
      rfl
    change R u (b + 1) = R u b + 1 + R w (walkNL w h k + 1 - 1) - _
    rw [hs, Nat.add_sub_cancel]
    omega
  | succ j hj ih =>
    have hcode : u (b + j) = w (walkNL w h k + j - 1) := by
      have hh := primedCode_block (primedSimInput w) h k j (by omega)
      simpa only [show j ≠ 0 from by omega, ↓reduceIte, primedIntervalLeft] using hh
    have hs : R u (b + (j + 1)) = R u (b + j) +
        (RandomWalk.lazyTwoDimensionalStep (w (walkNL w h k + j - 1))).2 := by
      rw [← Nat.add_assoc]
      rw [R, Finset.sum_range_succ]
      rw [hcode]
      rfl
    have ht : walkNL w h k + (j + 1) - 1 = (walkNL w h k + j - 1) + 1 := by omega
    have hw : R w ((walkNL w h k + j - 1) + 1) = R w (walkNL w h k + j - 1) +
        (RandomWalk.lazyTwoDimensionalStep (w (walkNL w h k + j - 1))).2 :=
      Finset.sum_range_succ _ _
    change R u (b + (j + 1)) = R u b + 1 + _ - _
    rw [hs, ih (by omega), ht, hw]
    dsimp only [u, b]
    omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The original vertical coordinate returns to its left-exit level just before
the next right entry, whose last down step is excluded from this primed block. -/
private theorem gluing_R_before_entry (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) : R w (walkNR w h (k + 1) - 1) = R w (walkNL w h k) := by
  have hp := (walkNR_succ_spec w h k).1
  have hl := (walkNR_succ_spec w h k).2
  have hc := walkNR_succ_previous_code w h k
  have ht : walkNR w h (k + 1) - 1 + 1 = walkNR w h (k + 1) := by omega
  have hs : R w (walkNR w h (k + 1)) = R w (walkNR w h (k + 1) - 1) - 1 := by
    conv_lhs => rw [← ht]
    rw [R, Finset.sum_range_succ, hc]
    rfl
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The vertical level at the `k`th primed block base is exactly `k`. -/
theorem primed_R_at_block_base (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    R (primedCode (primedSimInput w) h)
      (primedIntervalBase (primedSimInput w) h k) = (k : ℤ) := by
  induction k with
  | zero => rw [primedIntervalBase_zero]; rfl
  | succ k ih =>
    have hw := primedIntervalWidth_pos (primedSimInput w) h k
    have hh := gluing_primed_R_block w h k (primedIntervalWidth (primedSimInput w) h k)
      hw le_rfl
    have ht : walkNL w h k + primedIntervalWidth (primedSimInput w) h k - 1 =
        walkNR w h (k + 1) - 1 := by
      have hg := (walkNR_succ_spec w h k).1
      change walkNL w h k + (walkNR w h (k + 1) - walkNL w h k) - 1 = _
      omega
    rw [ht, gluing_R_before_entry, ih] at hh
    rw [primedIntervalBase_succ]
    omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The upper-right stack has exactly `k` entries before replacement `k`. -/
theorem primed_UR_length_at_block_base (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) :
    (kmswStage (primedCode (primedSimInput w) h)
      (primedIntervalBase (primedSimInput w) h k)).UR.length = k := by
  let u := primedCode (primedSimInput w) h
  let b := primedIntervalBase (primedSimInput w) h k
  have hLR := kmswStage_LR_length u b
  rw [primedStage_LR_eq_root, List.length_singleton] at hLR
  have hUR := kmswStage_UR_length u b
  have hR := primed_R_at_block_base w h k
  change R u b = _ at hR
  dsimp only [u, b] at hUR hLR hR
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
A permanently missing upper-right edge retains its index counted from
the bottom of the stack. -/
private theorem gluing_UR_reverse_index_persists (u : ℕ → Fin 3) (a b i e : ℕ)
    (hab : a ≤ b) (hmissing : ¬ EdgePresent u e)
    (he : (kmswStage u a).UR.reverse[i]? = some e) :
    (kmswStage u b).UR.reverse[i]? = some e := by
  induction b, hab using Nat.le_induction with
  | base => exact he
  | succ b hab ih =>
    have hi : i < (kmswStage u b).UR.reverse.length :=
      (List.getElem?_eq_some_iff.mp ih).1
    generalize hc : u b = c
    fin_cases c
    · cases hp : (kmswStage u b).UL.dropLast.reverse <;>
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp,
          State.addEdge] using ih
    · have hs : (kmswStage u (b + 1)).UR.reverse =
          (kmswStage u b).UR.reverse ++ [(kmswStage u b).nextEdge + 1] := by
        simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      rw [hs, List.getElem?_append_left hi]
      exact ih
    · cases hur : (kmswStage u b).UR with
      | nil => rw [hur] at ih; simp only [List.reverse_nil, List.getElem?_nil] at ih
               contradiction
      | cons f fs =>
        have hi' : i < fs.length := by
          by_contra hn
          have hie : i = fs.length := by
            rw [hur, List.length_reverse, List.length_cons] at hi
            omega
          have hef : e = f := by
            rw [hur, List.reverse_cons, hie] at ih
            have hh : (fs.reverse ++ [f])[fs.length]? = some f := by
              rw [List.getElem?_append_right (by
                simp only [List.length_reverse]
                exact le_rfl)]
              simp only [List.length_reverse, Nat.sub_self, List.getElem?_cons_zero]
            rw [hh] at ih
            exact Option.some.inj ih.symm
          apply hmissing
          subst e
          have ha := (kmswStage_boundary_ids_lt_nextEdge u b).2 f (by
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inr (hur ▸ List.mem_cons_self))))
          refine ⟨b + 1, ha.trans_le (kmswStage_nextEdge_mono u (Nat.le_succ b)), ?_⟩
          simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur]
        have hh : fs.reverse[i]? = some e := by
          rw [hur, List.reverse_cons,
            List.getElem?_append_left (by simpa only [List.length_reverse] using hi')] at ih
          exact ih
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur] using hh

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The corrected same-index primed boundary correspondence: index `k` from
the bottom of every sufficiently late upper-right stack is precisely beta-zero preimage `k`.
Missing edges have geometric ordering here, without a directed orientation. -/
theorem primedBeta0EdgeIndex_UR_reverse_order (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hrawfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (k n : ℕ) (hn : primedIntervalBase (primedSimInput w) h k + 1 ≤ n) :
    (kmswStage (primedCode (primedSimInput w) h) n).UR.reverse[k]? =
      some (primedBeta0EdgeIndex w h hfin hb hrawfin k) := by
  let u := primedCode (primedSimInput w) h
  let b := primedIntervalBase (primedSimInput w) h k
  let e := primedBeta0EdgeIndex w h hfin hb hrawfin k
  have hc : u b = 1 := gluing_primed_base_code w h k
  have he : e = (kmswStage u b).nextEdge + 1 := by
    dsimp only [e]
    rw [primedBeta0EdgeIndex_eq_creation]
    exact congrArg (fun t => t + 1) (kmswMissingRootStage_agree u b).2.1
  have hmissing : ¬ EdgePresent u e := by
    rintro ⟨m, hm, hp⟩
    have hepos : e ≠ 0 := by omega
    have ha := kmswMissingRootStage_agree u m
    apply primedBeta0EdgeIndex_missing w h hfin hb hrawfin k
    exact ⟨m, ha.2.1.symm ▸ hm, (ha.2.2.2.2.1 e hepos).trans hp⟩
  apply gluing_UR_reverse_index_persists u (b + 1) n k e hn hmissing
  have hl : (kmswStage u b).UR.reverse.length = k := by
    simpa only [List.length_reverse] using primed_UR_length_at_block_base w h k
  rw [kmswStage, hc]
  change (((kmswStage u b).nextEdge + 1) :: (kmswStage u b).UR).reverse[k]? = some e
  rw [List.reverse_cons, List.getElem?_append_right (by omega), hl, Nat.sub_self]
  exact congrArg some he.symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Lemma 5.13; not a paper result.
The hatted left boundary and the permanent primed upper-right boundary glue
at the same beta-zero index. The primed geometric edge remains tagged missing. -/
theorem gluingBoundary_same_index (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hrawfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (k n : ℕ) (hn : primedIntervalBase (primedSimInput w) h k + 1 ≤ n) :
    hatLimitEdgeMap w h (kmswLeftBoundaryEdge (hatCodes w h) k) =
        primedLimitEdgeMap w h (primedBeta0EdgeIndex w h hfin hb hrawfin k) ∧
      (kmswStage (primedCode (primedSimInput w) h) n).UR.reverse[k]? =
        some (primedBeta0EdgeIndex w h hfin hb hrawfin k) ∧
      ¬ PrimedEdgePresent w h (primedBeta0EdgeIndex w h hfin hb hrawfin k) := by
  refine ⟨?_, primedBeta0EdgeIndex_UR_reverse_order w h hfin hb hrawfin k n hn,
    primedBeta0EdgeIndex_missing w h hfin hb hrawfin k⟩
  exact (hattedLeftBoundaryBeta0EdgeCorrespondence_proved w h hrawfin hb k).trans
    (primedBeta0EdgeIndex_maps_to_stream w h hfin hb hrawfin k).symm

end DirectedDistances.KMSW
