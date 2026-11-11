module

public import DirectedDistances.KMSW.PrimedSimIterate

/-! # Coherent all-stage maps for the primed active simulation

P2 helper toward lem-quad-kmsw; not counted
strictly after an interval base, so it cannot describe local stage zero.
The canonical recursive maps have a separate initial-simulation clause
before the first C13 replacement triangle. These are finite incidence and
frontier helpers; ordered planar identification remains a separate obligation. -/

public section
namespace DirectedDistances.KMSW

/-- P2 helper toward lem-quad-kmsw; not counted
or pair of maps can make the active root-LR simulation hold at local stage
zero: its inherited `after_base` field would assert a natural number is
strictly less than zero. -/
theorem primedSimActiveRootLR_zero_impossible
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k n : ℕ)
    (eφ vφ : ℕ → ℕ) :
    ¬ PrimedSimActiveRootLR (primedCode (primedSimInput w) h)
      w h k 0 n eφ vφ := by
  intro sim
  exact Nat.not_lt_zero _ sim.forget.after_base

private theorem stageIndex_eq (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k m : ℕ)
    (hl : primedIntervalBase (primedSimInput w) h k ≤ m)
    (hr : m < primedIntervalBase (primedSimInput w) h (k + 1)) :
    primedIntervalIndex (primedSimInput w) h m = k := by
  let q := primedIntervalIndex (primedSimInput w) h m
  have hq := primedIntervalIndex_spec (primedSimInput w) h m
  have hle : q ≤ k := by
    change Nat.find _ ≤ k
    exact Nat.find_min' _ hr
  have hge : k ≤ q := by
    by_contra hn
    have hb := primedIntervalBase_mono (primedSimInput w) h
      (show q + 1 ≤ k by omega)
    change m < primedIntervalBase (primedSimInput w) h (q + 1) at hq
    omega
  exact Nat.le_antisymm hle hge

/-- P2 helper toward lem-quad-kmsw; not counted
first `m` primed steps. Stage zero uses the initial exit stage; positive
stages use the block containing their last consumed code. -/
@[expose] noncomputable def primedStageTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) : ℕ :=
  if m = 0 then walkNL w h 0 else
    let k := primedIntervalIndex (primedSimInput w) h (m - 1)
    walkNL w h k + (m - primedIntervalBase (primedSimInput w) h k) - 1

/-- P2 helper toward lem-quad-kmsw; not counted
global left exit, before the local replacement triangle. -/
theorem primedStageTime_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    primedStageTime w h 0 = walkNL w h 0 := by
  simp only [primedStageTime, ↓reduceIte]

/-- P2 helper toward lem-quad-kmsw; not counted
final stage, canonical global time agrees with the ordinary-run indices. -/
theorem primedStageTime_block (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k m : ℕ) (hl : primedIntervalBase (primedSimInput w) h k < m)
    (hr : m ≤ primedIntervalBase (primedSimInput w) h (k + 1)) :
    primedStageTime w h m =
      walkNL w h k + (m - primedIntervalBase (primedSimInput w) h k) - 1 := by
  have hm : m ≠ 0 := by omega
  have hi := stageIndex_eq w h k (m - 1) (by omega) (by omega)
  simp only [primedStageTime, hm, ↓reduceIte, hi]

/-- P2 helper toward lem-quad-kmsw; not counted
last kept global stage, exactly as in `primedSimActiveRootLR_at_crossing`. -/
theorem primedStageTime_at_crossing (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) :
    primedStageTime w h (primedIntervalBase (primedSimInput w) h (k + 1)) =
      walkNR w h (k + 1) - 1 := by
  have hw := primedIntervalWidth_pos (primedSimInput w) h k
  have hb := primedIntervalBase_succ (primedSimInput w) h k
  rw [primedStageTime_block w h k _ (by omega) le_rfl, hb]
  have hg := (walkNR_succ_spec w h k).1
  change walkNL w h k +
    (primedIntervalBase (primedSimInput w) h k +
      (walkNR w h (k + 1) - walkNL w h k) -
        primedIntervalBase (primedSimInput w) h k) - 1 = _
  omega

/-- P2 helper toward lem-quad-kmsw; not counted
code jumps across the omitted R-excursion to the next left exit. -/
theorem primedStageTime_after_crossing (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k : ℕ) :
    primedStageTime w h (primedIntervalBase (primedSimInput w) h k + 1) =
      walkNL w h k := by
  have hw := primedIntervalWidth_pos (primedSimInput w) h k
  have hb := primedIntervalBase_succ (primedSimInput w) h k
  rw [primedStageTime_block w h k _ (by omega) (by omega)]
  omega

private theorem stageIndex_bounds (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : 1 ≤ m) :
    let k := primedIntervalIndex (primedSimInput w) h (m - 1)
    primedIntervalBase (primedSimInput w) h k < m ∧
      m ≤ primedIntervalBase (primedSimInput w) h (k + 1) := by
  dsimp only
  have hr := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
  constructor
  · cases hk : primedIntervalIndex (primedSimInput w) h (m - 1) with
    | zero => rw [primedIntervalBase_zero]; omega
    | succ k =>
      have hn := Nat.find_min (primedIntervalIndex_exists (primedSimInput w) h (m - 1))
        (show k < Nat.find (primedIntervalIndex_exists (primedSimInput w) h (m - 1)) by
          change k < primedIntervalIndex (primedSimInput w) h (m - 1)
          omega)
      omega
  · omega

/-- P2 helper toward lem-quad-kmsw; not counted
ordinary primed step, dispatching on its code. -/
@[expose] def primedOrdinaryStepEdgeMap (sh gl : State) (c : Fin 3)
    (eφ : ℕ → ℕ) : ℕ → ℕ :=
  if c = 0 then primedOrdinaryLeftEdgeMap sh gl eφ
  else if c = 1 then kmswShiftUpEdgeMap sh gl eφ else eφ

/-- P2 helper toward lem-quad-kmsw; not counted
ordinary primed step, with the same dispatch as the edge map. -/
@[expose] def primedOrdinaryStepVertexMap (sh gl : State) (c : Fin 3)
    (vφ : ℕ → ℕ) : ℕ → ℕ :=
  if c = 0 then primedOrdinaryLeftVertexMap sh gl vφ
  else if c = 1 then kmswShiftUpVertexMap sh gl vφ else vφ

private theorem ordinary_extend (sh gl : State) (c : Fin 3) (eφ vφ : ℕ → ℕ) :
    (∀ e, e < sh.nextEdge → primedOrdinaryStepEdgeMap sh gl c eφ e = eφ e) ∧
    (∀ v, v < sh.nextVertex → primedOrdinaryStepVertexMap sh gl c vφ v = vφ v) := by
  fin_cases c
  · exact primedLeft_maps_extend sh gl eφ vφ
  · exact primedUp_maps_extend sh gl eφ vφ
  · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

private theorem ordinary_sim
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ)
    (c : Fin 3) (hu : u m = c) (hw : w n = c) :
    PrimedSimActiveRootLR u w h k (m + 1) (n + 1)
      (primedOrdinaryStepEdgeMap (kmswMissingRootStage u m) (kmswStage w n) c eφ)
      (primedOrdinaryStepVertexMap (kmswMissingRootStage u m) (kmswStage w n) c vφ) ∧
    PrimedURUnreachableOrCut u w h k (m + 1)
      (primedOrdinaryStepEdgeMap (kmswMissingRootStage u m) (kmswStage w n) c eφ)
      (primedOrdinaryStepVertexMap (kmswMissingRootStage u m) (kmswStage w n) c vφ) := by
  fin_cases c
  · change PrimedSimActiveRootLR u w h k (m + 1) (n + 1)
        (primedOrdinaryLeftEdgeMap _ _ eφ) (primedOrdinaryLeftVertexMap _ _ vφ) ∧ _
    constructor
    · cases hp : (kmswMissingRootStage u m).UL.dropLast.reverse with
      | nil =>
        simpa only [primedOrdinaryLeftEdgeMap, primedOrdinaryLeftVertexMap, hp,
          ↓reduceIte] using sim.step_left_empty hm hu hw hp
      | cons a as =>
        simpa only [primedOrdinaryLeftEdgeMap, primedOrdinaryLeftVertexMap, hp,
          List.cons_ne_nil, ↓reduceIte] using
            primedSimActiveRootLR_left_nonempty sim hm hu hw hp
    · exact primedURUnreachableOrCut_step_left (n := n) hinv hu
  · exact ⟨sim.step_up hm hu hw, sim.forget.URUnreachableOrCut_step_up hm hinv hu hw⟩
  · exact ⟨sim.step_down hm hu hw, primedURUnreachableOrCut_step_down hinv hu⟩

/-- P2 helper toward lem-quad-kmsw; not counted
per local stage, recursively using the explicit initial, first-triangle,
ordinary-step and replacement-crossing maps. -/
@[expose] noncomputable def primedAllEdgeMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ → ℕ
  | 0 => primedInitialEdgeMap w (walkNL w h 0)
  | m + 1 =>
    if m = 0 then primedFirstStepEdgeMap w (walkNL w h 0) else
      let k := primedIntervalIndex (primedSimInput w) h (m - 1)
      let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) m
      if m < primedIntervalBase (primedSimInput w) h (k + 1) then
        primedOrdinaryStepEdgeMap sh (kmswStage w (primedStageTime w h m))
          (primedCode (primedSimInput w) h m) (primedAllEdgeMap w h m)
      else
        primedCrossingEdgeMap sh (kmswStage w (walkNL w h (k + 1) - 1))
          (primedAllEdgeMap w h m)

/-- P2 helper toward lem-quad-kmsw; not counted
the same recursive branch and stage as `primedAllEdgeMap`. -/
@[expose] noncomputable def primedAllVertexMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ → ℕ
  | 0 => primedInitialVertexMap w (walkNL w h 0)
  | m + 1 =>
    if m = 0 then primedFirstStepVertexMap w (walkNL w h 0) else
      let k := primedIntervalIndex (primedSimInput w) h (m - 1)
      let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) m
      if m < primedIntervalBase (primedSimInput w) h (k + 1) then
        primedOrdinaryStepVertexMap sh (kmswStage w (primedStageTime w h m))
          (primedCode (primedSimInput w) h m) (primedAllVertexMap w h m)
      else
        primedCrossingVertexMap sh (kmswStage w (walkNL w h (k + 1) - 1))
          (primedAllVertexMap w h m)

/-- P2 helper toward lem-quad-kmsw; not counted
initial complement simulation, cut simulation and empty-UR invariant. -/
theorem primedAll_sim_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    PrimedComplementSim (primedCode (primedSimInput w) h) w 0
      (primedStageTime w h 0) (primedAllEdgeMap w h 0) (primedAllVertexMap w h 0) ∧
    PrimedComplementSimCut (primedCode (primedSimInput w) h) w h 0 0
      (primedStageTime w h 0) (primedAllEdgeMap w h 0) (primedAllVertexMap w h 0) ∧
    PrimedURUnreachable (primedCode (primedSimInput w) h) w 0
      (primedAllVertexMap w h 0) := by
  exact ⟨primedInitial_complementSim _ w h, primedInitial_complementSimCut _ w h,
    primedInitial_URUnreachable _ w _⟩

/-- P2 helper toward lem-quad-kmsw; not counted
its predecessor on every previously allocated edge and vertex ID. -/
theorem primedAll_maps_extend (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    (∀ e, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge →
      primedAllEdgeMap w h (m + 1) e = primedAllEdgeMap w h m e) ∧
    (∀ v, v < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex →
      primedAllVertexMap w h (m + 1) v = primedAllVertexMap w h m v) := by
  by_cases hm : m = 0
  · subst m
    exact primedFirstStep_maps_extend _ w h
  · by_cases hb : m < primedIntervalBase (primedSimInput w) h
        (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)
    · simpa only [primedAllEdgeMap, primedAllVertexMap, hm, ↓reduceIte, hb] using
        ordinary_extend (kmswMissingRootStage (primedCode (primedSimInput w) h) m)
          (kmswStage w (primedStageTime w h m)) (primedCode (primedSimInput w) h m)
          (primedAllEdgeMap w h m) (primedAllVertexMap w h m)
    · simpa only [primedAllEdgeMap, primedAllVertexMap, hm, ↓reduceIte, hb] using
        primedCrossing_maps_extend
          (kmswMissingRootStage (primedCode (primedSimInput w) h) m)
          (kmswStage w (walkNL w h
            (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) - 1))
          (primedAllEdgeMap w h m) (primedAllVertexMap w h m)

private theorem all_sim_index (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, 1 ≤ m →
      let k := primedIntervalIndex (primedSimInput w) h (m - 1)
      PrimedSimActiveRootLR (primedCode (primedSimInput w) h) w h k m
        (primedStageTime w h m) (primedAllEdgeMap w h m) (primedAllVertexMap w h m) ∧
      PrimedURUnreachableOrCut (primedCode (primedSimInput w) h) w h k m
        (primedAllEdgeMap w h m) (primedAllVertexMap w h m) := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _
    by_cases hm : m = 0
    · subst m
      have hw := primedIntervalWidth_pos (primedSimInput w) h 0
      have hb := primedIntervalBase_succ (primedSimInput w) h 0
      have hzero := primedIntervalBase_zero (primedSimInput w) h
      have hidx := stageIndex_eq w h 0 0 (by omega) (by omega)
      have ht : primedStageTime w h 1 = walkNL w h 0 := by
        simpa only [hzero, zero_add] using primedStageTime_after_crossing w h 0
      simp only [Nat.add_sub_cancel, hidx, ht]
      have hu := (primedInitial_code_alignment (primedSimInput w) h).1
      exact ⟨primedFirstStep_simActiveRootLR _ w h hu,
        primedFirstStep_URUnreachableOrCut _ w h hu⟩
    · let k := primedIntervalIndex (primedSimInput w) h (m - 1)
      obtain ⟨hl, hr⟩ := stageIndex_bounds w h m (by omega)
      change primedIntervalBase (primedSimInput w) h k < m at hl
      change m ≤ primedIntervalBase (primedSimInput w) h (k + 1) at hr
      obtain ⟨hs, hi⟩ := ih (by omega)
      change PrimedSimActiveRootLR _ w h k m _ _ _ at hs
      change PrimedURUnreachableOrCut _ w h k m _ _ at hi
      by_cases ho : m < primedIntervalBase (primedSimInput w) h (k + 1)
      · have hidx := stageIndex_eq w h k m (by omega) ho
        simp only [Nat.add_sub_cancel, hidx]
        have ho' : m < primedIntervalBase (primedSimInput w) h k +
            primedIntervalWidth (primedSimInput w) h k := by
          rw [← primedIntervalBase_succ]
          exact ho
        have ht0 := primedStageTime_block w h k m hl hr
        have ht1 := primedStageTime_block w h k (m + 1) (by omega) (by omega)
        have ht : primedStageTime w h (m + 1) = primedStageTime w h m + 1 := by
          rw [ht1, ht0]
          omega
        have hc := primedCode_positive_offset (primedSimInput w) h k
          (m - primedIntervalBase (primedSimInput w) h k) (by omega) (by omega)
        have hsum : primedIntervalBase (primedSimInput w) h k +
            (m - primedIntervalBase (primedSimInput w) h k) = m := by omega
        rw [hsum] at hc
        change primedCode (primedSimInput w) h m =
          w (walkNL w h k + (m - primedIntervalBase (primedSimInput w) h k) - 1) at hc
        rw [← ht0] at hc
        have hstep := ordinary_sim hs ho' hi (primedCode (primedSimInput w) h m) rfl hc.symm
        rw [← ht] at hstep
        change m < primedIntervalBase (primedSimInput w) h
          (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) at ho
        simpa only [primedAllEdgeMap, primedAllVertexMap, hm, ↓reduceIte, ho] using hstep
      · have hB : m = primedIntervalBase (primedSimInput w) h (k + 1) := by omega
        have hw := primedIntervalWidth_pos (primedSimInput w) h (k + 1)
        have hb := primedIntervalBase_succ (primedSimInput w) h (k + 1)
        have hidx := stageIndex_eq w h (k + 1) m (by omega) (by omega)
        simp only [Nat.add_sub_cancel, hidx]
        have ht0 : primedStageTime w h m = walkNR w h (k + 1) - 1 := by
          rw [hB]
          exact primedStageTime_at_crossing w h k
        have ht1 : primedStageTime w h (m + 1) = walkNL w h (k + 1) := by
          rw [hB]
          exact primedStageTime_after_crossing w h (k + 1)
        rw [ht0] at hs
        have hu := hs.crossing_primedCode
        have hs' := hs.crossing hi hu
        have hi' := primedURUnreachableOrCut_crossing hi hu
        rw [ht1]
        change ¬ m < primedIntervalBase (primedSimInput w) h
          (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) at ho
        simpa only [primedAllEdgeMap, primedAllVertexMap, hm, ↓reduceIte, ho] using
          And.intro hs' hi'

/-- P2 helper toward lem-quad-kmsw; not counted
stage, the canonical recursive maps carry the active root-LR simulation
and unreachable-or-cut invariant at canonical global time. Stage zero is
handled separately by `primedAll_sim_zero`; ordered planar identification
and the cut-completed object remain separate obligations. -/
theorem primedAll_sim (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, 1 ≤ m → ∃ k,
      PrimedSimActiveRootLR (primedCode (primedSimInput w) h) w h k m
        (primedStageTime w h m) (primedAllEdgeMap w h m) (primedAllVertexMap w h m) ∧
      PrimedURUnreachableOrCut (primedCode (primedSimInput w) h) w h k m
        (primedAllEdgeMap w h m) (primedAllVertexMap w h m) := by
  intro m hm
  exact ⟨primedIntervalIndex (primedSimInput w) h (m - 1), all_sim_index w h m hm⟩

end DirectedDistances.KMSW
