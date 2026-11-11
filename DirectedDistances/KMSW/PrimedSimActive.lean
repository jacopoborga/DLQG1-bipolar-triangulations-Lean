module

public import DirectedDistances.KMSW.PrimedExcursionStep

/-! # Active primed simulation helpers

No identification of the full hatted UL with β₀ is asserted. The local UR
can have an unmatched cut tail; only its common, ordinary-step prefix is
aligned with the global UR. None of these helpers counts as the paper lemma. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- Restore an unused time-zero letter to the global code stream. Partial -/
abbrev primedSimInput (w : ℕ → Fin 3) : ℕ → Fin 3
  | 0 => 0
  | i + 1 => w i

/-- Partial active simulation after the replacement triangle in block `k`.
The inherited boundary clause quantifies only over local boundary edges.
`after_base` excludes the pre-crossing stage, to which this time formula does
not apply. UL equality aligns the left-step control stack. The common UR
prefix has length equal to the vertical displacement since this block's exit;
its tails need not agree, since the local tail can consist of cut edges.
These are induction data, not a proof of `lem-quad-kmsw` -/
structure PrimedSimActive (u w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k m n : ℕ) (eφ vφ : ℕ → ℕ) : Prop
    extends PrimedComplementSimCut u w h k m n eφ vφ where
  after_base : primedIntervalBase (primedSimInput w) h k < m
  time_alignment : n = primedIntervalLeft (primedSimInput w) h k +
    (m - primedIntervalBase (primedSimInput w) h k) - 1
  active_alignment : eφ (kmswMissingRootStage u m).active = (kmswStage w n).active
  UL_alignment : (kmswMissingRootStage u m).UL.map eφ = (kmswStage w n).UL
  UR_alignment : ∃ xs ys zs : List ℕ,
    (kmswMissingRootStage u m).UR = xs ++ ys ∧
    (kmswStage w n).UR = xs.map eφ ++ zs ∧
    (xs.length : ℤ) = R w n - R w (walkNL w h k) ∧
    ∀ e ∈ xs,
      (kmswStage w n).west (eφ e) = vφ ((kmswMissingRootStage u m).west e) ∧
      (kmswStage w n).east (eφ e) = vφ ((kmswMissingRootStage u m).east e)

/-- Forget active and stack alignment, retaining precisely the old partial
cut clauses. Partial helper for `lem-quad-kmsw` -/
theorem PrimedSimActive.toCut {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) :
    PrimedComplementSimCut u w h k m n eφ vφ := sim.toPrimedComplementSimCut

/-- The inherited boundary clause in its surviving-local-frontier form. -/
theorem PrimedSimActive.frontier_image {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) (e : ℕ)
    (he : e ∈ primedGlobalFrontier (kmswMissingRootStage u m)) :
    eφ e ∈ primedGlobalFrontier (kmswStage w n) ∨ eφ e ∈ cutAtExit w h k := by
  apply sim.boundary_image e
  simpa only [primedGlobalFrontier, List.mem_append, or_assoc] using he

/-- First replacement triangle, with the C18 missing root and coherent active
and control-stack images. The first-code case hypothesis is discharged when
instantiating `u` by `primedCode`. Partial helper, not `lem-quad-kmsw` -/
theorem primedFirstStep_simActive (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu : u 0 = 1) :
    PrimedSimActive u w h 0 1 (walkNL w h 0)
      (primedFirstStepEdgeMap w (walkNL w h 0))
      (primedFirstStepVertexMap w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hstep : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  refine { toPrimedComplementSimCut := primedFirstStep_complementSimCut u w h hu
           after_base := ?_, time_alignment := ?_, active_alignment := ?_,
           UL_alignment := ?_, UR_alignment := ?_ }
  · rw [primedIntervalBase_zero]; omega
  · simp only [primedIntervalBase_zero, primedIntervalLeft]
    change n = n + (1 - 0) - 1
    omega
  · change primedFirstStepEdgeMap w n (kmswMissingRootStage u 1).active =
      (kmswStage w n).active
    rw [hstep]
    simp [kmswMissingRootStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit, primedFirstStepEdgeMap, hdrop, State.addEdge]
    rfl
  · change (kmswMissingRootStage u 1).UL.map (primedFirstStepEdgeMap w n) =
      (kmswStage w n).UL
    rw [hstep]
    simp [kmswMissingRootStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit, primedFirstStepEdgeMap, hdrop, State.addEdge]
    rfl
  · exact ⟨[], _, _, rfl, rfl, by simp, by simp⟩

/-- Second triangle in the up case, including active and stack images. -/
theorem primedSecondUp_simActive (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu0 : u 0 = 1) (hu1 : u 1 = 1)
    (hw : w (walkNL w h 0) = 1) :
    PrimedSimActive u w h 0 2 (walkNL w h 0 + 1)
      (primedSecondTriangleEdgeMap u w (walkNL w h 0))
      (primedSecondTriangleVertexMap u w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w n
  have hl : kmswMissingRootStage u 2 =
      kmswStepOfStep (kmswStepOfStep kmswMissingRootInit .up) .up := by
    simp only [kmswMissingRootStage, hu0, hu1]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep s .up := by
    change kmswStep s (w n) = _
    rw [hw]; rfl
  have hs := primedFirstStep_simActive u w h hu0
  have hul : (kmswMissingRootStage u 1).UL.map (primedFirstStepEdgeMap w n) = s.UL :=
    hs.UL_alignment
  have ha : primedFirstStepEdgeMap w n 1 = s.active := by
    simpa [kmswMissingRootStage, hu0, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit] using hs.active_alignment
  have heast : s.east s.active = primedFirstStepVertexMap w n 2 := by
    have hp := hs.present_incidence 1 (by
      simp [kmswMissingRootStage, hu0, kmswStep, kmswCodeStep, kmswStepOfStep,
        kmswMissingRootInit, kmswInit, State.addEdge]) (by
      simp [kmswMissingRootStage, hu0, kmswStep, kmswCodeStep, kmswStepOfStep,
        kmswMissingRootInit, kmswInit, State.addEdge])
    have hp2 := hp.2
    change s.east (primedFirstStepEdgeMap w n 1) = _ at hp2
    simpa [ha, kmswMissingRootStage, hu0, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge] using hp2
  have hsul : s.UL = [s.active] := by
    simpa [kmswMissingRootStage, hu0, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit, ha] using hul.symm
  change PrimedSimActive u w h 0 2 (n + 1) _ _
  refine { toPrimedComplementSimCut := primedSecondUp_complementSimCut u w h hu0 hu1 hw
           after_base := ?_, time_alignment := ?_, active_alignment := ?_,
           UL_alignment := ?_, UR_alignment := ?_ }
  · rw [primedIntervalBase_zero]; omega
  · simp only [primedIntervalBase_zero, primedIntervalLeft]
    change n + 1 = n + (2 - 0) - 1
    omega
  · rw [hl, hg]
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, s, n]
  · rw [hl, hg]
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hsul, s, n]
  · refine ⟨[4], [2], s.UR, ?_, ?_, ?_, ?_⟩
    · rw [hl]; rfl
    · rw [hg]
      simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
        hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
        kmswInit, State.addEdge, s, n]
    · have hr : R w (n + 1) = R w n + 1 := by
        simp [R, Finset.sum_range_succ, show w n = 1 from hw, lazyTwoDimensionalStep]
      simp only [List.length_cons, List.length_nil]
      change (1 : ℤ) = R w (n + 1) - R w n
      omega
    · intro e he
      have he4 : e = 4 := by simpa using he
      subst e
      rw [hl, hg]
      simp [primedSecondTriangleEdgeMap, primedSecondTriangleVertexMap,
        kmswShiftUpEdgeMap, kmswShiftUpVertexMap, kmswMissingRootStage,
        hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
        kmswInit, State.addEdge, s, n]
      exact heast

/-- Second triangle in the left case. The unmatched UR tail is retained. -/
theorem primedSecondLeft_simActive (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu0 : u 0 = 1) (hu1 : u 1 = 0)
    (hw : w (walkNL w h 0) = 0) :
    PrimedSimActive u w h 0 2 (walkNL w h 0 + 1)
      (primedSecondTriangleEdgeMap u w (walkNL w h 0))
      (primedSecondTriangleVertexMap u w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w n
  have hl : kmswMissingRootStage u 2 =
      kmswStepOfStep (kmswStepOfStep kmswMissingRootInit .up) .left := by
    simp only [kmswMissingRootStage, hu0, hu1]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep s .left := by
    change kmswStep s (w n) = _
    rw [hw]; rfl
  have hs := primedFirstStep_simActive u w h hu0
  have ha : primedFirstStepEdgeMap w n 1 = s.active := by
    simpa [kmswMissingRootStage, hu0, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit] using hs.active_alignment
  have hul : (kmswMissingRootStage u 1).UL.map (primedFirstStepEdgeMap w n) = s.UL :=
    hs.UL_alignment
  have hsul : s.UL = [s.active] := by
    simpa [kmswMissingRootStage, hu0, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit, ha] using hul.symm
  change PrimedSimActive u w h 0 2 (n + 1) _ _
  refine { toPrimedComplementSimCut := primedSecondLeft_complementSimCut u w h hu0 hu1 hw
           after_base := ?_, time_alignment := ?_, active_alignment := ?_,
           UL_alignment := ?_, UR_alignment := ?_ }
  · rw [primedIntervalBase_zero]; omega
  · simp only [primedIntervalBase_zero, primedIntervalLeft]
    change n + 1 = n + (2 - 0) - 1
    omega
  · rw [hl, hg]
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hsul, s, n]
  · rw [hl, hg]
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, hsul, s, n]
  · refine ⟨[], _, _, rfl, rfl, ?_, by simp⟩
    have hr : R w (n + 1) = R w n := by
      simp [R, Finset.sum_range_succ, show w n = 0 from hw, lazyTwoDimensionalStep]
    change (0 : ℤ) = R w (n + 1) - R w n
    omega

/-- The up-then-down finite prefix activates the aligned missing side and
retains the unmatched cut tail. Partial helper, not `lem-quad-kmsw` -/
theorem primedThirdDown_simActive (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu0 : u 0 = 1) (hu1 : u 1 = 1) (hu2 : u 2 = 2)
    (hw0 : w (walkNL w h 0) = 1) (hw1 : w (walkNL w h 0 + 1) = 2) :
    PrimedSimActive u w h 0 3 (walkNL w h 0 + 2)
      (primedSecondTriangleEdgeMap u w (walkNL w h 0))
      (primedSecondTriangleVertexMap u w (walkNL w h 0)) := by
  let n := walkNL w h 0
  let s := kmswStage w n
  have hl : kmswMissingRootStage u 3 =
      kmswStepOfStep (kmswStepOfStep (kmswStepOfStep kmswMissingRootInit .up) .up) .down := by
    simp only [kmswMissingRootStage, hu0, hu1, hu2]; rfl
  have hg : kmswStage w (n + 2) =
      kmswStepOfStep (kmswStepOfStep s .up) .down := by
    change kmswStep (kmswStep s (w n)) (w (n + 1)) = _
    rw [hw0, hw1]; rfl
  have hs := primedSecondUp_simActive u w h hu0 hu1 hw0
  have hul : (kmswMissingRootStage u 2).UL.map
      (primedSecondTriangleEdgeMap u w n) = (kmswStepOfStep s .up).UL := by
    have hh := hs.UL_alignment
    change _ = (kmswStep s (w n)).UL at hh
    simpa [show w n = 1 from hw0, kmswStep, kmswCodeStep] using hh
  change PrimedSimActive u w h 0 3 (n + 2) _ _
  refine { toPrimedComplementSimCut := primedThirdDown_complementSimCut u w h hu0 hu1 hu2 hw0 hw1
           after_base := ?_, time_alignment := ?_, active_alignment := ?_,
           UL_alignment := ?_, UR_alignment := ?_ }
  · rw [primedIntervalBase_zero]; omega
  · simp only [primedIntervalBase_zero, primedIntervalLeft]
    change n + 2 = n + (3 - 0) - 1
    omega
  · rw [hl, hg]
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, s, n]
  · rw [hl, hg]
    have huL : s.UL.dropLast = [] := by
      have hh := hul
      simp [kmswMissingRootStage, hu0, hu1, kmswStep, kmswCodeStep,
        kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge,
        primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, s, n] at hh
      exact hh
    simp [primedSecondTriangleEdgeMap, kmswShiftUpEdgeMap, kmswMissingRootStage,
      hu0, kmswStep, kmswCodeStep, kmswStepOfStep, kmswMissingRootInit,
      kmswInit, State.addEdge, huL, s, n]
  · refine ⟨[], _, _, rfl, rfl, ?_, by simp⟩
    have hr1 : R w (n + 1) = R w n + 1 := by
      simp [R, Finset.sum_range_succ, show w n = 1 from hw0, lazyTwoDimensionalStep]
    have hr2 : R w (n + 2) = R w (n + 1) - 1 := by
      change R w ((n + 1) + 1) = _
      simp [R, Finset.sum_range_succ, show w (n + 1) = 2 from hw1,
        lazyTwoDimensionalStep, sub_eq_add_neg]
    change (0 : ℤ) = R w (n + 2) - R w n
    omega

/-- An ordinary down step has aligned nonempty UR heads, with ordered
incidence. An empty common prefix would make this the compressed crossing,
which the strict block bound excludes. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.down_heads {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k) (hw : w n = 2) :
    ∃ a as bs,
      (kmswMissingRootStage u m).UR = a :: as ∧
      (kmswStage w n).UR = eφ a :: bs ∧
      (kmswStage w n).west (eφ a) = vφ ((kmswMissingRootStage u m).west a) ∧
      (kmswStage w n).east (eφ a) = vφ ((kmswMissingRootStage u m).east a) := by
  have ha := sim.after_base
  have ht := sim.time_alignment
  change n = walkNL w h k +
    (m - primedIntervalBase (primedSimInput w) h k) - 1 at ht
  have hgap := (walkNR_succ_spec w h k).1
  change m < primedIntervalBase (primedSimInput w) h k +
    (walkNR w h (k + 1) - walkNL w h k) at hm
  have hle : walkNL w h k ≤ n := by omega
  have hlt : n + 1 < walkNR w h (k + 1) := by omega
  obtain ⟨xs, ys, zs, hl, hg, hlen, hi⟩ := sim.UR_alignment
  cases xs with
  | nil =>
      have hr : R w (n + 1) = R w n - 1 := by
        simp [R, Finset.sum_range_succ, hw, lazyTwoDimensionalStep, sub_eq_add_neg]
      have hlevel : R w (n + 1) = R w (walkNL w h k) - 1 := by
        simp only [List.length_nil, Nat.cast_zero] at hlen
        omega
      have hhit : walkNR w h (k + 1) ≤ n + 1 := by
        change firstFlowRHit w h (walkNL w h k) ≤ n + 1
        unfold firstFlowRHit
        exact Nat.find_min' _ ⟨by omega, hlevel⟩
      omega
  | cons a xs =>
      refine ⟨a, xs ++ ys, xs.map eφ ++ zs, ?_, ?_, hi a (by simp)⟩
      · simpa only [List.cons_append] using hl
      · simpa only [List.map_cons, List.cons_append] using hg

/-- Boundary images surviving an ordinary down step retain their frontier-or-cut
membership. Both heads are aligned by `down_heads`; this branch allocates no
IDs, so the maps are unchanged. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.down_boundary_image {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 2) (hw : w n = 2) :
    ∀ e, e ∈ primedGlobalFrontier (kmswMissingRootStage u (m + 1)) →
      eφ e ∈ primedGlobalFrontier (kmswStage w (n + 1)) ∨
      eφ e ∈ cutAtExit w h k := by
  obtain ⟨a, as, bs, hlocal, hglobal, _⟩ := sim.down_heads hm hw
  have hl : kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) .down := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep (kmswStage w n) .down := by
    simp only [kmswStage, hw]; rfl
  intro e he
  have hold : e ∈ primedGlobalFrontier (kmswMissingRootStage u m) := by
    simp only [hl, primedGlobalFrontier, kmswStepOfStep, hlocal,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    rcases he with (he | he) | he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl (Or.inl he))
    · exact Or.inr (Or.inl (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr he))
  rcases sim.frontier_image e hold with hf | hc
  · left
    rw [hg]
    exact primedGlobalFrontier_down_mono _ _ hf
  · exact Or.inr hc

/-- Both incidence clauses survive an ordinary down step. The activated
common-prefix head uses ordered incidence; every other edge retains its old
incidence. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.down_incidence {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 2) (hw : w n = 2) :
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = true →
      (kmswStage w (n + 1)).west (eφ e) =
        vφ ((kmswMissingRootStage u (m + 1)).west e) ∧
      (kmswStage w (n + 1)).east (eφ e) =
        vφ ((kmswMissingRootStage u (m + 1)).east e)) ∧
    (∀ e, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      (kmswMissingRootStage u (m + 1)).present e = false →
      ({(kmswStage w (n + 1)).west (eφ e),
        (kmswStage w (n + 1)).east (eφ e)} : Multiset ℕ) =
        {vφ ((kmswMissingRootStage u (m + 1)).west e),
          vφ ((kmswMissingRootStage u (m + 1)).east e)}) := by
  obtain ⟨a, as, bs, hlocal, hglobal, hi⟩ := sim.down_heads hm hw
  have hl : kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) .down := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep (kmswStage w n) .down := by
    simp only [kmswStage, hw]; rfl
  constructor
  · intro e he hp
    simp only [hl, hg, kmswStepOfStep, hlocal, hglobal] at he hp ⊢
    by_cases hea : e = a
    · subst e; exact hi
    · have hold : (kmswMissingRootStage u m).present e = true := by
        simpa only [ite_eq_right hea] using hp
      exact sim.present_incidence e he hold
  · intro e he hp
    simp only [hl, hg, kmswStepOfStep, hlocal, hglobal] at he hp ⊢
    by_cases hea : e = a
    · subst e; simp at hp
    · have hold : (kmswMissingRootStage u m).present e = false := by
        simpa only [ite_eq_right hea] using hp
      exact sim.missing_incidence e he hold

/-- All the weaker cut clauses survive an ordinary down step, with the
identity extension of both allocation maps. Partial helper, not -/
theorem PrimedSimActive.down_toCut {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 2) (hw : w n = 2) :
    PrimedComplementSimCut u w h k (m + 1) (n + 1) eφ vφ := by
  obtain ⟨a, as, bs, hlocal, hglobal, _⟩ := sim.down_heads hm hw
  have hl : kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) .down := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep (kmswStage w n) .down := by
    simp only [kmswStage, hw]; rfl
  have ha := sim.after_base
  have ht := sim.time_alignment
  change n = walkNL w h k +
    (m - primedIntervalBase (primedSimInput w) h k) - 1 at ht
  have hgap := (walkNR_succ_spec w h k).1
  change m < primedIntervalBase (primedSimInput w) h k +
    (walkNR w h (k + 1) - walkNL w h k) at hm
  have hle : walkNL w h k ≤ n := by omega
  have hlt : n + 1 < walkNR w h (k + 1) := by omega
  have hreach := lPhase_reachablePresentEdges_succ_eq w h k n hle hlt
  have hnot : eφ a ∉ stageReachablePresentEdges w (n + 1) := by
    have hun := lPhase_activeWest_unreachable w h k (n + 1) (by omega) hlt
    have hactive : act w (n + 1) = eφ a := by
      simp only [act, hg, kmswStepOfStep, hglobal]
    rw [hactive] at hun
    intro he
    exact hun he.2.2.1
  have hroot : eφ 0 ≠ eφ a := by
    intro heq
    have hur : eφ 0 ∈ (kmswStage w n).UR := by rw [heq, hglobal]; simp
    exact (kmswStage_status w n).2.2.2.2.2 _ hur sim.missing_root.2.2
  have hi := sim.down_incidence hm hu hw
  refine {
    edge_bound := ?_
    edge_injective := ?_
    vertex_bound := ?_
    vertex_injective := ?_
    present_incidence := hi.1
    missing_incidence := hi.2
    present_complement := ?_
    missing_root := ?_
    triangle_incidence := ?_
    boundary_image := ?_ }
  · simpa only [hl, hg, kmswStepOfStep, hlocal, hglobal] using sim.edge_bound
  · simpa only [hl, kmswStepOfStep, hlocal] using sim.edge_injective
  · simpa only [hl, hg, kmswStepOfStep, hlocal, hglobal] using sim.vertex_bound
  · simpa only [hl, kmswStepOfStep, hlocal] using sim.vertex_injective
  · intro e he hp
    simp only [hl, hg, kmswStepOfStep, hlocal, hglobal] at he hp ⊢
    by_cases hea : e = a
    · subst e; exact ⟨by simp, hnot⟩
    · have hold : (kmswMissingRootStage u m).present e = true := by
        simpa only [ite_eq_right hea] using hp
      have hh := sim.present_complement e he hold
      refine ⟨?_, ?_⟩
      · split <;> simp_all only
      · rw [hreach]; exact hh.2
  · refine ⟨kmswMissingRootStage_present_zero u (m + 1), ?_, ?_⟩
    · simpa only [hg, kmswStepOfStep, hglobal, ite_eq_right hroot] using sim.missing_root.2.1
    · simpa only [hg, kmswStepOfStep, hglobal] using sim.missing_root.2.2
  · simpa only [hl, hg, kmswStepOfStep, hlocal, hglobal] using sim.triangle_incidence
  · intro e he
    apply sim.down_boundary_image hm hu hw e
    simpa only [primedGlobalFrontier, List.mem_append, or_assoc] using he

/-- One ordinary down step preserves the active invariant without allocating
any ID: the explicit extension maps are `eφ` and `vφ` themselves. -/
theorem PrimedSimActive.step_down {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 2) (hw : w n = 2) :
    PrimedSimActive u w h k (m + 1) (n + 1) eφ vφ := by
  have ha := sim.after_base
  have ht := sim.time_alignment
  have hl : kmswMissingRootStage u (m + 1) =
      kmswStepOfStep (kmswMissingRootStage u m) .down := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hg : kmswStage w (n + 1) = kmswStepOfStep (kmswStage w n) .down := by
    simp only [kmswStage, hw]; rfl
  have hr : R w (n + 1) = R w n - 1 := by
    simp [R, Finset.sum_range_succ, hw, lazyTwoDimensionalStep, sub_eq_add_neg]
  obtain ⟨xs, ys, zs, hxs, hgs, hlen, hi⟩ := sim.UR_alignment
  have hne : xs ≠ [] := by
    intro hempty
    subst xs
    simp only [List.length_nil, Nat.cast_zero] at hlen
    change n = walkNL w h k +
      (m - primedIntervalBase (primedSimInput w) h k) - 1 at ht
    have hgap := (walkNR_succ_spec w h k).1
    change m < primedIntervalBase (primedSimInput w) h k +
      (walkNR w h (k + 1) - walkNL w h k) at hm
    have hhit : walkNR w h (k + 1) ≤ n + 1 := by
      change firstFlowRHit w h (walkNL w h k) ≤ n + 1
      unfold firstFlowRHit
      exact Nat.find_min' _ ⟨by omega, by omega⟩
    omega
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a xs =>
    have hlocal : (kmswMissingRootStage u m).UR = a :: (xs ++ ys) := by
      simpa only [List.cons_append] using hxs
    have hglobal : (kmswStage w n).UR = eφ a :: (xs.map eφ ++ zs) := by
      simpa only [List.map_cons, List.cons_append] using hgs
    refine {
      toPrimedComplementSimCut := sim.down_toCut hm hu hw
      after_base := by omega
      time_alignment := by omega
      active_alignment := ?_
      UL_alignment := ?_
      UR_alignment := ?_ }
    · simp only [hl, hg, kmswStepOfStep, hlocal, hglobal]
    · simpa only [hl, hg, kmswStepOfStep, hlocal, hglobal, List.map_append,
        List.map_cons, List.map_nil] using
        congrArg (fun es => es ++ [eφ a]) sim.UL_alignment
    · refine ⟨xs, ys, zs, ?_, ?_, ?_, ?_⟩
      · simp only [hl, kmswStepOfStep, hlocal]
      · simp only [hg, kmswStepOfStep, hglobal]
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen
        omega
      · intro e he
        simpa only [hl, hg, kmswStepOfStep, hlocal, hglobal] using
          hi e (List.mem_cons_of_mem a he)

/-- Extension-form ordinary down transition, with explicit witnesses equal
to the old maps. Partial helper, not `lem-quad-kmsw` -/
theorem PrimedSimActive.step_down_extends {u w : ℕ → Fin 3} {h : HasFlowLineHits w}
    {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hu : u m = 2) (hw : w n = 2) :
    ∃ eφ' vφ',
      (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
      (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
      PrimedSimActive u w h k (m + 1) (n + 1) eφ' vφ' := by
  exact ⟨eφ, vφ, fun _ _ => rfl, fun _ _ => rfl, sim.step_down hm hu hw⟩

/- The ordinary up and left goals, for `c = 1` and `c = 0` respectively, are:

```
(sim : PrimedSimActive u w h k m n eφ vφ)
(hm : m < primedIntervalBase (primedSimInput w) h k +
  primedIntervalWidth (primedSimInput w) h k)
(hu : u m = c) (hw : w n = c)
⊢ ∃ eφ' vφ',
    (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
    (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
    PrimedSimActive u w h k (m+1) (n+1) eφ' vφ'
```

For up, the intended witnesses are `kmswShiftUpEdgeMap` and
`kmswShiftUpVertexMap` on the current local/global states. For left with
nonempty UL predecessors, only the new active edge is allocated; with empty
predecessors both sides allocate the active edge, missing LL side, and vertex.
The remaining work includes the allocation injections, incidence, complement,
root, triangle, surviving-boundary, and common-prefix clauses for these cases.
The finite second-up/second-left instances above do not discharge these goals.

For the compressed crossing let `u = primedCode ω h`, `w i = ω (i+1)`,
`m = primedIntervalBase ω h (k+1)`, `n = walkNR w h (k+1)-1`, and
`PrimedSimActive u w h k m n eφ vφ` to
`PrimedSimActive u w h (k+1) (m+1) n' eφ' vφ'`.
For `E = (kmswMissingRootStage u m).nextEdge`,
`V = (kmswMissingRootStage u m).nextVertex`, and
`s = kmswStage w (n'-1)`, the required new images are
`eφ' E = s.nextEdge`, `eφ' (E+1) = s.active`,
`vφ' V = s.east s.active`, together with agreement on all old allocated IDs.
The change of cut, surviving boundary images through the omitted excursion,
identification is assumed. None of these remaining goals is a Lean declaration. -/

end DirectedDistances.KMSW
