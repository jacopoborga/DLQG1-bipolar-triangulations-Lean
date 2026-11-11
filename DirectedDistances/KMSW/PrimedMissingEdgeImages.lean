module

public import DirectedDistances.KMSW.PrimedLimitDartIdentification
public import DirectedDistances.KMSW.PrimedMissingEdgeCoverage
import DirectedDistances.KMSW.SDPIdentifyBdy

public section
namespace DirectedDistances.KMSW

private theorem intervalIndex_at_predecessor (w : ℕ → Fin 3)
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

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Each C13 replacement creates a local geometric side whose limit image is
exactly the old active edge at that left exit. -/
theorem primedLimitEdgeMap_left_exit_preimage (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    ∃ a, primedLimitEdgeMap w h a = act w (walkNL w h k - 1) := by
  let u := primedCode (primedSimInput w) h
  cases k with
  | zero =>
    refine ⟨2, ?_⟩
    have hc : u 0 = 1 := primedCode_zero (primedSimInput w) h
    have ha : 2 < (kmswMissingRootStage u 1).nextEdge := by
      simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
        kmswMissingRootInit, kmswInit, State.addEdge]
    rw [(primedLimit_maps_eq_of_allocated w h 1).1 2 ha]
    simp only [primedAllEdgeMap, primedFirstStepEdgeMap, ↓reduceIte]
    rfl
  | succ k =>
    let m := primedIntervalBase (primedSimInput w) h (k + 1)
    let sh := kmswMissingRootStage u m
    have hm : m ≠ 0 := by
      have hb := primedIntervalBase_ge (primedSimInput w) h (k + 1)
      dsimp [m]
      omega
    have hi : primedIntervalIndex (primedSimInput w) h (m - 1) = k :=
      intervalIndex_at_predecessor w h k
    have hc : u m = 1 := (primedCrossing_codes w h k).1
    have ha : sh.nextEdge + 1 < (kmswMissingRootStage u (m + 1)).nextEdge := by
      simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
        State.addEdge, sh]
    refine ⟨sh.nextEdge + 1, ?_⟩
    rw [(primedLimit_maps_eq_of_allocated w h (m + 1)).1 _ ha]
    have ho : ¬ m < primedIntervalBase (primedSimInput w) h (k + 1) :=
      lt_irrefl m
    simp only [primedAllEdgeMap, hm, ↓reduceIte, hi, ho]
    change primedCrossingEdgeMap sh _ _ (sh.nextEdge + 1) = _
    simp only [primedCrossingEdgeMap, Nat.add_one_ne_self, ↓reduceIte]
    rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every beta-zero boundary edge is recreated as a primed geometric side. -/
theorem primedBeta0MissingEdgeImage (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (h : HasFlowLineHits w) : primedBeta0MissingEdgeImageGoal w hfin hb h := by
  intro e he
  obtain ⟨k, hk⟩ := beta0_westBoundary_eq_left_exit w hfin hb h e he
  rw [PaperProofs.Section5.sourceFlowNL_eq_walkNL] at hk
  rw [hk]
  exact primedLimitEdgeMap_left_exit_preimage w h k

private theorem image_block_bounds (w : ℕ → Fin 3) (h : HasFlowLineHits w)
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

private theorem image_ordinary_alignment (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)) :
    primedStageTime w h (m + 1) = primedStageTime w h m + 1 ∧
      primedCode (primedSimInput w) h m = w (primedStageTime w h m) := by
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  obtain ⟨hl, hr⟩ := image_block_bounds w h m hm
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

private theorem missing_new_ordinary_image (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (e : ℕ)
    (he : e < (kmswMissingRootStage (primedCode (primedSimInput w) h) (m + 1)).nextEdge)
    (hnew : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge ≤ e)
    (hp : ¬ PrimedEdgePresent w h e) :
    primeGeomEdge w hfin hb (primedLimitEdgeMap w h e) := by
  let u := primedCode (primedSimInput w) h
  let sh := kmswMissingRootStage u m
  let n := primedStageTime w h m
  let gl := kmswStage w n
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  obtain ⟨_, hc⟩ := image_ordinary_alignment w h m hm ho
  obtain ⟨hl, hr⟩ := image_block_bounds w h m hm
  have ht0 := primedStageTime_block w h k m hl hr
  change e < (kmswMissingRootStage u (m + 1)).nextEdge at he
  change sh.nextEdge ≤ e at hnew
  change primedIntervalBase (primedSimInput w) h k < m at hl
  change m ≤ primedIntervalBase (primedSimInput w) h (k + 1) at hr
  change u m = w n at hc
  have hwidth := primedIntervalBase_succ (primedSimInput w) h k
  have hN : walkNL w h k ≤ n := by change n = _ at ht0; omega
  have hR : n + 1 < walkNR w h (k + 1) := by
    change m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
    change primedIntervalBase (primedSimInput w) h (k + 1) =
      primedIntervalBase (primedSimInput w) h k +
        (walkNR w h (k + 1) - walkNL w h k) at hwidth
    change n = _ at ht0
    omega
  have hfalse : (kmswMissingRootStage u (m + 1)).present e = false := by
    cases hh : (kmswMissingRootStage u (m + 1)).present e with
    | false => rfl
    | true => exact (hp ⟨m + 1, he, hh⟩).elim
  have hmap := (primedLimit_maps_eq_of_allocated w h (m + 1)).1 e he
  have hlocal : kmswMissingRootStage u (m + 1) = kmswStep sh (u m) := rfl
  have hglobal : kmswStage w (n + 1) = kmswStep gl (u m) := by
    change kmswStep gl (w n) = _
    rw [← hc]
  obtain ⟨j, hs, _⟩ := primedAll_sim w h m (by omega)
  generalize hcode : u m = c at hlocal hglobal
  fin_cases c
  · change kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left at hlocal
    change kmswStage w (n + 1) = kmswStepOfStep gl .left at hglobal
    cases hpred : sh.UL.dropLast.reverse with
    | nil =>
      have hgp : gl.UL.dropLast.reverse = [] := by
        have hh := hs.forget.left_predecessors
        change sh.UL.dropLast.reverse.map _ = gl.UL.dropLast.reverse at hh
        rw [hpred, List.map_nil] at hh
        exact hh.symm
      have heq : e = sh.nextEdge + 1 := by
        simp only [hlocal, kmswStepOfStep, hpred,
          State.addEdge] at he hfalse
        by_contra hne
        have he0 : e = sh.nextEdge := by omega
        subst e
        simp at hfalse
      subst e
      have hE : primedLimitEdgeMap w h (sh.nextEdge + 1) = gl.nextEdge + 1 := by
        rw [hmap]
        simp only [primedAllEdgeMap, hm, ↓reduceIte, ho]
        change primedOrdinaryStepEdgeMap sh gl (u m) _ (sh.nextEdge + 1) = _
        rw [hcode]
        change primedOrdinaryLeftEdgeMap sh gl _ (sh.nextEdge + 1) = _
        rw [primedOrdinaryLeftEdgeMap, ite_eq_left hpred]
        simp only [kmswShiftUpEdgeMap, Nat.add_one_ne_self, ↓reduceIte]
      have ha : gl.nextEdge + 1 < (kmswStage w (n + 1)).nextEdge := by
        simp [hglobal, kmswStepOfStep, hgp, State.addEdge]
      have hwest : edgeWest w (gl.nextEdge + 1) =
          (kmswStage w (n + 1)).west (act w (n + 1)) := by
        rw [← (edge_endpoints_eq w ha).1]
        simp [act, hglobal, kmswStepOfStep, hgp,
          State.addEdge]
      rw [hE]
      exact Or.inl (fun hg => lPhase_activeWest_unreachable w h k (n + 1)
        (by omega) hR (hwest ▸ hg.1))
    | cons a as =>
      simp only [hlocal, kmswStepOfStep, hpred,
        State.addEdge] at he hfalse
      by_contra hne
      have he0 : e = sh.nextEdge := by omega
      subst e
      simp at hfalse
  · change kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up at hlocal
    change kmswStage w (n + 1) = kmswStepOfStep gl .up at hglobal
    have heq : e = sh.nextEdge + 1 := by
      simp only [hlocal, kmswStepOfStep, State.addEdge]
        at he hfalse
      by_contra hne
      have he0 : e = sh.nextEdge := by omega
      subst e
      simp at hfalse
    subst e
    have hE : primedLimitEdgeMap w h (sh.nextEdge + 1) = gl.nextEdge + 1 := by
      rw [hmap]
      simp only [primedAllEdgeMap, hm, ↓reduceIte, ho]
      change primedOrdinaryStepEdgeMap sh gl (u m) _ (sh.nextEdge + 1) = _
      rw [hcode]
      change kmswShiftUpEdgeMap sh gl _ (sh.nextEdge + 1) = _
      simp only [kmswShiftUpEdgeMap, Nat.add_one_ne_self, ↓reduceIte]
    have ha : gl.nextEdge + 1 < (kmswStage w (n + 1)).nextEdge := by
      simp [hglobal, kmswStepOfStep, State.addEdge]
    have hwest : edgeWest w (gl.nextEdge + 1) = gl.nextVertex := by
      rw [← (edge_endpoints_eq w ha).1]
      simp [hglobal, kmswStepOfStep, State.addEdge]
    rw [hE]
    exact Or.inl (fun hg => lPhase_up_fresh_vertex_unreachable w h k n hN hR
      (hc.symm.trans hcode) (hwest ▸ hg.1))
  · change kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .down at hlocal
    cases hUR : sh.UR with
    | nil =>
      simp only [hlocal, kmswStepOfStep, hUR,
        State.addEdge] at he hfalse
      have he0 : e = sh.nextEdge := by omega
      subst e
      simp at hfalse
    | cons a as =>
      simp only [hlocal, kmswStepOfStep, hUR] at he
      omega

private theorem left_exit_primeGeom (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (k : ℕ) :
    primeGeomEdge w hfin hb (act w (walkNL w h k - 1)) := by
  apply Or.inr
  apply (primeBetaEdge_iff_MhatWestBoundaryEdge w hfin hb _).mpr
  have he := mhatWestBoundaryEdge_leftExit w h (k + 1) (by omega)
  simpa only [Nat.add_sub_cancel, PaperProofs.Section5.sourceFlowNL_eq_walkNL] using he

private theorem missing_allocated_image (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    ∀ m e, e < (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge →
      ¬ PrimedEdgePresent w h e →
      primeGeomEdge w hfin hb (primedLimitEdgeMap w h e) := by
  let u := primedCode (primedSimInput w) h
  intro m
  induction m with
  | zero =>
    intro e he _
    have he0 : e = 0 := by change e < 1 at he; omega
    subst e
    exact (primedLimitRoot_primeMissingEdge w h hfin hb).1
  | succ m ih =>
    intro e he hp
    by_cases hold : e < (kmswMissingRootStage u m).nextEdge
    · exact ih e hold hp
    have hnew : (kmswMissingRootStage u m).nextEdge ≤ e := by omega
    by_cases hm : m = 0
    · subst m
      have hc : u 0 = 1 := primedCode_zero (primedSimInput w) h
      change e < (kmswMissingRootStage u 1).nextEdge at he
      have hel : e < 3 := by
        rw [kmswMissingRootStage, hc] at he
        exact he
      have hepos : 1 ≤ e := by change 1 ≤ e at hnew; exact hnew
      have he2 : e = 2 := by
        by_contra hne
        have he1 : e = 1 := by omega
        subst e
        apply hp
        refine ⟨1, he, ?_⟩
        change (kmswMissingRootStage u 1).present 1 = true
        rw [kmswMissingRootStage, hc]
        rfl
      subst e
      rw [(primedLimit_maps_eq_of_allocated w h 1).1 _ he]
      change primeGeomEdge w hfin hb (act w (walkNL w h 0 - 1))
      exact left_exit_primeGeom w h hfin hb 0
    · let k := primedIntervalIndex (primedSimInput w) h (m - 1)
      by_cases ho : m < primedIntervalBase (primedSimInput w) h (k + 1)
      · exact missing_new_ordinary_image w h hfin hb m hm ho e he hnew hp
      · have hr := (image_block_bounds w h m hm).2
        have hB : m = primedIntervalBase (primedSimInput w) h (k + 1) := by
          change m ≤ primedIntervalBase (primedSimInput w) h (k + 1) at hr
          omega
        let sh := kmswMissingRootStage u m
        have hc : u m = 1 := by rw [hB]; exact (primedCrossing_codes w h k).1
        have hlocal : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
          change kmswStep sh (u m) = _
          rw [hc]
          rfl
        have hfalse : (kmswMissingRootStage u (m + 1)).present e = false := by
          cases hh : (kmswMissingRootStage u (m + 1)).present e with
          | false => rfl
          | true => exact (hp ⟨m + 1, he, hh⟩).elim
        change e < (kmswMissingRootStage u (m + 1)).nextEdge at he
        change sh.nextEdge ≤ e at hnew
        have heq : e = sh.nextEdge + 1 := by
          simp only [hlocal, kmswStepOfStep, State.addEdge] at he hfalse
          by_contra hne
          have he0 : e = sh.nextEdge := by omega
          subst e
          simp at hfalse
        subst e
        rw [(primedLimit_maps_eq_of_allocated w h (m + 1)).1 _ he]
        have ho' : ¬ m < primedIntervalBase (primedSimInput w) h
            (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) := ho
        simp only [primedAllEdgeMap, hm, ↓reduceIte, ho']
        change primeGeomEdge w hfin hb (primedCrossingEdgeMap sh _ _ (sh.nextEdge + 1))
        simp only [primedCrossingEdgeMap, Nat.add_one_ne_self, ↓reduceIte]
        exact left_exit_primeGeom w h hfin hb (k + 1)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every missing primed edge, including the root, has retained primed geometry. -/
theorem primedMissingLimitEdge_primeGeomEdge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (hp : ¬ PrimedEdgePresent w h e) :
    primeGeomEdge w hfin hb (primedLimitEdgeMap w h e) := by
  obtain ⟨m, hm⟩ := (primedLocalIds_eventually_allocated w h).1 e
  exact missing_allocated_image w h hfin hb m e hm hp

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
This discharges the isolated nonroot missing-image proposition without assuming it. -/
theorem primedMissingNonrootImage (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedMissingNonrootImageGoal w h hfin hb := by
  intro e _ hp
  exact primedMissingLimitEdge_primeGeomEdge w h hfin hb e hp

private theorem LL_step_cases (s : State) (c : Fin 3) (e : ℕ)
    (he : e ∈ (kmswStep s c).LL) :
    e ∈ s.LL ∨ (c = 0 ∧ s.UL.dropLast.reverse = [] ∧ e = s.nextEdge + 1) := by
  fin_cases c
  · change e ∈ (kmswStepOfStep s .left).LL at he
    cases hp : s.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hp, State.addEdge, List.mem_cons] at he
      rcases he with he | he
      · exact Or.inr ⟨rfl, rfl, he⟩
      · exact Or.inl he
    | cons a as =>
      exact Or.inl (by simpa only [kmswStepOfStep, hp, State.addEdge] using he)
  · change e ∈ (kmswStepOfStep s .up).LL at he
    exact Or.inl he
  · change e ∈ (kmswStepOfStep s .down).LL at he
    cases hp : s.UR <;>
      exact Or.inl (by simpa only [kmswStepOfStep, hp, State.addEdge] using he)

private theorem LL_previous_of_reachable (w : ℕ → Fin 3) (n e : ℕ)
    (hr : Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩)
    (he : e ∈ (kmswStage w (n + 1)).LL) : e ∈ (kmswStage w n).LL := by
  rcases LL_step_cases (kmswStage w n) (w n) e he with he | ⟨hc, hp, _⟩
  · exact he
  · have hm := (mem_stageReachableVertices_iff w (n + 1) _).mpr
      ((actReachableBefore_activeWest_iff w (n + 1)).mpr hr)
    have hh := (stageReachableVertices_left_activeWest_iff w n hc).mp hm
    rw [hp] at hh
    exact hh.elim

private theorem LL_previous_in_right_phase (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k a b : ℕ) (hab : a ≤ b) (ha : walkNR w h k ≤ a + 1)
    (hb : b < walkNL w h k) (e : ℕ) (he : e ∈ (kmswStage w b).LL) :
    e ∈ (kmswStage w a).LL := by
  induction b, hab using Nat.le_induction with
  | base => exact he
  | succ b hab ih =>
    apply ih (by omega)
    exact LL_previous_of_reachable w b e
      (flowLine_phase_reachable w h k (b + 1) (by omega) hb) he

private theorem LL_crossing_old (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k e : ℕ) (he : e ∈ (kmswStage w (walkNL w h (k + 1))).LL) :
    e ∈ (kmswStage w (walkNR w h (k + 1) - 1)).LL := by
  let t := walkNL w h (k + 1)
  have ht := (walkNL_spec w h (k + 1)).1
  have hr := (walkNR_succ_spec w h k).1
  have hp := primedCrossing_exit_predecessor_nonempty w h (k + 1) (by omega)
  have hstep : kmswStage w t = kmswStep (kmswStage w (t - 1)) 0 := by
    have hpos : t - 1 + 1 = t := by dsimp [t]; omega
    conv_lhs => rw [← hpos]
    change kmswStep _ (w (t - 1)) = _
    exact congrArg (kmswStep (kmswStage w (t - 1))) (walkNL_previous_code w h (k + 1))
  have heold : e ∈ (kmswStage w (t - 1)).LL := by
    rw [hstep] at he
    rcases LL_step_cases _ 0 e he with he | ⟨_, hh, _⟩
    · exact he
    · exact (hp hh).elim
  apply LL_previous_in_right_phase w h (k + 1)
    (walkNR w h (k + 1) - 1) (t - 1) (by dsimp [t]; omega) (by omega)
    (by dsimp [t]; omega) e heold

private theorem LL_initial_image (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : ℕ) (he : e ∈ (kmswStage w (walkNL w h 0)).LL) :
    ∃ a, primedLimitEdgeMap w h a = e := by
  let t := walkNL w h 0
  have ht := (walkNL_spec w h 0).1
  have hz := walkNR_zero w h
  have hbefore : ∀ e ∈ (kmswStage w (t - 1)).LL, False := by
    intro e he
    have hm := LL_previous_in_right_phase w h 0 0 (t - 1) (by omega)
      (by rw [hz]; omega) (by dsimp [t]; omega) e he
    exact List.not_mem_nil hm
  have hstep := primedInitial_globalExitTransition w h
  rw [hstep] at he
  rcases LL_step_cases _ 0 e he with he | ⟨_, hp, he⟩
  · exact (hbefore e he).elim
  · refine ⟨0, ?_⟩
    have hmap := (primedAll_maps_extend w h 0).1 0 (by change 0 < 1; decide)
    have hlim := (primedLimit_maps_eq_of_allocated w h 0).1 0
      (by change 0 < 1; decide)
    have hfirst : primedAllEdgeMap w h 1 0 = (kmswStage w (t - 1)).nextEdge + 1 := rfl
    exact hlim.trans (hmap.symm.trans (hfirst.trans he.symm))

private theorem LL_stage_image (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m e, e ∈ (kmswStage w (primedStageTime w h m)).LL →
      ∃ a, primedLimitEdgeMap w h a = e := by
  let u := primedCode (primedSimInput w) h
  intro m
  induction m with
  | zero =>
    intro e he
    rw [primedStageTime_zero] at he
    exact LL_initial_image w h e he
  | succ m ih =>
    intro e he
    by_cases hm : m = 0
    · subst m
      have ht : primedStageTime w h 1 = walkNL w h 0 := by
        simpa only [primedIntervalBase_zero, zero_add] using
          primedStageTime_after_crossing w h 0
      rw [ht] at he
      exact LL_initial_image w h e he
    · let k := primedIntervalIndex (primedSimInput w) h (m - 1)
      by_cases ho : m < primedIntervalBase (primedSimInput w) h (k + 1)
      · obtain ⟨ht, hc⟩ := image_ordinary_alignment w h m hm ho
        let sh := kmswMissingRootStage u m
        let gl := kmswStage w (primedStageTime w h m)
        rw [ht] at he
        rcases LL_step_cases gl (w (primedStageTime w h m)) e he with he | ⟨hw, hp, heq⟩
        · exact ih e he
        · have hcode : u m = 0 := hc.trans hw
          obtain ⟨j, hs, _⟩ := primedAll_sim w h m (by omega)
          have hpred : sh.UL.dropLast.reverse = [] := by
            have hh := hs.forget.left_predecessors
            change sh.UL.dropLast.reverse.map _ = gl.UL.dropLast.reverse at hh
            rw [hp] at hh
            cases hh' : sh.UL.dropLast.reverse with
            | nil => rfl
            | cons a as => rw [hh'] at hh; cases hh
          have hlocal : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
            change kmswStep sh (u m) = _
            rw [hcode]
            rfl
          have ha : sh.nextEdge + 1 < (kmswMissingRootStage u (m + 1)).nextEdge := by
            simp only [hlocal, kmswStepOfStep, hpred, State.addEdge]
            omega
          refine ⟨sh.nextEdge + 1, ?_⟩
          rw [(primedLimit_maps_eq_of_allocated w h (m + 1)).1 _ ha]
          have ho' : m < primedIntervalBase (primedSimInput w) h
              (primedIntervalIndex (primedSimInput w) h (m - 1) + 1) := ho
          simp only [primedAllEdgeMap, hm, ↓reduceIte, ho']
          change primedOrdinaryStepEdgeMap sh gl (u m) _ (sh.nextEdge + 1) = e
          rw [hcode]
          change primedOrdinaryLeftEdgeMap sh gl _ (sh.nextEdge + 1) = e
          rw [primedOrdinaryLeftEdgeMap, ite_eq_left hpred]
          simpa only [kmswShiftUpEdgeMap, Nat.add_one_ne_self, ↓reduceIte] using heq.symm
      · have hr := (image_block_bounds w h m hm).2
        have hB : m = primedIntervalBase (primedSimInput w) h (k + 1) := by
          change m ≤ primedIntervalBase (primedSimInput w) h (k + 1) at hr
          omega
        have ht := primedStageTime_after_crossing w h (k + 1)
        rw [← hB] at ht
        rw [ht] at he
        apply ih e
        rw [hB, primedStageTime_at_crossing]
        exact LL_crossing_old w h k e he

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every ambient permanently missing edge has a primed geometric preimage. -/
theorem primedAmbientMissingEdgeImage (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (h : HasFlowLineHits w) : primedAmbientMissingEdgeImageGoal w hfin hb h := by
  intro e hp _
  have ha := kmsw_edge_allocated_by_self w e
  have hf : (kmswStage w e).present e = false := by
    cases hh : (kmswStage w e).present e with
    | false => rfl
    | true => exact (hp ⟨e, ha, hh⟩).elim
  have hLL : e ∈ (kmswStage w e).LL := by
    rcases ((kmswStage_status w e).1 e ha).mp hf with hur | hll
    · obtain ⟨n, hn, hpresent⟩ :=
        kmswStage_UR_edge_eventually_present_of_R_unbounded w hb.R_unbounded_below e e hur
      exact (hp ⟨n, ha.trans_le (kmswStage_nextEdge_mono w hn), hpresent⟩).elim
    · exact hll
  have hNR : ∀ k, k ≤ walkNR w h k := by
    intro k
    induction k with
    | zero => rw [walkNR_zero]
    | succ k ih =>
      have hL := (walkNL_spec w h k).1
      have hR := (walkNR_succ_spec w h k).1
      omega
  let m := primedIntervalBase (primedSimInput w) h (e + 1)
  have ht : e ≤ primedStageTime w h m := by
    rw [primedStageTime_at_crossing]
    have hh := hNR (e + 1)
    omega
  exact LL_stage_image w h m e (primedCrossing_LL_persistent w ht hLL).1

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The limit edge image is precisely the full primed geometric carrier. -/
theorem primeGeomEdge_iff_primedLimitEdge (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (h : HasFlowLineHits w) : primeGeomEdge_iff_primedLimitEdgeGoal w hfin hb h := by
  classical
  intro e
  constructor
  · intro hg
    by_cases hp : primePresentEdge w e
    · exact primedLimitEdge_preimage_of_present_nonMhat w h e hp.1 hp.2
    · rcases primeMissingEdge_source_cases w hfin hb e ⟨hg, hp⟩ with
        ⟨hbeta, _⟩ | ⟨hmissing, houtside⟩
      · exact primedBeta0MissingEdgeImage w hfin hb h e hbeta
      · exact primedAmbientMissingEdgeImage w hfin hb h e hmissing houtside
  · rintro ⟨a, rfl⟩
    by_cases hp : PrimedEdgePresent w h a
    · exact primedPresentLimitEdge_primeGeomEdge w hfin hb h hp
    · exact primedMissingLimitEdge_primeGeomEdge w h hfin hb a hp

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Missing tags agree on the full geometric image, including the C18 root. -/
theorem primedLimitEdgeMap_missing (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (e : ℕ) :
    ¬ PrimedEdgePresent w h e ↔
      primeMissingEdge w hfin hb (primedLimitEdgeMap w h e) := by
  constructor
  · intro hp
    exact (primedLimitEdgeMap_missing_iff w h hfin hb e).mpr
      ⟨primedMissingLimitEdge_primeGeomEdge w h hfin hb e hp, hp⟩
  · intro hp
    exact ((primedLimitEdgeMap_missing_iff w h hfin hb e).mp hp).2

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The corrected limit dart map bijects all primed darts with retained ambient darts. -/
@[expose] noncomputable def primedGeometricDartEquiv (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    (ℕ × Bool) ≃ {d // d ∈ primeDartSet w hfin hb} :=
  Equiv.ofBijective
    (fun d => ⟨primedLimitDartMap w h d,
      (primeGeomEdge_iff_primedLimitEdge w hfin hb h _).mpr ⟨d.1, rfl⟩⟩)
    ⟨fun _ _ hd => primedLimitDartMap_injective w h (congrArg Subtype.val hd), by
      rintro ⟨⟨e, b⟩, hg⟩
      obtain ⟨a, ha⟩ := (primeGeomEdge_iff_primedLimitEdge w hfin hb h e).mp hg
      refine ⟨(a, b ^^ primedLimitSideFlip w h a), Subtype.ext ?_⟩
      apply Prod.ext
      · exact ha
      · change ((b ^^ primedLimitSideFlip w h a) ^^ primedLimitSideFlip w h a) = b
        cases b <;> cases primedLimitSideFlip w h a <;> rfl⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The dart equivalence evaluates by the corrected geometric dart map. -/
theorem primedGeometricDartEquiv_apply (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    (primedGeometricDartEquiv w h hfin hb d).val = primedLimitDartMap w h d := rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The primed dart equivalence preserves the C18 root, edge reversal, missing tags
and directed tails. Rotation and realized-face identification remain separate. -/
theorem primedGeometricDartIdentification (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    ∃ H' : (ℕ × Bool) ≃ {d // d ∈ primeDartSet w hfin hb},
      (H' futureMapRootDart).val = (kmswLLCreatedEdge w (walkNL w h 0), false) ∧
      (∀ d, (H' (futureMapEdgeInv d)).val = futureMapEdgeInv (H' d).val) ∧
      (∀ d, ¬ PrimedEdgePresent w h d.1 ↔
        primeMissingEdge w hfin hb (H' d).val.1) ∧
      (∀ d, (d.2 = false ∧ PrimedEdgePresent w h d.1) ↔
        ((H' d).val.2 = false ∧ primePresentEdge w (H' d).val.1)) := by
  refine ⟨primedGeometricDartEquiv w h hfin hb, primedLimitDartMap_root w h,
    primedLimitDartMap_edgeInv w h, ?_, primedLimitDartMap_tail w h⟩
  intro d
  exact primedLimitEdgeMap_missing w h hfin hb d.1

end DirectedDistances.KMSW
