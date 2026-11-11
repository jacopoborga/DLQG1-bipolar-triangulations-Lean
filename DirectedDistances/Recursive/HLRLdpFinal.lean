module

public import DirectedDistances.Recursive.PrimedEntryDecoderExists
public import DirectedDistances.Recursive.HattedLeftSeamDecoderExists
public import DirectedDistances.Recursive.HLRLdpAssembly
import DirectedDistances.KMSW.KMSWLeftLLFirstHit

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open Quiver MeasureTheory ProbabilityTheory Filter
open scoped Classical

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The lower-left stack changes only at a fresh left step. -/
private theorem final_LL_step (s : State) (c : Fin 3) :
    (kmswStep s c).LL =
      if c = 0 ∧ s.UL.dropLast.reverse = [] then
        (s.nextEdge + 1) :: s.LL else s.LL := by
  fin_cases c
  · cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  · simp [kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  · cases hp : s.UR <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A reachable active west endpoint rules out creation of a missing left edge. -/
private theorem final_LL_step_of_reachable (w : ℕ → Fin 3) (n : ℕ)
    (hr : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩) :
    (kmswStage w (n + 1)).LL = (kmswStage w n).LL := by
  change (kmswStep (kmswStage w n) (w n)).LL = _
  rw [final_LL_step]
  apply ite_eq_right
  rintro ⟨hc, hp⟩
  have hm := (mem_stageReachableVertices_iff w (n + 1) _).mpr
    ((actReachableBefore_activeWest_iff w (n + 1)).mpr hr)
  have hh := (stageReachableVertices_left_activeWest_iff w n hc).mp hm
  rw [hp] at hh
  exact hh

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The lower-left list is unchanged throughout a right phase before its exit. -/
private theorem final_LL_right_phase (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k a b : ℕ) (hab : a ≤ b) (ha : walkNR w h k ≤ a + 1)
    (hb : b < walkNL w h k) :
    (kmswStage w b).LL = (kmswStage w a).LL := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [final_LL_step_of_reachable w b
      (flowLine_phase_reachable w h k (b + 1) (by omega) hb)]
    exact ih (by omega)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
At the initial left exit the sole ambient LL edge is the retained primed root. -/
private theorem final_LL_initial (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (kmswStage w (walkNL w h 0)).LL =
      [kmswLLCreatedEdge w (walkNL w h 0)] := by
  let t := walkNL w h 0
  have ht : 0 < t := by
    have hh := (walkNL_spec w h 0).1
    rw [walkNR_zero] at hh
    exact hh
  have hold : (kmswStage w (t - 1)).LL = [] :=
    final_LL_right_phase w h 0 0 (t - 1) (by omega)
      (by rw [walkNR_zero]; omega) (by omega)
  have hp := (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have hs := primedInitial_globalExitTransition w h
  change kmswStage w t = kmswStep (kmswStage w (t - 1)) 0 at hs
  change (kmswStage w (t - 1)).UL.dropLast.reverse = [] at hp
  rw [hs, final_LL_step, ite_eq_left ⟨rfl, hp⟩, hold]
  congr 1
  change _ = (kmswStage w t).nextEdge - 1
  rw [hs]
  simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Later compressed crossing steps skip no lower-left boundary edges. -/
private theorem final_LL_crossing (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage w (walkNL w h (k + 1))).LL =
      (kmswStage w (walkNR w h (k + 1) - 1)).LL := by
  let t := walkNL w h (k + 1)
  have ht := (walkNL_spec w h (k + 1)).1
  have hr := (walkNR_succ_spec w h k).1
  have hp := primedCrossing_exit_predecessor_nonempty w h (k + 1) (by omega)
  have hs : kmswStage w t = kmswStep (kmswStage w (t - 1)) 0 := by
    have he : t - 1 + 1 = t := by dsimp [t]; omega
    conv_lhs => rw [← he]
    change kmswStep _ (w (t - 1)) = _
    exact congrArg (kmswStep (kmswStage w (t - 1)))
      (walkNL_previous_code w h (k + 1))
  rw [hs, final_LL_step, ite_eq_right (by rintro ⟨_, hh⟩; exact hp hh)]
  exact final_LL_right_phase w h (k + 1) _ _ (by dsimp [t]; omega)
    (by omega) (by dsimp [t]; omega)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Ordinary compressed steps retain the same raw code and advance raw time by one. -/
private theorem final_ordinary_alignment (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)) :
    primedStageTime w h (m + 1) = primedStageTime w h m + 1 ∧
      primedCode (primedSimInput w) h m = w (primedStageTime w h m) := by
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  have hr : m ≤ primedIntervalBase (primedSimInput w) h (k + 1) := by
    have hi := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
    change m - 1 < primedIntervalBase (primedSimInput w) h (k + 1) at hi
    omega
  have hl : primedIntervalBase (primedSimInput w) h k < m := by
    cases hk : k with
    | zero => rw [primedIntervalBase_zero]; omega
    | succ j =>
      have hh := Nat.find_min
        (primedIntervalIndex_exists (primedSimInput w) h (m - 1))
        (show j < Nat.find
          (primedIntervalIndex_exists (primedSimInput w) h (m - 1)) by
          change j < k; omega)
      change ¬ m - 1 < primedIntervalBase (primedSimInput w) h (j + 1) at hh
      omega
  change m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
  have ht0 := primedStageTime_block w h k m hl hr
  have ht1 := primedStageTime_block w h k (m + 1) (by omega) (by omega)
  constructor
  · rw [ht0, ht1]
    omega
  · have hc := primedCode_positive_offset (primedSimInput w) h k
      (m - primedIntervalBase (primedSimInput w) h k) (by omega) (by
        rw [primedIntervalBase_succ] at ho
        omega)
    have he : primedIntervalBase (primedSimInput w) h k +
        (m - primedIntervalBase (primedSimInput w) h k) = m := by omega
    rw [he] at hc
    change primedCode (primedSimInput w) h m =
      w (walkNL w h k + (m - primedIntervalBase (primedSimInput w) h k) - 1) at hc
    rwa [← ht0] at hc

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A fresh ordinary LL endpoint has the same ordered ambient west endpoint. -/
private theorem final_fresh_west (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : m ≠ 0)
    (ho : m < primedIntervalBase (primedSimInput w) h
      (primedIntervalIndex (primedSimInput w) h (m - 1) + 1))
    (hc : primedCode (primedSimInput w) h m = 0)
    (hp : (kmswStage (primedCode (primedSimInput w) h) m).UL.dropLast.reverse = []) :
    primedLimitVertexMap w h
        (edgeWest (primedCode (primedSimInput w) h)
          ((kmswStage (primedCode (primedSimInput w) h) m).nextEdge + 1)) =
      edgeWest w ((kmswStage w (primedStageTime w h m)).nextEdge + 1) := by
  let u := primedCode (primedSimInput w) h
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w (primedStageTime w h m)
  have ha := kmswMissingRootStage_agree u m
  have hp' : sh.UL.dropLast.reverse = [] := by
    change (kmswMissingRootStage u m).UL.dropLast.reverse = []
    rw [ha.2.2.2.2.2.2.2.1]
    exact hp
  obtain ⟨_, hs, _⟩ := primedAll_sim w h m (by omega)
  have hgp : gl.UL.dropLast.reverse = [] := by
    have hh := hs.forget.left_predecessors
    change sh.UL.dropLast.reverse.map _ = gl.UL.dropLast.reverse at hh
    rw [hp', List.map_nil] at hh
    exact hh.symm
  have hgc : w (primedStageTime w h m) = 0 :=
    (final_ordinary_alignment w h m hm ho).2.symm.trans hc
  change u m = 0 at hc
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    change kmswStep sh (u m) = _
    rw [hc]
    rfl
  have hg : kmswStage w (primedStageTime w h m + 1) =
      kmswStepOfStep gl .left := by
    change kmswStep gl (w (primedStageTime w h m)) = _
    rw [hgc]
    rfl
  have hv : sh.nextVertex < (kmswMissingRootStage u (m + 1)).nextVertex := by
    rw [hl]
    simp only [kmswStepOfStep, hp', State.addEdge]
    omega
  have he : sh.nextEdge + 1 < (kmswStage u (m + 1)).nextEdge := by
    rw [← (kmswMissingRootStage_agree u (m + 1)).2.1, hl]
    simp only [kmswStepOfStep, hp', State.addEdge]
    omega
  have hw : edgeWest u (sh.nextEdge + 1) = sh.nextVertex := by
    rw [← (edge_endpoints_eq u he).1,
      ← (kmswMissingRootStage_agree u (m + 1)).2.2.1, hl]
    simp [kmswStepOfStep, hp', State.addEdge]
  have hge : gl.nextEdge + 1 <
      (kmswStage w (primedStageTime w h m + 1)).nextEdge := by
    rw [hg]
    simp only [kmswStepOfStep, hgp, State.addEdge]
    omega
  rw [← ha.2.1, hw, (primedLimit_maps_eq_of_allocated w h (m + 1)).2 _ hv]
  simp only [primedAllVertexMap, hm, ↓reduceIte, ho]
  change primedOrdinaryStepVertexMap sh gl (u m) _ sh.nextVertex = _
  rw [hc]
  simp only [primedOrdinaryStepVertexMap, ↓reduceIte, primedOrdinaryLeftVertexMap,
    hp', kmswShiftUpVertexMap]
  rw [← (edge_endpoints_eq w hge).1, hg]
  simp [kmswStepOfStep, hgp, State.addEdge]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The LL endpoint list has exactly the ambient order after adjoining the retained root. -/
private theorem final_LL_west_list (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    (kmswStage (primedCode (primedSimInput w) h) m).LL.map
        (fun e => primedLimitVertexMap w h
          (edgeWest (primedCode (primedSimInput w) h) e)) ++
        [edgeWest w (kmswLLCreatedEdge w (walkNL w h 0))] =
      (kmswStage w (primedStageTime w h m)).LL.map (edgeWest w) := by
  let u := primedCode (primedSimInput w) h
  induction m with
  | zero =>
    rw [primedStageTime_zero, final_LL_initial]
    rfl
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      have ht := primedStageTime_after_crossing w h 0
      rw [primedIntervalBase_zero, zero_add] at ht
      rw [ht, final_LL_initial]
      have hc : u 0 = 1 := primedCode_zero (primedSimInput w) h
      change (kmswStep (kmswStage u 0) (u 0)).LL.map _ ++ _ = _
      rw [hc, final_LL_step, ite_eq_right (by rintro ⟨hh, _⟩; cases hh)]
      rfl
    · by_cases ho : m < primedIntervalBase (primedSimInput w) h
          (primedIntervalIndex (primedSimInput w) h (m - 1) + 1)
      · obtain ⟨ht, hc⟩ := final_ordinary_alignment w h m hm ho
        rw [ht]
        change (kmswStep (kmswStage u m) (u m)).LL.map _ ++ _ =
          (kmswStep (kmswStage w (primedStageTime w h m))
            (w (primedStageTime w h m))).LL.map _
        rw [← hc, final_LL_step, final_LL_step]
        obtain ⟨_, hs, _⟩ := primedAll_sim w h m (by omega)
        have hp : (kmswStage u m).UL.dropLast.reverse = [] ↔
            (kmswStage w (primedStageTime w h m)).UL.dropLast.reverse = [] := by
          have hh := hs.forget.left_predecessors
          change (kmswMissingRootStage u m).UL.dropLast.reverse.map _ = _ at hh
          rw [(kmswMissingRootStage_agree u m).2.2.2.2.2.2.2.1] at hh
          exact (List.map_eq_nil_iff).symm.trans (Iff.of_eq (congrArg (· = []) hh))
        by_cases hf : u m = 0 ∧ (kmswStage u m).UL.dropLast.reverse = []
        · rw [ite_eq_left hf, ite_eq_left ⟨hf.1, hp.mp hf.2⟩]
          simp only [List.map_cons, List.cons_append]
          rw [final_fresh_west w h m hm ho hf.1 hf.2, ih]
        · rw [ite_eq_right hf, ite_eq_right (by
            rintro ⟨hc', hp'⟩; exact hf ⟨hc', hp.mpr hp'⟩)]
          exact ih
      · let k := primedIntervalIndex (primedSimInput w) h (m - 1)
        have hr := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
        have hB : m = primedIntervalBase (primedSimInput w) h (k + 1) := by
          change m - 1 < primedIntervalBase (primedSimInput w) h (k + 1) at hr
          change ¬ m < primedIntervalBase (primedSimInput w) h (k + 1) at ho
          omega
        have hc : u m = 1 := by rw [hB]; exact (primedCrossing_codes w h k).1
        have ht := primedStageTime_after_crossing w h (k + 1)
        rw [← hB] at ht
        rw [ht, final_LL_crossing, ← primedStageTime_at_crossing w h k, ← hB]
        change (kmswStep (kmswStage u m) (u m)).LL.map _ ++ _ = _
        rw [hc, final_LL_step, ite_eq_right (by rintro ⟨hh, _⟩; cases hh)]
        exact ih

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The ambient reversed LL west endpoints have the exact negative boundary indices. -/
private theorem final_ambient_LL_vertex (w : ℕ → Fin 3) (hb : BoundaryHitWitnesses w)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ (kmswStage w n).LL.length) :
    ((kmswStage w n).LL.reverse.map (edgeWest w))[k - 1]? =
      some (boundaryVertex w hb (-(k : ℤ))) := by
  have hh := kmswLL_reverse_get_first_hit w n k hk hkn
  dsimp only at hh
  have ht : boundaryHitTime w hb (-(k : ℤ)) =
      Nat.find (kmswLL_level_hit w n k hk hkn) := by
    simp only [boundaryHitTime, dite_eq_right (by omega : -(k : ℤ) ≠ 0),
      dite_eq_right (by omega : ¬ 0 < -(k : ℤ))]
  have hv := (boundaryVertex_left_missing_edge w hb
    (k := -(k : ℤ)) (by omega)).1
  have he : kmswLLCreatedEdge w (boundaryHitTime w hb (-(k : ℤ))) <
      (kmswStage w (boundaryHitTime w hb (-(k : ℤ)))).nextEdge := by
    have hp := kmswStage_nextEdge_mono w
      (Nat.zero_le (boundaryHitTime w hb (-(k : ℤ))))
    change 1 ≤ _ at hp
    change _ - 1 < _
    omega
  rw [(edge_endpoints_eq w he).1] at hv
  have hi : k - 1 < (kmswStage w n).LL.reverse.length := by
    rw [List.length_reverse]
    omega
  rw [List.getElem?_map, List.getElem?_eq_getElem hi]
  change some (edgeWest w ((kmswStage w n).LL.reverse.get ⟨k - 1, hi⟩)) = _
  rw [hh.2.2, ← ht, hv]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every required ambient negative boundary index is eventually present at compressed times. -/
private theorem final_LL_length_eventually (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hb : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ m in atTop, k ≤ (kmswStage w (primedStageTime w h m)).LL.length := by
  let N := boundaryHitTime w hb (-(k : ℤ))
  have hNR (j : ℕ) : j ≤ walkNR w h j := by
    induction j with
    | zero => rw [walkNR_zero]
    | succ j ih =>
      have hL := (walkNL_spec w h j).1
      have hR := (walkNR_succ_spec w h j).1
      omega
  let M := primedIntervalBase (primedSimInput w) h (N + 1)
  have hM : N ≤ primedStageTime w h M := by
    rw [primedStageTime_at_crossing]
    have hh := hNR (N + 1)
    omega
  have hmono : Monotone (primedStageTime w h) :=
    monotone_nat_of_le_succ (primedStageTime_succ_le w h)
  filter_upwards [eventually_ge_atTop M] with m hm
  have hn : N ≤ primedStageTime w h m := hM.trans (hmono hm)
  have hmin := runningMin_le (L w) (primedStageTime w h m) N hn
  have hhit := boundaryHitTime_left_spec w hb (k := -(k : ℤ)) (by omega)
  have hlen := kmswStage_LL_length w (primedStageTime w h m)
  change minL w (primedStageTime w h m) ≤ L w N at hmin
  change L w N = -(k : ℤ) at hhit
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The primed LL list enumerates precisely the ambient vertices west of its retained root. -/
theorem primedEntryOuterLLVertexIdentification_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) (i : ℕ) :
    PrimedEntryOuterLLVertexIdentification w h hb i := by
  let u := primedCode (primedSimInput w) h
  filter_upwards [final_LL_length_eventually w h hb (i + 2) (by omega)] with m hm
  have hl := congrArg List.reverse (final_LL_west_list w h m)
  simp only [List.reverse_append, List.reverse_singleton, ← List.map_reverse] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_append, List.length_singleton, List.length_map,
    List.length_reverse] at hlen
  change 1 + (kmswStage u m).LL.length =
    (kmswStage w (primedStageTime w h m)).LL.length at hlen
  have hi : i < (kmswStage u m).LL.reverse.length := by
    rw [List.length_reverse]
    omega
  let e := (kmswStage u m).LL.reverse[i]
  have hem : e ∈ (kmswStage u m).LL := List.mem_reverse.mp (List.getElem_mem hi)
  have heb : e < (kmswStage u m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u m).2 e (by
      simp only [List.mem_append]
      tauto)
  refine ⟨(kmswStage u m).west e, ?_, ?_⟩
  · rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  · have hv := final_ambient_LL_vertex w hb (primedStageTime w h m) (i + 2)
      (by omega) hm
    have hidx : i + 2 - 1 = i + 1 := by omega
    rw [hidx, ← hl] at hv
    change ((kmswStage u m).LL.reverse.map
      (fun e => primedLimitVertexMap w h (edgeWest u e)))[i]? = _ at hv
    rw [List.getElem?_map, List.getElem?_eq_getElem hi] at hv
    rw [(edge_endpoints_eq u heb).1]
    exact Option.some.inj hv

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
All outer boundary indices, including both retained root endpoints, are identified. -/
private theorem primedEntryOuterVertexIdentification_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) (j : ℕ) :
    PrimedEntryOuterVertexIdentification w h hb j := by
  rcases j with _ | j
  · exact primedEntryOuterVertexIdentification_zero_proved w h hb
  rcases j with _ | i
  · exact primedEntryOuterVertexIdentification_one_proved w h hb
  have hh := primedEntryOuterLLVertexIdentification_proved w h hb i
  filter_upwards [hh] with n hn
  obtain ⟨a, ha, ham⟩ := hn
  refine ⟨a, ?_, ham⟩
  simpa only [primedEntryOuterVertex, List.cons_append, List.nil_append,
    List.getElem?_cons_succ] using ha

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Injectivity of H' makes the eventual outer endpoint independent of the stage. -/
private theorem final_outer_fixed (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hb : BoundaryHitWitnesses w) (j : ℕ) :
    ∃ a, (∀ᶠ n in atTop,
      primedEntryOuterVertex (kmswStage (primedCode (primedSimInput w) h) n) j =
        some a) ∧ primedLimitVertexMap w h a = boundaryVertex w hb (-(j : ℤ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (primedEntryOuterVertexIdentification_proved w h hb j)
  obtain ⟨a, _, ham⟩ := hN N le_rfl
  refine ⟨a, ?_, ham⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨b, hb', hbm⟩ := hN n hn
  have he : b = a := (primedLimit_maps_injective_on_allocated w h).2
    ((primedLocalIds_eventually_allocated w h).2 b)
    ((primedLocalIds_eventually_allocated w h).2 a) (hbm.trans ham.symm)
  rwa [he] at hb'

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every outer/glue pair has its exact eventual first-entry distance, including bottom. -/
private theorem primedEntryBoundaryStageDistance_eventually (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (j k : ℕ) :
    ∀ᶠ n in atTop,
      primedEntryBoundaryStageDistance (primedCode (primedSimInput w) h) n j k =
        leftLengthSup (leftPrimedEntryLengths w ⟨boundaryVertex w hb (-(j : ℤ))⟩
          ⟨kmswBeta0Vertices w hfin hb k⟩) := by
  obtain ⟨a, ha, ham⟩ := final_outer_fixed w h hb j
  let b := edgeEast (primedCode (primedSimInput w) h)
    (primedBeta0EdgeIndex w h hfin hb hfin k)
  have hglue := primedEntryGlueVertex_eventually w h hfin hb k
  have hdist := primedEntryStageDistance_identification w h hfin a b
  have hbm := primedEntryGlueVertexIdentification_proved w h hfin hb k
  change primedLimitVertexMap w h b = kmswBeta0Vertices w hfin hb k at hbm
  filter_upwards [ha, hglue, hdist] with n hn hg hd
  unfold primedEntryBoundaryStageDistance
  rw [hn, hg]
  change primedEntryStageDistance _ n a b = _
  rw [hd, ham, hbm]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The stabilized code equals the ambient first-entry distance for every pair of indices. -/
private theorem primedEntryDistanceCode_identification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (j k : ℕ) :
    primedEntryDistanceCode (primedCode (primedSimInput w) h) j k =
      some (leftLengthSup (leftPrimedEntryLengths w
        ⟨boundaryVertex w hb (-(j : ℤ))⟩ ⟨kmswBeta0Vertices w hfin hb k⟩)) :=
  (primedEntryDistanceCode_eq_some_iff _ j k _).mpr
    (primedEntryBoundaryStageDistance_eventually w h hfin hb j k)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The code identification holds simultaneously for all incidence and boundary witnesses. -/
private theorem primedEntryDistanceCodeIdentification_proved :
    PrimedEntryDistanceCodeIdentification := by
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω h
  dsimp only
  intro hfin hb j k
  rw [hatLawPrimedCodes, dite_eq_left h, rightHat_boundaryIdTotal_eq ω hb]
  exact primedEntryDistanceCode_identification _ h hfin hb j k

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The measurable primed decoder has the exact specification for all j and k. -/
theorem primedEntryDecoderExists_proved : PrimedEntryDecoderExists := by
  refine ⟨primedEntryDecoder, measurable_primedEntryDecoder, ?_⟩
  filter_upwards [primedEntryDistanceCodeIdentification_proved] with ω h
  dsimp only
  intro hfin hb j k
  unfold primedEntryDecoder
  rw [h hfin hb j k, Option.getD_some]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Both constructed decoders give left Busemann locality without any open premise. -/
private theorem leftBusemannLdpLocality_proved : LeftBusemannLdpLocality :=
  leftBusemannLdpLocality_of_decoders primedEntryDecoderExists_proved
    hattedLeftSeamDecoderExists_proved

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The ℕ-indexed left and right LDP Busemann profiles, j ↦ V(-j) and j ↦ V(j), are independent. -/
theorem hLR_ldp_proved :
    IndepFun (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannLDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure :=
  hLR_ldp_of_leftLocality leftBusemannLdpLocality_proved

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integer-indexed LDP Busemann increments are mutually independent. -/
theorem ldpIncrements_iIndep_proved :
    iIndepFun (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure :=
  ldpIncrements_iIndep_of_leftLocality leftBusemannLdpLocality_proved

end DirectedDistances.Recursive
