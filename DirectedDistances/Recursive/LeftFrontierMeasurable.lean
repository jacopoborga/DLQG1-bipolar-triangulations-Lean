module

public import DirectedDistances.Recursive.LeftFrontierEnvelope
public import DirectedDistances.Recursive.IndependenceFromLR
public import DirectedDistances.Probability.FrontierIndependence
public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.Recursive.LeftStationaryBusemann
import DirectedDistances.KMSW.DirectedContainHat

/-! # Past-measurable left frontier envelopes

Past-measurable frontier decomposition of D₀ at τ₋₁, for the `hfrontL`
hypothesis in the `item-busemann-ind` reduction (plan B.2 in
paper results; F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Probability

/-- Indices of early-reachable vertices in the ordered cutoff east frontier -/
@[expose] def leftPastFrontierIndices (k : ℕ) (p : ℕ → Fin 3) : Set ℕ :=
  {j | 1 ≤ j ∧ ∃ u,
    (CutConverse.pendingVertices (kmswStage p k))[j - 1]? = some u ∧
    (earlyPathLengths p k 0 u).Nonempty}

 
@[expose] noncomputable def leftPastSdpCoefficient (k : ℕ) (p : ℕ → Fin 3)
    (j : ℕ) : ℤ :=
  ((earlySdp p k ⟨0⟩
    ⟨((CutConverse.pendingVertices (kmswStage p k))[j - 1]?).getD 0⟩).toNat : ℤ)

/-- actual frontier is finite by `LeftFrontierEnvelope`. Plan B.2; F1/F4 remain. -/
@[expose] noncomputable def leftPastLdpCoefficient (k : ℕ) (p : ℕ → Fin 3)
    (j : ℕ) : ℤ :=
  (((earlyLdp p k ⟨0⟩
    ⟨((CutConverse.pendingVertices (kmswStage p k))[j - 1]?).getD 0⟩).unbotD 0 : ℕ) : ℤ)



@[expose] noncomputable def leftPastSdpEnvelope (k : ℕ) (p : ℕ → Fin 3)
    (x : ℕ → ℤ) : ℤ :=
  sInf ((fun j => leftPastSdpCoefficient k p j + x j) '' leftPastFrontierIndices k p)



@[expose] noncomputable def leftPastLdpEnvelope (k : ℕ) (p : ℕ → Fin 3)
    (x : ℕ → ℤ) : ℤ :=
  sSup ((fun j => leftPastLdpCoefficient k p j + x j) '' leftPastFrontierIndices k p)

private theorem past_indices_congr {k : ℕ} {p q : ℕ → Fin 3}
    (hp : ∀ i, i < k → p i = q i) :
    leftPastFrontierIndices k p = leftPastFrontierIndices k q := by
  ext j
  simp only [leftPastFrontierIndices, Set.mem_ofPred_eq, kmswStage_congr hp,
    earlyPathLengths_congr k 0 _ hp]

private theorem past_sdp_congr {k : ℕ} {p q : ℕ → Fin 3}
    (hp : ∀ i, i < k → p i = q i) (j : ℕ) :
    leftPastSdpCoefficient k p j = leftPastSdpCoefficient k q j := by
  unfold leftPastSdpCoefficient
  rw [kmswStage_congr hp, earlySdp_congr k 0 _ hp]

private theorem past_ldp_congr {k : ℕ} {p q : ℕ → Fin 3}
    (hp : ∀ i, i < k → p i = q i) (j : ℕ) :
    leftPastLdpCoefficient k p j = leftPastLdpCoefficient k q j := by
  unfold leftPastLdpCoefficient
  rw [kmswStage_congr hp, earlyLdp_congr k 0 _ hp]

private def extendPast (k : ℕ) (p : Fin k → Fin 3) : ℕ → Fin 3 :=
  fun i => if hi : i < k then p ⟨i, hi⟩ else 0



theorem measurable_leftPastSdpEnvelope (k : ℕ) :
    Measurable (Function.uncurry (leftPastSdpEnvelope k)) := by
  have hm : ∀ q : Fin k → Fin 3,
      Measurable (fun z : (ℕ → Fin 3) × (ℕ → ℤ) =>
        leftPastSdpEnvelope k (extendPast k q) z.2) := by
    intro q
    exact Measurable.sInf (Set.to_countable _) (fun j _ =>
      measurable_const.add ((measurable_pi_apply j).comp measurable_snd))
  have hh : Measurable (fun z : ((ℕ → Fin 3) × (ℕ → ℤ)) × (Fin k → Fin 3) =>
      leftPastSdpEnvelope k (extendPast k z.2) z.1.2) :=
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
  simp only [Function.uncurry, Function.comp_apply, leftPastSdpEnvelope,
    past_indices_congr hp, past_sdp_congr hp]



theorem measurable_leftPastLdpEnvelope (k : ℕ) :
    Measurable (Function.uncurry (leftPastLdpEnvelope k)) := by
  have hm : ∀ q : Fin k → Fin 3,
      Measurable (fun z : (ℕ → Fin 3) × (ℕ → ℤ) =>
        leftPastLdpEnvelope k (extendPast k q) z.2) := by
    intro q
    exact Measurable.sSup (Set.to_countable _) (fun j _ =>
      measurable_const.add ((measurable_pi_apply j).comp measurable_snd))
  have hh : Measurable (fun z : ((ℕ → Fin 3) × (ℕ → ℤ)) × (Fin k → Fin 3) =>
      leftPastLdpEnvelope k (extendPast k z.2) z.1.2) :=
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
  simp only [Function.uncurry, Function.comp_apply, leftPastLdpEnvelope,
    past_indices_congr hp, past_ldp_congr hp]

private theorem past_shift_UR_suffix (w : ℕ → Fin 3) (t m : ℕ) :
    (kmswStage w (t + m)).UR =
      ((kmswStage (fun i => w (t + i)) m).UR.map (kmswShiftEdgeMapAll w t m)) ++
        (kmswStage w t).UR.drop ((kmswStage (fun i => w (t + i)) m).LR.length - 1) := by
  let ws := fun i => w (t + i)
  induction m with
  | zero => simp [kmswStage, kmswInit]
  | succ m ih =>
    let sh := kmswStage ws m
    let gl := kmswStage w (t + m)
    let ep := kmswShiftEdgeMapAll w t m
    let en := kmswShiftEdgeMapAll w t (m + 1)
    have hsh : kmswStage ws (m + 1) = kmswStepOfStep sh (kmswCodeStep (ws m)) := rfl
    have hgl : kmswStage w (t + (m + 1)) =
        kmswStepOfStep gl (kmswCodeStep (ws m)) := by
      rw [Nat.add_succ]
      rfl
    have hmap : sh.UR.map en = sh.UR.map ep := by
      apply List.map_congr_left
      intro e he
      apply kmswShiftEdgeMapAll_extend
      exact (kmswStage_boundary_ids_lt_nextEdge ws m).2 e
        (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr he)))
    have hlen : 1 ≤ sh.LR.length := by
      have h := kmswStage_LR_length ws m
      have hmin := runningMin_le (R ws) m 0 (Nat.zero_le m)
      have hz : R ws 0 = 0 := by simp [R]
      change minR ws m ≤ R ws 0 at hmin
      change ((sh.LR.length : ℕ) : ℤ) = _ at h
      omega
    change gl.UR = sh.UR.map ep ++ (kmswStage w t).UR.drop (sh.LR.length - 1) at ih
    dsimp only [en] at hmap
    rw [hsh, hgl]
    cases hc : kmswCodeStep (ws m) with
    | up =>
      have hnew : en (sh.nextEdge + 1) = gl.nextEdge + 1 := by
        change kmswShiftNextEdgeMap sh gl (kmswCodeStep (ws m)) ep _ = _
        simp [hc, kmswShiftNextEdgeMap, kmswShiftUpEdgeMap]
      dsimp only [en] at hnew
      simpa only [hc, kmswStepOfStep, State.addEdge, List.map_cons, hnew,
        hmap, List.cons_append] using congrArg (List.cons (gl.nextEdge + 1)) ih
    | left =>
      cases hs : sh.UL.dropLast.reverse <;>
        cases hg : gl.UL.dropLast.reverse <;>
          simpa only [hc, kmswStepOfStep, hs, hg, State.addEdge, hmap] using ih
    | down =>
      cases hs : sh.UR with
      | cons e es =>
        have hg : gl.UR = ep e :: (es.map ep ++
            (kmswStage w t).UR.drop (sh.LR.length - 1)) := by
          simpa only [hs, List.map_cons, List.cons_append] using ih
        have htail : es.map en = es.map ep := by
          have hh := hmap
          rw [hs, List.map_cons, List.map_cons] at hh
          exact (List.cons.inj hh).2
        dsimp only [en] at htail
        simp only [kmswStepOfStep, hs, hg, htail]
      | nil =>
        have hres : gl.UR = (kmswStage w t).UR.drop (sh.LR.length - 1) := by
          simpa only [hs, List.map_nil, List.nil_append] using ih
        have hdrop : (kmswStage w t).UR.drop sh.LR.length = gl.UR.tail := by
          calc
            (kmswStage w t).UR.drop sh.LR.length =
                ((kmswStage w t).UR.drop (sh.LR.length - 1)).drop 1 := by
              rw [List.drop_drop]
              congr 1
              omega
            _ = gl.UR.tail := by rw [← hres, List.drop_one]
        cases hg : gl.UR with
        | nil =>
          simp only [kmswStepOfStep, hs, hg, State.addEdge, List.map_nil,
            List.nil_append, List.length_append, List.length_singleton, Nat.add_sub_cancel]
          simpa only [hg, List.tail_nil] using hdrop.symm
        | cons e es =>
          simp only [kmswStepOfStep, hs, hg, State.addEdge, List.map_nil,
            List.nil_append, List.length_append, List.length_singleton, Nat.add_sub_cancel]
          simpa only [hg, List.tail_cons] using hdrop.symm

private theorem past_shift_LR_entry (w : ℕ → Fin 3) (t m : ℕ) :
    ∀ (i e : ℕ), (kmswStage (fun i => w (t + i)) m).LR[i]? = some e →
      (act w t :: (kmswStage w t).UR)[i]? = some (kmswShiftEdgeMapAll w t m e) ∨
        (act w t :: (kmswStage w t).UR).length ≤ i := by
  let ws := fun i => w (t + i)
  induction m with
  | zero =>
    intro i e he
    have he' : ([0] : List ℕ)[i]? = some e := he
    have hi : i = 0 := by
      have hbound := (List.getElem?_eq_some_iff.mp he').1
      simp only [List.length_singleton] at hbound
      omega
    subst i
    have he0 : e = 0 := by simpa using he'.symm
    subst e
    exact Or.inl rfl
  | succ m ih =>
    let sh := kmswStage ws m
    let gl := kmswStage w (t + m)
    let ep := kmswShiftEdgeMapAll w t m
    let en := kmswShiftEdgeMapAll w t (m + 1)
    have hsh : kmswStage ws (m + 1) = kmswStepOfStep sh (kmswCodeStep (ws m)) := rfl
    have hgl : kmswStage w (t + (m + 1)) =
        kmswStepOfStep gl (kmswCodeStep (ws m)) := by rw [Nat.add_succ]; rfl
    have hOld (i e : ℕ) (he : sh.LR[i]? = some e) :
        (act w t :: (kmswStage w t).UR)[i]? = some (en e) ∨
          (act w t :: (kmswStage w t).UR).length ≤ i := by
      have hmem : e ∈ sh.LR := List.mem_of_getElem? he
      have heb : e < sh.nextEdge :=
        (kmswStage_boundary_ids_lt_nextEdge ws m).2 e
          (by simp only [List.mem_append]; exact Or.inr hmem)
      dsimp only [en]
      rw [kmswShiftEdgeMapAll_extend w t m e heb]
      exact ih i e he
    intro i e he
    change (act w t :: (kmswStage w t).UR)[i]? = some (en e) ∨
      (act w t :: (kmswStage w t).UR).length ≤ i
    change (kmswStage ws (m + 1)).LR[i]? = some e at he
    rw [hsh] at he
    cases hc : kmswCodeStep (ws m) with
    | up => exact hOld i e (by simpa only [hc, kmswStepOfStep, State.addEdge] using he)
    | left =>
      cases hp : sh.UL.dropLast.reverse <;>
        exact hOld i e (by simpa only [hc, kmswStepOfStep, hp, State.addEdge] using he)
    | down =>
      cases hs : sh.UR with
      | cons a as => exact hOld i e (by simpa only [hc, kmswStepOfStep, hs] using he)
      | nil =>
        have he' : (sh.LR ++ [sh.nextEdge])[i]? = some e := by
          simpa only [hc, kmswStepOfStep, hs, State.addEdge] using he
        by_cases hi : i < sh.LR.length
        · exact hOld i e (by rw [List.getElem?_append_left hi] at he'; exact he')
        · have hilen : i = sh.LR.length := by
            have hbound := (List.getElem?_eq_some_iff.mp he').1
            simp only [List.length_append, List.length_singleton] at hbound
            omega
          subst i
          have heq : e = sh.nextEdge := by
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at he'
            simpa using he'.symm
          subst e
          have hres : gl.UR = (kmswStage w t).UR.drop (sh.LR.length - 1) := by
            have hh := past_shift_UR_suffix w t m
            change gl.UR = sh.UR.map ep ++ _ at hh
            simpa only [hs, List.map_nil, List.nil_append] using hh
          have hlen : 1 ≤ sh.LR.length := by
            have hh := kmswStage_LR_length ws m
            have hm := runningMin_le (R ws) m 0 (Nat.zero_le m)
            have hz : R ws 0 = 0 := by simp [R]
            change minR ws m ≤ R ws 0 at hm
            change ((sh.LR.length : ℕ) : ℤ) = _ at hh
            omega
          cases hg : gl.UR with
          | cons f fs =>
            have hnew : en sh.nextEdge = f := by
              change kmswShiftNextEdgeMap sh gl (kmswCodeStep (ws m)) ep _ = _
              simp [hc, kmswShiftNextEdgeMap, hs, hg, kmswShiftDownMismatchEdgeMap]
            left
            rw [hnew, show sh.LR.length = (sh.LR.length - 1) + 1 by omega]
            change (kmswStage w t).UR[sh.LR.length - 1]? = some f
            have hh : ((kmswStage w t).UR.drop (sh.LR.length - 1))[0]? = some f := by
              rw [← hres, hg]
              rfl
            simpa only [List.getElem?_drop, Nat.add_zero] using hh
          | nil =>
            right
            have hd : (kmswStage w t).UR.drop (sh.LR.length - 1) = [] :=
              hres.symm.trans hg
            have hb := List.drop_eq_nil_iff.mp hd
            simp only [List.length_cons]
            omega

private theorem pending_eq_shifted_positive_label (w : ℕ → Fin 3) (t : ℕ)
    (hs : BoundaryHitWitnesses (fun i => w (t + i))) {j : ℕ} (hj : 1 ≤ j)
    (hbound : j ≤ (CutConverse.pendingVertices (kmswStage w t)).length) :
    (CutConverse.pendingVertices (kmswStage w t))[j - 1]? =
        some (shiftLimitVertex w t
          ⟨boundaryVertex (fun i => w (t + i)) hs (j : ℤ)⟩).id := by
  let ws := fun i => w (t + i)
  let e := kmswRightBoundaryEdge ws (j - 1)
  have hedata : EdgePresent ws e ∧ edgeEast ws e = boundaryVertex ws hs (j : ℤ) := by
    by_cases hj1 : j = 1
    · subst j
      dsimp [e]
      rw [kmswRightBoundaryEdge_zero, boundaryVertex_one]
      refine ⟨?_, ?_⟩
      · exact kmswShift_active_edge_present_limit w t 0
      · exact (edge_endpoints_eq ws (j := 0) (e := 0) (by change 0 < 1; omega)).2.symm
    · have hi : 1 ≤ j - 1 := by omega
      have hh := boundaryVertex_right_edge_present_source ws hs hi
      have hc : ((j - 1 : ℕ) : ℤ) + 1 = (j : ℤ) := by omega
      exact ⟨hh.1, by simpa only [hc] using hh.2.2⟩
  obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually ws hs.R_unbounded_below (j - 1)
  have hentry : (kmswStage ws N).LR[j - 1]? = some e := hN N le_rfl
  have heb : e < (kmswStage ws N).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge ws N).2 e
      (by simp only [List.mem_append]; exact Or.inr (List.mem_of_getElem? hentry))
  let ef : {e : ℕ // EdgePresent ws e} := ⟨e, hedata.1⟩
  have hinc := (shiftLimitEdge_incidence w t ef).2
  have heq : shiftLimitEdge w t ef = kmswShiftEdgeMapAll w t N e :=
    shiftLimitEdge_eq w t N ef heb
  change edgeEast w (shiftLimitEdge w t ef) =
    (shiftLimitVertex w t ⟨edgeEast ws e⟩).id at hinc
  rw [heq, hedata.2] at hinc
  have hfront : (act w t :: (kmswStage w t).UR).map (edgeEast w) =
      CutConverse.pendingVertices (kmswStage w t) := by
    change edgeEast w (act w t) :: (kmswStage w t).UR.map (edgeEast w) =
      (kmswStage w t).east (act w t) :: (kmswStage w t).UR.map (kmswStage w t).east
    rw [← (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl t))).2]
    congr 1
    apply List.map_congr_left
    intro f hf
    have hfb : f < (kmswStage w t).nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge w t).2 f
        (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hf)))
    exact (edge_endpoints_eq w hfb).2.symm
  rcases past_shift_LR_entry w t N (j - 1) e hentry with hidx | hfresh
  · have hh := congrArg (Option.map (edgeEast w)) hidx
    rw [← List.getElem?_map, hfront] at hh
    simpa only [Option.map_some, hinc] using hh
  · have hlen := congrArg List.length hfront
    simp only [List.length_map, List.length_cons] at hlen hfresh
    omega

/-- Exact past-prefix characterization of the left-hit interface indices.
This supplies the converse cutoff identification in plan B.2 -/
theorem leftPastFrontierIndices_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h (-1) → w i = p i) :
    leftPastFrontierIndices (boundaryHitTime w h (-1)) p =
      leftFrontierIndices w h hs := by
  rw [← past_indices_congr hp]
  ext j
  constructor
  · rintro ⟨hj, u, hu, hr⟩
    have hlen := (List.getElem?_eq_some_iff.mp hu).1
    have hb : j ≤ (CutConverse.pendingVertices
        (kmswStage w (boundaryHitTime w h (-1)))).length := by omega
    have he := pending_eq_shifted_positive_label w (boundaryHitTime w h (-1)) hs hj hb
    change _ = some (leftFrontierVertex w h hs j).id at he
    have hu' : u = (leftFrontierVertex w h hs j).id := Option.some.inj (hu.symm.trans he)
    rw [hu'] at hr
    obtain ⟨n, q, _, hq⟩ := hr
    refine ⟨hj, ?_⟩
    have hz : boundaryPresentVertex w h 0 = (⟨0⟩ : PresentVertex w) := by
      simp only [boundaryPresentVertex, boundaryVertex_zero]
    rw [hz]
    exact ⟨q, hq⟩
  · intro hj
    refine ⟨hj.1, (leftFrontierVertex w h hs j).id,
      leftFrontierIndices_pending w h hs hj, ?_⟩
    have hr := hj.2
    simp only [EarlyReachable, boundaryPresentVertex] at hr
    obtain ⟨q, hq⟩ := hr
    exact ⟨q.length, q, rfl, hq⟩

private theorem sdp_coefficient_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h (-1) → w i = p i)
    {j : ℕ} (hj : j ∈ leftFrontierIndices w h hs) :
    leftPastSdpCoefficient (boundaryHitTime w h (-1)) p j =
      ((earlySdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j)).toNat : ℤ) := by
  obtain ⟨u, hu, he, _⟩ := leftFrontier_coefficients_prefix w h hs hj p hp
  unfold leftPastSdpCoefficient
  rw [hu]
  change ((earlySdp p _ ⟨0⟩ ⟨u⟩).toNat : ℤ) = _
  rw [← he]

private theorem ldp_coefficient_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h (-1) → w i = p i)
    {j : ℕ} (hj : j ∈ leftFrontierIndices w h hs) :
    leftPastLdpCoefficient (boundaryHitTime w h (-1)) p j =
      (((earlyLdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j)).unbotD 0 : ℕ) : ℤ) := by
  obtain ⟨u, hu, _, he⟩ := leftFrontier_coefficients_prefix w h hs hj p hp
  unfold leftPastLdpCoefficient
  rw [hu]
  change (((earlyLdp p _ ⟨0⟩ ⟨u⟩).unbotD 0 : ℕ) : ℤ) = _
  rw [← he]



theorem leftPastSdpEnvelope_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannSDP (boundaryPresentVertex _ hs) Xs)
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h (-1) → w i = p i) :
    X 0 - X (-1) = leftPastSdpEnvelope (boundaryHitTime w h (-1)) p
      (fun j => Xs (j : ℤ)) := by
  rw [leftFrontier_sdp_busemann w h hs X Xs hX hXs]
  unfold leftPastSdpEnvelope
  rw [leftPastFrontierIndices_eq w h hs p hp]
  congr 1
  exact Set.image_congr fun j hj => by rw [sdp_coefficient_eq w h hs p hp hj]



theorem leftPastLdpEnvelope_eq (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded (w := fun i => w (boundaryHitTime w h (-1) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannLDP hbs (boundaryPresentVertex _ hs) Xs)
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h (-1) → w i = p i) :
    X 0 - X (-1) = leftPastLdpEnvelope (boundaryHitTime w h (-1)) p
      (fun j => Xs (j : ℤ)) := by
  rw [leftFrontier_ldp_busemann w h hs hb hbs X Xs hX hXs]
  unfold leftPastLdpEnvelope
  rw [leftPastFrontierIndices_eq w h hs p hp]
  congr 1
  exact Set.image_congr fun j hj => by rw [ldp_coefficient_eq w h hs p hp hj]

private theorem ae_comp_left_frontier_hit {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂iidCodeMeasure, p (codeShift (codeFstFirstHit (-1) ω).toNat ω) := by
  apply ae_of_ae_map
    (measurable_codeShift_toNat _ (measurableSet_codePast_codeFstFirstHit_eq (-1))).aemeasurable
  rw [map_codeShift_codeFstFirstHit]
  exact hp

private theorem left_frontier_codeShift_future (ω : ℕ → Fin 3) (t : ℕ) :
    (fun i => codeShift t ω (i + 1)) = (fun i => ω ((t + i) + 1)) := by
  funext i
  change (if i + 1 = 0 then 0 else ω (t + (i + 1))) = ω ((t + i) + 1)
  rw [ite_eq_right (by omega : ¬ i + 1 = 0)]
  rfl

private theorem ae_left_frontier_ldp_data :
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

/-- Past-measurable shortest frontier decomposition of D₀ at τ₋₁, exactly
`hfrontL` in `busemannSDPMeasurableVersion_ind_of_LR` (plan B.2;
is not counted as a paper result; F1/F4 remain. -/
theorem busemannSDPMeasurableVersion_left_frontier :
    ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂iidCodeMeasure,
        busemannSDPMeasurableVersion ω 0 - busemannSDPMeasurableVersion ω (0 - 1) =
          F (codeFstFirstHit (-1) ω).toNat
            (codePastVector (codeFstFirstHit (-1)) ω)
            (fun j => busemannSDPMeasurableVersion
              (codeShift (codeFstFirstHit (-1) ω).toNat ω) (j : ℤ)) := by
  refine ⟨leftPastSdpEnvelope, measurable_leftPastSdpEnvelope, ?_⟩
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion,
    ae_comp_left_frontier_hit iidCodes_ae_busemannSDPMeasurableVersion] with ω hdata hsdata
  obtain ⟨h, hX⟩ := hdata
  have hhit := codeFstFirstHit_eq_boundaryHitTime ω h (by omega : (-1 : ℤ) ≤ -1)
  have ht : (codeFstFirstHit (-1) ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h (-1) := by
    rw [hhit, ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [left_frontier_codeShift_future] at hsdata
  obtain ⟨hs, hXs⟩ := hsdata
  apply leftPastSdpEnvelope_eq (fun i => ω (i + 1)) h hs _ _ hX hXs
  intro i hi
  simp only [codePastVector, hhit, ENat.natCast_lt_natCast, ite_eq_left hi]

/-- Past-measurable longest frontier decomposition of D₀ at τ₋₁, exactly
`hfrontL` in `busemannLDPMeasurableVersion_ind_of_LR` (plan B.2;
is not counted as a paper result; F1/F4 remain. -/
theorem busemannLDPMeasurableVersion_left_frontier :
    ∃ F : ℕ → (ℕ → Fin 3) → (ℕ → ℤ) → ℤ,
      (∀ k, Measurable (Function.uncurry (F k))) ∧
      ∀ᵐ ω ∂iidCodeMeasure,
        busemannLDPMeasurableVersion ω 0 - busemannLDPMeasurableVersion ω (0 - 1) =
          F (codeFstFirstHit (-1) ω).toNat
            (codePastVector (codeFstFirstHit (-1)) ω)
            (fun j => busemannLDPMeasurableVersion
              (codeShift (codeFstFirstHit (-1) ω).toNat ω) (j : ℤ)) := by
  refine ⟨leftPastLdpEnvelope, measurable_leftPastLdpEnvelope, ?_⟩
  filter_upwards [ae_left_frontier_ldp_data,
    ae_comp_left_frontier_hit ae_left_frontier_ldp_data] with ω hdata hsdata
  obtain ⟨hb, h, hX⟩ := hdata
  have hhit := codeFstFirstHit_eq_boundaryHitTime ω h (by omega : (-1 : ℤ) ≤ -1)
  have ht : (codeFstFirstHit (-1) ω).toNat =
      boundaryHitTime (fun i => ω (i + 1)) h (-1) := by
    rw [hhit, ENat.toNat_natCast]
  rw [ht] at hsdata ⊢
  rw [left_frontier_codeShift_future] at hsdata
  obtain ⟨hbs, hs, hXs⟩ := hsdata
  apply leftPastLdpEnvelope_eq (fun i => ω (i + 1)) h hs hb hbs _ _ hX hXs
  intro i hi
  simp only [codePastVector, hhit, ENat.natCast_lt_natCast, ite_eq_left hi]

end DirectedDistances.Recursive
