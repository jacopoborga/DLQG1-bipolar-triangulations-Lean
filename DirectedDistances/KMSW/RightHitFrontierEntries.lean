module

public import DirectedDistances.KMSW.InftyCutEntry
public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.KMSW.StageFrontier
public import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.KMSW.LeftHitFrontierEntries
import DirectedDistances.KMSW.LeftStationaryGeometry
import DirectedDistances.KMSW.BoundaryEnumeration
import DirectedDistances.KMSW.WalkRecordCounts

/-! # Frontier labels at a right hit

Helpers toward the frontier decomposition in the `item-busemann-ind`
crossing-vertex identification with a negative shifted boundary label and
the label's ordered position in the cutoff UL frontier are proved below. -/

public section
namespace DirectedDistances.KMSW

/-- At the first right hit, every vertex with an early incoming edge (or the
root) and a late outgoing edge is incident to the cutoff UL frontier. This is
the stage-frontier part of the frontier-label coverage helper for the
`item-busemann-ind` reduction (`lem-directed-contain`, -/
theorem rightHit_crossing_vertex_on_UL (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (u : PresentVertex w)
    (hin : u = ⟨boundaryVertex w h 0⟩ ∨
      ∃ e, ∃ he : EdgePresent w e,
        actTime w e he < boundaryHitTime w h 1 ∧ edgeEast w e = u.id)
    (hout : ∃ f, ∃ hf : EdgePresent w f,
      boundaryHitTime w h 1 ≤ actTime w f hf ∧ edgeWest w f = u.id) :
    ∃ g, g ∈ (kmswStage w (boundaryHitTime w h 1)).UL ∧
      ((kmswStage w (boundaryHitTime w h 1)).west g = u.id ∨
        (kmswStage w (boundaryHitTime w h 1)).east g = u.id) := by
  let t := boundaryHitTime w h 1
  have ht : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    have hhit := boundaryHitTime_right_spec w h (by norm_num : (1 : ℤ) ≤ 1)
    change R w t = -(1 : ℤ) at hhit
    rw [ht0] at hhit
    simp [R] at hhit
  rcases hout with ⟨f, hf, hft, hfu⟩
  have hentry : ∃ g, g ∈ (kmswStage w t).UL ++ (kmswStage w t).UR ∧
      ((kmswStage w t).west g = u.id ∨ (kmswStage w t).east g = u.id) := by
    rcases hin with hroot | ⟨e, he, het, heu⟩
    · have hu0 : u.id = 0 := by
        have hid := congrArg PresentVertex.id hroot
        simpa [boundaryVertex_zero] using hid
      have he0lt : 0 < (kmswStage w 0).nextEdge := by
        simp [kmswStage, kmswInit]
      have he0present : (kmswStage w 0).present 0 = true := by
        simp [kmswStage, kmswInit]
      have he0 : EdgePresent w 0 :=
        EdgePresent.of_stage_present he0lt he0present
      have he0west : edgeWest w 0 = 0 := by
        simp [edgeWest, kmswStage, kmswInit]
      have htime0 : actTime w 0 he0 = 0 :=
        (actTime_eq_iff w 0 he0 0).2 rfl
      exact cut_entry_frontier_of_shared_endpoint w he0 hf
        (by rw [htime0]; exact ht) hft
        (Or.inl (he0west.trans hu0.symm)) hfu
    · exact cut_entry_frontier_of_shared_endpoint w he hf het hft
        (Or.inr heu) hfu
  obtain ⟨g, hg, hend⟩ := hentry
  have hUR : (kmswStage w t).UR = [] :=
    boundaryHit_right_UR_empty w h (by norm_num : (1 : ℤ) ≤ 1)
  rcases List.mem_append.mp hg with hgUL | hgUR
  · exact ⟨g, hgUL, hend⟩
  · simp [hUR] at hgUR

/-- A late outgoing edge at a right hit starts at the limit image of a shifted
active initial vertex. Identifying this active initial vertex with one of the
negative shifted boundary labels is the remaining frontier enumeration step -/
theorem rightHit_late_outgoing_is_shifted_activeInitial (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (u : PresentVertex w)
    (hout : ∃ f, ∃ hf : EdgePresent w f,
      boundaryHitTime w h 1 ≤ actTime w f hf ∧ edgeWest w f = u.id) :
    ∃ n : ℕ, u = shiftLimitVertex w (boundaryHitTime w h 1)
      ⟨activeInitial (fun i => w (boundaryHitTime w h 1 + i)) n⟩ := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  rcases hout with ⟨f, hf, hft, hfu⟩
  obtain ⟨ef, hmap⟩ := (shiftLimitEdge_image_iff w t f hf).2 hft
  let n := actTime ws ef.val ef.property
  have hwestShift : edgeWest ws ef.val = activeInitial ws n := by
    dsimp [activeInitial, n]
    exact congrArg (edgeWest ws) (actTime_spec ws ef.val ef.property)
  have hinc := shiftLimitEdge_incidence w t ef
  have hwest : edgeWest w f =
      (shiftLimitVertex w t ⟨edgeWest ws ef.val⟩).id := by
    calc
      edgeWest w f = edgeWest w (shiftLimitEdge w t ef) := by rw [hmap]
      _ = (shiftLimitVertex w t ⟨edgeWest ws ef.val⟩).id := hinc.1
  have hsource : (shiftLimitVertex w t ⟨edgeWest ws ef.val⟩).id =
      (shiftLimitVertex w t ⟨activeInitial ws n⟩).id := by
    exact congrArg PresentVertex.id
      (congrArg (shiftLimitVertex w t) (congrArg PresentVertex.mk hwestShift))
  have hid : u.id = (shiftLimitVertex w t ⟨activeInitial ws n⟩).id := by
    calc
      u.id = edgeWest w f := hfu.symm
      _ = (shiftLimitVertex w t ⟨edgeWest ws ef.val⟩).id := hwest
      _ = (shiftLimitVertex w t ⟨activeInitial ws n⟩).id := hsource
  refine ⟨n, ?_⟩
  cases u with
  | mk uid =>
    apply congrArg PresentVertex.mk
    exact hid

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

/-- Each negative shifted boundary label maps either to an endpoint of the
right-hit UL frontier or to a vertex with no early incident edge. This is a
frontier-candidate form of past determination for the `item-busemann-ind`
it does not identify the label's position in the ordered UL list. -/
theorem rightHit_shifted_negative_label_frontier_or_no_early_edge
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i =>
      w (boundaryHitTime w h 1 + i))) (j : ℕ) (hj : 1 ≤ j) :
    let t := boundaryHitTime w h 1
    let ws := fun i => w (t + i)
    let u : PresentVertex w :=
      shiftLimitVertex w t ⟨boundaryVertex ws hs (-(j : ℤ))⟩
    (∃ e, e ∈ (kmswStage w t).UL ∧
      ((kmswStage w t).west e = u.id ∨ (kmswStage w t).east e = u.id)) ∨
    (∀ e (he : EdgePresent w e), actTime w e he < t →
      edgeWest w e ≠ u.id ∧ edgeEast w e ≠ u.id) := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let n := boundaryHitTime ws hs (-(j : ℤ))
  have hjneg : (-(j : ℤ)) ≤ -1 := by omega
  have hlabel : boundaryVertex ws hs (-(j : ℤ)) = activeInitial ws n :=
    boundaryVertex_left_hit_eq ws hs hjneg
  have hshiftLabel : shiftLimitVertex w t
      ⟨boundaryVertex ws hs (-(j : ℤ))⟩ =
      ⟨activeInitial w (t + n)⟩ := by
    calc
      shiftLimitVertex w t ⟨boundaryVertex ws hs (-(j : ℤ))⟩ =
          shiftLimitVertex w t ⟨activeInitial ws n⟩ :=
            congrArg (shiftLimitVertex w t) (congrArg PresentVertex.mk hlabel)
      _ = ⟨activeInitial w (t + n)⟩ :=
            shiftLimitVertex_activeInitial_rightHitEntries w t n
  have hfront : UpperFrontierEndpoint (kmswStage w t)
      (activeInitial w (t + n)) := by
    have hstage := (kmswStage_act_endpoint_since w
      (t := t) (m := t + n + 1) (n := t + n) (by omega) (by omega)).1
    rw [← CutConverse.activeInitial_eq w (t + n)] at hstage
    exact hstage
  have hUR : (kmswStage w t).UR = [] :=
    boundaryHit_right_UR_empty w h (by norm_num : (1 : ℤ) ≤ 1)
  have hresult :
      (∃ e, e ∈ (kmswStage w t).UL ∧
        ((kmswStage w t).west e = activeInitial w (t + n) ∨
          (kmswStage w t).east e = activeInitial w (t + n))) ∨
      (∀ e (he : EdgePresent w e), actTime w e he < t →
        edgeWest w e ≠ activeInitial w (t + n) ∧
          edgeEast w e ≠ activeInitial w (t + n)) := by
    rcases hfront with ⟨e, he, hend⟩ | hfresh
    · rcases List.mem_append.mp he with heUL | heUR
      · exact Or.inl ⟨e, heUL, hend⟩
      · simp [hUR] at heUR
    · right
      intro e he hearly
      have halloc : e < (kmswStage w t).nextEdge := by
        rw [actTime_spec w e he]
        exact act_lt_nextEdge w (Nat.le_of_lt hearly)
      have hb := kmswStage_endpoints_lt_nextVertex w t e halloc
      rw [(edge_endpoints_eq w halloc).1, (edge_endpoints_eq w halloc).2] at hb
      constructor
      · intro heq
        have : edgeWest w e < (kmswStage w t).nextVertex := hb.1
        omega
      · intro heq
        have : edgeEast w e < (kmswStage w t).nextVertex := hb.2
        omega
  simpa only [t, ws, hshiftLabel] using hresult

private theorem shiftVertexMapAll_old_image_lowerBoundary_rightEntries
    (w : ℕ → Fin 3) (t m : ℕ) :
    ∀ v, v < (kmswStage (fun i => w (t + i)) m).nextVertex →
      kmswShiftVertexMapAll w t m v < (kmswStage w t).nextVertex →
      ∃ n e, (e ∈ (kmswStage (fun i => w (t + i)) n).LL ∨
        e ∈ (kmswStage (fun i => w (t + i)) n).LR) ∧
        ((kmswStage (fun i => w (t + i)) n).west e = v ∨
          (kmswStage (fun i => w (t + i)) n).east e = v) := by
  let ws := fun i => w (t + i)
  induction m with
  | zero =>
    intro v hv _
    have hv' : v = 0 ∨ v = 1 := by change v < 2 at hv; omega
    refine ⟨0, 0, Or.inr (by change 0 ∈ [0]; simp), ?_⟩
    rcases hv' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | succ m ih =>
    intro v hv hmap
    by_cases hold : v < (kmswStage ws m).nextVertex
    · apply ih v hold
      rw [← kmswShiftVertexMapAll_extend w t m v hold]
      exact hmap
    · let sh := kmswStage ws m
      let gl := kmswStage w (t + m)
      have hstep : kmswStage ws (m + 1) =
          kmswStepOfStep sh (kmswCodeStep (ws m)) := rfl
      have hnext : (kmswStage w t).nextVertex ≤ gl.nextVertex :=
        CutConverse.nextVertex_mono w (Nat.le_add_right t m)
      change v < (kmswStage ws (m + 1)).nextVertex at hv
      rw [hstep] at hv
      cases hc : kmswCodeStep (ws m) with
      | up =>
        have hvEq : v = sh.nextVertex := by
          simp only [hc, kmswStepOfStep, State.addEdge] at hv
          change ¬ v < sh.nextVertex at hold
          omega
        subst v
        have hnew : kmswShiftVertexMapAll w t (m + 1) sh.nextVertex =
            gl.nextVertex := by
          change kmswShiftNextVertexMap sh gl (kmswCodeStep (ws m))
            (kmswShiftVertexMapAll w t m) sh.nextVertex = _
          simp [hc, kmswShiftNextVertexMap, kmswShiftUpVertexMap]
        rw [hnew] at hmap
        omega
      | left =>
        cases hp : sh.UL.dropLast.reverse with
        | nil =>
          have hvEq : v = sh.nextVertex := by
            simp only [hc, kmswStepOfStep, hp, State.addEdge] at hv
            change ¬ v < sh.nextVertex at hold
            omega
          refine ⟨m + 1, sh.nextEdge + 1, Or.inl ?_, Or.inl ?_⟩
          · change sh.nextEdge + 1 ∈ (kmswStage ws (m + 1)).LL
            rw [hstep]
            simp [hc, kmswStepOfStep, hp, State.addEdge]
          · change (kmswStage ws (m + 1)).west (sh.nextEdge + 1) = v
            rw [hstep]
            simp only [hc, kmswStepOfStep, hp, State.addEdge, ↓reduceIte]
            exact hvEq.symm
        | cons e es =>
          simp only [hc, kmswStepOfStep, hp, State.addEdge] at hv
          exact (hold hv).elim
      | down =>
        cases hp : sh.UR with
        | nil =>
          have hvEq : v = sh.nextVertex := by
            simp only [hc, kmswStepOfStep, hp, State.addEdge] at hv
            change ¬ v < sh.nextVertex at hold
            omega
          refine ⟨m + 1, sh.nextEdge, Or.inr ?_, Or.inr ?_⟩
          · change sh.nextEdge ∈ (kmswStage ws (m + 1)).LR
            rw [hstep]
            simp [hc, kmswStepOfStep, hp, State.addEdge]
          · change (kmswStage ws (m + 1)).east sh.nextEdge = v
            rw [hstep]
            simp only [hc, kmswStepOfStep, hp, State.addEdge, ↓reduceIte]
            exact hvEq.symm
        | cons e es =>
          simp only [hc, kmswStepOfStep, hp] at hv
          exact (hold hv).elim

private theorem shiftLimitVertex_old_image_boundary_rightEntries
    (w : ℕ → Fin 3) (t : ℕ)
    (hs : BoundaryHitWitnesses (fun i => w (t + i)))
    (a : PresentVertex (fun i => w (t + i)))
    (ha : kmswVertexAllocated (fun i => w (t + i)) a)
    (hold : (shiftLimitVertex w t a).id < (kmswStage w t).nextVertex) :
    ∃ k : ℤ, a = ⟨boundaryVertex (fun i => w (t + i)) hs k⟩ := by
  obtain ⟨m, hm⟩ := ha
  rw [shiftLimitVertex_eq w t m a hm] at hold
  obtain ⟨k, hk⟩ := boundaryVertex_covers_lowerBoundary (fun i => w (t + i)) hs a.id
    (shiftVertexMapAll_old_image_lowerBoundary_rightEntries w t m a.id hm hold)
  refine ⟨k, ?_⟩
  cases a
  exact congrArg PresentVertex.mk hk.symm

private theorem rightHit_crossing_activeEast_fresh_rightEntries
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    ∀ e (he : EdgePresent w e),
      actTime w e he < boundaryHitTime w h 1 →
      edgeEast w e ≠ (kmswStage w (boundaryHitTime w h 1)).east
        (act w (boundaryHitTime w h 1)) := by
  let t := boundaryHitTime w h 1
  have htpos : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    have hhit := boundaryHitTime_right_spec w h (by norm_num : (1 : ℤ) ≤ 1)
    change R w t = -1 at hhit
    rw [ht0] at hhit
    simp [R] at hhit
  have ht : t = (t - 1) + 1 := by omega
  have hcoord (c : Fin 3) :
      -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).2 ∧
        (RandomWalk.lazyTwoDimensionalStep c).2 ≤ 1 := by
    fin_cases c <;> norm_num [RandomWalk.lazyTwoDimensionalStep]
  have hstrict : ∀ j < t, R w t < R w j := by
    let hit := h.rightHit 1 (by norm_num : (1 : ℤ) ≤ 1)
    have hfind : t = Nat.find hit := by
      simp [t, boundaryHitTime]
    have hzero : R w 0 = 0 := by simp [R]
    have hchar := (strict_running_minimum_iff_first_hit (R w) hzero
      (by
        intro n
        have hstep : |R w (n + 1) - R w n| ≤ 1 := by
          have hR : R w (n + 1) = R w n +
              (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
            Finset.sum_range_succ _ _
          rw [hR]
          have hdiff : R w n +
              (RandomWalk.lazyTwoDimensionalStep (w n)).2 - R w n =
                (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by omega
          rw [hdiff]
          exact abs_le.mpr (hcoord (w n))
        exact hstep)
      t t (-1) (by norm_num) (h.rightHit 1 (by norm_num : (1 : ℤ) ≤ 1))).2
      ⟨le_rfl, boundaryHitTime_right_spec w h (by norm_num : (1 : ℤ) ≤ 1), hfind⟩
    intro j hj
    exact (Finset.mem_filter.mp hchar.1).2 j hj
  let r := t - 1
  have hrt : r + 1 = t := by dsimp [r]; omega
  have hprev : R w r = 0 := by
    have hhit := boundaryHitTime_right_spec w h (by norm_num : (1 : ℤ) ≤ 1)
    have hsum : R w (r + 1) = R w r +
        (RandomWalk.lazyTwoDimensionalStep (w r)).2 := Finset.sum_range_succ _ _
    have hstep : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w r)).2 ∧
        (RandomWalk.lazyTwoDimensionalStep (w r)).2 ≤ 1 := hcoord (w r)
    have hrec := hstrict r (by dsimp [r]; omega)
    rw [← hrt, hsum] at hrec
    change R w t = -1 at hhit
    rw [← hrt, hsum] at hhit
    omega
  have hmin : minR w r = 0 := by
    obtain ⟨i, hi, hmi⟩ := runningMin_attained (R w) r
    have hle := runningMin_le (R w) r r (le_rfl)
    change minR w r ≤ R w r at hle
    change minR w r = R w i at hmi
    have hri : 0 ≤ R w i := by
      by_cases hir : i = r
      · subst i; exact hprev ▸ le_rfl
      · have hbefore := hstrict i (by omega)
        rw [boundaryHitTime_right_spec w h (by norm_num : (1 : ℤ) ≤ 1)] at hbefore
        omega
    rw [hprev] at hle
    omega
  have hUR : (kmswStage w r).UR = [] := by
    have hlen := kmswStage_UR_length w r
    have hlen0 : ((kmswStage w r).UR.length : ℤ) = 0 := by
      rw [hlen, hprev, hmin]
      norm_num
    have : (kmswStage w r).UR.length = 0 := by exact_mod_cast hlen0
    exact List.length_eq_zero_iff.mp this
  have hw : w r = 2 := by
    have hsum : R w (r + 1) = R w r +
        (RandomWalk.lazyTwoDimensionalStep (w r)).2 := Finset.sum_range_succ _ _
    have hhit := boundaryHitTime_right_spec w h (by norm_num : (1 : ℤ) ≤ 1)
    change R w t = -1 at hhit
    rw [← hrt, hsum, hprev] at hhit
    have hdelta : (RandomWalk.lazyTwoDimensionalStep (w r)).2 = -1 := by omega
    have hc (c : Fin 3) :
        (RandomWalk.lazyTwoDimensionalStep c).2 = -1 → c = 2 := by
      intro hd
      fin_cases c
      · simp [RandomWalk.lazyTwoDimensionalStep] at hd
      · simp [RandomWalk.lazyTwoDimensionalStep] at hd
      · rfl
    exact hc (w r) hdelta
  have heast : (kmswStage w (r + 1)).east (act w (r + 1)) =
      (kmswStage w r).nextVertex := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      hUR, State.addEdge]
  intro e he hearly heq
  have htime := actTime_spec w e he
  have her : actTime w e he ≤ r := by dsimp [r]; omega
  have heb : e < (kmswStage w r).nextEdge := by
    rw [htime]
    exact act_lt_nextEdge w her
  have hb := (kmswStage_endpoints_lt_nextVertex w r e heb).2
  rw [(edge_endpoints_eq w heb).2] at hb
  change edgeEast w e = (kmswStage w t).east (act w t) at heq
  rw [← hrt, heast] at heq
  omega

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

/-- Nonpositive shifted boundary labels occupy the corresponding position of
the cutoff UL frontier's westward list, unless the label is fresh beyond the
cutoff (a disjunction; see `rightHit_shifted_negative_label_ordered_frontier_exclusive`
for the exclusive form). A fresh label has no early incident edge. Helper for the
`item-busemann-ind` frontier decomposition (`lem-directed-contain`, -/
theorem rightHit_shifted_negative_label_ordered_frontier_or_no_early_edge
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses
      (fun i => w (boundaryHitTime w h 1 + i))) :
    let t := boundaryHitTime w h 1
    let ws := fun i => w (t + i)
    let F := (kmswStage w t).UL.reverse.map (kmswStage w t).west
    ∀ j : ℕ,
      F[j]? = some (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∨
      ∀ e, ∀ he : EdgePresent w e, actTime w e he < t →
        edgeWest w e ≠ (shiftLimitVertex w t
          ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∧
        edgeEast w e ≠ (shiftLimitVertex w t
          ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let F := (kmswStage w t).UL.reverse.map (kmswStage w t).west
  let τ : ℕ → ℕ := fun j =>
    if j = 0 then 0 else boundaryHitTime ws hs (-(j : ℤ))
  change ∀ j : ℕ,
    F[j]? = some (shiftLimitVertex w t
      ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∨
    ∀ e, ∀ he : EdgePresent w e, actTime w e he < t →
      edgeWest w e ≠ (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∧
      edgeEast w e ≠ (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id
  have hF : F = CutConverse.westStack w t := rfl
  intro j
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
  rcases hcore with ⟨hj, hstack⟩ | ⟨hj, hstack, hfresh⟩
  · left
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
  · right
    intro e he hearly
    have hid := congrArg PresentVertex.id hvertex
    have hfresh' : (kmswStage w t).nextVertex ≤
        (shiftLimitVertex w t ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id := by
      rw [hid]
      exact hfresh
    have heb : e < (kmswStage w t).nextEdge := by
      rw [actTime_spec w e he]
      exact act_lt_nextEdge w hearly.le
    have hb := kmswStage_endpoints_lt_nextVertex w t e heb
    rw [(edge_endpoints_eq w heb).1, (edge_endpoints_eq w heb).2] at hb
    constructor <;> intro heq <;> omega

/-- Exclusive form of
`rightHit_shifted_negative_label_ordered_frontier_or_no_early_edge`: the
nonpositive shifted label `x'_{-j}` is the `j`-th entry of the cutoff UL
frontier's westward list exactly when `j` is below its length; beyond the
length the label has no early incident edge. Hence an entry `F[j]? = some u`
always satisfies `u = x'_{-j}.id`, so the frontier index set is a function of
the past codes. Helper for the `item-busemann-ind` frontier decomposition
numbered paper result. -/
theorem rightHit_shifted_negative_label_ordered_frontier_exclusive
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses
      (fun i => w (boundaryHitTime w h 1 + i))) :
    let t := boundaryHitTime w h 1
    let ws := fun i => w (t + i)
    let F := (kmswStage w t).UL.reverse.map (kmswStage w t).west
    ∀ j : ℕ,
      (j < F.length ∧ F[j]? = some (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id) ∨
      (F.length ≤ j ∧ ∀ e, ∀ he : EdgePresent w e, actTime w e he < t →
        edgeWest w e ≠ (shiftLimitVertex w t
          ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∧
        edgeEast w e ≠ (shiftLimitVertex w t
          ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id) := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let F := (kmswStage w t).UL.reverse.map (kmswStage w t).west
  change ∀ j : ℕ,
    (j < F.length ∧ F[j]? = some (shiftLimitVertex w t
      ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id) ∨
    (F.length ≤ j ∧ ∀ e, ∀ he : EdgePresent w e, actTime w e he < t →
      edgeWest w e ≠ (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∧
      edgeEast w e ≠ (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id)
  intro j
  have hlen : F.length = (CutConverse.westStack w t).length := rfl
  have hT2 := rightHit_shifted_negative_label_ordered_frontier_or_no_early_edge w h hs j
  change F[j]? = some (shiftLimitVertex w t
      ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∨
    ∀ e, ∀ he : EdgePresent w e, actTime w e he < t →
      edgeWest w e ≠ (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id ∧
      edgeEast w e ≠ (shiftLimitVertex w t
        ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id at hT2
  by_cases hjF : j < F.length
  · left
    refine ⟨hjF, ?_⟩
    rcases hT2 with hget | hno
    · exact hget
    · -- Below the length, the stack invariant puts the label at `F[j]`.
      let τ : ℕ → ℕ := fun j =>
        if j = 0 then 0 else boundaryHitTime ws hs (-(j : ℤ))
      have hcore := rightEntries_shifted_left_hit_stack w t hs j
      change
        (j < (CutConverse.westStack w t).length ∧
          CutConverse.westStack w (t + τ j) = (CutConverse.westStack w t).drop j) ∨
        ((CutConverse.westStack w t).length ≤ j ∧
          CutConverse.westStack w (t + τ j) = [activeInitial w (t + τ j)] ∧
          (kmswStage w t).nextVertex ≤ activeInitial w (t + τ j)) at hcore
      rcases hcore with ⟨_, hstack⟩ | ⟨hj', _⟩
      · have hlabel : boundaryVertex ws hs (-(j : ℤ)) = activeInitial ws (τ j) := by
          by_cases hj0 : j = 0
          · subst j
            simp [τ, boundaryVertex_zero, activeInitial, act, edgeWest,
              kmswStage, kmswInit]
          · have hk : -(j : ℤ) ≤ -1 := by omega
            have ht : τ j = boundaryHitTime ws hs (-(j : ℤ)) := by simp [τ, hj0]
            rw [ht]
            exact boundaryVertex_left_hit_eq ws hs hk
        have hvertex : shiftLimitVertex w t
            ⟨boundaryVertex ws hs (-(j : ℤ))⟩ =
              ⟨activeInitial w (t + τ j)⟩ := by
          rw [hlabel]
          exact shiftLimitVertex_activeInitial_rightHitEntries w t (τ j)
        have hdrop : F.drop j =
            activeInitial w (t + τ j) :: (F.drop j).tail := by
          calc
            F.drop j = CutConverse.westStack w (t + τ j) := hstack.symm
            _ = activeInitial w (t + τ j) ::
                (CutConverse.westStack w (t + τ j)).tail :=
              rightEntries_westStack_head w (t + τ j)
            _ = activeInitial w (t + τ j) :: (F.drop j).tail := by
              have hF : F = CutConverse.westStack w t := rfl
              congr 1
              rw [hF, hstack]
        have hgetval : F[j] = activeInitial w (t + τ j) := by
          have hh := List.drop_eq_getElem_cons hjF
          rw [hdrop] at hh
          exact (List.cons.inj hh).1.symm
        have hid : (shiftLimitVertex w t
            ⟨boundaryVertex ws hs (-(j : ℤ))⟩).id =
            activeInitial w (t + τ j) := by
          simpa using congrArg PresentVertex.id hvertex
        rw [hid]
        exact List.getElem?_eq_some_iff.mpr ⟨hjF, hgetval⟩
      · exact absurd (hlen ▸ hjF) (Nat.not_lt.mpr hj')
  · right
    refine ⟨Nat.le_of_not_lt hjF, ?_⟩
    rcases hT2 with hget | hno
    · have hnone : F[j]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hjF)
      rw [hnone] at hget
      exact absurd hget (by simp)
    · exact hno

/-- A crossing vertex at the first right hit is a nonpositive shifted left
Helper for the `item-busemann-ind` frontier decomposition; not a numbered
paper result. -/
theorem rightHit_crossing_eq_shifted_west_label (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses
      (fun i => w (boundaryHitTime w h 1 + i)))
    (u : PresentVertex w)
    (hin : u = ⟨boundaryVertex w h 0⟩ ∨
      ∃ e, ∃ he : EdgePresent w e,
        actTime w e he < boundaryHitTime w h 1 ∧ edgeEast w e = u.id)
    (hout : ∃ f, ∃ hf : EdgePresent w f,
      boundaryHitTime w h 1 ≤ actTime w f hf ∧ edgeWest w f = u.id) :
    ∃ j : ℕ, u = shiftLimitVertex w (boundaryHitTime w h 1)
      ⟨boundaryVertex
        (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩ := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  have huBound : u.id < (kmswStage w t).nextVertex := by
    rcases hin with hroot | ⟨e, he, het, heu⟩
    · rw [hroot, boundaryVertex_zero]
      have hmono := CutConverse.nextVertex_mono w (Nat.zero_le t)
      have hinit : (kmswStage w 0).nextVertex = 2 := rfl
      change 0 < (kmswStage w t).nextVertex
      omega
    · have heb : e < (kmswStage w t).nextEdge := by
        rw [actTime_spec w e he]
        exact act_lt_nextEdge w het.le
      have hb := (kmswStage_endpoints_lt_nextVertex w t e heb).2
      rw [(edge_endpoints_eq w heb).2, heu] at hb
      exact hb
  obtain ⟨n, hun⟩ := rightHit_late_outgoing_is_shifted_activeInitial w h u hout
  let a : PresentVertex ws := ⟨activeInitial ws n⟩
  have ha : kmswVertexAllocated ws a := by
    refine ⟨n, ?_⟩
    have heb := act_lt_nextEdge ws (Nat.le_refl n)
    have hb := (kmswStage_endpoints_lt_nextVertex ws n (act ws n) heb).1
    rw [(edge_endpoints_eq ws heb).1] at hb
    exact hb
  have himageBound : (shiftLimitVertex w t a).id < (kmswStage w t).nextVertex := by
    have hid := congrArg PresentVertex.id hun
    exact hid.symm ▸ huBound
  obtain ⟨k, hk⟩ := shiftLimitVertex_old_image_boundary_rightEntries
    w t hs a ha himageBound
  have huk : u = shiftLimitVertex w t ⟨boundaryVertex ws hs k⟩ := by
    exact hun.trans (congrArg (shiftLimitVertex w t) hk)
  by_cases hkpos : 0 < k
  · let q := k.toNat
    have hq : (q : ℤ) = k := by dsimp [q]; omega
    have hqpos : 1 ≤ q := by omega
    have hpending := shifted_positive_label_frontier_or_fresh w t hs hqpos
    have hUR : (kmswStage w t).UR = [] :=
      boundaryHit_right_UR_empty w h (by norm_num : (1 : ℤ) ≤ 1)
    have hqimage : shiftLimitVertex w t ⟨boundaryVertex ws hs (q : ℤ)⟩ = u := by
      rw [hq]
      exact huk.symm
    have hsmall : (shiftLimitVertex w t ⟨boundaryVertex ws hs (q : ℤ)⟩).id <
        (kmswStage w t).nextVertex := by
      rw [hqimage]
      exact huBound
    have hnotfresh : ¬ (kmswStage w t).nextVertex ≤
        (shiftLimitVertex w t ⟨boundaryVertex ws hs (q : ℤ)⟩).id := by omega
    rcases hpending with hpending | hfresh
    · have hqle : q = 1 := by
        have hpending' := hpending
        simp [CutConverse.pendingVertices, hUR] at hpending'
        have hidx := (List.getElem?_eq_some_iff.mp hpending').1
        simp only [List.length_singleton] at hidx
        omega
      have hqimage1 : shiftLimitVertex w t
          ⟨boundaryVertex ws hs (1 : ℤ)⟩ = u := by
        simpa [hqle] using hqimage
      have heast : u.id = (kmswStage w t).east (act w t) := by
        have hi : some ((kmswStage w t).east (act w t)) =
            some (shiftLimitVertex w t ⟨boundaryVertex ws hs (1 : ℤ)⟩).id := by
          simpa [CutConverse.pendingVertices, hUR, act, hqle] using hpending
        have hval := Option.some.inj hi
        have hmapid := congrArg PresentVertex.id hqimage1
        calc
          u.id = (shiftLimitVertex w t ⟨boundaryVertex ws hs (1 : ℤ)⟩).id := hmapid.symm
          _ = (kmswStage w t).east (act w t) := hval.symm
      rcases hin with hroot | ⟨e, he, het, heu⟩
      · have hrootid : u.id = 0 := by
          have := congrArg PresentVertex.id hroot
          simpa [boundaryVertex_zero] using this
        have hne := activeEast_ne_activeInitial w
          (j := 0) (n := t) (Nat.zero_le t)
        have hzero : activeInitial w 0 = 0 := by
          simp [activeInitial, edgeWest, act, kmswStage, kmswInit]
        rw [hzero] at hne
        exact False.elim (hne (heast.symm.trans hrootid))
      · have hne := rightHit_crossing_activeEast_fresh_rightEntries w h e he het
        exact False.elim (hne (heu.trans heast))
    · exact (hnotfresh hfresh).elim
  · let j := (-k).toNat
    have hindex : -(j : ℤ) = k := by dsimp [j]; omega
    refine ⟨j, ?_⟩
    simpa only [ws, hindex] using huk

end DirectedDistances.KMSW
