module

public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.KMSW.CutEquivalenceConverse
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.KMSW.LeftStationaryGeometry
import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.RightBoundaryRightmost

/-! # East frontier entries at a left hit

Helpers toward frontier-label coverage in the frontier decomposition for
`k ≤ -1` geometry of `lem-directed-contain`, -/

public section
namespace DirectedDistances.KMSW

open Quiver

private theorem shiftVertexMapAll_old_image_lowerBoundary
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
      have hstep : kmswStage ws (m + 1) = kmswStepOfStep sh (kmswCodeStep (ws m)) := rfl
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

/-- An allocated shifted vertex whose image is allocated by the cutoff has
a shifted boundary label. Helper for frontier-label coverage in B.2
statement does not claim that the label's sign is past-determined. -/
private theorem shiftLimitVertex_old_image_boundary (w : ℕ → Fin 3) (t : ℕ)
    (hs : BoundaryHitWitnesses (fun i => w (t + i)))
    (a : PresentVertex (fun i => w (t + i)))
    (ha : kmswVertexAllocated (fun i => w (t + i)) a)
    (hold : (shiftLimitVertex w t a).id < (kmswStage w t).nextVertex) :
    ∃ k : ℤ, a = ⟨boundaryVertex (fun i => w (t + i)) hs k⟩ := by
  obtain ⟨m, hm⟩ := ha
  rw [shiftLimitVertex_eq w t m a hm] at hold
  obtain ⟨k, hk⟩ := boundaryVertex_covers_lowerBoundary (fun i => w (t + i)) hs a.id
    (shiftVertexMapAll_old_image_lowerBoundary w t m a.id hm hold)
  refine ⟨k, ?_⟩
  cases a
  exact congrArg PresentVertex.mk hk.symm

private theorem shift_UR_suffix (w : ℕ → Fin 3) (t m : ℕ) :
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

private theorem shift_LR_entry (w : ℕ → Fin 3) (t m : ℕ) :
    ∀ (i e : ℕ), (kmswStage (fun i => w (t + i)) m).LR[i]? = some e →
      (act w t :: (kmswStage w t).UR)[i]? = some (kmswShiftEdgeMapAll w t m e) ∨
        (kmswStage w t).nextVertex ≤ edgeEast w (kmswShiftEdgeMapAll w t m e) := by
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
          (kmswStage w t).nextVertex ≤ edgeEast w (en e) := by
      have hmem : e ∈ sh.LR := List.mem_of_getElem? he
      have heb : e < sh.nextEdge :=
        (kmswStage_boundary_ids_lt_nextEdge ws m).2 e
          (by simp only [List.mem_append]; exact Or.inr hmem)
      dsimp only [en]
      rw [kmswShiftEdgeMapAll_extend w t m e heb]
      exact ih i e he
    intro i e he
    change (act w t :: (kmswStage w t).UR)[i]? = some (en e) ∨
      (kmswStage w t).nextVertex ≤ edgeEast w (en e)
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
            have hh := shift_UR_suffix w t m
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
            have hnew : en sh.nextEdge = gl.nextEdge := by
              change kmswShiftNextEdgeMap sh gl (kmswCodeStep (ws m)) ep _ = _
              simp [hc, kmswShiftNextEdgeMap, hs, hg, kmswShiftFreshEdgeMap]
            right
            rw [hnew]
            have heb : gl.nextEdge < (kmswStage w (t + (m + 1))).nextEdge := by
              rw [hgl]
              simp [hc, kmswStepOfStep, hg, State.addEdge]
            have hend : edgeEast w gl.nextEdge = gl.nextVertex := by
              rw [← (edge_endpoints_eq w heb).2, hgl]
              simp [hc, kmswStepOfStep, hg, State.addEdge]
            rw [hend]
            exact CutConverse.nextVertex_mono w (Nat.le_add_right t m)

/-- Positive shifted boundary labels enumerate the cutoff east frontier
in order until their images are fresh. The ordered list is precisely the
repository's `pendingVertices`: active terminal vertex followed by UR east
endpoints. Helper for B.2 (`lem-directed-contain`, -/
theorem shifted_positive_label_frontier_or_fresh (w : ℕ → Fin 3) (t : ℕ)
    (hs : BoundaryHitWitnesses (fun i => w (t + i))) {j : ℕ} (hj : 1 ≤ j) :
    (CutConverse.pendingVertices (kmswStage w t))[j - 1]? =
        some (shiftLimitVertex w t
          ⟨boundaryVertex (fun i => w (t + i)) hs (j : ℤ)⟩).id ∨
      (kmswStage w t).nextVertex ≤ (shiftLimitVertex w t
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
  rcases shift_LR_entry w t N (j - 1) e hentry with hidx | hfresh
  · left
    have hh := congrArg (Option.map (edgeEast w)) hidx
    rw [← List.getElem?_map, hfront] at hh
    simpa only [Option.map_some, hinc] using hh
  · right
    rwa [hinc] at hfresh

/-- Past determination of the positive frontier labels at the left hit:
the image is the `j`th eastward vertex of the cutoff UR frontier (the
zero-based list entry `j - 1`), or has no early incident present edge.
Helper for the frontier decomposition in `item-busemann-ind`, -/
theorem leftHit_shifted_east_label_frontier_or_no_early_edge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    {j : ℕ} (hj : 1 ≤ j) :
    (CutConverse.pendingVertices (kmswStage w (boundaryHitTime w h (-1))))[j - 1]? =
        some (shiftLimitVertex w (boundaryHitTime w h (-1))
          ⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩).id ∨
      ∀ e, ∀ he : EdgePresent w e, actTime w e he < boundaryHitTime w h (-1) →
        edgeWest w e ≠ (shiftLimitVertex w (boundaryHitTime w h (-1))
          ⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩).id ∧
        edgeEast w e ≠ (shiftLimitVertex w (boundaryHitTime w h (-1))
          ⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩).id := by
  rcases shifted_positive_label_frontier_or_fresh w (boundaryHitTime w h (-1)) hs hj
      with hfront | hfresh
  · exact Or.inl hfront
  · right
    intro e he het
    have heb : e < (kmswStage w (boundaryHitTime w h (-1))).nextEdge := by
      rw [actTime_spec w e he]
      exact act_lt_nextEdge w het.le
    have hb := kmswStage_endpoints_lt_nextVertex w (boundaryHitTime w h (-1)) e heb
    rw [(edge_endpoints_eq w heb).1, (edge_endpoints_eq w heb).2] at hb
    constructor <;> omega

/-- The shift embedding preserves active initial vertices. Helper for the
frontier-label coverage in B.2 (`lem-directed-contain`, -/
private theorem shiftLimitVertex_activeInitial_frontier (w : ℕ → Fin 3) (t n : ℕ) :
    shiftLimitVertex w t ⟨activeInitial (fun i => w (t + i)) n⟩ =
      ⟨activeInitial w (t + n)⟩ := by
  let ws := fun i => w (t + i)
  let e : {e : ℕ // EdgePresent ws e} :=
    ⟨act ws n, kmswShift_active_edge_present_limit w t n⟩
  have ht : actTime ws e.val e.property = n :=
    (actTime_eq_iff ws _ _ n).2 rfl
  have he : shiftLimitEdge w t e = act w (t + n) := by
    change act w (t + actTime ws e.val e.property) = _
    rw [ht]
  have hinc := (shiftLimitEdge_incidence w t e).1
  rw [he] at hinc
  exact congrArg PresentVertex.mk hinc.symm

/-- Every vertex with a late outgoing edge is the image of a shifted active
initial vertex. Helper for B.2 (`lem-directed-contain`,
label. -/
private theorem late_outgoing_eq_shifted_activeInitial (w : ℕ → Fin 3) (t : ℕ)
    (u : PresentVertex w)
    (hout : ∃ f, ∃ hf : EdgePresent w f,
      t ≤ actTime w f hf ∧ edgeWest w f = u.id) :
    ∃ n : ℕ, u = shiftLimitVertex w t
      ⟨activeInitial (fun i => w (t + i)) n⟩ := by
  obtain ⟨f, hf, ht, hw⟩ := hout
  refine ⟨actTime w f hf - t, ?_⟩
  rw [shiftLimitVertex_activeInitial_frontier, Nat.add_sub_of_le ht]
  have hid : u.id = activeInitial w (actTime w f hf) := by
    change u.id = edgeWest w (act w (actTime w f hf))
    rw [← actTime_spec w f hf, hw]
  cases u
  exact congrArg PresentVertex.mk hid

/-- Frontier-label coverage at the left hit, including the empty early
prefix at `x₀`. Helper for the frontier decomposition in
as a numbered paper result. -/
theorem leftHit_crossing_eq_shifted_east_label (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (u : PresentVertex w)
    (hin : u = ⟨boundaryVertex w h 0⟩ ∨
      ∃ e, ∃ he : EdgePresent w e,
        actTime w e he < boundaryHitTime w h (-1) ∧ edgeEast w e = u.id)
    (hout : ∃ f, ∃ hf : EdgePresent w f,
      boundaryHitTime w h (-1) ≤ actTime w f hf ∧ edgeWest w f = u.id) :
    ∃ j : ℕ, 1 ≤ j ∧ u = shiftLimitVertex w (boundaryHitTime w h (-1))
      ⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩ := by
  let t := boundaryHitTime w h (-1)
  let ws := fun i => w (t + i)
  have hold : u.id < (kmswStage w t).nextVertex := by
    rcases hin with hu | ⟨e, he, het, hez⟩
    · rw [hu, boundaryVertex_zero]
      have hmono := CutConverse.nextVertex_mono w (Nat.zero_le t)
      have hinit : (kmswStage w 0).nextVertex = 2 := rfl
      change 0 < (kmswStage w t).nextVertex
      omega
    · have heb : e < (kmswStage w t).nextEdge := by
        rw [actTime_spec w e he]
        exact act_lt_nextEdge w het.le
      have hb := (kmswStage_endpoints_lt_nextVertex w t e heb).2
      rw [(edge_endpoints_eq w heb).2, hez] at hb
      exact hb
  obtain ⟨n, hun⟩ := late_outgoing_eq_shifted_activeInitial w t u hout
  let a : PresentVertex ws := ⟨activeInitial ws n⟩
  have ha : kmswVertexAllocated ws a := by
    refine ⟨n, ?_⟩
    have heb := act_lt_nextEdge ws (Nat.le_refl n)
    have hb := (kmswStage_endpoints_lt_nextVertex ws n (act ws n) heb).1
    rw [(edge_endpoints_eq ws heb).1] at hb
    exact hb
  obtain ⟨k, hk⟩ := shiftLimitVertex_old_image_boundary w t hs a ha (hun ▸ hold)
  have huk : u = shiftLimitVertex w t ⟨boundaryVertex ws hs k⟩ := by
    exact hun.trans (congrArg (shiftLimitVertex w t) hk)
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k ≤ 0 := by omega
    have hlabel := leftShift_labels w h (k := -1) (by omega) hs hk0
    have hu : u = ⟨boundaryVertex w h (-1 + k)⟩ := huk.trans hlabel
    rcases hin with hzero | ⟨e, he, _, hez⟩
    · have hid := congrArg PresentVertex.id (hzero.symm.trans hu)
      have hidx := boundaryVertex_injective w h
        (show boundaryVertex w h 0 = boundaryVertex w h (-1 + k) from hid)
      omega
    · have hne := boundaryVertex_nonpos_no_incoming w h
        (by omega : -1 + k ≤ 0) e he
      apply hne
      exact hez.trans (congrArg PresentVertex.id hu)
  refine ⟨k.toNat, by omega, ?_⟩
  have hcast : (k.toNat : ℤ) = k := by omega
  rw [hcast]
  exact huk

end DirectedDistances.KMSW
