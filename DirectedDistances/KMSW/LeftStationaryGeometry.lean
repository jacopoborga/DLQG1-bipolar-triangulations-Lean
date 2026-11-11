module

public import DirectedDistances.KMSW.StageFrontier
public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.KMSW.DirectedContain

/-! # Left-side geometry for the shifted-future route

Geometric helpers toward `item-busemann-stationary` for the increments with
nonpositive shifted boundary labels and transfer finite directed path lengths.
They are not a stationarity theorem and are not counted as a paper result.
The source identification obligations F1 and F4 remain. -/

public section
namespace DirectedDistances.KMSW

open Quiver

private theorem coordinate_succ_ge_L_LeftGeometry (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  have hL : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  rw [hL]
  omega

private theorem exists_coordinate_eq_of_le_LeftGeometry (f : ℕ → ℤ)
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

private theorem boundaryHitTime_left_eq_find_LeftGeometry (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : k ≠ 0),
    dite_eq_right (by omega : ¬ 0 < k)]

/-- Left-coordinate hit times are antitone on negative indices
Geometric input toward `item-busemann-stationary`; F1/F4 remain. -/
theorem boundaryHitTime_left_antitone (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {a b : ℤ} (hb : b ≤ -1) (hab : a ≤ b) :
    boundaryHitTime w h b ≤ boundaryHitTime w h a := by
  have ha : a ≤ -1 := by omega
  have haHit := boundaryHitTime_left_spec w h ha
  obtain ⟨m, hm, hmb⟩ := exists_coordinate_eq_of_le_LeftGeometry (L w)
    (coordinate_succ_ge_L_LeftGeometry w) (by simp [L]) (by omega : b < 0)
    (by rw [haHit]; omega)
  rw [boundaryHitTime_left_eq_find_LeftGeometry w h hb]
  exact (Nat.find_min' (h.leftHit b hb) hmb).trans hm

private theorem L_shift_add_LeftGeometry (w : ℕ → Fin 3) (t n : ℕ) :
    L w (t + n) = L w t + L (fun i => w (t + i)) n := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
    have hg : L w (t + n + 1) = L w (t + n) +
        (RandomWalk.lazyTwoDimensionalStep (w (t + n))).1 :=
      Finset.sum_range_succ _ _
    have hs : L (fun i => w (t + i)) (n + 1) =
        L (fun i => w (t + i)) n +
          (RandomWalk.lazyTwoDimensionalStep (w (t + n))).1 :=
      Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hs, ih]
    omega

/-- The first hit of a negative shifted level translates to the first hit
of the sum of the two negative levels (`eqn-bdy-vertex-kmsw`, -/
theorem leftShift_boundaryHitTime (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    {j : ℤ} (hj : j ≤ -1) :
    boundaryHitTime w h k +
        boundaryHitTime (fun i => w (boundaryHitTime w h k + i)) hs j =
      boundaryHitTime w h (k + j) := by
  let t := boundaryHitTime w h k
  let ws := fun i => w (t + i)
  let s := boundaryHitTime ws hs j
  let u := boundaryHitTime w h (k + j)
  have hkHit : L w t = k := boundaryHitTime_left_spec w h hk
  have hjHit : L ws s = j := boundaryHitTime_left_spec ws hs hj
  have hkj : k + j ≤ -1 := by omega
  have huHit : L w u = k + j := boundaryHitTime_left_spec w h hkj
  have htu : t ≤ u := boundaryHitTime_left_antitone w h hk (by omega)
  have hsum := L_shift_add_LeftGeometry w t s
  have hglobal : u ≤ t + s := by
    dsimp [u]
    rw [boundaryHitTime_left_eq_find_LeftGeometry w h hkj]
    apply Nat.find_min'
    change L w (t + s) = L w t + L ws s at hsum
    omega
  have hshift : s ≤ u - t := by
    dsimp [s]
    rw [boundaryHitTime_left_eq_find_LeftGeometry ws hs hj]
    apply Nat.find_min'
    have hsub := L_shift_add_LeftGeometry w t (u - t)
    rw [Nat.add_sub_of_le htu] at hsub
    change L w u = L w t + L ws (u - t) at hsub
    omega
  change t + s = u
  omega

private theorem active_present_LeftGeometry (w : ℕ → Fin 3) (n : ℕ) :
    EdgePresent w (act w n) := by
  refine ⟨n, act_lt_nextEdge w le_rfl, ?_⟩
  apply (kmswStage_status w n).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem shiftLimitVertex_activeInitial_LeftGeometry
    (w : ℕ → Fin 3) (t n : ℕ) :
    shiftLimitVertex w t ⟨activeInitial (fun i => w (t + i)) n⟩ =
      ⟨activeInitial w (t + n)⟩ := by
  let ws := fun i => w (t + i)
  let e : {e : ℕ // EdgePresent ws e} :=
    ⟨act ws n, active_present_LeftGeometry ws n⟩
  have ht : actTime ws e.val e.property = n :=
    (actTime_eq_iff ws _ _ n).2 rfl
  have he : shiftLimitEdge w t e = act w (t + n) := by
    change act w (t + actTime ws e.val e.property) = _
    rw [ht]
  have hinc := (shiftLimitEdge_incidence w t e).1
  rw [he] at hinc
  exact congrArg PresentVertex.mk hinc.symm

/-- Nonpositive hit-indexed boundary vertices are allocated, including the
This applies in particular to every shifted boundary vertex used below;
it is a geometric helper, with F1/F4 still outstanding. -/
theorem boundaryVertex_left_allocated (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {j : ℤ} (hj : j ≤ 0) :
    kmswVertexAllocated w ⟨boundaryVertex w h j⟩ := by
  by_cases hj0 : j = 0
  · subst j
    rw [boundaryVertex_zero]
    exact ⟨0, by change 0 < 2; omega⟩
  · rw [boundaryVertex_left_hit_eq w h (by omega : j ≤ -1)]
    refine ⟨boundaryHitTime w h j, ?_⟩
    have he := act_lt_nextEdge w (Nat.le_refl (boundaryHitTime w h j))
    have hb := (kmswStage_endpoints_lt_nextVertex w _ _ he).1
    rw [(edge_endpoints_eq w he).1] at hb
    exact hb

/-- At a negative left hit, all nonpositive shifted boundary labels map to
the corresponding translated global labels (`eqn-bdy-vertex-hit`,
stationarity theorem; F1/F4 remain. -/
theorem leftShift_labels (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    {j : ℤ} (hj : j ≤ 0) :
    shiftLimitVertex w (boundaryHitTime w h k)
        ⟨boundaryVertex (fun i => w (boundaryHitTime w h k + i)) hs j⟩ =
      ⟨boundaryVertex w h (k + j)⟩ := by
  by_cases hj0 : j = 0
  · subst j
    rw [boundaryVertex_zero, shiftLimitVertex_root, add_zero,
      boundaryVertex_left_hit_eq w h hk]
    exact congrArg PresentVertex.mk (CutConverse.activeInitial_eq w _).symm
  · have hjneg : j ≤ -1 := by omega
    rw [boundaryVertex_left_hit_eq _ hs hjneg,
      shiftLimitVertex_activeInitial_LeftGeometry,
      leftShift_boundaryHitTime w h hk hs hjneg,
      boundaryVertex_left_hit_eq w h (by omega : k + j ≤ -1)]

/-- Every edge of a directed path from `x_(k+j)`, with `k ≤ -1` and `j ≤ 0`,
is activated at or after the kth left hit (`lem-directed-contain`, -/
theorem left_boundary_path_edges_late (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k j : ℤ} (hk : k ≤ -1) (hj : j ≤ 0)
    {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h (k + j)⟩ : PresentVertex w) v) :
    ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
      boundaryHitTime w h k ≤ actTime w e he := by
  intro e he hePresent
  obtain ⟨n, htn, hen⟩ := directedPath_edges_from_boundaryVertex_left w h
    (by omega : k + j ≤ -1) p e he
  have htime : actTime w e hePresent = n :=
    (actTime_eq_iff w e hePresent n).2 hen
  rw [htime]
  exact (boundaryHitTime_left_antitone w h hk (by omega : k + j ≤ k)).trans htn

private theorem shiftLimitVertex_path_map_LeftGeometry (w : ℕ → Fin 3) (t : ℕ) :
    ∀ {a b : PresentVertex (fun i => w (t + i))} (p : Path a b),
      ∃ q : Path (shiftLimitVertex w t a) (shiftLimitVertex w t b),
        q.length = p.length := by
  intro a b p
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons mid target p e ih =>
    obtain ⟨q, hq⟩ := ih
    let ef : {f : ℕ // EdgePresent (fun i => w (t + i)) f} :=
      ⟨e.val, e.property.1⟩
    have hpresent := shiftLimitEdge_present w t ef
    have hinc := shiftLimitEdge_incidence w t ef
    have hmid : (⟨edgeWest (fun i => w (t + i)) e.val⟩ :
        PresentVertex (fun i => w (t + i))) = mid :=
      congrArg PresentVertex.mk e.property.2.1
    have htarget : (⟨edgeEast (fun i => w (t + i)) e.val⟩ :
        PresentVertex (fun i => w (t + i))) = target :=
      congrArg PresentVertex.mk e.property.2.2
    have hmidMap := congrArg (shiftLimitVertex w t) hmid
    have htargetMap := congrArg (shiftLimitVertex w t) htarget
    have hwest : edgeWest w (shiftLimitEdge w t ef) =
        (shiftLimitVertex w t mid).id := by
      calc
        edgeWest w (shiftLimitEdge w t ef) =
            (shiftLimitVertex w t ⟨edgeWest (fun i => w (t + i)) e.val⟩).id := hinc.1
        _ = (shiftLimitVertex w t mid).id := congrArg PresentVertex.id hmidMap
    have heast : edgeEast w (shiftLimitEdge w t ef) =
        (shiftLimitVertex w t target).id := by
      calc
        edgeEast w (shiftLimitEdge w t ef) =
            (shiftLimitVertex w t ⟨edgeEast (fun i => w (t + i)) e.val⟩).id := hinc.2
        _ = (shiftLimitVertex w t target).id := congrArg PresentVertex.id htargetMap
    let f : (shiftLimitVertex w t mid) ⟶ (shiftLimitVertex w t target) :=
      ⟨shiftLimitEdge w t ef, hpresent, hwest, heast⟩
    exact ⟨q.cons f, by simp [Path.length_cons, hq]⟩

private theorem shifted_path_lengths_eq_LeftGeometry (w : ℕ → Fin 3) (t : ℕ)
    (a b : PresentVertex (fun i => w (t + i))) (x : PresentVertex w)
    (ha : kmswVertexAllocated (fun i => w (t + i)) a)
    (hb : kmswVertexAllocated (fun i => w (t + i)) b)
    (hsource : shiftLimitVertex w t a = x)
    (hlate : ∀ p : Path x (shiftLimitVertex w t b),
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        t ≤ actTime w e he) :
    {n | ∃ p : Path x (shiftLimitVertex w t b), p.length = n} =
      {n | ∃ p : Path a b, p.length = n} := by
  cases hsource
  ext n
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨b', hb', q, hq, hlen, _⟩ := shiftLimitVertex_late_path_lift w t a ha p
      (hlate p)
    have hbb : b' = b := shiftLimitVertex_injective w t hb' hb hq
    subst b'
    exact ⟨q, hlen.trans hp⟩
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq⟩ := shiftLimitVertex_path_map_LeftGeometry w t p
    exact ⟨q, hq.trans hp⟩

/-- Global and shifted path-length sets agree for every nonpositive
shifted boundary source and allocated shifted target (`lem-directed-contain`,
identity or stationarity theorem; F1/F4 remain, and no paper result is counted. -/
theorem leftShift_path_lengths (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    {j : ℤ} (hj : j ≤ 0) :
    ∀ b : PresentVertex (fun i => w (boundaryHitTime w h k + i)),
      kmswVertexAllocated (fun i => w (boundaryHitTime w h k + i)) b →
      {n | ∃ p : Path (⟨boundaryVertex w h (k + j)⟩ : PresentVertex w)
          (shiftLimitVertex w (boundaryHitTime w h k) b), p.length = n} =
        {n | ∃ p : Path
          (⟨boundaryVertex (fun i => w (boundaryHitTime w h k + i)) hs j⟩ :
            PresentVertex (fun i => w (boundaryHitTime w h k + i))) b,
          p.length = n} := by
  intro b hb
  apply shifted_path_lengths_eq_LeftGeometry w (boundaryHitTime w h k)
    ⟨boundaryVertex (fun i => w (boundaryHitTime w h k + i)) hs j⟩ b
    ⟨boundaryVertex w h (k + j)⟩ (boundaryVertex_left_allocated _ hs hj) hb
    (leftShift_labels w h hk hs hj)
  intro p e he hePresent
  exact left_boundary_path_edges_late w h hk hj p e he hePresent

/-- Reachability from a translated left boundary vertex is equivalent to
reachability in the shifted graph, for allocated shifted targets
not a stationarity theorem, and F1/F4 remain. -/
theorem leftShift_reachable_iff (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h k + i)))
    {j : ℤ} (hj : j ≤ 0)
    (b : PresentVertex (fun i => w (boundaryHitTime w h k + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h k + i)) b) :
    Reachable (⟨boundaryVertex w h (k + j)⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h k) b) ↔
      Reachable
        (⟨boundaryVertex (fun i => w (boundaryHitTime w h k + i)) hs j⟩ :
          PresentVertex (fun i => w (boundaryHitTime w h k + i))) b := by
  have hlengths := leftShift_path_lengths w h hk hs hj b hb
  constructor
  · rintro ⟨p⟩
    have hp : p.length ∈ {n | ∃ q : Path
        (⟨boundaryVertex w h (k + j)⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h k) b), q.length = n} := ⟨p, rfl⟩
    rw [hlengths] at hp
    obtain ⟨q, _⟩ := hp
    exact ⟨q⟩
  · rintro ⟨p⟩
    have hp : p.length ∈ {n | ∃ q : Path
        (⟨boundaryVertex (fun i => w (boundaryHitTime w h k + i)) hs j⟩ :
          PresentVertex (fun i => w (boundaryHitTime w h k + i))) b,
        q.length = n} := ⟨p, rfl⟩
    rw [← hlengths] at hp
    obtain ⟨q, _⟩ := hp
    exact ⟨q⟩

end DirectedDistances.KMSW
