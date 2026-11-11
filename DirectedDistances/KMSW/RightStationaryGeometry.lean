module

public import DirectedDistances.KMSW.StageFrontier
public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.KMSW.InftyCutEastChain
public import DirectedDistances.KMSW.DirectedContain

/-! Supporting lemmas for paper labels `thm-busemann` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

open Quiver

private theorem coordinate_succ_ge_R_rightGeometry (w : ℕ → Fin 3) (n : ℕ) :
    R w n - 1 ≤ R w (n + 1) := by
  have hR : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  rw [hR]
  omega

private theorem exists_coordinate_eq_of_le_rightGeometry (f : ℕ → ℤ)
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

private theorem boundaryHitTime_right_eq_find_rightGeometry (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : k ≠ 0),
    dite_eq_left (by omega : 0 < k)]

/-- Right-coordinate hit times are monotone on positive indices -/
theorem boundaryHitTime_right_mono (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {a b : ℤ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    boundaryHitTime w h a ≤ boundaryHitTime w h b := by
  have hb : 1 ≤ b := by omega
  have hbHit := boundaryHitTime_right_spec w h hb
  obtain ⟨m, hm, hma⟩ := exists_coordinate_eq_of_le_rightGeometry (R w)
    (coordinate_succ_ge_R_rightGeometry w) (by simp [R]) (by omega : -a < 0)
    (by rw [hbHit]; omega)
  rw [boundaryHitTime_right_eq_find_rightGeometry w h ha]
  exact (Nat.find_min' (h.rightHit a ha) hma).trans hm

/-- At a positive right hit, shifted vertices zero and one map to the
corresponding consecutive global boundary vertices
(eqn-bdy-vertex-hit, eqn-bdy-vertex-kmsw,
this is a combinatorial root-label helper, not a source identification. -/
theorem rightShift_root_labels (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hShift : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i))) :
    shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) ⟨0⟩ =
        ⟨boundaryVertex w h (k : ℤ)⟩ ∧
      shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) ⟨1⟩ =
        ⟨boundaryVertex w h ((k + 1 : ℕ) : ℤ)⟩ := by
  let t := boundaryHitTime w h (k : ℤ)
  let wt := fun i => w (t + i)
  have he := boundaryHitTime_right_boundary_edge w h hk
  have hroot := boundaryVertex_root_edge wt hShift
  have hrootPresent : EdgePresent wt 0 := by
    refine ⟨0, ?_, hroot.2.2.2⟩
    change 0 < 1
    omega
  have hrootImage := shiftLimitEdge_root w t hrootPresent
  have hinc := shiftLimitEdge_incidence w t ⟨0, hrootPresent⟩
  rw [hrootImage] at hinc
  constructor
  · rw [shiftLimitVertex_root]
    apply congrArg PresentVertex.mk
    calc
      (kmswStage w t).west (act w t) = edgeWest w (act w t) :=
        (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl t))).1
      _ = boundaryVertex w h (k : ℤ) := he.2.1
  · have hact0 : act wt 0 = 0 := rfl
    have hrootEast : edgeEast wt 0 = 1 := by
      have hend := (edge_endpoints_eq wt (act_lt_nextEdge wt (Nat.le_refl 0))).2
      rw [hact0] at hend
      have heast := hroot.2.2.1
      rw [← hend, heast, boundaryVertex_one]
    apply congrArg PresentVertex.mk
    calc
      (shiftLimitVertex w t ⟨1⟩).id =
          (shiftLimitVertex w t ⟨edgeEast wt 0⟩).id := by rw [hrootEast]
      _ = edgeEast w (act w t) := hinc.2.symm
      _ = boundaryVertex w h ((k + 1 : ℕ) : ℤ) := he.2.2




theorem right_boundary_path_edges_late (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k j : ℕ}
    (hk : 1 ≤ k) (hkj : k ≤ j) {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) v) :
    ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
      boundaryHitTime w h (k : ℤ) ≤ actTime w e he := by
  have hj : 1 ≤ j := le_trans hk hkj
  intro e he hePresent
  obtain ⟨n, htn, hen⟩ := directedPath_edges_from_boundaryVertex_right w h
    (show 1 ≤ (j : ℤ) by exact_mod_cast hj) p e he
  have htime : actTime w e hePresent = n :=
    (actTime_eq_iff w e hePresent n).2 hen
  rw [htime]
  exact (boundaryHitTime_right_mono w h (by exact_mod_cast hk)
    (by exact_mod_cast hkj)).trans htn

private theorem shiftLimitVertex_path_map_rightGeometry (w : ℕ → Fin 3) (t : ℕ) :
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

private theorem shifted_path_lengths_eq_rightGeometry (w : ℕ → Fin 3) (t : ℕ)
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
    obtain ⟨q, hq⟩ := shiftLimitVertex_path_map_rightGeometry w t p
    exact ⟨q, hq.trans hp⟩

/-- For either endpoint of the positive right boundary edge at τ_k, every
global path length to an allocated shifted target agrees with the corresponding
shifted path-length set. The two equalities use the explicit hit witness and
the shift embedding; they are geometric helpers on the code graph, not a
Busemann identity or the paper's stationarity claim (thm-busemann, -/
theorem rightShift_path_lengths (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hShift : BoundaryHitWitnesses
      (fun i => w (boundaryHitTime w h (k : ℤ) + i))) :
    (∀ b : PresentVertex (fun i =>
        w (boundaryHitTime w h (k : ℤ) + i)),
      kmswVertexAllocated (fun i => w (boundaryHitTime w h (k : ℤ) + i)) b →
      {n | ∃ p : Path (⟨boundaryVertex w h (k : ℤ)⟩ : PresentVertex w)
          (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b), p.length = n} =
        {n | ∃ p : Path (⟨0⟩ : PresentVertex
          (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b, p.length = n}) ∧
    (∀ b : PresentVertex (fun i =>
        w (boundaryHitTime w h (k : ℤ) + i)),
      kmswVertexAllocated (fun i => w (boundaryHitTime w h (k : ℤ) + i)) b →
      {n | ∃ p : Path
          (⟨boundaryVertex w h ((k + 1 : ℕ) : ℤ)⟩ : PresentVertex w)
          (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b), p.length = n} =
        {n | ∃ p : Path (⟨1⟩ : PresentVertex
          (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b, p.length = n}) := by
  let t := boundaryHitTime w h (k : ℤ)
  let wt := fun i => w (t + i)
  have hroot := rightShift_root_labels w h k hk hShift
  have halloc0 : kmswVertexAllocated wt ⟨0⟩ :=
    ⟨0, by change 0 < 2; omega⟩
  have halloc1 : kmswVertexAllocated wt ⟨1⟩ :=
    ⟨0, by change 1 < 2; omega⟩
  constructor
  · intro b hb
    apply shifted_path_lengths_eq_rightGeometry w t ⟨0⟩ b
      ⟨boundaryVertex w h (k : ℤ)⟩ halloc0 hb hroot.1
    intro p e he hePresent
    simpa [t] using right_boundary_path_edges_late w h hk le_rfl p e he hePresent
  · intro b hb
    apply shifted_path_lengths_eq_rightGeometry w t ⟨1⟩ b
      ⟨boundaryVertex w h ((k + 1 : ℕ) : ℤ)⟩ halloc1 hb hroot.2
    intro p e he hePresent
    simpa [t] using right_boundary_path_edges_late w h hk (Nat.le_succ k) p e he hePresent

end DirectedDistances.KMSW
