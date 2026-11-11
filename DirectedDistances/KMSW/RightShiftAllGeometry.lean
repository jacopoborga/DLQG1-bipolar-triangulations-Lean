module

public import DirectedDistances.KMSW.RightStationaryGeometry
import DirectedDistances.KMSW.DirectedContainHat

/-! # All nonnegative boundary indices under a right-hit shift

Geometric helpers toward `item-busemann-ind` and `item-busemann-stationary`
are not counted as paper results; the source identification obligations F1/F4
remain. -/

public section
namespace DirectedDistances.KMSW

open Quiver

private theorem R_shift_add_AllGeometry (w : ℕ → Fin 3) (t n : ℕ) :
    R w (t + n) = R w t + R (fun i => w (t + i)) n := by
  induction n with
  | zero => simp [R]
  | succ n ih =>
    have hglobal : R w (t + n + 1) = R w (t + n) +
        (RandomWalk.lazyTwoDimensionalStep (w (t + n))).2 :=
      Finset.sum_range_succ _ _
    have hshift : R (fun i => w (t + i)) (n + 1) =
        R (fun i => w (t + i)) n +
          (RandomWalk.lazyTwoDimensionalStep (w (t + n))).2 :=
      Finset.sum_range_succ _ _
    rw [Nat.add_succ, hglobal, hshift, ih]
    omega

private theorem boundaryHitTime_right_eq_find_AllGeometry (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_left (by omega : 0 < k)]

/-- Positive right-hit times translate under a right-hit shift. Geometric
helper toward `item-busemann-ind` / `item-busemann-stationary` -/
theorem rightShift_boundaryHitTime (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    {j : ℕ} (hj : 1 ≤ j) :
    boundaryHitTime w h (k : ℤ) +
        boundaryHitTime (fun i => w (boundaryHitTime w h (k : ℤ) + i)) hs (j : ℤ) =
      boundaryHitTime w h ((k + j : ℕ) : ℤ) := by
  let t := boundaryHitTime w h (k : ℤ)
  let ws := fun i => w (t + i)
  let s := boundaryHitTime ws hs (j : ℤ)
  let u := boundaryHitTime w h ((k + j : ℕ) : ℤ)
  have hkZ : 1 ≤ (k : ℤ) := by omega
  have hjZ : 1 ≤ (j : ℤ) := by omega
  have hkjZ : 1 ≤ ((k + j : ℕ) : ℤ) := by omega
  have ht : R w t = -(k : ℤ) := boundaryHitTime_right_spec w h hkZ
  have hsR : R ws s = -(j : ℤ) := boundaryHitTime_right_spec ws hs hjZ
  have hu : R w u = -((k + j : ℕ) : ℤ) :=
    boundaryHitTime_right_spec w h hkjZ
  have htu : t ≤ u := boundaryHitTime_right_mono w h hkZ (by omega)
  have hsum : R w (t + s) = -((k + j : ℕ) : ℤ) := by
    have hR := R_shift_add_AllGeometry w t s
    change R w (t + s) = R w t + R ws s at hR
    omega
  have hu_le : u ≤ t + s := by
    change boundaryHitTime w h ((k + j : ℕ) : ℤ) ≤ t + s
    rw [boundaryHitTime_right_eq_find_AllGeometry w h hkjZ]
    exact Nat.find_min' (h.rightHit _ hkjZ) hsum
  have hdiff : R ws (u - t) = -(j : ℤ) := by
    have hR := R_shift_add_AllGeometry w t (u - t)
    rw [Nat.add_sub_of_le htu] at hR
    change R w u = R w t + R ws (u - t) at hR
    omega
  have hs_le : s ≤ u - t := by
    change boundaryHitTime ws hs (j : ℤ) ≤ u - t
    rw [boundaryHitTime_right_eq_find_AllGeometry ws hs hjZ]
    exact Nat.find_min' (hs.rightHit _ hjZ) hdiff
  change t + s = u
  omega

/-- Every nonnegative shifted boundary index has the translated global label,
and its shifted vertex is allocated. Geometric helper toward
`item-busemann-ind` / `item-busemann-stationary` -/
theorem rightShift_labels (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (j : ℕ) :
    shiftLimitVertex w (boundaryHitTime w h (k : ℤ))
        ⟨boundaryVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)) hs (j : ℤ)⟩ =
      ⟨boundaryVertex w h ((k + j : ℕ) : ℤ)⟩ ∧
    kmswVertexAllocated (fun i => w (boundaryHitTime w h (k : ℤ) + i))
      ⟨boundaryVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)) hs (j : ℤ)⟩ := by
  let t := boundaryHitTime w h (k : ℤ)
  let ws := fun i => w (t + i)
  by_cases hj0 : j = 0
  · subst j
    have hroot := (rightShift_root_labels w h k hk hs).1
    have halloc : kmswVertexAllocated ws ⟨0⟩ := ⟨0, by change 0 < 2; omega⟩
    simpa only [Nat.cast_zero, boundaryVertex_zero, Nat.add_zero] using
      And.intro hroot halloc
  · have hj : 1 ≤ j := by omega
    let n := boundaryHitTime ws hs (j : ℤ)
    have he : EdgePresent ws (act ws n) :=
      kmswShift_active_edge_present_limit w t n
    let ef : {e : ℕ // EdgePresent ws e} := ⟨act ws n, he⟩
    have hinc := shiftLimitEdge_incidence w t ef
    have hedge : shiftLimitEdge w t ef = act w (t + n) := by
      change act w (t + actTime ws (act ws n) he) = act w (t + n)
      rw [(actTime_eq_iff ws (act ws n) he n).2 rfl]
    have htime : t + n = boundaryHitTime w h ((k + j : ℕ) : ℤ) :=
      rightShift_boundaryHitTime w h k hk hs hj
    have hvertex : boundaryVertex ws hs (j : ℤ) = edgeWest ws (act ws n) :=
      boundaryVertex_eq_edgeWest_hit ws hs (j : ℤ)
    constructor
    · apply congrArg PresentVertex.mk
      change (shiftLimitVertex w t ⟨boundaryVertex ws hs (j : ℤ)⟩).id = _
      calc
        _ = edgeWest w (shiftLimitEdge w t ef) := by
          simpa only [hvertex] using hinc.1.symm
        _ = edgeWest w (act w (t + n)) := by rw [hedge]
        _ = boundaryVertex w h ((k + j : ℕ) : ℤ) := by
          rw [htime, ← boundaryVertex_eq_edgeWest_hit w h ((k + j : ℕ) : ℤ)]
    · obtain ⟨m, hm, _⟩ := he
      have hb := (kmswStage_endpoints_lt_nextVertex ws m (act ws n) hm).1
      rw [(edge_endpoints_eq ws hm).1] at hb
      refine ⟨m, ?_⟩
      change boundaryVertex ws hs (j : ℤ) < (kmswStage ws m).nextVertex
      rw [hvertex]
      exact hb

private theorem shiftLimitVertex_path_map_AllGeometry (w : ℕ → Fin 3) (t : ℕ) :
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

private theorem shifted_path_lengths_eq_AllGeometry (w : ℕ → Fin 3) (t : ℕ)
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
    obtain ⟨q, hq⟩ := shiftLimitVertex_path_map_AllGeometry w t p
    exact ⟨q, hq.trans hp⟩

/-- All path-length sets from a nonnegative shifted boundary index agree
with those from its global translate. Geometric helper toward
`item-busemann-ind` / `item-busemann-stationary` -/
theorem rightShift_path_lengths_all (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (j : ℕ) :
    ∀ b : PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)),
      kmswVertexAllocated (fun i => w (boundaryHitTime w h (k : ℤ) + i)) b →
      {n | ∃ p : Path
          (⟨boundaryVertex w h ((k + j : ℕ) : ℤ)⟩ : PresentVertex w)
          (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b), p.length = n} =
        {n | ∃ p : Path
          (⟨boundaryVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)) hs
            (j : ℤ)⟩ : PresentVertex
              (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b, p.length = n} := by
  let t := boundaryHitTime w h (k : ℤ)
  let ws := fun i => w (t + i)
  have hlabel := rightShift_labels w h k hk hs j
  intro b hb
  apply shifted_path_lengths_eq_AllGeometry w t
    ⟨boundaryVertex ws hs (j : ℤ)⟩ b
    ⟨boundaryVertex w h ((k + j : ℕ) : ℤ)⟩ hlabel.2 hb hlabel.1
  intro p e he hePresent
  exact right_boundary_path_edges_late w h hk (by omega : k ≤ k + j) p e he hePresent




theorem rightShift_reachable_iff_all (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 1 ≤ k)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (j : ℕ)
    (b : PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h (k : ℤ) + i)) b) :
    Reachable (⟨boundaryVertex w h ((k + j : ℕ) : ℤ)⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b) ↔
      Reachable (⟨boundaryVertex
        (fun i => w (boundaryHitTime w h (k : ℤ) + i)) hs (j : ℤ)⟩ :
        PresentVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b := by
  have hlengths := rightShift_path_lengths_all w h k hk hs j b hb
  constructor
  · rintro ⟨p⟩
    have hp : p.length ∈ {n | ∃ q : Path
        (⟨boundaryVertex w h ((k + j : ℕ) : ℤ)⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h (k : ℤ)) b), q.length = n} :=
      ⟨p, rfl⟩
    rw [hlengths] at hp
    obtain ⟨q, _⟩ := hp
    exact ⟨q⟩
  · rintro ⟨p⟩
    have hp : p.length ∈ {n | ∃ q : Path
        (⟨boundaryVertex (fun i => w (boundaryHitTime w h (k : ℤ) + i)) hs
          (j : ℤ)⟩ : PresentVertex
            (fun i => w (boundaryHitTime w h (k : ℤ) + i))) b, q.length = n} :=
      ⟨p, rfl⟩
    rw [← hlengths] at hp
    obtain ⟨q, _⟩ := hp
    exact ⟨q⟩

end DirectedDistances.KMSW
