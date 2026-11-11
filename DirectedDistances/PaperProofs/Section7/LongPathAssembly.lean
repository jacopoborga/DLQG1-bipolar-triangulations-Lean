module

public import DirectedDistances.PaperProofs.Section7.LongPathFutureBoundaryExit
public import DirectedDistances.PaperProofs.Section7.LongPathBusemannBound
import DirectedDistances.PaperProofs.Section7.LongPathBoundarySegment
import DirectedDistances.PaperProofs.Section7.LongPathGeodesicDecomposition
import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix

/-! Supporting lemmas for paper labels `lem-long-path` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem window_arrow_data (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (e : a ⟶ b) :
    EdgePresent w (kmswWindowEdgeMapInf w n e.val) ∧
      edgeWest w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n a.id ∧
      edgeEast w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n b.id := by
  obtain ⟨m, hm, hp⟩ := e.property.1
  have hr := kmswWindowPatchData_rel w n m
  have hg : kmswWindowEdgeMapInf w n e.val < (kmswStage w (n + m)).nextEdge := by
    rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.edge_bound e.val hm
  refine ⟨⟨n + m, hg, ?_⟩, ?_, ?_⟩
  · rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.present e.val hm hp
  · rw [← (edge_endpoints_eq w hg).1,
      kmswWindowEdgeMapInf_west w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).1, e.property.2.1]
  · rw [← (edge_endpoints_eq w hg).2,
      kmswWindowEdgeMapInf_east w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).2, e.property.2.2]

private theorem window_path_lifts (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (q : Path a b) :
    ∃ p : Path (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n b.id⟩, p.length = q.length := by
  induction q with
  | nil => exact ⟨Path.nil, rfl⟩
  | cons q e ih =>
    obtain ⟨p, hp⟩ := ih
    have he := window_arrow_data w n e
    refine ⟨p.cons ⟨kmswWindowEdgeMapInf w n e.val, he⟩, ?_⟩
    simp only [Path.length_cons, hp]

private theorem future_boundary_path_in_base (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℕ) (hk : 0 < k)
    (hFuture : BoundaryHitWitnesses
      (fun i => w (boundaryHitTime w h (-(k : ℤ)) + i))) (j : ℕ) :
    let n := boundaryHitTime w h (-(k : ℤ))
    ∃ q : Path (⟨boundaryVertex w h (-(k : ℤ))⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hFuture (j : ℤ))⟩,
      q.length = j := by
  let n := boundaryHitTime w h (-(k : ℤ))
  obtain ⟨p, hp⟩ := futureRightBoundary_path (fun i => w (n + i)) hFuture j
  obtain ⟨q, hq⟩ := window_path_lifts w n p
  have hzero : kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hFuture 0) =
      boundaryVertex w h (-(k : ℤ)) := by
    rw [boundaryVertex_zero, kmswWindowVertexMapInf_eq_stage w n 0 0
      (by change 0 < 2; omega)]
    change (kmswStage w n).west (act w n) = boundaryVertex w h (-(k : ℤ))
    exact boundaryHit_activeInitial_stable_of_ne_zero w h (by omega) le_rfl
  change ∃ q : Path (⟨boundaryVertex w h (-(k : ℤ))⟩ : PresentVertex w)
    ⟨kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hFuture (j : ℤ))⟩, q.length = j
  change q.length = p.length at hq
  have hresult : ∃ q : Path
      (⟨kmswWindowVertexMapInf w n
        (boundaryVertex (fun i => w (n + i)) hFuture 0)⟩ : PresentVertex w)
      ⟨kmswWindowVertexMapInf w n
        (boundaryVertex (fun i => w (n + i)) hFuture (j : ℤ))⟩,
      q.length = j := ⟨q, hq.trans hp⟩
  rw [hzero] at hresult
  exact hresult

private theorem negative_hit_strict (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℕ) (hk : 0 < k) :
    ∀ j < boundaryHitTime w h (-(k : ℤ)), -(k : ℤ) < L w j := by
  have hkneg : -(k : ℤ) ≤ -1 := by omega
  have hfind : boundaryHitTime w h (-(k : ℤ)) =
      Nat.find (h.leftHit (-(k : ℤ)) hkneg) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : -(k : ℤ) ≠ 0),
      dite_eq_right (by omega : ¬0 < -(k : ℤ))]
  intro j hj
  induction j with
  | zero => simp only [L, Finset.sum_range_zero]; omega
  | succ j ih =>
    have hprev := ih (by omega)
    have hnot : L w (j + 1) ≠ -(k : ℤ) := by
      apply Nat.find_min (h.leftHit (-(k : ℤ)) hkneg)
      rw [← hfind]
      exact hj
    have hsum : L w (j + 1) = L w j +
        (RandomWalk.lazyTwoDimensionalStep (w j)).1 := Finset.sum_range_succ _ _
    have hlow : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
      change -1 ≤ ((w j).val : ℤ) - 1
      omega
    omega













theorem exists_stage_path_ge_boundaryBusemannDiff (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hbound : PresentPathLengthsBounded (w := w))
    (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hbound (fun i => ⟨boundaryVertex w h i⟩) X)
    (ell k : ℕ) (hell : 0 < ell) (hlt : ell < k)
    (P : InfinitePresentPath w ⟨boundaryVertex w h (-(ell : ℤ))⟩)
    (hP : P.HasLongestSegments)
    (y : ℕ → PresentVertex w) (hy : Function.Injective y)
    (htail : ∀ T, ∃ N, ∀ r, N ≤ r → ∃ s, T ≤ s ∧ y r = (P.initial s).1)
    (hreach : ∀ r, Reachable (⟨boundaryVertex w h (-(k : ℤ))⟩ : PresentVertex w) (y r))
    (hFuture : BoundaryHitWitnesses
      (fun i => w (boundaryHitTime w h (-(k : ℤ)) + i))) :
    let n := boundaryHitTime w h (-(k : ℤ))
    ∃ a b : StagePresentVertex w n,
      a.id < (kmswStage w n).nextVertex ∧ b.id < (kmswStage w n).nextVertex ∧
      ∃ q : Path a b, (max (X (-(ell : ℤ)) - X (-(k : ℤ))) 0).toNat ≤ q.length := by
  let n := boundaryHitTime w h (-(k : ℤ))
  obtain ⟨T, _, hBefore, j, hj⟩ :=
    first_unpresent_edge_future_boundary w h ell k hlt P hFuture
  obtain ⟨bpath, _⟩ := future_boundary_path_in_base w h k (by omega) hFuture j
  have hz : (P.initial T).1 =
      (⟨kmswWindowVertexMapInf w n
        (boundaryVertex (fun i => w (n + i)) hFuture (j : ℤ))⟩ : PresentVertex w) :=
    congrArg (fun v : ℕ => (⟨v⟩ : PresentVertex w)) hj
  rw [← hz] at bpath
  obtain ⟨N, hN⟩ := htail T
  let y' := fun r => y (N + r)
  have hy' : Function.Injective y' := by
    intro r s hrs
    have heq := hy hrs
    omega
  have htail' : ∀ r, ∃ s, T ≤ s ∧ y' r = (P.initial s).1 := by
    intro r
    exact hN (N + r) (by omega)
  have hrA : ∀ r, Reachable (⟨boundaryVertex w h (-(ell : ℤ))⟩ : PresentVertex w)
      (y' r) := by
    intro r
    obtain ⟨s, _, hs⟩ := htail' r
    rw [hs]
    exact ⟨(P.initial s).2⟩
  have hrZ : ∀ r, Reachable (P.initial T).1 (y' r) := by
    intro r
    obtain ⟨s, hTs, hs⟩ := htail' r
    obtain ⟨_, q, _, _, _, _⟩ := P.exists_shift_split T (s - T)
    have hindex : T + (s - T) = s := by omega
    rw [hindex] at q
    rw [hs]
    exact ⟨q⟩
  have hrBoth : ∀ r, Reachable
      (⟨boundaryVertex w h (-(ell : ℤ))⟩ : PresentVertex w) (y' r) ∧
      Reachable (⟨boundaryVertex w h (-(k : ℤ))⟩ : PresentVertex w) (y' r) :=
    fun r => ⟨hrA r, hreach (N + r)⟩
  have hdecomp := prefix_decomp hbound P hP T rfl y' htail' hrA hrZ
  have hdiff : X (-(ell : ℤ)) - X (-(k : ℤ)) ≤ (T : ℤ) :=
    ldpPrefix_ge_boundaryBusemannDiff hbound
      (fun i => ⟨boundaryVertex w h i⟩) X hX y' hy' hrBoth hrZ bpath T hdecomp
  have hp : ∀ e ∈ pathEdgeList (P.initial T).2,
      e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true := by
    intro e he
    rw [P.prefix_edges T] at he
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
    rw [← hi]
    exact hBefore i.val i.isLt
  obtain ⟨q, hq⟩ := path_lifts_to_stage_of_edges_present w n (P.initial T).2 hp
  have hn : boundaryHitTime w h (-(ell : ℤ)) ≤ n := by
    by_contra hnot
    have hstrict := negative_hit_strict w h ell hell n (by omega)
    have hhit : L w n = -(k : ℤ) := boundaryHitTime_left_spec w h (by omega)
    omega
  have ha := boundaryVertex_lt_stageNextVertex w h (-(ell : ℤ)) n hn
  have hb : (P.initial T).1.id < (kmswStage w n).nextVertex := by
    cases T with
    | zero =>
      have heq := Path.eq_of_length_zero (P.initial 0).2 (P.prefix_length 0)
      have hid := congrArg PresentVertex.id heq
      exact hid ▸ ha
    | succ t =>
      have he := (hBefore t (Nat.lt_succ_self t)).1
      have hend := (kmswStage_endpoints_lt_nextVertex w n (P.edge t) he).2
      rw [(edge_endpoints_eq w he).2, (P.edge_incoming_at_succ w t).2] at hend
      exact hend
  refine ⟨⟨boundaryVertex w h (-(ell : ℤ))⟩, ⟨(P.initial T).1.id⟩, ha, hb, q, ?_⟩
  rw [hq, P.prefix_length]
  omega

end DirectedDistances.PaperProofs.Section7
