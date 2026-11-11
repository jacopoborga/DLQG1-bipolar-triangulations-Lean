module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.KMSW.CommonFutureM0
import DirectedDistances.KMSW.KMSWShift
import DirectedDistances.PaperProofs.Section7.CellLDPUpperConcatenation
import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryMerge
import DirectedDistances.PaperProofs.Section7.CellLDPUpperEdgeMerge
import DirectedDistances.PaperProofs.Section7.CellLDPUpperRouteUp

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open scoped Classical




theorem sdp_cell_upper_chain (dxW dzW dnz dnσ dσW : ℤ)
    (Xl Xs Xk Xns : ℤ) (dxz : ℤ)
    (hgeo : dxz = dxW - dzW)
    (hX : dxW - dσW = Xl - Xs)
    (hXn : dnz - dnσ = Xk - Xns)
    (hseam : dnσ = dσW) (hconf : dnz ≤ dzW) :
    dxz ≤ (Xl - Xs) - (Xk - Xns) := by
  omega



private theorem sdpRecord_R_shift_add (w : ℕ → Fin 3) (t m : ℕ) :
    R w (t + m) = R w t + R (fun i => w (t + i)) m := by
  induction m with
  | zero => simp [R]
  | succ m ih =>
    have hg : R w (t + m + 1) = R w (t + m) +
        (RandomWalk.lazyTwoDimensionalStep (w (t + m))).2 :=
      Finset.sum_range_succ _ _
    have hs : R (fun i => w (t + i)) (m + 1) =
        R (fun i => w (t + i)) m +
          (RandomWalk.lazyTwoDimensionalStep (w (t + m))).2 :=
      Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hs, ih]
    omega




private theorem sdpRecord_window_image (w : ℕ → Fin 3) (n t : ℕ) :
    (⟨kmswWindowVertexMapInf w n
      (recordVertex (fun i => w (n + i)) t).id⟩ : PresentVertex w) =
      recordVertex w (n + t) := by
  let u : ℕ → Fin 3 := fun i => w (n + i)
  have he : act u t < (kmswStage u t).nextEdge :=
    act_lt_nextEdge u (Nat.le_refl t)
  have hactive := (kmswWindowPatchData_rel w n t).active
  change (kmswWindowPatchData w n t).φ (act u t) = act w (n + t) at hactive
  have hmap : kmswWindowEdgeMapInf w n (act u t) = act w (n + t) := by
    rw [kmswWindowEdgeMapInf_eq_stage w n t (act u t) he]
    exact hactive
  have hwest := kmswWindowEdgeMapInf_west w n t (act u t) he
  apply congrArg (fun v : ℕ => (⟨v⟩ : PresentVertex w))
  change kmswWindowVertexMapInf w n ((kmswStage u t).west (act u t)) =
    (kmswStage w (n + t)).west (act w (n + t))
  rw [← hwest, hmap]




theorem cell_sdp_upper_record_targets (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (ℓ k : ℤ)
    (hℓ : boundaryVertex w h0 ℓ < (kmswStage w n).nextVertex) :
    ∃ y : ℕ → PresentVertex (fun i => w (n + i)), Function.Injective y ∧
      (∀ j, Reachable
        (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
        Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
          (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
      (∀ j, Reachable (boundaryPresentVertex w h0 ℓ)
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w) ∧
        Reachable (boundaryPresentVertex w h0 ((kmswStage w n).LR.length : ℤ))
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)) ∧
      (∀ j, ∃ m, n < m ∧
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w) =
          recordVertex w m) := by
  let u : ℕ → Fin 3 := fun i => w (n + i)
  let σn : ℤ := ((kmswStage w n).UR.length + 1 : ℕ)
  obtain ⟨k', _, _, hr⟩ := stage_cell_upper_boundary_route w n hn
    (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n) hℓ
  have hr0 := stageToLimit_reachable w n hr
  obtain ⟨nk, hk⟩ := boundaryVertex_allocated u hn k
  obtain ⟨ns, hs⟩ := boundaryVertex_allocated u hn σn
  obtain ⟨nk', hk'⟩ := boundaryVertex_allocated u hn k'
  let Nfuture := max nk (max ns nk')
  let N := n + Nfuture
  have hnkN : nk ≤ Nfuture := by
    change nk ≤ max nk (max ns nk')
    exact Nat.le_max_left _ _
  have hnsN : ns ≤ Nfuture := by
    change ns ≤ max nk (max ns nk')
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hnk'N : nk' ≤ Nfuture := by
    change nk' ≤ max nk (max ns nk')
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  let P : ℕ → Prop := fun m => ∀ i < m, R w m < R w i
  have hP : {m | P m}.Infinite := by
    simpa [P] using
      right_record_infinite w (R_unbounded_below_of_boundaryHitWitnesses w h0)
  let q : ℕ → ℕ := fun j => natSelect P (N + j + 1)
  have hrecord (j : ℕ) : ∀ i < q j, R w (q j) < R w i := by
    intro i hi
    exact (natSelect_spec hP (N + j + 1)).1 i hi
  have hcount (j : ℕ) : Nat.count P (q j) = N + j + 1 :=
    natSelect_spec hP (N + j + 1) |>.2
  have hqgt (j : ℕ) : N < q j := by
    have hh : Nat.count P (q j) ≤ q j := Nat.count_le P
    rw [hcount j] at hh
    omega
  have hqmono : StrictMono q := by
    intro i j hij
    by_contra hnot
    have hh := Nat.count_monotone (p := P) (Nat.le_of_not_gt hnot)
    rw [hcount j, hcount i] at hh
    omega
  have hshift (j : ℕ) : ∀ i < q j - n,
      R u (q j - n) ≤ R u i - 1 := by
    intro i hi
    have hglobal := hrecord j (n + i) (by omega)
    have htime : n + (q j - n) = q j := by have := hqgt j; omega
    have htarget : R w (q j) = R w n + R u (q j - n) := by
      have hh := sdpRecord_R_shift_add w n (q j - n)
      rw [htime] at hh
      simpa [u] using hh
    have hprior : R w (n + i) = R w n + R u i := by
      simpa [u] using sdpRecord_R_shift_add w n i
    rw [htarget, hprior] at hglobal
    omega
  let y : ℕ → PresentVertex u := fun j => recordVertex u (q j - n)
  have hy : Function.Injective y := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have htime : q i - n < q j - n := by
        have hm := hqmono hlt
        have hjn := hqgt j
        omega
      exact recordVertex_ne u htime (hshift j) hij
    · have htime : q j - n < q i - n := by
        have hm := hqmono hgt
        have hin := hqgt i
        omega
      exact recordVertex_ne u htime (hshift i) hij.symm
  have reaches (d : ℤ) (nd : ℕ)
      (hd : boundaryVertex u hn d < (kmswStage u nd).nextVertex)
      (hnd : nd ≤ Nfuture) (j : ℕ) :
      Reachable (boundaryPresentVertex u hn d) (y j) := by
    have htime : n + (q j - n) = q j := by have := hqgt j; omega
    have hstage : nd ≤ q j - n - 1 := by have := hqgt j; omega
    have halloc : boundaryVertex u hn d <
        (kmswStage u (q j - n - 1)).nextVertex :=
      hd.trans_le (CutConverse.nextVertex_mono u hstage)
    have hpos : 0 < q j - n := by
      have hq := hqgt j
      dsimp [N] at hq
      omega
    have hreach := allocated_vertex_reaches_strict_record u (q j - n)
      (hshift j) hpos (boundaryVertex u hn d) halloc
    simpa [boundaryPresentVertex, y] using hreach
  have hseam : boundaryVertex w h0 ((kmswStage w n).LR.length : ℤ) =
      kmswWindowVertexMapInf w n (boundaryVertex u hn σn) := by
    have hmerge : ∀ r : ℕ, 1 ≤ r →
        kmswRightBoundaryEdge w (r - 1 + (kmswStage w n).LR.length) =
          kmswWindowEdgeMapInf w n
            (kmswRightBoundaryEdge u
              (r - 1 + ((kmswStage w n).UR.length + 1))) := by
      intro r _hr
      exact rightBoundary_edge_merge_explicit w n h0 hn (r - 1)
    have hs := rightBoundary_vertices_merge_of_edges w n
      (kmswStage w n).LR.length ((kmswStage w n).UR.length + 1)
      h0 hn hmerge 0
    simpa only [Nat.zero_add, u, σn] using hs
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · intro j
    exact ⟨reaches k nk hk hnkN j, reaches σn ns hs hnsN j⟩
  · intro j
    constructor
    · obtain ⟨p⟩ := (reaches k' nk' hk' hnk'N j)
      obtain ⟨q', _⟩ := cell_window_path_forward w n p
      exact hr0.trans ⟨q'⟩
    · obtain ⟨p⟩ := (reaches σn ns hs hnsN j)
      obtain ⟨q', _⟩ := cell_window_path_forward w n p
      change Reachable (⟨boundaryVertex w h0
        ((kmswStage w n).LR.length : ℤ)⟩ : PresentVertex w) _
      rw [hseam]
      exact ⟨q'⟩
  · intro j
    refine ⟨q j, by have := hqgt j; dsimp [N] at this; omega, ?_⟩
    have htime : n + (q j - n) = q j := by have := hqgt j; omega
    change (⟨kmswWindowVertexMapInf w n
      (recordVertex u (q j - n)).id⟩ : PresentVertex w) = recordVertex w (q j)
    have h := sdpRecord_window_image w n (q j - n)
    rw [htime] at h
    exact h

end DirectedDistances.PaperProofs.Section7
