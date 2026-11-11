module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.KMSW.CommonFutureM0
import DirectedDistances.PaperProofs.Section7.CellLDPUpperConcatenation
import DirectedDistances.PaperProofs.Section7.CellLDPUpperEdgeMerge
import DirectedDistances.PaperProofs.Section7.CellLDPUpperRouteUp

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open scoped Classical



private theorem boundary_triple_common_sequence (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (a b c : ℤ) :
    ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
      ∀ j, Reachable (boundaryPresentVertex w h a) (y j) ∧
        Reachable (boundaryPresentVertex w h b) (y j) ∧
        Reachable (boundaryPresentVertex w h c) (y j) := by
  obtain ⟨na, ha⟩ := boundaryVertex_allocated w h a
  obtain ⟨nb, hb⟩ := boundaryVertex_allocated w h b
  obtain ⟨nc, hc⟩ := boundaryVertex_allocated w h c
  let N := max na (max nb nc)
  let P : ℕ → Prop := fun m => ∀ i < m, R w m < R w i
  have hP : {m | P m}.Infinite :=
    right_record_infinite w (R_unbounded_below_of_boundaryHitWitnesses w h)
  let q : ℕ → ℕ := fun j => natSelect P (N + j + 1)
  have hrecord (j : ℕ) : ∀ i < q j, R w (q j) ≤ R w i - 1 := by
    intro i hi
    have hh : R w (q j) < R w i := (natSelect_spec hP (N + j + 1)).1 i hi
    omega
  have hcount (j : ℕ) : Nat.count P (q j) = N + j + 1 :=
    (natSelect_spec hP (N + j + 1)).2
  have hgt (j : ℕ) : N < q j := by
    have hh : Nat.count P (q j) ≤ q j := Nat.count_le P
    rw [hcount j] at hh
    omega
  have hmono : StrictMono q := by
    intro i j hij
    by_contra hnot
    have hh := Nat.count_monotone (p := P) (Nat.le_of_not_gt hnot)
    rw [hcount j, hcount i] at hh
    omega
  have reaches (d : ℤ) (nd : ℕ)
      (hd : boundaryVertex w h d < (kmswStage w nd).nextVertex)
      (hnd : nd ≤ N) (j : ℕ) :
      Reachable (boundaryPresentVertex w h d) (recordVertex w (q j)) := by
    have hstage : nd ≤ q j - 1 := by have := hgt j; omega
    exact allocated_vertex_reaches_strict_record w (q j) (hrecord j)
      (by have := hgt j; omega) (boundaryVertex w h d)
      (hd.trans_le (CutConverse.nextVertex_mono w hstage))
  refine ⟨fun j => recordVertex w (q j), ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt'
    · exact False.elim (recordVertex_ne w (hmono hlt) (hrecord j) hij)
    · exact heq
    · exact False.elim (recordVertex_ne w (hmono hgt') (hrecord i) hij.symm)
  · exact reaches a na ha (Nat.le_max_left _ _) j
  · exact reaches b nb hb ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) j
  · exact reaches c nc hc ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)) j




theorem cell_common_target (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (ℓ k : ℤ)
    (hℓ : boundaryVertex w h0 ℓ < (kmswStage w n).nextVertex) :
    ∃ y : ℕ → PresentVertex (fun i => w (n + i)), Function.Injective y ∧
      (∀ j, Reachable (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
        Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
          (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
      (∀ j, Reachable (boundaryPresentVertex w h0 ℓ)
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w) ∧
        Reachable (boundaryPresentVertex w h0 ((kmswStage w n).LR.length : ℤ))
          (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)) := by
  obtain ⟨k', _, _, hr⟩ := stage_cell_upper_boundary_route w n hn
    (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n) hℓ
  have hr0 := stageToLimit_reachable w n hr
  obtain ⟨y, hy, hyr⟩ := boundary_triple_common_sequence (fun i => w (n + i)) hn
    k (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) k'
  have hmerge : ∀ q : ℕ, 1 ≤ q →
      kmswRightBoundaryEdge w (q - 1 + (kmswStage w n).LR.length) =
        kmswWindowEdgeMapInf w n
          (kmswRightBoundaryEdge (fun i => w (n + i))
            (q - 1 + ((kmswStage w n).UR.length + 1))) := by
    intro q _hq
    exact rightBoundary_edge_merge_explicit w n h0 hn (q - 1)
  have hseam := rightBoundary_vertices_merge_of_edges w n
    (kmswStage w n).LR.length ((kmswStage w n).UR.length + 1) h0 hn hmerge 0
  simp only [Nat.zero_add] at hseam
  refine ⟨y, hy, fun j => ⟨(hyr j).1, (hyr j).2.1⟩, fun j => ⟨?_, ?_⟩⟩
  · obtain ⟨q⟩ := (hyr j).2.2
    obtain ⟨p, _⟩ := cell_window_path_forward w n q
    exact hr0.trans ⟨p⟩
  · obtain ⟨q⟩ := (hyr j).2.1
    obtain ⟨p, _⟩ := cell_window_path_forward w n q
    change Reachable (⟨boundaryVertex w h0 ((kmswStage w n).LR.length : ℤ)⟩ :
      PresentVertex w) _
    rw [hseam]
    exact ⟨p⟩

end DirectedDistances.PaperProofs.Section7
