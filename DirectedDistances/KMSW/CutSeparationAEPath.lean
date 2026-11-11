/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.CutSeparationAE
public import DirectedDistances.KMSW.InfiniteBoundary
import DirectedDistances.RandomWalk.SecondCoordinateUnbounded

/-! # Non-vacuity for almost-sure path separation

The lower-right boundary supplies an infinite directed path from the root when the horizontal
coordinate stays nonnegative and the vertical coordinate is unbounded below -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk

/-- The lower-right boundary edges are present, pairwise distinct, and form an infinite
directed path from vertex `0` under the nonnegativity and unboundedness assumptions -/
theorem kmswRightBoundary_infinite_path (w : ℕ → Fin 3)
    (hL0 : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    Function.Injective (kmswRightBoundaryEdge w) ∧
      (∀ i, edgeEast w (kmswRightBoundaryEdge w i) =
        edgeWest w (kmswRightBoundaryEdge w (i + 1))) ∧
      edgeWest w (kmswRightBoundaryEdge w 0) = 0 ∧
      (∀ i, ∃ n, (kmswStage w n).present (kmswRightBoundaryEdge w i) = true) := by
  let P : ℕ → Prop := fun m => ∀ j, j < m → R w m < R w j
  have hrecords := right_record_infinite w hR
  have hinj : Function.Injective (kmswRightBoundaryEdge w) := by
    intro i j hij
    have htime : natSelect P i = natSelect P j := by
      apply CutConverse.act_injective w
      simpa [kmswRightBoundaryEdge, P] using hij
    have hci := (natSelect_spec (P := P) hrecords i).2
    have hcj := (natSelect_spec (P := P) hrecords j).2
    calc
      i = Nat.count P (natSelect P i) := hci.symm
      _ = Nat.count P (natSelect P j) := congrArg (Nat.count P) htime
      _ = j := hcj
  have hstep : ∀ i,
      edgeEast w (kmswRightBoundaryEdge w i) =
        edgeWest w (kmswRightBoundaryEdge w (i + 1)) := by
    intro i
    obtain ⟨N₁, hN₁⟩ := kmswStage_LR_getElem?_eventually w hR i
    obtain ⟨N₂, hN₂⟩ := kmswStage_LR_getElem?_eventually w hR (i + 1)
    let n := max N₁ N₂
    have hi := hN₁ n (le_trans (le_max_left _ _) (le_refl n))
    have hi1 := hN₂ n (le_trans (le_max_right _ _) (le_refl n))
    let s := kmswStage w n
    have hLL : s.LL = [] := kmswStage_LL_eq_nil w hL0 n
    have hchain : List.IsChain (fun e f => s.east e = s.west f) s.LR := by
      have hlow := (kmswStage_boundary_chain_invariant w n).2.1
      change WestEastChain s (s.LL ++ s.LR) at hlow
      rw [hLL] at hlow
      simpa [WestEastChain] using hlow
    obtain ⟨hidx, hval⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hidx1, hval1⟩ := List.getElem?_eq_some_iff.mp hi1
    have hrel := hchain.getElem i hidx1
    rw [hval, hval1] at hrel
    have hmem : kmswRightBoundaryEdge w i ∈ s.LR := by
      rw [← hval]
      exact List.getElem_mem hidx
    have hmem1 : kmswRightBoundaryEdge w (i + 1) ∈ s.LR := by
      rw [← hval1]
      exact List.getElem_mem hidx1
    have hbound0 : kmswRightBoundaryEdge w i < s.nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
        simp only [List.mem_append]
        tauto)
    have hbound1 : kmswRightBoundaryEdge w (i + 1) < s.nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
        simp only [List.mem_append]
        tauto)
    have he0 := (edge_endpoints_eq w hbound0)
    have he1 := (edge_endpoints_eq w hbound1)
    calc
      edgeEast w (kmswRightBoundaryEdge w i) = s.east (kmswRightBoundaryEdge w i) :=
        he0.2.symm
      _ = s.west (kmswRightBoundaryEdge w (i + 1)) := hrel
      _ = edgeWest w (kmswRightBoundaryEdge w (i + 1)) := he1.1
  have hstart : edgeWest w (kmswRightBoundaryEdge w 0) = 0 := by
    rw [kmswRightBoundaryEdge_zero]
    simp [edgeWest, kmswStage, kmswInit]
  have hpresent : ∀ i, ∃ n, (kmswStage w n).present (kmswRightBoundaryEdge w i) = true := by
    intro i
    obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually w hR i
    have he := hN N le_rfl
    obtain ⟨hidx, hval⟩ := List.getElem?_eq_some_iff.mp he
    have hmem : kmswRightBoundaryEdge w i ∈ (kmswStage w N).LR := by
      rw [← hval]
      exact List.getElem_mem hidx
    exact ⟨N, (kmswStage_status w N).2.2.1 _ hmem⟩
  exact ⟨hinj, hstep, hstart, hpresent⟩

/-- Almost surely there is an infinite injective directed path from `0`, and infinitely many -/
theorem pitmanCodes_ae_path_and_unavoidable_recordVertices :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      (∃ e : ℕ → ℕ,
        Function.Injective e ∧
        (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) ∧
        edgeWest w (e 0) = 0 ∧
        (∀ i, ∃ n, (kmswStage w n).present (e i) = true)) ∧
      {v : ℕ | ∀ e : ℕ → ℕ,
        (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) →
        edgeWest w (e 0) = 0 → Function.Injective e →
        ∃ i, edgeWest w (e i) = v ∨ edgeEast w (e i) = v}.Infinite := by
  have hRae := RandomWalk.pitmanCodes_ae_R_unbounded_below
  have hVae := pitmanCodes_ae_infinite_unavoidable_recordVertices
  filter_upwards [hRae, hVae] with ω hR hV
  let w : ℕ → Fin 3 := pitmanCode (fun i => ω (i + 1))
  have hL0 : ∀ j, 0 ≤ L w j := by
    intro j
    rw [RandomWalk.kmsw_L_eq]
    exact integrateCodes_pitmanCode_fst_nonneg _ j
  have hR' : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hR a
    exact ⟨n, by rw [RandomWalk.kmsw_R_eq]; exact hn⟩
  have hpath := kmswRightBoundary_infinite_path w hL0 hR'
  refine ⟨?_, hV⟩
  exact ⟨kmswRightBoundaryEdge w, hpath.1, hpath.2.1, hpath.2.2.1, hpath.2.2.2⟩

end DirectedDistances.KMSW
