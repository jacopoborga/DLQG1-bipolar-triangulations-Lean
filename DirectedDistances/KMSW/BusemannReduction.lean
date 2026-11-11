module

public import DirectedDistances.KMSW.FiniteAvoidance
public import DirectedDistances.KMSW.ActiveTimeMonotone

/-! Supporting lemmas for paper labels `def-ldp`, `lem-infty-cut`, `lem-uibot-bdy`, `thm-busemann` (see CORRESPONDENCE.md). -/

/-! # Reduction of the Busemann existence statements to two labelled premises

Under geometric local finiteness (`hfin`), the bounded-path-length input of the
LDP construction is discharged by `present_pathLengths_bddAbove`. The results
for the KMSW limit of any locally finite code to two labelled premises:
window finite avoidance (producer: `lem-infty-cut` via cut vertices of
sequences (producer: the footnote to `thm-busemann` and `lem-uibot-bdy`,
LDP is `-∞` (never `0`) on unreachable pairs; the statements only use finite
LDP values on reachable pairs. -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver

/-- Geometric local finiteness bounds all present path lengths, discharging the
bounded-length input of the LDP construction (`def-ldp`, -/
theorem presentPathLengthsBounded_of_hfin (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    PresentPathLengthsBounded (w := w) :=
  fun a b _ => present_pathLengths_bddAbove w hfin a b



theorem existsUnique_ldpBusemann_of_hfin (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (x : ℤ → PresentVertex w) (hcut : BusemannCutHypothesis x)
    (hcommon : BusemannCommonSequenceHypothesis x) :
    ∃! X : ℤ → ℤ, X 0 = 0 ∧
      ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w,
        (hy : Function.Injective y) →
        (hyr : ∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
          ∃ N, ∀ j, N ≤ j →
            X k' - X k =
              (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin)
                  (hyr j).2 : ℤ) -
                (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin)
                  (hyr j).1 : ℤ) :=
  existsUnique_ldpBoundaryDifference_from_cut x hcut hcommon
    (presentPathLengthsBounded_of_hfin w hfin)

/-- SDP boundary differences from window finite avoidance
reduction of `thm-busemann`, not its proof. -/
theorem existsUnique_sdpBusemann_of_finiteAvoidance (w : ℕ → Fin 3)
    (x : ℤ → PresentVertex w)
    (havoid : ∀ K : ℕ, ∃ z : PresentVertex w,
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K → FiniteAvoidance (x k) z)
    (hcommon : BusemannCommonSequenceHypothesis x) :
    ∃! X : ℤ → ℤ, X 0 = 0 ∧
      ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w, Function.Injective y →
        (∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
          ∃ N, ∀ j, N ≤ j →
            X k' - X k =
              ((sdp (x k') (y j)).toNat : ℤ) - ((sdp (x k) (y j)).toNat : ℤ) :=
  existsUnique_sdpBoundaryDifference_from_cut x
    (finiteAvoidance_implies_busemannCutHypothesis x havoid) hcommon

/-- LDP boundary differences from window finite avoidance, local finiteness
and the common reachable sequence premise. Conditional reduction of -/
theorem existsUnique_ldpBusemann_of_finiteAvoidance (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (x : ℤ → PresentVertex w)
    (havoid : ∀ K : ℕ, ∃ z : PresentVertex w,
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K → FiniteAvoidance (x k) z)
    (hcommon : BusemannCommonSequenceHypothesis x) :
    ∃! X : ℤ → ℤ, X 0 = 0 ∧
      ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w,
        (hy : Function.Injective y) →
        (hyr : ∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
          ∃ N, ∀ j, N ≤ j →
            X k' - X k =
              (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin)
                  (hyr j).2 : ℤ) -
                (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin)
                  (hyr j).1 : ℤ) :=
  existsUnique_ldpBusemann_of_hfin w hfin x
    (finiteAvoidance_implies_busemannCutHypothesis x havoid) hcommon

end DirectedDistances.KMSW
