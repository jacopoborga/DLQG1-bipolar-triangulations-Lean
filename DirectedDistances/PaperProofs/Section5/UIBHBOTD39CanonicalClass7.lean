/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass6

/-! Helper toward Definition 3.8 (consumer).

# Finite-window locality of the certified capture event -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open Set

/-- Helper toward Definition 3.8 (consumer): the finite-stage strong capture
event is determined by the code letters in the window that builds the stage. -/
theorem uibhbotD39StrongCaptureEvent_iff_of_codeWindow
    (W W' : ℤ → Fin 3) (N m r c : ℕ) (hm : m ≤ 2 * N)
    (hwindow : ∀ i : ℤ,
      i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    kmswWindowCaptureEventStrongRel (shiftedStream W' N) m r c ↔
      kmswWindowCaptureEventStrongRel (shiftedStream W N) m r c := by
  apply kmswWindowCaptureEventStrongRel_congr
  intro i hi
  have hlo : -(N : ℤ) ≤ (i : ℤ) - N := by omega
  have hhi : (i : ℤ) - N ≤ N := by omega
  exact hwindow ((i : ℤ) - N) ⟨hlo, hhi⟩

/-- Helper toward Definition 3.8 (consumer): the finite list of left-seam
indices associated with a captured finite stage is determined by its code
window. -/
theorem uibhbotD39LeftSeamSet_eq_of_codeWindow
    (W W' : ℤ → Fin 3) (N m r c : ℕ) (hm : m ≤ 2 * N)
    (hwindow : ∀ i : ℤ,
      i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    kmswBallLeftSeamSet (shiftedStream W' N) m r c =
      kmswBallLeftSeamSet (shiftedStream W N) m r c := by
  have hcode : ∀ i < m,
      shiftedStream W' N i = shiftedStream W N i := by
    intro i hi
    have hlo : -(N : ℤ) ≤ (i : ℤ) - N := by omega
    have hhi : (i : ℤ) - N ≤ N := by omega
    exact hwindow ((i : ℤ) - N) ⟨hlo, hhi⟩
  have hstage (k : ℕ) (hk : k ≤ m) :
      kmswStage (shiftedStream W' N) k = kmswStage (shiftedStream W N) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        have hk' : k ≤ m := by omega
        have hi : k < m := by omega
        change kmswStep (kmswStage (shiftedStream W' N) k)
            (shiftedStream W' N k) =
          kmswStep (kmswStage (shiftedStream W N) k)
            (shiftedStream W N k)
        rw [ih hk', hcode k hi]
  classical
  ext k
  simp only [kmswBallLeftSeamSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hv⟩
    refine ⟨hk, ?_⟩
    simpa only [hstage m le_rfl, hstage k (Nat.le_of_lt hk), hcode k hk] using hv
  · rintro ⟨hk, hv⟩
    refine ⟨hk, ?_⟩
    simpa only [hstage m le_rfl, hstage k (Nat.le_of_lt hk), hcode k hk] using hv















































































end DirectedDistances.PaperProofs.Section5

end
