/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass9

/-! Helper toward Definition 3.8 (consumer).

# Orientation of the canonical past seam change -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 (consumer): changing the height function in
the past transfer is conjugate to a vertical seam shear, with the abscissa
reversed by the common past transfer. -/
theorem uibhbotPastTransfer_changeSeam_eq_verticalShear
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (pastTransferHomeomorph (OrderIso.refl ℝ) (fun _ => 0) f
        continuous_const hf).symm.trans
        (pastTransferHomeomorph (OrderIso.refl ℝ) (fun _ => 0) g
          continuous_const hg) =
      uibhbotVerticalSeamTransfer (fun x => f (-x)) (fun x => g (-x))
        (hf.comp continuous_neg) (hg.comp continuous_neg) := by
  apply Homeomorph.ext
  intro z
  apply Complex.ext
  · simp [pastTransferHomeomorph, pastTransfer, pastTransferInv,
      uibhbotVerticalSeamTransfer]
  · simp [pastTransferHomeomorph, pastTransfer, pastTransferInv,
      uibhbotVerticalSeamTransfer]
    ring

/-- Helper toward Definition 3.8 (consumer): the seam change between two past
transfers preserves winding numbers, including when their seam heights vary
with the horizontal coordinate. -/
theorem uibhbotPastTransfer_changeSeam_orientationPreserving
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    OrientationPreserving
      ((pastTransferHomeomorph (OrderIso.refl ℝ) (fun _ => 0) f
          continuous_const hf).symm.trans
        (pastTransferHomeomorph (OrderIso.refl ℝ) (fun _ => 0) g
          continuous_const hg)) := by
  rw [uibhbotPastTransfer_changeSeam_eq_verticalShear]
  exact uibhbotVerticalSeamTransfer_orientationPreserving
    (fun x => f (-x)) (fun x => g (-x))
    (hf.comp continuous_neg) (hg.comp continuous_neg)

/-- Helper toward Definition 3.8 (consumer): the orientation-preserving plane
homeomorphism between two canonical past transfer coordinates. This statement
supplies the seam-change part of a finite-ball drawing comparison; it does not
assert an isomorphism of the full rooted maps. -/
theorem uibhbotD39PastStraightTransfer_changeSeam_orientationPreserving
    (W W' : ℤ → Fin 3)
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hL' : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W') n = a)
    (hR' : ∀ n, 0 ≤ R (kmswPastCode W') n) :
    OrientationPreserving
      ((uibhbotPastStraightTransfer W hL hR).symm.trans
        (uibhbotPastStraightTransfer W' hL' hR')) := by
  exact uibhbotPastTransfer_changeSeam_orientationPreserving
    (uibhbotPastSeamHeight W hL hR)
    (uibhbotPastSeamHeight W' hL' hR')
    (uibhbotPastSeamHeight_continuous W hL hR)
    (uibhbotPastSeamHeight_continuous W' hL' hR')



























































end DirectedDistances.PaperProofs.Section5

end
