module

public import DirectedDistances.Recursive.LDPExpansionF
import DirectedDistances.Recursive.LDPNondegenerate
import DirectedDistances.Recursive.LDPQuadraticFromMaster
import DirectedDistances.PaperProofs.Section6.Next.CharacteristicDiscriminant

/-! # Conditional LDP discriminant and actual-transform bridge

The discriminant is exactly `Δ(F) = (3F - 1)^2 - 4F^3` from
The quadratic for the actual shifted transform is derived from the displayed
master recursion, which remains a hypothesis. This helper does not discharge -/

public section
namespace DirectedDistances.Recursive

/-- not the paper result. The source discriminant is negative and the actual
shifted transform has nonzero imaginary part on one positive interval. -/
theorem ldp_discriminant_and_actual_transform_nonreal_of_master {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (3 * (integerCF f t).re - 1) ^ 2 - 4 * (integerCF f t).re ^ 3 < 0 ∧
      (ldpHat f t).im ≠ 0 := by
  obtain ⟨hf_lt, _⟩ := ldp_pmf_nondegenerate_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  obtain ⟨δ, hδ, hdisc⟩ :=
    DirectedDistances.PaperProofs.Section6.exists_integer_characteristic_discriminant_neg
      hf hfs hsymm (hf_lt 0)
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd
  obtain ⟨_, hnegative, hroot⟩ := hdisc t ht htd
  constructor
  · simpa only [integerCF] using hnegative
  · apply hroot (ldpHat f t)
    simpa only [integerCF] using
      ldp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec t

end DirectedDistances.Recursive
