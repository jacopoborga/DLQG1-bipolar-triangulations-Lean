module
public import Palomar.Principal.Support.DiskLocalLimitSource
@[expose] public section
noncomputable section
namespace DLQG1.Palomar.Principal
open MeasureTheory Filter DLQG1.Palomar.DiskMinimal
attribute [local instance] DLQG1.Palomar.GeometryInterface.metric
attribute [local instance] DLQG1.Palomar.GeometryInterface.topology
attribute [local instance] DLQG1.Palomar.DiskMinimal.modelMeasurable
attribute [local instance] DLQG1.Palomar.DiskMinimal.modelBorel
theorem disk_local_limit (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    Tendsto (fun k => finiteLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop
      (nhds DLQG1.Palomar.GeometryLawMinimal.sourceLaw) := by
  exact DLQG1.Palomar.DiskMinimal.disk_local_limit A hA ell hadm hlo hhi
end DLQG1.Palomar.Principal
