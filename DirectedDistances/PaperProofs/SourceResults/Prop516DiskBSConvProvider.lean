/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516SourceGeometricLaw

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/




















public section
noncomputable section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5
open MeasureTheory Filter
open scoped Topology

-- The geometric Borel structure on rooted map classes.
local instance instBorelD39Class_Prop516DiskBSConvProvider :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance instBorelSpaceD39Class_Prop516DiskBSConvProvider :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩




theorem prop_disk_bs_conv_source_provider
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    Tendsto (fun k => finiteGeometricLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop
      (𝓝 uibhbotSourceGeometricClassLaw) :=
  finiteGeometricLaw_tendsto_uibhbotSourceGeometricClassLaw A hA ell hadm hlo hhi

end DirectedDistances.PaperProofs.SourceResults
