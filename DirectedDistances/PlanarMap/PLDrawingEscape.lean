module

public import DirectedDistances.PlanarMap.PlaneRealization
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Set.Finite.Lattice







public section

namespace DirectedDistances.PlanarMap




theorem locally_finite_of_birthHalfPlane {D V : Type*}
    (flip : D → D) (vert : D → V) (arc : D → Polyline) (b : V → ℝ)
    (h1 : ∀ d z, z ∈ (arc d).image →
      min (b (vert d)) (b (vert (flip d))) ≤ z.im)
    (h2 : ∀ N : ℝ, {v | b v ≤ N}.Finite)
    (h3 : ∀ v, {d | vert d = v ∨ vert (flip d) = v}.Finite) :
    ∀ K : Set ℂ, Bornology.IsBounded K →
      {d | (K ∩ (arc d).image).Nonempty}.Finite := by
  intro K hK
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  have hfinite :
      (⋃ v ∈ {v | b v ≤ R}, {d | vert d = v ∨ vert (flip d) = v}).Finite :=
    (h2 R).biUnion (fun v _ => h3 v)
  apply hfinite.subset
  intro d hd
  obtain ⟨z, hzK, hzd⟩ := hd
  have hmin : min (b (vert d)) (b (vert (flip d))) ≤ R :=
    (h1 d z hzd).trans ((Complex.im_le_norm z).trans (hR z hzK))
  rcases min_le_iff.mp hmin with hleft | hright
  · exact Set.mem_iUnion₂.mpr ⟨vert d, hleft, Or.inl rfl⟩
  · exact Set.mem_iUnion₂.mpr ⟨vert (flip d), hright, Or.inr rfl⟩




theorem locally_finite_of_heightHalfPlane {D V : Type*}
    (flip : D → D) (vert : D → V) (pos : V → ℂ) (arc : D → Polyline)
    (h1 : ∀ d z, z ∈ (arc d).image →
      min (pos (vert d)).im (pos (vert (flip d))).im ≤ z.im)
    (h2 : ∀ N : ℝ, {v | (pos v).im ≤ N}.Finite)
    (h3 : ∀ v, {d | vert d = v ∨ vert (flip d) = v}.Finite) :
    ∀ K : Set ℂ, Bornology.IsBounded K →
      {d | (K ∩ (arc d).image).Nonempty}.Finite := by
  exact locally_finite_of_birthHalfPlane flip vert arc (fun v => (pos v).im) h1 h2 h3

end DirectedDistances.PlanarMap
