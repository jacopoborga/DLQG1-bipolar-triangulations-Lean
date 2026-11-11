module

public import DirectedDistances.KMSW.EventuallyPresent
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.PlanarMap.PlaneRealization
















public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap




theorem kmsw_edgePresent_of_uiqbot (w : ℕ → Fin 3) (hL0 : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (e : ℕ) : EdgePresent w e := by
  obtain ⟨N, hN⟩ := eventually_present_of_nonneg_of_unbounded w hL0 hR e
  exact ⟨N, hN N le_rfl⟩






theorem kmswConstructedDrawing_edgeCarrier (w : ℕ → Fin 3) (hL0 : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) :
    (∀ d : ℕ × Bool, EdgePresent w d.1 ∧
      kmswLimitDartVertex w d = if d.2 then edgeEast w d.1 else edgeWest w d.1) ∧
    {e : ℕ | EdgePresent w e} = Set.univ := by
  refine ⟨fun d => ⟨kmsw_edgePresent_of_uiqbot w hL0 hR d.1, rfl⟩, ?_⟩
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact kmsw_edgePresent_of_uiqbot w hL0 hR e

end DirectedDistances.KMSW
