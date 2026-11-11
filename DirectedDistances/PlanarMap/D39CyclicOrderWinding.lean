module

public import DirectedDistances.PlanarMap.D39DrawingRepresentation3Unique
































public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. A singleton star has the same successor
for every direction assignment. -/
theorem d39_ccw_successor_transfer_of_singleton
    {D : Type*} {star : Set D} {dir dir' : D → ℂ} {d e : D}
    (hstar : star = {d}) (hsucc : CcwSuccessor star dir d e) :
    CcwSuccessor star dir' d e := by
  rcases hsucc with ⟨hfinite, hd, he, _⟩
  have heq : e = d := Set.mem_singleton_iff.mp (hstar ▸ he)
  subst e
  exact ⟨hfinite, hd, hd, Or.inl ⟨rfl, hstar⟩⟩









































end DirectedDistances.PlanarMap

end

