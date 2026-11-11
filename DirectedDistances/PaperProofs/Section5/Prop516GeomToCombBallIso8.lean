module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso7
public import DirectedDistances.PlanarMap.D39RadialOrder14







public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. A counterclockwise successor transports
across corresponding radial segments, assuming the three-germ turn-order
comparison. -/
theorem d39_CcwSuccessor_transport_of_radial_segments
    {D : Type*} {star : Set D} {dir dir' : D → ℂ} {d e : D}
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (hThreeGerm :
      ∀ (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
        (u v w u' v' w' : ℂ)
        (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
        (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
        (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
        (hvw : v.arg ≠ w.arg)
        (hsegmentsU : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
          K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
            {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
        (hsegmentsV : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
          K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * v} =
            {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v'})
        (hsegmentsW : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
          K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * w} =
            {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * w'}),
        ccwTurn u w < ccwTurn u v ↔ ccwTurn u' w' < ccwTurn u' v')
    (hdir : ∀ x ∈ star, dir x ≠ 0 ∧ dir' x ≠ 0)
    (harg : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (hsegments : ∀ x ∈ star, ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * dir x} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * dir' x})
    (hsucc : CcwSuccessor star dir d e) :
    CcwSuccessor star dir' d e := by
  rcases hsucc with ⟨hfinite, hd, he, hcase⟩
  refine ⟨hfinite, hd, he, ?_⟩
  rcases hcase with hsingleton | ⟨hde, hmin⟩
  · exact Or.inl hsingleton
  · refine Or.inr ⟨hde, ?_⟩
    intro f hf hfd
    by_cases hfe : f = e
    · subst f
      exact le_rfl
    · have hdf : d ≠ f := fun h => hfd (h.symm)
      have harg_de : Complex.arg (dir d) ≠ Complex.arg (dir e) := by
        intro h
        exact hde (harg d hd e he h).symm
      have harg_df : Complex.arg (dir d) ≠ Complex.arg (dir f) := by
        intro h
        exact hfd (harg d hd f hf h).symm
      have harg_ef : Complex.arg (dir e) ≠ Complex.arg (dir f) := by
        intro h
        exact hfe (harg e he f hf h).symm
      have horder := hThreeGerm K hK hK0
        (dir d) (dir e) (dir f) (dir' d) (dir' e) (dir' f)
        (hdir d hd).1 (hdir e he).1 (hdir f hf).1
        (hdir d hd).2 (hdir e he).2 (hdir f hf).2
        harg_de harg_df harg_ef
        (hsegments d hd) (hsegments e he) (hsegments f hf)
      have hnotSource : ¬ ccwTurn (dir d) (dir f) <
          ccwTurn (dir d) (dir e) := not_lt_of_ge (hmin f hf hfd)
      have hnotTarget : ¬ ccwTurn (dir' d) (dir' f) <
          ccwTurn (dir' d) (dir' e) := fun h => hnotSource (horder.mpr h)
      exact le_of_not_gt hnotTarget




















































end DirectedDistances.PaperProofs.Section5

end
