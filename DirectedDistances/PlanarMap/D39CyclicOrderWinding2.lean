module

public import DirectedDistances.PlanarMap.D39CyclicOrderWinding








public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. The counterclockwise circular arc of
radius `r`, with its argument lifted from `a` to `b`. -/
def d39CcwCircleArc (r a b : ℝ) :
    Path ((r : ℂ) * Complex.exp (a * Complex.I))
      ((r : ℂ) * Complex.exp (b * Complex.I)) where
  toFun t := (r : ℂ) * Complex.exp
    (((1 - (t : ℝ)) * a + (t : ℝ) * b) * Complex.I)
  source' := by simp
  target' := by simp
  continuous_toFun := by continuity

/-- Helper toward Proposition 5.16. The loop that follows the first radial
segment out, travels counterclockwise along the circle, and returns radially
to the center. -/
def d39SectorLoop (r a b : ℝ) : Path (0 : ℂ) 0 :=
  (Path.segment (0 : ℂ) ((r : ℂ) * Complex.exp (a * Complex.I))).trans
    ((d39CcwCircleArc r a b).trans
      (Path.segment ((r : ℂ) * Complex.exp (b * Complex.I)) 0))

/-- Helper toward Proposition 5.16. The open sector swept out between lifted
arguments `a` and `b` at radii strictly between zero and `r`. -/
def d39OpenSector (r a b : ℝ) : Set ℂ :=
  {w | ∃ ρ θ : ℝ, 0 < ρ ∧ ρ < r ∧ a < θ ∧ θ < b ∧
    w = (ρ : ℂ) * Complex.exp (θ * Complex.I)}

/-- Helper toward Proposition 5.16. For a fixed initial dart, the successor
minimum is equivalent to saying that no other dart has a strictly smaller
counterclockwise turn than the proposed successor. This is the order-theoretic
form of the sector test; connecting sector winding values to strict turns is
separate. -/
theorem ccwSuccessor_iff_no_intermediate_turn
    {D : Type*} {star : Set D} {dir : D → ℂ} {d e : D} :
    CcwSuccessor star dir d e ↔
      star.Finite ∧ d ∈ star ∧ e ∈ star ∧
        ((e = d ∧ star = {d}) ∨
          (e ≠ d ∧ ∀ f ∈ star, f ≠ d →
            ¬ (ccwTurn (dir d) (dir f) < ccwTurn (dir d) (dir e)))) := by
  change
    (star.Finite ∧ d ∈ star ∧ e ∈ star ∧
      ((e = d ∧ star = {d}) ∨
        (e ≠ d ∧ ∀ f ∈ star, f ≠ d →
          ccwTurn (dir d) (dir e) ≤ ccwTurn (dir d) (dir f)))) ↔ _
  constructor
  · rintro ⟨hfin, hd, he, hs | ⟨hne, hmin⟩⟩
    · exact ⟨hfin, hd, he, Or.inl hs⟩
    · refine ⟨hfin, hd, he, Or.inr ⟨hne, ?_⟩⟩
      intro f hf hfd hlt
      exact (not_lt_of_ge (hmin f hf hfd)) hlt
  · rintro ⟨hfin, hd, he, hs | ⟨hne, hno⟩⟩
    · exact ⟨hfin, hd, he, Or.inl hs⟩
    · refine ⟨hfin, hd, he, Or.inr ⟨hne, ?_⟩⟩
      intro f hf hfd
      exact le_of_not_gt (hno f hf hfd)








































































end DirectedDistances.PlanarMap

end
