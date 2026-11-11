/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals4
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals3







public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: any type that injects into a finite ordinal
is finite. -/
private theorem finite_of_injective_fin
    {α : Type*} {n : ℕ} (f : α → Fin n) (hf : Function.Injective f) :
    Finite α :=
  Finite.of_injective f hf

/-- Helper toward Definition 3.2: a successor that raises a bounded natural
rank by one reaches a terminal index after finitely many iterations. -/
private theorem bounded_rank_reaches_terminal
    {I : Type*} (next : I → Option I) (rank : I → ℕ) (bound : ℕ)
    (hstep : ∀ {i j}, next i = some j → rank j = rank i + 1)
    (hbound : ∀ i, rank i ≤ bound) (start : I) :
    ∃ n : ℕ,
      next (((fun i => (next i).getD start)^[n]) start) = none := by
  let step : I → I := fun i => (next i).getD start
  have hmain : ∀ d : ℕ, ∀ i : I, bound - rank i = d →
      ∃ n : ℕ, next (step^[n] i) = none := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hgap
        cases hi : next i with
        | none => exact ⟨0, by simpa [step, hi]⟩
        | some j =>
            have hrank := hstep hi
            have hdecr : bound - rank j < d := by
              have hb := hbound j
              rw [hrank] at hb
              omega
            obtain ⟨n, hn⟩ := ih (bound - rank j) hdecr j rfl
            refine ⟨n + 1, ?_⟩
            rw [Function.iterate_succ_apply]
            simpa [step, hi] using hn
  exact hmain (bound - rank start) start rfl

/-- Helper toward Definition 3.2: in the finite v7 branch, the full boundary
dart-index type is finite because its position map is an equivalence with a
finite ordinal. -/
theorem IsBoundEdges32.finite_dartIndex
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S) :
    Finite (InfiniteBoundaryDartIndex B.presentation) := by
  rcases (IsBoundEdges32.finite_iff hfinite).mp h with ⟨hcore, _⟩
  rcases hcore with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpositions, _, _⟩
  rcases hpositions with ⟨n, position, _, _⟩
  exact finite_of_injective_fin position position.injective

/-- Helper toward Definition 3.2: the upper-left side index is finite in the
finite v7 branch, as a subtype image of its full dart-index type. -/
theorem IsBoundEdges32.finite_upperLeft_index
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S) : Finite B.presentation.upperLeft.Index := by
  letI := IsBoundEdges32.finite_dartIndex hfinite h
  exact Finite.of_injective InfiniteBoundaryDartIndex.upperLeft (by
    intro i j hij
    exact (InfiniteBoundaryDartIndex.upperLeft.inj hij))

/-- Helper toward Definition 3.2: the upper-right side index is finite in the
finite v7 branch, as a subtype image of its full dart-index type. -/
theorem IsBoundEdges32.finite_upperRight_index
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S) : Finite B.presentation.upperRight.Index := by
  letI := IsBoundEdges32.finite_dartIndex hfinite h
  exact Finite.of_injective InfiniteBoundaryDartIndex.upperRight (by
    intro i j hij
    exact (InfiniteBoundaryDartIndex.upperRight.inj hij))

/-- Helper toward Definition 3.2: the lower-right side index is finite in the
finite v7 branch, as a subtype image of its full dart-index type. -/
theorem IsBoundEdges32.finite_lowerRight_index
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S) : Finite B.presentation.lowerRight.Index := by
  letI := IsBoundEdges32.finite_dartIndex hfinite h
  exact Finite.of_injective InfiniteBoundaryDartIndex.lowerRight (by
    intro i j hij
    exact (InfiniteBoundaryDartIndex.lowerRight.inj hij))

/-- Helper toward Definition 3.2: the lower-left side index is finite in the
finite v7 branch, as a subtype image of its full dart-index type. -/
theorem IsBoundEdges32.finite_lowerLeft_index
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S) : Finite B.presentation.lowerLeft.Index := by
  letI := IsBoundEdges32.finite_dartIndex hfinite h
  exact Finite.of_injective InfiniteBoundaryDartIndex.lowerLeft (by
    intro i j hij
    exact (InfiniteBoundaryDartIndex.lowerLeft.inj hij))

/-- Helper toward Definition 3.2: in the finite v7 branch, iterating
`sideNext` from any listed dart reaches a terminal index. The rank is the
position offset from the supplied finite cyclic cut. -/
theorem IsBoundEdges32.finite_sideNext_reaches_terminal
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (h : IsBoundEdges32 M B G U S)
    (i : InfiniteBoundaryDartIndex B.presentation) :
    ∃ n : ℕ,
      sideNext B.presentation
        (((fun j => (sideNext B.presentation j).getD i)^[n]) i) = none := by
  rcases (IsBoundEdges32.finite_iff hfinite).mp h with ⟨hcore, _⟩
  rcases hcore with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpositions, _, _⟩
  rcases hpositions with ⟨n, position, _, hword⟩
  rcases hword with hn | ⟨cut, _, hnextSide⟩
  · subst n
    exact Fin.elim0 (position i)
  · have hnpos : 0 < n := by
      by_contra hnot
      have hn0 : n = 0 := by omega
      subst n
      exact Fin.elim0 (position i)
    let rank : InfiniteBoundaryDartIndex B.presentation → ℕ := fun j =>
      boundaryCycleOffset4 cut (position j)
    have hstep : ∀ {a b}, sideNext B.presentation a = some b →
        rank b = rank a + 1 := by
      intro a b hab
      have hoffset := (hnextSide a b).mp hab
      exact hoffset.2
    have hbound : ∀ j, rank j ≤ n - 1 := by
      intro j
      have hlt : rank j < n := by
        dsimp [rank, boundaryCycleOffset4]
        exact Nat.mod_lt _ hnpos
      omega
    exact bounded_rank_reaches_terminal (sideNext B.presentation)
      rank (n - 1) hstep hbound i




























































end DirectedDistances.PlanarMap

end
