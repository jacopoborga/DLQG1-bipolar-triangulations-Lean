/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder6

/- The source's four consecutive boundary runs may be empty; UL and LR are simple
directed paths of non-missing edges, while UR and LL are the consecutive
missing-edge runs between the specified terminal and initial vertices.
The v7 finite core retains the v6 clauses except for closing-junction labels.
Those labels are required at junctions determined by the endpoints of a
nonempty upper-left or lower-right path. If both present paths are nonempty,
the v6 closing-junction clause is retained. Supplied finite junction data
still require exactly their eight labels, while bare missing-only cycles need
no selected junction labels. The infinite branch is exactly v3 and retains
its limiting data without additional finite marks.

construction of the supplied presentations remain separate obligations. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: when UL is nonempty, its initial and terminal
vertices determine the lower-left/upper-left and upper-left/upper-right
junction labels. -/
@[expose] def UpperLeftPathJunctionLabels7
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) : Prop :=
  (Nonempty P.upperLeft.Index →
    ∃ i, (∀ j, P.upperLeft.next j ≠ some i) ∧
      P.upperLeft.initialVertex? =
        some (boundaryDartInitial M (P.upperLeft.darts i)) ∧
      P.lowerLeft.terminalVertex? =
        some (boundaryDartInitial M (P.upperLeft.darts i))) ∧
  (Nonempty P.upperLeft.Index →
    ∃ i, P.upperLeft.next i = none ∧
      P.upperLeft.terminalVertex? =
        some (boundaryDartTerminal M (P.upperLeft.darts i)) ∧
      P.upperRight.initialVertex? =
        some (boundaryDartTerminal M (P.upperLeft.darts i)))

/-- Helper toward Definition 3.2: when LR is nonempty, its initial and terminal
vertices determine the upper-right/lower-right and lower-right/lower-left
junction labels. -/
@[expose] def LowerRightPathJunctionLabels7
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) : Prop :=
  (Nonempty P.lowerRight.Index →
    ∃ i, (∀ j, P.lowerRight.next j ≠ some i) ∧
      P.lowerRight.initialVertex? =
        some (boundaryDartInitial M (P.lowerRight.darts i)) ∧
      P.upperRight.terminalVertex? =
        some (boundaryDartInitial M (P.lowerRight.darts i))) ∧
  (Nonempty P.lowerRight.Index →
    ∃ i, P.lowerRight.next i = none ∧
      P.lowerRight.terminalVertex? =
        some (boundaryDartTerminal M (P.lowerRight.darts i)) ∧
      P.lowerLeft.initialVertex? =
        some (boundaryDartTerminal M (P.lowerRight.darts i)))

/-- Helper toward Definition 3.2: endpoint labels at each junction identified
by a nonempty present path, with no labels demanded at junctions lying only on
bare missing runs. -/
@[expose] def PresentPathJunctionLabels7
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M) : Prop :=
  UpperLeftPathJunctionLabels7 P ∧ LowerRightPathJunctionLabels7 P

/-- Helper toward Definition 3.2: use v6's closing-junction labels when both
present paths are nonempty; otherwise require only the junction labels fixed
by whichever present path is nonempty. -/
@[expose] def RequiredFiniteBoundaryJoinEndpointLabels7
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (S : E × Bool → E × Bool) : Prop :=
  (Nonempty P.upperLeft.Index ∧ Nonempty P.lowerRight.Index →
    RequiredFiniteBoundaryJoinEndpointLabels4 P S) ∧
  (¬ (Nonempty P.upperLeft.Index ∧ Nonempty P.lowerRight.Index) →
    PresentPathJunctionLabels7 P)

/-- Helper toward Definition 3.2: v6's finite core, changing only its
closing-junction labels to the v7 requirement. -/
@[expose] def FiniteExternalFaceIntervalCore7
    (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  IsBoundaryOrderOfInf M P ∧
  (∀ d, G.dartBorders d U ↔
    ∃ i : InfiniteBoundaryDartIndex P, InfiniteBoundaryDartIndex.dart P i = d) ∧
  Function.Injective (InfiniteBoundaryDartIndex.dart P) ∧
  IsGeometricExternalFaceSucc G U S ∧
  ULOkInf P ∧ UROkInf P ∧ LROkInf P ∧ LLOkInf P ∧
  IsSimpleBoundarySide M P.upperLeft ∧ IsSimpleBoundarySide M P.lowerRight ∧
  BoundarySideEndpointLabels M P.upperLeft ∧
  BoundarySideEndpointLabels M P.upperRight ∧
  BoundarySideEndpointLabels M P.lowerRight ∧
  BoundarySideEndpointLabels M P.lowerLeft ∧
  FiniteBoundaryPositionOrder4 P S ∧
  (∀ i j : InfiniteBoundaryDartIndex P,
    S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
    boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
      boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j)) ∧
  (Nonempty (InfiniteBoundaryDartIndex P) →
    RequiredFiniteBoundaryJoinEndpointLabels7 P S)

/-- Helper toward Definition 3.2: finite v7 consists of the v7 finite core and
exact agreement with any supplied finite junction data. -/
@[expose] def IsFiniteExternalFaceIntervalOrder7
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  FiniteExternalFaceIntervalCore7 M B.presentation G U S ∧
    SuppliedFiniteJunctionLabels6 B

/-- Helper toward Definition 3.2: v7's finite core with supplied junctions,
or exactly v3's infinite boundary data without additional finite marks. -/
@[expose] def IsExternalFaceIntervalOrder7
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  ((externalBoundaryDartSet4 M).Finite ∧
    IsFiniteExternalFaceIntervalOrder7 M B G U S) ∨
  (¬ (externalBoundaryDartSet4 M).Finite ∧ B.finiteJunctions? = none ∧
    IsExternalFaceIntervalOrder3 M B.presentation G U S)

variable {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: when both present paths are nonempty, the v7
finite core is equivalent to the v6 core, including every original clause. -/
theorem FiniteExternalFaceIntervalCore7.iff_core6_of_present_paths
    (hul : Nonempty P.upperLeft.Index) (hlr : Nonempty P.lowerRight.Index) :
    FiniteExternalFaceIntervalCore7 M P G U S ↔
      FiniteExternalFaceIntervalCore6 M P G U S := by
  unfold FiniteExternalFaceIntervalCore7 FiniteExternalFaceIntervalCore6
  constructor
  · rintro ⟨hmap, hcover, hinj, hgeom, hulok, hurok, hlrok, hllok,
      hsimpleUL, hsimpleLR, hulLabels, hurLabels, hlrLabels, hllLabels,
      hpositions, hjoins, hclose⟩
    refine ⟨hmap, hcover, hinj, hgeom, hulok, hurok, hlrok, hllok,
      hsimpleUL, hsimpleLR, hulLabels, hurLabels, hlrLabels, hllLabels,
      hpositions, hjoins, ?_⟩
    intro hne
    exact (hclose hne).1 ⟨hul, hlr⟩
  · rintro ⟨hmap, hcover, hinj, hgeom, hulok, hurok, hlrok, hllok,
      hsimpleUL, hsimpleLR, hulLabels, hurLabels, hlrLabels, hllLabels,
      hpositions, hjoins, hclose⟩
    refine ⟨hmap, hcover, hinj, hgeom, hulok, hurok, hlrok, hllok,
      hsimpleUL, hsimpleLR, hulLabels, hurLabels, hlrLabels, hllLabels,
      hpositions, hjoins, ?_⟩
    intro hne
    constructor
    · intro _
      exact hclose hne
    · intro hnot
      exact (hnot ⟨hul, hlr⟩).elim

/-- Helper toward Definition 3.2: for a finite external boundary, v7 is
exactly its finite predicate. -/
theorem IsExternalFaceIntervalOrder7.finite_iff
    (hfinite : (externalBoundaryDartSet4 M).Finite) :
    IsExternalFaceIntervalOrder7 M B G U S ↔
      IsFiniteExternalFaceIntervalOrder7 M B G U S := by
  constructor
  · rintro (⟨_, h7⟩ | ⟨hi, _, _⟩)
    · exact h7
    · exact (hi hfinite).elim
  · intro h7
    exact Or.inl ⟨hfinite, h7⟩

/-- Helper toward Definition 3.2: the infinite branch of v7 is exactly v3. -/
theorem IsExternalFaceIntervalOrder7.infinite_iff
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite) :
    IsExternalFaceIntervalOrder7 M B G U S ↔
      B.finiteJunctions? = none ∧
        IsExternalFaceIntervalOrder3 M B.presentation G U S := by
  constructor
  · rintro (⟨hf, _⟩ | ⟨_, hn, h3⟩)
    · exact (hinfinite hf).elim
    · exact ⟨hn, h3⟩
  · rintro ⟨hn, h3⟩
    exact Or.inr ⟨hinfinite, hn, h3⟩

/-- Helper toward Definition 3.2: the finite v7 predicate is its core paired
with exactly the supplied-junction label clause from v6. -/
theorem IsExternalFaceIntervalOrder7.empty_iff_of_some
    [IsEmpty (InfiniteBoundaryDartIndex B.presentation)]
    (J : FiniteBoundaryJunctions V) (hj : B.finiteJunctions? = some J) :
    IsExternalFaceIntervalOrder7 M B G U S ↔
      FiniteExternalFaceIntervalCore7 M B.presentation G U S ∧
        FiniteBoundaryJunctionLabels6 B.presentation J := by
  constructor
  · rintro (⟨_, ⟨hc, hl⟩⟩ | ⟨_, hn, _⟩)
    · exact ⟨hc, (suppliedFiniteJunctionLabels6_iff_of_some J hj).mp hl⟩
    · rw [hj] at hn
      cases hn
  · rintro ⟨hc, hl⟩
    have hf : (externalBoundaryDartSet4 M).Finite := by
      apply (externalBoundaryDartSet4_finite_iff M).mpr
      apply Set.finite_empty.subset
      intro e he
      rcases (((IsBoundaryOrderOfInf_iff B.presentation).mp hc.1).1 e).mpr he
        with ⟨i, _⟩
      exact isEmptyElim i
    exact Or.inl ⟨hf, ⟨hc,
      (suppliedFiniteJunctionLabels6_iff_of_some J hj).mpr hl⟩⟩

/-- Helper toward Definition 3.2: on a finite boundary with nonempty UL and LR
paths, v7 is equivalent to v6 and hence to v5. -/
theorem IsExternalFaceIntervalOrder7.iff6_of_present_paths
    (hul : Nonempty B.presentation.upperLeft.Index)
    (hlr : Nonempty B.presentation.lowerRight.Index) :
    IsExternalFaceIntervalOrder7 M B G U S ↔
      IsExternalFaceIntervalOrder6 M B G U S := by
  by_cases hfinite : (externalBoundaryDartSet4 M).Finite
  · rw [IsExternalFaceIntervalOrder7.finite_iff hfinite,
      IsExternalFaceIntervalOrder6.finite_iff hfinite]
    constructor
    · rintro ⟨hcore, hlabels⟩
      exact ⟨(FiniteExternalFaceIntervalCore7.iff_core6_of_present_paths hul hlr).mp
        hcore, hlabels⟩
    · rintro ⟨hcore, hlabels⟩
      exact ⟨(FiniteExternalFaceIntervalCore7.iff_core6_of_present_paths hul hlr).mpr
        hcore, hlabels⟩
  · have hinfinite : ¬ (externalBoundaryDartSet4 M).Finite := hfinite
    rw [IsExternalFaceIntervalOrder7.infinite_iff hinfinite,
      IsExternalFaceIntervalOrder6.infinite_iff hinfinite]

/-- Helper toward Definition 3.2: with both present paths nonempty, v7 is also
equivalent to v5 by the established v6/v5 characterization. -/
theorem IsExternalFaceIntervalOrder7.iff5_of_present_paths
    (hul : Nonempty B.presentation.upperLeft.Index)
    (hlr : Nonempty B.presentation.lowerRight.Index) :
    IsExternalFaceIntervalOrder7 M B G U S ↔
      IsExternalFaceIntervalOrder5 M B G U S := by
  exact (IsExternalFaceIntervalOrder7.iff6_of_present_paths hul hlr).trans
    (IsExternalFaceIntervalOrder6.iff5_of_nonempty
      ⟨InfiniteBoundaryDartIndex.upperLeft hul.some⟩)

/-- Helper toward Definition 3.2: supplied junction data in a finite v7
predicate require exactly the eight labels equal to those supplied vertices. -/
theorem IsFiniteExternalFaceIntervalOrder7.supplied_junctions_iff_of_some
    (J : FiniteBoundaryJunctions V) (hj : B.finiteJunctions? = some J) :
    IsFiniteExternalFaceIntervalOrder7 M B G U S ↔
      FiniteExternalFaceIntervalCore7 M B.presentation G U S ∧
        FiniteBoundaryJunctionLabels6 B.presentation J := by
  unfold IsFiniteExternalFaceIntervalOrder7
  rw [suppliedFiniteJunctionLabels6_iff_of_some J hj]





































/-- Helper toward Definition 3.2: a sole nonempty UL path still carries labels
at both of its determined junctions (the UL endpoints). -/
theorem FiniteExternalFaceIntervalCore7.sole_ul_endpoint_labels
    (h : FiniteExternalFaceIntervalCore7 M P G U S)
    (hsole : ∀ i, sideTag P i = (0 : Fin 4))
    (hul : Nonempty P.upperLeft.Index) :
    UpperLeftPathJunctionLabels7 P := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hclose⟩
  have htotal : Nonempty (InfiniteBoundaryDartIndex P) :=
    ⟨InfiniteBoundaryDartIndex.upperLeft hul.some⟩
  have hnot : ¬ (Nonempty P.upperLeft.Index ∧ Nonempty P.lowerRight.Index) := by
    rintro ⟨_, ⟨i⟩⟩
    have hbad := hsole (InfiniteBoundaryDartIndex.lowerRight i)
    simp [sideTag] at hbad
  exact (hclose htotal).2 hnot |>.1

/-- Helper toward Definition 3.2: the established cyclic interval and wrap
clauses for a sole UL block remain unchanged in v7. -/
theorem sole_ul_finite_cyclic_clauses7 (n : ℕ) :
    IsCyclicSideWordAt4 (fun _ : Fin (n + 1) => (0 : Fin 4))
      ⟨0, Nat.zero_lt_succ n⟩ ∧
    (∀ i j : Fin (n + 1), boundaryLinearNext4 i = some j ↔
      (0 : Fin 4) = 0 ∧
        boundaryCycleOffset4 ⟨0, Nat.zero_lt_succ n⟩ j =
          boundaryCycleOffset4 ⟨0, Nat.zero_lt_succ n⟩ i + 1) ∧
    boundaryCycleSucc4 (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) =
      (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) :=
  sole_ul_finite_cyclic_clauses6 n

/-- Helper toward Definition 3.2: once a cyclic cut orders four blocks, a
side cannot recur after a different side; v7 retains v6's rejection. -/
theorem IsCyclicSideWordAt7.no_side_recurrence
    {n : ℕ} {tag : Fin n → Fin 4} {cut : Fin n}
    (h : IsCyclicSideWordAt4 tag cut) {i j k : Fin n}
    (hij : boundaryCycleOffset4 cut i ≤ boundaryCycleOffset4 cut j)
    (hjk : boundaryCycleOffset4 cut j ≤ boundaryCycleOffset4 cut k)
    (hends : tag i = tag k) (hmiddle : tag i ≠ tag j) : False :=
  IsCyclicSideWordAt6.no_side_recurrence h hij hjk hends hmiddle

/-- Helper toward Definition 3.2: cyclic rotation cannot hide the concrete
UL–UR–UL–UR recurrence; v7 retains v6's rejection. -/
theorem not_isCyclicSideWord7_alternating :
    ¬ IsCyclicSideWord4 (fun i : Fin 4 =>
      if i.val % 2 = 0 then (0 : Fin 4) else 1) :=
  not_isCyclicSideWord6_alternating
