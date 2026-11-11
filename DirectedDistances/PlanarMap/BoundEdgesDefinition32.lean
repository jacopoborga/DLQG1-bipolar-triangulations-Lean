/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder7Sanity
















public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE}
variable {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: the upper-left edge set read from the
supplied upper-left side, retaining its edge identities and forgetting dart
traversal bits. -/
@[expose] def upperLeftBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) : Set E :=
  {e | ∃ i : B.presentation.upperLeft.Index,
    (B.presentation.upperLeft.darts i).1 = e}

/-- Helper toward Definition 3.2: the upper-right set read from the supplied
consecutive missing-edge run. -/
@[expose] def upperRightBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) : Set E :=
  {e | ∃ i : B.presentation.upperRight.Index,
    (B.presentation.upperRight.darts i).1 = e}

/-- Helper toward Definition 3.2: the lower-right edge set read from the
supplied lower-right side, retaining its edge identities and forgetting dart
traversal bits. -/
@[expose] def lowerRightBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) : Set E :=
  {e | ∃ i : B.presentation.lowerRight.Index,
    (B.presentation.lowerRight.darts i).1 = e}

/-- Helper toward Definition 3.2: the lower-left set read from the supplied
consecutive missing-edge run. -/
@[expose] def lowerLeftBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) : Set E :=
  {e | ∃ i : B.presentation.lowerLeft.Index,
    (B.presentation.lowerLeft.darts i).1 = e}

/-- Helper toward Definition 3.2: the v7 external-face interval-order
predicate on the supplied four-part boundary presentation. -/
@[expose] def IsBoundEdges32
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  IsExternalFaceIntervalOrder7 M B G U S

/-- Helper toward Definition 3.2: upper-left membership is occurrence in the
supplied upper-left side. -/
@[simp]
theorem mem_upperLeftBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) (e : E) :
    e ∈ upperLeftBoundary32 B ↔
      ∃ i : B.presentation.upperLeft.Index,
        (B.presentation.upperLeft.darts i).1 = e := Iff.rfl

/-- Helper toward Definition 3.2: upper-right membership is occurrence in the
supplied upper-right missing-edge run. -/
@[simp]
theorem mem_upperRightBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) (e : E) :
    e ∈ upperRightBoundary32 B ↔
      ∃ i : B.presentation.upperRight.Index,
        (B.presentation.upperRight.darts i).1 = e := Iff.rfl

/-- Helper toward Definition 3.2: lower-right membership is occurrence in the
supplied lower-right side. -/
@[simp]
theorem mem_lowerRightBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) (e : E) :
    e ∈ lowerRightBoundary32 B ↔
      ∃ i : B.presentation.lowerRight.Index,
        (B.presentation.lowerRight.darts i).1 = e := Iff.rfl

/-- Helper toward Definition 3.2: lower-left membership is occurrence in the
supplied lower-left missing-edge run. -/
@[simp]
theorem mem_lowerLeftBoundary32
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) (e : E) :
    e ∈ lowerLeftBoundary32 B ↔
      ∃ i : B.presentation.lowerLeft.Index,
        (B.presentation.lowerLeft.darts i).1 = e := Iff.rfl

variable {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: the v7 predicate supplies all four side
clauses, the external-face dart coverage, and simple present sides, in either
its finite or limiting infinite branch. -/
theorem IsBoundEdges32.presentation_facts
    (h : IsBoundEdges32 M B G U S) :
    (∀ d, G.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex B.presentation,
        InfiniteBoundaryDartIndex.dart B.presentation i = d) ∧
    ULOkInf B.presentation ∧ UROkInf B.presentation ∧
    LROkInf B.presentation ∧ LLOkInf B.presentation ∧
    IsSimpleBoundarySide M B.presentation.upperLeft ∧
    IsSimpleBoundarySide M B.presentation.lowerRight := by
  by_cases hfinite : (externalBoundaryDartSet4 M).Finite
  · have h7 := (IsExternalFaceIntervalOrder7.finite_iff hfinite).mp h
    rcases h7 with ⟨hc, _⟩
    rcases hc with ⟨_, hcover, _, _, hul, hur, hlr, hll,
      hsimpleUL, hsimpleLR, _⟩
    exact ⟨hcover, hul, hur, hlr, hll, hsimpleUL, hsimpleLR⟩
  · have hinfinite : ¬ (externalBoundaryDartSet4 M).Finite := hfinite
    have h7 := (IsExternalFaceIntervalOrder7.infinite_iff hinfinite).mp h
    rcases h7 with ⟨_, h3⟩
    rcases h3 with ⟨h2, _, _⟩
    rcases h2 with ⟨hbase, hul, hur, hlr, hll, hsimpleUL, hsimpleLR, _⟩
    rcases hbase with ⟨_, hcover, _, _, _, _⟩
    exact ⟨hcover, hul, hur, hlr, hll, hsimpleUL, hsimpleLR⟩

/-- Helper toward Definition 3.2: endpoint-label validity for all four sides
is part of either v7 branch. When finite junctions are supplied, the
finite-supplied-junction theorem retains all eight labels. -/
theorem IsBoundEdges32.endpoint_labels
    (h : IsBoundEdges32 M B G U S) :
    BoundarySideEndpointLabels M B.presentation.upperLeft ∧
    BoundarySideEndpointLabels M B.presentation.upperRight ∧
    BoundarySideEndpointLabels M B.presentation.lowerRight ∧
    BoundarySideEndpointLabels M B.presentation.lowerLeft := by
  by_cases hfinite : (externalBoundaryDartSet4 M).Finite
  · have h7 := (IsExternalFaceIntervalOrder7.finite_iff hfinite).mp h
    rcases h7 with ⟨hc, _⟩
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hul, hur, hlr, hll, _⟩
    exact ⟨hul, hur, hlr, hll⟩
  · have hinfinite : ¬ (externalBoundaryDartSet4 M).Finite := hfinite
    have h7 := (IsExternalFaceIntervalOrder7.infinite_iff hinfinite).mp h
    rcases h7 with ⟨_, h3⟩
    rcases h3 with ⟨h2, _, _⟩
    rcases h2 with ⟨_, _, _, _, _, _, _, hul, hur, hlr, hll, _⟩
    exact ⟨hul, hur, hlr, hll⟩

/-- Helper toward Definition 3.2: the finite branch is exactly the v7 finite
predicate, with its supplied junction labels. -/
theorem IsBoundEdges32.finite_iff
    (hfinite : (externalBoundaryDartSet4 M).Finite) :
    IsBoundEdges32 M B G U S ↔ IsFiniteExternalFaceIntervalOrder7 M B G U S :=
  IsExternalFaceIntervalOrder7.finite_iff hfinite

/-- Helper toward Definition 3.2: the infinite branch retains precisely the
v3 limiting presentation and has no finite junction marks. -/
theorem IsBoundEdges32.infinite_iff
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite) :
    IsBoundEdges32 M B G U S ↔
      B.finiteJunctions? = none ∧
        IsExternalFaceIntervalOrder3 M B.presentation G U S :=
  IsExternalFaceIntervalOrder7.infinite_iff hinfinite

/-- Helper toward Definition 3.2: with no listed boundary darts and supplied
finite junctions, the finite branch retains exactly their eight endpoint
labels; empty present sides are zero-edge paths at those supplied vertices. -/
theorem IsBoundEdges32.empty_iff_of_some
    [IsEmpty (InfiniteBoundaryDartIndex B.presentation)]
    (J : FiniteBoundaryJunctions V) (hj : B.finiteJunctions? = some J) :
    IsBoundEdges32 M B G U S ↔
      FiniteExternalFaceIntervalCore7 M B.presentation G U S ∧
        FiniteBoundaryJunctionLabels6 B.presentation J :=
  IsExternalFaceIntervalOrder7.empty_iff_of_some J hj

/-- Helper toward Definition 3.2: on the finite branch, a supplied four-way
junction record is used exactly through its eight endpoint labels. -/
theorem IsBoundEdges32.finite_supplied_junctions_iff
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (J : FiniteBoundaryJunctions V) (hj : B.finiteJunctions? = some J) :
    IsBoundEdges32 M B G U S ↔
      FiniteExternalFaceIntervalCore7 M B.presentation G U S ∧
        FiniteBoundaryJunctionLabels6 B.presentation J := by
  rw [IsBoundEdges32.finite_iff hfinite]
  exact IsFiniteExternalFaceIntervalOrder7.supplied_junctions_iff_of_some J hj

/-- Helper toward Definition 3.2: an upper-left edge is present, is traversed
in its directed orientation, and its oriented dart borders the supplied
external face U. This is the PL dart-border form of the left-side
characterization. -/
theorem mem_upperLeftBoundary32_iff_forward_dartBorders
    (h : IsBoundEdges32 M B G U S) (e : E) :
    e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, M.forward ⟨e, hp⟩) U := by
  have hfacts := IsBoundEdges32.presentation_facts h
  constructor
  · rintro ⟨i, hi⟩
    rcases ((ULOkInf_iff B.presentation).mp hfacts.2.1).1 i with
      ⟨hp, hforward, _⟩
    subst e
    refine ⟨hp, ?_⟩
    have hborder :
        G.dartBorders (B.presentation.upperLeft.darts i) U :=
      (hfacts.1 _).mpr ⟨InfiniteBoundaryDartIndex.upperLeft i, by
        rw [InfiniteBoundaryDartIndex.dart_eq]
      ⟩
    have hd : B.presentation.upperLeft.darts i =
        ((B.presentation.upperLeft.darts i).1,
          M.forward ⟨(B.presentation.upperLeft.darts i).1, hp⟩) :=
      Prod.ext rfl hforward
    rw [← hd]
    exact hborder
  · rintro ⟨hp, hborder⟩
    rcases (hfacts.1 _).mp hborder with ⟨i, hi⟩
    cases i with
    | upperLeft i =>
      have hi' : B.presentation.upperLeft.darts i =
          (e, M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      exact ⟨i, congrArg Prod.fst hi'⟩
    | upperRight i =>
      have hi' : B.presentation.upperRight.darts i =
          (e, M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      have hmissing :=
        ((UROkInf_iff B.presentation).mp hfacts.2.2.1).1 i
      have hedge := congrArg Prod.fst hi'
      have hmissing' : M.toPlaneMapWithMissing.missing e := by
        simpa only [hedge] using hmissing
      exact (hp hmissing').elim
    | lowerRight i =>
      have hi' : B.presentation.lowerRight.darts i =
          (e, M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      rcases ((LROkInf_iff B.presentation).mp hfacts.2.2.2.1).1 i with
        ⟨hp', hreverse, _⟩
      have hedge := congrArg Prod.fst hi'
      have hbit := congrArg Prod.snd hi'
      have hforwardEq :
          M.forward ⟨(B.presentation.lowerRight.darts i).1, hp'⟩ =
            M.forward ⟨e, hp⟩ := by
        apply congrArg M.forward
        apply Subtype.ext
        exact hedge
      have hrev : (B.presentation.lowerRight.darts i).2 =
          !M.forward ⟨e, hp⟩ :=
        hreverse.trans (congrArg (fun b : Bool => !b) hforwardEq)
      have hcontra : M.forward ⟨e, hp⟩ = !M.forward ⟨e, hp⟩ :=
        hbit.symm.trans hrev
      have hfalse : False := by
        cases hfw : M.forward ⟨e, hp⟩ <;> simp [hfw] at hcontra
      exact hfalse.elim
    | lowerLeft i =>
      have hi' : B.presentation.lowerLeft.darts i =
          (e, M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      have hmissing :=
        ((LLOkInf_iff B.presentation).mp hfacts.2.2.2.2.1).1 i
      have hedge := congrArg Prod.fst hi'
      have hmissing' : M.toPlaneMapWithMissing.missing e := by
        simpa only [hedge] using hmissing
      exact (hp hmissing').elim

/-- Helper toward Definition 3.2: a lower-right edge is present, traversed
opposite its directed orientation, and its reverse-oriented dart borders the
supplied external face U. This is the PL dart-border form of the right-side
characterization. -/
theorem mem_lowerRightBoundary32_iff_reverse_dartBorders
    (h : IsBoundEdges32 M B G U S) (e : E) :
    e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) U := by
  have hfacts := IsBoundEdges32.presentation_facts h
  constructor
  · rintro ⟨i, hi⟩
    rcases ((LROkInf_iff B.presentation).mp hfacts.2.2.2.1).1 i with
      ⟨hp, hreverse, _⟩
    subst e
    refine ⟨hp, ?_⟩
    have hborder :
        G.dartBorders (B.presentation.lowerRight.darts i) U :=
      (hfacts.1 _).mpr ⟨InfiniteBoundaryDartIndex.lowerRight i, by
        rw [InfiniteBoundaryDartIndex.dart_eq]
      ⟩
    have hd : B.presentation.lowerRight.darts i =
        ((B.presentation.lowerRight.darts i).1,
          !(M.forward ⟨(B.presentation.lowerRight.darts i).1, hp⟩)) :=
      Prod.ext rfl hreverse
    rw [← hd]
    exact hborder
  · rintro ⟨hp, hborder⟩
    rcases (hfacts.1 _).mp hborder with ⟨i, hi⟩
    cases i with
    | upperLeft i =>
      have hi' : B.presentation.upperLeft.darts i =
          (e, !M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      rcases ((ULOkInf_iff B.presentation).mp hfacts.2.1).1 i with
        ⟨hp', hforward, _⟩
      have hedge := congrArg Prod.fst hi'
      have hbit := congrArg Prod.snd hi'
      have hforwardEq :
          M.forward ⟨(B.presentation.upperLeft.darts i).1, hp'⟩ =
            M.forward ⟨e, hp⟩ := by
        apply congrArg M.forward
        apply Subtype.ext
        exact hedge
      have hfw : (B.presentation.upperLeft.darts i).2 =
          M.forward ⟨e, hp⟩ := hforward.trans hforwardEq
      have hcontra : M.forward ⟨e, hp⟩ = !M.forward ⟨e, hp⟩ :=
        hfw.symm.trans hbit
      have hfalse : False := by
        cases hfw' : M.forward ⟨e, hp⟩ <;> simp [hfw'] at hcontra
      exact hfalse.elim
    | upperRight i =>
      have hi' : B.presentation.upperRight.darts i =
          (e, !M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      have hmissing :=
        ((UROkInf_iff B.presentation).mp hfacts.2.2.1).1 i
      have hedge := congrArg Prod.fst hi'
      have hmissing' : M.toPlaneMapWithMissing.missing e := by
        simpa only [hedge] using hmissing
      exact (hp hmissing').elim
    | lowerRight i =>
      have hi' : B.presentation.lowerRight.darts i =
          (e, !M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      exact ⟨i, congrArg Prod.fst hi'⟩
    | lowerLeft i =>
      have hi' : B.presentation.lowerLeft.darts i =
          (e, !M.forward ⟨e, hp⟩) := by
        simpa only [InfiniteBoundaryDartIndex.dart_eq] using hi
      have hmissing :=
        ((LLOkInf_iff B.presentation).mp hfacts.2.2.2.2.1).1 i
      have hedge := congrArg Prod.fst hi'
      have hmissing' : M.toPlaneMapWithMissing.missing e := by
        simpa only [hedge] using hmissing
      exact (hp hmissing').elim

/-- Helper toward Definition 3.2: every upper-right run edge is missing and
has no orientation in the directed map. The run itself is exactly the supplied
upper-right side between its retained endpoint labels. -/
theorem upperRightBoundary32_missing
    (h : IsBoundEdges32 M B G U S) {e : E}
    (he : e ∈ upperRightBoundary32 B) :
    M.toPlaneMapWithMissing.missing e := by
  rcases he with ⟨i, hi⟩
  have hmissing :=
    ((UROkInf_iff B.presentation).mp
      (IsBoundEdges32.presentation_facts h).2.2.1).1 i
  simpa only [hi] using hmissing

/-- Helper toward Definition 3.2: every lower-left run edge is missing and
has no orientation in the directed map. The run itself is exactly the supplied
lower-left side between its retained endpoint labels. -/
theorem lowerLeftBoundary32_missing
    (h : IsBoundEdges32 M B G U S) {e : E}
    (he : e ∈ lowerLeftBoundary32 B) :
    M.toPlaneMapWithMissing.missing e := by
  rcases he with ⟨i, hi⟩
  have hmissing :=
    ((LLOkInf_iff B.presentation).mp
      (IsBoundEdges32.presentation_facts h).2.2.2.2.1).1 i
  simpa only [hi] using hmissing

/-- Helper toward Definition 3.2: upper-right membership means an occurrence
in the supplied consecutive upper-right run, and under v7 that occurrence is
a missing edge. -/
theorem mem_upperRightBoundary32_iff_missing_run
    (h : IsBoundEdges32 M B G U S) (e : E) :
    e ∈ upperRightBoundary32 B ↔
      ∃ i : B.presentation.upperRight.Index,
        (B.presentation.upperRight.darts i).1 = e ∧
          M.toPlaneMapWithMissing.missing e := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi, upperRightBoundary32_missing h ⟨i, hi⟩⟩
  · rintro ⟨i, hi, _⟩
    exact ⟨i, hi⟩

/-- Helper toward Definition 3.2: lower-left membership means an occurrence
in the supplied consecutive lower-left run, and under v7 that occurrence is
a missing edge. -/
theorem mem_lowerLeftBoundary32_iff_missing_run
    (h : IsBoundEdges32 M B G U S) (e : E) :
    e ∈ lowerLeftBoundary32 B ↔
      ∃ i : B.presentation.lowerLeft.Index,
        (B.presentation.lowerLeft.darts i).1 = e ∧
          M.toPlaneMapWithMissing.missing e := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi, lowerLeftBoundary32_missing h ⟨i, hi⟩⟩
  · rintro ⟨i, hi, _⟩
    exact ⟨i, hi⟩















































end DirectedDistances.PlanarMap

end
