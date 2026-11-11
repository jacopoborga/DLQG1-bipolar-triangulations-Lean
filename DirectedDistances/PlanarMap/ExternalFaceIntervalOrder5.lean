/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder4































public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

variable {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: supplied junctions in external-face traversal
order UL–UR–LR–LL. LR traversal reverses its directed path orientation. The
vertices need not be distinct; validity is required separately. -/
structure FiniteBoundaryJunctions (V : Type uV) where
  lowerLeftUpperLeft : V
  upperLeftUpperRight : V
  upperRightLowerRight : V
  lowerRightLowerLeft : V

/-- Helper toward Definition 3.2: the supplied boundary presentation paired
with optional retained finite junction data. Infinite or boundaryless limiting
constructions supply `none`; the structure asserts no existence theorem. -/
structure BoundaryPresentationWithJunctions (M : DirectedPlaneMapWithMissing V E) where
  presentation : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M
  finiteJunctions? : Option (FiniteBoundaryJunctions V)

/-- Helper toward Definition 3.2: all eight labels equal the supplied four
junctions. Empty-side endpoint validity identifies its two junction vertices,
giving precisely the corresponding zero-edge path. -/
@[expose] def FiniteBoundaryJunctionLabels5
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    (J : FiniteBoundaryJunctions V) : Prop :=
  P.upperLeft.initialVertex? = some J.lowerLeftUpperLeft ∧
  P.upperLeft.terminalVertex? = some J.upperLeftUpperRight ∧
  P.upperRight.initialVertex? = some J.upperLeftUpperRight ∧
  P.upperRight.terminalVertex? = some J.upperRightLowerRight ∧
  P.lowerRight.initialVertex? = some J.upperRightLowerRight ∧
  P.lowerRight.terminalVertex? = some J.lowerRightLowerLeft ∧
  P.lowerLeft.initialVertex? = some J.lowerRightLowerLeft ∧
  P.lowerLeft.terminalVertex? = some J.lowerLeftUpperLeft

/-- Helper toward Definition 3.2: supplied finite junctions require their
exact labels; absent data impose no additional label requirement. -/
@[expose] def SuppliedFiniteJunctionLabels5
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M) : Prop :=
  match B.finiteJunctions? with
  | none => True
  | some J => FiniteBoundaryJunctionLabels5 B.presentation J

/-- Helper toward Definition 3.2: v4's finite geometric, interval, endpoint
and closing-junction clauses, omitting only its empty-boundary frontier-vertex
test. No side, simplicity, coverage or cyclic-order clause is discarded. -/
@[expose] def FiniteExternalFaceIntervalCore5
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
  RequiredFiniteBoundaryJoinEndpointLabels4 P S



@[expose] def IsFiniteExternalFaceIntervalOrder5
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  FiniteExternalFaceIntervalCore5 M B.presentation G U S ∧
    SuppliedFiniteJunctionLabels5 B

/-- Helper toward Definition 3.2: v4's finite core with supplied junctions,
or precisely v3's infinite boundary data without additional finite marks.
Finiteness is still determined by the map, not by a free boundary flag. -/
@[expose] def IsExternalFaceIntervalOrder5
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  ((externalBoundaryDartSet4 M).Finite ∧
    IsFiniteExternalFaceIntervalOrder5 M B G U S) ∨
  (¬ (externalBoundaryDartSet4 M).Finite ∧ B.finiteJunctions? = none ∧
    IsExternalFaceIntervalOrder3 M B.presentation G U S)

variable {P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}

/-- Helper toward Definition 3.2: the finite core is exactly v4 minus its
empty-boundary label clause. -/
theorem isFiniteExternalFaceIntervalOrder4_iff_core5 :
    IsFiniteExternalFaceIntervalOrder4 M P G U S ↔
      FiniteExternalFaceIntervalCore5 M P G U S ∧
        RequiredEmptyFiniteBoundaryLabels4 P G U := by
  unfold IsFiniteExternalFaceIntervalOrder4 FiniteExternalFaceIntervalCore5
  tauto

/-- Helper toward Definition 3.2: on a nonempty boundary the removed v4
empty-label clause is vacuous. -/
theorem FiniteExternalFaceIntervalCore5.toIsFiniteExternalFaceIntervalOrder4
    (h : FiniteExternalFaceIntervalCore5 M P G U S)
    (hne : Nonempty (InfiniteBoundaryDartIndex P)) :
    IsFiniteExternalFaceIntervalOrder4 M P G U S := by
  apply isFiniteExternalFaceIntervalOrder4_iff_core5.mpr
  refine ⟨h, ?_⟩
  intro hempty _
  exact (hempty.false hne.some).elim

/-- Helper toward Definition 3.2: every nonempty v5 boundary projects to
v4 on the underlying presentation. -/
theorem IsExternalFaceIntervalOrder5.toIsExternalFaceIntervalOrder4
    (h : IsExternalFaceIntervalOrder5 M B G U S)
    (hne : Nonempty (InfiniteBoundaryDartIndex B.presentation)) :
    IsExternalFaceIntervalOrder4 M B.presentation G U S := by
  rcases h with ⟨hfinite, hcore, _⟩ | ⟨hinfinite, _, h3⟩
  · exact Or.inl ⟨hfinite, hcore.toIsFiniteExternalFaceIntervalOrder4 hne⟩
  · exact Or.inr ⟨hinfinite, h3⟩

/-- Helper toward Definition 3.2: absent supplied junctions place no new
label condition on a bare presentation, including an all-missing cycle.
This is not an existence or full cycle-acceptance theorem. -/
theorem suppliedFiniteJunctionLabels5_of_none (h : B.finiteJunctions? = none) :
    SuppliedFiniteJunctionLabels5 B := by
  unfold SuppliedFiniteJunctionLabels5
  rw [h]
  trivial

/-- Helper toward Definition 3.2: supplied junction data require equality
to those exact junctions, rather than existentially chosen vertices. -/
theorem suppliedFiniteJunctionLabels5_iff_of_some
    (J : FiniteBoundaryJunctions V) (h : B.finiteJunctions? = some J) :
    SuppliedFiniteJunctionLabels5 B ↔
      FiniteBoundaryJunctionLabels5 B.presentation J := by
  unfold SuppliedFiniteJunctionLabels5
  rw [h]

/-- Helper toward Definition 3.2: for an infinite boundary, including every
nonempty one-ended instance, v5 is precisely v3 with absent finite marks.
No new restriction is imposed on the underlying limiting endpoint data. -/
theorem IsExternalFaceIntervalOrder5.infinite_iff
    (hinfinite : ¬ (externalBoundaryDartSet4 M).Finite) :
    IsExternalFaceIntervalOrder5 M B G U S ↔
      B.finiteJunctions? = none ∧
        IsExternalFaceIntervalOrder3 M B.presentation G U S := by
  constructor
  · rintro (⟨hf, _⟩ | ⟨_, hn, h3⟩)
    · exact (hinfinite hf).elim
    · exact ⟨hn, h3⟩
  · rintro ⟨hn, h3⟩
    exact Or.inr ⟨hinfinite, hn, h3⟩

/-- Helper toward Definition 3.2: on a finite boundary, v5 is exactly its
finite core together with the supplied-junction clause. -/
theorem IsExternalFaceIntervalOrder5.finite_iff
    (hfinite : (externalBoundaryDartSet4 M).Finite) :
    IsExternalFaceIntervalOrder5 M B G U S ↔
      IsFiniteExternalFaceIntervalOrder5 M B G U S := by
  constructor
  · rintro (⟨_, h5⟩ | ⟨hi, _⟩)
    · exact h5
    · exact (hi hfinite).elim
  · intro h5
    exact Or.inl ⟨hfinite, h5⟩

/-- Helper toward Definition 3.2: with no additional supplied junctions,
every nonempty boundary has exactly the v4 predicate. -/
theorem IsExternalFaceIntervalOrder5.nonempty_iff_of_none
    (hn : B.finiteJunctions? = none)
    (hne : Nonempty (InfiniteBoundaryDartIndex B.presentation)) :
    IsExternalFaceIntervalOrder5 M B G U S ↔
      IsExternalFaceIntervalOrder4 M B.presentation G U S := by
  constructor
  · exact fun h => h.toIsExternalFaceIntervalOrder4 hne
  · rintro (⟨hf, h4⟩ | ⟨hi, h3⟩)
    · exact Or.inl ⟨hf,
        (isFiniteExternalFaceIntervalOrder4_iff_core5.mp h4).1,
        suppliedFiniteJunctionLabels5_of_none hn⟩
    · exact Or.inr ⟨hi, hn, h3⟩

/-- Helper toward Definition 3.2: the finite core retains all four endpoint
validity predicates, including their zero-edge-path interpretation. -/
theorem FiniteExternalFaceIntervalCore5.endpointLabels
    (h : FiniteExternalFaceIntervalCore5 M P G U S) :
    BoundarySideEndpointLabels M P.upperLeft ∧
      BoundarySideEndpointLabels M P.upperRight ∧
      BoundarySideEndpointLabels M P.lowerRight ∧
      BoundarySideEndpointLabels M P.lowerLeft := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hul, hur, hlr, hll, _⟩
  exact ⟨hul, hur, hlr, hll⟩

/-- Helper toward Definition 3.2: exact labels on empty UL and LR sides
retain their two zero-edge paths. Equality of the two path vertices is not
assumed, nor is their distinctness. -/
theorem FiniteBoundaryJunctionLabels5.zero_edge_paths
    {J : FiniteBoundaryJunctions V}
    (h : FiniteBoundaryJunctionLabels5 P J)
    [IsEmpty P.upperLeft.Index] [IsEmpty P.lowerRight.Index]
    (hul : BoundarySideEndpointLabels M P.upperLeft)
    (hlr : BoundarySideEndpointLabels M P.lowerRight) :
    J.lowerLeftUpperLeft = J.upperLeftUpperRight ∧
      J.upperRightLowerRight = J.lowerRightLowerLeft := by
  rcases h with ⟨huli, hult, _, _, hlri, hlrt, _⟩
  exact ⟨hul.2.2 inferInstance _ _ huli hult,
    hlr.2.2 inferInstance _ _ hlri hlrt⟩

/-- Helper toward Definition 3.2: exact boundary coverage makes an entirely
empty listed boundary finite without using an exterior-frontier vertex test. -/
theorem FiniteExternalFaceIntervalCore5.finite_of_isEmpty
    (h : FiniteExternalFaceIntervalCore5 M P G U S)
    [IsEmpty (InfiniteBoundaryDartIndex P)] :
    (externalBoundaryDartSet4 M).Finite := by
  apply (externalBoundaryDartSet4_finite_iff M).mpr
  apply Set.finite_empty.subset
  intro e he
  rcases (((IsBoundaryOrderOfInf_iff P).mp h.1).1 e).mpr he with ⟨i, _⟩
  exact isEmptyElim i

/-- Helper toward Definition 3.2: on an entirely empty finite boundary,
supplied junctions require precisely their eight labels. This is a full
predicate characterization, not merely a condition on the new clause. -/
theorem IsExternalFaceIntervalOrder5.empty_iff_of_some
    [IsEmpty (InfiniteBoundaryDartIndex B.presentation)]
    (J : FiniteBoundaryJunctions V) (hj : B.finiteJunctions? = some J) :
    IsExternalFaceIntervalOrder5 M B G U S ↔
      FiniteExternalFaceIntervalCore5 M B.presentation G U S ∧
        FiniteBoundaryJunctionLabels5 B.presentation J := by
  constructor
  · rintro (⟨_, hc, hl⟩ | ⟨_, hn, _⟩)
    · exact ⟨hc, (suppliedFiniteJunctionLabels5_iff_of_some J hj).mp hl⟩
    · rw [hj] at hn
      cases hn
  · rintro ⟨hc, hl⟩
    exact Or.inl ⟨hc.finite_of_isEmpty, hc,
      (suppliedFiniteJunctionLabels5_iff_of_some J hj).mpr hl⟩

/-- Helper toward Definition 3.2: on an entirely empty boundary with no
supplied finite junctions, v5 imposes no labels beyond the unchanged core.
In particular the new clause does not select vertices from bare data. -/
theorem IsExternalFaceIntervalOrder5.empty_iff_of_none
    [IsEmpty (InfiniteBoundaryDartIndex B.presentation)]
    (hn : B.finiteJunctions? = none) :
    IsExternalFaceIntervalOrder5 M B G U S ↔
      FiniteExternalFaceIntervalCore5 M B.presentation G U S := by
  constructor
  · rintro (⟨_, hc, _⟩ | ⟨hi, _, h3⟩)
    · exact hc
    · have h4 : IsExternalFaceIntervalOrder4 M B.presentation G U S :=
        Or.inr ⟨hi, h3⟩
      have hmap := h4.boundary_coverage.1
      have hf : (externalBoundaryDartSet4 M).Finite := by
        apply (externalBoundaryDartSet4_finite_iff M).mpr
        apply Set.finite_empty.subset
        intro e he
        rcases (((IsBoundaryOrderOfInf_iff B.presentation).mp hmap).1 e).mpr he
          with ⟨i, _⟩
        exact isEmptyElim i
      exact (hi hf).elim
  · intro hc
    exact Or.inl ⟨hc.finite_of_isEmpty, hc,
      suppliedFiniteJunctionLabels5_of_none hn⟩

/-- Helper toward Definition 3.2: in the entirely empty supplied case the
two retained present paths are zero-edge paths at the prescribed junctions. -/
theorem IsExternalFaceIntervalOrder5.empty_supplied_zero_edge_paths
    [IsEmpty (InfiniteBoundaryDartIndex B.presentation)]
    (h : IsExternalFaceIntervalOrder5 M B G U S)
    (J : FiniteBoundaryJunctions V) (hj : B.finiteJunctions? = some J) :
    J.lowerLeftUpperLeft = J.upperLeftUpperRight ∧
      J.upperRightLowerRight = J.lowerRightLowerLeft := by
  rcases (IsExternalFaceIntervalOrder5.empty_iff_of_some J hj).mp h with ⟨hc, hl⟩
  let : IsEmpty B.presentation.upperLeft.Index :=
    ⟨fun i => isEmptyElim (InfiniteBoundaryDartIndex.upperLeft i)⟩
  let : IsEmpty B.presentation.lowerRight.Index :=
    ⟨fun i => isEmptyElim (InfiniteBoundaryDartIndex.lowerRight i)⟩
  exact hl.zero_edge_paths hc.endpointLabels.1 hc.endpointLabels.2.2.1

/-- Helper toward Definition 3.2: an empty boundary has an empty finite
cyclic position enumeration, independently of all endpoint labels. -/
theorem finiteBoundaryPositionOrder4_of_isEmpty
    [IsEmpty (InfiniteBoundaryDartIndex P)] :
    FiniteBoundaryPositionOrder4 P S := by
  let position : InfiniteBoundaryDartIndex P ≃ Fin 0 :=
    { toFun := fun i => isEmptyElim i
      invFun := fun i => Fin.elim0 i
      left_inv := fun i => isEmptyElim i
      right_inv := fun i => Fin.elim0 i }
  refine ⟨0, position, ?_, Or.inl rfl⟩
  intro i
  exact isEmptyElim i

/-- Helper toward Definition 3.2: an empty side is simple without a chosen
vertex; its optional zero-edge-path marks are checked separately. -/
theorem isSimpleBoundarySide_of_isEmpty5
    (Q : InfiniteBoundarySide.{uV, uE, uUL} V E) [IsEmpty Q.Index] :
    IsSimpleBoundarySide M Q := by
  constructor
  · intro i j _
    cases i with
    | inl i => exact isEmptyElim i
    | inr i => exact isEmptyElim i.val
  · intro i
    exact isEmptyElim i

/-- Helper toward Definition 3.2: absent endpoint labels satisfy endpoint
validity on any side; they do not choose a zero-edge-path vertex. -/
theorem boundarySideEndpointLabels_of_none5
    (Q : InfiniteBoundarySide.{uV, uE, uUL} V E)
    (hi : Q.initialVertex? = none) (ht : Q.terminalVertex? = none) :
    BoundarySideEndpointLabels M Q := by
  constructor
  · intro v hv
    rw [hi] at hv
    cases hv
  · constructor
    · intro v hv
      rw [ht] at hv
      cases hv
    · intro _ v z hv _
      rw [hi] at hv
      cases hv

/-- Helper toward Definition 3.2: for an entirely empty listed boundary,
the geometric/coverage and endpoint-validity obligations suffice for the
finite core. No existence of a presentation or geometric correspondence is
assumed silently or proved here. -/
theorem finiteExternalFaceIntervalCore5_of_isEmpty
    [IsEmpty (InfiniteBoundaryDartIndex P)]
    (hmap : IsBoundaryOrderOfInf M P)
    (hcover : ∀ d, G.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex P, InfiniteBoundaryDartIndex.dart P i = d)
    (hgeom : IsGeometricExternalFaceSucc G U S)
    (hend : BoundarySideEndpointLabels M P.upperLeft ∧
      BoundarySideEndpointLabels M P.upperRight ∧
      BoundarySideEndpointLabels M P.lowerRight ∧
      BoundarySideEndpointLabels M P.lowerLeft) :
    FiniteExternalFaceIntervalCore5 M P G U S := by
  let : IsEmpty P.upperLeft.Index :=
    ⟨fun i => isEmptyElim (InfiniteBoundaryDartIndex.upperLeft i)⟩
  let : IsEmpty P.upperRight.Index :=
    ⟨fun i => isEmptyElim (InfiniteBoundaryDartIndex.upperRight i)⟩
  let : IsEmpty P.lowerRight.Index :=
    ⟨fun i => isEmptyElim (InfiniteBoundaryDartIndex.lowerRight i)⟩
  let : IsEmpty P.lowerLeft.Index :=
    ⟨fun i => isEmptyElim (InfiniteBoundaryDartIndex.lowerLeft i)⟩
  refine ⟨hmap, hcover, ?_, hgeom, ULOkInf_of_isEmpty P, UROkInf_of_isEmpty P,
    LROkInf_of_isEmpty P, LLOkInf_of_isEmpty P,
    isSimpleBoundarySide_of_isEmpty5 P.upperLeft,
    isSimpleBoundarySide_of_isEmpty5 P.lowerRight,
    hend.1, hend.2.1, hend.2.2.1, hend.2.2.2,
    finiteBoundaryPositionOrder4_of_isEmpty, ?_, ?_⟩
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i

/-- Helper toward Definition 3.2: an entirely empty boundary with no supplied
junctions and all eight labels absent is accepted once its geometric coverage
and external-successor obligations are proved. No vertex is selected. -/
theorem IsExternalFaceIntervalOrder5.empty_without_labels
    [IsEmpty (InfiniteBoundaryDartIndex B.presentation)]
    (hn : B.finiteJunctions? = none)
    (hlabels : B.presentation.upperLeft.initialVertex? = none ∧
      B.presentation.upperLeft.terminalVertex? = none ∧
      B.presentation.upperRight.initialVertex? = none ∧
      B.presentation.upperRight.terminalVertex? = none ∧
      B.presentation.lowerRight.initialVertex? = none ∧
      B.presentation.lowerRight.terminalVertex? = none ∧
      B.presentation.lowerLeft.initialVertex? = none ∧
      B.presentation.lowerLeft.terminalVertex? = none)
    (hmap : IsBoundaryOrderOfInf M B.presentation)
    (hcover : ∀ d, G.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex B.presentation,
        InfiniteBoundaryDartIndex.dart B.presentation i = d)
    (hgeom : IsGeometricExternalFaceSucc G U S) :
    IsExternalFaceIntervalOrder5 M B G U S := by
  apply (IsExternalFaceIntervalOrder5.empty_iff_of_none hn).mpr
  apply finiteExternalFaceIntervalCore5_of_isEmpty hmap hcover hgeom
  rcases hlabels with ⟨huli, hult, huri, hurt, hlri, hlrt, hlli, hllt⟩
  exact ⟨boundarySideEndpointLabels_of_none5 B.presentation.upperLeft huli hult,
    boundarySideEndpointLabels_of_none5 B.presentation.upperRight huri hurt,
    boundarySideEndpointLabels_of_none5 B.presentation.lowerRight hlri hlrt,
    boundarySideEndpointLabels_of_none5 B.presentation.lowerLeft hlli hllt⟩

/-- Helper toward Definition 3.2: a supplied infinite UL ray and exact map
coverage imply that the map's external boundary is infinite. -/
theorem externalBoundaryDartSet4_infinite_of_upperLeft_ray
    (hmap : IsBoundaryOrderOfInf M P) (ray : ℕ ↪ P.upperLeft.Index) :
    ¬ (externalBoundaryDartSet4 M).Finite := by
  intro hf
  let f : ℕ → E × Bool := fun n => P.upperLeft.darts (ray n)
  have hinj : Function.Injective f := P.upperLeft.darts.injective.comp ray.injective
  have hpre : (f ⁻¹' externalBoundaryDartSet4 M).Finite := hf.preimage hinj.injOn
  apply Set.infinite_univ (α := ℕ)
  apply hpre.subset
  intro n _
  apply (((IsBoundaryOrderOfInf_iff P).mp hmap).1 _).mp
  refine ⟨InfiniteBoundaryDartIndex.upperLeft (ray n), ?_⟩
  rw [InfiniteBoundaryDartIndex.dart_eq]

/-- Helper toward Definition 3.2: an UL ray, in particular a nonempty
one-ended UL presentation, has exactly v3's predicate when finite junctions
are absent. Infinitude is proved from the ray and coverage in each direction, -/
theorem IsExternalFaceIntervalOrder5.upperLeft_ray_iff
    (hn : B.finiteJunctions? = none) (ray : ℕ ↪ B.presentation.upperLeft.Index) :
    IsExternalFaceIntervalOrder5 M B G U S ↔
      IsExternalFaceIntervalOrder3 M B.presentation G U S := by
  constructor
  · intro h5
    have hne : Nonempty (InfiniteBoundaryDartIndex B.presentation) :=
      ⟨InfiniteBoundaryDartIndex.upperLeft (ray 0)⟩
    have h4 := h5.toIsExternalFaceIntervalOrder4 hne
    have hi := externalBoundaryDartSet4_infinite_of_upperLeft_ray
      h4.boundary_coverage.1 ray
    exact h4.toIsExternalFaceIntervalOrder3 hi
  · intro h3
    have hi := externalBoundaryDartSet4_infinite_of_upperLeft_ray h3.1.1.1 ray
    exact (IsExternalFaceIntervalOrder5.infinite_iff hi).mpr ⟨hn, h3⟩

































end DirectedDistances.PlanarMap
