/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder7

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: a finite all-missing cycle with empty
present paths is accepted without selecting a junction vertex or labeling the
bare missing runs. -/
theorem bare_all_missing_cycle_without_labels
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (P : InfiniteBoundaryPresentation.{uV, uE, uUL, uUR, uLR, uLL} M)
    [IsEmpty P.upperLeft.Index] [IsEmpty P.lowerRight.Index]
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (hfinite : (externalBoundaryDartSet4 M).Finite)
    (hne : Nonempty (InfiniteBoundaryDartIndex P))
    (hmap : IsBoundaryOrderOfInf M P)
    (hcover : ∀ d, G.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex P, InfiniteBoundaryDartIndex.dart P i = d)
    (hgeom : IsGeometricExternalFaceSucc G U S)
    (hsides : UROkInf P ∧ LLOkInf P)
    (hpositions : FiniteBoundaryPositionOrder4 P S)
    (hjoins : ∀ i j : InfiniteBoundaryDartIndex P,
      S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j))
    (hnolabels : ∀ k : Fin 4,
      sideInitialVertex? P k = none ∧ sideTerminalVertex? P k = none) :
    IsExternalFaceIntervalOrder7 M
      { presentation := P, finiteJunctions? := none } G U S := by
  have hurok := (UROkInf_iff P).mp hsides.1
  have hllok := (LLOkInf_iff P).mp hsides.2
  have hdart_missing : ∀ i : InfiniteBoundaryDartIndex P,
      M.toPlaneMapWithMissing.missing (InfiniteBoundaryDartIndex.dart P i).1 := by
    intro i
    cases i with
    | upperLeft i => exact isEmptyElim i
    | upperRight i =>
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hurok.1 i
    | lowerRight i => exact isEmptyElim i
    | lowerLeft i =>
      simpa only [InfiniteBoundaryDartIndex.dart_eq] using hllok.1 i
  have hinj : Function.Injective (InfiniteBoundaryDartIndex.dart P) := by
    intro i j hij
    by_contra hneij
    have hdup := (((IsBoundaryOrderOfInf_iff P).mp hmap).2.2)
      (InfiniteBoundaryDartIndex.dart P i).1 i j hneij rfl
      (congrArg Prod.fst hij).symm
    rcases hdup with ⟨hnotmissing, _, _⟩
    exact hnotmissing (hdart_missing i)
  have hULnone : P.upperLeft.initialVertex? = none ∧
      P.upperLeft.terminalVertex? = none := by
    simpa [sideInitialVertex?, sideTerminalVertex?] using hnolabels (0 : Fin 4)
  have hURnone : P.upperRight.initialVertex? = none ∧
      P.upperRight.terminalVertex? = none := by
    simpa [sideInitialVertex?, sideTerminalVertex?] using hnolabels (1 : Fin 4)
  have hLRnone : P.lowerRight.initialVertex? = none ∧
      P.lowerRight.terminalVertex? = none := by
    simpa [sideInitialVertex?, sideTerminalVertex?] using hnolabels (2 : Fin 4)
  have hLLnone : P.lowerLeft.initialVertex? = none ∧
      P.lowerLeft.terminalVertex? = none := by
    simpa [sideInitialVertex?, sideTerminalVertex?] using hnolabels (3 : Fin 4)
  have hlabelsUL : BoundarySideEndpointLabels M P.upperLeft :=
    boundarySideEndpointLabels_of_none6 P.upperLeft hULnone.1 hULnone.2
  have hlabelsUR : BoundarySideEndpointLabels M P.upperRight :=
    boundarySideEndpointLabels_of_none6 P.upperRight hURnone.1 hURnone.2
  have hlabelsLR : BoundarySideEndpointLabels M P.lowerRight :=
    boundarySideEndpointLabels_of_none6 P.lowerRight hLRnone.1 hLRnone.2
  have hlabelsLL : BoundarySideEndpointLabels M P.lowerLeft :=
    boundarySideEndpointLabels_of_none6 P.lowerLeft hLLnone.1 hLLnone.2
  have hclose : Nonempty (InfiniteBoundaryDartIndex P) →
      RequiredFiniteBoundaryJoinEndpointLabels7 P S := by
    intro _
    constructor
    · intro hboth
      exact isEmptyElim hboth.1.some
    · intro _
      constructor
      · constructor
        · intro hnonempty
          exact isEmptyElim hnonempty.some
        · intro hnonempty
          exact isEmptyElim hnonempty.some
      · constructor
        · intro hnonempty
          exact isEmptyElim hnonempty.some
        · intro hnonempty
          exact isEmptyElim hnonempty.some
  have hcore : FiniteExternalFaceIntervalCore7 M P G U S := by
    exact ⟨hmap, hcover, hinj, hgeom,
      ULOkInf_of_isEmpty P, hsides.1, LROkInf_of_isEmpty P, hsides.2,
      isSimpleBoundarySide_of_isEmpty6 P.upperLeft,
      isSimpleBoundarySide_of_isEmpty6 P.lowerRight,
      hlabelsUL, hlabelsUR, hlabelsLR, hlabelsLL, hpositions, hjoins,
      fun _ => hclose hne⟩
  exact (IsExternalFaceIntervalOrder7.finite_iff hfinite).mpr
    ⟨hcore, suppliedFiniteJunctionLabels6_of_none rfl⟩

end DirectedDistances.PlanarMap

end
