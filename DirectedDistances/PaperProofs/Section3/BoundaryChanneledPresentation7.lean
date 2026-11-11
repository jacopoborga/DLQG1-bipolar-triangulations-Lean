/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation6
public import DirectedDistances.PlanarMap.BoundEdgesMapDrawingBridge32

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the finite channel presentation has the
required endpoint labels at every closing join. -/
theorem boundaryChanneledPresentation_requiredJoinEndpointLabels7
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (_hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H) :
    RequiredFiniteBoundaryJoinEndpointLabels7
      (boundaryChanneledPresentationWithJunctions R G).presentation
      (fun d => rot.symm (d.1, !d.2)) := by
  let M := boundaryChanneledPlaneMap R G
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let S := fun d : G.GeometricEdge × Bool => rot.symm (d.1, !d.2)
  have hℓ : 0 < ℓ := R.B.left_length_pos
  have hr : 0 < r := R.B.right_length_pos
  have hULnonempty : Nonempty P.upperLeft.Index := by
    change Nonempty (Fin ℓ)
    exact ⟨⟨0, hℓ⟩⟩
  have hLRnonempty : Nonempty P.lowerRight.Index := by
    change Nonempty (Fin r)
    exact ⟨⟨0, hr⟩⟩
  have hBoth : Nonempty P.upperLeft.Index ∧ Nonempty P.lowerRight.Index :=
    ⟨hULnonempty, hLRnonempty⟩
  have hLabels := boundaryChanneledPresentation_presentSide_endpointLabels6 R G
  have hULinitial : P.upperLeft.initialVertex? = some R.B.source := by
    simp [P, boundaryChanneledPresentationWithJunctions]
  have hULterminal : P.upperLeft.terminalVertex? = some R.B.sink := by
    simp [P, boundaryChanneledPresentationWithJunctions]
  have hLRinitial : P.lowerRight.initialVertex? = some R.B.sink := by
    simp [P, boundaryChanneledPresentationWithJunctions]
  have hLRterminal : P.lowerRight.terminalVertex? = some R.B.source := by
    simp [P, boundaryChanneledPresentationWithJunctions]
  have hULlast : ∃ a : P.upperLeft.Index,
      P.upperLeft.next a = none ∧
        boundaryDartTerminal M (P.upperLeft.darts a) = R.B.sink := by
    have h := hLabels.1.2.1 R.B.sink hULterminal
    exact h.1 hULnonempty
  have hLRlast : ∃ a : P.lowerRight.Index,
      P.lowerRight.next a = none ∧
        boundaryDartTerminal M (P.lowerRight.darts a) = R.B.source := by
    have h := hLabels.2.2.1 R.B.source hLRterminal
    exact h.1 hLRnonempty
  have hULterminal_of_last : ∀ a : P.upperLeft.Index,
      P.upperLeft.next a = none →
        boundaryDartTerminal M (P.upperLeft.darts a) = R.B.sink := by
    exact (hLabels.1.2.1 R.B.sink hULterminal).2
  have hLRterminal_of_last : ∀ a : P.lowerRight.Index,
      P.lowerRight.next a = none →
        boundaryDartTerminal M (P.lowerRight.darts a) = R.B.source := by
    exact (hLabels.2.2.1 R.B.source hLRterminal).2
  have hURinitial : P.upperRight.initialVertex? = some R.B.sink := by
    simp [P, boundaryChanneledPresentationWithJunctions, emptyBoundarySide]
  have hURterminal : P.upperRight.terminalVertex? = some R.B.sink := by
    simp [P, boundaryChanneledPresentationWithJunctions, emptyBoundarySide]
  have hLLinitial : P.lowerLeft.initialVertex? = some R.B.source := by
    simp [P, boundaryChanneledPresentationWithJunctions, emptyBoundarySide]
  have hLLterminal : P.lowerLeft.terminalVertex? = some R.B.source := by
    simp [P, boundaryChanneledPresentationWithJunctions, emptyBoundarySide]
  have hURempty : IsEmpty P.upperRight.Index := by
    change IsEmpty Empty
    infer_instance
  have hLLempty : IsEmpty P.lowerLeft.Index := by
    change IsEmpty Empty
    infer_instance
  constructor
  · intro _
    unfold RequiredFiniteBoundaryJoinEndpointLabels4
    intro i j hsucc hstop
    have hjoin :
        boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
          boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j) := by
      let d := InfiniteBoundaryDartIndex.dart P i
      have hrot := H.vert_rotation (rot.symm (d.1, !d.2))
      rw [Equiv.apply_symm_apply] at hrot
      calc
        boundaryDartTerminal M d = boundaryDartInitial M (d.1, !d.2) := by
          rw [boundaryDartTerminal_eq, boundaryDartInitial_eq]
          cases d.2 <;> rfl
        _ = boundaryDartInitial M (rot.symm (d.1, !d.2)) := hrot
        _ = boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j) := by
          exact congrArg (boundaryDartInitial M) hsucc
    cases i with
    | upperLeft i =>
        have hstop' : P.upperLeft.next i = none := by
          simpa [sideNext] using hstop
        have hvi :
            boundaryDartTerminal M (P.upperLeft.darts i) = R.B.sink :=
          hULterminal_of_last i hstop'
        cases j with
        | upperLeft j =>
            have hjoin' : boundaryDartTerminal M (P.upperLeft.darts i) =
                boundaryDartInitial M (P.upperLeft.darts j) := by
              simpa only [InfiniteBoundaryDartIndex.dart_eq] using hjoin
            have hinit : boundaryDartInitial M (P.upperLeft.darts j) = R.B.sink :=
              hjoin'.symm.trans hvi
            rcases hULlast with ⟨a, ha, hterm⟩
            let x : P.upperLeft.Index ⊕
                {a : P.upperLeft.Index // P.upperLeft.next a = none} := Sum.inl j
            let y : P.upperLeft.Index ⊕
                {a : P.upperLeft.Index // P.upperLeft.next a = none} := Sum.inr ⟨a, ha⟩
            have hvertex :
                boundarySideVertex M P.upperLeft x =
                  boundarySideVertex M P.upperLeft y := by
              change boundaryDartInitial M (P.upperLeft.darts j) =
                boundaryDartTerminal M (P.upperLeft.darts a)
              exact hinit.trans hterm.symm
            have hsimple := boundaryChanneledPresentation_upperLeft_simple R G
            have heq : x = y := hsimple.1 hvertex
            have hne : x ≠ y := by simp [x, y]
            exact (hne heq).elim
        | upperRight j => exact False.elim (hURempty.false j)
        | lowerRight j =>
            simp only [InfiniteBoundaryDartIndex.dart_eq] at ⊢
            dsimp only [sideTag, sideTerminalVertex?, sideInitialVertex?]
            norm_num at ⊢
            refine ⟨?_, ?_, ?_⟩
            · change P.upperLeft.terminalVertex? =
                some (boundaryDartTerminal M (P.upperLeft.darts i))
              rw [hvi]
              exact hULterminal
            · change P.lowerRight.initialVertex? =
                some (boundaryDartTerminal M (P.upperLeft.darts i))
              rw [hvi]
              exact hLRinitial
            · intro k hk₁ hk₂
              fin_cases k
              · simp [sideDistance] at hk₁
              · rw [hvi]
                exact ⟨hURinitial, hURterminal⟩
              · simp [sideDistance] at hk₂
              · simp [sideDistance] at hk₂
        | lowerLeft j => exact False.elim (hLLempty.false j)
    | upperRight i => exact False.elim (hURempty.false i)
    | lowerRight i =>
        have hstop' : P.lowerRight.next i = none := by
          simpa [sideNext] using hstop
        have hvi :
            boundaryDartTerminal M (P.lowerRight.darts i) = R.B.source :=
          hLRterminal_of_last i hstop'
        cases j with
        | upperLeft j =>
            simp only [InfiniteBoundaryDartIndex.dart_eq] at ⊢
            dsimp only [sideTag, sideTerminalVertex?, sideInitialVertex?]
            norm_num at ⊢
            refine ⟨?_, ?_, ?_⟩
            · change P.lowerRight.terminalVertex? =
                some (boundaryDartTerminal M (P.lowerRight.darts i))
              rw [hvi]
              exact hLRterminal
            · change P.upperLeft.initialVertex? =
                some (boundaryDartTerminal M (P.lowerRight.darts i))
              rw [hvi]
              exact hULinitial
            · intro k hk₁ hk₂
              fin_cases k
              · simp [sideDistance] at hk₂
              · simp [sideDistance] at hk₂
              · simp [sideDistance] at hk₁
              · rw [hvi]
                exact ⟨hLLinitial, hLLterminal⟩
        | upperRight j => exact False.elim (hURempty.false j)
        | lowerRight j =>
            have hjoin' : boundaryDartTerminal M (P.lowerRight.darts i) =
                boundaryDartInitial M (P.lowerRight.darts j) := by
              simpa only [InfiniteBoundaryDartIndex.dart_eq] using hjoin
            have hinit : boundaryDartInitial M (P.lowerRight.darts j) = R.B.source :=
              hjoin'.symm.trans hvi
            rcases hLRlast with ⟨a, ha, hterm⟩
            let x : P.lowerRight.Index ⊕
                {a : P.lowerRight.Index // P.lowerRight.next a = none} := Sum.inl j
            let y : P.lowerRight.Index ⊕
                {a : P.lowerRight.Index // P.lowerRight.next a = none} := Sum.inr ⟨a, ha⟩
            have hvertex :
                boundarySideVertex M P.lowerRight x =
                  boundarySideVertex M P.lowerRight y := by
              change boundaryDartInitial M (P.lowerRight.darts j) =
                boundaryDartTerminal M (P.lowerRight.darts a)
              exact hinit.trans hterm.symm
            have hsimple := boundaryChanneledPresentation_lowerRight_simple R G
            have heq : x = y := hsimple.1 hvertex
            have hne : x ≠ y := by simp [x, y]
            exact (hne heq).elim
        | lowerLeft j => exact False.elim (hLLempty.false j)
    | lowerLeft i => exact False.elim (hLLempty.false i)
  · intro hnot
    have hBoth' :
        Nonempty (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.Index ∧
          Nonempty (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.Index := by
      simpa [P] using hBoth
    exact (hnot hBoth').elim

end DirectedDistances.PaperProofs.Section3

end
end

