/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package3
public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance5

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter

/-- Helper toward Definition 3.2: the external successor of a labeled UIQBOT
boundary dart either follows its supplied within-side step or makes the unique
root junction to the first dart on the next nonempty side. -/
theorem uiqbot_successor_classification
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∀ i j : InfiniteBoundaryDartIndex P,
      uiqbotCanonicalBoundaryDartExternalSucc w hfin
          (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
        sideNext P i = some j ∨
          (sideNext P i = none ∧ firstOnSide P j ∧
            nextNonemptySide P (sideTag P i) (sideTag P j) ∧
            boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
              boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j)) := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  have hinj := uiqbotCanonicalBoundaryPresentationLabeledX_dartInjective
    w hfin htrans hR hL0
  let iLR := (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0).symm 0
  let eUL := uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0
  let iUL := eUL.symm 0
  have hrootSide : boundaryDartTerminal M (P.lowerRight.darts iLR) =
      boundaryDartInitial M (P.upperLeft.darts iUL) := by
    have hend := uiqbotCanonicalBoundaryPresentationLabeledX_rootEndpointVertices
      w hfin htrans hR hL0
    exact hend.1.trans hend.2.symm
  have hroot : boundaryDartTerminal M
      (InfiniteBoundaryDartIndex.dart P (.lowerRight iLR)) =
      boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P (.upperLeft iUL)) := by
    rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
    exact hrootSide
  intro i j hsucc
  by_cases hhas : ∃ k, sideNext P i = some k
  · obtain ⟨k, hk⟩ := hhas
    have hwithin := uiqbotCanonicalBoundaryPresentationLabeledX_withinSideSuccessor3
      w hfin htrans hR hL0 i k hk
    have hidx : j = k := hinj (hsucc.symm.trans hwithin.1)
    subst j
    exact Or.inl hk
  · have hstop : sideNext P i = none := by
      cases hnext : sideNext P i with
      | none => rfl
      | some k => exact (hhas ⟨k, hnext⟩).elim
    have hjoinSet :
        {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
          sideNext P p.1 = none ∧
            S (InfiniteBoundaryDartIndex.dart P p.1) =
              InfiniteBoundaryDartIndex.dart P p.2} =
          {(InfiniteBoundaryDartIndex.lowerRight iLR,
            InfiniteBoundaryDartIndex.upperLeft iUL)} := by
      simpa [P, S, iLR, iUL] using
        uiqbotCanonicalBoundaryPresentationLabeledX_unconditionalJoinSet
          w hfin htrans hR hL0
    have hpair : (i, j) ∈
        {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
          sideNext P p.1 = none ∧
            S (InfiniteBoundaryDartIndex.dart P p.1) =
              InfiniteBoundaryDartIndex.dart P p.2} := ⟨hstop, hsucc⟩
    rw [hjoinSet] at hpair
    have hp := Set.mem_singleton_iff.mp hpair
    have hi : i = .lowerRight iLR := congrArg Prod.fst hp
    have hj : j = .upperLeft iUL := congrArg Prod.snd hp
    subst i
    subst j
    refine Or.inr ⟨hstop, ?_, ?_, hroot⟩
    · intro k hprev
      cases k with
      | upperLeft n =>
          change ℕ at n
          simp [sideNext, uiqbotCanonicalBoundaryPresentationLabeledX,
            uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]
            at hprev
          injection hprev with hprev
          change n + 1 = eUL.symm 0 at hprev
          have hzero : eUL (n + 1) = 0 := by
            calc
              eUL (n + 1) = eUL (eUL.symm 0) := congrArg eUL hprev
              _ = 0 := eUL.apply_symm_apply 0
          have hself : eUL (n + 1) = n + 1 := by
            dsimp [eUL, uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv]
            rfl
          have hnat : n + 1 = 0 := hself.symm.trans hzero
          exact Nat.succ_ne_zero n (by simpa only [Nat.add_one] using hnat)
      | upperRight n => cases n
      | lowerRight n =>
          simp [sideNext, uiqbotCanonicalBoundaryPresentationLabeledX,
            uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation,
            iUL] at hprev
      | lowerLeft n => cases n
    · have hUL : Nonempty P.upperLeft.Index := ⟨iUL⟩
      have hUR : IsEmpty P.upperRight.Index := by
        change IsEmpty Empty
        infer_instance
      have hLR : Nonempty P.lowerRight.Index := ⟨iLR⟩
      have hLL : IsEmpty P.lowerLeft.Index := by
        change IsEmpty Empty
        infer_instance
      have hnext : nextNonemptySide P 2 0 := by
        unfold nextNonemptySide
        refine ⟨hUL, by norm_num [sideDistance], ?_⟩
        intro c hc₁ hc₂
        fin_cases c <;> simp_all [sideDistance, sideNonempty]
      simpa [sideTag] using hnext

/-- Helper toward Definition 3.2: the UIQBOT existence package with its exact
external successor classification and within-side successor obligations discharged. -/
theorem exists_uiqbot_bound_edges32
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool))
      (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) ℕ
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : G.Face) (S : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool →
        (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool),
      B = uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions
        w hfin htrans hR hL0 ∧ B.finiteJunctions? = none ∧
        IsBoundEdges32 M B G U S := by
  exact exists_uiqbot_bound_edges32_of_open_clauses3 w hfin htrans hR hL0
    (uiqbot_successor_classification w hfin htrans hR hL0)

end DirectedDistances.PaperProofs.Section4

end
