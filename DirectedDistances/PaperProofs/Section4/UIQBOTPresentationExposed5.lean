/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed4

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

variable {V : Type*} {E : Type*} {M : DirectedPlaneMapWithMissing V E}

/-- Helper toward Definition 3.2: the finite external-successor joins of a
boundary presentation. -/
@[expose] def uiqbotPresentationJoinSet (P : InfiniteBoundaryPresentation M)
    (S : E × Bool → E × Bool) :
    Set (InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P) :=
  {p | sideNext P p.1 = none ∧
    nextNonemptySide P (sideTag P p.1) (sideTag P p.2) ∧
    S (InfiniteBoundaryDartIndex.dart P p.1) =
      InfiniteBoundaryDartIndex.dart P p.2}

/-- Helper toward Definition 3.2: name the join set after updating the lower
left endpoint labels. -/
@[expose] def uiqbotEndpointUpdateJoinSet
    (P : InfiniteBoundaryPresentation M) (a b : Option V)
    (S : E × Bool → E × Bool) :
    Set (InfiniteBoundaryDartIndex (uiqbotEndpointUpdatePresentation P a b) ×
      InfiniteBoundaryDartIndex (uiqbotEndpointUpdatePresentation P a b)) :=
  uiqbotPresentationJoinSet (uiqbotEndpointUpdatePresentation P a b) S

/-- Helper toward Definition 3.2: name the original join set used when
transporting an endpoint update. -/
@[expose] def uiqbotEndpointUpdateOriginalJoinSet
    (P : InfiniteBoundaryPresentation M) (S : E × Bool → E × Bool) :
    Set (InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P) :=
  uiqbotPresentationJoinSet P S

/-- Helper toward Definition 3.2: membership in the updated join set is
equivalent to membership of the transported pair in the original join set. -/
theorem uiqbotEndpointUpdateJoinSet_mem_iff
    (P : InfiniteBoundaryPresentation M) (a b : Option V)
    (S : E × Bool → E × Bool)
    (p : InfiniteBoundaryDartIndex (uiqbotEndpointUpdatePresentation P a b) ×
      InfiniteBoundaryDartIndex (uiqbotEndpointUpdatePresentation P a b)) :
    p ∈ uiqbotEndpointUpdateJoinSet P a b S ↔
      (uiqbotEndpointUpdateIndexEquiv P a b p.1,
        uiqbotEndpointUpdateIndexEquiv P a b p.2) ∈
          uiqbotEndpointUpdateOriginalJoinSet P S := by
  let Q := uiqbotEndpointUpdatePresentation P a b
  let e := uiqbotEndpointUpdateIndexEquiv P a b
  change (sideNext Q p.1 = none ∧
      nextNonemptySide Q (sideTag Q p.1) (sideTag Q p.2) ∧
      S (InfiniteBoundaryDartIndex.dart Q p.1) =
        InfiniteBoundaryDartIndex.dart Q p.2) ↔
    (sideNext P (e p.1) = none ∧
      nextNonemptySide P (sideTag P (e p.1)) (sideTag P (e p.2)) ∧
      S (InfiniteBoundaryDartIndex.dart P (e p.1)) =
        InfiniteBoundaryDartIndex.dart P (e p.2))
  constructor
  · rintro ⟨hstop, hnext, hsucc⟩
    refine ⟨?_, ?_, ?_⟩
    · have htransport := uiqbotEndpointUpdateIndexEquiv_sideNext P a b p.1
      rw [← htransport]
      simpa using hstop
    · have htag₁ := uiqbotEndpointUpdateIndexEquiv_sideTag P a b p.1
      have htag₂ := uiqbotEndpointUpdateIndexEquiv_sideTag P a b p.2
      rw [← htag₁, ← htag₂] at hnext
      exact (uiqbotEndpointUpdate_nextNonemptySide P a b
        (sideTag P (e p.1)) (sideTag P (e p.2))).mp hnext
    · have hdart₁ := uiqbotEndpointUpdateIndexEquiv_dart P a b p.1
      have hdart₂ := uiqbotEndpointUpdateIndexEquiv_dart P a b p.2
      rw [← hdart₁, ← hdart₂] at hsucc
      exact hsucc
  · rintro ⟨hstop, hnext, hsucc⟩
    refine ⟨?_, ?_, ?_⟩
    · have htransport := uiqbotEndpointUpdateIndexEquiv_sideNext P a b p.1
      rw [← htransport] at hstop
      simpa using hstop
    · have htag₁ := uiqbotEndpointUpdateIndexEquiv_sideTag P a b p.1
      have htag₂ := uiqbotEndpointUpdateIndexEquiv_sideTag P a b p.2
      have hnext' := (uiqbotEndpointUpdate_nextNonemptySide P a b
        (sideTag P (e p.1)) (sideTag P (e p.2))).mpr hnext
      rw [← htag₁, ← htag₂]
      exact hnext'
    · have hdart₁ := uiqbotEndpointUpdateIndexEquiv_dart P a b p.1
      have hdart₂ := uiqbotEndpointUpdateIndexEquiv_dart P a b p.2
      rw [← hdart₁, ← hdart₂]
      exact hsucc

/-- Helper toward Definition 3.2: the updated join set is the image of the
original join set under the inverse index equivalence on both coordinates. -/
theorem uiqbotEndpointUpdate_joinSet
    (P : InfiniteBoundaryPresentation M) (a b : Option V)
    (S : E × Bool → E × Bool) :
    uiqbotEndpointUpdateJoinSet P a b S =
      Set.image (fun p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P =>
        ((uiqbotEndpointUpdateIndexEquiv P a b).symm p.1,
          (uiqbotEndpointUpdateIndexEquiv P a b).symm p.2))
        (uiqbotEndpointUpdateOriginalJoinSet P S) := by
  ext q
  rw [uiqbotEndpointUpdateJoinSet_mem_iff]
  change (uiqbotEndpointUpdateIndexEquiv P a b q.1,
      uiqbotEndpointUpdateIndexEquiv P a b q.2) ∈
        uiqbotEndpointUpdateOriginalJoinSet P S ↔
    q ∈ Set.image (fun p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P =>
      ((uiqbotEndpointUpdateIndexEquiv P a b).symm p.1,
        (uiqbotEndpointUpdateIndexEquiv P a b).symm p.2))
      (uiqbotEndpointUpdateOriginalJoinSet P S)
  constructor
  · intro h
    exact ⟨(uiqbotEndpointUpdateIndexEquiv P a b q.1,
      uiqbotEndpointUpdateIndexEquiv P a b q.2), h, by simp⟩
  · rintro ⟨p, hp, hq⟩
    change ((uiqbotEndpointUpdateIndexEquiv P a b).symm p.1,
      (uiqbotEndpointUpdateIndexEquiv P a b).symm p.2) = q at hq
    have hp₁ : p.1 = uiqbotEndpointUpdateIndexEquiv P a b q.1 := by
      have h := congrArg (uiqbotEndpointUpdateIndexEquiv P a b)
        (congrArg Prod.fst hq)
      simpa using h
    have hp₂ : p.2 = uiqbotEndpointUpdateIndexEquiv P a b q.2 := by
      have h := congrArg (uiqbotEndpointUpdateIndexEquiv P a b)
        (congrArg Prod.snd hq)
      simpa using h
    change (p.1, p.2) ∈ uiqbotPresentationJoinSet P S at hp
    rw [hp₁, hp₂] at hp
    exact hp

/-- Helper toward Definition 3.2: labeling the canonical presentation at the
root transports join-set membership through the constructor-preserving index
equivalence. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_mem_iff
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (q : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) ×
      InfiniteBoundaryDartIndex
        (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0)) :
    q ∈ uiqbotPresentationJoinSet
        (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0)
        (uiqbotCanonicalBoundaryDartExternalSucc w hfin) ↔
      (uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
          w hfin htrans hR hL0 q.1,
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
          w hfin htrans hR hL0 q.2) ∈
        uiqbotPresentationJoinSet
          (uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0)
          (uiqbotCanonicalBoundaryDartExternalSucc w hfin) := by
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
    w hfin htrans hR hL0
  change (sideNext Q q.1 = none ∧
      nextNonemptySide Q (sideTag Q q.1) (sideTag Q q.2) ∧
      S (InfiniteBoundaryDartIndex.dart Q q.1) =
        InfiniteBoundaryDartIndex.dart Q q.2) ↔
    (sideNext P (e q.1) = none ∧
      nextNonemptySide P (sideTag P (e q.1)) (sideTag P (e q.2)) ∧
      S (InfiniteBoundaryDartIndex.dart P (e q.1)) =
        InfiniteBoundaryDartIndex.dart P (e q.2))
  constructor
  · rintro ⟨hstop, hnext, hsucc⟩
    refine ⟨?_, ?_, ?_⟩
    · have htransport := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideNext
        w hfin htrans hR hL0 q.1
      rw [← htransport]
      simpa using hstop
    · have htag₁ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideTag
        w hfin htrans hR hL0 q.1
      have htag₂ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideTag
        w hfin htrans hR hL0 q.2
      rw [← htag₁, ← htag₂] at hnext
      have hn : nextNonemptySide Q (sideTag P (e q.1)) (sideTag P (e q.2)) ↔
          nextNonemptySide P (sideTag P (e q.1)) (sideTag P (e q.2)) := by rfl
      exact hn.mp hnext
    · have hdart₁ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_dart
        w hfin htrans hR hL0 q.1
      have hdart₂ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_dart
        w hfin htrans hR hL0 q.2
      rw [← hdart₁, ← hdart₂] at hsucc
      exact hsucc
  · rintro ⟨hstop, hnext, hsucc⟩
    refine ⟨?_, ?_, ?_⟩
    · have htransport := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideNext
        w hfin htrans hR hL0 q.1
      rw [← htransport] at hstop
      simpa using hstop
    · have htag₁ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideTag
        w hfin htrans hR hL0 q.1
      have htag₂ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_sideTag
        w hfin htrans hR hL0 q.2
      have hn : nextNonemptySide Q (sideTag P (e q.1)) (sideTag P (e q.2)) ↔
          nextNonemptySide P (sideTag P (e q.1)) (sideTag P (e q.2)) := by rfl
      have hnext' := hn.mpr hnext
      rw [← htag₁, ← htag₂]
      exact hnext'
    · have hdart₁ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_dart
        w hfin htrans hR hL0 q.1
      have hdart₂ := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv_dart
        w hfin htrans hR hL0 q.2
      rw [← hdart₁, ← hdart₂]
      exact hsucc

/-- Helper toward Definition 3.2: labeling the canonical presentation
transports its join set along the constructor-preserving index equivalence. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_transport
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
    let Q := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
      w hfin htrans hR hL0
    uiqbotPresentationJoinSet P S =
      Set.image (fun p : InfiniteBoundaryDartIndex Q × InfiniteBoundaryDartIndex Q =>
        (e.symm p.1, e.symm p.2)) (uiqbotPresentationJoinSet Q S) := by
  classical
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquiv
    w hfin htrans hR hL0
  change uiqbotPresentationJoinSet P S = _
  let f := fun p : InfiniteBoundaryDartIndex Q × InfiniteBoundaryDartIndex Q =>
    (e.symm p.1, e.symm p.2)
  ext q
  rw [uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_mem_iff]
  change (e q.1, e q.2) ∈ uiqbotPresentationJoinSet Q S ↔
    q ∈ Set.image f (uiqbotPresentationJoinSet Q S)
  constructor
  · intro h
    exact ⟨(e q.1, e q.2), h, by simp [f]⟩
  · rintro ⟨p, hp, hq⟩
    change (e.symm p.1, e.symm p.2) = q at hq
    have hp₁ : p.1 = e q.1 := by
      have h := congrArg e (congrArg Prod.fst hq)
      simpa using h
    have hp₂ : p.2 = e q.2 := by
      have h := congrArg e (congrArg Prod.snd hq)
      simpa using h
    change (p.1, p.2) ∈ uiqbotPresentationJoinSet Q S at hp
    rw [hp₁, hp₂] at hp
    exact hp































































end DirectedDistances.PaperProofs.Section4

end
