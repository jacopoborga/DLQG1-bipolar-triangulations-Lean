/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTSideSimplicity

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory Filter Quiver

/-- Helper toward Definition 3.2: the canonical geometric darts have the
KMSW west and east endpoints, with LR traversed in reverse. -/
private theorem uiqbotSimplicityEndpoints (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (e : ℕ) :
    let D := uiqbotPresentationDirectedMapX w hfin
    let M := uiqbotMapWithNoMissing D
    let ι := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
    (boundaryDartInitial M (ι e,
      M.forward ⟨ι e, by simp [M, uiqbotMapWithNoMissing]⟩) = edgeWest w e) ∧
    (boundaryDartInitial M (ι e,
      !(M.forward ⟨ι e, by simp [M, uiqbotMapWithNoMissing]⟩)) = edgeEast w e) ∧
    (boundaryDartTerminal M (ι e,
      !(M.forward ⟨ι e, by simp [M, uiqbotMapWithNoMissing]⟩)) = edgeWest w e) := by
  dsimp only
  let D := uiqbotPresentationDirectedMapX w hfin
  let M := uiqbotMapWithNoMissing D
  let ι := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  have hcompat (e : ℕ) : D.tail (ι e) = edgeWest w e ∧
      D.head (ι e) = edgeEast w e := by
    have hiota : ι e = Quotient.mk (uiqbotPresentationDrawing w hfin).edgeSetoid
        (e, false) := kmswGeometricEdgeEquiv_apply w hfin
          (uiqbotPresentationDrawing w hfin) e
    have htail (q : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
        D.tail q = (if !q.out.2 then kmswLimitDartVertex w q.out
          else kmswLimitDartVertex w (q.out.1, !q.out.2)) := by rfl
    have hhead (q : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
        D.head q = (if !q.out.2 then kmswLimitDartVertex w (q.out.1, !q.out.2)
          else kmswLimitDartVertex w q.out) := by rfl
    rw [hiota, htail, hhead]
    obtain hout | hout :=
      (uiqbotPresentationDrawing w hfin).geometricEdge_out_mk (e, false)
    · rw [hout]
      simp [kmswLimitDartVertex, edgeWest, edgeEast]
    · rw [hout]
      simp [kmswLimitDartVertex, edgeWest, edgeEast]
  have hmiss (e : ℕ) : ¬ M.toPlaneMapWithMissing.missing (ι e) := by
    simp [M, uiqbotMapWithNoMissing]
  have hUL (e : ℕ) : boundaryDartInitial M
      (ι e, M.forward ⟨ι e, hmiss e⟩) = edgeWest w e := by
    by_cases hf : D.forward (ι e)
    · simpa [boundaryDartInitial_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
    · simpa [boundaryDartInitial_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
  have hLRinitial (e : ℕ) : boundaryDartInitial M
      (ι e, !(M.forward ⟨ι e, hmiss e⟩)) = edgeEast w e := by
    by_cases hf : D.forward (ι e)
    · simpa [boundaryDartInitial_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).2
    · simpa [boundaryDartInitial_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).2
  have hLRterminal (e : ℕ) : boundaryDartTerminal M
      (ι e, !(M.forward ⟨ι e, hmiss e⟩)) = edgeWest w e := by
    by_cases hf : D.forward (ι e)
    · simpa [boundaryDartTerminal_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
    · simpa [boundaryDartTerminal_eq, M, uiqbotMapWithNoMissing, hf,
        DirectedPlaneMap.head, DirectedPlaneMap.tail] using (hcompat e).1
  exact ⟨hUL e, hLRinitial e, hLRterminal e⟩

/-- Helper toward Definition 3.2: UL occurrences follow the west endpoints
of successive left-boundary edges. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftVertexSequence
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let σ := uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
      w hfin htrans hR hL0
    ∀ i : ℕ, boundarySideVertex M P.upperLeft (.inl (σ.symm i)) =
      edgeWest w (kmswLeftBoundaryEdge w i) := by
  dsimp only
  intro i
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let ι := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let σ := uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0
  have hmiss (e : ℕ) : ¬ M.toPlaneMapWithMissing.missing (ι e) := by
    simp [M, uiqbotMapWithNoMissing]
  have hdart : P.upperLeft.darts (σ.symm i) =
      (ι (kmswLeftBoundaryEdge w i),
       M.forward ⟨ι (kmswLeftBoundaryEdge w i),
          hmiss (kmswLeftBoundaryEdge w i)⟩) := by
    change (uiqbotDefinition32Presentation w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).upperLeft.darts i = _
    rfl
  change boundaryDartInitial M (P.upperLeft.darts (σ.symm i)) = _
  rw [hdart]
  exact (uiqbotSimplicityEndpoints w hfin (kmswLeftBoundaryEdge w i)).1

/-- Helper toward Definition 3.2: LR initial occurrences are the successive
west endpoints on the right chain, and its terminal occurrence is the root. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightVertexSequence
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let ρ := uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
      w hfin htrans hR hL0
    (∀ i : ℕ, boundarySideVertex M P.lowerRight (.inl (ρ.symm i)) =
      edgeWest w (kmswRightBoundaryEdge w (i + 1))) ∧
    boundarySideVertex M P.lowerRight
      (.inr ⟨ρ.symm 0, by
        change (uiqbotDefinition32Presentation w htrans hR hL0
          (uiqbotPresentationDirectedMapX w hfin)
          (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).lowerRight.next (0 : ℕ) = none
        rfl⟩) = edgeWest w (kmswRightBoundaryEdge w 0) := by
  dsimp only
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let ι := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let ρ := uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0
  have hmiss (e : ℕ) : ¬ M.toPlaneMapWithMissing.missing (ι e) := by
    simp [M, uiqbotMapWithNoMissing]
  constructor
  · intro i
    have hdart : P.lowerRight.darts (ρ.symm i) =
        (ι (kmswRightBoundaryEdge w i),
         !M.forward ⟨ι (kmswRightBoundaryEdge w i),
            hmiss (kmswRightBoundaryEdge w i)⟩) := by
      change (uiqbotDefinition32Presentation w htrans hR hL0
        (uiqbotPresentationDirectedMapX w hfin)
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).lowerRight.darts (i : ℕ) = _
      rfl
    change boundaryDartInitial M (P.lowerRight.darts (ρ.symm i)) = _
    rw [hdart]
    have hend := (uiqbotSimplicityEndpoints w hfin
      (kmswRightBoundaryEdge w i)).2.1
    calc
      boundaryDartInitial M (P.lowerRight.darts (ρ.symm i)) =
          edgeEast w (kmswRightBoundaryEdge w i) := hend
      _ = edgeWest w (kmswRightBoundaryEdge w (i + 1)) :=
        (kmswRightBoundary_infinite_present_path w hL0 hR).2.1 i
  · have hdart : P.lowerRight.darts (ρ.symm 0) =
        (ι (kmswRightBoundaryEdge w 0),
         !M.forward ⟨ι (kmswRightBoundaryEdge w 0),
            hmiss (kmswRightBoundaryEdge w 0)⟩) := by
      change (uiqbotDefinition32Presentation w htrans hR hL0
        (uiqbotPresentationDirectedMapX w hfin)
        (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).lowerRight.darts (0 : ℕ) = _
      rfl
    change boundaryDartTerminal M (P.lowerRight.darts (ρ.symm 0)) = _
    rw [hdart]
    exact (uiqbotSimplicityEndpoints w hfin
      (kmswRightBoundaryEdge w 0)).2.2

/-- Helper toward Definition 3.2: a finite directed path along a present
boundary chain joins its west endpoint to a later east endpoint. -/
private def uiqbotSimplicityBoundaryPath (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (i : ℕ) : (k : ℕ) →
      Path (⟨edgeWest w (e i)⟩ : PresentVertex w)
        ⟨edgeEast w (e (i + k))⟩
  | 0 => Hom.toPath (⟨e i, hp i, rfl, rfl⟩ :
      (⟨edgeWest w (e i)⟩ : PresentVertex w) ⟶ ⟨edgeEast w (e i)⟩)
  | k + 1 => by
      simpa only [Nat.add_succ] using
        (congrArg (fun x => (⟨x⟩ : PresentVertex w)) (hpath (i + k)) ▸
          uiqbotSimplicityBoundaryPath w e hp hpath i k).cons
          (⟨e (i + k + 1), hp (i + k + 1), rfl, rfl⟩)

/-- Helper toward Definition 3.2: the finite boundary-chain path has positive
length. -/
private theorem uiqbotSimplicityBoundaryPath_pos (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (i k : ℕ) : 0 < (uiqbotSimplicityBoundaryPath w e hp hpath i k).length := by
  induction k with
  | zero => simp [uiqbotSimplicityBoundaryPath, Path.length_toPath]
  | succ k ih =>
      change 0 < ((congrArg (fun x => (⟨x⟩ : PresentVertex w))
        (hpath (i + k)) ▸ uiqbotSimplicityBoundaryPath w e hp hpath i k).cons _).length
      rw [Path.length_cons]
      omega

/-- Helper toward Definition 3.2: casting the endpoints of a path preserves
the path structure. -/
private def uiqbotSimplicityBoundaryPathCast {V : Type} [Quiver V]
    {a b c d : V} (hs : a = c) (ht : b = d) (p : Path a b) : Path c d :=
  Eq.ndrec (motive := fun c' => Path c' d)
    (Eq.ndrec (motive := fun d' => Path a d') p ht) hs

/-- Helper toward Definition 3.2: endpoint casts preserve path length. -/
private theorem uiqbotSimplicityBoundaryPathCast_length {V : Type} [Quiver V]
    {a b c d : V} (hs : a = c) (ht : b = d) (p : Path a b) :
    (uiqbotSimplicityBoundaryPathCast hs ht p).length = p.length := by
  cases hs
  cases ht
  rfl

/-- Helper toward Definition 3.2: west vertices on an infinite present
boundary chain never repeat. -/
private theorem uiqbotSimplicityBoundaryWest_no_repeat (w : ℕ → Fin 3)
    (e : ℕ → ℕ) (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    {i j : ℕ} (hij : i < j)
    (heq : edgeWest w (e i) = edgeWest w (e j)) : False := by
  let k := j - i - 1
  have hidx : i + k = j - 1 := by dsimp [k]; omega
  have hjpos : 0 < j := by omega
  have hend : edgeEast w (e (i + k)) = edgeWest w (e j) := by
    rw [hidx]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hpath (j - 1)
  let p := uiqbotSimplicityBoundaryPath w e hp hpath i k
  have ht : (⟨edgeEast w (e (i + k))⟩ : PresentVertex w) =
      ⟨edgeWest w (e i)⟩ := by
    apply congrArg (fun x => (⟨x⟩ : PresentVertex w))
    exact hend.trans heq.symm
  let loop := uiqbotSimplicityBoundaryPathCast rfl ht p
  have hzero := presentVertex_acyclic w _ loop
  have hpos : 0 < p.length := by
    simpa [p] using uiqbotSimplicityBoundaryPath_pos w e hp hpath i k
  rw [uiqbotSimplicityBoundaryPathCast_length rfl ht p] at hzero
  omega

/-- Helper toward Definition 3.2: west vertices on an infinite present
boundary chain are pairwise distinct. -/
private theorem uiqbotSimplicityBoundaryWest_injective (w : ℕ → Fin 3)
    (e : ℕ → ℕ) (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) :
    Function.Injective (fun i => edgeWest w (e i)) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact uiqbotSimplicityBoundaryWest_no_repeat w e hp hpath hij heq
  · exact uiqbotSimplicityBoundaryWest_no_repeat w e hp hpath hji heq.symm

/-- Helper toward Definition 3.2: the vertex-occurrence map of the canonical
upper-left side is injective. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftVertexInjective
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    Function.Injective (boundarySideVertex
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft) := by
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let σ := uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0
  have hnextULNat (i : ℕ) : P.upperLeft.next (σ.symm i) =
      some (σ.symm (i + 1)) := by
    change (uiqbotDefinition32Presentation w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).upperLeft.next i = some (i + 1)
    rfl
  have hnextUL (i : P.upperLeft.Index) :
      P.upperLeft.next i = some (σ.symm (σ i + 1)) := by
    rw [← σ.symm_apply_apply i]
    exact hnextULNat (σ i)
  have hseq := uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftVertexSequence
    w hfin htrans hR hL0
  change ∀ i : ℕ,
      boundarySideVertex M P.upperLeft (.inl (σ.symm i)) =
        edgeWest w (kmswLeftBoundaryEdge w i) at hseq
  have hseqIdx (i : P.upperLeft.Index) :
      boundarySideVertex M P.upperLeft (.inl i) = edgeWest w (kmswLeftBoundaryEdge w (σ i)) := by
    have hh := hseq (σ i)
    simpa only [Equiv.symm_apply_apply] using hh
  have hchain := kmswLeftBoundary_infinite_present_path w htrans hL0 hR
  have hwest := uiqbotSimplicityBoundaryWest_injective w
    (kmswLeftBoundaryEdge w) hchain.2.2.2 hchain.2.1
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          rw [hseqIdx i, hseqIdx j] at hab
          exact congrArg Sum.inl (σ.injective (hwest hab))
      | inr j =>
          have hnext : P.upperLeft.next j.val ≠ none := by
            rw [hnextUL]
            simp
          exact False.elim (hnext j.property)
  | inr i =>
      have hnext : P.upperLeft.next i.val ≠ none := by
        rw [hnextUL]
        simp
      exact False.elim (hnext i.property)

/-- Helper toward Definition 3.2: the vertex-occurrence map of the canonical
lower-right side is injective, including its terminal root occurrence. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightVertexInjective
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    Function.Injective (boundarySideVertex
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight) := by
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let ρ := uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0
  have hnextLRNat (i : ℕ) : P.lowerRight.next (ρ.symm i) =
      (if i = 0 then none else some (ρ.symm (i - 1))) := by
    change (uiqbotDefinition32Presentation w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).lowerRight.next i =
        (if i = 0 then none else some (i - 1))
    rfl
  have hnextLR (i : P.lowerRight.Index) :
      P.lowerRight.next i =
        (if ρ i = 0 then none else some (ρ.symm (ρ i - 1))) := by
    rw [← ρ.symm_apply_apply i]
    exact hnextLRNat (ρ i)
  have hseq := uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightVertexSequence
    w hfin htrans hR hL0
  change (∀ i : ℕ,
      boundarySideVertex M P.lowerRight (.inl (ρ.symm i)) =
        edgeWest w (kmswRightBoundaryEdge w (i + 1))) ∧
      boundarySideVertex M P.lowerRight
        (.inr ⟨ρ.symm 0, _⟩) = edgeWest w (kmswRightBoundaryEdge w 0) at hseq
  have hseqIdx (i : P.lowerRight.Index) :
      boundarySideVertex M P.lowerRight (.inl i) =
        edgeWest w (kmswRightBoundaryEdge w (ρ i + 1)) := by
    have hh := hseq.1 (ρ i)
    simpa only [Equiv.symm_apply_apply] using hh
  have hzero : P.lowerRight.next (ρ.symm 0) = none := by
    change (uiqbotDefinition32Presentation w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).lowerRight.next (0 : ℕ) = none
    rfl
  have hrootSeq : boundarySideVertex M P.lowerRight
      (.inr ⟨ρ.symm 0, hzero⟩) = edgeWest w (kmswRightBoundaryEdge w 0) := hseq.2
  have hroot : edgeWest w (kmswRightBoundaryEdge w 0) = 0 :=
    (kmswRightBoundary_infinite_present_path w hL0 hR).2.2.1
  have hchain := kmswRightBoundary_infinite_present_path w hL0 hR
  have hwest := uiqbotSimplicityBoundaryWest_injective w
    (kmswRightBoundaryEdge w) hchain.2.2.2 hchain.2.1
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          rw [hseqIdx i, hseqIdx j] at hab
          apply congrArg Sum.inl
          exact ρ.injective (Nat.succ.inj (hwest hab))
      | inr j =>
          have hj0 : ρ j.val = 0 := by
            by_contra hjne
            have hj := j.property
            rw [hnextLR] at hj
            simp [hjne] at hj
          have hjval : j.val = ρ.symm 0 := by
            apply ρ.injective
            rw [ρ.apply_symm_apply]
            exact hj0
          have hj : j = ⟨ρ.symm 0, hzero⟩ := Subtype.ext hjval
          rw [hj, hseqIdx i, hrootSeq] at hab
          have hbad := hwest hab
          omega
  | inr i =>
      cases b with
      | inl j =>
          have hi0 : ρ i.val = 0 := by
            by_contra hine
            have hi := i.property
            rw [hnextLR] at hi
            simp [hine] at hi
          have hival : i.val = ρ.symm 0 := by
            apply ρ.injective
            rw [ρ.apply_symm_apply]
            exact hi0
          have hi : i = ⟨ρ.symm 0, hzero⟩ := Subtype.ext hival
          rw [hi, hseqIdx j, hrootSeq] at hab
          have hbad := hwest hab.symm
          omega
      | inr j =>
          have hi0 : ρ i.val = 0 := by
            by_contra hine
            have hi := i.property
            rw [hnextLR] at hi
            simp [hine] at hi
          have hj0 : ρ j.val = 0 := by
            by_contra hjne
            have hj := j.property
            rw [hnextLR] at hj
            simp [hjne] at hj
          apply congrArg Sum.inr
          exact Subtype.ext (ρ.injective (hi0.trans hj0.symm))

/-- Helper toward Definition 3.2: the canonical UL successor has no finite
directed cycle. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftSimple
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    IsSimpleBoundarySide
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let σ := uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0
  have hnextNat (n : ℕ) : P.upperLeft.next (σ.symm n) = some (σ.symm (n + 1)) := by
    change (uiqbotDefinition32Presentation w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).upperLeft.next n =
        some (n + 1)
    rfl
  have hnext (i : P.upperLeft.Index) :
      P.upperLeft.next i = some (σ.symm (σ i + 1)) := by
    rw [← σ.symm_apply_apply i]
    exact hnextNat (σ i)
  have hstepLt : ∀ {i j : P.upperLeft.Index},
      P.upperLeft.next i = some j → σ i < σ j := by
    intro i j hstep
    rw [hnext] at hstep
    have heq := Option.some.inj hstep
    have hidx := congrArg σ heq
    simp only [Equiv.apply_symm_apply] at hidx
    omega
  unfold IsSimpleBoundarySide
  refine ⟨uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftVertexInjective
    w hfin htrans hR hL0, ?_⟩
  intro i hcycle
  have hlt : ∀ {i j : P.upperLeft.Index},
      Relation.TransGen (fun i j => P.upperLeft.next i = some j) i j → σ i < σ j := by
    intro i j h
    induction h with
    | single hstep => exact hstepLt hstep
    | tail hprefix hlast ih => exact lt_trans ih (hstepLt hlast)
  exact (Nat.lt_irrefl (σ i) (hlt hcycle)).elim

/-- Helper toward Definition 3.2: the canonical LR successor has no finite
directed cycle. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightSimple
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    IsSimpleBoundarySide
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let ρ := uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0
  have hnextNat (n : ℕ) : P.lowerRight.next (ρ.symm n) =
      (if n = 0 then none else some (ρ.symm (n - 1))) := by
    change (uiqbotDefinition32Presentation w htrans hR hL0
      (uiqbotPresentationDirectedMapX w hfin)
      (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin))).lowerRight.next n =
        (if n = 0 then none else some (n - 1))
    rfl
  have hnext (i : P.lowerRight.Index) :
      P.lowerRight.next i =
        (if ρ i = 0 then none else some (ρ.symm (ρ i - 1))) := by
    rw [← ρ.symm_apply_apply i]
    exact hnextNat (ρ i)
  have hstepLt : ∀ {i j : P.lowerRight.Index},
      P.lowerRight.next i = some j → ρ j < ρ i := by
    intro i j hstep
    have hi : ρ i ≠ 0 := by
      intro hz
      rw [hnext, if_pos hz] at hstep
      cases hstep
    rw [hnext, if_neg hi] at hstep
    have heq := Option.some.inj hstep
    have hidx := congrArg ρ heq
    simp only [Equiv.apply_symm_apply] at hidx
    omega
  unfold IsSimpleBoundarySide
  refine ⟨uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightVertexInjective
    w hfin htrans hR hL0, ?_⟩
  intro i hcycle
  have hlt : ∀ {i j : P.lowerRight.Index},
      Relation.TransGen (fun i j => P.lowerRight.next i = some j) i j → ρ j < ρ i := by
    intro i j h
    induction h with
    | single hstep => exact hstepLt hstep
    | tail hprefix hlast ih => exact lt_trans (hstepLt hlast) ih
  exact (Nat.lt_irrefl (ρ i) (hlt hcycle)).elim

end DirectedDistances.PaperProofs.Section4

end


