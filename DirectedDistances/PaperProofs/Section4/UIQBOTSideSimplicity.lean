/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTIntervalOrder3Clauses

/-! Helpers toward Definition 3.2: simplicity of the canonical UIQBOT sides. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory Filter Quiver

/-- Helper toward Definition 3.2: the hit event required by the hit-indexed
vertex enumeration is excluded by a nonnegative horizontal coordinate. -/
private theorem uiqbotBoundaryHitWitnesses_not_of_hL0 (w : ℕ → Fin 3)
    (hL0 : ∀ j, 0 ≤ L w j) : ¬ BoundaryHitWitnesses w := by
  intro h
  obtain ⟨n, hn⟩ := h.leftHit (-1) (by omega)
  have hnonneg := hL0 n
  omega

/-- Helper toward Definition 3.2: the endpoint maps on the canonical
presentation's two directed boundary chains are their KMSW endpoints. -/
private theorem uiqbotCanonicalBoundaryEndpoints (w : ℕ → Fin 3)
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

/-- Helper toward Definition 3.2: a finite directed path along a present
KMSW boundary chain. -/
private def uiqbotBoundaryPath (w : ℕ → Fin 3) (e : ℕ → ℕ)
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
          uiqbotBoundaryPath w e hp hpath i k).cons
          (⟨e (i + k + 1), hp (i + k + 1), rfl, rfl⟩)

/-- Helper toward Definition 3.2: every such nonempty chain path has positive
length. -/
private theorem uiqbotBoundaryPath_pos (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (i k : ℕ) : 0 < (uiqbotBoundaryPath w e hp hpath i k).length := by
  induction k with
  | zero => simp [uiqbotBoundaryPath, Path.length_toPath]
  | succ k ih =>
      change 0 < ((congrArg (fun x => (⟨x⟩ : PresentVertex w))
        (hpath (i + k)) ▸ uiqbotBoundaryPath w e hp hpath i k).cons _).length
      rw [Path.length_cons]
      omega

/-- Helper toward Definition 3.2: casting the endpoints of a path preserves
its length. -/
private def uiqbotBoundaryPathCast {V : Type} [Quiver V] {a b c d : V}
    (hs : a = c) (ht : b = d) (p : Path a b) : Path c d :=
  Eq.ndrec (motive := fun c' => Path c' d)
    (Eq.ndrec (motive := fun d' => Path a d') p ht) hs



private theorem uiqbotBoundaryPathCast_length {V : Type} [Quiver V]
    {a b c d : V} (hs : a = c) (ht : b = d) (p : Path a b) :
    (uiqbotBoundaryPathCast hs ht p).length = p.length := by
  cases hs
  cases ht
  rfl

/-- Helper toward Definition 3.2: west vertices on an infinite present
boundary chain are pairwise distinct. -/
private theorem uiqbotBoundaryWest_no_repeat (w : ℕ → Fin 3)
    (e : ℕ → ℕ) (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    {i j : ℕ} (hij : i < j)
    (heq : edgeWest w (e i) = edgeWest w (e j)) : False := by
  let k := j - i - 1
  have hsum : i + k + 1 = j := by dsimp [k]; omega
  have hidx : i + k = j - 1 := by omega
  have hjpos : 0 < j := by omega
  have hend : edgeEast w (e (i + k)) = edgeWest w (e j) := by
    rw [hidx]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hpath (j - 1)
  let p := uiqbotBoundaryPath w e hp hpath i k
  have ht : (⟨edgeEast w (e (i + k))⟩ : PresentVertex w) =
      ⟨edgeWest w (e i)⟩ := by
    apply congrArg (fun x => (⟨x⟩ : PresentVertex w))
    exact hend.trans heq.symm
  let loop := uiqbotBoundaryPathCast rfl ht p
  have hzero := presentVertex_acyclic w _ loop
  have hpos : 0 < p.length := by
    simpa [p] using uiqbotBoundaryPath_pos w e hp hpath i k
  rw [uiqbotBoundaryPathCast_length rfl ht p] at hzero
  omega

/-- Helper toward Definition 3.2: west vertices on an infinite present
boundary chain are pairwise distinct. -/
private theorem uiqbotBoundaryWest_injective (w : ℕ → Fin 3)
    (e : ℕ → ℕ) (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) :
    Function.Injective (fun i => edgeWest w (e i)) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact uiqbotBoundaryWest_no_repeat w e hp hpath hij heq
  · exact uiqbotBoundaryWest_no_repeat w e hp hpath hji heq.symm

/-- Helper toward Definition 3.2: event-conditional upper-left vertex
injectivity; the event is incompatible with `hL0`. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftVertexInjective_of_event
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (hevent : BoundaryHitWitnesses w) :
    Function.Injective (boundarySideVertex
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft) :=
  False.elim (uiqbotBoundaryHitWitnesses_not_of_hL0 w hL0 hevent)

/-- Helper toward Definition 3.2: event-conditional lower-right vertex
injectivity; the event is incompatible with `hL0`. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightVertexInjective_of_event
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (hevent : BoundaryHitWitnesses w) :
    Function.Injective (boundarySideVertex
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight) :=
  False.elim (uiqbotBoundaryHitWitnesses_not_of_hL0 w hL0 hevent)

/-- Helper toward Definition 3.2: event-conditional upper-left simplicity;
the event is incompatible with `hL0`. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftSimple_of_event
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (hevent : BoundaryHitWitnesses w) :
    IsSimpleBoundarySide
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft :=
  False.elim (uiqbotBoundaryHitWitnesses_not_of_hL0 w hL0 hevent)

/-- Helper toward Definition 3.2: event-conditional lower-right simplicity;
the event is incompatible with `hL0`. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightSimple_of_event
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (hevent : BoundaryHitWitnesses w) :
    IsSimpleBoundarySide
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight :=
  False.elim (uiqbotBoundaryHitWitnesses_not_of_hL0 w hL0 hevent)



























































































































































































































































end DirectedDistances.PaperProofs.Section4

end
