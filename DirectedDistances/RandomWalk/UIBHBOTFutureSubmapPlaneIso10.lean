module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso8
import DirectedDistances.KMSW.UIBHBOTGlueDrawingCcw
import DirectedDistances.KMSW.InfiniteTriangulation
import DirectedDistances.KMSW.PastFaceSucc
import all DirectedDistances.KMSW.StageReversalEdges
import Mathlib.Dynamics.PeriodicPts.Defs
import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryLabels

/-! This file records the positive-index external-dart first-return obligation
and proves an obstruction to it under the current plane-side definition.
The imported code-side successor is `j ↦ j - 1`, and Iso4 identifies the
positive-index dart with its KMSW right-boundary edge. The required statement
below concerns the first return of the ambient whole-plane face successor to
the future-submap carrier.

At absolute time zero the nonnegative boundary darts belong to past creation
triangles, and their ambient face-successor orbits close after three steps.
Consequently the recorded positive-index agreement is almost surely impossible:
the transitions at labels 3, 2, and 1 would put four distinct boundary darts in
one three-periodic orbit. The outer face obtained after removing past edges
cannot be represented by first return within a single ambient face orbit.
No definition in Iso2, source statement, or target binder is changed here. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5

/-- Helper toward Lemma 5.10. At absolute time zero, every nonnegative
future boundary dart belongs to a past creation triangle. This identifies
its ambient face; it does not identify the outer face of the submap with
that single ambient face. -/
theorem ae_uibhbot_runZero_boundary_past_triangle :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ h0 : BoundaryHitWitnesses (shiftedStream W 0),
          ∀ j : ℤ, 0 ≤ j →
            ∃ (e : ℕ) (t : TriangleCreationTime (kmswPastCode W)),
              wholePlaneDartι W 0
                  (futureMapBoundaryDart (shiftedStream W 0) h0 j) =
                kmswPastDart W (e, false) ∧
              (e, false) ∈ stageTriangleDartList (kmswPastCode W) t := by
  filter_upwards [uibhbotCodeLawRel_ae_past_leftHit,
    uibhbotCodeLawRel_ae_past_R_nonneg,
    uibhbotCodeLawRel_ae_past_finiteIncidence] with W hL hR hfin h0 j hj
  obtain ⟨e, ⟨N, he⟩, heq⟩ :=
    uibhbotCcw_nonneg_boundary_in_past W h0 hL hR.1 hfin j hj
  have hdart : wholePlaneDartι W 0
      (futureMapBoundaryDart (shiftedStream W 0) h0 j) =
        kmswPastDart W (e, false) := by
    change (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 j), true) =
      (kmswPastEdge W e, true)
    rw [heq]
  rcases List.mem_append.mp he with he | he
  · obtain ⟨s, _, hc, hm, hse⟩ :=
      kmswStage_LL_exists_revLeftRecord (kmswPastCode W) N e he
    have hnil : (kmswStage (kmswPastCode W) s).UL.dropLast.reverse = [] := by
      have hl := kmswStage_UL_length (kmswPastCode W) s
      apply List.length_eq_zero_iff.mp
      simp only [List.length_reverse, List.length_dropLast]
      omega
    let t : TriangleCreationTime (kmswPastCode W) := ⟨s, Or.inl hc⟩
    refine ⟨e, t, hdart, ?_⟩
    simp [stageTriangleDartList, stageTriangleDartTriple, t, hc, hnil, hse]
  · rw [uibhbotPastStage_LR_eq_root W hR.1 N] at he
    have he0 : e = 0 := List.mem_singleton.mp he
    subst e
    have hc := uibhbotCcw_past_first_up W hR.2
    let t : TriangleCreationTime (kmswPastCode W) := ⟨0, Or.inr hc⟩
    refine ⟨0, t, hdart, ?_⟩
    simp [stageTriangleDartList, stageTriangleDartTriple, t, hc, kmswStage, kmswInit]

/-- Helper toward Lemma 5.10. The ambient face of a nonnegative run-zero
boundary dart closes after three steps. Following this one triangle does
not traverse the merged outer face of the future submap. -/
theorem ae_uibhbot_runZero_boundary_faceSucc_iterate_three :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ h0 : BoundaryHitWitnesses (shiftedStream W 0),
        ∀ H : WholePlaneRotationHypothesis W,
          ∀ j : ℤ, 0 ≤ j →
            (wholePlaneFaceSucc W H)^[3]
                (wholePlaneDartι W 0
                  (futureMapBoundaryDart (shiftedStream W 0) h0 j)) =
              wholePlaneDartι W 0
                (futureMapBoundaryDart (shiftedStream W 0) h0 j) := by
  filter_upwards [ae_uibhbot_runZero_boundary_past_triangle,
    uibhbotCodeLawRel_ae_past_finiteIncidence] with W htri hfin h0 H j hj
  obtain ⟨e, t, he, ht⟩ := htri h0 j hj
  rw [he]
  let p := stageTriangleDartTriple (kmswPastCode W) t
  have hc := kmswInfFaceSucc_stageTriangle_cycle (kmswPastCode W) hfin t
  change FaceSucc3Cycle _ p.1 p.2.1 p.2.2 at hc
  have hs (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList (kmswPastCode W) t) :=
    kmswPastDart_faceSucc_of_triangle W H hfin d ⟨t, hd⟩
  have h1 : p.1 ∈ stageTriangleDartList (kmswPastCode W) t := by
    simp only [stageTriangleDartList, p, List.mem_cons, true_or]
  have h2 : p.2.1 ∈ stageTriangleDartList (kmswPastCode W) t := by
    simp only [stageTriangleDartList, p, List.mem_cons, true_or, or_true]
  have h3 : p.2.2 ∈ stageTriangleDartList (kmswPastCode W) t := by
    simp only [stageTriangleDartList, p, List.mem_cons, true_or, or_true]
  have hs1 := (hs p.1 h1).trans (congrArg (kmswPastDart W) hc.1)
  have hs2 := (hs p.2.1 h2).trans (congrArg (kmswPastDart W) hc.2.1)
  have hs3 := (hs p.2.2 h3).trans (congrArg (kmswPastDart W) hc.2.2.1)
  change (e, false) ∈ [p.1, p.2.1, p.2.2] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht
  · rw [ht]
    change wholePlaneFaceSucc W H (wholePlaneFaceSucc W H
      (wholePlaneFaceSucc W H (kmswPastDart W p.1))) = _
    rw [hs1, hs2, hs3]
  · rw [ht]
    change wholePlaneFaceSucc W H (wholePlaneFaceSucc W H
      (wholePlaneFaceSucc W H (kmswPastDart W p.2.1))) = _
    rw [hs2, hs3, hs1]
  · rw [ht]
    change wholePlaneFaceSucc W H (wholePlaneFaceSucc W H
      (wholePlaneFaceSucc W H (kmswPastDart W p.2.2))) = _
    rw [hs3, hs1, hs2]

/-- Helper toward Lemma 5.10. With the recorded ambient-face first-return
definition, the positive-index agreement cannot hold even at start zero:
four distinct boundary darts cannot lie in one three-periodic ambient orbit.
This concerns the current representation, not a discrepancy in the paper. -/
theorem ae_uibhbotFuturePlaneGeometricSide_not_all_positive_faceNext_zero :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode 0 W (i + 1)),
        ∀ H : WholePlaneRotationHypothesis W,
          ¬ ∀ j : ℤ, 1 ≤ j →
            (uibhbotFuturePlaneGeometricSide 0 W h H).faceNext
              (futureMapBoundaryDart (fun i => uibhbotFutureCode 0 W (i + 1)) h j)
              (futureMapBoundaryDart (fun i => uibhbotFutureCode 0 W (i + 1)) h (j - 1)) := by
  filter_upwards [ae_uibhbot_runZero_boundary_faceSucc_iterate_three,
    ae_uibhbotBoundaryHitTime_zero] with W hperiod htime h H
  intro hagree
  let f := wholePlaneFaceSucc W H
  let b (j : ℤ) := (uibhbotFutureSubmapDartEquiv 0 W h
    (futureMapBoundaryDart (fun i => uibhbotFutureCode 0 W (i + 1)) h j)).1
  have hb : Function.Injective b := by
    intro i j hij
    apply futureMapBoundaryDart_injective _ h
    apply (uibhbotFutureSubmapDartEquiv 0 W h).injective
    exact Subtype.ext hij
  have hstream : (fun i => uibhbotFutureCode 0 W (i + 1)) = shiftedStream W 0 := by
    rw [uibhbotFutureCode_stream, htime,
      lemma38StartStream_eq_shifted W 0 (by omega)]
    rfl
  have h0 : BoundaryHitWitnesses (shiftedStream W 0) := by
    rw [← hstream]
    exact h
  have hmap (j : ℤ) : b j = wholePlaneDartι W 0
      (futureMapBoundaryDart (shiftedStream W 0) h0 j) := by
    dsimp only [b]
    rw [uibhbotFutureSubmapDartEquiv_val]
    simp only [uibhbotFutureEdge, htime, lemma38StartEdgeι,
      le_refl, ite_true, Int.natAbs_zero, wholePlaneDartι]
    have hboundary : futureMapBoundaryDart
        (fun i => uibhbotFutureCode 0 W (i + 1)) h j =
          futureMapBoundaryDart (shiftedStream W 0) h0 j := by
      have hh : h = (by rw [hstream]; exact h0) := Subsingleton.elim _ _
      rw [hh]
      simp only [hstream]
    rw [hboundary]
  have hp : Function.IsPeriodicPt f 3 (b 3) := by
    change f^[3] (b 3) = b 3
    rw [hmap]
    exact hperiod h0 H 3 (by omega)
  obtain ⟨n3, _, hn3, _⟩ := hagree 3 (by omega)
  obtain ⟨n2, _, hn2, _⟩ := hagree 2 (by omega)
  obtain ⟨n1, _, hn1, _⟩ := hagree 1 (by omega)
  change f^[n3] (b 3) = b 2 at hn3
  change f^[n2] (b 2) = b 1 at hn2
  change f^[n1] (b 1) = b 0 at hn1
  let times : Fin 4 → ℕ := ![0, n3, n2 + n3, n1 + (n2 + n3)]
  have htimes (i : Fin 4) : f^[times i] (b 3) = b (3 - (i.val : ℤ)) := by
    fin_cases i
    · rfl
    · exact hn3
    · change f^[n2 + n3] (b 3) = b 1
      rw [Function.iterate_add_apply, hn3, hn2]
    · change f^[n1 + (n2 + n3)] (b 3) = b 0
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hn3, hn2, hn1]
  let residues (i : Fin 4) : Fin 3 := ⟨times i % 3, Nat.mod_lt _ (by omega)⟩
  have hinj : Function.Injective residues := by
    intro i j hij
    have heq : times i % 3 = times j % 3 := congrArg Fin.val hij
    have hbij : b (3 - (i.val : ℤ)) = b (3 - (j.val : ℤ)) := by
      rw [← htimes i, ← htimes j, ← hp.iterate_mod_apply (times i),
        ← hp.iterate_mod_apply (times j), heq]
    have hval := hb hbij
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective residues hinj
  norm_num at hcard



















































end DirectedDistances.RandomWalk
