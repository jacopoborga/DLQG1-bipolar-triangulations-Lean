module

public import DirectedDistances.KMSW.PastSeamMatch
public import DirectedDistances.KMSW.M0CutFaceSuccInner

import all DirectedDistances.KMSW.M0CutFaceSuccInner
import all DirectedDistances.KMSW.StageReversalRotation

/-! Supporting lemmas for paper labels `thm-busemann` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW




private theorem pastFace_stage_triangle (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (x : StageDart (kmswStage w n).nextEdge)
    (hx : reversalDartVal x ∈ stageTriangleDartList w j) :
    reversalDartVal ((kmswMap w n).faceSucc x) =
      (stageTriangleDartList w j).formPerm (reversalDartVal x) := by
  classical
  have hxm : x ∈ reversalTriangleWord w n j hj := by
    rw [← reversalTriangleWord_val w n j hj] at hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
    exact (reversalDartVal_injective _ hyx) ▸ hy
  have hmap := reversal_formPerm_map reversalDartVal (reversalDartVal_injective _)
    (reversalTriangleWord w n j hj) (reversalTriangleWord_nodup w n j hj) x hxm
  rw [reversalTriangleWord_val] at hmap
  rw [reversalTriangleWord_faceSucc w n j hj x hxm]
  exact hmap.symm




private theorem pastFace_inf_triangle (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : d ∈ stageTriangleDartList w j) :
    kmswInfFaceSucc w hfin d = (stageTriangleDartList w j).formPerm d := by
  classical
  obtain ⟨a, ha⟩ := kmswInfFaceSucc_eventually_eq_stage w hfin d
  let n := max a (j.val + 1)
  obtain ⟨hb, heq⟩ := ha n (Nat.le_max_left _ _)
  rw [heq]
  exact pastFace_stage_triangle w n j (by dsimp only [n]; omega) (⟨d.1, hb⟩, d.2) hd




private theorem pastFace_inf_eq_stage (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (n : ℕ) (j : TriangleCreationTime w) (hj : j.val < n)
    (x : StageDart (kmswStage w n).nextEdge)
    (hx : reversalDartVal x ∈ stageTriangleDartList w j) :
    kmswInfFaceSucc w hfin (reversalDartVal x) =
      reversalDartVal ((kmswMap w n).faceSucc x) := by
  classical
  rw [pastFace_inf_triangle w hfin j _ hx]
  exact (pastFace_stage_triangle w n j hj x hx).symm




theorem wholePlaneFaceSucc_run_of_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (shiftedStream W N),
      d ∈ stageTriangleDartList (shiftedStream W N) j) :
    wholePlaneFaceSucc W H (wholePlaneDartι W N d) =
      wholePlaneDartι W N (kmswInfFaceSucc (shiftedStream W N) (H.1 N) d) := by
  obtain ⟨M, hNM, hpow⟩ :=
    wholePlaneRotation_symm_pow_at_common_run W H N (d.1, !d.2)
  have hc := hpow 1
  simp only [pow_one] at hc
  change wholePlaneFaceSucc W H (wholePlaneDartι W N d) =
    wholePlaneDartι W M (kmswInfFaceSucc (shiftedStream W M) (H.1 M)
      (wholePlaneDartTrans W N M hNM d)) at hc
  have hu : KMSWFiniteIncidence (fun i => shiftedStream W M (M - N + i)) := by
    rw [shiftedStream_shift W N M hNM]
    exact H.1 N
  have ht : ∃ j : TriangleCreationTime (fun i => shiftedStream W M (M - N + i)),
      d ∈ stageTriangleDartList (fun i => shiftedStream W M (M - N + i)) j := by
    rw [shiftedStream_shift W N M hNM]
    exact hd
  have htrans : wholePlaneDartTrans W N M hNM
      (kmswInfFaceSucc (shiftedStream W N) (H.1 N) d) =
      kmswInfFaceSucc (shiftedStream W M) (H.1 M)
        (wholePlaneDartTrans W N M hNM d) := by
    simpa only [wholePlaneDartTrans, wholePlaneEdgeTrans,
      shiftedStream_shift W N M hNM] using
      m0Cut_window_faceSucc_of_triangle (shiftedStream W M) (M - N) hu (H.1 M) d ht
  rw [hc, ← htrans]
  exact congrFun (wholePlaneDartι_trans W N M hNM) _




theorem kmswPastDart_faceSucc_of_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hfin' : KMSWFiniteIncidence (kmswPastCode W)) (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (kmswPastCode W),
      d ∈ stageTriangleDartList (kmswPastCode W) j) :
    wholePlaneFaceSucc W H (kmswPastDart W d) =
      kmswPastDart W (kmswInfFaceSucc (kmswPastCode W) hfin' d) := by
  obtain ⟨j, hdj⟩ := hd
  let N := j.val + 1
  have hjN : j.val < N := Nat.lt_succ_self _
  have hb := stageTriangleDartList_lt (kmswPastCode W) N j hjN d hdj
  let x : StageDart (kmswStage (kmswPastCode W) N).nextEdge := (⟨d.1, hb⟩, d.2)
  let y := kmswRevDart (shiftedStream W N) (kmswPastCode W) N
    (kmswPastCode_rev W N) x
  obtain ⟨k, hk, hword⟩ := kmswRevDart_triangle_words (shiftedStream W N)
    (kmswPastCode W) N (kmswPastCode_rev W N) j hjN
  have hy : reversalDartVal y ∈ stageTriangleDartList (shiftedStream W N) k := by
    apply hword.mem_iff.mp
    exact List.mem_map.mpr ⟨d, hdj, rfl⟩
  have hkN : k.val < N := by omega
  have hsrc := pastFace_inf_eq_stage (kmswPastCode W) hfin' N j hjN x hdj
  have htgt := pastFace_inf_eq_stage (shiftedStream W N) (H.1 N) N k hkN y hy
  have hface := kmswRevDart_faceSucc (shiftedStream W N) (kmswPastCode W) N
    (kmswPastCode_rev W N) x
  have hinput : kmswPastDart W d = wholePlaneDartι W N (reversalDartVal y) :=
    kmswPastDart_eq_stage W N d hb
  rw [hinput, wholePlaneFaceSucc_run_of_triangle W H N _ ⟨k, hy⟩, htgt]
  change wholePlaneDartι W N (reversalDartVal ((kmswMap _ N).faceSucc y)) = _
  rw [← hface]
  rw [show kmswInfFaceSucc (kmswPastCode W) hfin' d =
    reversalDartVal ((kmswMap (kmswPastCode W) N).faceSucc x) from hsrc]
  exact (kmswPastDart_eq_stage W N
    (reversalDartVal ((kmswMap (kmswPastCode W) N).faceSucc x))
    ((kmswMap (kmswPastCode W) N).faceSucc x).1.isLt).symm




theorem kmswPastDart_faceSucc_of_not_outer (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hfin' : KMSWFiniteIncidence (kmswPastCode W))
    (h' : BoundaryHitWitnesses (kmswPastCode W)) (d : ℕ × Bool)
    (hd : ∀ k : ℤ, d ≠ futureMapBoundaryDart (kmswPastCode W) h' k) :
    wholePlaneFaceSucc W H (kmswPastDart W d) =
      kmswPastDart W (kmswInfFaceSucc (kmswPastCode W) hfin' d) := by
  exact kmswPastDart_faceSucc_of_triangle W H hfin' d
    (m0Cut_triangle_of_not_outer (kmswPastCode W) h' d hd)




private theorem pastFace_west_triangle (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (e : ℕ) : ∃ j : TriangleCreationTime w, (e, false) ∈ stageTriangleDartList w j := by
  apply m0Cut_triangle_of_not_outer w h (e, false)
  intro k heq
  have hb := congrArg Prod.snd heq
  change false = true at hb
  cases hb





theorem kmswPastDart_outer_splice (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h' : BoundaryHitWitnesses (kmswPastCode W))
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) :
    kmswPastDart W (futureMapBoundaryDart (kmswPastCode W) h' k) =
        wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 (-k), false) ∧
      (∃ j : TriangleCreationTime (shiftedStream W 0),
        (boundaryOuterEdge (shiftedStream W 0) h0 (-k), false) ∈
          stageTriangleDartList (shiftedStream W 0) j) ∧
      wholePlaneFaceSucc W H
          (kmswPastDart W (futureMapBoundaryDart (kmswPastCode W) h' k)) =
        wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0)
          (boundaryOuterEdge (shiftedStream W 0) h0 (-k), false)) := by
  have he := congrArg Prod.fst (kmswPastDart_seam_match_neg W h0 h' k)
  have heq : kmswPastDart W (futureMapBoundaryDart (kmswPastCode W) h' k) =
      wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 (-k), false) := by
    change (kmswPastEdge W _, false) = (wholePlaneEdgeι W 0 _, false)
    exact Prod.ext he rfl
  have ht := pastFace_west_triangle (shiftedStream W 0) h0
    (boundaryOuterEdge (shiftedStream W 0) h0 (-k))
  refine ⟨heq, ht, ?_⟩
  rw [heq]
  exact m0Cut_faceSucc_runZero_of_triangle W H _ ht





theorem wholePlaneDart_runZero_outer_splice (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hfin' : KMSWFiniteIncidence (kmswPastCode W))
    (h' : BoundaryHitWitnesses (kmswPastCode W))
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) :
    wholePlaneDartι W 0 (futureMapBoundaryDart (shiftedStream W 0) h0 k) =
        kmswPastDart W (boundaryOuterEdge (kmswPastCode W) h' (-k), false) ∧
      (∃ j : TriangleCreationTime (kmswPastCode W),
        (boundaryOuterEdge (kmswPastCode W) h' (-k), false) ∈
          stageTriangleDartList (kmswPastCode W) j) ∧
      wholePlaneFaceSucc W H
          (wholePlaneDartι W 0 (futureMapBoundaryDart (shiftedStream W 0) h0 k)) =
        kmswPastDart W (kmswInfFaceSucc (kmswPastCode W) hfin'
          (boundaryOuterEdge (kmswPastCode W) h' (-k), false)) := by
  have heq : wholePlaneDartι W 0
      (futureMapBoundaryDart (shiftedStream W 0) h0 k) =
      kmswPastDart W (boundaryOuterEdge (kmswPastCode W) h' (-k), false) := by
    change (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 k), true) = _
    have he := congrArg Prod.fst (kmswPastDart_seam_match_neg W h0 h' (-k))
    rw [neg_neg] at he
    exact Prod.ext he.symm rfl
  have ht := pastFace_west_triangle (kmswPastCode W) h'
    (boundaryOuterEdge (kmswPastCode W) h' (-k))
  refine ⟨heq, ht, ?_⟩
  rw [heq]
  exact kmswPastDart_faceSucc_of_triangle W H hfin' _ ht





theorem wholePlaneFaceSucc_runZero_or_past (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hfin' : KMSWFiniteIncidence (kmswPastCode W))
    (h' : BoundaryHitWitnesses (kmswPastCode W))
    (h0 : BoundaryHitWitnesses (shiftedStream W 0)) (D : WholePlaneDart W) :
    (∃ d : ℕ × Bool, D = wholePlaneDartι W 0 d ∧
      (∃ j : TriangleCreationTime (shiftedStream W 0),
        d ∈ stageTriangleDartList (shiftedStream W 0) j) ∧
      wholePlaneFaceSucc W H D =
        wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d)) ∨
    (∃ d : ℕ × Bool, D = kmswPastDart W d ∧
      (∃ j : TriangleCreationTime (kmswPastCode W),
        d ∈ stageTriangleDartList (kmswPastCode W) j) ∧
      wholePlaneFaceSucc W H D =
        kmswPastDart W (kmswInfFaceSucc (kmswPastCode W) hfin' d)) := by
  classical
  rcases D with ⟨E, b⟩
  rcases kmswPastEdge_cover W E with ⟨e, he⟩ | ⟨e, he⟩
  · subst E
    let d : ℕ × Bool := (e, !b)
    have hrep : (kmswPastEdge W e, b) = kmswPastDart W d := by
      change (_, b) = (_, !(!b))
      rw [Bool.not_not]
    rw [hrep]
    by_cases ho : ∃ k : ℤ, d = futureMapBoundaryDart (kmswPastCode W) h' k
    · obtain ⟨k, hk⟩ := ho
      rw [hk]
      obtain ⟨heq, ht, hf⟩ := kmswPastDart_outer_splice W H h' h0 k
      exact Or.inl ⟨_, heq, ht, hf⟩
    · have ht := m0Cut_triangle_of_not_outer (kmswPastCode W) h' d
        (fun k hk => ho ⟨k, hk⟩)
      exact Or.inr ⟨d, rfl, ht, kmswPastDart_faceSucc_of_triangle W H hfin' d ht⟩
  · subst E
    by_cases ho : ∃ k : ℤ, (e, b) = futureMapBoundaryDart (shiftedStream W 0) h0 k
    · obtain ⟨k, hk⟩ := ho
      obtain ⟨heq, ht, hf⟩ := wholePlaneDart_runZero_outer_splice W H hfin' h' h0 k
      rw [← hk] at heq hf
      exact Or.inr ⟨_, heq, ht, hf⟩
    · have ht := m0Cut_triangle_of_not_outer (shiftedStream W 0) h0 (e, b)
        (fun k hk => ho ⟨k, hk⟩)
      exact Or.inl ⟨(e, b), rfl, ht, m0Cut_faceSucc_runZero_of_triangle W H (e, b) ht⟩

end DirectedDistances.KMSW
