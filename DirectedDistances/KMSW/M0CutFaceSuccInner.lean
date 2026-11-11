module

public import DirectedDistances.KMSW.M0CutFaceSuccTransport
public import DirectedDistances.KMSW.WholePlaneCofinalFreshness
import DirectedDistances.KMSW.WholePlaneRightBoundaryRot
import DirectedDistances.KMSW.KMSWWindowPatchRotation
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.KMSW.RunBoundaryStackSets

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The opposite endpoint's non-record condition gives face-successor transport.
This helper does not establish the geometric cut identification. -/
theorem m0Cut_faceSucc_runZero_of_nonrecord (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : ℕ × Bool)
    (hd : KMSWNonrecordVertex (shiftedStream W 0)
      (if !d.2 then edgeEast (shiftedStream W 0) d.1
        else edgeWest (shiftedStream W 0) d.1)) :
    wholePlaneFaceSucc W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) := by
  apply m0Cut_faceSucc_runZero_of_fresh W H d
  intro M h0M
  exact wholePlaneFresh_of_nonrecord W 0 M h0M _ hd

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Recorded triangle faces commute with the infinite window edge map, even at
vertices which are not fresh. -/
private theorem m0Cut_window_faceSucc_of_triangle (w : ℕ → Fin 3) (s : ℕ)
    (hu : KMSWFiniteIncidence (fun i => w (s + i))) (hw : KMSWFiniteIncidence w)
    (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (fun i => w (s + i)),
      d ∈ stageTriangleDartList (fun i => w (s + i)) j) :
    (kmswWindowEdgeMapInf w s
        (kmswInfFaceSucc (fun i => w (s + i)) hu d).1,
      (kmswInfFaceSucc (fun i => w (s + i)) hu d).2) =
      kmswInfFaceSucc w hw (kmswWindowEdgeMapInf w s d.1, d.2) := by
  let u := fun i => w (s + i)
  obtain ⟨j, hdj⟩ := hd
  obtain ⟨a, ha⟩ := kmswInfFaceSucc_eventually_eq_stage u hu d
  obtain ⟨b, hb⟩ := kmswInfFaceSucc_eventually_eq_stage w hw
    (kmswWindowEdgeMapInf w s d.1, d.2)
  let m := max (max a b) (j.val + 1)
  obtain ⟨hedge, hsrc⟩ := ha m (by dsimp only [m]; omega)
  obtain ⟨himage, htgt⟩ := hb (s + m) (by dsimp only [m]; omega)
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, hedge⟩, d.2)
  have hx : (x.1.val, x.2) ∈ stageTriangleDartsVal u m := by
    apply List.mem_flatMap.mpr
    exact ⟨j, (mem_stageTriangleTimes u m j).mpr (by dsimp only [m]; omega), hdj⟩
  have hface := kmswWindowDartMap_faceSucc w s m x hx
  have hmap : kmswWindowDartMap w s m x =
      (⟨kmswWindowEdgeMapInf w s d.1, himage⟩, d.2) := by
    apply Prod.ext
    · apply Fin.ext
      exact (kmswWindowEdgeMapInf_eq_stage w s m d.1 hedge).symm
    · rfl
  rw [hsrc]
  have hout := kmswWindowEdgeMapInf_eq_stage w s m
    ((kmswMap u m).faceSucc x).1.val ((kmswMap u m).faceSucc x).1.isLt
  change (kmswWindowEdgeMapInf w s ((kmswMap u m).faceSucc x).1.val,
    ((kmswMap u m).faceSucc x).2) = _
  rw [hout]
  change ((kmswWindowDartMap w s m ((kmswMap u m).faceSucc x)).1.val,
    (kmswWindowDartMap w s m ((kmswMap u m).faceSucc x)).2) = _
  rw [← hface, hmap]
  exact htgt.symm

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The labelled outer darts exhaust all darts not lying on recorded triangles. -/
private theorem m0Cut_triangle_of_not_outer (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hd : ∀ k : ℤ, d ≠ futureMapBoundaryDart w h k) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  have hL : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩
  by_contra ht
  rcases (kmswRunInfDart_boundary_iff_not_triangle w hL hR d).mpr ht with
    ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · have hrange : e ∈ Set.range (fun j : ℕ =>
        kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
      rw [← kmswRunEventuallyLL_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    dsimp only at hj
    apply hd (-((j : ℤ) + 1))
    rw [futureMapBoundaryDart, boundaryOuterEdge_of_negative w h (by omega), hj]
  · have hrange : e ∈ Set.range (fun j : ℕ => kmswRightBoundaryEdge w j) := by
      rw [← kmswRunEventuallyLR_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    dsimp only at hj
    by_cases hj0 : j = 0
    · subst j
      apply hd 0
      rw [futureMapBoundaryDart_zero, ← hj, kmswRightBoundaryEdge_zero]
      rfl
    · apply hd (j : ℤ)
      rw [futureMapBoundaryDart, boundaryOuterEdge_of_positive w h (by omega),
        Int.toNat_natCast, hj]

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
A run-zero triangle's face successor is preserved in the colimit, including
at record boundary vertices. This does not identify complementary plane faces. -/
theorem m0Cut_faceSucc_runZero_of_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (shiftedStream W 0),
      d ∈ stageTriangleDartList (shiftedStream W 0) j) :
    wholePlaneFaceSucc W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) := by
  obtain ⟨M, h0M, hpow⟩ :=
    wholePlaneRotation_symm_pow_at_common_run W H 0 (d.1, !d.2)
  have hc := hpow 1
  simp only [pow_one] at hc
  change wholePlaneFaceSucc W H (wholePlaneDartι W 0 d) =
    wholePlaneDartι W M (kmswInfFaceSucc (shiftedStream W M) (H.1 M)
      (wholePlaneDartTrans W 0 M h0M d)) at hc
  have hu : KMSWFiniteIncidence (fun i => shiftedStream W M (M - 0 + i)) := by
    rw [shiftedStream_shift W 0 M h0M]
    exact H.1 0
  have ht : ∃ j : TriangleCreationTime (fun i => shiftedStream W M (M - 0 + i)),
      d ∈ stageTriangleDartList (fun i => shiftedStream W M (M - 0 + i)) j := by
    rw [shiftedStream_shift W 0 M h0M]
    exact hd
  have htrans : wholePlaneDartTrans W 0 M h0M
      (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) =
      kmswInfFaceSucc (shiftedStream W M) (H.1 M)
        (wholePlaneDartTrans W 0 M h0M d) := by
    simpa only [wholePlaneDartTrans, wholePlaneEdgeTrans,
      shiftedStream_shift W 0 M h0M] using
      m0Cut_window_faceSucc_of_triangle (shiftedStream W M) (M - 0) hu (H.1 M) d ht
  rw [hc, ← htrans]
  exact congrFun (wholePlaneDartι_trans W 0 M h0M) _

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Every run-zero dart off the labelled outer face retains its face successor in
the two-sided colimit. No freshness or colimit-presence premise is added.
The geometric cut and complementary-face identification remain separate. -/
theorem m0Cut_faceSucc_runZero_of_not_outer (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (d : ℕ × Bool)
    (hd : ∀ k : ℤ, d ≠ futureMapBoundaryDart (shiftedStream W 0) h k) :
    wholePlaneFaceSucc W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) := by
  exact m0Cut_faceSucc_runZero_of_triangle W H d
    (m0Cut_triangle_of_not_outer (shiftedStream W 0) h d hd)

end DirectedDistances.KMSW
