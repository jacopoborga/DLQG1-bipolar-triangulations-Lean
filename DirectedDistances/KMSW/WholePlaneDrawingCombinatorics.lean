module

public import DirectedDistances.KMSW.KMSWWholePlaneFaces
public import DirectedDistances.KMSW.KMSWWindowEventualCaptureH
public import DirectedDistances.KMSW.LimitRotationVertex
public import DirectedDistances.PlanarMap.PlaneRealization

/-! Helper toward F4c / Theorem 1.4 (whole-plane drawing); not a paper result.
The whole-plane geometric dart incidence, finite stars and rotation compatibility. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward F4c / Theorem 1.4 (whole-plane drawing); not a paper result.
The incident vertex of a geometric dart, with false at the west endpoint and -/
@[expose] def wholePlaneDartVertex (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1

/-- Helper toward F4c / Theorem 1.4 (whole-plane drawing); not a paper result.
The whole-plane PL drawing type, using geometric edges, their reversal, the -/
abbrev WholePlaneDrawing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :=
  PLDrawing (WholePlaneDart W) (WholePlaneVertex W) (wholePlaneDartFlip W)
    (wholePlaneRotation W H) (wholePlaneDartVertex W)

/-- Helper toward F4c / Theorem 1.4 (whole-plane drawing); not a paper result.
Dart incidence agrees with the one-sided endpoint at each colimit inclusion -/
theorem wholePlaneDartVertex_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    wholePlaneDartVertex W (wholePlaneDartι W N d) =
      wholePlaneVertexι W N (kmswLimitDartVertex (shiftedStream W N) d) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp [wholePlaneDartVertex, wholePlaneDartι,
    wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι, kmswLimitDartVertex]

private theorem wholePlaneDartVertex_trans (W : ℤ → Fin 3) (N M : ℕ)
    (hNM : N ≤ M) (d : ℕ × Bool) :
    kmswLimitDartVertex (shiftedStream W M) (wholePlaneDartTrans W N M hNM d) =
      wholePlaneVertexTrans W N M hNM
        (kmswLimitDartVertex (shiftedStream W N) d) := by
  rcases d with ⟨e, b⟩
  cases b with
  | false =>
      change edgeWest (shiftedStream W M)
          (wholePlaneEdgeTrans W N M hNM e) =
        wholePlaneVertexTrans W N M hNM (edgeWest (shiftedStream W N) e)
      exact wholePlaneEdgeTrans_west W N M hNM e
  | true =>
      change edgeEast (shiftedStream W M)
          (wholePlaneEdgeTrans W N M hNM e) =
        wholePlaneVertexTrans W N M hNM (edgeEast (shiftedStream W N) e)
      exact wholePlaneEdgeTrans_east W N M hNM e

/-- Helper toward F4c / Theorem 1.4 (whole-plane drawing); not a paper result.
Every whole-plane vertex has finitely many incident geometric darts, including -/
theorem wholePlaneStar_finite (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) :
    {d : WholePlaneDart W | wholePlaneDartVertex W d = v}.Finite := by
  classical
  let S : Set (WholePlaneEdge W) := {e |
    wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v}
  have hS : S.Finite := wholePlane_incidentEdges_finite W H v
  have hfinite :
      (S.image (fun e => (e, false)) ∪ S.image (fun e => (e, true))).Finite :=
    (hS.image (fun e => (e, false))).union (hS.image (fun e => (e, true)))
  apply hfinite.subset
  rintro ⟨e, b⟩ hd
  change (if b then wholePlaneEdgeEast W e else wholePlaneEdgeWest W e) = v at hd
  cases b with
  | false =>
      apply Set.mem_union_left
      exact ⟨e, Or.inl hd, rfl⟩
  | true =>
      apply Set.mem_union_right
      exact ⟨e, Or.inr hd, rfl⟩

/-- Helper toward F4c / Theorem 1.4 (whole-plane drawing); not a paper result.
Whole-plane rotation preserves the incident vertex of every geometric dart -/
theorem wholePlaneRotation_preserves_dartVertex (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : WholePlaneDart W) :
    wholePlaneDartVertex W (wholePlaneRotation W H d) = wholePlaneDartVertex W d := by
  classical
  rcases d with ⟨q, b⟩
  obtain ⟨⟨N, e⟩, rfl⟩ := Quotient.exists_rep q
  let d₀ : ℕ × Bool := (e, b)
  obtain ⟨M, hNM, hf⟩ := H.2 N (kmswLimitDartVertex (shiftedStream W N) d₀)
  let dM := wholePlaneDartTrans W N M hNM d₀
  have hbase : kmswLimitDartVertex (shiftedStream W M) dM =
      wholePlaneVertexTrans W N M hNM
        (kmswLimitDartVertex (shiftedStream W N) d₀) := by
    simpa [dM] using wholePlaneDartVertex_trans W N M hNM d₀
  have hf' : ∀ L (hML : M ≤ L), wholePlaneFresh W M L hML
      (kmswLimitDartVertex (shiftedStream W M) dM) := by
    intro L hML
    rw [hbase]
    exact hf L hML
  have hι : wholePlaneDartι W M dM = wholePlaneDartι W N d₀ :=
    congrFun (wholePlaneDartι_trans W N M hNM) d₀
  have hrot : wholePlaneRotation W H (wholePlaneDartι W N d₀) =
      wholePlaneDartι W M
        (kmswInfRot (shiftedStream W M) (H.1 M) dM) := by
    rw [← hι]
    exact wholePlaneRotation_ι_of_fresh W H M dM hf'
  change wholePlaneDartVertex W
    (wholePlaneRotation W H (wholePlaneDartι W N d₀)) =
      wholePlaneDartVertex W (wholePlaneDartι W N d₀)
  calc
    wholePlaneDartVertex W
        (wholePlaneRotation W H (wholePlaneDartι W N d₀)) =
        wholePlaneVertexι W M
          (kmswLimitDartVertex (shiftedStream W M)
            (kmswInfRot (shiftedStream W M) (H.1 M) dM)) := by
      rw [hrot, wholePlaneDartVertex_ι]
    _ = wholePlaneVertexι W M (kmswLimitDartVertex (shiftedStream W M) dM) := by
      rw [kmswLimitDartVertex_rot (shiftedStream W M) (H.1 M) dM]
    _ = wholePlaneVertexι W N (kmswLimitDartVertex (shiftedStream W N) d₀) := by
      rw [wholePlaneDartVertex_trans]
      exact congrFun (wholePlaneVertexι_trans W N M hNM)
        (kmswLimitDartVertex (shiftedStream W N) d₀)
    _ = wholePlaneDartVertex W (wholePlaneDartι W N d₀) := by
      rw [wholePlaneDartVertex_ι]

end DirectedDistances.KMSW
