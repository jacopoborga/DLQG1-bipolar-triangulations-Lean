module

public import DirectedDistances.KMSW.WholePlanePastGlueGeometry
public import DirectedDistances.KMSW.PastFaceSucc

public section
namespace DirectedDistances.KMSW.WholePlaneGlueRotationPast

open DirectedDistances.PlanarMap Set WholePlanePastGlueData

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0)
  (monotone_family_all w0)
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "fp" => seamFun wp hp (past_finiteIncidence W H)
local notation "pos" => gluedPos W h0 hp H
local notation "arc" => gluedArc W h0 hp H

include h0 hp H

omit h0 in



theorem rot_past (d : ℕ × Bool)
    (hd : ∀ j : ℤ,
      kmswInfRot wp (past_finiteIncidence W H) d ≠
        (boundaryOuterEdge wp hp j, false)) :
    wholePlaneRotation W H (kmswPastDart W d) =
      kmswPastDart W (kmswInfRot wp (past_finiteIncidence W H) d) := by
  let r := kmswInfRot wp (past_finiteIncidence W H) d
  let x : ℕ × Bool := (r.1, !r.2)
  have hnot : ∀ k : ℤ, x ≠ futureMapBoundaryDart wp hp k := by
    intro k he
    cases hb : r.2
    · have hf := congrArg Prod.fst he
      exact hd k (Prod.ext (by
        simpa [x, r, futureMapBoundaryDart] using hf) (by simpa [r] using hb))
    · have hf := congrArg Prod.snd he
      simp [x, futureMapBoundaryDart, hb] at hf
  have hface := kmswPastDart_faceSucc_of_not_outer W H
    (past_finiteIncidence W H) hp x hnot
  have hface' : wholePlaneFaceSucc W H (kmswPastDart W x) =
      kmswPastDart W d := by
    simpa [x, r, kmswInfFaceSucc] using hface
  have hrot : wholePlaneDartFlip W (kmswPastDart W x) =
      wholePlaneRotation W H (kmswPastDart W d) := by
    simpa [wholePlaneFaceSucc] using
      congrArg (wholePlaneRotation W H) hface'
  rw [pastDart_flip] at hrot
  simpa [x, r] using hrot.symm

omit h0 in



theorem rot_past_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ,
      kmswLimitDartVertex wp d ≠ boundaryVertex wp hp k) :
    wholePlaneRotation W H (kmswPastDart W d) =
      kmswPastDart W (kmswInfRot wp (past_finiteIncidence W H) d) := by
  apply rot_past W hp H d
  intro k he
  have hrot := kmswLimitDartVertex_rot wp (past_finiteIncidence W H) d
  rw [he] at hrot
  change edgeWest wp (boundaryOuterEdge wp hp k) =
    kmswLimitDartVertex wp d at hrot
  rw [(boundaryOuterEdge_endpoints wp hp k).1] at hrot
  exact (hv k) hrot.symm

omit h0 H in



theorem star_past_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ,
      kmswLimitDartVertex wp d ≠ boundaryVertex wp hp k) :
    {E : WholePlaneDart W |
      wholePlaneDartVertex W E = wholePlaneDartVertex W (kmswPastDart W d)} =
    kmswPastDart W ''
      {e : ℕ × Bool | kmswLimitDartVertex wp e = kmswLimitDartVertex wp d} := by
  classical
  ext D
  constructor
  · intro hD
    change wholePlaneDartVertex W D =
      wholePlaneDartVertex W (kmswPastDart W d) at hD
    rcases dart_cover W D with hrun | hpast
    · obtain ⟨e, rfl⟩ := hrun
      rw [wholePlaneDartVertex_ι, pastDart_vertex] at hD
      have hrun : kmswPastVertex W (kmswLimitDartVertex wp d) ∈
          range (wholePlaneVertexι W 0) := ⟨_, hD⟩
      obtain ⟨k, hk⟩ := past_vertex_boundary_of_mem_runZero W hp _ hrun
      exact ((hv k) hk.symm).elim
    · obtain ⟨e, rfl⟩ := hpast
      rw [pastDart_vertex, pastDart_vertex] at hD
      have he := kmswPastVertex_injective W hD
      exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    change wholePlaneDartVertex W (kmswPastDart W e) =
      wholePlaneDartVertex W (kmswPastDart W d)
    rw [pastDart_vertex, pastDart_vertex, he]

omit h0 H in



theorem notSeam_of_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ,
      kmswLimitDartVertex wp d ≠ boundaryVertex wp hp k)
    (e : ℕ × Bool)
    (he : kmswLimitDartVertex wp e = kmswLimitDartVertex wp d) :
    ¬ kmswPastSeamEdge W e.1 := by
  intro hs
  obtain ⟨N, hmem⟩ := hs
  have hbound : e.1 < (kmswStage wp N).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge wp N).2
    simp only [List.mem_append]
    rcases List.mem_append.mp hmem with hLL | hLR
    · exact Or.inl (Or.inr hLL)
    · exact Or.inr hLR
  have hends := edge_endpoints_eq wp hbound
  have hend : (kmswStage wp N).west e.1 = kmswLimitDartVertex wp e ∨
      (kmswStage wp N).east e.1 = kmswLimitDartVertex wp e := by
    cases hb : e.2
    · left
      simpa [kmswLimitDartVertex, hb] using hends.1
    · right
      simpa [kmswLimitDartVertex, hb] using hends.2
  obtain ⟨k, hk⟩ := stageLLLRVertex_eq_boundaryVertex wp hp _
    ⟨N, e.1, by
      rcases List.mem_append.mp hmem with hLL | hLR
      · exact Or.inl hLL
      · exact Or.inr hLR, hend⟩
  exact (hv k) ((hk.trans he).symm)

end
end DirectedDistances.KMSW.WholePlaneGlueRotationPast
