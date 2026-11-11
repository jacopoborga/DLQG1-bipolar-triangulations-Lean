module

public import DirectedDistances.KMSW.WholePlanePastGlueData
public import DirectedDistances.KMSW.M0CutFaceSuccInner

public section
namespace DirectedDistances.KMSW.WholePlaneGlueRotationRunZero

open DirectedDistances.PlanarMap Set WholePlanePastGlueData

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0) (monotone_family_all w0)
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "fp" => seamFun wp hp (past_finiteIncidence W H)
local notation "pos" => gluedPos W h0 hp H
local notation "arc" => gluedArc W h0 hp H




private theorem dart_injective : Function.Injective (wholePlaneDartι W 0) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ heq
  change (wholePlaneEdgeι W 0 e, b) = (wholePlaneEdgeι W 0 f, c) at heq
  have hef := wholePlaneEdgeι_injective W 0 (congrArg Prod.fst heq)
  have hbc := congrArg Prod.snd heq
  cases hef
  cases hbc
  rfl




theorem rot_runZero (d : ℕ × Bool)
    (hd : ∀ j : ℤ, kmswInfRot w0 (H.1 0) d ≠ (boundaryOuterEdge w0 h0 j, false)) :
    wholePlaneRotation W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfRot w0 (H.1 0) d) := by
  let r := kmswInfRot w0 (H.1 0) d
  have hn (j : ℤ) : (r.1, !r.2) ≠ futureMapBoundaryDart w0 h0 j := by
    intro heq
    apply hd j
    have he := congrArg (fun x : ℕ × Bool => (x.1, !x.2)) heq
    simpa only [futureMapBoundaryDart, Bool.not_true, Bool.not_not] using he
  have hc := m0Cut_faceSucc_runZero_of_not_outer W H h0 (r.1, !r.2) hn
  have hf : kmswInfFaceSucc w0 (H.1 0) (r.1, !r.2) = d := by
    change (kmswInfRot w0 (H.1 0)).symm (r.1, !!r.2) = d
    simp only [Bool.not_not]
    exact (kmswInfRot w0 (H.1 0)).symm_apply_apply d
  rw [hf] at hc
  change (wholePlaneRotation W H).symm
    (wholePlaneDartι W 0 (r.1, !!r.2)) = wholePlaneDartι W 0 d at hc
  simp only [Bool.not_not] at hc
  exact ((wholePlaneRotation W H).symm_apply_eq.mp hc).symm




theorem rot_runZero_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ, kmswLimitDartVertex w0 d ≠ boundaryVertex w0 h0 k) :
    wholePlaneRotation W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfRot w0 (H.1 0) d) := by
  apply rot_runZero W h0 H d
  intro k heq
  have hr := (P0).vert_rotation d
  rw [heq] at hr
  apply hv k
  exact hr.symm.trans (boundaryOuterEdge_endpoints w0 h0 k).1

include hp in




theorem star_runZero_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ, kmswLimitDartVertex w0 d ≠ boundaryVertex w0 h0 k) :
    {E | wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W 0 d)} =
    wholePlaneDartι W 0 '' {e | kmswLimitDartVertex w0 e = kmswLimitDartVertex w0 d} := by
  ext E
  change (wholePlaneDartVertex W E =
    wholePlaneDartVertex W (wholePlaneDartι W 0 d)) ↔ _
  constructor
  · intro he
    rcases dart_cover W E with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · refine ⟨e, ?_, rfl⟩
      rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι] at he
      exact wholePlaneVertexι_injective W 0 he
    · rw [pastDart_vertex, wholePlaneDartVertex_ι] at he
      obtain ⟨k, hk⟩ := past_vertex_boundary_of_mem_runZero W hp
        (kmswLimitDartVertex wp e) ⟨_, he.symm⟩
      rw [← hk, seam_vertex W h0 hp] at he
      exact (hv (1 - k) (wholePlaneVertexι_injective W 0 he).symm).elim
  · rintro ⟨e, he, rfl⟩
    rw [wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, he]




theorem rotation_agreement_runZero_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ, kmswLimitDartVertex w0 d ≠ boundaryVertex w0 h0 k) :
    CcwSuccessor {E | wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W 0 d)}
      (fun E => (arc E).initialDirection) (wholePlaneDartι W 0 d)
      (wholePlaneRotation W H (wholePlaneDartι W 0 d)) := by
  rw [rot_runZero_offSeam W h0 H d hv, star_runZero_offSeam W h0 hp d hv]
  have hs := (P0).rotation_agreement d
  rcases hs with ⟨hfin, hd, hr, hcase⟩
  refine ⟨hfin.image _, ⟨d, hd, rfl⟩, ⟨_, hr, rfl⟩, ?_⟩
  rcases hcase with ⟨heq, hsingle⟩ | ⟨hne, hmin⟩
  · left
    refine ⟨congrArg (wholePlaneDartι W 0) heq, ?_⟩
    rw [hsingle, Set.image_singleton]
    rfl
  · right
    refine ⟨fun heq => hne (dart_injective W heq), ?_⟩
    rintro E ⟨e, he, rfl⟩ hne'
    have he' : e ≠ d := fun heq => hne' (congrArg (wholePlaneDartι W 0) heq)
    simpa only [gluedArc_runZero] using hmin e he he'




theorem initial_arg_injective_runZero_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ, kmswLimitDartVertex w0 d ≠ boundaryVertex w0 h0 k) :
    ∀ E, wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W 0 d) →
      Complex.arg (arc E).initialDirection =
        Complex.arg (arc (wholePlaneDartι W 0 d)).initialDirection →
      E = wholePlaneDartι W 0 d := by
  intro E he harg
  have hm : E ∈ {E | wholePlaneDartVertex W E =
      wholePlaneDartVertex W (wholePlaneDartι W 0 d)} := he
  rw [star_runZero_offSeam W h0 hp d hv] at hm
  obtain ⟨e, he', rfl⟩ := hm
  rw [gluedArc_runZero, gluedArc_runZero] at harg
  exact congrArg (wholePlaneDartι W 0) ((P0).initial_arg_injective e d he' harg)

end
end DirectedDistances.KMSW.WholePlaneGlueRotationRunZero
