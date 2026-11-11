module

public import DirectedDistances.KMSW.WholePlaneGlueRotationPast

public section
namespace DirectedDistances.KMSW.WholePlaneGlueRotationPastAgree

open DirectedDistances.PlanarMap Set WholePlanePastGlueData WholePlaneGlueRotationPast

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




theorem rotation_agreement_past_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ, kmswLimitDartVertex wp d ≠ boundaryVertex wp hp k) :
    CcwSuccessor {E | wholePlaneDartVertex W E =
      wholePlaneDartVertex W (kmswPastDart W d)}
      (fun E => (arc E).initialDirection) (kmswPastDart W d)
      (wholePlaneRotation W H (kmswPastDart W d)) := by
  rw [rot_past_offSeam W hp H d hv, star_past_offSeam W hp d hv]
  have hs := (Pt).rotation_agreement d
  rcases hs with ⟨hfin, hd, hr, hcase⟩
  refine ⟨hfin.image _, ⟨d, hd, rfl⟩, ⟨_, hr, rfl⟩, ?_⟩
  rcases hcase with ⟨heq, hsingle⟩ | ⟨hne, hmin⟩
  · left
    refine ⟨congrArg (kmswPastDart W) heq, ?_⟩
    rw [hsingle, Set.image_singleton]
  · right
    refine ⟨fun heq => hne (kmswPastDart_injective W heq), ?_⟩
    rintro E ⟨e, he, rfl⟩ hne'
    have he' : e ≠ d := fun heq => hne' (congrArg (kmswPastDart W) heq)
    simpa only [gluedArc_past W h0 hp H d (notSeam_of_offSeam W hp d hv d hd),
      gluedArc_past W h0 hp H _ (notSeam_of_offSeam W hp d hv _ hr),
      gluedArc_past W h0 hp H e (notSeam_of_offSeam W hp d hv e he)] using hmin e he he'




theorem initial_arg_injective_past_offSeam (d : ℕ × Bool)
    (hv : ∀ k : ℤ, kmswLimitDartVertex wp d ≠ boundaryVertex wp hp k) :
    ∀ E, wholePlaneDartVertex W E =
      wholePlaneDartVertex W (kmswPastDart W d) →
      Complex.arg (arc E).initialDirection =
        Complex.arg (arc (kmswPastDart W d)).initialDirection →
      E = kmswPastDart W d := by
  intro E he harg
  have hm : E ∈ {E | wholePlaneDartVertex W E =
      wholePlaneDartVertex W (kmswPastDart W d)} := he
  rw [star_past_offSeam W hp d hv] at hm
  obtain ⟨e, he', rfl⟩ := hm
  rw [gluedArc_past W h0 hp H e (notSeam_of_offSeam W hp d hv e he'),
    gluedArc_past W h0 hp H d (notSeam_of_offSeam W hp d hv d rfl)] at harg
  exact congrArg (kmswPastDart W) ((Pt).initial_arg_injective e d he' harg)

end
end DirectedDistances.KMSW.WholePlaneGlueRotationPastAgree
