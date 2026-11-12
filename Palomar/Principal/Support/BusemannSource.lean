/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DirectedDistances.Paper.Section1.BusemannM0

/-! EXPERIMENTAL Solution transport. Existing public source exports are imported.
The three previously private well-definedness proofs and their literal helper
definitions below are copied from the accepted implementation, with stable
public names for the compared auxiliary targets. No target assumption is added.
Not compiled or compared yet; excluded from the approved preparation tree. -/
public section
namespace DirectedDistances.KMSW
@[expose] noncomputable def runRot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) :
    Equiv.Perm (ℕ × Bool) :=
  if inv then (kmswInfRot (shiftedStream W N) (H.1 N)).symm
  else kmswInfRot (shiftedStream W N) (H.1 N)

@[expose] def eventualValue (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool) (y : WholePlaneDart W) : Prop :=
  ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
    wholePlaneDartι W M' (runRot W H inv M'
      (wholePlaneDartTrans W N M' (hNM.trans hMM') d)) = y

private theorem eventualValue_unique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool)
    (y z : WholePlaneDart W) (hy : eventualValue W H inv N d y)
    (hz : eventualValue W H inv N d z) : y = z := by
  obtain ⟨M, hNM, hy⟩ := hy
  obtain ⟨L, hNL, hz⟩ := hz
  exact (hy (max M L) (Nat.le_max_left M L)).symm.trans
    (hz (max M L) (Nat.le_max_right M L))

private def base (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast (shiftedStream W N) d.1 else edgeWest (shiftedStream W N) d.1

private theorem trans_base (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M)
    (d : ℕ × Bool) :
    base W M (wholePlaneDartTrans W N M h d) =
      wholePlaneVertexTrans W N M h (base W N d) := by
  cases hb : d.2 <;> simp only [base, wholePlaneDartTrans, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeTrans_west W N M h d.1
  · exact wholePlaneEdgeTrans_east W N M h d.1

private theorem runRot_trans (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N M : ℕ) (h : N ≤ M) (d : ℕ × Bool)
    (hf : wholePlaneFresh W N M h (base W N d)) :
    wholePlaneDartTrans W N M h (runRot W H inv N d) =
      runRot W H inv M (wholePlaneDartTrans W N M h d) := by
  cases inv
  · exact wholePlaneInfRot_trans_of_fresh W N M h (H.1 N) (H.1 M) _ hf d rfl
  · exact wholePlaneInfRot_symm_trans_of_fresh W N M h (H.1 N) (H.1 M) _ hf d rfl

theorem eventualValue_existsUnique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    ∃! y, eventualValue W H inv N d y := by
  obtain ⟨M, hNM, hf⟩ := H.2 N (base W N d)
  let e := wholePlaneDartTrans W N M hNM d
  have hy : eventualValue W H inv N d
      (wholePlaneDartι W M (runRot W H inv M e)) := by
    refine ⟨M, hNM, fun L hML => ?_⟩
    have hr := runRot_trans W H inv M L hML e (by
      change wholePlaneFresh W M L hML
        (base W M (wholePlaneDartTrans W N M hNM d))
      rw [trans_base]
      exact hf L hML)
    have hc := congrFun (wholePlaneDartTrans_comp W N M L hNM hML) d
    change wholePlaneDartTrans W M L hML e =
      wholePlaneDartTrans W N L (hNM.trans hML) d at hc
    rw [← hc, ← hr]
    exact congrFun (wholePlaneDartι_trans W M L hML) (runRot W H inv M e)
  exact ⟨_, hy, fun z hz => eventualValue_unique W H inv N d _ _ hz hy⟩

@[expose] noncomputable def value (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    WholePlaneDart W :=
  (eventualValue_existsUnique W H inv N d).exists.choose

private theorem value_spec (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    eventualValue W H inv N d (value W H inv N d) :=
  (eventualValue_existsUnique W H inv N d).exists.choose_spec

private theorem eventualValue_trans (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N M : ℕ) (h : N ≤ M)
    (d : ℕ × Bool) (y : WholePlaneDart W)
    (hy : eventualValue W H inv M (wholePlaneDartTrans W N M h d) y) :
    eventualValue W H inv N d y := by
  obtain ⟨L, hML, hy⟩ := hy
  refine ⟨L, h.trans hML, fun K hLK => ?_⟩
  rw [← congrFun (wholePlaneDartTrans_comp W N M K h (hML.trans hLK)) d]
  exact hy K hLK

private theorem value_trans (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N M : ℕ) (h : N ≤ M) (d : ℕ × Bool) :
    value W H inv M (wholePlaneDartTrans W N M h d) = value W H inv N d :=
  eventualValue_unique W H inv N d _ _
    (eventualValue_trans W H inv N M h d _ (value_spec W H inv M _))
    (value_spec W H inv N d)

theorem value_rel (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) (s : Bool) :
    value W H inv a.1 (a.2, s) = value W H inv b.1 (b.2, s) := by
  obtain ⟨M, ha, hb, he⟩ := hab
  calc
    value W H inv a.1 (a.2, s) =
        value W H inv M (wholePlaneDartTrans W a.1 M ha (a.2, s)) :=
      (value_trans W H inv a.1 M ha (a.2, s)).symm
    _ = value W H inv M (wholePlaneDartTrans W b.1 M hb (b.2, s)) :=
      congrArg (value W H inv M) (Prod.ext he rfl)
    _ = value W H inv b.1 (b.2, s) := value_trans W H inv b.1 M hb (b.2, s)

@[expose] def eventualPresence (W : ℤ → Fin 3) (N e : ℕ) : Prop :=
  ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
    EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W N L (hNM.trans hML) e)

private theorem eventualPresence_trans (W : ℤ → Fin 3) (N M : ℕ)
    (hNM : N ≤ M) (e : ℕ) :
    eventualPresence W M (wholePlaneEdgeTrans W N M hNM e) ↔
      eventualPresence W N e := by
  constructor
  · rintro ⟨L, hML, hp⟩
    refine ⟨L, hNM.trans hML, fun K hLK => ?_⟩
    rw [← congrFun (wholePlaneEdgeTrans_comp W N M K hNM (hML.trans hLK)) e]
    exact hp K hLK
  · rintro ⟨L, hNL, hp⟩
    refine ⟨max M L, Nat.le_max_left M L, fun K hK => ?_⟩
    have hc := congrFun (wholePlaneEdgeTrans_comp W N M K hNM
      ((Nat.le_max_left M L).trans hK)) e
    change wholePlaneEdgeTrans W M K ((Nat.le_max_left M L).trans hK)
      (wholePlaneEdgeTrans W N M hNM e) = _ at hc
    rw [hc]
    exact hp K ((Nat.le_max_right M L).trans hK)

theorem eventualPresence_rel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    eventualPresence W a.1 a.2 = eventualPresence W b.1 b.2 := by
  obtain ⟨M, ha, hb, he⟩ := hab
  apply propext
  apply (eventualPresence_trans W a.1 M ha a.2).symm.trans
  rw [he]
  exact eventualPresence_trans W b.1 M hb b.2

@[expose] def endpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

end DirectedDistances.KMSW
namespace DLQG1.Palomar.Principal.Transport
open DirectedDistances.KMSW
/-- The new public representative choice is the existing forward source rotation. -/
theorem value_false_eq_sourceRot (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (d : ℕ × Bool) :
    value W H false N d = wholePlaneRot W H (wholePlaneDartι W N d) := rfl
/-- The new public representative choice is the existing inverse source rotation. -/
theorem value_true_eq_sourceRotInv (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (d : ℕ × Bool) :
    value W H true N d = wholePlaneRotInv W H (wholePlaneDartι W N d) := rfl
/-- The new literal eventual-presence predicate is the actual source edge status. -/
theorem eventualPresence_eq_source (W : ℤ → Fin 3) (N e : ℕ) :
    eventualPresence W N e = wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := rfl
end DLQG1.Palomar.Principal.Transport
