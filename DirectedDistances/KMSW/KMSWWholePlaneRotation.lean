module

public import DirectedDistances.KMSW.KMSWWholePlaneRotationTransport

/-! Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
vertex rotation on the colimit darts under an explicit deterministic hypothesis on the word
(WholePlaneRotationHypothesis; its almost-sure discharge is separate); faces,
orientation/presence, β_0^{L,R}, the cut and the source identification (Q-F4c, unanswered)
are not treated; not the paper result. -/

public section
namespace DirectedDistances.KMSW

/-- including missing geometric edges; not the paper result. -/
@[expose] def WholePlaneDart (W : ℤ → Fin 3) : Type := WholePlaneEdge W × Bool

private noncomputable def runRot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) :
    Equiv.Perm (ℕ × Bool) :=
  if inv then (kmswInfRot (shiftedStream W N) (H.1 N)).symm
  else kmswInfRot (shiftedStream W N) (H.1 N)

private def eventualValue (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
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

private theorem eventualValue_existsUnique (W : ℤ → Fin 3)
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

private noncomputable def value (W : ℤ → Fin 3)
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

private theorem value_rel (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
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

private noncomputable def action (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (x : WholePlaneDart W) :
    WholePlaneDart W :=
  Quotient.lift (fun a : Σ _ : ℕ, ℕ => value W H inv a.1 (a.2, x.2))
    (fun a b hab => value_rel W H inv a b hab x.2) x.1

private theorem action_ι (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    action W H inv (wholePlaneDartι W N d) = value W H inv N d := rfl

private theorem action_agree (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool)
    (hf : ∀ M (h : N ≤ M), wholePlaneFresh W N M h (base W N d)) :
    action W H inv (wholePlaneDartι W N d) =
      wholePlaneDartι W N (runRot W H inv N d) := by
  rw [action_ι]
  apply eventualValue_unique W H inv N d _ _ (value_spec W H inv N d)
  refine ⟨N, Nat.le_refl N, fun M hNM => ?_⟩
  rw [← runRot_trans W H inv N M hNM d (hf M hNM)]
  exact congrFun (wholePlaneDartι_trans W N M hNM) (runRot W H inv N d)

private theorem infRot_base (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (d : ℕ × Bool) :
    base W N (kmswInfRot (shiftedStream W N) (H.1 N) d) = base W N d := by
  let w := shiftedStream W N
  obtain ⟨n, hn⟩ := kmswInfRot_eventually_eq_stage w (H.1 N) d
  obtain ⟨hd, he⟩ := hn n (Nat.le_refl n)
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  have hb (z : StageDart (kmswStage w n).nextEdge) :
      stageEndpoint (kmswStage w n) z = base W N (z.1.val, z.2) := by
    obtain ⟨hw, he⟩ := edge_endpoints_eq w z.1.isLt
    cases hs : z.2 <;>
      simp only [stageEndpoint, base, hs, Bool.false_eq_true, ↓reduceIte, hw, he] <;> rfl
  rw [he, ← hb (stageRot w n x), ← hb x]
  exact ((stageRot_sameCycle_iff_endpoint_eq w n x (stageRot w n x)).mp
    ⟨1, rfl⟩).symm

private theorem runRot_base (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    base W N (runRot W H inv N d) = base W N d := by
  cases inv
  · exact infRot_base W H N d
  · have he := infRot_base W H N ((kmswInfRot (shiftedStream W N) (H.1 N)).symm d)
    rw [Equiv.apply_symm_apply] at he
    exact he.symm

private theorem runRot_cancel (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    runRot W H (!inv) N (runRot W H inv N d) = d := by
  cases inv
  · exact Equiv.symm_apply_apply _ d
  · exact Equiv.apply_symm_apply _ d

private theorem action_cancel_ι (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    action W H (!inv) (action W H inv (wholePlaneDartι W N d)) =
      wholePlaneDartι W N d := by
  obtain ⟨M, hNM, hf⟩ := H.2 N (base W N d)
  let e := wholePlaneDartTrans W N M hNM d
  have hfe : ∀ L (hML : M ≤ L), wholePlaneFresh W M L hML (base W M e) := by
    intro L hML
    change wholePlaneFresh W M L hML
      (base W M (wholePlaneDartTrans W N M hNM d))
    rw [trans_base]
    exact hf L hML
  have hfr : ∀ L (hML : M ≤ L),
      wholePlaneFresh W M L hML (base W M (runRot W H inv M e)) := by
    intro L hML
    rw [runRot_base]
    exact hfe L hML
  have hi := congrFun (wholePlaneDartι_trans W N M hNM) d
  change wholePlaneDartι W M e = wholePlaneDartι W N d at hi
  rw [← hi, action_agree W H inv M e hfe,
    action_agree W H (!inv) M (runRot W H inv M e) hfr, runRot_cancel]

private theorem action_cancel (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (x : WholePlaneDart W) :
    action W H (!inv) (action W H inv x) = x := by
  obtain ⟨q, s⟩ := x
  refine Quotient.inductionOn q ?_
  rintro ⟨N, e⟩
  exact action_cancel_ι W H inv N (e, s)

/-- Whole-plane vertex rotation for the helper toward F4c
obtained from unique eventual values and quotient descent; not the paper result. -/
@[expose] noncomputable def wholePlaneRot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L (kmswInfRot (shiftedStream W L) (H.1 L)
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H false a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H false a b hab x.2) x.1

/-- Inverse whole-plane vertex rotation for the helper toward F4c
not the paper result. -/
@[expose] noncomputable def wholePlaneRotInv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L ((kmswInfRot (shiftedStream W L) (H.1 L)).symm
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H true a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H true a b hab x.2) x.1

/-- Forward-after-inverse cancellation for the helper toward F4c -/
theorem wholePlaneRot_comp_inv (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) :
    wholePlaneRot W H ∘ wholePlaneRotInv W H = id := by
  funext x
  exact action_cancel W H true x

/-- Inverse-after-forward cancellation for the helper toward F4c -/
theorem wholePlaneRotInv_comp_rot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    wholePlaneRotInv W H ∘ wholePlaneRot W H = id := by
  funext x
  exact action_cancel W H false x

/-- Whole-plane rotation permutation for the helper toward F4c
Its deterministic hypothesis has a separate almost-sure discharge; not the paper result. -/
@[expose] noncomputable def wholePlaneRotation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Equiv.Perm (WholePlaneDart W) where
  toFun := wholePlaneRot W H
  invFun := wholePlaneRotInv W H
  left_inv := congrFun (wholePlaneRotInv_comp_rot W H)
  right_inv := congrFun (wholePlaneRot_comp_inv W H)

/-- Choice-free uniqueness characterization of the representative value, toward F4c -/
theorem wholePlaneRot_existsUnique_eventual (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) :
    ∃! y : WholePlaneDart W, ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
      wholePlaneDartι W L (kmswInfRot (shiftedStream W L) (H.1 L)
        (wholePlaneDartTrans W N L (hNM.trans hML) d)) = y :=
  eventualValue_existsUnique W H false N d

/-- The descended rotation is the eventual embedded one-sided value, toward F4c -/
theorem wholePlaneRot_eventually (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) :
    ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
      wholePlaneDartι W L (kmswInfRot (shiftedStream W L) (H.1 L)
        (wholePlaneDartTrans W N L (hNM.trans hML) d)) =
          wholePlaneRot W H (wholePlaneDartι W N d) :=
  value_spec W H false N d



theorem wholePlaneRotation_ι_of_fresh (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool)
    (hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (if d.2 then edgeEast (shiftedStream W N) d.1
        else edgeWest (shiftedStream W N) d.1)) :
    wholePlaneRotation W H (wholePlaneDartι W N d) =
      wholePlaneDartι W N (kmswInfRot (shiftedStream W N) (H.1 N) d) :=
  action_agree W H false N d hf

/-- Inverse agreement at a base which stays fresh, toward F4c -/
theorem wholePlaneRotation_symm_ι_of_fresh (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool)
    (hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (if d.2 then edgeEast (shiftedStream W N) d.1
        else edgeWest (shiftedStream W N) d.1)) :
    (wholePlaneRotation W H).symm (wholePlaneDartι W N d) =
      wholePlaneDartι W N ((kmswInfRot (shiftedStream W N) (H.1 N)).symm d) :=
  action_agree W H true N d hf

end DirectedDistances.KMSW
