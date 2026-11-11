module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso12
public import DirectedDistances.KMSW.KMSWMeasurability
public import DirectedDistances.KMSW.StageMapCongr
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryLabels

/-! The code side retains all ten geometric fields, including missing edges. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory Filter DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section5
open scoped Classical

/-- Helper toward Lemma 5.10. Codes on which the witness-dependent KMSW
side is defined; the witnesses are properties, not additional random inputs. -/
@[expose] def kmswSideDomain : Set (ℕ → Fin 3) :=
  {w | BoundaryHitWitnesses (fun i => w (i + 1)) ∧
    KMSWFiniteIncidence (fun i => w (i + 1))}

/-- Helper toward Lemma 5.10. The full code-built marked side in Iso12,
written independently of the UIBHBOT sample and boundary index. -/
@[expose] noncomputable def kmswCodeGeometricSide
    (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hf : KMSWFiniteIncidence (fun i => w (i + 1))) : GeometricSideSubmap where
  vertices := {v | ∃ e, edgeWest (fun i => w (i + 1)) e = v ∨
    edgeEast (fun i => w (i + 1)) e = v}
  edges := {e | ∃ n, e < (kmswStage (fun i => w (i + 1)) n).nextEdge}
  west := edgeWest (fun i => w (i + 1))
  east := edgeEast (fun i => w (i + 1))
  present := {e | EdgePresent (fun i => w (i + 1)) e}
  rotation := fun d e => kmswInfRot (fun i => w (i + 1)) hf d = e
  faceNext := fun d e => kmswInfFaceSucc (fun i => w (i + 1)) hf d = e
  root := boundaryVertex (fun i => w (i + 1)) hb 0
  boundary := fun i => futureMapBoundaryDart (fun j => w (j + 1)) hb (-(i : ℤ) - 1)
  seam := fun i => (boundaryOuterEdge (fun j => w (j + 1)) hb (i : ℤ), false)

/-- Helper toward Lemma 5.10. Exact specialization to the side identified
with the corrected embedded future side by Iso12. -/
theorem kmswCodeGeometricSide_futureCode (k : ℤ) (W : ℤ → Fin 3)
    (hb : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (hf : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1))) :
    kmswCodeGeometricSide (uibhbotFutureCode k W) hb hf =
      uibhbotFutureCodeGeometricSide k W hb hf := rfl

/-- Helper toward Lemma 5.10. Each permanent west endpoint is a finite-prefix
observable, including on codes outside the side domain. -/
theorem measurable_kmswCodeSide_west (e : ℕ) :
    Measurable (fun w : ℕ → Fin 3 => edgeWest (fun i => w (i + 1)) e) :=
  measurable_kmswStage_shift_comp e (fun s => s.west e)

/-- Helper toward Lemma 5.10. Each permanent east endpoint is a finite-prefix
observable, including on codes outside the side domain. -/
theorem measurable_kmswCodeSide_east (e : ℕ) :
    Measurable (fun w : ℕ → Fin 3 => edgeEast (fun i => w (i + 1)) e) :=
  measurable_kmswStage_shift_comp e (fun s => s.east e)

/-- Helper toward Lemma 5.10. Vertex membership is a countable union of
finite-prefix endpoint events; missing geometric edges are retained. -/
theorem measurableSet_kmswCodeSide_vertices (v : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 | ∃ e,
      edgeWest (fun i => w (i + 1)) e = v ∨
        edgeEast (fun i => w (i + 1)) e = v} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun e =>
    (measurableSet_eq_fun (measurable_kmswCodeSide_west e) measurable_const).union
      (measurableSet_eq_fun (measurable_kmswCodeSide_east e) measurable_const)

/-- Helper toward Lemma 5.10. Allocation membership is a countable union
of finite-prefix stage events. -/
theorem measurableSet_kmswCodeSide_edges (e : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 | ∃ n,
      e < (kmswStage (fun i => w (i + 1)) n).nextEdge} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun n => measurableSet_kmswStage_shift n (fun s => e < s.nextEdge)

/-- Helper toward Lemma 5.10. Directed presence is measurable separately
from geometric allocation, preserving missing-edge status. -/
theorem measurableSet_kmswCodeSide_present (e : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 | EdgePresent (fun i => w (i + 1)) e} := by
  unfold EdgePresent
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun n => measurableSet_kmswStage_shift n
    (fun s => e < s.nextEdge ∧ s.present e = true)

/-- Helper toward Lemma 5.10. A finite-stage rotation entry retains the
permanent edge ID and the dart polarity. -/
@[expose] def kmswCodeSideFiniteRotation (w : ℕ → Fin 3) (n : ℕ)
    (d e : ℕ × Bool) : Prop :=
  ∃ hd : d.1 < (kmswStage (fun i => w (i + 1)) n).nextEdge,
    ((stageRot (fun i => w (i + 1)) n (⟨d.1, hd⟩, d.2)).1.val,
      (stageRot (fun i => w (i + 1)) n (⟨d.1, hd⟩, d.2)).2) = e

/-- Helper toward Lemma 5.10. Common prefixes preserve finite rotation entries. -/
theorem kmswCodeSideFiniteRotation_of_prefix (w w' : ℕ → Fin 3)
    (n : ℕ) (h : ∀ i < n + 1, w i = w' i) (d e : ℕ × Bool) :
    kmswCodeSideFiniteRotation w n d e → kmswCodeSideFiniteRotation w' n d e := by
  rintro ⟨hd, he⟩
  let u := fun i => w (i + 1)
  let u' := fun i => w' (i + 1)
  have hp : ∀ i < n, u i = u' i := fun i hi => h (i + 1) (by omega)
  let I := kmswStageDirectedMapIsoOfPrefix u u' n hp
  let x : StageDart (kmswStage u n).nextEdge := (⟨d.1, hd⟩, d.2)
  have hx := kmswStageDirectedMapIsoOfPrefix_val u u' n hp x
  have hy := kmswStageDirectedMapIsoOfPrefix_val u u' n hp (stageRot u n x)
  have hb : d.1 < (kmswStage u' n).nextEdge := by
    rw [← kmswStage_congr hp]
    exact hd
  have hIx : I.toEquiv x = (⟨d.1, hb⟩, d.2) :=
    Prod.ext (Fin.ext hx.1) hx.2
  refine ⟨hb, ?_⟩
  have hr := I.rot_comm x
  change I.toEquiv (stageRot u n x) = stageRot u' n (I.toEquiv x) at hr
  have hv := congrArg (fun z => (z.1.val, z.2)) hr
  rw [hIx] at hv
  exact hv.symm.trans ((Prod.ext hy.1 hy.2).trans he)

/-- Helper toward Lemma 5.10. Finite rotation entries are prefix events. -/
theorem measurableSet_kmswCodeSideFiniteRotation (n : ℕ) (d e : ℕ × Bool) :
    MeasurableSet {w | kmswCodeSideFiniteRotation w n d e} := by
  refine measurableSet_of_factors_prefix (n + 1) _ ?_
  intro w w' h
  exact ⟨kmswCodeSideFiniteRotation_of_prefix w w' n h d e,
    kmswCodeSideFiniteRotation_of_prefix w' w n (fun i hi => (h i hi).symm) d e⟩

/-- Helper toward Lemma 5.10. The infinite rotation entry is exactly an
eventual finite-prefix entry on its proved finite-incidence domain. -/
theorem kmswCodeSide_rotation_iff_eventually
    (w : ℕ → Fin 3) (hf : KMSWFiniteIncidence (fun i => w (i + 1)))
    (d e : ℕ × Bool) :
    kmswInfRot (fun i => w (i + 1)) hf d = e ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → kmswCodeSideFiniteRotation w n d e := by
  obtain ⟨M, hM⟩ := kmswInfRot_eventually_eq_stage (fun i => w (i + 1)) hf d
  constructor
  · intro he
    refine ⟨M, fun n hn => ?_⟩
    obtain ⟨hd, hdval⟩ := hM n hn
    exact ⟨hd, hdval.symm.trans he⟩
  · rintro ⟨N, hN⟩
    obtain ⟨hd, hdval⟩ := hM (max M N) (le_max_left _ _)
    obtain ⟨hd', hentry⟩ := hN (max M N) (le_max_right _ _)
    exact hdval.trans hentry

/-- Helper toward Lemma 5.10. Every infinite rotation relation coordinate is
measurable on the natural witness domain. -/
theorem measurableSet_kmswCodeSide_rotation (d e : ℕ × Bool) :
    MeasurableSet {w : kmswSideDomain |
      kmswInfRot (fun i => w.1 (i + 1)) w.2.2 d = e} := by
  have he : {w : kmswSideDomain |
      kmswInfRot (fun i => w.1 (i + 1)) w.2.2 d = e} =
      ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n),
        {w : kmswSideDomain | kmswCodeSideFiniteRotation w.1 n d e} := by
    ext w
    simpa only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq] using
      kmswCodeSide_rotation_iff_eventually w.1 w.2.2 d e
  rw [he]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ =>
      (measurableSet_kmswCodeSideFiniteRotation n d e).preimage measurable_subtype_coe

/-- Helper toward Lemma 5.10. The face relation is measurable by inverse
rotation after dart reversal, with no ambient-face substitution. -/
theorem measurableSet_kmswCodeSide_faceNext (d e : ℕ × Bool) :
    MeasurableSet {w : kmswSideDomain |
      kmswInfFaceSucc (fun i => w.1 (i + 1)) w.2.2 d = e} := by
  have he : {w : kmswSideDomain |
      kmswInfFaceSucc (fun i => w.1 (i + 1)) w.2.2 d = e} =
      {w : kmswSideDomain |
        kmswInfRot (fun i => w.1 (i + 1)) w.2.2 e = (d.1, !d.2)} := by
    ext w
    change (kmswInfRot (fun i => w.1 (i + 1)) w.2.2).symm (d.1, !d.2) = e ↔ _
    exact (Equiv.symm_apply_eq _).trans eq_comm
  rw [he]
  exact measurableSet_kmswCodeSide_rotation e (d.1, !d.2)

/-- Helper toward Lemma 5.10. Hitting times are measurable on the witness
domain, by measurable least selection of finite-prefix coordinate events. -/
theorem measurable_kmswCodeSide_boundaryHitTime (k : ℤ) :
    Measurable (fun w : kmswSideDomain =>
      boundaryHitTime (fun i => w.1 (i + 1)) w.2.1 k) := by
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryHitTime]
  · by_cases hkpos : 0 < k
    · have hm := measurable_find
        (fun w : kmswSideDomain => w.2.1.rightHit k (by omega))
        (fun n => (measurableSet_R n (fun z => z = -k)).preimage
          (measurable_pi_iff.mpr (fun i =>
            (measurable_pi_apply (i + 1)).comp measurable_subtype_coe)))
      simpa [boundaryHitTime, hk0, hkpos] using hm
    · have hm := measurable_find
        (fun w : kmswSideDomain => w.2.1.leftHit k (by omega))
        (fun n => (measurableSet_L n (fun z => z = k)).preimage
          (measurable_pi_iff.mpr (fun i =>
            (measurable_pi_apply (i + 1)).comp measurable_subtype_coe)))
      simpa [boundaryHitTime, hk0, hkpos] using hm

private theorem measurable_side_select {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] (f : ℕ → Ω → β) (hf : ∀ n, Measurable (f n))
    (g : Ω → ℕ) (hg : Measurable g) : Measurable (fun w => f (g w) w) := by
  have hm : Measurable (fun p : Ω × ℕ => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact hm.comp (measurable_id.prodMk hg)

/-- Helper toward Lemma 5.10. All integer-indexed outer-boundary edges are
measurable, including the missing negative edges and the root edge. -/
theorem measurable_kmswCodeSide_boundaryOuterEdge (k : ℤ) :
    Measurable (fun w : kmswSideDomain =>
      boundaryOuterEdge (fun i => w.1 (i + 1)) w.2.1 k) := by
  by_cases hkneg : k ≤ -1
  · simp only [boundaryOuterEdge, ite_eq_left hkneg]
    exact measurable_side_select
      (fun n w => kmswLLCreatedEdge (fun i => w.1 (i + 1)) n)
      (fun n => (measurable_kmswStage_shift_comp n
        (fun s => s.nextEdge - 1)).comp measurable_subtype_coe)
      _ (measurable_kmswCodeSide_boundaryHitTime k)
  · by_cases hkpos : 1 ≤ k
    · have he : (fun w : kmswSideDomain =>
          boundaryOuterEdge (fun i => w.1 (i + 1)) w.2.1 k) =
          (fun w : kmswSideDomain =>
            act (fun i => w.1 (i + 1))
              (boundaryHitTime (fun i => w.1 (i + 1)) w.2.1 k)) := by
        funext w
        rw [boundaryOuterEdge_of_positive _ _ hkpos,
          ← (boundaryHitTime_right_boundary_edge _ w.2.1 (j := k.toNat)
            (by omega)).1]
        congr 2
        exact Int.toNat_of_nonneg (by omega)
      rw [he]
      exact measurable_side_select
        (fun n w => act (fun i => w.1 (i + 1)) n)
        (fun n => (measurable_kmswStage_shift_comp n
          (fun s => s.active)).comp measurable_subtype_coe)
        _ (measurable_kmswCodeSide_boundaryHitTime k)
    · have hk : k = 0 := by omega
      subst k
      simpa only [boundaryOuterEdge_zero] using
        (measurable_const : Measurable (fun _ : kmswSideDomain => (0 : ℕ)))

/-- Helper toward Lemma 5.10. Every boundary-dart coordinate is measurable. -/
theorem measurable_kmswCodeSide_boundary (i : ℕ) :
    Measurable (fun w : kmswSideDomain =>
      (kmswCodeGeometricSide w.1 w.2.1 w.2.2).boundary i) :=
  (measurable_kmswCodeSide_boundaryOuterEdge (-(i : ℤ) - 1)).prodMk measurable_const

/-- Helper toward Lemma 5.10. Every seam-dart coordinate is measurable. -/
theorem measurable_kmswCodeSide_seam (i : ℕ) :
    Measurable (fun w : kmswSideDomain =>
      (kmswCodeGeometricSide w.1 w.2.1 w.2.2).seam i) :=
  (measurable_kmswCodeSide_boundaryOuterEdge (i : ℤ)).prodMk measurable_const

/-- Helper toward Lemma 5.10. The root coordinate is the constant vertex zero. -/
theorem measurable_kmswCodeSide_root :
    Measurable (fun w : kmswSideDomain =>
      (kmswCodeGeometricSide w.1 w.2.1 w.2.2).root) := by
  simpa only [kmswCodeGeometricSide, boundaryVertex_zero] using
    (measurable_const : Measurable (fun _ : kmswSideDomain => (0 : ℕ)))

private theorem measurable_side_decide {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → Prop) (hP : MeasurableSet {w | P w}) :
    Measurable (fun w => decide (P w)) := by
  apply measurable_to_bool
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hP

/-- Helper toward Lemma 5.10. All ten fields of the full marked KMSW side
are jointly measurable on their natural construction domain. -/
theorem measurable_kmswCodeGeometricSide :
    Measurable (fun w : kmswSideDomain =>
      kmswCodeGeometricSide w.1 w.2.1 w.2.2) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun w : kmswSideDomain =>
    geometricSideCode (kmswCodeGeometricSide w.1 w.2.1 w.2.2))
  have hv : ∀ v, Measurable (fun w : kmswSideDomain =>
      decide (v ∈ (kmswCodeGeometricSide w.1 w.2.1 w.2.2).vertices)) := by
    intro v
    exact measurable_side_decide _
      ((measurableSet_kmswCodeSide_vertices v).preimage measurable_subtype_coe)
  have he : ∀ e, Measurable (fun w : kmswSideDomain =>
      decide (e ∈ (kmswCodeGeometricSide w.1 w.2.1 w.2.2).edges)) := by
    intro e
    exact measurable_side_decide _
      ((measurableSet_kmswCodeSide_edges e).preimage measurable_subtype_coe)
  have hp : ∀ e, Measurable (fun w : kmswSideDomain =>
      decide (e ∈ (kmswCodeGeometricSide w.1 w.2.1 w.2.2).present)) := by
    intro e
    exact measurable_side_decide _
      ((measurableSet_kmswCodeSide_present e).preimage measurable_subtype_coe)
  have hr : ∀ d e, Measurable (fun w : kmswSideDomain =>
      decide ((kmswCodeGeometricSide w.1 w.2.1 w.2.2).rotation d e)) := by
    intro d e
    exact measurable_side_decide _ (measurableSet_kmswCodeSide_rotation d e)
  have hf : ∀ d e, Measurable (fun w : kmswSideDomain =>
      decide ((kmswCodeGeometricSide w.1 w.2.1 w.2.2).faceNext d e)) := by
    intro d e
    exact measurable_side_decide _ (measurableSet_kmswCodeSide_faceNext d e)
  exact (measurable_pi_iff.mpr hv).prodMk
    ((measurable_pi_iff.mpr he).prodMk
      ((measurable_pi_iff.mpr (fun e =>
        (measurable_kmswCodeSide_west e).comp measurable_subtype_coe)).prodMk
        ((measurable_pi_iff.mpr (fun e =>
          (measurable_kmswCodeSide_east e).comp measurable_subtype_coe)).prodMk
          ((measurable_pi_iff.mpr hp).prodMk
            ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr (hr d))).prodMk
              ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr (hf d))).prodMk
                (measurable_kmswCodeSide_root.prodMk
                  ((measurable_pi_iff.mpr measurable_kmswCodeSide_boundary).prodMk
                    (measurable_pi_iff.mpr measurable_kmswCodeSide_seam)))))))))

/-- Helper toward Lemma 5.10. The marked-isomorphism class of the full code
side is measurable on its witness domain. -/
theorem measurable_kmswCodeGeometricSide_class :
    Measurable (fun w : kmswSideDomain =>
      geometricSideClass (kmswCodeGeometricSide w.1 w.2.1 w.2.2)) :=
  measurable_geometricSideClass.comp measurable_kmswCodeGeometricSide

/-- Helper toward Lemma 5.10. The construction domain is measurable. -/
theorem measurableSet_kmswSideDomain : MeasurableSet kmswSideDomain := by
  have hs : Measurable (fun w : ℕ → Fin 3 => fun i => w (i + 1)) := by fun_prop
  have hb : MeasurableSet {w : ℕ → Fin 3 |
      BoundaryHitWitnesses (fun i => w (i + 1))} := by
    have he : {w : ℕ → Fin 3 | BoundaryHitWitnesses (fun i => w (i + 1))} =
        {w | (∀ k : ℤ, 1 ≤ k → ∃ n, R (fun i => w (i + 1)) n = -k) ∧
          (∀ k : ℤ, k ≤ -1 → ∃ n, L (fun i => w (i + 1)) n = k)} := by
      ext w
      exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
    rw [he]
    rw [Set.ofPred_and]
    apply MeasurableSet.inter
    · simp only [Set.ofPred_forall, Set.ofPred_exists]
      exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        MeasurableSet.iUnion fun n => (measurableSet_R n (fun z => z = -k)).preimage hs
    · simp only [Set.ofPred_forall, Set.ofPred_exists]
      exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        MeasurableSet.iUnion fun n => (measurableSet_L n (fun z => z = k)).preimage hs
  exact hb.inter (measurableSet_finiteIncidence.preimage hs)

/-- Helper toward Lemma 5.10. Both construction properties hold together
almost surely under the iid code law. -/
theorem ae_mem_kmswSideDomain : ∀ᵐ w ∂iidCodeMeasure, w ∈ kmswSideDomain := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses, iidCodes_ae_finite_incident_edges]
    with w hb hf
  exact ⟨hb, hf⟩

/-- Helper toward Lemma 5.10. A total measurable realization of the code
side. Outside the measurable null exceptional set, the displayed empty-field
value is only a completion convention, with no map-identification claim. -/
@[expose] noncomputable def kmswCodeGeometricSideTotal (w : ℕ → Fin 3) :
    GeometricSideSubmap :=
  if h : w ∈ kmswSideDomain then kmswCodeGeometricSide w h.1 h.2
  else
    { vertices := ∅, edges := ∅, west := fun _ => 0, east := fun _ => 0
      present := ∅, rotation := fun _ _ => False, faceNext := fun _ _ => False
      root := 0, boundary := fun _ => (0, false), seam := fun _ => (0, false) }

/-- Helper toward Lemma 5.10. The total realization is exactly the
witness-dependent code side wherever the construction properties hold. -/
theorem kmswCodeGeometricSideTotal_eq (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hf : KMSWFiniteIncidence (fun i => w (i + 1))) :
    kmswCodeGeometricSideTotal w = kmswCodeGeometricSide w hb hf := by
  exact dite_eq_left ⟨hb, hf⟩

/-- Helper toward Lemma 5.10. The full-space code-side realization is measurable. -/
theorem measurable_kmswCodeGeometricSideTotal : Measurable kmswCodeGeometricSideTotal :=
  measurable_kmswCodeGeometricSide.dite measurable_const measurableSet_kmswSideDomain

/-- Helper toward Lemma 5.10. The full-space marked-class observable is measurable. -/
theorem measurable_kmswCodeGeometricSideTotal_class :
    Measurable (fun w => geometricSideClass (kmswCodeGeometricSideTotal w)) :=
  measurable_geometricSideClass.comp measurable_kmswCodeGeometricSideTotal

/-- Helper toward Lemma 5.10. Almost surely the total class is the class
of the actual complete KMSW side, with both construction witnesses supplied. -/
theorem ae_kmswCodeGeometricSideTotal_class :
    ∀ᵐ w ∂iidCodeMeasure,
      ∃ (hb : BoundaryHitWitnesses (fun i => w (i + 1)))
        (hf : KMSWFiniteIncidence (fun i => w (i + 1))),
        geometricSideClass (kmswCodeGeometricSideTotal w) =
          geometricSideClass (kmswCodeGeometricSide w hb hf) := by
  filter_upwards [ae_mem_kmswSideDomain] with w hw
  exact ⟨hw.1, hw.2, congrArg geometricSideClass
    (kmswCodeGeometricSideTotal_eq w hw.1 hw.2)⟩

/-- Helper toward Lemma 5.10. The future-code class has the iid KMSW class
law, by measurable pushforward composition and the proved future code law. -/
theorem kmswCodeGeometricSideTotal_future_class_law (k : ℤ) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (fun W => geometricSideClass (kmswCodeGeometricSideTotal (uibhbotFutureCode k W))) =
      iidCodeMeasure.map (fun w => geometricSideClass (kmswCodeGeometricSideTotal w)) := by
  change (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    ((fun w => geometricSideClass (kmswCodeGeometricSideTotal w)) ∘ uibhbotFutureCode k) = _
  rw [← Measure.map_map measurable_kmswCodeGeometricSideTotal_class
    (measurable_uibhbotFutureCode k), uibhbotFutureCode_law]

/-- Helper toward Lemma 5.10. The measurable future-code class represents
the corrected embedded future side almost surely, with actual construction
witnesses supplied rather than assumed. -/
theorem ae_kmswCodeGeometricSideTotal_future_class (k : ℤ) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (hb : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
        (H : WholePlaneRotationHypothesis W)
        (_hf : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1))),
        geometricSideClass (kmswCodeGeometricSideTotal (uibhbotFutureCode k W)) =
          geometricSideClass (uibhbotFutureInducedPlaneGeometricSide k W hb H) := by
  have hd : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      uibhbotFutureCode k W ∈ kmswSideDomain := by
    have h := ae_mem_kmswSideDomain
    rw [← uibhbotFutureCode_law k] at h
    exact ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h
  have hH : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      WholePlaneRotationHypothesis W := by
    filter_upwards [ae_uibhbotCodeLawRel_boundaryShift_rotationHypothesis,
      ae_uibhbotBoundaryHitTime_zero] with W hrot hzero
    have hh := hrot 0
    rw [hzero] at hh
    have hs : shiftWordInt W 0 = W := by
      funext i
      exact congrArg W (add_zero i)
    rw [hs] at hh
    exact hh
  filter_upwards [hd, hH, ae_uibhbotFutureInducedPlaneGeometricSide_class_eq]
    with W hd H heq
  refine ⟨hd.1, H, hd.2, ?_⟩
  rw [kmswCodeGeometricSideTotal_eq _ hd.1 hd.2,
    kmswCodeGeometricSide_futureCode]
  exact (heq k hd.1 H hd.2).symm

/-- Helper toward Lemma 5.10. The recorded first-claim law target, with a
measurable iid marked-class observable and an almost surely identified
UIBHBOT future observable at every integer boundary index. This says nothing
about the separate directed-path-containment claim of the lemma. -/
theorem uibhbotFutureInducedPlaneGeometricSide_class_law :
    ∃ Y : (ℕ → Fin 3) → GeometricSideClass,
      Measurable Y ∧
      (∀ᵐ w ∂iidCodeMeasure,
        ∃ (hb : BoundaryHitWitnesses (fun i => w (i + 1)))
          (hf : KMSWFiniteIncidence (fun i => w (i + 1))),
          Y w = geometricSideClass (kmswCodeGeometricSide w hb hf)) ∧
      ∀ k : ℤ, ∃ X : (ℤ → Fin 3) → GeometricSideClass,
        AEMeasurable X (uibhbotCodeLawRel : Measure (ℤ → Fin 3)) ∧
        (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
          ∃ (hb : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
            (H : WholePlaneRotationHypothesis W)
            (_hf : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1))),
            X W = geometricSideClass
              (uibhbotFutureInducedPlaneGeometricSide k W hb H)) ∧
        (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map X = iidCodeMeasure.map Y := by
  refine ⟨fun w => geometricSideClass (kmswCodeGeometricSideTotal w),
    measurable_kmswCodeGeometricSideTotal_class, ae_kmswCodeGeometricSideTotal_class, ?_⟩
  intro k
  refine ⟨fun W => geometricSideClass
    (kmswCodeGeometricSideTotal (uibhbotFutureCode k W)),
    (measurable_kmswCodeGeometricSideTotal_class.comp
      (measurable_uibhbotFutureCode k)).aemeasurable,
    ae_kmswCodeGeometricSideTotal_future_class k,
    kmswCodeGeometricSideTotal_future_class_law k⟩

/-- Helper toward Lemma 5.10. The complete field encoding of the total side
is measurable, giving coordinate measurability on the entire code space. -/
theorem measurable_kmswCodeGeometricSideTotal_code :
    Measurable (fun w => geometricSideCode (kmswCodeGeometricSideTotal w)) :=
  measurable_comap_iff.mp measurable_kmswCodeGeometricSideTotal

/-- Helper toward Lemma 5.10. Full-space vertex-membership coordinate. -/
theorem measurable_kmswCodeSideTotal_vertices (v : ℕ) :
    Measurable (fun w => decide (v ∈ (kmswCodeGeometricSideTotal w).vertices)) :=
  (measurable_pi_apply v).comp measurable_kmswCodeGeometricSideTotal_code.fst

/-- Helper toward Lemma 5.10. Full-space geometric edge-membership coordinate. -/
theorem measurable_kmswCodeSideTotal_edges (e : ℕ) :
    Measurable (fun w => decide (e ∈ (kmswCodeGeometricSideTotal w).edges)) :=
  (measurable_pi_apply e).comp measurable_kmswCodeGeometricSideTotal_code.snd.fst

/-- Helper toward Lemma 5.10. Full-space west-endpoint coordinate. -/
theorem measurable_kmswCodeSideTotal_west (e : ℕ) :
    Measurable (fun w => (kmswCodeGeometricSideTotal w).west e) :=
  (measurable_pi_apply e).comp measurable_kmswCodeGeometricSideTotal_code.snd.snd.fst

/-- Helper toward Lemma 5.10. Full-space east-endpoint coordinate. -/
theorem measurable_kmswCodeSideTotal_east (e : ℕ) :
    Measurable (fun w => (kmswCodeGeometricSideTotal w).east e) :=
  (measurable_pi_apply e).comp measurable_kmswCodeGeometricSideTotal_code.snd.snd.snd.fst

/-- Helper toward Lemma 5.10. Full-space directed-presence coordinate. -/
theorem measurable_kmswCodeSideTotal_present (e : ℕ) :
    Measurable (fun w => decide (e ∈ (kmswCodeGeometricSideTotal w).present)) :=
  (measurable_pi_apply e).comp measurable_kmswCodeGeometricSideTotal_code.snd.snd.snd.snd.fst

/-- Helper toward Lemma 5.10. Full-space rotation-relation coordinate. -/
theorem measurable_kmswCodeSideTotal_rotation (d e : ℕ × Bool) :
    Measurable (fun w => decide ((kmswCodeGeometricSideTotal w).rotation d e)) :=
  (measurable_pi_apply e).comp ((measurable_pi_apply d).comp
    measurable_kmswCodeGeometricSideTotal_code.snd.snd.snd.snd.snd.fst)

/-- Helper toward Lemma 5.10. Full-space face-successor relation coordinate. -/
theorem measurable_kmswCodeSideTotal_faceNext (d e : ℕ × Bool) :
    Measurable (fun w => decide ((kmswCodeGeometricSideTotal w).faceNext d e)) :=
  (measurable_pi_apply e).comp ((measurable_pi_apply d).comp
    measurable_kmswCodeGeometricSideTotal_code.snd.snd.snd.snd.snd.snd.fst)

/-- Helper toward Lemma 5.10. Full-space root coordinate. -/
theorem measurable_kmswCodeSideTotal_root :
    Measurable (fun w => (kmswCodeGeometricSideTotal w).root) :=
  measurable_kmswCodeGeometricSideTotal_code.snd.snd.snd.snd.snd.snd.snd.fst

/-- Helper toward Lemma 5.10. Full-space indexed boundary-dart coordinate. -/
theorem measurable_kmswCodeSideTotal_boundary (i : ℕ) :
    Measurable (fun w => (kmswCodeGeometricSideTotal w).boundary i) :=
  (measurable_pi_apply i).comp
    measurable_kmswCodeGeometricSideTotal_code.snd.snd.snd.snd.snd.snd.snd.snd.fst

/-- Helper toward Lemma 5.10. Full-space indexed seam-dart coordinate. -/
theorem measurable_kmswCodeSideTotal_seam (i : ℕ) :
    Measurable (fun w => (kmswCodeGeometricSideTotal w).seam i) :=
  (measurable_pi_apply i).comp
    measurable_kmswCodeGeometricSideTotal_code.snd.snd.snd.snd.snd.snd.snd.snd.snd

end DirectedDistances.RandomWalk

