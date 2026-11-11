module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso7




public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5

private theorem wholePlaneDartFlip_side (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    (wholePlaneDartFlip W d).2 = !d.2 := rfl

/-- Helper toward Lemma 5.10. Almost surely, the whole-plane rotation
hypothesis holds after shifting the UIBHBOT code to any boundary hit. -/
theorem ae_uibhbotCodeLawRel_boundaryShift_rotationHypothesis :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      WholePlaneRotationHypothesis
        (shiftWordInt W (uibhbotBoundaryHitTime k W)) := by
  have hmeasShift (t : ℤ) :
      Measurable (fun W : ℤ → Fin 3 => shiftWordInt W t) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (i + t)
  have hmeasEvent (k t : ℤ) : MeasurableSet
      {W : ℤ → Fin 3 | uibhbotBoundaryHitTime k W = t ∧
        WholePlaneRotationHypothesis (shiftWordInt W t)} := by
    exact (measurableSet_eq_fun (measurable_uibhbotBoundaryHitTime k)
      measurable_const).inter
      (measurableSet_uibhbotRotationHypothesisRel.preimage (hmeasShift t))
  have hmeasShiftHit (k : ℤ) : MeasurableSet
      {W : ℤ → Fin 3 |
        WholePlaneRotationHypothesis
          (shiftWordInt W (uibhbotBoundaryHitTime k W))} := by
    rw [show {W : ℤ → Fin 3 |
        WholePlaneRotationHypothesis
          (shiftWordInt W (uibhbotBoundaryHitTime k W))} =
      ⋃ t : ℤ, {W : ℤ → Fin 3 | uibhbotBoundaryHitTime k W = t ∧
        WholePlaneRotationHypothesis (shiftWordInt W t)} by
      ext W
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨uibhbotBoundaryHitTime k W, rfl, h⟩
      · rintro ⟨t, ht, h⟩
        simpa [ht] using h]
    exact MeasurableSet.iUnion fun t => hmeasEvent k t
  have hmeas : MeasurableSet {W : ℤ → Fin 3 | ∀ k : ℤ,
      WholePlaneRotationHypothesis
        (shiftWordInt W (uibhbotBoundaryHitTime k W))} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter hmeasShiftHit
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, ∀ k : ℤ,
    WholePlaneRotationHypothesis
      (shiftWordInt W (uibhbotBoundaryHitTime k W))
  rw [ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable hmeas]
  exact uibhbotWordFamilyLaw_ae_boundaryShift_rotationHypothesis

private theorem wholePlaneStartIso_faceSucc (W : ℤ → Fin 3) (t : ℤ)
    (phi : WholePlaneStartIso W t)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W t))
    (d : WholePlaneDart (shiftWordInt W t)) :
    phi.dart (wholePlaneFaceSucc (shiftWordInt W t) H' d) =
      wholePlaneFaceSucc W H (phi.dart d) := by
  have hstep (x : WholePlaneDart (shiftWordInt W t)) :
      phi.dart ((wholePlaneRotation (shiftWordInt W t) H').symm x) =
        (wholePlaneRotation W H).symm (phi.dart x) := by
    have hr := phi.rot H H' ((wholePlaneRotation (shiftWordInt W t) H').symm x)
    rw [Equiv.apply_symm_apply] at hr
    calc
      phi.dart ((wholePlaneRotation (shiftWordInt W t) H').symm x) =
          (wholePlaneRotation W H).symm
            (wholePlaneRotation W H
              (phi.dart ((wholePlaneRotation (shiftWordInt W t) H').symm x))) := by
                rw [Equiv.symm_apply_apply]
      _ = (wholePlaneRotation W H).symm (phi.dart x) := by rw [← hr]
  have hflip (x : WholePlaneDart (shiftWordInt W t)) :
      phi.dart (wholePlaneDartFlip (shiftWordInt W t) x) =
        wholePlaneDartFlip W (phi.dart x) := by
    apply Prod.ext
    · calc
        (phi.dart (wholePlaneDartFlip (shiftWordInt W t) x)).1 =
            phi.edge (wholePlaneDartFlip (shiftWordInt W t) x).1 :=
              congrArg Prod.fst (phi.dart_apply _)
        _ = phi.edge x.1 := congrArg phi.edge (wholePlaneDartFlip_edge _ x)
        _ = (phi.dart x).1 := (congrArg Prod.fst (phi.dart_apply x)).symm
        _ = (wholePlaneDartFlip W (phi.dart x)).1 :=
              (wholePlaneDartFlip_edge W (phi.dart x)).symm
    · calc
        (phi.dart (wholePlaneDartFlip (shiftWordInt W t) x)).2 =
            (wholePlaneDartFlip (shiftWordInt W t) x).2 :=
              congrArg Prod.snd (phi.dart_apply _)
        _ = !x.2 := wholePlaneDartFlip_side (shiftWordInt W t) x
        _ = !(phi.dart x).2 :=
              congrArg (fun b : Bool => !b)
                (congrArg Prod.snd (phi.dart_apply x)).symm
        _ = (wholePlaneDartFlip W (phi.dart x)).2 :=
              (wholePlaneDartFlip_side W (phi.dart x)).symm
  change phi.dart ((wholePlaneRotation (shiftWordInt W t) H').symm
      (wholePlaneDartFlip (shiftWordInt W t) d)) =
    (wholePlaneRotation W H).symm (wholePlaneDartFlip W (phi.dart d))
  rw [hstep, hflip]

/-- Helper toward Lemma 5.10. Negative external future darts have first return
length one when the future code begins at a positive boundary time, by
transporting the missing-boundary successor across the integer-start
isomorphism. -/
theorem ae_uibhbotFuturePlaneGeometricSide_externalFaceNext_negative_positiveStart :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ _hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
              e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
                ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
                  (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite,
              0 < uibhbotBoundaryHitTime k W →
                ∀ j : ℤ, j ≤ -1 →
                  (uibhbotFuturePlaneGeometricSide k W h H).faceNext
                    (futureMapBoundaryDart
                      (fun i => uibhbotFutureCode k W (i + 1)) h j)
                    (futureMapBoundaryDart
                      (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1)) := by
  filter_upwards [ae_uibhbotFutureSubmap_externalEdge_missing_negative,
    ae_uibhbotCodeLawRel_boundaryShift_rotationHypothesis]
    with W hmissing hrot k h H _hfin ht j hj
  let t := uibhbotBoundaryHitTime k W
  let V := shiftWordInt W t
  have hV : WholePlaneRotationHypothesis V := hrot k
  let phi := Classical.choice (wholePlaneStartIso_nonempty W t)
  have hstream : (fun i => uibhbotFutureCode k W (i + 1)) = shiftedStream V 0 := by
    rw [uibhbotFutureCode_stream, lemma38StartStream_eq_nonnegative W t (by omega)]
    funext i
    simp [V, shiftWordInt, shiftedStream, Int.toNat_of_nonneg (by omega : 0 ≤ t)]
  have hVh : BoundaryHitWitnesses (shiftedStream V 0) := by
    rw [← hstream]
    exact h
  have hmissing' : ¬ wholePlaneEdgePresent V
      (wholePlaneEdgeι V 0
        (boundaryOuterEdge (shiftedStream V 0) hVh j)) := by
    have hm := hmissing k h j hj
    have he : phi.edge (wholePlaneEdgeι V 0
        (boundaryOuterEdge (shiftedStream V 0) hVh j)) =
        uibhbotFutureEdge k W
          (boundaryOuterEdge (fun i => uibhbotFutureCode k W (i + 1)) h j) := by
      simpa [uibhbotFutureEdge, hstream] using
        (phi.iota_edge (boundaryOuterEdge (shiftedStream V 0) hVh j))
    intro hp
    apply hm
    rw [← he]
    exact (phi.present _).2 hp
  have hstep := (wholePlane_missing_boundary_faceSucc V hV 0 hVh j hj hmissing').2
  have hmap (d : ℕ × Bool) :
      (uibhbotFutureSubmapDartEquiv k W h d).1 =
        phi.dart (show WholePlaneDart (shiftWordInt W t) from
          (wholePlaneEdgeι (shiftWordInt W t) 0 d.1, d.2)) := by
    rw [uibhbotFutureSubmapDartEquiv_val]
    change (uibhbotFutureEdge k W d.1, d.2) =
      phi.dart (show WholePlaneDart (shiftWordInt W t) from
        (wholePlaneEdgeι (shiftWordInt W t) 0 d.1, d.2))
    rw [phi.dart_apply]
    change (uibhbotFutureEdge k W d.1, d.2) =
      (phi.edge (wholePlaneEdgeι (shiftWordInt W t) 0 d.1), d.2)
    simp only [uibhbotFutureEdge, phi.iota_edge, t]
  have hVh' : BoundaryHitWitnesses
      (fun i => uibhbotFutureCode k W (i + 1)) := by
    simpa only [hstream] using hVh
  have hboundary (j : ℤ) :
      futureMapBoundaryDart
          (fun i => uibhbotFutureCode k W (i + 1)) h j =
        futureMapBoundaryDart (shiftedStream V 0) hVh j := by
    have hh : h = hVh' := Subsingleton.elim _ _
    rw [hh]
    simp only [hstream]
  have hstep' :
      wholePlaneFaceSucc W H
          (uibhbotFutureSubmapDartEquiv k W h
            (futureMapBoundaryDart
              (fun i => uibhbotFutureCode k W (i + 1)) h j)).1 =
        (uibhbotFutureSubmapDartEquiv k W h
          (futureMapBoundaryDart
            (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1))).1 := by
    have hφ := wholePlaneStartIso_faceSucc W t phi H hV
      (wholePlaneDartι V 0
        (futureMapBoundaryDart (shiftedStream V 0) hVh j))
    rw [hmap, hmap]
    rw [hboundary j, hboundary (j - 1)]
    simpa only [V, phi.dart_apply, wholePlaneDartι] using
      hφ.symm.trans (congrArg phi.dart hstep)
  change ∃ n : ℕ, 0 < n ∧
    (wholePlaneFaceSucc W H)^[n]
        (uibhbotFutureSubmapDartEquiv k W h
          (futureMapBoundaryDart
            (fun i => uibhbotFutureCode k W (i + 1)) h j)).1 =
      (uibhbotFutureSubmapDartEquiv k W h
        (futureMapBoundaryDart
          (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1))).1 ∧
    ∀ m : ℕ, 0 < m → m < n →
      ((wholePlaneFaceSucc W H)^[m]
        (uibhbotFutureSubmapDartEquiv k W h
          (futureMapBoundaryDart
            (fun i => uibhbotFutureCode k W (i + 1)) h j)).1).1 ∉
        (uibhbotFutureSubmap k W h).edges
  refine ⟨1, by norm_num, ?_, ?_⟩
  · change wholePlaneFaceSucc W H
      (uibhbotFutureSubmapDartEquiv k W h
        (futureMapBoundaryDart
          (fun i => uibhbotFutureCode k W (i + 1)) h j)).1 = _
    exact hstep'
  · intro m hm0 hm1
    omega

/-- Helper toward Lemma 5.10. For every start time, a negative external
future dart has the preceding future boundary dart as its first return. -/
theorem ae_uibhbotFuturePlaneGeometricSide_externalFaceNext_negative :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ _hfin : ∀ v : ℕ, {e : ℕ | ∃ n,
              e < (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).nextEdge ∧
                ((kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).west e = v ∨
                  (kmswStage (fun i => uibhbotFutureCode k W (i + 1)) n).east e = v)}.Finite,
              ∀ j : ℤ, j ≤ -1 →
                (uibhbotFuturePlaneGeometricSide k W h H).faceNext
                  (futureMapBoundaryDart
                    (fun i => uibhbotFutureCode k W (i + 1)) h j)
                  (futureMapBoundaryDart
                    (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1)) := by
  filter_upwards [
    ae_uibhbotFuturePlaneGeometricSide_externalFaceNext_negative_nonpositiveStart,
    ae_uibhbotFuturePlaneGeometricSide_externalFaceNext_negative_positiveStart]
    with W hnonpos hpos k h H _hfin j hj
  by_cases ht : uibhbotBoundaryHitTime k W ≤ 0
  · exact hnonpos k h H _hfin ht j hj
  · exact hpos k h H _hfin (by omega) j hj























end DirectedDistances.RandomWalk
