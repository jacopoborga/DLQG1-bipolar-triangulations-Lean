module

public import DirectedDistances.KMSW.WholePlaneShiftIso
public import DirectedDistances.KMSW.WholePlaneLeftmostIncoming
public import DirectedDistances.KMSW.WholePlaneBoundaryRayCoalescence
public import DirectedDistances.KMSW.WholePlaneIntegerRuns

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem wholePlaneVertexShift_runEmbed (W : ℤ → Fin 3) (n v : ℕ) :
    wholePlaneVertexShift W n
        (wholePlaneVertexι W 0 (kmswWindowVertexMapInf (shiftedStream W 0) n v)) =
      wholePlaneVertexι (shiftWord W n) 0 v := by
  rw [wholePlaneVertexShift_ι]
  have h := congrFun (wholePlaneVertexι_trans (shiftWord W n) 0 n (Nat.zero_le n)) v
  simpa only [Function.comp_apply, wholePlaneVertexTrans, Nat.sub_zero,
    ← shiftedStream_shiftWord W n 0, Nat.zero_add] using h

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem wholePlaneEdgeShift_runEmbed (W : ℤ → Fin 3) (n e : ℕ) :
    wholePlaneEdgeShift W n
        (wholePlaneEdgeι W 0 (kmswWindowEdgeMapInf (shiftedStream W 0) n e)) =
      wholePlaneEdgeι (shiftWord W n) 0 e := by
  rw [wholePlaneEdgeShift_ι]
  have h := congrFun (wholePlaneEdgeι_trans (shiftWord W n) 0 n (Nat.zero_le n)) e
  simpa only [Function.comp_apply, wholePlaneEdgeTrans, Nat.sub_zero,
    ← shiftedStream_shiftWord W n 0, Nat.zero_add] using h

private theorem shift_symm_pow (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n)) (k : ℕ)
    (e : WholePlaneEdge W) (b : Bool) :
    ((wholePlaneRotation (shiftWord W n) H').symm ^ k)
        (wholePlaneEdgeShift W n e, b) =
      (wholePlaneEdgeShift W n
        (((wholePlaneRotation W H).symm ^ k) (e, b)).1,
        (((wholePlaneRotation W H).symm ^ k) (e, b)).2) := by
  exact (wholePlaneRotation_symm_pow_shift W n H' k (e, b)).symm

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem wholePlaneRightmostOutgoingAt_shift (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (v : WholePlaneVertex W) (e : WholePlaneEdge W) :
    wholePlaneRightmostOutgoingAt W H v e ↔
      wholePlaneRightmostOutgoingAt (shiftWord W n) H'
        (wholePlaneVertexShift W n v) (wholePlaneEdgeShift W n e) := by
  have hv : wholePlaneVertexShift W n (wholePlaneEdgeWest W e) =
      wholePlaneVertexShift W n v ↔ wholePlaneEdgeWest W e = v :=
    ⟨fun h => (wholePlaneVertexShift_bijective W n).1 h,
      congrArg (wholePlaneVertexShift W n)⟩
  simp only [wholePlaneRightmostOutgoingAt, shift_symm_pow W n H H',
    wholePlaneEdgePresent_shift, wholePlaneEdgeShift_west, hv]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem wholePlaneLeftmostIncomingAt_shift (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (v : WholePlaneVertex W) (e : WholePlaneEdge W) :
    wholePlaneLeftmostIncomingAt W H v e ↔
      wholePlaneLeftmostIncomingAt (shiftWord W n) H'
        (wholePlaneVertexShift W n v) (wholePlaneEdgeShift W n e) := by
  have hv : wholePlaneVertexShift W n (wholePlaneEdgeEast W e) =
      wholePlaneVertexShift W n v ↔ wholePlaneEdgeEast W e = v :=
    ⟨fun h => (wholePlaneVertexShift_bijective W n).1 h,
      congrArg (wholePlaneVertexShift W n)⟩
  simp only [wholePlaneLeftmostIncomingAt, shift_symm_pow W n H H',
    wholePlaneEdgePresent_shift, wholePlaneEdgeShift_east, hv]


/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
@[expose] def WholePlaneRightmostRay.shift (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (P : WholePlaneRightmostRay W H) : WholePlaneRightmostRay (shiftWord W n) H' where
  vertex i := wholePlaneVertexShift W n (P.vertex i)
  edge i := wholePlaneEdgeShift W n (P.edge i)
  rightmost i := (wholePlaneRightmostOutgoingAt_shift W n H H' _ _).mp (P.rightmost i)
  target i := (wholePlaneEdgeShift_east W n (P.edge i)).trans
    (congrArg (wholePlaneVertexShift W n) (P.target i))

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
@[expose] noncomputable def WholePlaneRightmostRay.unshift (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (P : WholePlaneRightmostRay (shiftWord W n) H') : WholePlaneRightmostRay W H where
  vertex i := (wholePlaneVertexShiftEquiv W n).symm (P.vertex i)
  edge i := (wholePlaneEdgeShiftEquiv W n).symm (P.edge i)
  rightmost i := by
    apply (wholePlaneRightmostOutgoingAt_shift W n H H' _ _).mpr
    change wholePlaneRightmostOutgoingAt (shiftWord W n) H'
      (wholePlaneVertexShiftEquiv W n ((wholePlaneVertexShiftEquiv W n).symm _))
      (wholePlaneEdgeShiftEquiv W n ((wholePlaneEdgeShiftEquiv W n).symm _))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact P.rightmost i
  target i := by
    apply (wholePlaneVertexShift_bijective W n).1
    rw [← wholePlaneEdgeShift_east]
    change wholePlaneEdgeEast (shiftWord W n)
        (wholePlaneEdgeShiftEquiv W n ((wholePlaneEdgeShiftEquiv W n).symm _)) =
      wholePlaneVertexShiftEquiv W n ((wholePlaneVertexShiftEquiv W n).symm _)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact P.target i

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem WholePlaneRightmostRay.shift_unshift_vertex (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (P : WholePlaneRightmostRay (shiftWord W n) H') (i : ℕ) :
    wholePlaneVertexShift W n ((P.unshift W n H H').vertex i) = P.vertex i :=
  (wholePlaneVertexShiftEquiv W n).apply_symm_apply _

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem WholePlaneRightmostRay.shift_unshift_edge (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (P : WholePlaneRightmostRay (shiftWord W n) H') (i : ℕ) :
    wholePlaneEdgeShift W n ((P.unshift W n H H').edge i) = P.edge i :=
  (wholePlaneEdgeShiftEquiv W n).apply_symm_apply _


/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem WholePlaneRightmostRay.shift_vertex (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (P : WholePlaneRightmostRay W H) (i : ℕ) :
    (P.shift W n H H').vertex i = wholePlaneVertexShift W n (P.vertex i) := rfl

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem WholePlaneRightmostRay.shift_edge (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (P : WholePlaneRightmostRay W H) (i : ℕ) :
    (P.shift W n H H').edge i = wholePlaneEdgeShift W n (P.edge i) := rfl

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem wholePlaneRightBoundary_rightmost_chain_start (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (h : BoundaryHitWitnesses (shiftedStream (shiftWord W n) 0)) :
    ∃ (v : ℕ → WholePlaneVertex W) (e : ℕ → WholePlaneEdge W),
      v 0 = wholePlaneVertexι W 0
        (kmswWindowVertexMapInf (shiftedStream W 0) n 1) ∧
      (∀ j : ℕ, e j = wholePlaneEdgeι W 0
        (kmswWindowEdgeMapInf (shiftedStream W 0) n
          (kmswRightBoundaryEdge (shiftedStream (shiftWord W n) 0) (j + 1)))) ∧
      ∀ j : ℕ, wholePlaneRightmostOutgoingAt W H (v j) (e j) ∧
        wholePlaneEdgeEast W (e j) = v (j + 1) := by
  obtain ⟨B, hzero, hedge⟩ :=
    wholePlaneRightmostRay_exists_root_terminal (shiftWord W n) H' 0 h
  let P := B.unshift W n H H'
  refine ⟨P.vertex, P.edge, ?_, ?_, fun j => ⟨P.rightmost j, P.target j⟩⟩
  · apply (wholePlaneVertexShift_bijective W n).1
    rw [wholePlaneVertexShift_runEmbed]
    exact (B.shift_unshift_vertex W n H H' 0).trans hzero
  · intro j
    apply (wholePlaneEdgeShift_bijective W n).1
    rw [wholePlaneEdgeShift_runEmbed]
    exact (B.shift_unshift_edge W n H H' j).trans (hedge j)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result.
The named hLL premise supplies incoming LL presence in the shifted word at N = 0
for every k ≤ 0, including k = 0. -/
theorem wholePlaneRightmostRays_coalesce_from_boundary_start (W : ℤ → Fin 3) (n : ℕ)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWord W n))
    (h : BoundaryHitWitnesses (shiftedStream (shiftWord W n) 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent (shiftWord W n)
      (wholePlaneEdgeι (shiftWord W n) 0
        (kmswLLCreatedEdge (shiftedStream (shiftWord W n) 0)
          (boundaryHitTime (shiftedStream (shiftWord W n) 0) h (k - 1)))))
    (k k' : ℤ) (P Q : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 = wholePlaneVertexι W 0
      (kmswWindowVertexMapInf (shiftedStream W 0) n
        (boundaryVertex (shiftedStream (shiftWord W n) 0) h k)))
    (hQ : Q.vertex 0 = wholePlaneVertexι W 0
      (kmswWindowVertexMapInf (shiftedStream W 0) n
        (boundaryVertex (shiftedStream (shiftWord W n) 0) h k'))) :
    ∃ s s', 0 < s ∧ 0 < s' ∧ ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
  have hp : (P.shift W n H H').vertex 0 = wholePlaneVertexι (shiftWord W n) 0
      (boundaryVertex (shiftedStream (shiftWord W n) 0) h k) := by
    rw [WholePlaneRightmostRay.shift_vertex, hP, wholePlaneVertexShift_runEmbed]
  have hq : (Q.shift W n H H').vertex 0 = wholePlaneVertexι (shiftWord W n) 0
      (boundaryVertex (shiftedStream (shiftWord W n) 0) h k') := by
    rw [WholePlaneRightmostRay.shift_vertex, hQ, wholePlaneVertexShift_runEmbed]
  obtain ⟨s, s', hs, hs', ht⟩ :=
    wholePlaneRightmostRays_coalesce_from_boundary_pos (shiftWord W n) H' 0 h hLL
      k k' (P.shift W n H H') (Q.shift W n H H') hp hq
  exact ⟨s, s', hs, hs', fun t => (wholePlaneVertexShift_bijective W n).1 (ht t)⟩

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
probability-one scope: under H / a.s.): transfer to paper starts n ≥ 0 via the cofinal shift
isomorphism; not the paper result. -/
theorem wholePlaneIID_ae_rightmostRays_coalesce_from_boundary_start :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∃ H : WholePlaneRotationHypothesis W,
      ∀ n : ℕ, ∃ h : BoundaryHitWitnesses (fun i : ℕ => W ((i : ℤ) + n)),
        ∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay W H),
          P.vertex 0 = wholePlaneVertexι W 0
            (kmswWindowVertexMapInf (shiftedStream W 0) n
              (boundaryVertex (fun i : ℕ => W ((i : ℤ) + n)) h k)) →
          Q.vertex 0 = wholePlaneVertexι W 0
            (kmswWindowVertexMapInf (shiftedStream W 0) n
              (boundaryVertex (fun i : ℕ => W ((i : ℤ) + n)) h k')) →
          ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
  have hzero : ∀ᵐ V ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis V,
        ∃ h : BoundaryHitWitnesses (shiftedStream V 0),
          ∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay V H),
            P.vertex 0 = wholePlaneVertexι V 0
              (boundaryVertex (shiftedStream V 0) h k) →
            Q.vertex 0 = wholePlaneVertexι V 0
              (boundaryVertex (shiftedStream V 0) h k') →
            ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
    filter_upwards [wholePlaneIID_ae_rightmostRays_coalesce_from_boundary] with V hv
    obtain ⟨H, hH⟩ := hv
    exact ⟨H, hH 0⟩
  have hall := wholePlaneIID_ae_shift_all _ hzero
  filter_upwards [wholePlaneIID_ae_rotationHypothesis, hall] with W H hh
  refine ⟨H, fun n => ?_⟩
  have hn : ∃ H' : WholePlaneRotationHypothesis (shiftWord W n),
      ∃ h : BoundaryHitWitnesses (shiftedStream (shiftWord W n) 0),
        ∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay (shiftWord W n) H'),
          P.vertex 0 = wholePlaneVertexι (shiftWord W n) 0
            (boundaryVertex (shiftedStream (shiftWord W n) 0) h k) →
          Q.vertex 0 = wholePlaneVertexι (shiftWord W n) 0
            (boundaryVertex (shiftedStream (shiftWord W n) 0) h k') →
          ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := hh (n : ℤ)
  obtain ⟨H', h, hc⟩ := hn
  have hstart : ∃ h : BoundaryHitWitnesses (shiftedStream (shiftWord W n) 0),
      ∀ (k k' : ℤ) (P Q : WholePlaneRightmostRay W H),
        P.vertex 0 = wholePlaneVertexι W 0
          (kmswWindowVertexMapInf (shiftedStream W 0) n
            (boundaryVertex (shiftedStream (shiftWord W n) 0) h k)) →
        Q.vertex 0 = wholePlaneVertexι W 0
          (kmswWindowVertexMapInf (shiftedStream W 0) n
            (boundaryVertex (shiftedStream (shiftWord W n) 0) h k')) →
        ∃ s s', ∀ t, P.vertex (s + t) = Q.vertex (s' + t) := by
    refine ⟨h, fun k k' P Q hP hQ => ?_⟩
    have hp : (P.shift W n H H').vertex 0 = wholePlaneVertexι (shiftWord W n) 0
        (boundaryVertex (shiftedStream (shiftWord W n) 0) h k) := by
      rw [WholePlaneRightmostRay.shift_vertex, hP, wholePlaneVertexShift_runEmbed]
    have hq : (Q.shift W n H H').vertex 0 = wholePlaneVertexι (shiftWord W n) 0
        (boundaryVertex (shiftedStream (shiftWord W n) 0) h k') := by
      rw [WholePlaneRightmostRay.shift_vertex, hQ, wholePlaneVertexShift_runEmbed]
    obtain ⟨s, s', ht⟩ := hc k k' (P.shift W n H H') (Q.shift W n H H') hp hq
    exact ⟨s, s', fun t => (wholePlaneVertexShift_bijective W n).1 (ht t)⟩
  have hu : (fun i : ℕ => W ((i : ℤ) + n)) =
      shiftedStream (shiftWord W n) 0 := integerRun_eq_shiftedStream_zero W (n : ℤ)
  simpa only [← hu] using hstart

end DirectedDistances.KMSW
