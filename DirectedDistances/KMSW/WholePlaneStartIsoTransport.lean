module

public import DirectedDistances.KMSW.WholePlaneStartIso
public import DirectedDistances.KMSW.WholePlaneRightmostRays
public import DirectedDistances.KMSW.M0CutSeam

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW



private theorem startIso_inversePow (W : ℤ → Fin 3) (n : ℤ)
    (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (k : ℕ) (d : WholePlaneDart (shiftWordInt W n)) :
    phi.dart (((wholePlaneRotation (shiftWordInt W n) H').symm ^ k) d) =
      ((wholePlaneRotation W H).symm ^ k) (phi.dart d) := by
  have hstep (x : WholePlaneDart (shiftWordInt W n)) :
      phi.dart ((wholePlaneRotation (shiftWordInt W n) H').symm x) =
        (wholePlaneRotation W H).symm (phi.dart x) := by
    have hr := phi.rot H H' ((wholePlaneRotation (shiftWordInt W n) H').symm x)
    rw [Equiv.apply_symm_apply] at hr
    calc
      phi.dart ((wholePlaneRotation (shiftWordInt W n) H').symm x) =
          (wholePlaneRotation W H).symm
            (wholePlaneRotation W H (phi.dart
              ((wholePlaneRotation (shiftWordInt W n) H').symm x))) := by
        rw [Equiv.symm_apply_apply]
      _ = (wholePlaneRotation W H).symm (phi.dart x) := by
        rw [← hr]
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
        hstep, ih]



theorem wholePlaneRightmostOutgoingAt_startIso_iff (W : ℤ → Fin 3)
    (n : ℤ) (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (v : WholePlaneVertex (shiftWordInt W n))
    (e : WholePlaneEdge (shiftWordInt W n)) :
    wholePlaneRightmostOutgoingAt W H (phi.vertex v) (phi.edge e) ↔
      wholePlaneRightmostOutgoingAt (shiftWordInt W n) H' v e := by
  have hend : wholePlaneEdgeWest W (phi.edge e) =
      phi.vertex (wholePlaneEdgeWest (shiftWordInt W n) e) := phi.west e
  have hbase : wholePlaneEdgeWest W (phi.edge e) = phi.vertex v ↔
      wholePlaneEdgeWest (shiftWordInt W n) e = v := by
    constructor
    · intro h
      apply phi.vertex.injective
      exact hend.symm.trans h
    · intro h
      rw [hend, h]
  have hpow (k : ℕ) (d : WholePlaneDart (shiftWordInt W n)) :
      phi.edge (((wholePlaneRotation (shiftWordInt W n) H').symm ^ k) d).1 =
        (((wholePlaneRotation W H).symm ^ k) (phi.edge d.1, d.2)).1 := by
    have ht := congrArg Prod.fst (startIso_inversePow W n phi H H' k d)
    simpa only [phi.dart_apply] using ht
  have hside (k : ℕ) (d : WholePlaneDart (shiftWordInt W n)) :
      (((wholePlaneRotation (shiftWordInt W n) H').symm ^ k) d).2 =
        (((wholePlaneRotation W H).symm ^ k) (phi.edge d.1, d.2)).2 := by
    have ht := congrArg Prod.snd (startIso_inversePow W n phi H H' k d)
    simpa only [phi.dart_apply] using ht
  unfold wholePlaneRightmostOutgoingAt
  constructor
  · rintro ⟨hp, hb, k, hk, hs, hpk, hmin⟩
    refine ⟨(phi.present e).mp hp, hbase.mp hb, k, hk, ?_, ?_, ?_⟩
    · rw [hside k (e, false)]
      exact hs
    · apply (phi.present _).mp
      rw [hpow k (e, false)]
      exact hpk
    · intro j hj hjk hpj
      apply hmin j hj hjk
      have hpW := (phi.present _).mpr hpj
      rw [hpow j (e, false)] at hpW
      exact hpW
  · rintro ⟨hp, hb, k, hk, hs, hpk, hmin⟩
    refine ⟨(phi.present e).mpr hp, hbase.mpr hb, k, hk, ?_, ?_, ?_⟩
    · rw [← hside k (e, false)]
      exact hs
    · have hpW := (phi.present _).mpr hpk
      rw [hpow k (e, false)] at hpW
      exact hpW
    · intro j hj hjk hpj
      apply hmin j hj hjk
      apply (phi.present _).mp
      rw [hpow j (e, false)]
      exact hpj



theorem wholePlaneLeftmostIncomingAt_startIso_iff (W : ℤ → Fin 3)
    (n : ℤ) (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (v : WholePlaneVertex (shiftWordInt W n))
    (e : WholePlaneEdge (shiftWordInt W n)) :
    wholePlaneLeftmostIncomingAt W H (phi.vertex v) (phi.edge e) ↔
      wholePlaneLeftmostIncomingAt (shiftWordInt W n) H' v e := by
  have hend : wholePlaneEdgeEast W (phi.edge e) =
      phi.vertex (wholePlaneEdgeEast (shiftWordInt W n) e) := phi.east e
  have hbase : wholePlaneEdgeEast W (phi.edge e) = phi.vertex v ↔
      wholePlaneEdgeEast (shiftWordInt W n) e = v := by
    constructor
    · intro h
      apply phi.vertex.injective
      exact hend.symm.trans h
    · intro h
      rw [hend, h]
  have hpow (k : ℕ) (d : WholePlaneDart (shiftWordInt W n)) :
      phi.edge (((wholePlaneRotation (shiftWordInt W n) H').symm ^ k) d).1 =
        (((wholePlaneRotation W H).symm ^ k) (phi.edge d.1, d.2)).1 := by
    have ht := congrArg Prod.fst (startIso_inversePow W n phi H H' k d)
    simpa only [phi.dart_apply] using ht
  have hside (k : ℕ) (d : WholePlaneDart (shiftWordInt W n)) :
      (((wholePlaneRotation (shiftWordInt W n) H').symm ^ k) d).2 =
        (((wholePlaneRotation W H).symm ^ k) (phi.edge d.1, d.2)).2 := by
    have ht := congrArg Prod.snd (startIso_inversePow W n phi H H' k d)
    simpa only [phi.dart_apply] using ht
  unfold wholePlaneLeftmostIncomingAt
  constructor
  · rintro ⟨hp, hb, k, hk, hs, hpk, hmin⟩
    refine ⟨(phi.present e).mp hp, hbase.mp hb, k, hk, ?_, ?_, ?_⟩
    · rw [hside k (e, true)]
      exact hs
    · apply (phi.present _).mp
      rw [hpow k (e, true)]
      exact hpk
    · intro j hj hjk hpj
      apply hmin j hj hjk
      have hpW := (phi.present _).mpr hpj
      rw [hpow j (e, true)] at hpW
      exact hpW
  · rintro ⟨hp, hb, k, hk, hs, hpk, hmin⟩
    refine ⟨(phi.present e).mpr hp, hbase.mpr hb, k, hk, ?_, ?_, ?_⟩
    · rw [← hside k (e, true)]
      exact hs
    · have hpW := (phi.present _).mpr hpk
      rw [hpow k (e, true)] at hpW
      exact hpW
    · intro j hj hjk hpj
      apply hmin j hj hjk
      apply (phi.present _).mp
      rw [hpow j (e, true)]
      exact hpj




theorem wholePlaneRightmostOutgoingAt_startIso_dart_iff (W : ℤ → Fin 3)
    (n : ℤ) (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (v : WholePlaneVertex (shiftWordInt W n))
    (d : WholePlaneDart (shiftWordInt W n)) :
    wholePlaneRightmostOutgoingAt W H (phi.vertex v) (phi.dart d).1 ↔
      wholePlaneRightmostOutgoingAt (shiftWordInt W n) H' v d.1 := by
  simpa only [phi.dart_apply] using
    wholePlaneRightmostOutgoingAt_startIso_iff W n phi H H' v d.1




theorem wholePlaneLeftmostIncomingAt_startIso_dart_iff (W : ℤ → Fin 3)
    (n : ℤ) (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (v : WholePlaneVertex (shiftWordInt W n))
    (d : WholePlaneDart (shiftWordInt W n)) :
    wholePlaneLeftmostIncomingAt W H (phi.vertex v) (phi.dart d).1 ↔
      wholePlaneLeftmostIncomingAt (shiftWordInt W n) H' v d.1 := by
  simpa only [phi.dart_apply] using
    wholePlaneLeftmostIncomingAt_startIso_iff W n phi H H' v d.1



@[expose] noncomputable def wholePlaneRightmostRay_startIso
    (W : ℤ → Fin 3) (n : ℤ) (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (P : WholePlaneRightmostRay (shiftWordInt W n) H') :
    WholePlaneRightmostRay W H where
  vertex i := phi.vertex (P.vertex i)
  edge i := phi.edge (P.edge i)
  rightmost i :=
    (wholePlaneRightmostOutgoingAt_startIso_iff W n phi H H'
      (P.vertex i) (P.edge i)).2 (P.rightmost i)
  target i := (phi.east (P.edge i)).trans (congrArg phi.vertex (P.target i))



@[expose] noncomputable def m0CutLeftmostChain_startIso
    (W : ℤ → Fin 3) (n : ℤ) (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (v : WholePlaneVertex (shiftWordInt W n))
    (Q : M0CutLeftmostChain (shiftWordInt W n) H' v) :
    M0CutLeftmostChain W H (phi.vertex v) where
  vertex i := phi.vertex (Q.vertex i)
  edge i := phi.edge (Q.edge i)
  endpoint := congrArg phi.vertex Q.endpoint
  leftmost i :=
    (wholePlaneLeftmostIncomingAt_startIso_iff W n phi H H'
      (Q.vertex i) (Q.edge i)).2 (Q.leftmost i)
  westEndpoint i := (phi.west (Q.edge i)).trans (congrArg phi.vertex (Q.westEndpoint i))



theorem wholePlaneRightmostRay_startIso_unique (W : ℤ → Fin 3)
    (n : ℤ) (phi : WholePlaneStartIso W n)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (P : WholePlaneRightmostRay (shiftWordInt W n) H')
    (huniq : ∀ Q : WholePlaneRightmostRay (shiftWordInt W n) H',
      Q.vertex 0 = P.vertex 0 →
        Q.vertex = P.vertex ∧ Q.edge = P.edge) :
    ∀ Q : WholePlaneRightmostRay W H,
      Q.vertex 0 = phi.vertex (P.vertex 0) →
        Q.vertex = (wholePlaneRightmostRay_startIso W n phi H H' P).vertex ∧
          Q.edge = (wholePlaneRightmostRay_startIso W n phi H H' P).edge := by
  intro Q hQ
  let Q' : WholePlaneRightmostRay (shiftWordInt W n) H' := {
    vertex := fun i => phi.vertex.symm (Q.vertex i)
    edge := fun i => phi.edge.symm (Q.edge i)
    rightmost := by
      intro i
      have hQ : wholePlaneRightmostOutgoingAt W H
          (phi.vertex (phi.vertex.symm (Q.vertex i)))
          (phi.edge (phi.edge.symm (Q.edge i))) := by
        simpa only [Equiv.apply_symm_apply] using Q.rightmost i
      exact (wholePlaneRightmostOutgoingAt_startIso_iff W n phi H H'
        (phi.vertex.symm (Q.vertex i)) (phi.edge.symm (Q.edge i))).mp hQ
    target := by
      intro i
      apply phi.vertex.injective
      calc
        phi.vertex (wholePlaneEdgeEast (shiftWordInt W n)
            (phi.edge.symm (Q.edge i))) = wholePlaneEdgeEast W (Q.edge i) := by
          rw [← phi.east (phi.edge.symm (Q.edge i)), Equiv.apply_symm_apply]
        _ = Q.vertex (i + 1) := Q.target i
        _ = phi.vertex (phi.vertex.symm (Q.vertex (i + 1))) :=
          (Equiv.apply_symm_apply _ _).symm }
  have hstart : Q'.vertex 0 = P.vertex 0 := by
    dsimp [Q']
    have := congrArg phi.vertex.symm hQ
    simpa using this
  obtain ⟨hv, he⟩ := huniq Q' hstart
  constructor
  · funext i
    have hi := congrArg phi.vertex (congrFun hv i)
    change Q.vertex i = phi.vertex (P.vertex i)
    simpa [Q'] using hi
  · funext i
    have hi := congrArg phi.edge (congrFun he i)
    change Q.edge i = phi.edge (P.edge i)
    simpa [Q'] using hi

end DirectedDistances.KMSW
