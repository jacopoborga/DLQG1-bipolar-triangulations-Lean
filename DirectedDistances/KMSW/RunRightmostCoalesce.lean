module

public import DirectedDistances.KMSW.RunRightmostRayExists
public import DirectedDistances.KMSW.RunRightmostDescent
public import DirectedDistances.KMSW.RunRightBoundaryChain
public import DirectedDistances.KMSW.RunBoundaryVertexLabels

/-! Helper toward Lemma 3.10 (lem-uibot-bdy, C4 intrinsic reading: coalescence of
rightmost directed paths in m_{n,inf}); not a paper result. Sources: -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, C4 intrinsic reading: coalescence of
rightmost directed paths in m_{n,inf}); not a paper result. Sources:
Shifting a rightmost ray preserves its edge identities and selected edges. -/
def kmswRunRightmostRay_shift {w : ℕ → Fin 3} {hfin : KMSWFiniteIncidence w}
    (P : KMSWRunRightmostRay w hfin) (m : ℕ) : KMSWRunRightmostRay w hfin :=
  { vertex := fun i => P.vertex (m + i)
    edge := fun i => P.edge (m + i)
    rightmost := fun i => P.rightmost (m + i)
    target := fun i => by
      simpa only [Nat.add_assoc] using P.target (m + i) }

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, C4 intrinsic reading: coalescence of
rightmost directed paths in m_{n,inf}); not a paper result. Sources:
Every intrinsic rightmost ray reaches the positive right-boundary ray after its
first edge is shifted to an active terminal. -/
theorem kmswRunRightmostRay_hits_boundaryChain (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w)
    (P : KMSWRunRightmostRay w hfin) :
    ∃ i k, 1 ≤ i ∧ 1 ≤ k ∧
      P.vertex i = (kmswRunRightBoundaryRay w hfin h).vertex (k - 1) := by
  obtain ⟨n, he, hp⟩ := (P.rightmost 0).1
  obtain ⟨t, _, hactive⟩ := kmswStage_present_eq_active w n (P.edge 0) he hp
  have hstart : P.vertex 1 = edgeEast w (act w t) := by
    calc
      P.vertex 1 = edgeEast w (P.edge 0) := (P.target 0).symm
      _ = edgeEast w (act w t) := congrArg (edgeEast w) hactive.symm
  let P1 := kmswRunRightmostRay_shift P 1
  have hstart1 : P1.vertex 0 = edgeEast w (act w t) := by
    simpa [P1, kmswRunRightmostRay_shift] using hstart
  obtain ⟨i, j, _, hhit⟩ :=
    kmswRunRightmostRay_hits_rightBoundary w hfin h P1 t hstart1
  have hboundary :
      edgeEast w (kmswRightBoundaryEdge w j) =
        (kmswRunRightBoundaryRay w hfin h).vertex j := by
    simp only [kmswRunRightBoundaryRay]
    exact (kmswRightBoundaryEdge_hit_endpoints w h j).2
  refine ⟨i + 1, j + 1, by omega, by omega, ?_⟩
  have hh := hhit.trans hboundary
  simpa [P1, kmswRunRightmostRay_shift, Nat.add_comm] using hh

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, C4 intrinsic reading: coalescence of
rightmost directed paths in m_{n,inf}); not a paper result. Sources:
Two rays sharing a vertex agree in both vertices and edge identities thereafter. -/
theorem kmswRunRightmostRays_agree_full_after_common_vertex
    {w : ℕ → Fin 3} {hfin : KMSWFiniteIncidence w}
    (P Q : KMSWRunRightmostRay w hfin) (i j : ℕ)
    (h : P.vertex i = Q.vertex j) :
    ∀ t, P.vertex (i + t) = Q.vertex (j + t) ∧
      P.edge (i + t) = Q.edge (j + t) := by
  intro t
  have hv := kmswRunRightmostRays_agree_after_common_vertex P Q i j h t
  have he := kmswRunRightmostOutAt_unique w hfin (P.vertex (i + t))
    (P.rightmost (i + t)) (by rw [hv]; exact Q.rightmost (j + t))
  exact ⟨hv, he⟩

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, C4 intrinsic reading: coalescence of
rightmost directed paths in m_{n,inf}); not a paper result. Sources:
Any two intrinsic rightmost rays coalesce at positive indices, including their
edge sequences, by meeting the same right-boundary ray. -/
theorem kmswRunRightmostRays_coalesce (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w)
    (P Q : KMSWRunRightmostRay w hfin) :
    ∃ s s', 0 < s ∧ 0 < s' ∧
      ∀ t, P.vertex (s + t) = Q.vertex (s' + t) ∧
        P.edge (s + t) = Q.edge (s' + t) := by
  let B := kmswRunRightBoundaryRay w hfin h
  obtain ⟨i, k, hi, hk, hP⟩ := kmswRunRightmostRay_hits_boundaryChain w hfin h P
  obtain ⟨j, k', hj, hk', hQ⟩ := kmswRunRightmostRay_hits_boundaryChain w hfin h Q
  let a := k - 1
  let b := k' - 1
  let c := max a b
  have hac : a ≤ c := Nat.le_max_left _ _
  have hbc : b ≤ c := Nat.le_max_right _ _
  have hpt := kmswRunRightmostRays_agree_full_after_common_vertex P B i a hP
  have hqt := kmswRunRightmostRays_agree_full_after_common_vertex Q B j b hQ
  refine ⟨i + (c - a), j + (c - b), by omega, by omega, ?_⟩
  intro t
  have hpt' := hpt (c - a + t)
  have hqt' := hqt (c - b + t)
  have hpt'' : P.vertex ((i + (c - a)) + t) = B.vertex (c + t) ∧
      P.edge ((i + (c - a)) + t) = B.edge (c + t) := by
    simpa only [← Nat.add_assoc, Nat.add_sub_of_le hac] using hpt'
  have hqt'' : Q.vertex ((j + (c - b)) + t) = B.vertex (c + t) ∧
      Q.edge ((j + (c - b)) + t) = B.edge (c + t) := by
    simpa only [← Nat.add_assoc, Nat.add_sub_of_le hbc] using hqt'
  exact ⟨hpt''.1.trans hqt''.1.symm, hpt''.2.trans hqt''.2.symm⟩

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, C4 intrinsic reading: coalescence of
rightmost directed paths in m_{n,inf}); not a paper result. Sources:
Boundary-started rays satisfy the same positive-index coalescence conclusion. -/
theorem kmswRunRightmostRays_coalesce_from_boundary (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w)
    (k k' : ℤ) (P Q : KMSWRunRightmostRay w hfin)
    (_hP : P.vertex 0 = boundaryVertex w h k)
    (_hQ : Q.vertex 0 = boundaryVertex w h k') :
    ∃ s s', 0 < s ∧ 0 < s' ∧
      ∀ t, P.vertex (s + t) = Q.vertex (s' + t) ∧
        P.edge (s + t) = Q.edge (s' + t) :=
  kmswRunRightmostRays_coalesce w hfin h P Q

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, C4 intrinsic reading: coalescence of
rightmost directed paths in m_{n,inf}); not a paper result. Sources:
Under the imported C3 hypotheses, each boundary vertex starts a unique intrinsic
rightmost ray. -/
theorem kmswRunRightmostRay_existsUnique_from_boundary
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)))
    (k : ℤ) :
    ∃! R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      R.vertex 0 = boundaryVertex (shiftedStream W 0) h k := by
  obtain ⟨R, hR⟩ := kmswRunRightmostRay_exists' W H h hLL P
    (boundaryVertex (shiftedStream W 0) h k)
  refine ⟨R, hR, ?_⟩
  intro S hS
  have hv0 := kmswRunRightmostRays_agree_after_common_vertex R S 0 0
    (hR.trans hS.symm)
  have hv (i : ℕ) : R.vertex i = S.vertex i := by
    simpa only [Nat.zero_add] using hv0 i
  have he (i : ℕ) : R.edge i = S.edge i :=
    kmswRunRightmostOutAt_unique (w := shiftedStream W 0) (hfin := H.1 0)
      (R.vertex i) (R.rightmost i) (by rw [hv i]; exact S.rightmost i)
  cases R with
  | mk rv re rr rt =>
    cases S with
    | mk sv se sr st =>
      have hvertex : rv = sv := funext hv
      have hedge : re = se := funext he
      subst sv
      subst se
      rfl

end DirectedDistances.KMSW
