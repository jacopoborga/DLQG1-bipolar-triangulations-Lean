module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.M0CutPresence

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source: -/
@[expose] def m0CutReachable (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (u v : WholePlaneVertex W) : Prop :=
  ∃ n, m0CutReachableLength (m0CutDirectedStep W H S) n u v

/-- Cut-level characterization of `thm-busemann`, Theorem 1.4 in -/
@[expose] def m0CutIsBoundaryBusemannSDP (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (x : ℤ → WholePlaneVertex W) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W, Function.Injective y →
      (∀ j, m0CutReachable W H S (x k) (y j) ∧
        m0CutReachable W H S (x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
          X k' - X k =
            ((m0CutSDP W H S (x k') (y j)).toNat : ℤ) -
              ((m0CutSDP W H S (x k) (y j)).toNat : ℤ)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
cut LDP values are finite on the reachable pairs, as asserted by the `∃ n n'`
clauses. -/
@[expose] def m0CutIsBoundaryBusemannLDP (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (x : ℤ → WholePlaneVertex W) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W,
      Function.Injective y →
      (∀ j, m0CutReachable W H S (x k) (y j) ∧
        m0CutReachable W H S (x k') (y j)) →
        ∃ N, ∀ j, N ≤ j →
          ∃ n n' : ℕ,
            m0CutLDP W H S (x k') (y j) =
                (((n : ℕ∞) : WithBot ℕ∞)) ∧
              m0CutLDP W H S (x k) (y j) =
                (((n' : ℕ∞) : WithBot ℕ∞)) ∧
              X k' - X k = (n : ℤ) - (n' : ℤ)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
run-zero vertex image. -/
theorem m0Cut_reachable_target_is_vertex (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h)
    {a : ℕ} {v : WholePlaneVertex W}
    (hr : m0CutReachable W H S (wholePlaneVertexι W 0 a) v) :
    ∃ b, wholePlaneVertexι W 0 b = v := by
  rcases hr with ⟨n, hn⟩
  cases n with
  | zero => exact ⟨a, hn⟩
  | succ n =>
    obtain ⟨u, _, hs⟩ := hn
    obtain ⟨e, _, _, hv⟩ :=
      (m0Cut_directedStep_iff_present W H h hLL S hS u v).mp hs
    exact ⟨edgeEast (shiftedStream W 0) e, hv⟩

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source: -/
theorem m0Cut_reachable_iff_present (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h)
    (u v : ℕ) :
    m0CutReachable W H S (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) ↔
      Reachable (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩ := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨p, _⟩ :=
      (m0Cut_reachableLength_iff_presentPath W H h hLL S hS n u v).mp hn
    exact ⟨p⟩
  · rintro ⟨p⟩
    refine ⟨p.length, ?_⟩
    exact (m0Cut_reachableLength_iff_presentPath W H h hLL S hS
      p.length u v).mpr ⟨p, rfl⟩

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
finite natural value supplied by `PresentPathLengthsBounded`. -/
theorem m0Cut_ldp_eq_finiteNat (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h)
    (hbound : PresentPathLengthsBounded (w := shiftedStream W 0))
    (u v : ℕ)
    (hr : m0CutReachable W H S (wholePlaneVertexι W 0 u)
      (wholePlaneVertexι W 0 v)) :
    m0CutLDP W H S (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
      (((presentLdpFiniteNat hbound
        ((m0Cut_reachable_iff_present W H h hLL S hS u v).mp hr) : ℕ∞) :
          WithBot ℕ∞)) := by
  let hp := (m0Cut_reachable_iff_present W H h hLL S hS u v).mp hr
  obtain ⟨p, hlong⟩ := exists_isLongest_of_bddAbove (hbound _ _ hp) hp
  calc
    m0CutLDP W H S (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
        presentLdp (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩ :=
      m0Cut_ldp_eq_present W H h hLL S hS u v
    _ = (((p.length : ℕ∞) : WithBot ℕ∞)) := presentLdp_eq_length hlong
    _ = (((presentLdpFiniteNat hbound hp : ℕ∞) : WithBot ℕ∞)) := by
      rw [presentLdpFiniteNat_eq_length hbound hp hlong]

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source: -/
theorem m0Cut_isBoundaryBusemannSDP_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h)
    (X : ℤ → ℤ) :
    m0CutIsBoundaryBusemannSDP W H S
      (fun k => wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k)) X ↔
      IsBoundaryBusemannSDP (boundaryPresentVertex (shiftedStream W 0) h) X := by
  let x : ℤ → WholePlaneVertex W := fun k =>
    wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)
  let xrun : ℤ → PresentVertex (shiftedStream W 0) :=
    boundaryPresentVertex (shiftedStream W 0) h
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    intro k k' y hy hyr
    let ycut : ℕ → WholePlaneVertex W := fun j =>
      wholePlaneVertexι W 0 (y j).id
    have hycut : Function.Injective ycut := by
      intro i j hij
      apply hy
      cases hi : y i with
      | mk a =>
        cases hj : y j with
        | mk b =>
          have hab : a = b := by
            have hids := wholePlaneVertexι_injective W 0 hij
            simpa [hi, hj] using hids
          subst b
          rfl
    have hyrcut (j : ℕ) : m0CutReachable W H S (x k) (ycut j) ∧
        m0CutReachable W H S (x k') (ycut j) := by
      cases y j
      constructor
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k) (y j).id).mpr
        simpa only [boundaryPresentVertex] using (hyr j).1
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k') (y j).id).mpr
        simpa only [boundaryPresentVertex] using (hyr j).2
    obtain ⟨N, hN⟩ := hc.2 k k' ycut hycut hyrcut
    refine ⟨N, fun j hj => ?_⟩
    have heq := hN j hj
    change X k' - X k =
      ((m0CutSDP W H S (wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k'))
        (wholePlaneVertexι W 0 (y j).id)).toNat : ℤ) -
      ((m0CutSDP W H S (wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k))
        (wholePlaneVertexι W 0 (y j).id)).toNat : ℤ) at heq
    rw [m0Cut_sdp_eq_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k') (y j).id,
        m0Cut_sdp_eq_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k) (y j).id] at heq
    change X k' - X k =
      ((sdp (⟨boundaryVertex (shiftedStream W 0) h k'⟩ :
        PresentVertex (shiftedStream W 0)) (y j)).toNat : ℤ) -
      ((sdp (⟨boundaryVertex (shiftedStream W 0) h k⟩ :
        PresentVertex (shiftedStream W 0)) (y j)).toNat : ℤ)
    exact heq
  · intro hr
    refine ⟨hr.1, ?_⟩
    intro k k' y hy hyr
    let z : ℕ → ℕ := fun j => Classical.choose (by
      have ht := (hyr j).1
      change m0CutReachable W H S
        (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k))
        (y j) at ht
      exact m0Cut_reachable_target_is_vertex W H h hLL S hS ht)
    have hz (j : ℕ) : wholePlaneVertexι W 0 (z j) = y j :=
      Classical.choose_spec (by
        have ht := (hyr j).1
        change m0CutReachable W H S
          (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k))
          (y j) at ht
        exact m0Cut_reachable_target_is_vertex W H h hLL S hS ht)
    let y' : ℕ → PresentVertex (shiftedStream W 0) := fun j => ⟨z j⟩
    have hy' : Function.Injective y' := by
      intro i j hij
      apply hy
      have hzij : z i = z j := congrArg PresentVertex.id hij
      calc
        y i = wholePlaneVertexι W 0 (z i) := (hz i).symm
        _ = wholePlaneVertexι W 0 (z j) := congrArg (wholePlaneVertexι W 0) hzij
        _ = y j := hz j
    have hyr' (j : ℕ) : Reachable (xrun k) (y' j) ∧
        Reachable (xrun k') (y' j) := by
      constructor
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k) (z j)).mp
        have ht := (hyr j).1
        rw [← hz j] at ht
        exact ht
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k') (z j)).mp
        have ht := (hyr j).2
        rw [← hz j] at ht
        exact ht
    obtain ⟨N, hN⟩ := hr.2 k k' y' hy' hyr'
    refine ⟨N, fun j hj => ?_⟩
    have heq := hN j hj
    rw [← hz j]
    have hxk' : boundaryPresentVertex (shiftedStream W 0) h k' =
        (⟨boundaryVertex (shiftedStream W 0) h k'⟩ :
          PresentVertex (shiftedStream W 0)) := rfl
    have hxk : boundaryPresentVertex (shiftedStream W 0) h k =
        (⟨boundaryVertex (shiftedStream W 0) h k⟩ :
          PresentVertex (shiftedStream W 0)) := rfl
    rw [hxk', hxk] at heq
    change X k' - X k =
      ((sdp (⟨boundaryVertex (shiftedStream W 0) h k'⟩ :
        PresentVertex (shiftedStream W 0)) (⟨z j⟩ :
        PresentVertex (shiftedStream W 0))).toNat : ℤ) -
      ((sdp (⟨boundaryVertex (shiftedStream W 0) h k⟩ :
        PresentVertex (shiftedStream W 0)) (⟨z j⟩ :
        PresentVertex (shiftedStream W 0))).toNat : ℤ) at heq
    change X k' - X k =
      ((m0CutSDP W H S (wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k'))
        (wholePlaneVertexι W 0 (z j))).toNat : ℤ) -
      ((m0CutSDP W H S (wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k))
        (wholePlaneVertexι W 0 (z j))).toNat : ℤ)
    rw [m0Cut_sdp_eq_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k') (z j),
        m0Cut_sdp_eq_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k) (z j)]
    exact heq

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source: -/
theorem m0Cut_isBoundaryBusemannLDP_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h)
    (hbound : PresentPathLengthsBounded (w := shiftedStream W 0))
    (X : ℤ → ℤ) :
    m0CutIsBoundaryBusemannLDP W H S
      (fun k => wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k)) X ↔
      IsBoundaryBusemannLDP hbound
        (boundaryPresentVertex (shiftedStream W 0) h) X := by
  let x : ℤ → WholePlaneVertex W := fun k =>
    wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)
  let xrun : ℤ → PresentVertex (shiftedStream W 0) :=
    boundaryPresentVertex (shiftedStream W 0) h
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    intro k k' y hy hyr
    let ycut : ℕ → WholePlaneVertex W := fun j =>
      wholePlaneVertexι W 0 (y j).id
    have hycut : Function.Injective ycut := by
      intro i j hij
      apply hy
      cases hi : y i with
      | mk a =>
        cases hj : y j with
        | mk b =>
          have hab : a = b := by
            have hids := wholePlaneVertexι_injective W 0 hij
            simpa [hi, hj] using hids
          subst b
          rfl
    have hyrcut (j : ℕ) : m0CutReachable W H S (x k) (ycut j) ∧
        m0CutReachable W H S (x k') (ycut j) := by
      cases y j
      constructor
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k) (y j).id).mpr
        simpa only [boundaryPresentVertex] using (hyr j).1
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k') (y j).id).mpr
        simpa only [boundaryPresentVertex] using (hyr j).2
    obtain ⟨N, hN⟩ := hc.2 k k' ycut hycut hyrcut
    refine ⟨N, fun j hj => ?_⟩
    obtain ⟨n, n', hcut', hcut, hdiff⟩ := hN j hj
    have hp' : Reachable (xrun k') (y j) := (hyr j).2
    have hp : Reachable (xrun k) (y j) := (hyr j).1
    have hproof' : hp' =
        (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k') (y j).id).mp (hyrcut j).2 :=
      Subsingleton.elim _ _
    have hproof : hp =
        (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k) (y j).id).mp (hyrcut j).1 :=
      Subsingleton.elim _ _
    have hfinite' := m0Cut_ldp_eq_finiteNat W H h hLL S hS hbound
      (boundaryVertex (shiftedStream W 0) h k') (y j).id (hyrcut j).2
    rw [← hproof'] at hfinite'
    have hfinite := m0Cut_ldp_eq_finiteNat W H h hLL S hS hbound
      (boundaryVertex (shiftedStream W 0) h k) (y j).id (hyrcut j).1
    rw [← hproof] at hfinite
    have hfiniteCut' : m0CutLDP W H S (x k') (ycut j) =
        (((presentLdpFiniteNat hbound hp' : ℕ∞) : WithBot ℕ∞)) := by
      exact hfinite'
    have hfiniteCut : m0CutLDP W H S (x k) (ycut j) =
        (((presentLdpFiniteNat hbound hp : ℕ∞) : WithBot ℕ∞)) := by
      exact hfinite
    have hn' : n = presentLdpFiniteNat hbound hp' := by
      have hc' := hcut'.symm.trans hfiniteCut'
      have hnat : (n : ℕ∞) = (presentLdpFiniteNat hbound hp' : ℕ∞) :=
        WithBot.coe_injective hc'
      exact_mod_cast hnat
    have hn : n' = presentLdpFiniteNat hbound hp := by
      have hc' := hcut.symm.trans hfiniteCut
      have hnat : (n' : ℕ∞) = (presentLdpFiniteNat hbound hp : ℕ∞) :=
        WithBot.coe_injective hc'
      exact_mod_cast hnat
    have hdiff' : (n' : ℤ) = (presentLdpFiniteNat hbound hp : ℤ) :=
      congrArg (fun q : ℕ => (q : ℤ)) hn
    have hdiff'' : (n : ℤ) = (presentLdpFiniteNat hbound hp' : ℤ) :=
      congrArg (fun q : ℕ => (q : ℤ)) hn'
    rw [hdiff'', hdiff'] at hdiff
    exact hdiff
  · intro hr
    refine ⟨hr.1, ?_⟩
    intro k k' y hy hyr
    let z : ℕ → ℕ := fun j => Classical.choose (by
      have ht := (hyr j).1
      change m0CutReachable W H S
        (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k))
        (y j) at ht
      exact m0Cut_reachable_target_is_vertex W H h hLL S hS ht)
    have hz (j : ℕ) : wholePlaneVertexι W 0 (z j) = y j :=
      Classical.choose_spec (by
        have ht := (hyr j).1
        change m0CutReachable W H S
          (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k))
          (y j) at ht
        exact m0Cut_reachable_target_is_vertex W H h hLL S hS ht)
    let y' : ℕ → PresentVertex (shiftedStream W 0) := fun j => ⟨z j⟩
    have hy' : Function.Injective y' := by
      intro i j hij
      apply hy
      have hzij : z i = z j := congrArg PresentVertex.id hij
      calc
        y i = wholePlaneVertexι W 0 (z i) := (hz i).symm
        _ = wholePlaneVertexι W 0 (z j) := congrArg (wholePlaneVertexι W 0) hzij
        _ = y j := hz j
    have hyr' (j : ℕ) : Reachable (xrun k) (y' j) ∧
        Reachable (xrun k') (y' j) := by
      constructor
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k) (z j)).mp
        have ht := (hyr j).1
        rw [← hz j] at ht
        exact ht
      · apply (m0Cut_reachable_iff_present W H h hLL S hS
          (boundaryVertex (shiftedStream W 0) h k') (z j)).mp
        have ht := (hyr j).2
        rw [← hz j] at ht
        exact ht
    obtain ⟨N, hN⟩ := hr.2 k k' y' hy' hyr'
    refine ⟨N, fun j hj => ?_⟩
    have hdiff := hN j hj
    have hp' := (hyr' j).2
    have hp := (hyr' j).1
    have hcutReach' : m0CutReachable W H S (x k') (y j) := (hyr j).2
    have hcutReach : m0CutReachable W H S (x k) (y j) := (hyr j).1
    have hfinite' := m0Cut_ldp_eq_finiteNat W H h hLL S hS hbound
      (boundaryVertex (shiftedStream W 0) h k') (z j) (by
        rw [hz j]
        exact hcutReach')
    have hfinite := m0Cut_ldp_eq_finiteNat W H h hLL S hS hbound
      (boundaryVertex (shiftedStream W 0) h k) (z j) (by
        rw [hz j]
        exact hcutReach)
    have hproof' : hp' = (m0Cut_reachable_iff_present W H h hLL S hS
        (boundaryVertex (shiftedStream W 0) h k') (z j)).mp (by
          rw [hz j]
          exact hcutReach') := Subsingleton.elim _ _
    rw [← hproof'] at hfinite'
    have hproof : hp = (m0Cut_reachable_iff_present W H h hLL S hS
        (boundaryVertex (shiftedStream W 0) h k) (z j)).mp (by
          rw [hz j]
          exact hcutReach) := Subsingleton.elim _ _
    rw [← hproof] at hfinite
    refine ⟨presentLdpFiniteNat hbound hp', presentLdpFiniteNat hbound hp, ?_,
      ?_, hdiff⟩
    · rw [← hz j]
      change m0CutLDP W H S
        (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k'))
        (wholePlaneVertexι W 0 (z j)) =
          (((presentLdpFiniteNat hbound hp' : ℕ∞) : WithBot ℕ∞))
      exact hfinite'
    · rw [← hz j]
      change m0CutLDP W H S
        (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k))
        (wholePlaneVertexι W 0 (z j)) =
          (((presentLdpFiniteNat hbound hp : ℕ∞) : WithBot ℕ∞))
      exact hfinite

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source: -/
theorem m0Cut_existsUnique_isBoundaryBusemannSDP_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h) :
    (∃! X, m0CutIsBoundaryBusemannSDP W H S
      (fun k => wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k)) X) ↔
    (∃! X, IsBoundaryBusemannSDP
      (boundaryPresentVertex (shiftedStream W 0) h) X) := by
  constructor
  · rintro ⟨X, hX, hu⟩
    refine ⟨X, (m0Cut_isBoundaryBusemannSDP_iff W H h hLL S hS X).mp hX, ?_⟩
    intro Y hY
    apply hu
    exact (m0Cut_isBoundaryBusemannSDP_iff W H h hLL S hS Y).mpr hY
  · rintro ⟨X, hX, hu⟩
    refine ⟨X, (m0Cut_isBoundaryBusemannSDP_iff W H h hLL S hS X).mpr hX, ?_⟩
    intro Y hY
    apply hu
    exact (m0Cut_isBoundaryBusemannSDP_iff W H h hLL S hS Y).mp hY

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source: -/
theorem m0Cut_existsUnique_isBoundaryBusemannLDP_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h)
    (hbound : PresentPathLengthsBounded (w := shiftedStream W 0)) :
    (∃! X, m0CutIsBoundaryBusemannLDP W H S
      (fun k => wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h k)) X) ↔
    (∃! X, IsBoundaryBusemannLDP hbound
      (boundaryPresentVertex (shiftedStream W 0) h) X) := by
  constructor
  · rintro ⟨X, hX, hu⟩
    refine ⟨X, (m0Cut_isBoundaryBusemannLDP_iff W H h hLL S hS hbound X).mp hX,
      ?_⟩
    intro Y hY
    apply hu
    exact (m0Cut_isBoundaryBusemannLDP_iff W H h hLL S hS hbound Y).mpr hY
  · rintro ⟨X, hX, hu⟩
    refine ⟨X, (m0Cut_isBoundaryBusemannLDP_iff W H h hLL S hS hbound X).mpr hX,
      ?_⟩
    intro Y hY
    apply hu
    exact (m0Cut_isBoundaryBusemannLDP_iff W H h hLL S hS hbound Y).mp hY

end DirectedDistances.KMSW
