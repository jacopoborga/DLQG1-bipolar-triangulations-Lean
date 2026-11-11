module

public import DirectedDistances.KMSW.KMSWShift
public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.ActiveTimeMonotone
public import DirectedDistances.KMSW.BusemannFromCut
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.KMSWShiftEmbedding

/-! # First-step KMSW transport for the LDP recursion

Finite-stage calculations for the three possibilities of `w 0` in
source-level boundary and limiting-path transport is kept separate from these
one-step state identities. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- The first global stage after a left code step, including its present root -/
theorem firstStage_left (w : ℕ → Fin 3) (h : w 0 = 0) :
    (kmswStage w 1).nextVertex = 3 ∧
    (kmswStage w 1).nextEdge = 3 ∧
    (kmswStage w 1).active = 1 ∧
    (kmswStage w 1).UL = [1] ∧
    (kmswStage w 1).LL = [2] ∧
    (kmswStage w 1).present 0 = true ∧
    (kmswStage w 1).present 1 = true ∧
    (kmswStage w 1).present 2 = false ∧
    (kmswStage w 1).west 1 = 2 ∧
    (kmswStage w 1).east 1 = 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, h, kmswStepOfStep, kmswInit,
    State.addEdge]

/-- The first global stage after an up code step, including the missing -/
theorem firstStage_up (w : ℕ → Fin 3) (h : w 0 = 1) :
    (kmswStage w 1).nextVertex = 3 ∧
    (kmswStage w 1).nextEdge = 3 ∧
    (kmswStage w 1).active = 1 ∧
    (kmswStage w 1).UL = [1] ∧
    (kmswStage w 1).UR = [2] ∧
    (kmswStage w 1).present 0 = true ∧
    (kmswStage w 1).present 1 = true ∧
    (kmswStage w 1).present 2 = false ∧
    (kmswStage w 1).west 1 = 0 ∧
    (kmswStage w 1).east 1 = 2 ∧
    (kmswStage w 1).west 2 = 2 ∧
    (kmswStage w 1).east 2 = 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, h, kmswStepOfStep, kmswInit,
    State.addEdge]

/-- The first global stage after a down code step, including activation of a -/
theorem firstStage_down (w : ℕ → Fin 3) (h : w 0 = 2) :
    (kmswStage w 1).nextVertex = 3 ∧
    (kmswStage w 1).nextEdge = 2 ∧
    (kmswStage w 1).active = 1 ∧
    (kmswStage w 1).UL = [0, 1] ∧
    (kmswStage w 1).LR = [0, 1] ∧
    (kmswStage w 1).present 0 = true ∧
    (kmswStage w 1).present 1 = true ∧
    (kmswStage w 1).west 1 = 1 ∧
    (kmswStage w 1).east 1 = 2 := by
  simp [kmswStage, kmswStep, kmswCodeStep, h, kmswStepOfStep, kmswInit,
    State.addEdge]

/-- At the first shifted stage, its initial root edge simulates the global
active edge created or activated at time one (`def-kmsw`, -/
theorem shiftedRoot_simulates_firstStage (w : ℕ → Fin 3) :
    Sim kmswInit (kmswStage w 1)
      (kmswShiftRootEdgeNatMap w 1) (kmswShiftRootVertexNatMap w 1) :=
  kmswShiftSim_init w 1

/-- The shifted run started from the explicit global first stage agrees with
the global run at every later stage (`def-kmsw`, -/
theorem shiftedRun_from_firstStage (w : ℕ → Fin 3) (m : ℕ) :
    kmswRun (kmswStage w 1) (fun i => w (1 + i)) m = kmswStage w (1 + m) := by
  simpa using kmswRun_shift_eq_stage w 1 m

/-- The horizontal walk coordinate of the shifted code is the global
coordinate translated by the first step (`eqn-kmsw-bdy`, -/
theorem shiftedL_eq_translated (w : ℕ → Fin 3) (n : ℕ) :
    L (fun i => w (i + 1)) n = L w (n + 1) - L w 1 := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
      have hs : L (fun i => w (i + 1)) (n + 1) =
          L (fun i => w (i + 1)) n +
            (RandomWalk.lazyTwoDimensionalStep (w (n + 1))).1 := by
        exact Finset.sum_range_succ _ _
      have hg : L w (n + 2) =
          L w (n + 1) + (RandomWalk.lazyTwoDimensionalStep (w (n + 1))).1 := by
        exact Finset.sum_range_succ _ _
      rw [hs, ih, hg]
      ring

/-- The vertical walk coordinate of the shifted code is the global
coordinate translated by the first step (`eqn-kmsw-bdy`, -/
theorem shiftedR_eq_translated (w : ℕ → Fin 3) (n : ℕ) :
    R (fun i => w (i + 1)) n = R w (n + 1) - R w 1 := by
  induction n with
  | zero => simp [R]
  | succ n ih =>
      have hs : R (fun i => w (i + 1)) (n + 1) =
          R (fun i => w (i + 1)) n +
            (RandomWalk.lazyTwoDimensionalStep (w (n + 1))).2 := by
        exact Finset.sum_range_succ _ _
      have hg : R w (n + 2) =
          R w (n + 1) + (RandomWalk.lazyTwoDimensionalStep (w (n + 1))).2 := by
        exact Finset.sum_range_succ _ _
      rw [hs, ih, hg]
      ring

/-- For a nonpositive boundary index, `boundaryHitTime` is the least
horizontal-coordinate hit time (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryHitTime_left_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
  unfold boundaryHitTime
  simp only [dif_neg (by omega : k ≠ 0), dif_neg (by omega : ¬ 0 < k)]

/-- For a positive boundary index, `boundaryHitTime` is the least
vertical-coordinate hit time (`eqn-bdy-vertex-kmsw`, -/
theorem boundaryHitTime_right_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    boundaryHitTime w h k = Nat.find (h.rightHit k hk) := by
  unfold boundaryHitTime
  simp only [dif_neg (by omega : k ≠ 0), dif_pos (by omega : 0 < k)]

/-- Translating a sequence by one time step translates its first-hit time by
one, provided the target is not already hit at time zero -/
theorem firstHit_shift_add_one {f : ℕ → ℤ} {a : ℤ}
    (hzero : f 0 ≠ a)
    (hglobal : ∃ n, f n = a)
    (hshift : ∃ n, f (n + 1) = a) :
    Nat.find hshift + 1 = Nat.find hglobal := by
  let m := Nat.find hglobal
  have hfm : f m = a := Nat.find_spec hglobal
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    exact hzero (hm0 ▸ hfm)
  let n := m - 1
  have hmn : m = n + 1 := by
    dsimp [n]
    omega
  have hshiftAtN : f (n + 1) = a := by
    rw [← hmn]
    exact hfm
  have hle : Nat.find hshift ≤ n := Nat.find_min' hshift hshiftAtN
  have hge : n ≤ Nat.find hshift := by
    by_contra hlt
    have hlt' : Nat.find hshift + 1 < m := by omega
    exact (Nat.find_min hglobal hlt') (Nat.find_spec hshift)
  change Nat.find hshift + 1 = m
  rw [hmn, Nat.le_antisymm hle hge]

/-- Equivalent time-indexed hit predicates have the same least hit time. -/
theorem natFind_eq_of_iff {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hiff : ∀ n, p n ↔ q n)
    (hp : ∃ n, p n) (hq : ∃ n, q n) :
    Nat.find hp = Nat.find hq := by
  apply Nat.le_antisymm
  · exact Nat.find_min' hp ((hiff (Nat.find hq)).2 (Nat.find_spec hq))
  · exact Nat.find_min' hq ((hiff (Nat.find hp)).1 (Nat.find_spec hp))

/-- First horizontal coordinate hits in the shifted code correspond to the
same global horizontal level shifted by `L w 1` (`eqn-kmsw-bdy`, -/
theorem shiftedL_firstHit_add_one (w : ℕ → Fin 3) (c : ℤ)
    (hlevel : c + L w 1 ≠ 0)
    (hglobal : ∃ n, L w n = c + L w 1) :
    Nat.find (show ∃ n, L (fun i => w (i + 1)) n = c from by
      obtain ⟨m, hm⟩ := hglobal
      have hm0 : m ≠ 0 := by
        intro h
        subst m
        have hz : L w 0 = 0 := by simp [L]
        rw [hz] at hm
        exact hlevel hm.symm
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      refine ⟨m - 1, ?_⟩
      rw [shiftedL_eq_translated]
      have hmn : m - 1 + 1 = m := by omega
      rw [hmn, hm]
      ring) + 1 = Nat.find hglobal := by
  have hzero : L w 0 ≠ c + L w 1 := by
    intro h
    have hz : L w 0 = 0 := by simp [L]
    rw [hz] at h
    exact hlevel h.symm
  have hshift : ∃ n, L w (n + 1) = c + L w 1 := by
    obtain ⟨m, hm⟩ := hglobal
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      have hz : L w 0 = 0 := by simp [L]
      rw [hz] at hm
      exact hlevel hm.symm
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    refine ⟨m - 1, ?_⟩
    have hmn : m - 1 + 1 = m := by omega
    rw [hmn]
    exact hm
  have hshift' : ∃ n, L (fun i => w (i + 1)) n = c := by
    obtain ⟨n, hn⟩ := hshift
    refine ⟨n, ?_⟩
    calc
      L (fun i => w (i + 1)) n = L w (n + 1) - L w 1 :=
        shiftedL_eq_translated w n
      _ = c := by rw [hn]; ring
  have hproof : hshift' = (show ∃ n, L (fun i => w (i + 1)) n = c from by
    obtain ⟨m, hm⟩ := hglobal
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      have hz : L w 0 = 0 := by simp [L]
      rw [hz] at hm
      exact hlevel hm.symm
    refine ⟨m - 1, ?_⟩
    rw [shiftedL_eq_translated]
    have hmn : m - 1 + 1 = m := by omega
    rw [hmn, hm]
    ring) := Subsingleton.elim _ _
  have hfindEq := congrArg Nat.find hproof
  have hpred : ∀ n, L (fun i => w (i + 1)) n = c ↔
      L w (n + 1) = c + L w 1 := by
    intro n
    rw [shiftedL_eq_translated]
    omega
  have hfindPred := natFind_eq_of_iff hpred hshift' hshift
  rw [← hfindEq, hfindPred]
  exact firstHit_shift_add_one hzero hglobal hshift

/-- After a first code step of type `(-1, 0)`, a shifted left-boundary hit
at index `k ≤ -1` occurs one step before the global hit at index `k - 1` -/
theorem shiftedLeftHitTime_leftStep (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) (k : ℤ) (hk : k ≤ -1) :
    boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
      boundaryHitTime w h0 (k - 1) := by
  have hL1 : L w 1 = -1 := by simp [L, hw]
  have hlevel : k + L w 1 ≠ 0 := by rw [hL1]; omega
  have hk' : k - 1 ≤ -1 := by omega
  have hglobal : ∃ n, L w n = k + L w 1 := by
    simpa [hL1, Int.sub_eq_add_neg] using h0.leftHit (k - 1) hk'
  have hcoord := shiftedL_firstHit_add_one w k hlevel hglobal
  rw [boundaryHitTime_left_eq_find (fun i => w (i + 1)) h1 hk,
    boundaryHitTime_left_eq_find w h0 hk']
  have hshiftFind : Nat.find (h1.leftHit k hk) =
      Nat.find (show ∃ n, L (fun i => w (i + 1)) n = k from by
        exact h1.leftHit k hk) := by
    congr 1
  have hglobalPred : ∀ n, L w n = k + L w 1 ↔ L w n = k - 1 := by
    intro n
    rw [hL1]
    omega
  have hglobalFind := natFind_eq_of_iff hglobalPred hglobal
    (h0.leftHit (k - 1) hk')
  rw [← hshiftFind, hglobalFind] at hcoord
  exact hcoord

/-- A shifted left-boundary hit at index `k` corresponds to the global
left-boundary hit at index `j` whenever the first horizontal increment is
`j - k` (`eqn-bdy-vertex-kmsw`, -/
theorem shiftedLeftHitTime_of_firstIncrement (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (k j : ℤ) (hk : k ≤ -1) (hj : j ≤ -1)
    (hstep : L w 1 = j - k) :
    boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
      boundaryHitTime w h0 j := by
  have hlevel : k + L w 1 ≠ 0 := by rw [hstep]; omega
  have hglobal : ∃ n, L w n = k + L w 1 := by
    obtain ⟨n, hn⟩ := h0.leftHit j hj
    exact ⟨n, by rw [hn, hstep]; omega⟩
  have hcoord := shiftedL_firstHit_add_one w k hlevel hglobal
  rw [boundaryHitTime_left_eq_find (fun i => w (i + 1)) h1 hk,
    boundaryHitTime_left_eq_find w h0 hj]
  have hproof : (show ∃ n, L (fun i => w (i + 1)) n = k from
      h1.leftHit k hk) = h1.leftHit k hk := Subsingleton.elim _ _
  have hshiftFind := congrArg Nat.find hproof
  have hpred : ∀ n, L w n = k + L w 1 ↔ L w n = j := by
    intro n
    rw [hstep]
    omega
  have hglobalFind := natFind_eq_of_iff hpred hglobal (h0.leftHit j hj)
  rw [← hshiftFind, hglobalFind] at hcoord
  exact hcoord

/-- First vertical coordinate hits in the shifted code correspond to the
same global vertical level shifted by `R w 1` (`eqn-kmsw-bdy`, -/
theorem shiftedR_firstHit_add_one (w : ℕ → Fin 3) (c : ℤ)
    (hlevel : c + R w 1 ≠ 0)
    (hglobal : ∃ n, R w n = c + R w 1) :
    Nat.find (show ∃ n, R (fun i => w (i + 1)) n = c from by
      obtain ⟨m, hm⟩ := hglobal
      have hm0 : m ≠ 0 := by
        intro h
        subst m
        have hz : R w 0 = 0 := by simp [R]
        rw [hz] at hm
        exact hlevel hm.symm
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      refine ⟨m - 1, ?_⟩
      rw [shiftedR_eq_translated]
      have hmn : m - 1 + 1 = m := by omega
      rw [hmn, hm]
      ring) + 1 = Nat.find hglobal := by
  have hzero : R w 0 ≠ c + R w 1 := by
    intro h
    have hz : R w 0 = 0 := by simp [R]
    rw [hz] at h
    exact hlevel h.symm
  have hshift : ∃ n, R w (n + 1) = c + R w 1 := by
    obtain ⟨m, hm⟩ := hglobal
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      have hz : R w 0 = 0 := by simp [R]
      rw [hz] at hm
      exact hlevel hm.symm
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    refine ⟨m - 1, ?_⟩
    have hmn : m - 1 + 1 = m := by omega
    rw [hmn]
    exact hm
  have hshift' : ∃ n, R (fun i => w (i + 1)) n = c := by
    obtain ⟨n, hn⟩ := hshift
    refine ⟨n, ?_⟩
    calc
      R (fun i => w (i + 1)) n = R w (n + 1) - R w 1 :=
        shiftedR_eq_translated w n
      _ = c := by rw [hn]; ring
  have hproof : hshift' = (show ∃ n, R (fun i => w (i + 1)) n = c from by
    obtain ⟨m, hm⟩ := hglobal
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      have hz : R w 0 = 0 := by simp [R]
      rw [hz] at hm
      exact hlevel hm.symm
    refine ⟨m - 1, ?_⟩
    rw [shiftedR_eq_translated]
    have hmn : m - 1 + 1 = m := by omega
    rw [hmn, hm]
    ring) := Subsingleton.elim _ _
  have hfindEq := congrArg Nat.find hproof
  have hpred : ∀ n, R (fun i => w (i + 1)) n = c ↔
      R w (n + 1) = c + R w 1 := by
    intro n
    rw [shiftedR_eq_translated]
    omega
  have hfindPred := natFind_eq_of_iff hpred hshift' hshift
  rw [← hfindEq, hfindPred]
  exact firstHit_shift_add_one hzero hglobal hshift

/-- A shifted right-boundary hit at index `k` corresponds to the global
right-boundary hit at index `j` whenever the first vertical increment is
`k - j` (`eqn-bdy-vertex-kmsw`, -/
theorem shiftedRightHitTime_of_firstIncrement (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (k j : ℤ) (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hstep : R w 1 = k - j) :
    boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
      boundaryHitTime w h0 j := by
  have htarget : -k + R w 1 = -j := by rw [hstep]; omega
  have hlevel : -k + R w 1 ≠ 0 := by rw [htarget]; omega
  have hglobal : ∃ n, R w n = -k + R w 1 := by
    obtain ⟨n, hn⟩ := h0.rightHit j hj
    exact ⟨n, by rw [hn, htarget]⟩
  have hcoord := shiftedR_firstHit_add_one w (-k) hlevel hglobal
  rw [boundaryHitTime_right_eq_find (fun i => w (i + 1)) h1 hk,
    boundaryHitTime_right_eq_find w h0 hj]
  have hproof : (show ∃ n, R (fun i => w (i + 1)) n = -k from
      h1.rightHit k hk) = h1.rightHit k hk := Subsingleton.elim _ _
  have hshiftFind := congrArg Nat.find hproof
  have hpred : ∀ n, R w n = -k + R w 1 ↔ R w n = -j := by
    intro n
    rw [htarget]
  have hglobalFind := natFind_eq_of_iff hpred hglobal (h0.rightHit j hj)
  rw [← hshiftFind, hglobalFind] at hcoord
  exact hcoord

/-- Boundary hit times after a left code step: the shifted left boundary
index `k` corresponds to global index `k - 1`, and the positive right indices
keep their labels (`eqn-bdy-vertex-kmsw`, -/
theorem firstStepHitTimes_left (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) :
    (∀ k : ℤ, k ≤ -1 →
      boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
        boundaryHitTime w h0 (k - 1)) ∧
    (∀ k : ℤ, 1 ≤ k →
      boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
        boundaryHitTime w h0 k) := by
  have hL : L w 1 = -1 := by simp [L, hw]
  have hR : R w 1 = 0 := by simp [R, hw]
  constructor
  · intro k hk
    apply shiftedLeftHitTime_of_firstIncrement w h0 h1 k (k - 1) hk (by omega)
    rw [hL]
    omega
  · intro k hk
    apply shiftedRightHitTime_of_firstIncrement w h0 h1 k k hk hk
    rw [hR]
    omega

/-- Boundary hit times after an up code step: the negative left indices keep
their labels, while right indices `k ≥ 2` correspond to global index `k - 1` -/
theorem firstStepHitTimes_up (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) :
    (∀ k : ℤ, k ≤ -1 →
      boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
        boundaryHitTime w h0 k) ∧
    (∀ k : ℤ, 2 ≤ k →
      boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
        boundaryHitTime w h0 (k - 1)) := by
  have hL : L w 1 = 0 := by simp [L, hw]
  have hR : R w 1 = 1 := by simp [R, hw]
  constructor
  · intro k hk
    apply shiftedLeftHitTime_of_firstIncrement w h0 h1 k k hk hk
    rw [hL]
    omega
  · intro k hk
    apply shiftedRightHitTime_of_firstIncrement w h0 h1 k (k - 1) (by omega) (by omega)
    rw [hR]
    omega

/-- Boundary hit times after a down code step: left indices `k ≤ -2`
correspond to global index `k + 1`, while positive right indices correspond to
`k + 1` (`eqn-bdy-vertex-kmsw`, -/
theorem firstStepHitTimes_down (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) :
    (∀ k : ℤ, k ≤ -2 →
      boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
        boundaryHitTime w h0 (k + 1)) ∧
    (∀ k : ℤ, 1 ≤ k →
      boundaryHitTime (fun i => w (i + 1)) h1 k + 1 =
        boundaryHitTime w h0 (k + 1)) := by
  have hL : L w 1 = 1 := by simp [L, hw]
  have hR : R w 1 = -1 := by simp [R, hw]
  constructor
  · intro k hk
    apply shiftedLeftHitTime_of_firstIncrement w h0 h1 k (k + 1) (by omega) (by omega)
    rw [hL]
    omega
  · intro k hk
    apply shiftedRightHitTime_of_firstIncrement w h0 h1 k (k + 1) hk (by omega)
    rw [hR]
    omega

/-- The arrow map induced on finite-stage quivers by a state simulation.
Every mapped edge remains allocated, present, and incident to the mapped -/
@[expose] def simStagePrefunctor (w : ℕ → Fin 3) (n : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim (kmswStage (fun i => w (i + 1)) n) (kmswStage w (n + 1)) eφ vφ) :
    Prefunctor (StagePresentVertex (fun i => w (i + 1)) n)
      (StagePresentVertex w (n + 1)) where
  obj a := ⟨vφ a.id⟩
  map {_ _} e :=
    ⟨eφ e.val, hsim.edge_bound e.val e.property.1,
      hsim.present e.val e.property.1 e.property.2.1,
      (hsim.incidence e.val e.property.1).1.trans
        (congrArg vφ e.property.2.2.1),
      (hsim.incidence e.val e.property.1).2.trans
        (congrArg vφ e.property.2.2.2)⟩

/-- The finite-stage path map induced by a state simulation preserves every
path length. -/
theorem simStagePrefunctor_length (w : ℕ → Fin 3) (n : ℕ)
    (eφ vφ : ℕ → ℕ)
    (hsim : Sim (kmswStage (fun i => w (i + 1)) n) (kmswStage w (n + 1)) eφ vφ)
    {a b : StagePresentVertex (fun i => w (i + 1)) n} (p : Path a b) :
    ((simStagePrefunctor w n eφ vφ hsim).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- Present paths in the shifted initial one-edge stage map to paths in the
first global stage with the same length (`def-kmsw`, -/
theorem shiftedInitialStage_path_length (w : ℕ → Fin 3)
    {a b : StagePresentVertex (fun i => w (i + 1)) 0} (p : Path a b) :
    ((simStagePrefunctor w 0 (kmswShiftRootEdgeNatMap w 1)
      (kmswShiftRootVertexNatMap w 1) (shiftedRoot_simulates_firstStage w)).mapPath p).length =
        p.length :=
  simStagePrefunctor_length w 0 (kmswShiftRootEdgeNatMap w 1)
    (kmswShiftRootVertexNatMap w 1) (shiftedRoot_simulates_firstStage w) p

/-- The finite-incidence producer consumed by the cut-based LDP construction:
activation order bounds the lengths of all present paths into a fixed -/
theorem presentPathLengthsBounded_of_finiteIncidence (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    PresentPathLengthsBounded (w := w) := by
  intro a b hr
  exact present_pathLengths_bddAbove w hfin a b

end DirectedDistances.Recursive
