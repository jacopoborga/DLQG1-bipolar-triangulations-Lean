/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceAmbientSelectorBridge4

/-! At an actual incoming corner, the first retained dart in a nonempty clockwise
scan step is an ambient positive iterate with no retained dart in between.
The iterate formulation treats the rotation cyclically, including a scan that
passes through the end of a chosen linear listing of the darts. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Xdp.Sdp

/-- Helper toward Lemma 5.6: the first side dart reached from an actual
incoming corner in a nonempty stored clockwise scan is the ambient clockwise
first return to the side's retained darts. The positive iterate and the
excluded intermediate darts make the cyclic wrap explicit. -/
theorem m0GeodesicSide_adjacentIncomingScan_firstStep_ambientFirstReturn
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (i : ℕ)
    (a : GeometricSideCell (m0GeodesicSide hp (P k) .left))
    (f : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left))
    (n : ℕ)
    (hincoming : geometricSideRayIncomingCorner
      (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) i a)
    (hscan : geometricSideClockwiseScan
      (m0GeodesicSide hp (P k) .left) a f n)
    (hn : 0 < n) :
    ∃ (d e : {d : ℕ × Bool //
        d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}),
      a = .inr d ∧ f 1 = .inr e ∧
      ∃ r : ℕ, 0 < r ∧
        ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[r]
          (wholePlaneDartι W 0 d.val) = wholePlaneDartι W 0 e.val ∧
        ∀ t : ℕ, 0 < t → t < r →
          ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[t]
            (wholePlaneDartι W 0 d.val) ∉
              wholePlaneDartι W 0 '' {x : ℕ × Bool |
                x.1 ∈ (m0GeodesicSide hp (P k) .left).edges} := by
  have hcornerDart : ∃ inc : {d : ℕ × Bool //
      d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}, a = .inr inc := by
    cases i with
    | zero =>
      exact ⟨⟨(m0GeodesicSide hp (P k) .left).boundary 1,
        m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩,
        (m0GeodesicSide_adjacent_incomingCorner_zero hp P k hcontain a).1
          hincoming⟩
    | succ j =>
      exact ⟨⟨((P (k - 1)).codePath.edge j, true), (hcontain j).1⟩,
        (m0GeodesicSide_adjacent_incomingCorner_succ hp P k hcontain j a).1
          hincoming⟩
  obtain ⟨inc, hinc⟩ := hcornerDart
  obtain ⟨d, e, hf0, hf1, r, hr, hend, hskip⟩ :=
    m0GeodesicSide_clockwiseScan_step_ambientFirstReturn hp (P k) .left
      hscan 0 hn
  have hinc_d : inc = d := by
    have heq : Sum.inr inc = Sum.inr d :=
      hinc.symm.trans (hscan.1.symm.trans hf0)
    exact Sum.inr.inj heq
  have hstart : a = .inr d := by
    rw [← hinc_d]
    exact hinc
  exact ⟨d, e, hstart, hf1, r, hr, hend, hskip⟩

/-- Helper toward Lemma 5.6: the realized adjacent ray's incoming scan is
nonempty, and its first step is the ambient clockwise first return. The
incoming dart has reversal bit `true` (including the exterior-boundary start),
while the selected outgoing dart has reversal bit `false`. -/
theorem m0GeodesicSide_adjacentIncomingScan_firstStep
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (i : ℕ) :
    ∃ (a : GeometricSideCell (m0GeodesicSide hp (P k) .left))
      (f : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)) (n : ℕ),
      geometricSideRayIncomingCorner (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) i a ∧
      geometricSideClockwiseScan (m0GeodesicSide hp (P k) .left) a f n ∧
      f n = m0GeodesicSideAdjacentDarts hp P k hcontain i ∧
      0 < n ∧
      ∃ (d e : {d : ℕ × Bool //
          d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}),
        a = .inr d ∧ f 1 = .inr e ∧
        ∃ r : ℕ, 0 < r ∧
          ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[r]
            (wholePlaneDartι W 0 d.val) = wholePlaneDartι W 0 e.val ∧
          ∀ t : ℕ, 0 < t → t < r →
            ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[t]
              (wholePlaneDartι W 0 d.val) ∉
                wholePlaneDartι W 0 '' {x : ℕ × Bool |
                  x.1 ∈ (m0GeodesicSide hp (P k) .left).edges} := by
  obtain ⟨a, f, n, hincoming, hscan, hend⟩ :=
    m0GeodesicSide_adjacent_incomingScan hp P k hcontain i
  have hne : a ≠ m0GeodesicSideAdjacentDarts hp P k hcontain i := by
    intro heq
    cases i with
    | zero =>
      have hcorner :=
        (m0GeodesicSide_adjacent_incomingCorner_zero hp P k hcontain a).1
          hincoming
      have hsum :
          (Sum.inr (⟨(m0GeodesicSide hp (P k) .left).boundary 1,
            m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩ :
              {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) :
            GeometricSideCell (m0GeodesicSide hp (P k) .left)) =
          Sum.inr (⟨((P (k - 1)).codePath.edge 0, false), (hcontain 0).1⟩ :
            {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) := by
        simpa [m0GeodesicSideAdjacentDarts] using hcorner.symm.trans heq
      have hsub := Sum.inr.inj hsum
      have hb := congrArg (fun x => x.val.2) hsub
      cases hb
    | succ j =>
      have hcorner :=
        (m0GeodesicSide_adjacent_incomingCorner_succ hp P k hcontain j a).1
          hincoming
      have hsum :
          (Sum.inr (⟨((P (k - 1)).codePath.edge j, true), (hcontain j).1⟩ :
            {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) :
            GeometricSideCell (m0GeodesicSide hp (P k) .left)) =
          Sum.inr (⟨((P (k - 1)).codePath.edge (j + 1), false),
            (hcontain (j + 1)).1⟩ :
            {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) := by
        simpa [m0GeodesicSideAdjacentDarts] using hcorner.symm.trans heq
      have hsub := Sum.inr.inj hsum
      have hb := congrArg (fun x => x.val.2) hsub
      cases hb
  have hn : 0 < n := by
    by_contra hnot
    have hz : n = 0 := by omega
    apply hne
    calc
      a = f 0 := hscan.1.symm
      _ = f n := by rw [hz]
      _ = m0GeodesicSideAdjacentDarts hp P k hcontain i := hend
  obtain ⟨d, e, hstart, hnext, r, hr, hendAmbient, hskip⟩ :=
    m0GeodesicSide_adjacentIncomingScan_firstStep_ambientFirstReturn
      hp P k hcontain i a f n hincoming hscan hn
  exact ⟨a, f, n, hincoming, hscan, hend, hn,
    d, e, hstart, hnext, r, hr, hendAmbient, hskip⟩

/-- Helper toward Lemma 5.6: if a qualifying side candidate agrees with the
selected ray up to index `i`, its dart at `i` does not occur earlier than the
selected dart in the chosen retained-dart scan. This is the candidate-relative
order statement before identifying scan order with ambient trace order. -/
theorem intrinsicallyLeftmostAdjacentRay_competitor_notEarlierInScan
    {M : GeometricSideSubmap} {longest : Bool}
    {v d : ℕ → GeometricSideCell M}
    (hselect : IntrinsicallyLeftmostAdjacentRay M longest v d)
    (i : ℕ) {v' d' : ℕ → GeometricSideCell M}
    (hcandidate : geometricSideAdjacentGeodesicCandidate M longest v' d')
    (hpref : ∀ j, j < i → d' j = d j) :
    ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
      geometricSideRayIncomingCorner M d i a ∧
      geometricSideClockwiseScan M a f n ∧ f n = d i ∧
      ∀ j, j < n → f j ≠ d' i := by
  obtain ⟨a, f, n, hincoming, hscan, hend, hfirst⟩ := hselect.2 i
  exact ⟨a, f, n, hincoming, hscan, hend,
    fun j hj => hfirst v' d' hcandidate hpref j hj⟩















































































end DirectedDistances.PaperProofs.Section5
