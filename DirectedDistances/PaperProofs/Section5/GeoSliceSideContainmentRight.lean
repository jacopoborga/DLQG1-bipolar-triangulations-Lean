/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLeftmostNonCrossing5
public import DirectedDistances.PaperProofs.Section5.GeoSliceSideContainment
public import DirectedDistances.PaperProofs.Section5.M0GeodesicSideCarrier

/-! # Right-side containment for geodesic slices -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}



theorem m0CutGeodesicPrecoalescenceEdges_mem_right_side_succ
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (j : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P j) (P (j + 1)) a b) :
    ∀ i < b,
      (P (j + 1)).codePath.edge i ∈ m0GeodesicSideEdges hp (P j) .right := by
  have hidx : (j + 1 : ℤ) - 1 = j := by omega
  have hab' : M0CutLeastEdgeCoalescence (P ((j + 1) - 1)) (P (j + 1)) a b := by
    rw [hidx]
    exact hab
  have hordered := m0CutAdjacentGeodesics_ordered_before_coalescence
    P T hleft (j + 1) a b hab'
  rw [hidx] at hordered
  exact hordered.2




theorem m0CutGeodesicRightSide_subset_succ
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (j : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (j + 1)) (P (j + 2)) a b) :
    m0GeodesicSideRegion hp (P (j + 2)) .right ⊆
      m0GeodesicSideRegion hp (P (j + 1)) .right := by
  have hidx : (j + 2 : ℤ) - 1 = j + 1 := by omega
  have hab' : M0CutLeastEdgeCoalescence
      (P ((j + 2) - 1)) (P (j + 2)) a b := by
    rw [hidx]
    exact hab
  have hordered := m0CutAdjacentGeodesics_ordered_before_coalescence
    P T hleft (j + 2) a b hab'
  rw [hidx] at hordered
  have htraceDisjoint :
      Disjoint (m0GeodesicLeftOpen hp (P (j + 1)))
        (m0GeodesicTrace hp (P (j + 2))) := by
    apply Set.disjoint_left.mpr
    intro z hzL hzT
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hzT
    by_cases hmb : m < b
    · have hright := hordered.2 m hmb hm
      exact hright.2 hzL
    · have hbm : b ≤ m := by omega
      let n := m - b
      have hbn : b + n = m := by dsimp [n]; omega
      have hedge := wholePlaneEdgeι_injective W 0 (hab.1 n)
      rw [hbn] at hedge
      have hnewOld : (P (j + 2)).codePath.edge m =
          (P (j + 1)).codePath.edge (a + n) := hedge.symm
      have hm' : z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
          (wholePlaneDartι W 0 ((P (j + 2)).codePath.edge m, false))).image := by
        simpa only [m0GeodesicSeam] using hm
      rw [hnewOld] at hm'
      have hzOld : z ∈ m0GeodesicTrace hp (P (j + 1)) :=
        m0Geodesic_arc_subset_trace hp (P (j + 1)) (a + n)
          (by simpa only [m0GeodesicSeam] using hm')
      exact (m0GeodesicLeftOpen_subset hp (P (j + 1)) hzL).2 hzOld
  have hsub : m0GeodesicLeftOpen hp (P (j + 1)) ⊆
      m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp (P (j + 2)) := by
    intro z hz
    exact ⟨(m0GeodesicLeftOpen_subset hp (P (j + 1)) hz).1,
      Set.disjoint_left.mp htraceDisjoint hz⟩
  let z := (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
    ((m0CutData W H h hLL).x j)
  have hprevIdx : (j + 1 : ℤ) - 1 = j := by omega
  have hzOld : z ∈ m0GeodesicLeftOpen hp (P (j + 1)) := by
    have hz := m0Geodesic_previous_pos_mem_leftOpen hp (P (j + 1))
    change (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x ((j + 1) - 1)) ∈ _ at hz
    rw [hprevIdx] at hz
    exact hz
  have hzAmbient : z ∈ m0GeodesicAmbientRegion W H h := by
    dsimp [z]
    rw [(m0CutData W H h hLL).x_eq h hLL j]
    exact m0Geodesic_pos_mem_ambient hp _
  have hzAbscissa : z.re = seamX (shiftedStream W 0) h (H.1 0) j := by
    dsimp [z]
    rw [(m0CutData W H h hLL).x_eq h hLL j, m0Geodesic_pos_runZero hp]
    rfl
  have hzWest : z.re < seamX (shiftedStream W 0) h (H.1 0) (j + 2) := by
    rw [hzAbscissa]
    exact seamX_strictMono (shiftedStream W 0) h (H.1 0) (by omega)
  have hzNew : z ∈ m0GeodesicLeftOpen hp (P (j + 2)) :=
    boundaryGluing_west_of_root_mem_leftOpen W h (j + 2) longest hp
      (P (j + 2)) hzAmbient hzWest
  have hcomponent : connectedComponentIn
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp (P (j + 2))) z =
        m0GeodesicLeftOpen hp (P (j + 2)) :=
    (connectedComponentIn_eq hzNew).symm
  have hleftOpen : m0GeodesicLeftOpen hp (P (j + 1)) ⊆
      m0GeodesicLeftOpen hp (P (j + 2)) := by
    have hcomponent' :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hzOld hsub
    rw [hcomponent] at hcomponent'
    exact hcomponent'
  intro q hq
  change q ∈ m0GeodesicAmbientRegion W H h \ m0GeodesicLeftOpen hp (P (j + 2)) at hq
  change q ∈ m0GeodesicAmbientRegion W H h \ m0GeodesicLeftOpen hp (P (j + 1))
  refine ⟨hq.1, ?_⟩
  intro hqOld
  have hqClosure : q ∈ closure (m0GeodesicLeftOpen hp (P (j + 2))) :=
    closure_mono hleftOpen (subset_closure hqOld)
  have hqNotTrace : q ∉ m0GeodesicTrace hp (P (j + 2)) := by
    intro hqTrace
    exact Set.disjoint_left.mp htraceDisjoint hqOld hqTrace
  have hqNew : q ∈ m0GeodesicLeftOpen hp (P (j + 2)) :=
    m0GeodesicLeftOpen_closure_inter_complement_subset hp (P (j + 2))
      ⟨hqClosure, ⟨hq.1, hqNotTrace⟩⟩
  exact hq.2 hqNew



















end DirectedDistances.PaperProofs.Section5
