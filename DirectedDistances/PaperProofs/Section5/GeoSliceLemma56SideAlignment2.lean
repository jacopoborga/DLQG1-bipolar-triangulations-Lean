/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SideAlignment




public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: the ambient witnesses in two slice witnesses
are proof-irrelevant. In particular, their geodesic fields can be transported
to the same dependent types. -/
theorem m0CutGeodesicSliceWitness_ambientData_eq
    {W : ℤ → Fin 3} {x : XDP}
    (s t : M0CutGeodesicSliceWitness W x) :
    s.H = t.H ∧ s.h = t.h ∧ s.hp = t.hp ∧ s.hLL = t.hLL := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Helper toward Lemma 5.6: two segment-geodesics selected by the cut-leftmost
predicate have the same edge stream even when their reference paths differ.
Only the left-boundary part of each closed-region comparison is used. -/
theorem m0CutGeodesicSlice_codePath_edge_eq_of_cutLeftmost
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (longest : Bool) (k : ℤ)
    (P Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (T U : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hP : Xdp.CutLeftmostXdp W H h hp hLL longest k P T)
    (hQ : Xdp.CutLeftmostXdp W H h hp hLL longest k Q U) :
    P.codePath.edge = Q.codePath.edge := by
  let w := shiftedStream W 0
  let hfam : ∀ n, ∃ A : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n A) := fun n =>
    ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  have hcontP : ∀ S : InfinitePresentPath w (boundaryPresentVertex w h k),
      (if longest then S.HasLongestSegments else S.HasShortestSegments) →
      pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
          (fun n => (S.edge n, false)) ⊆
        closedBetween
          (pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
            (fun n => (P.codePath.edge n, false)))
          (pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
            (fun n => (T.edge n, false))) := by
    cases longest with
    | true => exact (m0Cut_ldp_containment_iff W H h hp hLL k
        P.codePath.edge T.edge).mp hP
    | false => exact (Xdp.Sdp.m0Cut_sdp_containment_iff W H h hp hLL k
        P.codePath.edge T.edge).mp hP
  have hcontQ : ∀ S : InfinitePresentPath w (boundaryPresentVertex w h k),
      (if longest then S.HasLongestSegments else S.HasShortestSegments) →
      pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
          (fun n => (S.edge n, false)) ⊆
        closedBetween
          (pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
            (fun n => (Q.codePath.edge n, false)))
          (pathTrace (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w))
            (fun n => (U.edge n, false))) := by
    cases longest with
    | true => exact (m0Cut_ldp_containment_iff W H h hp hLL k
        Q.codePath.edge U.edge).mp hQ
    | false => exact (Xdp.Sdp.m0Cut_sdp_containment_iff W H h hp hLL k
        Q.codePath.edge U.edge).mp hQ
  have hPQ : Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf
      w (H.1 0) hfam P.codePath Q.codePath := by
    have hsub := hcontP Q.codePath Q.segments
    exact ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
      w (H.1 0) hfam (boundaryVertex w h k) P.codePath T Q.codePath).mp hsub).1
  have hQP : Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf
      w (H.1 0) hfam Q.codePath P.codePath := by
    have hsub := hcontQ P.codePath P.segments
    exact ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
      w (H.1 0) hfam (boundaryVertex w h k) Q.codePath U P.codePath).mp hsub).1
  exact Xdp.LeftmostXdpTransport.SharedDepartureArgRightOf.antisymm
    w (H.1 0) hfam P.codePath Q.codePath hPQ hQP

/-- Helper toward Lemma 5.6: the edge-stream comparison above identifies the
entire source paths, including their finite-prefix certificates. -/
theorem m0CutGeodesicSlice_codePath_eq_of_cutLeftmost
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (longest : Bool) (k : ℤ)
    (P Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (T U : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hP : Xdp.CutLeftmostXdp W H h hp hLL longest k P T)
    (hQ : Xdp.CutLeftmostXdp W H h hp hLL longest k Q U) :
    P.codePath = Q.codePath := by
  have he := m0CutGeodesicSlice_codePath_edge_eq_of_cutLeftmost W H h hp hLL
    longest k P Q T U hP hQ
  exact Xdp.LeftmostXdpTransport.infinitePresentPath_eq_of_edge_eq
    (shiftedStream W 0) P.codePath Q.codePath he.symm |>.symm

/-- Helper toward Lemma 5.6: arbitrary slice witnesses with the same stream
and index select the same source code path, after proof-irrelevance transport
of their ambient hypotheses. -/
theorem m0CutGeodesicSliceWitness_codePath_eq
    {W : ℤ → Fin 3} {x : XDP}
    (s t : M0CutGeodesicSliceWitness W x) (j : ℤ) :
    (s.P j).codePath = (t.P j).codePath := by
  obtain ⟨hH, hh, hhp, hLL⟩ := m0CutGeodesicSliceWitness_ambientData_eq s t
  cases hH
  cases hh
  cases hLL
  cases hhp
  exact m0CutGeodesicSlice_codePath_eq_of_cutLeftmost W s.H s.h s.hp s.hLL
    (if x = XDP.ldp then true else false) j (s.P j) (t.P j)
    (s.T j) (t.T j) (s.hleft j) (t.hleft j)

/-- Helper toward Lemma 5.6: the two geometric side classes at a fixed slice
index do not depend on which slice witness was selected. -/
theorem m0CutGeodesicSliceWitness_sideClass_eq
    {W : ℤ → Fin 3} {x : XDP}
    (s t : M0CutGeodesicSliceWitness W x) (j : ℤ) (side : ThinMapSide) :
    geometricSideClass (m0GeodesicSide s.hp (s.P j) side) =
      geometricSideClass (m0GeodesicSide t.hp (t.P j) side) := by
  obtain ⟨hH, hh, hhp, hLL⟩ := m0CutGeodesicSliceWitness_ambientData_eq s t
  cases hH
  cases hh
  cases hLL
  cases hhp
  have hcode := m0CutGeodesicSliceWitness_codePath_eq s t j
  have hP : s.P j = t.P j := by
    cases hleft : s.P j with
    | mk P hsegments hstart hstep =>
      cases hright : t.P j with
      | mk Q hsegments' hstart' hstep' =>
        have hpath : P = Q := by
          simpa [hleft, hright] using hcode
        cases hpath
        rfl
  rw [hP]






























end DirectedDistances.PaperProofs.Section5
