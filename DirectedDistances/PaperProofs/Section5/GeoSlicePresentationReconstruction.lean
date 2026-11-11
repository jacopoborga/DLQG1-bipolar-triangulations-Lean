/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceSideRecognition
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Assembly2






public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: existence of an intrinsic first-admissible
adjacent ray is preserved by a complete marked-side isomorphism. This
transports existence, without selecting or identifying an ambient ray. -/
theorem intrinsicallyLeftmostAdjacentRay_exists_iff
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N)
    (longest : Bool) :
    (∃ v d : ℕ → GeometricSideCell M,
      IntrinsicallyLeftmostAdjacentRay M longest v d) ↔
    (∃ v d : ℕ → GeometricSideCell N,
      IntrinsicallyLeftmostAdjacentRay N longest v d) := by
  constructor
  · rintro ⟨v, d, hl⟩
    exact ⟨I.equiv ∘ v, I.equiv ∘ d,
      intrinsicallyLeftmostAdjacentRay_map I longest hl⟩
  · rintro ⟨v, d, hl⟩
    exact ⟨I.equiv.symm ∘ v, I.equiv.symm ∘ d,
      intrinsicallyLeftmostAdjacentRay_map (GeometricSideMarkedIso.symm I) longest hl⟩

/-- Helper toward Lemma 5.6: equality of complete marked-side classes
transports intrinsic-ray existence to any representative. The statement
retains vertices and darts separately, including parallel-edge identity. -/
theorem intrinsicallyLeftmostAdjacentRay_exists_iff_of_class_eq
    (M N : GeometricSideSubmap) (longest : Bool)
    (hc : geometricSideClass M = geometricSideClass N) :
    (∃ v d : ℕ → GeometricSideCell M,
      IntrinsicallyLeftmostAdjacentRay M longest v d) ↔
    (∃ v d : ℕ → GeometricSideCell N,
      IntrinsicallyLeftmostAdjacentRay N longest v d) := by
  obtain ⟨I⟩ := (geometricSideClass_eq_iff M N).1 hc
  exact intrinsicallyLeftmostAdjacentRay_exists_iff I longest

section Recognition

variable (hrecog :
    ∀ {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
      {h : BoundaryHitWitnesses (shiftedStream W 0)}
      {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
      (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
      (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
      (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k))
      (hleft : ∀ k : ℤ,
        Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
      (k : ℤ)
      (hcontain : ∀ n : ℕ,
        (P (k - 1)).codePath.edge n ∈
          (m0GeodesicSide hp (P k) .left).edges ∧
        ((P (k - 1)).codePath.initial n).1.id ∈
          (m0GeodesicSide hp (P k) .left).vertices),
      ∃ v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left),
        geometricSideAdjacentGeodesicCandidate
          (m0GeodesicSide hp (P k) .left) longest v d ∧
        IntrinsicallyLeftmostAdjacentRay
          (m0GeodesicSide hp (P k) .left) longest v d)

include hrecog in
/-- Helper toward Lemma 5.6: the exact recognition contract from
`GeoSliceSideRecognition` gives intrinsic-ray existence on one simultaneous
almost-sure event, for every integer cut and both metrics. The same event
supplies the ambient leftmost rays and least coalescence offsets. Existence
also transports to every representative of each left-side class. This does
not identify an intrinsic ray with the preceding ambient geodesic. -/
theorem m0GeodesicSide_ae_intrinsicRay_exists_of_recognition :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ j : ℤ, ∃ a b : ℕ,
          M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) ∧
        (∀ k : ℤ, ∀ N : GeometricSideSubmap,
          geometricSideClass (m0GeodesicSide hp (P k) .left) =
            geometricSideClass N →
          ∃ v d : ℕ → GeometricSideCell N,
            IntrinsicallyLeftmostAdjacentRay N longest v d) := by
  filter_upwards [m0Cut_ae_realizedLeftSideSlice_eq] with W hW
  obtain ⟨H, h, hLL, hp, hmode⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, hc, hcontain, _⟩ := hmode longest
  refine ⟨P, T, hleft, hc, ?_⟩
  intro k N hN
  obtain ⟨v, d, _, hl⟩ :=
    hrecog hp P T hleft k (hcontain (k - 1) k (by omega))
  exact (intrinsicallyLeftmostAdjacentRay_exists_iff_of_class_eq
    (m0GeodesicSide hp (P k) .left) N longest hN).1 ⟨v, d, hl⟩

end Recognition

/- ## Remaining reconstruction obligations

Three approaches were checked against the available interfaces before
recording the reader statements as open.

1. Intrinsic scanning. The exact `hrecog` contract above yields an
   existential intrinsic ray. The actual preceding ray is a metric candidate
   by `m0GeodesicSide_realized_adjacentCandidate`; neither that fact nor the
   existential contract says that the actual ray is the first-admissible
   one. `m0GeodesicSide_intrinsicSelector_competitor_scan_ambientFirstReturns`
   supplies first-return scan positions but not their departure-angle order.
   Therefore it cannot yet identify a ray chosen intrinsically from the side
   with the actual preceding ray. No repaired rotation-angle module is used.
   The recognition contract also concerns left sides only; a corresponding
   identification of the next ray inside a right side is not supplied.
2. Source-preimage selection. `LMinusSidePresentation.classOption4_eq_some_iff`
   and right-side code fidelity identify complete side classes. Choosing an
   ambient preimage and reading its slice would define a choice-dependent
   value until slice-class equality for two equal presentation codes is
   proved. Side-class equality transports intrinsic-ray existence, as proved
   above, but does not itself establish that slice-class equality. Thus no
   arbitrary preimage is installed as a fixed slice reader.
3. Realized geometric restriction. `m0CutRealizedLeftSideSlice_self_eq` and
   `m0CutRealizedLeftSideSlice_self_faces_iff` recover exact carriers and
   represented faces at the upper cut. Their arguments still include `P`,
   the coalescence offsets and the realization maps used by
   `geometricSideBetweenTraces`. These are not outputs of a side-presentation
   decoder. In addition, equality of its vertex/edge carrier alone is not
   equality of complete marked `GeometricSideClass` values. Iterating that
   restriction consequently does not yet give the per-cut sequence readers.

The first missing identification has the following complete source-context -/

/- theorem m0GeodesicSide_realizedAdjacent_is_intrinsic
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    IntrinsicallyLeftmostAdjacentRay
      (m0GeodesicSide hp (P k) .left) longest
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) -/

/-! The complete reader obligation is recorded next with the exact recognition
premise expanded. The single almost-sure event includes both half-index
identifications, all past/future sequence identifications, and the actual
slice witness family. Thus neither countable simultaneity nor the source
realization is omitted. The normalized thin carriers are those used by
`lemma56_of_presentationDetermination`; no measurability premise is inserted.
The definitions of the fixed readers, their geometric identification, and -/

/- theorem geoSlice56_presentationReconstruction_of_recognition
    (hrecog :
      ∀ {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
        {h : BoundaryHitWitnesses (shiftedStream W 0)}
        {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
        (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
        (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
        (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
          (boundaryPresentVertex (shiftedStream W 0) h k))
        (hleft : ∀ k : ℤ,
          Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
        (k : ℤ)
        (hcontain : ∀ n : ℕ,
          (P (k - 1)).codePath.edge n ∈
            (m0GeodesicSide hp (P k) .left).edges ∧
          ((P (k - 1)).codePath.initial n).1.id ∈
            (m0GeodesicSide hp (P k) .left).vertices),
        ∃ v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left),
          geometricSideAdjacentGeodesicCandidate
            (m0GeodesicSide hp (P k) .left) longest v d ∧
          IntrinsicallyLeftmostAdjacentRay
            (m0GeodesicSide hp (P k) .left) longest v d)
    (x : XDP) :
    ∃ (F_L : LPlusThinPresentation → Option GeometricSideClass)
      (F_R : RMinusThinPresentation → Option GeometricSideClass)
      (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
      (past : ∀ j : ℤ, LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass))
      (future : ∀ j : ℤ, RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass)),
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∀ k : ℤ, k ≤ 0 →
          G k W = F_L (geoSlice56LeftCutObservation x k W)) ∧
        (∀ k : ℤ, 1 ≤ k →
          G k W = F_R (geoSlice56RightCutObservation x (k - 1) W)) ∧
        (∀ j : ℤ,
          (fun k : {k : ℤ // k ≤ j} => G k W) =
            past j (geoSlice56LeftCutObservation x j W)) ∧
        (∀ j : ℤ,
          (fun k : {k : ℤ // j + 1 ≤ k} => G k W) =
            future j (geoSlice56RightCutObservation x j W)) ∧
        ∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
        ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
          (boundaryPresentVertex (shiftedStream W 0) h k),
        ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k
          (if x = XDP.ldp then true else false),
          (∀ k, Xdp.CutLeftmostXdp W H h hp hLL
            (if x = XDP.ldp then true else false) k (P k) (T k)) ∧
          (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL
            (if x = XDP.ldp then true else false) k Q (T k) → Q = P k) ∧
          ∀ k : ℤ, ∃ a b : ℕ,
            ∃ hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b,
            G k W = some (geometricSideClass
              (m0CutGeodesicSlice (hp := hp) P k a b hab)) -/

end DirectedDistances.PaperProofs.Section5
