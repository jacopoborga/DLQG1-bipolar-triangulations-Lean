/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCanonicalCoding

/-! Helpers toward Lemma 5.5 (`lem-geo-infty-ind`),
below select canonical representatives of the existing glued quotients;
their geometric coordinates are then read through the existing whole-plane
block maps. This file does not claim that these maps factor through the
observation code across different source witnesses. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {longest : Bool}
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))

local notation "VertexSource" =>
  LPlusCanonicalVertexSource (W := W) (h := h) (k := k) longest hqMode
local notation "DartSource" =>
  LPlusCanonicalDartSource (W := W) (h := h) (k := k) longest hqMode
local notation "V" => lPlusBlockVertexImage
  (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
local notation "D" => lPlusBlockDartImage
  (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ

/-- Helper toward Lemma 5.5. Select the source representative certified by
the least raw vertex token of a glued vertex. -/
@[expose] noncomputable def lPlusCanonicalVertexRepresentative
    (v : LPlusGluedVertex longest hqMode hτ) : VertexSource :=
  Classical.choose (Nat.find_spec
    (lPlusCanonicalVertexCandidate_exists longest hqMode hτ v))

/-- Helper toward Lemma 5.5. The selected source vertex has the least raw
token and represents the given glued vertex. -/
theorem lPlusCanonicalVertexRepresentative_spec
    (v : LPlusGluedVertex longest hqMode hτ) :
    lPlusRawVertexToken longest hqMode
        (lPlusCanonicalVertexRepresentative hqMode hτ v) =
      lPlusCanonicalVertexId longest hqMode hτ v ∧
    (⟦lPlusCanonicalVertexRepresentative hqMode hτ v⟧ :
      LPlusGluedVertex longest hqMode hτ) = v :=
  Classical.choose_spec (Nat.find_spec
    (lPlusCanonicalVertexCandidate_exists longest hqMode hτ v))

/-- Helper toward Lemma 5.5. Read the ambient whole-plane vertex ID from
the least-token representative of a glued vertex. -/
@[expose] noncomputable def lPlusCanonicalVertexImage
    (v : LPlusGluedVertex longest hqMode hτ) : ℕ :=
  V (lPlusCanonicalVertexRepresentative hqMode hτ v)

/-- Helper toward Lemma 5.5. The canonical vertex image agrees with the
existing block image on every representative of the same glued vertex. -/
theorem lPlusCanonicalVertexImage_eq_of_mk
    (a : VertexSource) (v : LPlusGluedVertex longest hqMode hτ)
    (ha : (⟦a⟧ : LPlusGluedVertex longest hqMode hτ) = v) :
    lPlusCanonicalVertexImage hqMode hτ v = V a := by
  apply (lPlusCanonicalVertex_quotient_iff longest hqMode hτ
    (lPlusCanonicalVertexRepresentative hqMode hτ v) a).2
  exact (lPlusCanonicalVertexRepresentative_spec hqMode hτ v).2.trans ha.symm

/-- Helper toward Lemma 5.5. The minimal-token vertex IDs have exactly the
existing whole-plane block-image carrier. -/
theorem lPlusCanonicalVertexImage_range :
    Set.range (lPlusCanonicalVertexImage hqMode hτ) = Set.range V := by
  apply Set.Subset.antisymm
  · rintro n ⟨v, rfl⟩
    exact ⟨lPlusCanonicalVertexRepresentative hqMode hτ v, rfl⟩
  · rintro n ⟨a, rfl⟩
    refine ⟨(⟦a⟧ : LPlusGluedVertex longest hqMode hτ), ?_⟩
    exact lPlusCanonicalVertexImage_eq_of_mk hqMode hτ a _ rfl

/-- Helper toward Lemma 5.5. The canonical vertex map is injective on the
existing gluing quotient. -/
theorem lPlusCanonicalVertexImage_injective :
    Function.Injective (lPlusCanonicalVertexImage hqMode hτ) := by
  intro v w hvw
  have hclass := (lPlusCanonicalVertex_quotient_iff longest hqMode hτ
    (lPlusCanonicalVertexRepresentative hqMode hτ v)
    (lPlusCanonicalVertexRepresentative hqMode hτ w)).mp hvw
  calc
    v = ⟦lPlusCanonicalVertexRepresentative hqMode hτ v⟧ :=
      (lPlusCanonicalVertexRepresentative_spec hqMode hτ v).2.symm
    _ = ⟦lPlusCanonicalVertexRepresentative hqMode hτ w⟧ := hclass
    _ = w := (lPlusCanonicalVertexRepresentative_spec hqMode hτ w).2

/-- Helper toward Lemma 5.5. Select the source representative certified by
the least raw dart token of a glued dart. -/
@[expose] noncomputable def lPlusCanonicalDartRepresentative
    (d : LPlusGluedDart longest hqMode hτ) : DartSource :=
  Classical.choose (Nat.find_spec
    (lPlusCanonicalDartCandidate_exists longest hqMode hτ d))

/-- Helper toward Lemma 5.5. The selected source dart has the least raw
token and represents the given glued dart. -/
theorem lPlusCanonicalDartRepresentative_spec
    (d : LPlusGluedDart longest hqMode hτ) :
    lPlusRawDartToken longest hqMode
        (lPlusCanonicalDartRepresentative hqMode hτ d) =
      lPlusCanonicalDartId longest hqMode hτ d ∧
    (⟦lPlusCanonicalDartRepresentative hqMode hτ d⟧ :
      LPlusGluedDart longest hqMode hτ) = d :=
  Classical.choose_spec (Nat.find_spec
    (lPlusCanonicalDartCandidate_exists longest hqMode hτ d))

/-- Helper toward Lemma 5.5. Read the ambient whole-plane dart ID from the
least-token representative of a glued dart. -/
@[expose] noncomputable def lPlusCanonicalDartImage
    (d : LPlusGluedDart longest hqMode hτ) : ℕ × Bool :=
  D (lPlusCanonicalDartRepresentative hqMode hτ d)

/-- Helper toward Lemma 5.5. The canonical dart image agrees with the
existing block image on every representative of the same glued dart. -/
theorem lPlusCanonicalDartImage_eq_of_mk
    (a : DartSource) (d : LPlusGluedDart longest hqMode hτ)
    (ha : (⟦a⟧ : LPlusGluedDart longest hqMode hτ) = d) :
    lPlusCanonicalDartImage hqMode hτ d = D a := by
  apply (lPlusCanonicalDart_quotient_iff longest hqMode hτ
    (lPlusCanonicalDartRepresentative hqMode hτ d) a).2
  exact (lPlusCanonicalDartRepresentative_spec hqMode hτ d).2.trans ha.symm

/-- Helper toward Lemma 5.5. The minimal-token dart IDs have exactly the
existing whole-plane block-image carrier, retaining the endpoint bit. -/
theorem lPlusCanonicalDartImage_range :
    Set.range (lPlusCanonicalDartImage hqMode hτ) = Set.range D := by
  apply Set.Subset.antisymm
  · rintro n ⟨d, rfl⟩
    exact ⟨lPlusCanonicalDartRepresentative hqMode hτ d, rfl⟩
  · rintro n ⟨a, rfl⟩
    refine ⟨(⟦a⟧ : LPlusGluedDart longest hqMode hτ), ?_⟩
    exact lPlusCanonicalDartImage_eq_of_mk hqMode hτ a _ rfl

/-- Helper toward Lemma 5.5. The canonical dart map is injective on the
existing gluing quotient, including the local endpoint bit. -/
theorem lPlusCanonicalDartImage_injective :
    Function.Injective (lPlusCanonicalDartImage hqMode hτ) := by
  intro d e hdv
  have hclass := (lPlusCanonicalDart_quotient_iff longest hqMode hτ
    (lPlusCanonicalDartRepresentative hqMode hτ d)
    (lPlusCanonicalDartRepresentative hqMode hτ e)).mp hdv
  calc
    d = ⟦lPlusCanonicalDartRepresentative hqMode hτ d⟧ :=
      (lPlusCanonicalDartRepresentative_spec hqMode hτ d).2.symm
    _ = ⟦lPlusCanonicalDartRepresentative hqMode hτ e⟧ := hclass
    _ = e := (lPlusCanonicalDartRepresentative_spec hqMode hτ e).2

/-- Helper toward Lemma 5.5. Re-express the two carriers of decoder 4 by
the least-token representatives, retaining its existing geometric marks. -/
@[expose] noncomputable def lPlusCanonicalSide4
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) : GeometricSideSubmap :=
  { lPlusCodeBlockSide4 hτ hp P hqMode Tpath hfin hleft hk with
    vertices := Set.range (lPlusCanonicalVertexImage hqMode hτ)
    edges := {e | ∃ b : Bool,
      (e, b) ∈ Set.range (lPlusCanonicalDartImage hqMode hτ)} }

/-- Helper toward Lemma 5.5. The canonical side's vertex carrier is exactly
the range of its least-token vertex IDs. -/
theorem lPlusCanonicalSide4_vertices
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) :
    (lPlusCanonicalSide4 hτ hp P hqMode Tpath hfin hleft hk).vertices =
      Set.range (lPlusCanonicalVertexImage hqMode hτ) := rfl

/-- Helper toward Lemma 5.5. The canonical side's edge carrier is exactly
the range of its least-token dart IDs with the endpoint bit forgotten. -/
theorem lPlusCanonicalSide4_edges
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) :
    (lPlusCanonicalSide4 hτ hp P hqMode Tpath hfin hleft hk).edges =
      {e | ∃ b : Bool,
        (e, b) ∈ Set.range (lPlusCanonicalDartImage hqMode hτ)} := rfl

variable {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "B4" => lPlusCodeBlockSide4 hτ hp P hqMode Tpath hfin hleft hk
local notation "C4" => lPlusCanonicalSide4 hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5. The canonical vertex carrier is the old
whole-plane vertex carrier after the least-token image is evaluated. -/
theorem lPlusCanonicalSide4_vertices_eq_old : (C4).vertices = (B4).vertices := by
  rw [lPlusCanonicalSide4_vertices, lPlusCanonicalVertexImage_range]
  rfl

/-- Helper toward Lemma 5.5. The canonical edge carrier is the old
whole-plane geometric edge carrier, including missing edges. -/
theorem lPlusCanonicalSide4_edges_eq_old : (C4).edges = (B4).edges := by
  rw [lPlusCanonicalSide4_edges, lPlusCanonicalDartImage_range]
  rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4 west
endpoint coordinate. -/
theorem lPlusCanonicalSide4_west_eq_old : (C4).west = (B4).west := rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4 east
endpoint coordinate. -/
theorem lPlusCanonicalSide4_east_eq_old : (C4).east = (B4).east := rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4
directed-presence coordinate. -/
theorem lPlusCanonicalSide4_present_eq_old : (C4).present = (B4).present := rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4
corrected rotation relation on the existing whole-plane dart IDs. -/
theorem lPlusCanonicalSide4_rotation_eq_old : (C4).rotation = (B4).rotation := rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4
face-successor relation. -/
theorem lPlusCanonicalSide4_faceNext_eq_old : (C4).faceNext = (B4).faceNext := rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4 root
vertex mark. -/
theorem lPlusCanonicalSide4_root_eq_old : (C4).root = (B4).root := rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4
boundary dart marks. -/
theorem lPlusCanonicalSide4_boundary_eq_old : (C4).boundary = (B4).boundary := rfl

/-- Helper toward Lemma 5.5. The canonical side retains the decoder-4
seam dart marks. -/
theorem lPlusCanonicalSide4_seam_eq_old : (C4).seam = (B4).seam := rfl






























































end DirectedDistances.PaperProofs.Section5
