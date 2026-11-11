module

public import DirectedDistances.PaperProofs.Section4.ThinHalfTruncate
public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.DirectedPath.Distance
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.PlanarMap.GeneralEndpointGeodesic

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.PaperProofs.Section4
open DirectedDistances.PlanarMap
open Quiver

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper
The finite representative's boundary vertex; index zero is the source. -/
@[expose] noncomputable def thinRepresentativeBoundaryStart
    (R : HalfTruncationRep) (j : ℕ) :
    Option (DirectedDistances.PlanarMap.MapVertex R.rep.B.map) :=
  if j = 0 then some R.rep.B.source else
    ((boundaryDarts R.rep.B R.side)[j - 1]?).map
      (DirectedDistances.PlanarMap.dartHeadVertex R.rep.B.map)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper
The total longest-path length, with zero for an undefined or unreachable start. -/
@[expose] noncomputable def thinRepresentativeLdpLength
    (R : HalfTruncationRep) (j : ℕ) : ℤ :=
  match thinRepresentativeBoundaryStart R j with
  | none => 0
  | some v => Int.ofNat ((ldpSup v R.target).unbotD 0)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper
The total shortest-path length, with zero for an undefined or unreachable start. -/
@[expose] noncomputable def thinRepresentativeSdpLength
    (R : HalfTruncationRep) (j : ℕ) : ℤ :=
  match thinRepresentativeBoundaryStart R j with
  | none => 0
  | some v => Int.ofNat (sdp v R.target).toNat

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper
Finite longest-distance difference to the marked target, relative to the root. -/
@[expose] noncomputable def thinRepresentativeLdpDiff
    (R : HalfTruncationRep) (j : ℕ) : ℤ :=
  thinRepresentativeLdpLength R j - thinRepresentativeLdpLength R 0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper
Finite shortest-distance difference to the marked target, relative to the root. -/
@[expose] noncomputable def thinRepresentativeSdpDiff
    (R : HalfTruncationRep) (j : ℕ) : ℤ :=
  thinRepresentativeSdpLength R j - thinRepresentativeSdpLength R 0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper
The exact unresolved quotient step: representative distance differences agree
whenever their marked truncations are isomorphic. -/
@[expose] def ThinRepresentativeLdpInvariant : Prop :=
  ∀ R S : HalfTruncationRep,
    (∃ e : TruncationCell R ≃ TruncationCell S,
      ∀ t x y, truncationRelation R t x y ↔
        truncationRelation S t (e x) (e y)) →
      ∀ j, thinRepresentativeLdpDiff R j = thinRepresentativeLdpDiff S j

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper
Smallest remaining shortest-distance quotient-invariance obligation. -/
@[expose] def ThinRepresentativeSdpInvariant : Prop :=
  ∀ R S : HalfTruncationRep,
    (∃ e : TruncationCell R ≃ TruncationCell S,
      ∀ t x y, truncationRelation R t x y ↔
        truncationRelation S t (e x) (e y)) →
      ∀ j, thinRepresentativeSdpDiff R j = thinRepresentativeSdpDiff S j

end DirectedDistances.Recursive
