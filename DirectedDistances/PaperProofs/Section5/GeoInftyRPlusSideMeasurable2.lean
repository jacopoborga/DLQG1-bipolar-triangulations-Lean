/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusSideMeasurable

/-! # Permanent-ID measurability of the coherent geometric right side

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
local notation "HL" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
local notation "HT" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
local notation "HR" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
local notation "P" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q)

/-- Helper toward Lemma 5.5. At each good cut, one concrete finite half has
exactly the permanent vertex and dart images of the geometric ancestor level.
The embeddings and the selected infinite-path prefix are constructed together;
no geometric identification is assumed. This is a pointwise characterization,
without an assertion that the existential witnesses are measurably selected. -/
theorem geometricAncestor_finiteHalf_images
    (x : XDP) (q : Coherent x) (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2)) :
    let t := (selectedCutTime renewalTime (k + 1) q.1).toNat - 1
    ∃ (ℓ r n m : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap (W q) t))
      (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
      selectedCutSide x renewalTime a k q.1 =
        some ⟨_, ⟨_, ⟨_, KMSWMapIsoClass.mk (ancestorPosHalfRep R hR a)⟩⟩⟩ ∧
      boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v ∧
      ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
        (fun d => d.1.val) = List.ofFn (fun j : Fin m => (P x q).edge j.val) ∧
      ancestorPosVertexId (W q) t R hR I a ''
          ancestors (presentation (ancestorPosHalfRep R hR a) a v) =
        geometricAncestorVertices x renewalTime renewalTime_positiveSuccessTime a q s ∧
      ancestorPosDartId (W q) t R hR I a ''
          selectedDarts (presentation (ancestorPosHalfRep R hR a) a v) =
        {d : ℕ × Bool | d.1 ∈
          geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime a q s} := by
  intro t
  obtain ⟨ℓ, r, n, m, R, hR, I, v, hrep, hv, _, htarget, _, hp⟩ :=
    sourceAncestorPosHalf_boundary_prefix_embedding
      x renewalTime renewalTime_positiveSuccessTime q a s k hk
  have hseed (b : ThinMapSide) :
      AncestorPosHalfOffPrefixArcSeedIdentification
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) t R hR I b := by
    apply ancestorPos_arcSeeds_of_boundaryLaunch
      (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) t R hR I hp b
    apply (ancestorPos_boundaryLaunch_iff_seamLaunch
      (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) t R hR I hp b).mpr
    apply (ancestorPos_seamLaunch_iff_argumentOrder
      (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) t R hR I hp b).mpr
    intro i
    exact ancestorPos_seamLaunch_argumentOrder
      (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) t R hR I hp b i
  have hside := (ancestorPos_sideRanges_iff_arcSeeds
    (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) t R hR I hp).mpr hseed
  have hg := sourceAncestorPosHalf_geometric_of_sideRange
    x renewalTime renewalTime_positiveSuccessTime q a s k hk R hR I v htarget hp (hside a)
  refine ⟨ℓ, r, n, m, R, hR, I, v, hrep, hv, hp, ?_, hg.1⟩
  exact ancestorPos_vertices_image_of_darts
    (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q)
    (presentation (ancestorPosHalfRep R hR a) a v) a s
    (ancestorPosVertexId (W q) t R hR I a) (ancestorPosDartId (W q) t R hR I a)
    (fun d => (ancestorPos_ids_endpoints (W q) t R hR I a d).1) htarget hg.1























































































end DirectedDistances.PaperProofs.Section5
