/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyHattedSideIso
public import DirectedDistances.PaperProofs.Section5.GeoInftyIndCodeLevel
public import DirectedDistances.PaperProofs.SourceResults.GeoInfty










public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Code" => (ℕ → Option FiniteThinMap)
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: equality of coherent right-side codes determines
the complete geometric side, including all marks, up to marked isomorphism. -/
theorem rightSideCode_markedIso_of_eq (x : XDP) (q q' : Coherent x)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q')) := by
  obtain ⟨I⟩ :=
    ((DirectedDistances.PaperProofs.SourceResults.thin_ind x).2.1 .right q q').mp hc
  exact ⟨I.whole⟩

/-- Helper toward Lemma 5.5: the input code of a right-side presentation.
Geometric realization is a separate, partially defined operation, whose
existence is proved below on the full-measure source domain. -/
structure RPlusSidePresentation (x : XDP) where
  code : Code

/-- Helper toward Lemma 5.5: the presentation carries exactly the cylinder
sigma algebra read by its code projection. -/
noncomputable instance (x : XDP) : MeasurableSpace (RPlusSidePresentation x) :=
  MeasurableSpace.comap RPlusSidePresentation.code inferInstance

/-- Helper toward Lemma 5.5: the right-side reader, independent of the boundary
index. Its code projection retains every finite marked truncation. -/
@[expose] def decodeRPlus (x : XDP) (_k : ℤ) (c : Code) :
    RPlusSidePresentation x := ⟨c⟩

/-- Helper toward Lemma 5.5: the right-side reader is measurable for the
explicit cylinder sigma algebra on presentations. -/
theorem measurable_decodeRPlus (x : XDP) (k : ℤ) :
    Measurable (decodeRPlus x k) :=
  measurable_comap_iff.mpr measurable_id

/-- Helper toward Lemma 5.5: reading the code back from the presentation
recovers the entire input, so the sigma algebra retains every code cylinder. -/
theorem decodeRPlus_code (x : XDP) (k : ℤ) (c : Code) :
    (decodeRPlus x k c).code = c := rfl

/-- Helper toward Lemma 5.5: the code projection is measurable for the
specified presentation sigma algebra. -/
theorem measurable_rPlusSidePresentation_code (x : XDP) :
    Measurable (RPlusSidePresentation.code (x := x)) :=
  comap_measurable _

/-- Helper toward Lemma 5.5: the reader and code projection are inverse
on presentations, not only on observations from the source event. -/
theorem RPlusSidePresentation.decode_code {x : XDP}
    (r : RPlusSidePresentation x) (k : ℤ) :
    decodeRPlus x k r.code = r := rfl

/-- Helper toward Lemma 5.5: the observation is exactly the coherent-side
code of the hatted future path, with no change of boundary index. -/
theorem rightSideObsNonneg_eq_thinSideCode (x : XDP) (k : ℤ) (W : ℤ → Fin 3) :
    rightSideObsNonneg x k W =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
        (boundaryFutureHattedPath k W) := rfl

/-- Helper toward Lemma 5.5: the presentation obtained from the right-side
observation is almost-everywhere measurable under the whole-plane code law. -/
theorem aemeasurable_decodeRPlus_rightSideObsNonneg (x : XDP) (k : ℤ) :
    AEMeasurable (fun W => decodeRPlus x k (rightSideObsNonneg x k W))
      wholePlaneIIDCodeMeasure :=
  (measurable_decodeRPlus x k).comp_aemeasurable
    (aemeasurable_boundaryFourObservations x k 2)

/-- Helper toward Lemma 5.5: realize a presentation by any coherent path
with the given code. The preceding code-fidelity theorem proves independence
of this choice up to complete marked isomorphism. A code with no coherent
realization yields `none`, rather than a default geometric side. -/
@[expose] noncomputable def RPlusSidePresentation.realization {x : XDP}
    (r : RPlusSidePresentation x) : Option GeometricSideSubmap :=
  if h : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code
  then some (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
    .right h.choose)
  else none

/-- Helper toward Lemma 5.5: a presentation has no geometric realization
exactly when its code has no coherent preimage. -/
theorem RPlusSidePresentation.realization_eq_none_iff {x : XDP}
    (r : RPlusSidePresentation x) :
    r.realization = none ↔ ¬ ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code := by
  unfold RPlusSidePresentation.realization
  split <;> simp only [Option.some_ne_none, not_true_eq_false, not_false_eq_true, *]

/-- Helper toward Lemma 5.5: every returned geometric realization has the
given code and is an actual coherent geometric right side. -/
theorem RPlusSidePresentation.realization_eq_some_spec {x : XDP}
    (r : RPlusSidePresentation x) (M : GeometricSideSubmap)
    (hM : r.realization = some M) :
    ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code ∧
      geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q = M := by
  unfold RPlusSidePresentation.realization at hM
  split at hM
  · rename_i h
    exact ⟨h.choose, h.choose_spec, Option.some.inj hM⟩
  · cases hM

/-- Helper toward Lemma 5.5: the geometric realization of a coherent code
exists. This proof is supplied internally when accessing the realization. -/
theorem decodeRPlus_realization_isSome (x : XDP) (k : ℤ) (q : Coherent x) :
    (decodeRPlus x k
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1)).realization.isSome := by
  unfold RPlusSidePresentation.realization
  rw [dite_eq_left ⟨q, rfl⟩]
  rfl

/-- Helper toward Lemma 5.5: the hatted right side is completely
marked-isomorphic to the realization read from its code. No choice of path
representative changes the resulting marked isomorphism class. -/
theorem geometricSideSubmap_markedIso_decodeRPlus (x : XDP) (k : ℤ) (q : Coherent x) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
      ((decodeRPlus x k
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1)).realization.get
        (decodeRPlus_realization_isSome x k q))) := by
  let r := decodeRPlus x k
    (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1)
  have hsome := decodeRPlus_realization_isSome x k q
  obtain ⟨q', hcode, hside⟩ := r.realization_eq_some_spec
    (r.realization.get hsome) (Option.some_get hsome).symm
  rw [← hside]
  exact rightSideCode_markedIso_of_eq x q q' hcode.symm

/-- Helper toward Lemma 5.5: the actual observation always has a realization
on the coherent hatted-path event, including at boundary index zero. -/
theorem decodeRPlus_rightSideObsNonneg_realization_isSome (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) (hq : boundaryFutureHattedPath k W ∈ Coherent x) :
    (decodeRPlus x k (rightSideObsNonneg x k W)).realization.isSome :=
  decodeRPlus_realization_isSome x k ⟨boundaryFutureHattedPath k W, hq⟩

/-- Helper toward Lemma 5.5: the hatted geometric right side factors
through the code observation, as a complete marked isomorphism. -/
theorem boundaryFutureHattedSide_markedIso_decodeRPlus (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) (hq : boundaryFutureHattedPath k W ∈ Coherent x) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right
        ⟨boundaryFutureHattedPath k W, hq⟩)
      ((decodeRPlus x k (rightSideObsNonneg x k W)).realization.get
        (decodeRPlus_rightSideObsNonneg_realization_isSome x k W hq))) :=
  geometricSideSubmap_markedIso_decodeRPlus x k ⟨boundaryFutureHattedPath k W, hq⟩

/-- Helper toward Lemma 5.5: the observation has a geometric realization
almost surely. Its existence is discharged by the existing thin-side event,
rather than added to the source hypotheses. -/
theorem ae_decodeRPlus_rightSideObsNonneg_realization_isSome (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (decodeRPlus x k (rightSideObsNonneg x k W)).realization.isSome := by
  filter_upwards [(boundaryFutureThinSides_package x k).2.2.2.2.2] with W hq
  exact decodeRPlus_rightSideObsNonneg_realization_isSome x k W hq

section NonnegativeSide

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ Coherent
    (if longest then XDP.ldp else XDP.sdp))
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

include hτ Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: under exactly the standing context of the
hatted-side embedding, the actual nonnegative right side is marked-isomorphic
to the geometric realization read from its right-side code observation.
The realization's existence is proved internally, not assumed. -/
theorem boundaryGluing_nonneg_right_markedIso_decodeRPlus :
    Nonempty (GeometricSideMarkedIso
      (m0GeodesicSide hp P .right)
      ((decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
        (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.get
        (decodeRPlus_rightSideObsNonneg_realization_isSome
          (if longest then XDP.ldp else XDP.sdp) k W hqMode))) := by
  obtain ⟨I⟩ := boundaryGluing_nonneg_right_markedIso_nonempty
    hτ hp P hqMode Tpath hfin hleft hk
  obtain ⟨J⟩ := boundaryFutureHattedSide_markedIso_decodeRPlus
    (if longest then XDP.ldp else XDP.sdp) k W hqMode
  refine ⟨⟨I.equiv.trans J.equiv, ?_⟩⟩
  intro t u v
  exact (I.relation_iff t u v).trans (J.relation_iff t (I.equiv u) (I.equiv v))

end NonnegativeSide

/-- Helper toward Lemma 5.5: the right-side reader identifies the actual
geodesic sides on a single full-measure event, simultaneously for both modes
and every nonnegative boundary index. The path families are the witnesses
of `geo_infty_provider`; coherent paths, flow hits and finite incidence are
discharged by `wholePlane_ae_boundaryGluing_inputs`. -/
theorem ae_boundaryGluing_nonneg_right_markedIso_decodeRPlus :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n)) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ∧
        ∀ k : ℤ, 0 ≤ k →
          ∃ hreal : (decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
            (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.isSome,
          Nonempty (GeometricSideMarkedIso
            (m0GeodesicSide hp (P k) .right)
            ((decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
              (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.get
              hreal)) := by
  filter_upwards [DirectedDistances.PaperProofs.SourceResults.geo_infty_provider,
    wholePlane_ae_boundaryGluing_inputs] with W hgeo hglue
  obtain ⟨H, h, hLL, hp, _, hpaths⟩ := hgeo
  refine ⟨H, h, hLL, hp, ?_⟩
  intro longest
  obtain ⟨R, T, P, hR, hleft, huniq, hcoal⟩ := hpaths longest
  refine ⟨R, T, P, hR, hleft, huniq, hcoal, ?_⟩
  intro k hk
  obtain ⟨hτ, hfin, _, hcoherent⟩ := hglue h k
  have hq := hcoherent (if longest then XDP.ldp else XDP.sdp)
  exact ⟨decodeRPlus_rightSideObsNonneg_realization_isSome
      (if longest then XDP.ldp else XDP.sdp) k W hq,
    boundaryGluing_nonneg_right_markedIso_decodeRPlus
      hτ hp (P k) hq (T k) hfin (hleft k) hk⟩

end DirectedDistances.PaperProofs.Section5
