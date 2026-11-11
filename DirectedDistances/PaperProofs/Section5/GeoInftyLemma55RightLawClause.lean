/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusLemma55Assembly
public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusSideMeasurable3
public import DirectedDistances.PaperProofs.Section5.GeoInftySideReader
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassIndependence
public import DirectedDistances.PaperProofs.Section5.GeoSliceAdjacentCoalescence
public import DirectedDistances.PaperProofs.Section5.GeometricSideClass




public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- The R-plus coherent-side class map, extended by `none` off its exact
coherent domain. Helper toward Lemma 5.5. -/
noncomputable def geometricRightSideClassOption (x : XDP)
    (p : ℕ → ℤ × ℤ) : Option GeometricSideClass :=
  if hp : p ∈ Coherent x then
    some (geometricSideClass
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right
        ⟨p, hp⟩))
  else none

/-- Helper toward Lemma 5.5: the optional right-side class map is measurable
on the full hatted-path space. -/
theorem measurable_geometricRightSideClassOption (x : XDP) :
    Measurable (geometricRightSideClassOption x) := by
  change Measurable (fun p : ℕ → ℤ × ℤ =>
    if hp : p ∈ Coherent x then
      some (geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right
          ⟨p, hp⟩))
    else none)
  exact (measurable_some_geometricSideClass.comp
      (measurable_geometricRightSide_class x)).dite
    measurable_const
    (selectedCutCoherentDomain_measurable_conull x renewalTime
      renewalTime_positiveSuccessTime).1

/-- Reader data for one actual M0 right side and its R-plus realization.
The leftmost and uniqueness fields are inherited from the selected family
in Lemma 5.6; the last field is the proved marked isomorphism from the
nonnegative right-side reader. -/
structure M0RightSideReaderWitness (W : ℤ → Fin 3) (longest : Bool)
    (k : ℤ) where
  H : WholePlaneRotationHypothesis W
  h : BoundaryHitWitnesses (shiftedStream W 0)
  hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))
  hp : BoundaryHitWitnesses (kmswPastCode W)
  R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0)
  T : ∀ j : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h j)
  P : ∀ j : ℤ, M0CutInfiniteGeodesic W H h hLL j longest
  hR : ∀ j, (R j).vertex 0 = boundaryVertex (shiftedStream W 0) h j ∧
    (T j).edge = (R j).edge ∧
    ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
      ((T j).initial n).1.id ((T j).edge n)
  hleft : ∀ j, Xdp.CutLeftmostXdp W H h hp hLL longest j (P j) (T j)
  huniq : ∀ j Q, Xdp.CutLeftmostXdp W H h hp hLL longest j Q (T j) → Q = P j
  hreal : (decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
    (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.isSome
  hiso : Nonempty (GeometricSideMarkedIso (m0GeodesicSide hp (P k) .right)
    ((decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
      (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.get
        hreal))

/-- Helper toward Lemma 5.5. On the selected-family reader event, return the
class of the actual M0 right side; outside that event return `none`. -/
noncomputable def m0RightSideClassOption (longest : Bool) (k : ℤ)
    (W : ℤ → Fin 3) : Option GeometricSideClass :=
  if h : Nonempty (M0RightSideReaderWitness W longest k) then
    some (geometricSideClass
      (m0GeodesicSide (Classical.choice h).hp ((Classical.choice h).P k) .right))
  else none

/-- Helper toward Lemma 5.5: on one full-measure event, the actual M0 right
side class is the measurable class of the coherent R-plus hatted side. The
reader's marked isomorphism and the code-fidelity theorem identify the
presentation realization with this coherent representative. -/
theorem m0RightSideClassOption_ae_eq_geometricRightSideClassOption
    (longest : Bool) (k : ℤ) (hk : 0 ≤ k) :
    m0RightSideClassOption longest k =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => geometricRightSideClassOption
        (if longest then XDP.ldp else XDP.sdp)
        (boundaryFutureHattedPath k W)) := by
  let x := if longest then XDP.ldp else XDP.sdp
  filter_upwards [ae_boundaryGluing_nonneg_right_markedIso_decodeRPlus,
    (boundaryFutureThinSides_package x k).2.2.2.2.2] with W hreader hq
  obtain ⟨H, h, hLL, hp, hall⟩ := hreader
  obtain ⟨R, T, P, hR, hleft, huniq, hcoal, hside⟩ := hall longest
  obtain ⟨hreal, hiso⟩ := hside k hk
  let w : M0RightSideReaderWitness W longest k := {
    H := H, h := h, hLL := hLL, hp := hp, R := R, T := T, P := P,
    hR := hR, hleft := hleft, huniq := huniq, hreal := hreal, hiso := hiso }
  have hne : Nonempty (M0RightSideReaderWitness W longest k) := ⟨w⟩
  have hclass (v : M0RightSideReaderWitness W longest k) :
      geometricSideClass (m0GeodesicSide v.hp (v.P k) .right) =
        geometricSideClass (geometricSideSubmap x renewalTime
          renewalTime_positiveSuccessTime .right
          ⟨boundaryFutureHattedPath k W, hq⟩) := by
    let r := decodeRPlus x k (rightSideObsNonneg x k W)
    obtain ⟨q, hcode, hqside⟩ := r.realization_eq_some_spec
      (r.realization.get v.hreal) (Option.some_get v.hreal).symm
    have hcode' : thinSideCode x renewalTime renewalTime_positiveSuccessTime
        .right q.1 = thinSideCode x renewalTime renewalTime_positiveSuccessTime
          .right (boundaryFutureHattedPath k W) := by
      change thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
        rightSideObsNonneg x k W at hcode
      rw [rightSideObsNonneg_eq_thinSideCode] at hcode
      exact hcode
    calc
      geometricSideClass (m0GeodesicSide v.hp (v.P k) .right) =
          geometricSideClass (r.realization.get v.hreal) :=
        (geometricSideClass_eq_iff _ _).2 v.hiso
      _ = geometricSideClass
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) :=
        congrArg geometricSideClass hqside.symm
      _ = geometricSideClass
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right
            ⟨boundaryFutureHattedPath k W, hq⟩) :=
        (geometricSideClass_eq_iff _ _).2
          (rightSideCode_markedIso_of_eq x q ⟨boundaryFutureHattedPath k W, hq⟩ hcode')
  change m0RightSideClassOption longest k W =
    geometricRightSideClassOption x (boundaryFutureHattedPath k W)
  simp only [m0RightSideClassOption, dif_pos hne, geometricRightSideClassOption,
    dif_pos hq]
  exact congrArg some (hclass (Classical.choice hne))

/-- Helper toward Lemma 5.5: the actual M0 right-side class observable is
almost-everywhere measurable, by its identification with the measurable
coherent R-plus class map. -/
theorem aemeasurable_m0RightSideClassOption (longest : Bool) (k : ℤ)
    (hk : 0 ≤ k) :
    AEMeasurable (m0RightSideClassOption longest k) wholePlaneIIDCodeMeasure := by
  let x := if longest then XDP.ldp else XDP.sdp
  have hm : AEMeasurable
      (fun W => geometricRightSideClassOption x (boundaryFutureHattedPath k W))
      wholePlaneIIDCodeMeasure :=
    (measurable_geometricRightSideClassOption x).comp_aemeasurable
      (aemeasurable_boundaryFutureHattedPath k)
  exact hm.congr (m0RightSideClassOption_ae_eq_geometricRightSideClassOption
    longest k hk).symm

/-- Helper toward Lemma 5.5: the actual right-side observable is almost surely
the optional marked-isomorphism class read from its R-plus presentation. -/
theorem m0RightSideClassOption_ae_eq_RPlusPresentationClass
    (longest : Bool) (k : ℤ) (hk : 0 ≤ k) :
    m0RightSideClassOption longest k =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => (decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
        (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.map
          geometricSideClass) := by
  filter_upwards [ae_boundaryGluing_nonneg_right_markedIso_decodeRPlus] with W hreader
  obtain ⟨H, h, hLL, hp, hall⟩ := hreader
  obtain ⟨R, T, P, hR, hleft, huniq, hcoal, hside⟩ := hall longest
  obtain ⟨hreal, hiso⟩ := hside k hk
  let v : M0RightSideReaderWitness W longest k := {
    H := H, h := h, hLL := hLL, hp := hp, R := R, T := T, P := P,
    hR := hR, hleft := hleft, huniq := huniq, hreal := hreal, hiso := hiso }
  let hv : Nonempty (M0RightSideReaderWitness W longest k) := ⟨v⟩
  let r := decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
    (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)
  have hmap (u : M0RightSideReaderWitness W longest k) :
      r.realization.map geometricSideClass =
        some (geometricSideClass (r.realization.get u.hreal)) := by
    calc
      r.realization.map geometricSideClass =
          (some (r.realization.get u.hreal)).map geometricSideClass :=
        congrArg (fun a : Option GeometricSideSubmap => a.map geometricSideClass)
          (Option.some_get u.hreal).symm
      _ = some (geometricSideClass (r.realization.get u.hreal)) := rfl
  change m0RightSideClassOption longest k W = r.realization.map geometricSideClass
  rw [m0RightSideClassOption, dif_pos hv]
  calc
    some (geometricSideClass (m0GeodesicSide (Classical.choice hv).hp
      ((Classical.choice hv).P k) .right)) =
        some (geometricSideClass (r.realization.get (Classical.choice hv).hreal)) :=
      congrArg some ((geometricSideClass_eq_iff _ _).2 (Classical.choice hv).hiso)
    _ = r.realization.map geometricSideClass := (hmap (Classical.choice hv)).symm

/-- The nonnegative-index right-side clause of Lemma 5.5: for either XDP
mode, the actual M0 right-side class has the same law as at index zero. -/
theorem m0RightSideClassOption_law_eq_zero (longest : Bool) (k : ℤ)
    (hk : 0 ≤ k) :
    wholePlaneIIDCodeMeasure.map (m0RightSideClassOption longest k) =
      wholePlaneIIDCodeMeasure.map (m0RightSideClassOption longest 0) := by
  let x := if longest then XDP.ldp else XDP.sdp
  calc
    wholePlaneIIDCodeMeasure.map (m0RightSideClassOption longest k) =
        wholePlaneIIDCodeMeasure.map (fun W => geometricRightSideClassOption x
          (boundaryFutureHattedPath k W)) :=
      Measure.map_congr (m0RightSideClassOption_ae_eq_geometricRightSideClassOption
        longest k hk)
    _ = wholePlaneIIDCodeMeasure.map (fun W => geometricRightSideClassOption x
          (boundaryFutureHattedPath 0 W)) := by
      exact geometricRightSide_class_law_eq_zero x k hk
    _ = wholePlaneIIDCodeMeasure.map (m0RightSideClassOption longest 0) :=
      (Measure.map_congr
        (m0RightSideClassOption_ae_eq_geometricRightSideClassOption longest 0 (by omega))).symm

/- First remaining statement toward the full source Lemma 5.5, with its complete
binders. `A_L` and `A_R` are comment-only names for the actual marked classes
of the complete left and right M0 sides; they are not assumptions or Lean
declarations here.

  (A_L : XDP → ℤ → (ℤ → Fin 3) → GeometricSideClass)
  (A_R : XDP → ℤ → (ℤ → Fin 3) → GeometricSideClass)
  ∀ (x : XDP) (k : ℤ),
    IndepFun (A_L x k) (A_R x k) wholePlaneIIDCodeMeasure ∧
    (0 ≤ k → wholePlaneIIDCodeMeasure.map (A_R x k) =
      wholePlaneIIDCodeMeasure.map (A_R x 0)) ∧
    (k ≤ 0 → wholePlaneIIDCodeMeasure.map (A_L x k) =
      wholePlaneIIDCodeMeasure.map (A_L x 0))

The independence clause and the nonpositive-index left-side law are not
proved by this right-law helper. -/

end DirectedDistances.PaperProofs.Section5
