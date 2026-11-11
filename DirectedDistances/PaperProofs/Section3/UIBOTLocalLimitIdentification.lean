/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization
public import DirectedDistances.KMSW.KMSWWindowEventualCaptureH
public import DirectedDistances.KMSW.WholePlaneRunBoundaryDegree
public import DirectedDistances.KMSW.WholePlaneLLRecordEdges
public import DirectedDistances.KMSW.M0CutPresence
public import DirectedDistances.KMSW.WholePlanePastGlueDrawing
public import DirectedDistances.RandomWalk.PastCodeLaw
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas









public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Helper toward Proposition 3.9: the midpoint-root certificate is a
measurable finite cylinder under the two-sided iid code space. -/
theorem measurableSet_uibotRootWindowCapture (N r : ℕ) :
    MeasurableSet {W : ℤ → Fin 3 |
      UIBOTRootWindowCapture (shiftedStream W N) N r} := by
  let pref : (ℤ → Fin 3) → (Fin (2 * N) → Fin 3) :=
    fun W i => W ((i.val : ℤ) - N)
  let A : Set (Fin (2 * N) → Fin 3) :=
    {v | UIBOTRootWindowCapture (finiteCodeExtend (n := 2 * N + 1) v) N r}
  have hpref : Measurable pref :=
    Measurable.of_eval fun i => measurable_pi_apply ((i.val : ℤ) - N)
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have heq : {W : ℤ → Fin 3 |
      UIBOTRootWindowCapture (shiftedStream W N) N r} = pref ⁻¹' A := by
    ext W
    apply uibotRootWindowCapture_congr
    intro i hi
    simp only [finiteCodeExtend, Nat.add_sub_cancel, dite_eq_left hi, pref, shiftedStream]
  rw [heq]
  exact hA.preimage hpref

/-- Helper toward Proposition 3.9: strong capture holds eventually at
the chronological root, simultaneously for every radius, under the actual
two-sided iid law. No stopped-word law or extra recurrence premise is used. -/
theorem wholePlaneIID_ae_eventual_uibotRootWindowCapture :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ r : ℕ, ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → UIBOTRootWindowCapture (shiftedStream W N) N r := by
  filter_upwards [wholePlaneIID_ae_eventual_windowCaptureStrong] with W h r
  obtain ⟨N₀, h₀, hN⟩ := h 0 (activeInitial (shiftedStream W 0) 0) r
  refine ⟨N₀, ?_⟩
  intro N hlarge
  have hc := hN N hlarge
  rw [uibotWholePlaneVertexTrans_activeInitial] at hc
  simpa only [UIBOTRootWindowCapture, Nat.sub_zero, Nat.add_zero] using hc

/-- Helper toward Proposition 3.9: the probabilities of the concrete
finite-window chronological-root certificates tend to one. The events
need not be monotone; their eventual tails provide the lower bound. -/
theorem wholePlaneIID_uibotRootWindowCapture_tendsto_one (r : ℕ) :
    Tendsto (fun N : ℕ => wholePlaneIIDCodeMeasure
      {W | UIBOTRootWindowCapture (shiftedStream W N) N r}) atTop (𝓝 1) := by
  let T : ℕ → Set (ℤ → Fin 3) := fun K =>
    {W | ∀ N : ℕ, K ≤ N → UIBOTRootWindowCapture (shiftedStream W N) N r}
  have hmono : Monotone T := by
    intro K L hKL W hW N hLN
    exact hW N (hKL.trans hLN)
  have hfull : wholePlaneIIDCodeMeasure (⋃ K, T K) = 1 := by
    calc
      wholePlaneIIDCodeMeasure (⋃ K, T K) = wholePlaneIIDCodeMeasure Set.univ := by
        apply measure_congr
        filter_upwards [wholePlaneIID_ae_eventual_uibotRootWindowCapture] with W hW
        have hmem : W ∈ ⋃ K, T K := by
          obtain ⟨K, hK⟩ := hW r
          exact Set.mem_iUnion.mpr ⟨K, hK⟩
        exact propext ⟨fun _ => Set.mem_univ W, fun _ => hmem⟩
      _ = 1 := measure_univ
  have ht := tendsto_measure_iUnion_atTop (μ := wholePlaneIIDCodeMeasure) hmono
  rw [hfull] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
  · intro N
    exact measure_mono (fun W hW => hW N le_rfl)
  · intro N
    exact prob_le_one

/-- Helper toward Proposition 3.9: the same capture limit in real-valued
probabilities, for use in finite-window error estimates. -/
theorem wholePlaneIID_uibotRootWindowCapture_tendsto_one_real (r : ℕ) :
    Tendsto (fun N : ℕ => wholePlaneIIDCodeMeasure.real
      {W | UIBOTRootWindowCapture (shiftedStream W N) N r}) atTop (𝓝 (1 : ℝ)) := by
  simpa only [Measure.real, ENNReal.toReal_one, Function.comp_def] using
    (ENNReal.continuousAt_toReal ENNReal.one_ne_top).tendsto.comp
      (wholePlaneIID_uibotRootWindowCapture_tendsto_one r)

/-- Helper toward Proposition 3.9: every geometric edge of the actual
two-sided iid colimit is present, on one simultaneous almost-sure event.
An edge absent in a one-sided run is a lower-left record edge; backward
record escape proves its presence in the colimit. -/
theorem wholePlaneIID_ae_uibotAllEdgesPresent :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e := by
  filter_upwards [wholePlaneIID_ae_runBoundaryDegree,
    wholePlaneIID_ae_LL_record_edges] with W hh hrecord e
  obtain ⟨⟨N, k⟩, rfl⟩ := Quotient.exists_rep e
  by_cases hp : EdgePresent (shiftedStream W N) k
  · exact wholePlaneEdgePresent_ι_of_run_present W N k hp
  · obtain ⟨hN, _⟩ := hh N
    obtain ⟨m, hm⟩ :=
      (m0Cut_not_present_iff_eventually_LL (shiftedStream W N) hN k).mp hp
    have hk := hm m le_rfl
    rw [kmswStage_LL_eq] at hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
    have hrec : 0 < t ∧ ∀ j < t,
        L (shiftedStream W N) t < L (shiftedStream W N) j :=
      of_decide_eq_true (List.mem_filter.mp (List.mem_reverse.mp ht)).2
    exact (hrecord N t hrec.1 hrec.2).1

/-- Helper toward Proposition 3.9: the actual iid colimit has a geometric
root. This establishes existence and domain membership, not measurability
of a class-valued choice or the finite-map local-limit law. -/
theorem wholePlaneIID_ae_uibotGeometricDomain :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
        D39GeomDomain
          (uibotWholePlaneGeometricMap W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
          (uibotWholePlaneGeometricRoot W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H)) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis,
    wholePlaneIID_ae_runBoundaryDegree, wholePlaneIID_ae_pastCode_boundaryHitWitnesses,
    wholePlaneIID_ae_uibotAllEdgesPresent] with W H hh hpast hp
  obtain ⟨h0, _⟩ := hh 0
  have hpast' : BoundaryHitWitnesses (kmswPastCode W) := hpast
  exact ⟨H, h0, hpast', hp, uibotWholePlaneGeometricMap_domain W H
    (WholePlanePastGlueDrawing.glueDrawing W h0 hpast' H) hp⟩

/- OPEN units 4–5. Required statistical interface from primary_sol_1, with
all binders (its source appeared during this session; it is not imported):

uibotFiniteIIDWordLaw_admissible_subexponential
  (ell right : ℕ) (hell : 0 < ell) (hright : 0 < right) :
  letI : MeasurableSpace (Fin 3) := ⊤
  ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in Filter.atTop,
    n + ell + right ≡ 0 [MOD 3] →
      Real.exp (-epsilon * (n : ℝ)) ≤
        (uibotFiniteIIDWordLaw n).real
          {w | KMSWWalkAdmissible ell right n w}.

Combine this with the proved conditional concentration theorem in
UIBOTRootWindowConcentration to obtain convergence of the actual finite
optional-window pattern masses. No source probability premise is to be added.

Exact mathematical quantifiers for the remaining transport:
construct a measurable F : (ℤ → Fin 3) → D39GeomRootedMapClass such that,
for wholePlaneIIDCodeMeasure-almost every W, there exist
H : WholePlaneRotationHypothesis W,
h0 : BoundaryHitWitnesses (shiftedStream W 0),
hpast : BoundaryHitWitnesses (kmswPastCode W), and
hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e,
with F W equal to the d39DomainSetoid class of the exact map/root/domain
displayed in wholePlaneIID_ae_uibotGeometricDomain, using the SAME witnesses.

For every ell right : ℕ with hell : 0 < ell and hright : 0 < right,
construct finite maps Ffin(n,hn,hne) from
KMSWMapIsoClass ell right n × Fin n to D39GeomRootedMapClass, for every
n : ℕ, hn : 1 ≤ n and hne : Nonempty (KMSWMapIsoClass ell right n).
For every representative R of q and every j : Fin n, Ffin(n,hn,hne)(q,j)
must represent exactly uibotPeanoRootedAt R j, including its geometric faces.
For every ns : ℕ → ℕ with Tendsto ns atTop atTop, every
hsize : ∀ k, 1 ≤ ns k, every
hne : ∀ k, Nonempty (KMSWMapIsoClass ell right (ns k)), every r : ℕ,
and every b : Quotient (d39GeomBallClassSetoid r), prove
Tendsto (fun k =>
  (uibotFiniteUniformSampleLaw ell right (ns k) hell hright (hsize k) (hne k))
    {p | d39GeomBallClassMap r (Ffin(ns k,hsize k,hne k) p) = b})
  atTop (nhds (wholePlaneIIDCodeMeasure
    {W | d39GeomBallClassMap r (F W) = b})).
Here the ball-class convention uses radius r+1. F and Ffin have not been
defined by arbitrary defaults, and neither their measurability nor this
convergence is assumed by any declaration. The UIBOT qualifier remains. -/

end DirectedDistances.PaperProofs.Section3
