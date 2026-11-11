/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteClassMap
public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteStageExterior
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitIdentification2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable










public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Helper toward Proposition 3.9: DC is the remaining StageGeom-free
deterministic comparison, including the ambient geometry and retained faces. -/
@[expose] def UIBOTDeterministicComparison : Prop :=
  ∀ (n N r : ℕ) (_hr : 0 < r)
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (_hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (_hcap : UIBOTRootWindowCapture (shiftedStream W N) N r),
    Nonempty (D39GeomBallIsoV2 r
      (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega))
      (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G))

/-- Helper toward Proposition 3.9: DI is the remaining drawing-independence
statement, with individual edges and the ordered chronological root. -/
@[expose] def UIBOTDrawingIndependence : Prop :=
  ∀ (w : ℕ → Fin 3) (m j : ℕ) (hj : j ≤ m)
    (P P' : StageDrawing w m) (U : P.Face) (U' : P'.Face)
    (hU : P.IsUnbounded U) (hU' : P'.IsUnbounded U')
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (hborder' : ∀ d, P'.dartBorders d U' ↔ (kmswStageDirectedMap w m).IsOuter d),
    Nonempty (D39GeomRootedMapIsoV2
      (uibotFiniteClassDrawingRootedMap P U hU hborder j hj).map
      (uibotFiniteClassDrawingRootedMap P U hU hborder j hj).root
      (uibotFiniteClassDrawingRootedMap P' U' hU' hborder' j hj).map
      (uibotFiniteClassDrawingRootedMap P' U' hU' hborder' j hj).root)

/-- Helper toward Proposition 3.9: the exact witnesses of the glued
geometric domain, as a proposition used only to choose the a.e. realization. -/
@[expose] def UIBOTGeometricDomainEvent (W : ℤ → Fin 3) : Prop :=
  ∃ (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    D39GeomDomain
      (uibotWholePlaneGeometricMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
      (uibotWholePlaneGeometricRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))

/-- Helper toward Proposition 3.9: choose the already proved glued-domain
witnesses together, so that the root and map use identical choices. -/
@[expose] def uibotGluedRepresentative (W : ℤ → Fin 3) (h : UIBOTGeometricDomainEvent W) :
    D39DomainRootedMap := by
  let H := h.choose
  let h0 := h.choose_spec.choose
  let hpast := h.choose_spec.choose_spec.choose
  let hp := h.choose_spec.choose_spec.choose_spec.choose
  exact { V := WholePlaneVertex W
          E := (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).GeometricEdge
          map := uibotWholePlaneGeometricMap W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp
          root := uibotWholePlaneGeometricRoot W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H)
          domain := h.choose_spec.choose_spec.choose_spec.choose_spec }

/-- Helper toward Proposition 3.9: a canonical finite window representative
rooted at the midpoint, using the certified exterior face. -/
@[expose] def uibotWindowRepresentative (N : ℕ) (v : Fin (2 * N) → Fin 3) :
    D39DomainRootedMap :=
  let D := uibotFiniteClassDrawingChoice (finiteCodeExtend (n := 2 * N + 1) v) (2 * N)
  uibotFiniteClassDrawingRootedMap D.drawing D.exterior D.unbounded D.borders N
    (by omega)

/-- Helper toward Proposition 3.9: the whole-plane class of the exact glued
drawing on its conull domain. The off-domain value is used only in a.e. claims. -/
@[expose] def uibotWholePlaneClassMap (W : ℤ → Fin 3) : D39GeomRootedMapClass := by
  classical
  exact if h : UIBOTGeometricDomainEvent W then
    Quotient.mk d39DomainSetoid (uibotGluedRepresentative W h)
  else Quotient.mk d39DomainSetoid (uibotWindowRepresentative 0 (fun i => Fin.elim0 i))

/-- Helper toward Proposition 3.9: the class map represents the exact glued
drawing a.e., with identical witnesses in its map, root and domain. -/
theorem uibotWholePlaneClassMap_ae_represents :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
        (hdom : D39GeomDomain
          (uibotWholePlaneGeometricMap W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
          (uibotWholePlaneGeometricRoot W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))),
        uibotWholePlaneClassMap W = Quotient.mk d39DomainSetoid
          ({ V := WholePlaneVertex W,
             E := (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).GeometricEdge,
             map := uibotWholePlaneGeometricMap W H
               (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp,
             root := uibotWholePlaneGeometricRoot W H
               (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H),
             domain := hdom } : D39DomainRootedMap) := by
  filter_upwards [wholePlaneIID_ae_uibotGeometricDomain] with W h
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec, ?_⟩
  exact dite_eq_left h

private theorem midpoint_window (N : ℕ) (v : Fin (2 * N) → Fin 3) :
    uibotFiniteRootWindow (n := 2 * N + 1) N v ⟨N, by omega⟩ = some v := by
  have hv : UIBOTRootWindowValid (n := 2 * N + 1) N ⟨N, by omega⟩ := by
    constructor <;> dsimp <;> omega
  rw [uibotFiniteRootWindow, dite_eq_left hv]
  congr 1
  funext i
  congr 1
  apply Fin.ext
  simp only [Nat.sub_self, zero_add]

/-- Helper toward Proposition 3.9: under DC, on each capture event the
whole-plane ball is a.e. a function of the `2*N` coordinates in that window.
The ball-class index `r` denotes geometric radius `r+1`. -/
theorem uibotWholePlaneClassMap_ae_window (DC : UIBOTDeterministicComparison)
    (N r : ℕ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      UIBOTRootWindowCapture (shiftedStream W N) N (r + 1) →
      d39GeomBallClassMap r (uibotWholePlaneClassMap W) =
        Quotient.mk (d39GeomBallClassSetoid r)
          (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)) := by
  filter_upwards [uibotWholePlaneClassMap_ae_represents] with W h hcap
  obtain ⟨H, h0, hpast, hp, hdom, heq⟩ := h
  rw [heq, d39GeomBallClassMap_mk]
  apply Eq.symm
  apply Quotient.sound
  let v : Fin (2 * N) → Fin 3 := fun i => shiftedStream W N i.val
  let D := uibotFiniteClassDrawingChoice (finiteCodeExtend (n := 2 * N + 1) v) (2 * N)
  exact DC (2 * N + 1) N (r + 1) (Nat.succ_pos r) v ⟨N, by omega⟩ W H
    (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp
    D.drawing D.exterior D.unbounded D.borders (midpoint_window N v) hcap

private theorem good_pattern_realization (N : ℕ) (v : Fin (2 * N) → Fin 3) :
    ∃ W : ℤ → Fin 3, UIBOTGeometricDomainEvent W ∧
      (fun i : Fin (2 * N) => shiftedStream W N i.val) = v := by
  by_contra hn
  have hz : wholePlaneIIDCodeMeasure.real
      {W | (fun i : Fin (2 * N) => shiftedStream W N i.val) = v} = 0 := by
    calc
      _ = wholePlaneIIDCodeMeasure.real ∅ := by
        apply measureReal_congr
        filter_upwards [wholePlaneIID_ae_uibotGeometricDomain] with W hW
        exact propext ⟨fun hv => hn ⟨W, hW, hv⟩, False.elim⟩
      _ = 0 := measureReal_empty
  rw [wholePlaneIID_rootWindow_pattern_real] at hz
  exact (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 3) _)) hz

/-- Helper toward Proposition 3.9: under DC the chosen finite geometric
map has the canonical window ball whenever the finite window is captured. -/
theorem uibotFiniteGeometricClassMap_window (DC : UIBOTDeterministicComparison)
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (p : KMSWMapIsoClass ℓ ρ n × Fin n) (N r : ℕ)
    (v : Fin (2 * N) → Fin 3)
    (hw : uibotFiniteRootWindow N ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2 = some v)
    (hc : v ∈ uibotRootCapturePatterns N (r + 1)) :
    d39GeomBallClassMap r (uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne p) =
      Quotient.mk (d39GeomBallClassSetoid r) (uibotWindowRepresentative N v) := by
  obtain ⟨W, hW, hv⟩ := good_pattern_realization N v
  let H := hW.choose
  let h0 := hW.choose_spec.choose
  let hpast := hW.choose_spec.choose_spec.choose
  let hp := hW.choose_spec.choose_spec.choose_spec.choose
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  have hcap : UIBOTRootWindowCapture (shiftedStream W N) N (r + 1) :=
    (uibotRootCapturePatterns_iff W N (r + 1)).mp (hv.symm ▸ hc)
  let c := (kmswProcedureEquiv ℓ ρ n hn).symm p.1
  let D := uibotFiniteClassDrawingChoice (codeExtend c) (n - 1)
  let D' := uibotFiniteClassDrawingChoice (finiteCodeExtend (n := 2 * N + 1) v) (2 * N)
  obtain ⟨e⟩ := DC n N (r + 1) (Nat.succ_pos r) c.val p.2 W H G hp
    D.drawing D.exterior D.unbounded D.borders (hw.trans (congrArg some hv.symm)) hcap
  obtain ⟨f⟩ := DC (2 * N + 1) N (r + 1) (Nat.succ_pos r) v ⟨N, by omega⟩ W H G hp
    D'.drawing D'.exterior D'.unbounded D'.borders
    ((midpoint_window N v).trans (congrArg some hv.symm)) hcap
  apply Quotient.sound
  exact ⟨DirectedDistances.PaperProofs.Section3.trans e f.symm⟩

/-- Helper toward Proposition 3.9: DI identifies every allowed drawing
choice as a geometric rooted class, rather than merely a dart isomorphism. -/
theorem uibotFiniteClassDrawingRootedMap_class_eq (DI : UIBOTDrawingIndependence)
    (w : ℕ → Fin 3) (m j : ℕ) (hj : j ≤ m)
    (D D' : UIBOTFiniteClassDrawingData w m) :
    Quotient.mk d39DomainSetoid
      (uibotFiniteClassDrawingRootedMap D.drawing D.exterior D.unbounded D.borders j hj) =
    Quotient.mk d39DomainSetoid
      (uibotFiniteClassDrawingRootedMap D'.drawing D'.exterior D'.unbounded D'.borders j hj) :=
  Quotient.sound (DI w m j hj D.drawing D'.drawing D.exterior D'.exterior
    D.unbounded D'.unbounded D.borders D'.borders)

private theorem probability_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C : Set Ω)
    (hC : MeasurableSet C) (hBC : B ⊆ C)
    (h : ∀ᵐ x ∂μ, x ∈ C → (x ∈ A ↔ x ∈ B)) :
    |μ.real A - μ.real B| ≤ 1 - μ.real C := by
  have he : A ∩ C =ᵐ[μ] B := by
    filter_upwards [h] with x hx
    exact propext ⟨fun ha => (hx ha.2).mp ha.1,
      fun hb => ⟨(hx (hBC hb)).mpr hb, hBC hb⟩⟩
  have hl : μ.real B ≤ μ.real A := by
    rw [← measureReal_congr he]
    exact measureReal_mono Set.inter_subset_left
  have hu : μ.real A ≤ μ.real B + (1 - μ.real C) := by
    calc
      _ ≤ μ.real ((A ∩ C) ∪ Cᶜ) := measureReal_mono (by
        intro x hx
        by_cases hc : x ∈ C
        · exact Or.inl ⟨hx, hc⟩
        · exact Or.inr hc)
      _ ≤ μ.real (A ∩ C) + μ.real Cᶜ := measureReal_union_le _ _
      _ = _ := by rw [measureReal_congr he, measureReal_compl hC, probReal_univ]
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith only [hu]

/-- Helper toward Proposition 3.9: captured window patterns with a specified
geometric ball class; this is a subset of a finite coordinate space. -/
@[expose] def uibotWindowBallPatterns (N r : ℕ)
    (b : Quotient (d39GeomBallClassSetoid r)) : Set (Fin (2 * N) → Fin 3) :=
  {v | v ∈ uibotRootCapturePatterns N (r + 1) ∧
    Quotient.mk (d39GeomBallClassSetoid r) (uibotWindowRepresentative N v) = b}

/-- Helper toward Proposition 3.9: the fully quantified ball-mass convergence
for the chosen geometric maps, conditional on the remaining deterministic DC.
DI is separately needed for independence of drawing choice, as proved above;
the stronger all-drawings quantifier of DC suffices for this fixed choice.
This is a conditional helper, not Proposition 3.9 or a measurability claim. -/
theorem uibotGeometricBallLaw_tendsto_of_comparison (DC : UIBOTDeterministicComparison)
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (r : ℕ) (b : Quotient (d39GeomBallClassSetoid r)) :
    Tendsto (fun k =>
      (uibotFiniteUniformSampleLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
        {p | d39GeomBallClassMap r
          (uibotFiniteGeometricClassMap ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) p) = b})
      atTop (𝓝 (wholePlaneIIDCodeMeasure
        {W | d39GeomBallClassMap r (uibotWholePlaneClassMap W) = b})) := by
  classical
  let : MeasurableSpace (Fin 3) := ⊤
  let μ := wholePlaneIIDCodeMeasure
  let A : Set (ℤ → Fin 3) :=
    {W | d39GeomBallClassMap r (uibotWholePlaneClassMap W) = b}
  let ν k := uibotFiniteUniformSampleLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k)
  let E k : Set (KMSWMapIsoClass ℓ ρ (ns k) × Fin (ns k)) :=
    {p | d39GeomBallClassMap r
      (uibotFiniteGeometricClassMap ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) p) = b}
  let : ∀ k, IsProbabilityMeasure (ν k) := fun k =>
    uibotFiniteUniformSampleLaw_probability ℓ ρ (ns k) hℓ hρ (hsize k) (hne k)
  apply (ENNReal.tendsto_toReal_iff (fun k => measure_ne_top (ν k) (E k))
    (measure_ne_top μ A)).mp
  change Tendsto (fun k => (ν k).real (E k)) atTop (𝓝 (μ.real A))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hcaplarge := (wholePlaneIID_uibotRootWindowCapture_tendsto_one_real (r + 1)).eventually
    (lt_mem_nhds (show (1 : ℝ) - ε / 4 < 1 by linarith only [hε]))
  obtain ⟨N, hN⟩ := hcaplarge.exists
  let : MeasurableSpace (Option (Fin (2 * N) → Fin 3)) := ⊤
  let S := uibotWindowBallPatterns N r b
  let C : Set (ℤ → Fin 3) :=
    {W | UIBOTRootWindowCapture (shiftedStream W N) N (r + 1)}
  let B : Set (ℤ → Fin 3) :=
    {W | (fun i : Fin (2 * N) => shiftedStream W N i.val) ∈ S}
  have hBC : B ⊆ C := fun W hW =>
    (uibotRootCapturePatterns_iff W N (r + 1)).mp hW.1
  have heq : ∀ᵐ W ∂μ, W ∈ C → (W ∈ A ↔ W ∈ B) := by
    filter_upwards [uibotWholePlaneClassMap_ae_window DC N r] with W hW hc
    have hw := hW hc
    change d39GeomBallClassMap r (uibotWholePlaneClassMap W) = b ↔ _
    rw [hw]
    exact ⟨fun hb => ⟨(uibotRootCapturePatterns_iff W N (r + 1)).mpr hc, hb⟩,
      fun hb => hb.2⟩
  have herr := probability_error μ A B C (measurableSet_uibotRootWindowCapture N (r + 1))
    hBC heq
  have herrsmall : |μ.real A - μ.real B| < ε / 4 := by
    exact herr.trans_lt (by change 1 - μ.real C < ε / 4; linarith only [hN])
  let law k := uibotFiniteRootWindowLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) N
  have ht := uibotFiniteRootWindowLaw_event_tendsto ℓ ρ hℓ hρ ns hns hsize hne N S
  have hclose := (Metric.tendsto_atTop.mp ht) (ε / 4) (by positivity)
  obtain ⟨K₁, hK₁⟩ := hclose
  have hbadlim := uibotFiniteRootWindowLaw_event_tendsto
    ℓ ρ hℓ hρ ns hns hsize hne N (uibotRootCapturePatterns N (r + 1))ᶜ
  have hbadmass : μ.real {W | (fun i : Fin (2 * N) => shiftedStream W N i.val) ∈
      (uibotRootCapturePatterns N (r + 1))ᶜ} = 1 - μ.real C := by
    have hset : {W | (fun i : Fin (2 * N) => shiftedStream W N i.val) ∈
        (uibotRootCapturePatterns N (r + 1))ᶜ} = Cᶜ := by
      ext W
      exact not_congr (uibotRootCapturePatterns_iff W N (r + 1))
    rw [hset, measureReal_compl (measurableSet_uibotRootWindowCapture N (r + 1)),
      probReal_univ]
  rw [hbadmass] at hbadlim
  have hthreshold : 1 - μ.real C < 3 * ε / 8 := by linarith only [hN, hε]
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp
    (hbadlim.eventually (gt_mem_nhds hthreshold))
  have hnonelim := uibotFiniteRootWindowLaw_none_tendsto_zero
    ℓ ρ hℓ hρ ns hns hsize hne N
  obtain ⟨K₃, hK₃⟩ := eventually_atTop.mp
    (hnonelim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 8 by positivity)))
  refine ⟨max K₁ (max K₂ K₃), fun k hk => ?_⟩
  let : MeasurableSpace (KMSWMapIsoClass ℓ ρ (ns k)) := ⊤
  let : MeasurableSpace (Fin (ns k)) := ⊤
  let := uibotFiniteMapFintype ℓ ρ (ns k) (hsize k)
  let win (p : KMSWMapIsoClass ℓ ρ (ns k) × Fin (ns k)) :=
    uibotFiniteRootWindow N ((kmswProcedureEquiv ℓ ρ (ns k) (hsize k)).symm p.1).val p.2
  let Bk := win ⁻¹' (Option.some '' S)
  let Ck := win ⁻¹' (Option.some '' uibotRootCapturePatterns N (r + 1))
  have hmap (T : Set (Option (Fin (2 * N) → Fin 3))) :
      (law k).real T = (ν k).real (win ⁻¹' T) := by
    change ((ν k).map win T).toReal = _
    rw [Measure.map_apply (measurable_of_countable win) MeasurableSet.of_discrete]
    rfl
  have hBkCk : Bk ⊆ Ck := by
    rintro p ⟨v, hv, he⟩
    exact ⟨v, hv.1, he⟩
  have hEqk : ∀ᵐ p ∂ν k, p ∈ Ck → (p ∈ E k ↔ p ∈ Bk) := by
    apply Eventually.of_forall
    intro p hp
    obtain ⟨v, hc, hw⟩ := hp
    have hball := uibotFiniteGeometricClassMap_window DC ℓ ρ (ns k) hℓ hρ
      (hsize k) (hne k) p N r v hw.symm hc
    constructor
    · intro hp
      exact ⟨v, ⟨hc, hball.symm.trans hp⟩, hw⟩
    · rintro ⟨v', hv', hw'⟩
      have hvv : v' = v := Option.some.inj (hw'.trans hw.symm)
      exact hball.trans (hvv ▸ hv'.2)
  have herrk := probability_error (ν k) (E k) Bk Ck
    (measurable_of_countable win MeasurableSet.of_discrete) hBkCk hEqk
  have hCk : (ν k).real Ck = (law k).real
      (Option.some '' uibotRootCapturePatterns N (r + 1)) := (hmap _).symm
  have hBk : (ν k).real Bk = (law k).real (Option.some '' S) := (hmap _).symm
  have hsmallk : |(ν k).real (E k) - (ν k).real Bk| < ε / 2 := by
    rw [hCk] at herrk
    let : IsProbabilityMeasure (law k) :=
      uibotFiniteRootWindowLaw_probability ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) N
    have hpartition : (Option.some '' uibotRootCapturePatterns N (r + 1))ᶜ =
        ({none} : Set (Option (Fin (2 * N) → Fin 3))) ∪
          Option.some '' (uibotRootCapturePatterns N (r + 1))ᶜ := by
      ext x
      cases x <;> simp
    have hsum : 1 - (law k).real (Option.some '' uibotRootCapturePatterns N (r + 1)) ≤
        (law k).real {none} +
          (law k).real (Option.some '' (uibotRootCapturePatterns N (r + 1))ᶜ) := by
      rw [← probReal_univ (μ := law k), ← measureReal_compl MeasurableSet.of_discrete,
        hpartition]
      exact measureReal_union_le _ _
    have hb := hK₂ k (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk)
    have hn := hK₃ k (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk)
    exact (herrk.trans hsum).trans_lt (by linarith only [hb, hn])
  have hpattern : |(ν k).real Bk - μ.real B| < ε / 4 := by
    rw [hBk]
    exact hK₁ k (le_trans (le_max_left _ _) hk)
  rw [Real.dist_eq]
  calc
    |(ν k).real (E k) - μ.real A| ≤
        |(ν k).real (E k) - (ν k).real Bk| +
          |(ν k).real Bk - μ.real B| + |μ.real A - μ.real B| := by
      calc
        _ = |((ν k).real (E k) - (ν k).real Bk) +
          ((ν k).real Bk - μ.real B) + (μ.real B - μ.real A)| := by ring_nf
        _ ≤ |(ν k).real (E k) - (ν k).real Bk| +
            |(ν k).real Bk - μ.real B| + |μ.real B - μ.real A| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ = _ := by rw [abs_sub_comm (μ.real B) (μ.real A)]
    _ < ε := by linarith only [hsmallk, hpattern, herrsmall]

section MeasurableRealization

local instance : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass

/-- Helper toward Proposition 3.9: DC alone makes the exact glued class
choice a.e. measurable. Finite coordinate approximations converge a.e.; no
separability assumption on the full geometric class space is required. -/
theorem aemeasurable_uibotWholePlaneClassMap (DC : UIBOTDeterministicComparison) :
    AEMeasurable uibotWholePlaneClassMap wholePlaneIIDCodeMeasure := by
  let : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  let f (N : ℕ) (W : ℤ → Fin 3) : D39GeomRootedMapClass :=
    Quotient.mk d39DomainSetoid
      (uibotWindowRepresentative N (fun i => shiftedStream W N i.val))
  have hf (N : ℕ) : Measurable (f N) := by
    have hcoord : Measurable (fun W : ℤ → Fin 3 =>
        (fun i : Fin (2 * N) => shiftedStream W N i.val)) :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    exact (measurable_of_countable (fun v => Quotient.mk d39DomainSetoid
      (uibotWindowRepresentative N v))).comp hcoord
  apply aemeasurable_of_tendsto_metrizable_ae' (fun N => (hf N).aemeasurable)
  have heq : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N r : ℕ,
      UIBOTRootWindowCapture (shiftedStream W N) N (r + 1) →
      d39GeomBallClassMap r (uibotWholePlaneClassMap W) =
        d39GeomBallClassMap r (f N W) := by
    apply ae_all_iff.mpr
    intro N
    apply ae_all_iff.mpr
    intro r
    exact uibotWholePlaneClassMap_ae_window DC N r
  filter_upwards [heq, wholePlaneIID_ae_eventual_uibotRootWindowCapture] with W hW hcap
  apply EMetric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt hε)
  obtain ⟨N₀, hN₀⟩ := hcap (r + 1)
  refine ⟨N₀, fun N hN => ?_⟩
  have hm : f N W ∈ Metric.eball (uibotWholePlaneClassMap W) ((1 / 2 : ℝ≥0∞) ^ r) := by
    rw [d39GeomClass_openBall_eq_ballClass]
    exact hW N r (hN₀ N hN)
  exact lt_trans hm (by simpa only [one_div] using hr)

/-- Helper toward Proposition 3.9: a measurable version of the whole-plane
class map, changed only on a null set. Its definition is conditional on DC. -/
@[expose] def uibotMeasurableWholePlaneClassMap (DC : UIBOTDeterministicComparison) :
    (ℤ → Fin 3) → D39GeomRootedMapClass :=
  (aemeasurable_uibotWholePlaneClassMap DC).mk uibotWholePlaneClassMap

/-- Helper toward Proposition 3.9: the measurable version is Borel measurable. -/
theorem measurable_uibotMeasurableWholePlaneClassMap (DC : UIBOTDeterministicComparison) :
    Measurable (uibotMeasurableWholePlaneClassMap DC) :=
  (aemeasurable_uibotWholePlaneClassMap DC).measurable_mk

/-- Helper toward Proposition 3.9: the measurable version agrees a.e. with
the glued geometric class, hence preserves all captured-window identities. -/
theorem uibotMeasurableWholePlaneClassMap_ae_eq (DC : UIBOTDeterministicComparison) :
    uibotMeasurableWholePlaneClassMap DC =ᵐ[wholePlaneIIDCodeMeasure]
      uibotWholePlaneClassMap :=
  (aemeasurable_uibotWholePlaneClassMap DC).ae_eq_mk.symm

/-- Helper toward Proposition 3.9: the Borel measurable version represents
the exact glued drawing a.e., retaining the same witnesses in every field. -/
theorem uibotMeasurableWholePlaneClassMap_ae_represents (DC : UIBOTDeterministicComparison) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
        (hdom : D39GeomDomain
          (uibotWholePlaneGeometricMap W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
          (uibotWholePlaneGeometricRoot W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))),
        uibotMeasurableWholePlaneClassMap DC W = Quotient.mk d39DomainSetoid
          ({ V := WholePlaneVertex W,
             E := (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).GeometricEdge,
             map := uibotWholePlaneGeometricMap W H
               (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp,
             root := uibotWholePlaneGeometricRoot W H
               (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H),
             domain := hdom } : D39DomainRootedMap) := by
  filter_upwards [uibotMeasurableWholePlaneClassMap_ae_eq DC,
    uibotWholePlaneClassMap_ae_represents] with W hW hrep
  rw [hW]
  exact hrep

/-- Helper toward Proposition 3.9: on every capture event the measurable
version's ball is a.e. a measurable function of just `2*N` coordinates. -/
theorem uibotMeasurableWholePlaneClassMap_ae_window (DC : UIBOTDeterministicComparison)
    (N r : ℕ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      UIBOTRootWindowCapture (shiftedStream W N) N (r + 1) →
      d39GeomBallClassMap r (uibotMeasurableWholePlaneClassMap DC W) =
        Quotient.mk (d39GeomBallClassSetoid r)
          (uibotWindowRepresentative N (fun i => shiftedStream W N i.val)) := by
  filter_upwards [uibotMeasurableWholePlaneClassMap_ae_eq DC,
    uibotWholePlaneClassMap_ae_window DC N r] with W hW hcap
  rw [hW]
  exact hcap

/-- Helper toward Proposition 3.9: for the Borel measurable whole-plane
version, every finite ball class has the required actual finite-map limit.
DC and DI remain deterministic open inputs; DI certifies independence of
drawing choice, while DC suffices for this fixed-choice convergence. -/
theorem uibotMeasurableGeometricBallLaw_tendsto
    (DC : UIBOTDeterministicComparison) (_DI : UIBOTDrawingIndependence)
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (r : ℕ) (b : Quotient (d39GeomBallClassSetoid r)) :
    Tendsto (fun k =>
      (uibotFiniteUniformSampleLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
        {p | d39GeomBallClassMap r
          (uibotFiniteGeometricClassMap ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) p) = b})
      atTop (𝓝 (wholePlaneIIDCodeMeasure
        {W | d39GeomBallClassMap r (uibotMeasurableWholePlaneClassMap DC W) = b})) := by
  have heq : wholePlaneIIDCodeMeasure
      {W | d39GeomBallClassMap r (uibotMeasurableWholePlaneClassMap DC W) = b} =
      wholePlaneIIDCodeMeasure
        {W | d39GeomBallClassMap r (uibotWholePlaneClassMap W) = b} := by
    apply measure_congr
    filter_upwards [uibotMeasurableWholePlaneClassMap_ae_eq DC] with W hW
    rw [hW]
  rw [heq]
  exact uibotGeometricBallLaw_tendsto_of_comparison DC ℓ ρ hℓ hρ ns hns hsize hne r b

end MeasurableRealization

end DirectedDistances.PaperProofs.Section3

end
