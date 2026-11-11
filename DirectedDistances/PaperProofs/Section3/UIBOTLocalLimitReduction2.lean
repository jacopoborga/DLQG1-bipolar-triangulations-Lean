/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitReduction

/-! # Ball-level drawing independence toward Proposition 3.9

On a captured window, DC compares every exterior-certified finite drawing
with the same whole-plane drawing. Composition gives independence of the
finite geometric ball, including its edge identities, orientation and faces.
The ball-class index `r` denotes geometric radius `r + 1`.

The finite-map ball-mass convergence below requires only DC. The full-map
DI statement is neither assumed nor deduced: the imported convergence proof
uses only captured ball classes. DC remains the single open deterministic
input to this reduction. This file does not prove Proposition 3.9. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Helper toward Proposition 3.9: on a captured root window, DC identifies
the radius-`r` balls of any two exterior-certified drawings of the same
finite stage at the same chronological root. -/
theorem uibotFiniteStageExterior_ballIso_of_comparison
    (DC : UIBOTDeterministicComparison)
    (n N r : ℕ) (hr : 0 < r)
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P P' : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (U' : P'.Face)
    (hU : P.IsUnbounded U) (hU' : P'.IsUnbounded U')
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hborder' : ∀ d, P'.dartBorders d U' ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    Nonempty (D39GeomBallIsoV2 r
      (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega))
      (uibotFiniteStageExteriorMap P' U' hU' hborder')
      (uibotFiniteStageExteriorRoot P' j.val (by have := j.isLt; omega))) := by
  obtain ⟨e⟩ := DC n N r hr w j W H G hp P U hU hborder hwindow hcap
  obtain ⟨f⟩ := DC n N r hr w j W H G hp P' U' hU' hborder' hwindow hcap
  exact ⟨DirectedDistances.PaperProofs.Section3.trans e f.symm⟩

/-- Helper toward Proposition 3.9: on a captured window, the radius-`r + 1`
ball class of a finite rooted drawing is independent of all choices of
exterior-certified drawing data, under DC alone. -/
theorem uibotFiniteClassDrawingRootedMap_ballClass_eq_of_comparison
    (DC : UIBOTDeterministicComparison)
    (n N r : ℕ) (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (D D' : UIBOTFiniteClassDrawingData (finiteCodeExtend w) (n - 1))
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N (r + 1)) :
    d39GeomBallClassMap r (Quotient.mk d39DomainSetoid
      (uibotFiniteClassDrawingRootedMap D.drawing D.exterior D.unbounded D.borders
        j.val (by have := j.isLt; omega))) =
    d39GeomBallClassMap r (Quotient.mk d39DomainSetoid
      (uibotFiniteClassDrawingRootedMap D'.drawing D'.exterior D'.unbounded D'.borders
        j.val (by have := j.isLt; omega))) := by
  apply (d39GeomBallClassMap_mk_eq_iff r _ _).mpr
  exact uibotFiniteStageExterior_ballIso_of_comparison DC n N (r + 1)
    (Nat.succ_pos r) w j W H G hp D.drawing D'.drawing D.exterior D'.exterior
    D.unbounded D'.unbounded D.borders D'.borders hwindow hcap

/-- Helper toward Proposition 3.9: on each captured root window, changing
the drawing chosen by the actual finite class map leaves its ball class
unchanged, under DC alone. -/
theorem uibotFiniteGeometricClassMap_ball_eq_of_comparison
    (DC : UIBOTDeterministicComparison)
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (p : KMSWMapIsoClass ℓ ρ n × Fin n) (N r : ℕ)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (D : UIBOTFiniteClassDrawingData
      (codeExtend ((kmswProcedureEquiv ℓ ρ n hn).symm p.1)) (n - 1))
    (hwindow : uibotFiniteRootWindow N
      ((kmswProcedureEquiv ℓ ρ n hn).symm p.1).val p.2 =
        some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N (r + 1)) :
    d39GeomBallClassMap r (uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne p) =
    d39GeomBallClassMap r (Quotient.mk d39DomainSetoid
      (uibotFiniteClassDrawingRootedMap D.drawing D.exterior D.unbounded D.borders
        p.2.val (by have := p.2.isLt; omega))) := by
  let c := (kmswProcedureEquiv ℓ ρ n hn).symm p.1
  exact uibotFiniteClassDrawingRootedMap_ballClass_eq_of_comparison DC n N r c.val p.2
    W H G hp (uibotFiniteClassDrawingChoice (codeExtend c) (n - 1)) D hwindow hcap

/-- Helper toward Proposition 3.9: the finite geometric ball masses
converge to those of the Borel measurable whole-plane realization with DC
as the only remaining deterministic input; no full-map DI is required. -/
theorem uibotMeasurableGeometricBallLaw_tendsto_of_comparison
    (DC : UIBOTDeterministicComparison)
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

end DirectedDistances.PaperProofs.Section3

end
