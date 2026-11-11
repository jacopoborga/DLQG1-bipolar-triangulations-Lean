/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneSeamCuts
public import DirectedDistances.KMSW.MonotoneSeamAffine
public import DirectedDistances.KMSW.MonotoneSeamVertices
public import DirectedDistances.KMSW.WholePlanePastGlueGeometry
public import DirectedDistances.PlanarMap.SeamSectorDirection
public import DirectedDistances.PlanarMap.SeamSectorTurn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace DirectedDistances.KMSW.WholePlaneGlueSeamSectors

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
open scoped Classical Topology

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)
  (k : ℤ)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0)
  (monotone_family_all w0)
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "pos" => gluedPos W h0 hp H
local notation "arc" => gluedArc W h0 hp H
local notation "x0" => seamX w0 h0 ((And.left H) 0) k




private theorem seamCut_isolated :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ c ∈ seamCutSet w0 h0 ((And.left H) 0),
        c ≠ x0 → c ∉ Ioo (x0 - r) (x0 + r) := by
  classical
  let F : Set ℝ :=
    (seamCutSet w0 h0 ((And.left H) 0) ∩ Icc (x0 - 1) (x0 + 1)) \ {x0}
  have hF : F.Finite := by
    dsimp [F]
    exact (seamCutSet_inter_Icc_finite w0 h0 ((And.left H) 0)
      (x0 - 1) (x0 + 1)).sdiff
  have hxF : x0 ∉ F := by
    simp [F]
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 hF.isClosed.isOpen_compl x0 hxF
  let r := min 1 (ε / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min zero_lt_one (half_pos hε)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hre : r ≤ ε := by
    dsimp [r]
    exact (min_le_right 1 (ε / 2)).trans (by linarith [hε])
  refine ⟨r, hr, hr1, ?_⟩
  intro c hc hne hcnear
  have hcIcc : c ∈ Icc (x0 - 1) (x0 + 1) := by
    constructor <;> linarith [hcnear.1, hcnear.2, hr1]
  have hdist : |c - x0| < ε := by
    rw [abs_lt]
    constructor <;> linarith [hcnear.1, hcnear.2, hre]
  have hballc : c ∈ Metric.ball x0 ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hdist
  have hnot : c ∉ F := hball hballc
  exact hnot ⟨⟨hc, hcIcc⟩, hne⟩




theorem seam_window :
    ∃ r sL sR : ℝ, 0 < r ∧
      (∀ x ∈ Icc x0 (x0 + r), f0 x = f0 x0 + sR * (x - x0)) ∧
      (∀ x ∈ Icc (x0 - r) x0, f0 x = f0 x0 + sL * (x - x0)) := by
  obtain ⟨r, hr, hr1, hiso⟩ := seamCut_isolated W h0 H k
  have hnoR (c : ℝ) (hc : c ∈ seamCutSet w0 h0 ((And.left H) 0)) :
      c ∉ Ioo x0 (x0 + r) := by
    intro hcr
    rcases hcr with ⟨hcr1, hcr2⟩
    exact hiso c hc (ne_of_gt hcr1) ⟨by linarith [hr, hcr1], hcr2⟩
  have hnoL (c : ℝ) (hc : c ∈ seamCutSet w0 h0 ((And.left H) 0)) :
      c ∉ Ioo (x0 - r) x0 := by
    intro hcl
    rcases hcl with ⟨hcl1, hcl2⟩
    exact hiso c hc (ne_of_lt hcl2) ⟨hcl1, by linarith [hr, hcl2]⟩
  obtain ⟨mR, bR, hR⟩ := seamFun_affine_of_noCut w0 h0
    ((And.left H) 0) x0 (x0 + r) (by linarith) hnoR
  obtain ⟨mL, bL, hL⟩ := seamFun_affine_of_noCut w0 h0
    ((And.left H) 0) (x0 - r) x0 (by linarith) hnoL
  have hbaseR := hR x0 ⟨le_rfl, by linarith⟩
  have hbaseL := hL x0 ⟨by linarith, le_rfl⟩
  refine ⟨r, mL, mR, hr, ?_, ?_⟩
  · intro x hx
    rw [hR x hx, hbaseR]
    ring
  · intro x hx
    rw [hL x hx, hbaseL]
    ring




@[expose] noncomputable def seamWindowR (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (H : WholePlaneRotationHypothesis W) (k : ℤ) : ℝ := Classical.choose (seam_window W h0 H k)




theorem seam_window_slopes : ∃ sL sR : ℝ,
    (∀ x ∈ Icc x0 (x0 + seamWindowR W h0 H k),
      f0 x = f0 x0 + sR * (x - x0)) ∧
    (∀ x ∈ Icc (x0 - seamWindowR W h0 H k) x0,
      f0 x = f0 x0 + sL * (x - x0)) := by
  obtain ⟨sL, sR, _, hR, hL⟩ :=
    Classical.choose_spec (seam_window W h0 H k)
  exact ⟨sL, sR, hR, hL⟩




@[expose] noncomputable def seamSlopeL (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (H : WholePlaneRotationHypothesis W) (k : ℤ) : ℝ :=
  Classical.choose (seam_window_slopes W h0 H k)




@[expose] noncomputable def seamSlopeR (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (H : WholePlaneRotationHypothesis W) (k : ℤ) : ℝ :=
  Classical.choose (Classical.choose_spec (seam_window_slopes W h0 H k))




theorem seamWindow_spec :
    0 < seamWindowR W h0 H k ∧
      (∀ x ∈ Icc x0 (x0 + seamWindowR W h0 H k),
        f0 x = f0 x0 + seamSlopeR W h0 H k * (x - x0)) ∧
      (∀ x ∈ Icc (x0 - seamWindowR W h0 H k) x0,
        f0 x = f0 x0 + seamSlopeL W h0 H k * (x - x0)) := by
  obtain ⟨_, _, hr, _, _⟩ := Classical.choose_spec (seam_window W h0 H k)
  refine ⟨hr, ?_⟩
  have hsL : ∃ sR : ℝ,
      (∀ x ∈ Icc x0 (x0 + seamWindowR W h0 H k),
        f0 x = f0 x0 + sR * (x - x0)) ∧
      (∀ x ∈ Icc (x0 - seamWindowR W h0 H k) x0,
        f0 x = f0 x0 + seamSlopeL W h0 H k * (x - x0)) :=
    Classical.choose_spec (seam_window_slopes W h0 H k)
  have hs := Classical.choose_spec hsL
  simpa only [seamSlopeR, seamSlopeL] using hs




theorem runZero_nonseam_aboveSector
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (d : ℕ × Bool)
    (hd : kmswLimitDartVertex w0 d = boundaryVertex w0 h0 k)
    (hne : ∀ j : ℤ, d.1 ≠ boundaryOuterEdge w0 h0 j) :
    AboveSector (seamSlopeL W h0 H k) (seamSlopeR W h0 H k)
      ((P0).arc d).initialDirection := by
  have hs : ((P0).arc d).start = (⟨x0, f0 x0⟩ : ℂ) := by
    calc
      ((P0).arc d).start = (P0).pos (kmswLimitDartVertex w0 d) := (P0).arc_start d
      _ = (P0).pos (boundaryVertex w0 h0 k) := congrArg (P0).pos hd
      _ = (⟨x0, f0 x0⟩ : ℂ) := by
        rw [boundaryVertex_pos_eq w0 h0 ((And.left H) 0) k]
  have hpt : ((P0).arc d).point 1 ≠ ((P0).arc d).start := by
    intro h
    apply (P0).initial_nonzero d
    change ((P0).arc d).point 1 - ((P0).arc d).start = 0
    exact sub_eq_zero.mpr h
  have hw := seamWindow_spec W h0 H k
  unfold AboveSector
  exact initialDirection_above_graph f0 x0 (seamWindowR W h0 H k)
    (seamSlopeL W h0 H k) (seamSlopeR W h0 H k) hw.1 hw.2.1 hw.2.2
    ((P0).arc d) hs ((P0).arc_length d) hpt
    (fun z hz => by
      have hz' : z ∈
          (WholePlanePastGlueData.gluedArc W h0 hp H (wholePlaneDartι W 0 d)).interior := by
        rw [WholePlanePastGlueData.gluedArc_runZero W h0 hp H d]
        exact hz
      exact WholePlanePastGlueGeometry.runZero_interior_above W h0 hp H d hne hz')




theorem past_nonseam_belowSector (d : ℕ × Bool)
    (hd : kmswLimitDartVertex wp d = boundaryVertex wp hp (1 - k))
    (hne : ¬ kmswPastSeamEdge W d.1) :
    BelowSector (seamSlopeL W h0 H k) (seamSlopeR W h0 H k)
      ((Pt).arc d).initialDirection := by
  have hs : ((Pt).arc d).start = (⟨x0, f0 x0⟩ : ℂ) := by
    calc
      ((Pt).arc d).start = (Pt).pos (kmswLimitDartVertex wp d) := (Pt).arc_start d
      _ = (Pt).pos (boundaryVertex wp hp (1 - k)) := congrArg (Pt).pos hd
      _ = (P0).pos (boundaryVertex w0 h0 k) := by
        rw [pastDrawing_seam_pos W h0 hp H (1 - k)]
        have hidx : (1 : ℤ) - (1 - k) = k := by omega
        rw [hidx]
      _ = (⟨x0, f0 x0⟩ : ℂ) := by
        rw [boundaryVertex_pos_eq w0 h0 ((And.left H) 0) k]
  have hpt : ((Pt).arc d).point 1 ≠ ((Pt).arc d).start := by
    intro h
    apply (Pt).initial_nonzero d
    change ((Pt).arc d).point 1 - ((Pt).arc d).start = 0
    exact sub_eq_zero.mpr h
  have hw := seamWindow_spec W h0 H k
  unfold BelowSector
  have hbelow : ∀ z ∈ ((Pt).arc d).interior, z.im < f0 z.re := by
    intro z hz
    have hz' : z ∈
        (WholePlanePastGlueData.gluedArc W h0 hp H (kmswPastDart W d)).interior := by
      rw [WholePlanePastGlueData.gluedArc_past W h0 hp H d hne]
      exact hz
    exact WholePlanePastGlueGeometry.past_interior_below W h0 hp H d hne hz'
  exact initialDirection_below_graph f0 x0 (seamWindowR W h0 H k)
    (seamSlopeL W h0 H k) (seamSlopeR W h0 H k) hw.1 hw.2.1 hw.2.2
    ((Pt).arc d) hs ((Pt).arc_length d) hpt hbelow

end
end DirectedDistances.KMSW.WholePlaneGlueSeamSectors
