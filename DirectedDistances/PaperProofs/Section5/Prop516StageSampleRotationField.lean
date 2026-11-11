/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleFrontierField
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRotation

/-! # Sample stage rotation field

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Proposition 5.16. Translation of the plane preserves the
winding-based orientation predicate used by the topological successor field. -/
theorem orientationPreserving_addLeft (p : ℂ) :
    OrientationPreserving (Homeomorph.addLeft p) := by
  intro z L w hw n
  change HasWinding L w n ↔
    HasWinding (L.map (Homeomorph.addLeft p).continuous) (p + w) n
  have hmap (t : I) : (L.map (Homeomorph.addLeft p).continuous) t = p + L t := by
    change (Homeomorph.addLeft p) (L t) = p + L t
    rfl
  constructor
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    rw [hmap]
    calc
      Complex.exp (φ t) = L t - w := hφ t
      _ = (p + L t) - (p + w) := by ring
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    have hφt := hφ t
    rw [hmap t] at hφt
    calc
      Complex.exp (φ t) = (p + L t) - (p + w) := hφt
      _ = L t - w := by ring

/-- Helper toward Proposition 5.16. In any finite PL drawing, the rotation
successor at a vertex is the topological counterclockwise successor of the
parameterized polyline arcs. Translation to the vertex straightens their
initial subarcs; directions are positive rescalings of the initial segment
directions, which leaves their rays and angular order unchanged. -/
theorem plDrawing_toPath_rotation_topological_ccwSuccessor
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) :
    D39TopologicalCcwSuccessor {e | vert e = vert d}
      (fun e t => (P.arc e).toPath t) d (rot d) := by
  classical
  let star : Set D := {e | vert e = vert d}
  let scale : D → ℝ := fun e =>
    if (P.arc e).points.length = 2 then (1 / 2 : ℝ) else 1
  let dir : D → ℂ := fun e =>
    (scale e : ℂ) * (P.arc e).initialDirection
  let H : ℂ ≃ₜ ℂ := Homeomorph.addLeft (-P.pos (vert d))
  have hscale (e : D) : 0 < scale e := by
    by_cases hn : (P.arc e).points.length = 2
    · simp [scale, hn]
    · simp [scale, hn]
  refine ⟨H, orientationPreserving_addLeft _, dir, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hdir := P.initial_nonzero x
    exact mul_ne_zero (by exact_mod_cast ne_of_gt (hscale x)) hdir
  · intro x hx y hy harg
    have harg' : Complex.arg (P.arc x).initialDirection =
        Complex.arg (P.arc y).initialDirection := by
      dsimp [dir] at harg
      rw [Complex.arg_real_mul _ (hscale x),
        Complex.arg_real_mul _ (hscale y)] at harg
      exact harg
    exact P.initial_arg_injective x y (by exact hx.trans hy.symm) harg'
  · have hscaleStar : ∀ e ∈ star, 0 < scale e := by
      intro e he
      exact hscale e
    exact (ccwSuccessor_smul_pos star
      (fun e => (P.arc e).initialDirection) scale hscaleStar d (rot d)).2
      (P.rotation_agreement d)
  · intro x hx
    let p := P.arc x
    let t : I := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
    have hparam (s : I) (hs : (s : ℝ) ≤ 1 / 2) :
        (H ((P.arc x).toPath s)) =
          (((2 * (s : ℝ) : ℝ) : ℂ) * dir x) := by
      have hle : (s : ℝ) ≤ Polyline.segmentParameterEnd p.points.length 0 := by
        by_cases hn : p.points.length = 2
        · have hend : Polyline.segmentParameterEnd p.points.length 0 = 1 := by
            rw [hn]
            norm_num [Polyline.segmentParameterEnd]
          rw [hend]
          exact le_trans hs (by norm_num)
        · have hne : 0 + 2 ≠ p.points.length := by omega
          have hend : Polyline.segmentParameterEnd p.points.length 0 = 1 / 2 := by
            norm_num [Polyline.segmentParameterEnd, hne]
          rw [hend]
          exact hs
      have hfirst := Polyline.toPath_firstSegment_parameter_affine_apply
        p (P.arc_length x) s hle
      rw [Polyline.segmentParameterStart_zero] at hfirst
      simp only [p.point_zero_eq_start] at hfirst
      have hdirStart : p.point 1 - p.start = p.initialDirection := rfl
      have hxv : vert x = vert d := hx
      have hpos : p.start = P.pos (vert d) := by
        rw [P.arc_start x, hxv]
      by_cases hn : p.points.length = 2
      · have hend : Polyline.segmentParameterEnd p.points.length 0 = 1 := by
          simp [Polyline.segmentParameterEnd, hn]
        rw [hend] at hfirst
        simp only [sub_zero, div_one] at hfirst
        rw [hdirStart] at hfirst
        change -(P.pos (vert d)) + p.toPath s = _
        rw [hfirst, hpos]
        simp only [dir, scale, p, hn]
        push_cast
        ring_nf
      · have hne : 0 + 2 ≠ p.points.length := by omega
        have hend : Polyline.segmentParameterEnd p.points.length 0 = 1 / 2 := by
          norm_num [Polyline.segmentParameterEnd, hne]
        rw [hend] at hfirst
        simp only [sub_zero] at hfirst
        rw [hdirStart] at hfirst
        have hcoeff : (s : ℝ) / (1 / 2 : ℝ) = 2 * (s : ℝ) := by ring
        rw [hcoeff] at hfirst
        change -(P.pos (vert d)) + p.toPath s = _
        rw [hfirst, hpos]
        simp only [dir, scale, p, hn]
        push_cast
        ring_nf
    have ht : t ∈ Set.Icc (0 : I) t := ⟨by norm_num [t], le_rfl⟩
    refine ⟨t, by norm_num [t], by norm_num [t], ?_⟩
    apply Set.ext
    intro z
    constructor
    · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
      have hzero : (s : ℝ) ≥ 0 := by exact_mod_cast hs.1
      have hhalf : (s : ℝ) ≤ 1 / 2 := by exact_mod_cast hs.2
      refine ⟨(2 * (s : ℝ)), by positivity, ?_, ?_⟩
      · nlinarith
      · rw [hparam s hhalf]
    · rintro ⟨r, hr0, hr1, hz⟩
      let s : I := ⟨r / 2, ⟨by nlinarith, by nlinarith⟩⟩
      have hs : s ∈ Set.Icc (0 : I) t := by
        constructor
        · exact s.property.1
        · exact_mod_cast (by change r / 2 ≤ (1 / 2 : ℝ); nlinarith)
      refine ⟨(P.arc x).toPath s, ?_, ?_⟩
      · exact ⟨s, hs, rfl⟩
      · calc
          H ((P.arc x).toPath s) =
              (((2 * (s : ℝ) : ℝ) : ℂ) * dir x) := hparam s (by
                change (r / 2 : ℝ) ≤ 1 / 2
                nlinarith)
          _ = (r : ℂ) * dir x := by
                congr 1
                simp only [s]
                push_cast
                ring
          _ = z := hz.symm

/-- Helper toward Proposition 5.16. Every finite KMSW stage admits a
canonical layout drawing whose polyline arcs realize its topological
counterclockwise rotation successor. -/
theorem kmswStage_topological_rotation_ccwSuccessor_all
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ h : LayoutGood w n,
      ∀ d : StageDart (kmswStage w n).nextEdge,
        D39TopologicalCcwSuccessor
          {e | stageVertex w n e = stageVertex w n d}
          (fun e t => ((monotoneLayoutDrawing w n h).arc e).toPath t)
          d (stageRot w n d) := by
  obtain ⟨h, _⟩ := kmswStage_rotation_ccwSuccessor_all w n
  refine ⟨h, ?_⟩
  intro d
  exact plDrawing_toPath_rotation_topological_ccwSuccessor
    (monotoneLayoutDrawing w n h) d













































































end DirectedDistances.PaperProofs.Section5

end
