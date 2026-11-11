/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1Window
public import Mathlib.Topology.Algebra.Order.Floor

/-! # Càdlàg paths from rescaled integer samples -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter TopologicalSpace

/-- Helper toward E-STABLE / Theorem 1.6
rescaled integer-sample path uses the ceiling-minus-one index; not the paper
result. -/
theorem floorStep_left_limit (X : ℤ → ℝ) (a b : ℝ) (hb : 0 < b) :
    ∀ t : ℝ, Tendsto (fun s : ℝ => a * X ⌊b * s⌋)
      (nhdsWithin t (Set.Iio t))
      (nhds (a * X (⌈b * t⌉ - 1))) := by
  have hmul_left (t : ℝ) :
      Tendsto (fun s : ℝ => b * s) (nhdsWithin t (Set.Iio t))
        (nhdsWithin (b * t) (Set.Iio (b * t))) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (s := Set.Iio t) (t := Set.Iio (b * t))
    · exact (continuousAt_const.mul continuousAt_id).continuousWithinAt
    · intro s hs
      exact Set.mem_Iio.mpr (mul_lt_mul_of_pos_left hs hb)
  have hfloor_left (t : ℝ) :
      Tendsto (fun s : ℝ => ⌊b * s⌋) (nhdsWithin t (Set.Iio t))
        (pure (⌈b * t⌉ - 1)) := by
    exact (tendsto_floor_left_pure_ceil_sub_one (b * t)).comp (hmul_left t)
  intro t
  exact ((tendsto_pure_pure (fun n : ℤ => a * X n) (⌈b * t⌉ - 1)).comp
    (hfloor_left t)).mono_right (pure_le_nhds _)

/-- Helper toward E-STABLE / Theorem 1.6
path is càdlàg on the real line; not the paper result. -/
theorem floorStep_isCadlag (X : ℤ → ℝ) (a b : ℝ) (hb : 0 < b) :
    IsCadlag (fun t : ℝ => a * X ⌊b * t⌋) := by
  have hmul_right (t : ℝ) :
      Tendsto (fun s : ℝ => b * s) (nhdsWithin t (Set.Ioi t))
        (nhdsWithin (b * t) (Set.Ioi (b * t))) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (s := Set.Ioi t) (t := Set.Ioi (b * t))
    · exact (continuousAt_const.mul continuousAt_id).continuousWithinAt
    · intro s hs
      exact Set.mem_Ioi.mpr (mul_lt_mul_of_pos_left hs hb)
  have hfloor_right (t : ℝ) :
      Tendsto (fun s : ℝ => ⌊b * s⌋) (nhdsWithin t (Set.Ioi t))
        (pure ⌊b * t⌋) := by
    have hfloor : Tendsto (Int.floor : ℝ → ℤ)
        (nhdsWithin (b * t) (Set.Ioi (b * t))) (pure ⌊b * t⌋) :=
      (tendsto_floor_right_pure_floor (b * t)).mono_left
        (nhdsWithin_mono (b * t) fun _ hs => le_of_lt hs)
    exact hfloor.comp (hmul_right t)
  refine ⟨?_, ?_⟩
  · intro t
    exact ((tendsto_pure_pure (fun n : ℤ => a * X n) ⌊b * t⌋).comp
      (hfloor_right t)).mono_right (pure_le_nhds _)
  · intro t
    exact ⟨a * X (⌈b * t⌉ - 1), floorStep_left_limit X a b hb t⟩

/-- Helper toward E-STABLE / Theorem 1.6
the finite window with its inherited order and topology; not the paper result. -/
theorem floorStep_isCadlag_on_window {T : ℝ} (f : ℝ → ℝ)
    (hf : IsCadlag f) : IsCadlag (fun t : J1Window T => f (t : ℝ)) := by
  have hcoe_right (x : J1Window T) :
      Tendsto (fun y : J1Window T => (y : ℝ))
        (nhdsWithin x (Set.Ioi x))
        (nhdsWithin (x : ℝ) (Set.Ioi (x : ℝ))) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (s := Set.Ioi x) (t := Set.Ioi (x : ℝ))
    · exact continuous_subtype_val.continuousWithinAt
    · intro y hy
      exact Set.mem_Ioi.mpr (Subtype.coe_lt_coe.mpr hy)
  have hcoe_left (x : J1Window T) :
      Tendsto (fun y : J1Window T => (y : ℝ))
        (nhdsWithin x (Set.Iio x))
        (nhdsWithin (x : ℝ) (Set.Iio (x : ℝ))) := by
    apply ContinuousWithinAt.tendsto_nhdsWithin
      (s := Set.Iio x) (t := Set.Iio (x : ℝ))
    · exact continuous_subtype_val.continuousWithinAt
    · intro y hy
      exact Set.mem_Iio.mpr (Subtype.coe_lt_coe.mpr hy)
  refine ⟨?_, ?_⟩
  · intro x
    exact (hf.isRightContinuous (x : ℝ)).tendsto.comp (hcoe_right x)
  · intro x
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (x : ℝ)
    exact ⟨l, hl.comp (hcoe_left x)⟩

/-- Helper toward E-STABLE / Theorem 1.6
on the finite window `[0,T]`; not the paper result. -/
noncomputable def floorStepWindow (X : ℤ → ℝ) (a b : ℝ) (hb : 0 < b)
    (T : ℝ) (_hT : 0 < T) : CadlagWindow T :=
  ⟨fun t => a * X ⌊b * (t : ℝ)⌋,
    floorStep_isCadlag_on_window _ (floorStep_isCadlag X a b hb)⟩

/-- Helper toward E-STABLE / Theorem 1.6
rescaled integer sample; not the paper result. -/
theorem floorStepWindow_apply (X : ℤ → ℝ) (a b : ℝ) (hb : 0 < b)
    (T : ℝ) (hT : 0 < T) (t : J1Window T) :
    (floorStepWindow X a b hb T hT).1 t = a * X ⌊b * (t : ℝ)⌋ := rfl

end DirectedDistances.Probability
