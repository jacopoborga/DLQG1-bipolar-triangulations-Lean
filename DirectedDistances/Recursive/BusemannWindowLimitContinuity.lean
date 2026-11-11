module

public import DirectedDistances.Recursive.BusemannWindowLimit
public import DirectedDistances.Recursive.BusemannWindowLimitSDP
public import DirectedDistances.Probability.SkorokhodJ1WindowContinuityTimes

import DirectedDistances.Probability.SkorokhodJ1WindowCylinder
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open Set
open DirectedDistances.RandomWalk
open DirectedDistances.Probability
open scoped Topology ENNReal

/-! Continuity and consistency obligations for finite-window Busemann limits.

The available window theorems identify stable finite-dimensional laws only on a
co-countable set of times. Fixed-time continuity and restriction consistency
remain separate from functional convergence and require explicit proofs. -/

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
co-countable set of times at which almost every path is continuous. -/
theorem ldp_busemann_window_limit_continuityTimes_countable
    (hind : iIndepFun
      (fun j ω => ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => ldpBusemannWindowLaw n hT) atTop (𝓝 ν) ∧
        (continuityTimes (ν : Measure (J1WindowD T hT)))ᶜ.Countable := by
  obtain ⟨ν, hν, _⟩ := ldp_busemann_window_tendsto hind hsym hT
  exact ⟨ν, hν, countable_compl_continuityTimes
    (ν : Measure (J1WindowD T hT))⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
co-countable set of times at which almost every path is continuous. -/
theorem sdp_busemann_window_limit_continuityTimes_countable
    (hind : iIndepFun
      (fun j ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion j ω)
      iidCodeMeasure)
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) :
    ∃ ν : ProbabilityMeasure (J1WindowD T hT),
      Tendsto (fun n => sdpBusemannWindowLaw n hT) atTop (𝓝 ν) ∧
        (continuityTimes (ν : Measure (J1WindowD T hT)))ᶜ.Countable := by
  obtain ⟨ν, hν, _⟩ := sdp_busemann_window_tendsto hind hsym hT
  exact ⟨ν, hν, countable_compl_continuityTimes
    (ν : Measure (J1WindowD T hT))⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
into a larger time window. -/
@[expose] def restrictWindowTime {S T : ℝ} (hST : S < T)
    (t : J1Window S) :
    J1Window T :=
  ⟨t, t.property.1, t.property.2.trans hST.le⟩

private theorem restrictWindowTime_isometry {S T : ℝ} (hST : S < T) :
    Isometry (restrictWindowTime hST) := by
  apply Isometry.of_dist_eq
  intro x y
  simp [restrictWindowTime, Subtype.dist_eq]

private theorem restrictWindowTime_tendsto_left {S T : ℝ} (hST : S < T)
    (t : J1Window S) :
    Tendsto (restrictWindowTime hST) (𝓝[<] t)
      (𝓝[<] (restrictWindowTime hST t)) := by
  have hemb := (restrictWindowTime_isometry hST).isEmbedding
  have himage :
      restrictWindowTime hST '' (Iio t : Set (J1Window S)) =
        Iio (restrictWindowTime hST t) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (x : ℝ) < (t : ℝ) at hx
      exact hx
    · intro hy
      refine ⟨⟨y, ?_, ?_⟩, ?_, ?_⟩
      · exact y.property.1
      · exact hy.le.trans t.property.2
      · exact hy
      · exact Subtype.ext rfl
  change Tendsto (restrictWindowTime hST) (𝓝[Iio t] t)
    (𝓝[Iio (restrictWindowTime hST t)] (restrictWindowTime hST t))
  rw [← himage, ← hemb.map_nhdsWithin_eq (Iio t) t]
  exact le_rfl

private theorem restrictWindowTime_tendsto_right {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (t : J1Window S) (ht : (t : ℝ) < S) :
    Tendsto (restrictWindowTime hST) (𝓝[Ioi t] t)
      (𝓝[Ioi (restrictWindowTime hST t)] (restrictWindowTime hST t)) := by
  have hemb := (restrictWindowTime_isometry hST).isEmbedding
  let eS : J1Window S := ⟨S, hS.le, le_rfl⟩
  have himage :
      restrictWindowTime hST '' (Ioi t : Set (J1Window S)) =
        Ioi (restrictWindowTime hST t) ∩ Iic (restrictWindowTime hST eS) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by exact hx, x.property.2⟩
    · rintro ⟨hy, hye⟩
      refine ⟨⟨y, ?_, ?_⟩, ?_, ?_⟩
      · exact y.property.1
      · exact hye
      · exact hy
      · exact Subtype.ext rfl
  have hSlt : restrictWindowTime hST t < restrictWindowTime hST eS := by
    change (t : ℝ) < S
    exact ht
  have hmem : Iic (restrictWindowTime hST eS) ∈
      𝓝 (restrictWindowTime hST t) := Iic_mem_nhds hSlt
  have hfilter : 𝓝[Ioi (restrictWindowTime hST t) ∩
      Iic (restrictWindowTime hST eS)] (restrictWindowTime hST t) =
        𝓝[Ioi (restrictWindowTime hST t)] (restrictWindowTime hST t) :=
    nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hmem)
  change Tendsto (restrictWindowTime hST) (𝓝[Ioi t] t)
    (𝓝[Ioi (restrictWindowTime hST t)] (restrictWindowTime hST t))
  rw [← hfilter, ← himage, ← hemb.map_nhdsWithin_eq (Ioi t) t]
  exact le_rfl

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
shorter closed window preserves càdlàgness. -/
theorem isCadlag_restrictWindowTime {S T : ℝ} (hS : 0 < S) (hST : S < T)
    (f : CadlagWindow T) :
    IsCadlag (fun t : J1Window S => f.1 (restrictWindowTime hST t)) := by
  constructor
  · intro t
    by_cases ht : (t : ℝ) = S
    · have htop : t = (⟨S, hS.le, le_rfl⟩ : J1Window S) := Subtype.ext ht
      subst t
      have hempty : Ioi (⟨S, hS.le, le_rfl⟩ : J1Window S) = ∅ := by
        ext x
        simp only [mem_Ioi, mem_empty_iff_false, iff_false, not_lt]
        exact x.property.2
      change Tendsto
        (fun u : J1Window S => f.1 (restrictWindowTime hST u))
        (𝓝[Ioi (⟨S, hS.le, le_rfl⟩ : J1Window S)]
          (⟨S, hS.le, le_rfl⟩ : J1Window S))
        (𝓝 (f.1 (restrictWindowTime hST ⟨S, hS.le, le_rfl⟩)))
      rw [hempty, nhdsWithin_empty]
      exact tendsto_bot
    · have htS : (t : ℝ) < S := lt_of_le_of_ne t.property.2 ht
      have hmap := restrictWindowTime_tendsto_right hS hST t htS
      exact (f.2.isRightContinuous (restrictWindowTime hST t)).tendsto.comp hmap
  · intro t
    by_cases ht : (t : ℝ) = 0
    · have hbot : Iio (⟨0, le_rfl, hS.le⟩ : J1Window S) = ∅ := by
        ext x
        simp only [mem_Iio, mem_empty_iff_false, iff_false, not_lt]
        exact x.property.1
      refine ⟨f.1 (restrictWindowTime hST t), ?_⟩
      rw [show t = (⟨0, le_rfl, hS.le⟩ : J1Window S) by exact Subtype.ext ht]
      change Tendsto
        (fun u : J1Window S => f.1 (restrictWindowTime hST u))
        (𝓝[Iio (⟨0, le_rfl, hS.le⟩ : J1Window S)]
          (⟨0, le_rfl, hS.le⟩ : J1Window S))
        (𝓝 (f.1 (restrictWindowTime hST ⟨0, le_rfl, hS.le⟩)))
      rw [hbot, nhdsWithin_empty]
      exact tendsto_bot
    · obtain ⟨l, hl⟩ := f.2.tendsto_nhdsLT (restrictWindowTime hST t)
      exact ⟨l, hl.comp (restrictWindowTime_tendsto_left hST t)⟩

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
path from `[0,T]` to its shorter subwindow `[0,S]`. -/
@[expose] def restrictJ1Window {S T : ℝ} (hS : 0 < S) (hST : S < T) :
    J1WindowD T (lt_trans hS hST) → J1WindowD S hS :=
  fun x => ⟨⟨fun t => x.path.1 (restrictWindowTime hST t),
    isCadlag_restrictWindowTime hS hST x.path⟩⟩

private instance j1WindowPreconnectedSpace (S : ℝ) :
    PreconnectedSpace (J1Window S) :=
  Subtype.preconnectedSpace isPreconnected_Icc

private instance j1TimeChangeNonempty (T : ℝ) :
    Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩

private noncomputable def repairedWindowMap {S T : ℝ} (_hS : 0 < S) (hST : S < T)
    (φ : J1TimeChange T) (η : ℝ) (hη : 0 < η) (hηS : η < S)
    (δ : ℝ) (_hδη : δ < η)
    (_hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    J1Window S → ℝ := by
  let a : J1Window S := ⟨S - η, ⟨by linarith, by linarith⟩⟩
  let b : ℝ := (φ (restrictWindowTime hST a) : ℝ)
  let left : J1Window S → ℝ := fun t => φ (restrictWindowTime hST t)
  let line : J1Window S → ℝ := fun t =>
    b + ((t : ℝ) - (S - η)) * ((S - b) / η)
  exact (Set.Iic a).piecewise left line

private theorem repairedWindowMap_endpoint_bounds {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (φ : J1TimeChange T) (η : ℝ) (hη : 0 < η)
    (hηS : η < S) (δ : ℝ) (hδη : δ < η)
    (hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    ∀ t : J1Window S,
      repairedWindowMap hS hST φ η hη hηS δ hδη hδ t ∈ Set.Icc 0 S := by
  let a : J1Window S := ⟨S - η, ⟨by linarith, by linarith⟩⟩
  let b : ℝ := (φ (restrictWindowTime hST a) : ℝ)
  let anchor := restrictWindowTime hST a
  have hab : |b - (S - η)| ≤ δ := by
    dsimp [b, anchor]
    simpa [restrictWindowTime] using hδ (restrictWindowTime hST a)
  have hbS : b < S := by
    have h := (abs_le.mp hab).2
    linarith
  have hb0 : 0 ≤ b := (φ anchor).property.1
  intro t
  by_cases ht : t ≤ a
  · constructor
    · simpa [repairedWindowMap, a, Set.piecewise, ht] using
        (φ (restrictWindowTime hST t)).property.1
    · have hta : restrictWindowTime hST t ≤ restrictWindowTime hST a := by
        change (t : ℝ) ≤ S - η
        exact ht
      have hmono := φ.monotone hta
      have hreal : (φ (restrictWindowTime hST t) : ℝ) ≤ b := by
        exact_mod_cast hmono
      exact (by simpa [repairedWindowMap, a, Set.piecewise, ht] using
        hreal.trans hbS.le)
  · have hta : S - η < (t : ℝ) := by
      have : ¬ (t : ℝ) ≤ S - η := by
        exact ht
      exact lt_of_not_ge this
    have htS : (t : ℝ) ≤ S := t.property.2
    let c : ℝ := (S - b) / η
    have hc : 0 < c := div_pos (by linarith) hη
    have hta0 : 0 ≤ (t : ℝ) - (S - η) := by linarith
    have htaη : (t : ℝ) - (S - η) ≤ η := by linarith
    have hmul : η * c = S - b := by
      dsimp [c]
      exact mul_div_cancel₀ _ hη.ne'
    constructor
    · have hline0 : 0 ≤ b + ((t : ℝ) - (S - η)) * c :=
        add_nonneg hb0 (mul_nonneg hta0 hc.le)
      simpa [repairedWindowMap, a, b, c, Set.piecewise, ht] using hline0
    · have hupper : b + ((t : ℝ) - (S - η)) * c ≤ S := by
        calc
          b + ((t : ℝ) - (S - η)) * c ≤ b + η * c := by
            nlinarith [mul_le_mul_of_nonneg_right htaη hc.le]
          _ = S := by rw [hmul]; ring
      simpa [repairedWindowMap, a, b, c, Set.piecewise, ht] using hupper

private theorem repairedWindowMap_continuous {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (φ : J1TimeChange T) (η : ℝ) (hη : 0 < η)
    (hηS : η < S) (δ : ℝ) (hδη : δ < η)
    (hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    Continuous (repairedWindowMap hS hST φ η hη hηS δ hδη hδ) := by
  classical
  let a : J1Window S := ⟨S - η, ⟨by linarith, by linarith⟩⟩
  let b : ℝ := (φ (restrictWindowTime hST a) : ℝ)
  let left : J1Window S → ℝ := fun t => φ (restrictWindowTime hST t)
  let line : J1Window S → ℝ := fun t =>
    b + ((t : ℝ) - (S - η)) * ((S - b) / η)
  have hleft : Continuous left :=
    continuous_subtype_val.comp <|
      (j1TimeChange_continuous φ).comp
        ((restrictWindowTime_isometry hST).continuous)
  have hline : Continuous line := by
    dsimp [line]
    exact continuous_const.add
      ((continuous_subtype_val.sub continuous_const).mul continuous_const)
  have hfront : ∀ t ∈ frontier (Set.Iic a), left t = line t := by
    intro t ht
    have hta : t = a := by
      have hs : t ∈ ({a} : Set (J1Window S)) := frontier_Iic_subset a ht
      exact mem_singleton_iff.mp hs
    subst t
    change (φ (restrictWindowTime hST a) : ℝ) =
      b + ((a : ℝ) - (S - η)) * ((S - b) / η)
    rw [show (a : ℝ) = S - η by rfl]
    simp [b]
  have hraw : Continuous ((Set.Iic a).piecewise left line) :=
    continuous_piecewise hfront hleft.continuousOn hline.continuousOn
  simpa [repairedWindowMap, a, left, line, b] using hraw

private theorem repairedWindowMap_strictMono {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (φ : J1TimeChange T) (η : ℝ) (hη : 0 < η)
    (hηS : η < S) (δ : ℝ) (hδη : δ < η)
    (hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    StrictMono (fun t : J1Window S =>
      (⟨repairedWindowMap hS hST φ η hη hηS δ hδη hδ t,
        repairedWindowMap_endpoint_bounds hS hST φ η hη hηS δ hδη hδ t⟩ :
        J1Window S)) := by
  let a : J1Window S := ⟨S - η, ⟨by linarith, by linarith⟩⟩
  let b : ℝ := (φ (restrictWindowTime hST a) : ℝ)
  let left : J1Window S → ℝ := fun t => φ (restrictWindowTime hST t)
  let line : J1Window S → ℝ := fun t =>
    b + ((t : ℝ) - (S - η)) * ((S - b) / η)
  have hab : |b - (S - η)| ≤ δ := by
    dsimp [b]
    simpa [restrictWindowTime] using hδ (restrictWindowTime hST a)
  have hbS : b < S := by
    have h := (abs_le.mp hab).2
    linarith
  have hc : 0 < (S - b) / η := div_pos (by linarith) hη
  intro x y hxy
  have hxy' : (x : ℝ) < y := hxy
  change repairedWindowMap hS hST φ η hη hηS δ hδη hδ x <
    repairedWindowMap hS hST φ η hη hηS δ hδη hδ y
  by_cases hx : x ≤ a
  · by_cases hy : y ≤ a
    · simpa [repairedWindowMap, a, b, left, line, Set.piecewise, hx, hy] using
        (φ.strictMono (show restrictWindowTime hST x < restrictWindowTime hST y by
          change (x : ℝ) < y
          exact hxy'))
    · have hleft : left x ≤ b := by
        have hmono : φ (restrictWindowTime hST x) ≤
            φ (restrictWindowTime hST a) := φ.monotone (by
              change (x : ℝ) ≤ S - η
              exact hx)
        exact_mod_cast hmono
      have hy' : S - η < (y : ℝ) := by
        have : ¬ (y : ℝ) ≤ S - η := by
          intro h
          apply hy
          exact_mod_cast h
        exact lt_of_not_ge this
      have hright : b < line y := by
        dsimp [line]
        have hpos : 0 < ((y : ℝ) - (S - η)) * ((S - b) / η) :=
          mul_pos (by linarith) hc
        linarith
      simp [repairedWindowMap, a, hx, hy]
      exact lt_of_le_of_lt hleft hright
  · have hy : ¬ y ≤ a := by
      intro hy
      apply hx
      change (x : ℝ) ≤ S - η
      exact hxy'.le.trans (by change (y : ℝ) ≤ S - η; exact hy)
    have hxySub : (x : ℝ) - (S - η) < (y : ℝ) - (S - η) := by
      linarith
    have hmul :
        ((x : ℝ) - (S - η)) * ((S - b) / η) <
          ((y : ℝ) - (S - η)) * ((S - b) / η) :=
      mul_lt_mul_of_pos_right hxySub hc
    simpa [repairedWindowMap, a, b, left, line, Set.piecewise, hx, hy] using
      add_lt_add_left hmul b

private theorem repairedWindowMap_range_zero {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (φ : J1TimeChange T) (η : ℝ) (hη : 0 < η)
    (hηS : η < S) (δ : ℝ) (hδη : δ < η)
    (hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    repairedWindowMap hS hST φ η hη hηS δ hδη hδ
      (⟨0, le_rfl, hS.le⟩ : J1Window S) = 0 := by
  let zero : J1Window S := ⟨0, le_rfl, hS.le⟩
  let a : J1Window S := ⟨S - η, ⟨by linarith, by linarith⟩⟩
  have hzeroa : zero ≤ a := by
    change (0 : ℝ) ≤ S - η
    linarith
  have hzemb : restrictWindowTime hST zero =
      (⟨0, le_rfl, (lt_trans hS hST).le⟩ : J1Window T) := by
    apply Subtype.ext
    rfl
  let zeroT : J1Window T := ⟨0, le_rfl, (lt_trans hS hST).le⟩
  have hφzero : φ zeroT = zeroT := by
    apply Subtype.ext
    have hlow : (0 : ℝ) ≤ (φ zeroT : ℝ) := (φ zeroT).property.1
    have hhigh : (φ zeroT : ℝ) ≤ 0 := by
      obtain ⟨x, hx⟩ := φ.surjective zeroT
      have hzeroX : zeroT ≤ x := by
        change (0 : ℝ) ≤ x
        exact x.property.1
      have hmono := φ.monotone hzeroX
      rw [hx] at hmono
      exact_mod_cast hmono
    linarith
  have hzeroMap : repairedWindowMap hS hST φ η hη hηS δ hδη hδ zero = 0 := by
    change (Set.Iic a).piecewise
      (fun t : J1Window S => (φ (restrictWindowTime hST t) : ℝ))
      (fun t => (φ (restrictWindowTime hST a) : ℝ) +
        ((t : ℝ) - (S - η)) *
          ((S - (φ (restrictWindowTime hST a) : ℝ)) / η)) zero = 0
    rw [Set.piecewise_eq_of_mem (Set.Iic a) _ _ hzeroa]
    rw [hzemb]
    have hcoe : (φ zeroT : ℝ) = (zeroT : ℝ) := congrArg Subtype.val hφzero
    simpa [zeroT] using hcoe
  simpa [zero] using hzeroMap

private theorem repairedWindowMap_range_top {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (φ : J1TimeChange T) (η : ℝ) (hη : 0 < η)
    (hηS : η < S) (δ : ℝ) (hδη : δ < η)
    (hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    repairedWindowMap hS hST φ η hη hηS δ hδη hδ
      (⟨S, hS.le, le_rfl⟩ : J1Window S) = S := by
  let top : J1Window S := ⟨S, hS.le, le_rfl⟩
  let a : J1Window S := ⟨S - η, ⟨by linarith, by linarith⟩⟩
  let b : ℝ := (φ (restrictWindowTime hST a) : ℝ)
  have htopnot : ¬ top ≤ a := by
    intro h
    have h' : S ≤ S - η := by exact_mod_cast h
    linarith
  have hmul : η * ((S - b) / η) = S - b := mul_div_cancel₀ _ hη.ne'
  have hraw : repairedWindowMap hS hST φ η hη hηS δ hδη hδ top =
      b + ((top : ℝ) - (S - η)) * ((S - b) / η) := by
    simp [repairedWindowMap, top, a, b, htopnot]
  rw [hraw, show (top : ℝ) - (S - η) = η by ring, hmul]
  ring

private theorem repairedWindowMap_range {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (φ : J1TimeChange T) (η : ℝ) (hη : 0 < η)
    (hηS : η < S) (δ : ℝ) (hδη : δ < η)
    (hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    Function.Surjective (fun t : J1Window S =>
      (⟨repairedWindowMap hS hST φ η hη hηS δ hδη hδ t,
        repairedWindowMap_endpoint_bounds hS hST φ η hη hηS δ hδη hδ t⟩ :
        J1Window S)) := by
  let zero : J1Window S := ⟨0, le_rfl, hS.le⟩
  let top : J1Window S := ⟨S, hS.le, le_rfl⟩
  have hzero := repairedWindowMap_range_zero hS hST φ η hη hηS δ hδη hδ
  have htop := repairedWindowMap_range_top hS hST φ η hη hηS δ hδη hδ
  let raw : J1Window S → ℝ := repairedWindowMap hS hST φ η hη hηS δ hδη hδ
  have hiv := intermediate_value_univ zero top
    (repairedWindowMap_continuous hS hST φ η hη hηS δ hδη hδ)
  intro y
  have hy : (y : ℝ) ∈ Set.Icc (raw zero) (raw top) := by
    rw [show raw zero = 0 by exact hzero, show raw top = S by exact htop]
    exact y.property
  obtain ⟨x, hx⟩ := hiv hy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
on a shorter window by keeping it up to `S - η` and then interpolating linearly
to `(S, S)`, without increasing the time-change displacement. -/
theorem exists_repairedJ1WindowTimeChange
    {S T : ℝ} (hS : 0 < S) (hST : S < T) (φ : J1TimeChange T)
    (η δ : ℝ) (hη : 0 < η) (hηS : η < S) (hδη : δ < η)
    (hδ : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ δ) :
    ∃ μ : J1TimeChange S,
      StrictMono μ ∧ Continuous μ ∧
      μ ⟨0, le_rfl, hS.le⟩ = ⟨0, le_rfl, hS.le⟩ ∧
      μ ⟨S, hS.le, le_rfl⟩ = ⟨S, hS.le, le_rfl⟩ ∧
      (∀ t : J1Window S, (t : ℝ) ≤ S - η →
        (μ t : ℝ) = (φ (restrictWindowTime hST t) : ℝ)) ∧
      (∀ t : J1Window S, S - η ≤ (t : ℝ) →
        (μ t : ℝ) =
          (φ (restrictWindowTime hST
            ⟨S - η, ⟨by linarith, by linarith⟩⟩) : ℝ) +
          ((t : ℝ) - (S - η)) *
            ((S - (φ (restrictWindowTime hST
              ⟨S - η, ⟨by linarith, by linarith⟩⟩) : ℝ)) / η)) ∧
      (∀ t : J1Window S, |(μ t : ℝ) - t| ≤ δ) ∧
      (⨆ t : J1Window S, |(μ t : ℝ) - t|) ≤ δ := by
  classical
  let raw := repairedWindowMap hS hST φ η hη hηS δ hδη hδ
  let μ : J1TimeChange S := StrictMono.orderIsoOfSurjective _
    (repairedWindowMap_strictMono hS hST φ η hη hηS δ hδη hδ)
    (repairedWindowMap_range hS hST φ η hη hηS δ hδη hδ)
  have key : ∀ t, (μ t : ℝ) = raw t := fun t => rfl
  let a : J1Window S := ⟨S - η, ⟨by linarith, by linarith⟩⟩
  let b : ℝ := (φ (restrictWindowTime hST a) : ℝ)
  have hab : |b - (S - η)| ≤ δ := by
    dsimp [b]
    simpa [restrictWindowTime] using hδ (restrictWindowTime hST a)
  have hleft : ∀ t : J1Window S, (t : ℝ) ≤ S - η →
      raw t = (φ (restrictWindowTime hST t) : ℝ) := by
    intro t ht
    have h : t ≤ a := ht
    simp [raw, repairedWindowMap, a, h]
  have hright : ∀ t : J1Window S, S - η < (t : ℝ) →
      raw t = b + ((t : ℝ) - (S - η)) * ((S - b) / η) := by
    intro t ht
    have h : ¬ t ≤ a := by
      intro h'
      have : (t : ℝ) ≤ S - η := h'
      linarith
    simp [raw, repairedWindowMap, a, b, h]
  have hline : ∀ t : J1Window S, S - η ≤ (t : ℝ) →
      raw t = b + ((t : ℝ) - (S - η)) * ((S - b) / η) := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · exact hright t h
    · have hta : t = a := Subtype.ext h.symm
      rw [hleft t h.symm.le, ← h]
      subst hta
      simp [b]
  have hbound : ∀ t : J1Window S, |(μ t : ℝ) - t| ≤ δ := by
    intro t
    rw [key]
    by_cases ht : (t : ℝ) ≤ S - η
    · rw [hleft t ht]
      simpa [restrictWindowTime] using hδ (restrictWindowTime hST t)
    · have ht' : S - η < (t : ℝ) := lt_of_not_ge ht
      rw [hright t ht']
      have htS : (t : ℝ) ≤ S := t.property.2
      have hw0 : 0 ≤ (η - ((t : ℝ) - (S - η))) / η :=
        div_nonneg (by linarith) hη.le
      have hw1 : (η - ((t : ℝ) - (S - η))) / η ≤ 1 := by
        rw [div_le_one hη]; linarith
      have hE : b + ((t : ℝ) - (S - η)) * ((S - b) / η) - t =
          (b - (S - η)) * ((η - ((t : ℝ) - (S - η))) / η) := by
        field_simp
        ring
      rw [hE, abs_mul, abs_of_nonneg hw0]
      calc |b - (S - η)| * ((η - ((t : ℝ) - (S - η))) / η)
          ≤ |b - (S - η)| := mul_le_of_le_one_right (abs_nonneg _) hw1
        _ ≤ δ := hab
  have : Nonempty (J1Window S) := ⟨⟨0, le_rfl, hS.le⟩⟩
  refine ⟨μ, μ.strictMono, j1TimeChange_continuous μ, ?_, ?_, ?_, ?_,
    hbound, ciSup_le hbound⟩
  · apply Subtype.ext
    exact repairedWindowMap_range_zero hS hST φ η hη hηS δ hδη hδ
  · apply Subtype.ext
    exact repairedWindowMap_range_top hS hST φ η hη hηS δ hδη hδ
  · intro t ht
    rw [key, hleft t ht]
  · intro t ht
    rw [key, hline t ht]

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
is continuous at every path that is continuous at the right endpoint `S`
(Billingsley, 2nd ed., proof of Thm 16.2). -/
theorem continuousAt_restrictJ1Window_of_path_continuousAt {S T : ℝ}
    (hS : 0 < S) (hST : S < T) (x : J1WindowD T (lt_trans hS hST))
    (hx : ContinuousAt x.path.1 (⟨S, hS.le, hST.le⟩ : J1Window T)) :
    ContinuousAt (restrictJ1Window hS hST) x := by
  classical
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hxρ⟩ := Metric.continuousAt_iff.mp hx (ε / 4) (by linarith)
  have hηpos : 0 < min (ρ / 4) (S / 2) := lt_min (by linarith) (by linarith)
  have hηS : min (ρ / 4) (S / 2) < S := by
    have := min_le_right (ρ / 4) (S / 2); linarith
  have hηρ : min (ρ / 4) (S / 2) ≤ ρ / 4 := min_le_left _ _
  set η := min (ρ / 4) (S / 2) with hη
  have hδpos : 0 < min (η / 2) (ε / 4) := lt_min (by linarith) (by linarith)
  have hδη : min (η / 2) (ε / 4) < η := by
    have := min_le_left (η / 2) (ε / 4); linarith
  have hδε : min (η / 2) (ε / 4) ≤ ε / 4 := min_le_right _ _
  set δ := min (η / 2) (ε / 4) with hδdef
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  have hy' : (⨅ φ : J1TimeChange T,
      max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
        (⨆ t : J1Window T, |y.path.1 (φ t) - x.path.1 t|)) < δ := hy
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt hy'
  have h1 := (max_lt_iff.mp hφ).1
  have h2 := (max_lt_iff.mp hφ).2
  have hδφ : ∀ s : J1Window T, |(φ s : ℝ) - s| ≤ δ := fun s =>
    (le_ciSup (j1WindowTimeChangeDistortion_bddAbove φ) s).trans h1.le
  have hval : ∀ s : J1Window T, |y.path.1 (φ s) - x.path.1 s| ≤ δ := fun s =>
    (le_ciSup (j1WindowValueError_bddAbove y.path x.path φ) s).trans h2.le
  obtain ⟨μ, -, -, -, -, hμl, -, hμb, hμs⟩ :=
    exists_repairedJ1WindowTimeChange hS hST φ η δ hηpos hηS hδη hδφ
  have hne : Nonempty (J1Window S) := ⟨⟨0, le_rfl, hS.le⟩⟩
  have key : ∀ t : J1Window S,
      |y.path.1 (restrictWindowTime hST (μ t)) -
        x.path.1 (restrictWindowTime hST t)| ≤ 3 * ε / 4 := by
    intro t
    by_cases ht : (t : ℝ) ≤ S - η
    · have : restrictWindowTime hST (μ t) = φ (restrictWindowTime hST t) :=
        Subtype.ext (hμl t ht)
      rw [this]
      have := hval (restrictWindowTime hST t)
      linarith
    · have ht' : S - η < (t : ℝ) := lt_of_not_ge ht
      have htS : (t : ℝ) ≤ S := t.property.2
      let s : J1Window T := restrictWindowTime hST (μ t)
      let u : J1Window T := φ.symm s
      have hφu : ((φ u : J1Window T) : ℝ) = (μ t : ℝ) :=
        congrArg Subtype.val (φ.apply_symm_apply s)
      have hφu' : φ u = s := φ.apply_symm_apply s
      have h3 := abs_le.mp (hμb t)
      have h4 := abs_le.mp (hδφ u)
      have hu : dist u (⟨S, hS.le, hST.le⟩ : J1Window T) < ρ := by
        rw [Subtype.dist_eq, Real.dist_eq]
        change |(u : ℝ) - S| < ρ
        rw [abs_lt]
        constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
      have ht2 : dist (restrictWindowTime hST t)
          (⟨S, hS.le, hST.le⟩ : J1Window T) < ρ := by
        rw [Subtype.dist_eq, Real.dist_eq]
        change |(t : ℝ) - S| < ρ
        rw [abs_lt]
        constructor <;> linarith
      have e1 := hxρ hu
      have e2 := hxρ ht2
      rw [Real.dist_eq] at e1 e2
      have e3 := hval u
      rw [hφu'] at e3
      have e4 := abs_le.mp e3
      have e1' := abs_lt.mp e1
      have e2' := abs_lt.mp e2
      rw [abs_le]
      constructor <;> linarith [e4.1, e4.2, e1'.1, e1'.2, e2'.1, e2'.2]
  have hbdd : BddBelow (Set.range fun ψ : J1TimeChange S =>
      max (⨆ t : J1Window S, |((ψ t : ℝ) - (t : ℝ))|)
        (⨆ t : J1Window S, |(restrictJ1Window hS hST y).path.1 (ψ t) -
          (restrictJ1Window hS hST x).path.1 t|)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
  change (⨅ ψ : J1TimeChange S,
      max (⨆ t : J1Window S, |((ψ t : ℝ) - (t : ℝ))|)
        (⨆ t : J1Window S, |(restrictJ1Window hS hST y).path.1 (ψ t) -
          (restrictJ1Window hS hST x).path.1 t|)) < ε
  refine lt_of_le_of_lt (ciInf_le hbdd μ) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt hμs (by linarith)
  · exact lt_of_le_of_lt (ciSup_le fun t => key t) (by linarith)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
restriction to a shorter window. -/
@[simp] theorem restrictJ1Window_apply {S T : ℝ} (hS : 0 < S)
    (hST : S < T) (x : J1WindowD T (lt_trans hS hST))
    (t : J1Window S) :
    (restrictJ1Window hS hST x).path.1 t =
      x.path.1 (restrictWindowTime hST t) := rfl

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
is Borel measurable, as its time evaluations are measurable. -/
theorem measurable_restrictJ1Window {S T : ℝ} (hS : 0 < S) (hST : S < T) :
    Measurable (restrictJ1Window hS hST) := by
  classical
  let eS : J1Window S := ⟨S, hS.le, le_rfl⟩
  obtain ⟨D, hDcount, hD⟩ :=
    TopologicalSpace.exists_countable_dense (J1Window S)
  let D' : Set (J1Window S) := insert eS D
  have hD'dense : Dense D' := hD.mono (Set.subset_insert _ _)
  have hD'count : D'.Countable := hDcount.insert _
  have heval : Measurable
      (fun x : J1WindowD T (lt_trans hS hST) =>
        fun t : D' => (restrictJ1Window hS hST x).path.1 t.val) := by
    apply measurable_pi_iff.mpr
    intro t
    change Measurable (fun x : J1WindowD T (lt_trans hS hST) =>
      x.path.1 (restrictWindowTime hST t.val))
    exact measurable_j1WindowD_eval (lt_trans hS hST)
      (restrictWindowTime hST t.val)
  apply Measurable.of_comap_le
  change (borel (J1WindowD S hS)).comap (restrictJ1Window hS hST) ≤
      borel (J1WindowD T (lt_trans hS hST))
  rw [borel_eq_comap_pi_eval hS D' hD'dense hD'count
    (Set.mem_insert _ _), MeasurableSpace.comap_comp]
  exact heval.comap_le

end DirectedDistances.Recursive
