module

public import DirectedDistances.PaperProofs.Section7.CellLDPUpperGoodEvent
public import DirectedDistances.KMSW.StageSubgraph
import DirectedDistances.PaperProofs.Section7.CellLDPUpperPathwise

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.Recursive





theorem cell_ldp_upper_conditional
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hstatL : ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0))
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω | ∀ x y : StagePresentVertex (fun i => ω (i + 1)) n,
            x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            ldpSup x y ≤ ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)} := by
  classical
  intro ε hε hεlt
  obtain ⟨C, hC, hgood⟩ := cell_ldp_upper_good_event hind hstatL hsym ε hε hεlt
  refine ⟨C, hC, fun n hn A hA => (hgood n hn A hA).trans ?_⟩
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono_ae
  filter_upwards [iidCodes_ae_boundaryBusemannLDPMeasurableVersion,
    iidCodes_ae_boundaryBusemannLDPMeasurableVersion_shift n] with ω hbase hshift
  intro hG x y hx hy
  obtain ⟨hfin0, h0, hX⟩ := hbase
  rw [shiftedTail_eq_baseTail n ω] at hshift
  obtain ⟨hfinn, hn', hXn⟩ := hshift
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let T : ℝ := A ^ (ε / 2) * Real.sqrt (n : ℝ)
  let k : ℕ := ⌈T⌉₊ + 1
  let B : ℝ := A * (n : ℝ) ^ (3 / 4 : ℝ) / 4
  obtain ⟨⟨hUL, hUR, hLL, hLR⟩, hvalues⟩ := hG
  have hceil : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
  have hULN : (kmswStage w n).UL.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hUL.trans hceil
  have hURN : (kmswStage w n).UR.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hUR.trans hceil
  have hLLN : (kmswStage w n).LL.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hLL.trans hceil
  have hLRN : (kmswStage w n).LR.length ≤ ⌈T⌉₊ := by
    exact_mod_cast hLR.trans hceil
  have hB0 : ∀ i : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ i →
      i ≤ ((kmswStage w n).LR.length : ℤ) →
      |(busemannLDPMeasurableVersion ω i : ℝ)| ≤ B := by
    intro i hiL hiR
    apply (hvalues i ?_).1
    change |i| ≤ (k : ℤ)
    apply abs_le.mpr
    dsimp only [k]
    constructor <;> omega
  have hBn : ∀ i : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ i →
      i ≤ (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) →
      |(busemannLDPMeasurableVersion (codeShift n ω) i : ℝ)| ≤ B := by
    intro i hiL hiR
    apply (hvalues i ?_).2
    change |i| ≤ (k : ℤ)
    apply abs_le.mpr
    dsimp only [k]
    constructor <;> omega
  unfold ldpSup
  apply csSup_le'
  rintro _ ⟨m, ⟨p, rfl⟩, rfl⟩
  apply WithBot.coe_le_coe.mpr
  apply Nat.le_floor
  change (p.length : ℝ) ≤ A * (n : ℝ) ^ (3 / 4 : ℝ)
  have hp := cell_path_length_le_of_real_busemann_bounds w n h0 hn'
    (presentPathLengthsBounded_of_hfin w hfin0)
    (presentPathLengthsBounded_of_hfin (fun i => w (n + i)) hfinn)
    hX hXn B B hB0 hBn x y hx hy p
  dsimp only [B] at hp
  linarith only [hp]

end DirectedDistances.PaperProofs.Section7
