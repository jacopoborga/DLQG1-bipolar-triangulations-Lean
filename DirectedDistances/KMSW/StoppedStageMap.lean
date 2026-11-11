/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoltzmannMarks
public import DirectedDistances.KMSW.StageEdgesConnected
import DirectedDistances.PaperProofs.Section3.KMSWBdyGeometric
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Source-class data at the stopped KMSW stage

For `w := boltzmannKMSWStream ω` and `t := boltzmannTau r ω`, this file
collects the boundary, missing-edge, and edge-count properties of stage
`t - 1` on `boltzmannEvent r`. It uses the implemented step set
`{(-1, 0), (0, 1), (1, -1)}` (code `1` has increment `(0, 1)`). The legal-step convention
for Lemmas 3.11–3.12, not a proof of the map law or the paper's bijection.
Sources: `lem-kmsw-boltzmann` and `lem-boltzmann-finite`, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section3

/-- At each finite KMSW stage, the missing allocated edge IDs are exactly the -/
theorem kmswStage_missing_edges_exactly_UR_append_LL (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e < (kmswStage w n).nextEdge,
      ((kmswStage w n).present e = false ↔
        e ∈ (kmswStage w n).UR ++ (kmswStage w n).LL) := by
  intro e he
  rw [List.mem_append]
  exact (kmswStage_status w n).1 e he

/-- The stopped stage has no missing boundary runs or missing edges, its
geometric left and right boundary lengths are `L w t` and `r`, and its total
geometric edge count is `t`. The lengths are stated in their source carriers:
the left coordinate is an integer, while the right length is natural. This
records the numerical and boundary conditions needed for the source class of
establish the full map-law or bijection claims of Lemmas 3.11–3.12.
Sources: `lem-kmsw-bdy`, `lem-kmsw-boltzmann`, and `lem-boltzmann-finite`, -/
theorem stoppedStage_mem_sourceClass (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    (((kmswStage w (t - 1)).UR = [] ∧ (kmswStage w (t - 1)).LL = []) ∧
      (∀ e < (kmswStage w (t - 1)).nextEdge,
        (kmswStage w (t - 1)).present e = true) ∧
      (∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
        ¬ (kmswStageDirectedMap w (t - 1)).missing d) ∧
      (kmswStage w (t - 1)).LR.length = r ∧
      ((kmswStage w (t - 1)).UL.length : ℤ) = L w t ∧
      (kmswStage w (t - 1)).nextEdge = t ∧
      (kmswMap w (t - 1)).numEdges = t) := by
  dsimp only
  let t := boltzmannTau r ω
  let w := boltzmannKMSWStream ω
  have hobs := boltzmann_boundary_observable r hr ω hE
  dsimp only [t, w] at hobs
  rcases hobs with ⟨ht, _, _, hLLcard, hULcard, hLRcard, hURcard, _⟩
  have hbridge := kmsw_bdy_geometric_edge_bridge w (t - 1)
  rcases hbridge with
    ⟨_, _, _, _, _, _, _, _, hULbridge, hURbridge, hLLbridge, hLRbridge⟩
  have hURcardZero : Finset.card (kmswStageURDartsFinset w (t - 1)) = 0 := by
    exact_mod_cast hURcard
  have hLLcardZero : Finset.card (kmswStageLLDartsFinset w (t - 1)) = 0 := by
    exact_mod_cast hLLcard
  have hURlengthZero : (kmswStage w (t - 1)).UR.length = 0 := by
    calc
      _ = Finset.card (kmswStageURDartsFinset w (t - 1)) := hURbridge.symm
      _ = 0 := hURcardZero
  have hLLlengthZero : (kmswStage w (t - 1)).LL.length = 0 := by
    calc
      _ = Finset.card (kmswStageLLDartsFinset w (t - 1)) := hLLbridge.symm
      _ = 0 := hLLcardZero
  have hURnil : (kmswStage w (t - 1)).UR = [] := by
    exact List.length_eq_zero_iff.mp hURlengthZero
  have hLLnil : (kmswStage w (t - 1)).LL = [] := by
    exact List.length_eq_zero_iff.mp hLLlengthZero
  have hULbridgeInt :
      (Finset.card (kmswStageULDartsFinset w (t - 1)) : ℤ) =
        ((kmswStage w (t - 1)).UL.length : ℤ) := by
    exact_mod_cast hULbridge
  have hULlength :
      ((kmswStage w (t - 1)).UL.length : ℤ) = L w t := by
    calc
      _ = (Finset.card (kmswStageULDartsFinset w (t - 1)) : ℤ) :=
        hULbridgeInt.symm
      _ = L w t := hULcard
  have hLRcardNat : Finset.card (kmswStageLRDartsFinset w (t - 1)) = r := by
    exact_mod_cast hLRcard
  have hLRlength : (kmswStage w (t - 1)).LR.length = r := by
    calc
      _ = Finset.card (kmswStageLRDartsFinset w (t - 1)) := hLRbridge.symm
      _ = r := hLRcardNat
  have hnext : (kmswStage w (t - 1)).nextEdge = t := by
    have halloc := CutConverse.allocation_count w (t - 1)
    rw [hURnil, hLLnil] at halloc
    simp only [List.length_nil, Nat.add_zero] at halloc
    omega
  have hpresent : ∀ e < (kmswStage w (t - 1)).nextEdge,
      (kmswStage w (t - 1)).present e = true := by
    intro e he
    have hnoFalse : (kmswStage w (t - 1)).present e ≠ false := by
      intro hp
      have hmissing :=
        (kmswStage_missing_edges_exactly_UR_append_LL w (t - 1) e he).1 hp
      simp [hURnil, hLLnil] at hmissing
    cases hp : (kmswStage w (t - 1)).present e with
    | false => exact (hnoFalse hp).elim
    | true => rfl
  have hnoDart : ∀ d : StageDart (kmswStage w (t - 1)).nextEdge,
      ¬ (kmswStageDirectedMap w (t - 1)).missing d := by
    intro d hmissing
    have hp := hpresent d.1.val d.1.isLt
    change (kmswStage w (t - 1)).present d.1.val = false at hmissing
    rw [hp] at hmissing
    cases hmissing
  have hmapEdges : (kmswMap w (t - 1)).numEdges = t := by
    rw [kmswMap_numEdges w (t - 1)]
    exact hnext
  exact ⟨⟨hURnil, hLLnil⟩, hpresent, hnoDart, hLRlength, hULlength,
    hnext, hmapEdges⟩

end DirectedDistances.KMSW
