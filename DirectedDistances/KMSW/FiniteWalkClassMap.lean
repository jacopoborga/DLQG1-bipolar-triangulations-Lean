/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FiniteWalkClass
public import DirectedDistances.KMSW.StoppedStageMap
public import DirectedDistances.PaperProofs.Section3.KMSWBdyGeometric
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Finite walk classes give source-class KMSW stages

For a walk class with `n ≥ 1`, its stage at time `n - 1` has the four boundary
lengths prescribed by Lemma 3.6, no missing edges, and exactly `n` geometric
edges; its outer word is `UL ++ LR.reverse` (`thm-kmsw`,
`FiniteWalkClass.lean`. This is only helper data for the forward map: inverse
KMSW surjectivity and the source isomorphism-class carrier, including the
does not count Theorem 3.5.

The `decide` cross-checks below give cardinalities `1, 0, 0, 0` for
`(ℓ,r,n) = (1,1,1), (2,1,2), (1,2,2), (2,2,3)`, respectively. They are
finite walk-class counts only and do not claim agreement with triangulation
counts. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3

/-- The finite KMSW walk class maps to a stage with the boundary data and edge
count required of the source class in the forward direction of Theorem 3.5
walk constraints force `1 ≤ ℓ` and `1 ≤ r` from `1 ≤ n`; no positivity premise
on `ℓ` or `r` is needed. Theorem 3.5 surjectivity, its source isomorphism-class
carrier including `m₀`, and the legal-step convention ruling remain outstanding. -/
theorem kmswWalkClassMap_mem_sourceClass {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    let w := codeExtend c
    let m := n - 1
    1 ≤ ℓ ∧
    1 ≤ r ∧
    minL w m = 0 ∧
    minR w m = -(r : ℤ) + 1 ∧
    ((kmswStage w m).UL.length : ℤ) = L w m - minL w m + 1 ∧
    ((kmswStage w m).UR.length : ℤ) = R w m - minR w m ∧
    ((kmswStage w m).LL.length : ℤ) = -minL w m ∧
    ((kmswStage w m).LR.length : ℤ) = -minR w m + 1 ∧
    (kmswStage w m).UL.length = ℓ ∧
    (kmswStage w m).LR.length = r ∧
    (kmswStage w m).UR.length = 0 ∧
    (kmswStage w m).LL.length = 0 ∧
    (kmswStage w m).UR = [] ∧
    (kmswStage w m).LL = [] ∧
    (∀ e < (kmswStage w m).nextEdge, (kmswStage w m).present e = true) ∧
    (∀ d : StageDart (kmswStage w m).nextEdge,
      ¬ (kmswStageDirectedMap w m).missing d) ∧
    (kmswStage w m).nextEdge = n ∧
    (kmswMap w m).numEdges = n ∧
    stageOuterWordVal w m =
      ((kmswStage w m).UL.map fun e => (e, false)) ++
      ((kmswStage w m).LR.reverse.map fun e => (e, true)) := by
  dsimp only
  let w := codeExtend c
  let m := n - 1
  have hend : integrateCodes w m = ((ℓ : ℤ) - 1, -(r : ℤ) + 1) := by
    exact c.property.1
  have hcone : ∀ j ≤ m,
      0 ≤ (integrateCodes w j).1 ∧ -(r : ℤ) + 1 ≤ (integrateCodes w j).2 := by
    intro j hj
    exact c.property.2 j (Finset.mem_range.mpr (by omega))
  have hLend : L w m = (ℓ : ℤ) - 1 := by
    rw [kmsw_L_eq]
    exact congrArg Prod.fst hend
  have hRend : R w m = -(r : ℤ) + 1 := by
    rw [kmsw_R_eq]
    exact congrArg Prod.snd hend
  have hLbound : ∀ j ≤ m, 0 ≤ L w j := by
    intro j hj
    rw [kmsw_L_eq]
    exact (hcone j hj).1
  have hRbound : ∀ j ≤ m, -(r : ℤ) + 1 ≤ R w j := by
    intro j hj
    rw [kmsw_R_eq]
    exact (hcone j hj).2
  have hminL : minL w m = 0 := by
    have hle : runningMin (L w) m ≤ L w 0 := runningMin_le (L w) m 0 (by omega)
    have hge : 0 ≤ runningMin (L w) m := by
      obtain ⟨j, hj, hhit⟩ := runningMin_attained (L w) m
      rw [hhit]
      exact hLbound j hj
    have hzero : L w 0 = 0 := by simp [L]
    change runningMin (L w) m = 0
    rw [hzero] at hle
    omega
  have hminR : minR w m = -(r : ℤ) + 1 := by
    have hle : runningMin (R w) m ≤ R w m := runningMin_le (R w) m m le_rfl
    have hge : -(r : ℤ) + 1 ≤ runningMin (R w) m := by
      obtain ⟨j, hj, hhit⟩ := runningMin_attained (R w) m
      rw [hhit]
      exact hRbound j hj
    change runningMin (R w) m = -(r : ℤ) + 1
    rw [hRend] at hle
    omega
  have hℓpos : 1 ≤ ℓ := by
    have h := (hcone m le_rfl).1
    have h' : 0 ≤ (ℓ : ℤ) - 1 := by simpa only [hend] using h
    omega
  have hrpos : 1 ≤ r := by
    have h := (hcone 0 (by omega)).2
    have hzero : (integrateCodes w 0).2 = 0 := by simp [integrateCodes]
    have h' : -(r : ℤ) + 1 ≤ 0 := by simpa only [hzero] using h
    omega
  have hcards := kmsw_bdy_geometric_segment_cardinalities w m
  rcases hcards with ⟨hULcard, hURcard, hLLcard, hLRcard⟩
  have hbridge := kmsw_bdy_geometric_edge_bridge w m
  rcases hbridge with ⟨_, _, _, _, _, _, _, _, hULbridge, hURbridge,
    hLLbridge, hLRbridge⟩
  have hULcard' : (Finset.card (kmswStageULDartsFinset w m) : ℤ) = ℓ := by
    rw [hULcard, hLend, hminL]
    omega
  have hURcard' : (Finset.card (kmswStageURDartsFinset w m) : ℤ) = 0 := by
    rw [hURcard, hRend, hminR]
    omega
  have hLLcard' : (Finset.card (kmswStageLLDartsFinset w m) : ℤ) = 0 := by
    rw [hLLcard, hminL]
    norm_num
  have hLRcard' : (Finset.card (kmswStageLRDartsFinset w m) : ℤ) = r := by
    rw [hLRcard, hminR]
    omega
  have hULnat : Finset.card (kmswStageULDartsFinset w m) = ℓ := by
    exact_mod_cast hULcard'
  have hURnat : Finset.card (kmswStageURDartsFinset w m) = 0 := by
    exact_mod_cast hURcard'
  have hLLnat : Finset.card (kmswStageLLDartsFinset w m) = 0 := by
    exact_mod_cast hLLcard'
  have hLRnat : Finset.card (kmswStageLRDartsFinset w m) = r := by
    exact_mod_cast hLRcard'
  have hULlen : (kmswStage w m).UL.length = ℓ := by
    calc
      _ = Finset.card (kmswStageULDartsFinset w m) := hULbridge.symm
      _ = ℓ := hULnat
  have hURlen : (kmswStage w m).UR.length = 0 := by
    calc
      _ = Finset.card (kmswStageURDartsFinset w m) := hURbridge.symm
      _ = 0 := hURnat
  have hLLlen : (kmswStage w m).LL.length = 0 := by
    calc
      _ = Finset.card (kmswStageLLDartsFinset w m) := hLLbridge.symm
      _ = 0 := hLLnat
  have hLRlen : (kmswStage w m).LR.length = r := by
    calc
      _ = Finset.card (kmswStageLRDartsFinset w m) := hLRbridge.symm
      _ = r := hLRnat
  have hURnil : (kmswStage w m).UR = [] := List.length_eq_zero_iff.mp hURlen
  have hLLnil : (kmswStage w m).LL = [] := List.length_eq_zero_iff.mp hLLlen
  have hnext : (kmswStage w m).nextEdge = n := by
    have halloc := CutConverse.allocation_count w m
    rw [hURnil, hLLnil] at halloc
    simp only [List.length_nil, Nat.add_zero] at halloc
    omega
  have hpresent : ∀ e < (kmswStage w m).nextEdge,
      (kmswStage w m).present e = true := by
    intro e he
    have hnotfalse : (kmswStage w m).present e ≠ false := by
      intro hp
      have hmissing := (kmswStage_missing_edges_exactly_UR_append_LL w m e he).1 hp
      simp [hURnil, hLLnil] at hmissing
    cases hp : (kmswStage w m).present e with
    | false => exact (hnotfalse hp).elim
    | true => rfl
  have hnoDart : ∀ d : StageDart (kmswStage w m).nextEdge,
      ¬ (kmswStageDirectedMap w m).missing d := by
    intro d hmissing
    have hp := hpresent d.1.val d.1.isLt
    change (kmswStage w m).present d.1.val = false at hmissing
    rw [hp] at hmissing
    cases hmissing
  have houter : stageOuterWordVal w m =
      ((kmswStage w m).UL.map fun e => (e, false)) ++
      ((kmswStage w m).LR.reverse.map fun e => (e, true)) := by
    simpa [hURnil, hLLnil] using (kmsw_bdy_geometric_outer_order w m).1
  have hmapEdges : (kmswMap w m).numEdges = n := by
    rw [kmswMap_numEdges]
    exact hnext
  have hULformula : ((kmswStage w m).UL.length : ℤ) =
      L w m - minL w m + 1 := by
    rw [hULlen, hLend, hminL]
    omega
  have hURformula : ((kmswStage w m).UR.length : ℤ) =
      R w m - minR w m := by
    rw [hURlen, hRend, hminR]
    omega
  have hLLformula : ((kmswStage w m).LL.length : ℤ) = -minL w m := by
    rw [hLLlen, hminL]
    norm_num
  have hLRformula : ((kmswStage w m).LR.length : ℤ) =
      -minR w m + 1 := by
    rw [hLRlen, hminR]
    omega
  exact ⟨hℓpos, hrpos, hminL, hminR,
    hULformula, hURformula, hLLformula, hLRformula,
    hULlen, hLRlen, hURlen, hLLlen, hURnil, hLLnil,
    hpresent, hnoDart, hnext, hmapEdges, houter⟩

/-- Exact `decide` counts for the four tiny finite walk classes in this helper:
`1`, `0`, `0`, and `0`, in the parameter order displayed. These are walk-side
cross-checks only and make no claim of agreement with a triangulation count. -/
theorem tiny_KMSWWalkClass_cardinalities :
    Fintype.card (KMSWWalkClass 1 1 1) = 1 ∧
    Fintype.card (KMSWWalkClass 2 1 2) = 0 ∧
    Fintype.card (KMSWWalkClass 1 2 2) = 0 ∧
    Fintype.card (KMSWWalkClass 2 2 3) = 0 := by
  decide

end DirectedDistances.KMSW
