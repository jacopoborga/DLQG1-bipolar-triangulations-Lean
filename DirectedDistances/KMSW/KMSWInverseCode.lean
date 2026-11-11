/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWCodesOfWalk
public import DirectedDistances.PlanarMap.BipolarInverseWalk
public import DirectedDistances.PlanarMap.BipolarPeanoIncrement

/-! Supporting lemmas for paper labels `thm-kmsw` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}






theorem bipolarInverseWalk_step_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    bipolarInverseWalk B ⟨j + 1, hj⟩ -
        bipolarInverseWalk B ⟨j, by omega⟩ ∈
      ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  have hincr := peanoEdge_height_increment B j hj
  have hraw :
      ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
          (canonicalULHeight B (dartTailVertex B.map a) : ℤ),
        (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
          (canonicalLRHeight B (dartHeadVertex B.map a) : ℤ)) ∈
        ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
    dsimp [a, b] at hincr
    rcases hincr with h | h | h <;> rw [h] <;> simp
  have hdiff :
      bipolarInverseWalk B ⟨j + 1, hj⟩ - bipolarInverseWalk B ⟨j, by omega⟩ =
        ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
            (canonicalULHeight B (dartTailVertex B.map a) : ℤ),
          (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
            (canonicalLRHeight B (dartHeadVertex B.map a) : ℤ)) := by
    apply Prod.ext
    · simp [bipolarInverseWalk, a, b]
    · simp [bipolarInverseWalk, a, b]
  rw [hdiff]
  exact hraw







theorem kmswRepInverseWalk_step_mem
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    kmswRepInverseWalk R ⟨j + 1, hj⟩ -
        kmswRepInverseWalk R ⟨j, by omega⟩ ∈
      ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
  have hsize := kmswRep_numEdges R
  have hmap := bipolarInverseWalk_step_mem R.B j (by omega)
  have hcastSucc :
      Fin.cast R.edges.symm (⟨j + 1, hj⟩ : Fin n) =
        (⟨j + 1, by omega⟩ : Fin R.B.map.toCombinatorialMap.numEdges) := by
    exact Fin.ext rfl
  have hcast :
      Fin.cast R.edges.symm (⟨j, by omega⟩ : Fin n) =
        (⟨j, by omega⟩ : Fin R.B.map.toCombinatorialMap.numEdges) := by
    exact Fin.ext rfl
  change bipolarInverseWalk R.B (Fin.cast R.edges.symm ⟨j + 1, hj⟩) -
      bipolarInverseWalk R.B (Fin.cast R.edges.symm ⟨j, by omega⟩) ∈ _
  rw [hcastSucc, hcast]
  exact hmap






@[expose] noncomputable def kmswRepInverseCode
    (R : KMSWMapRep ℓ r n) : Fin (n - 1) → Fin 3 :=
  codesOfWalk (kmswRepInverseWalk R)






theorem kmswRepInverseCode_admissible
    (R : KMSWMapRep ℓ r n) :
    KMSWWalkAdmissible ℓ r n (kmswRepInverseCode R) := by
  have hn : 0 < n := by
    have h := contour_numEdges_pos R.B
    rw [R.edges] at h
    exact h
  have hstart :
      kmswRepInverseWalk R ⟨0, hn⟩ = (0, 0) :=
    kmswRepInverseWalk_zero R
  have hsteps : ∀ i : Fin (n - 1),
      kmswRepInverseWalk R ⟨i.val + 1, by omega⟩ -
        kmswRepInverseWalk R ⟨i.val, by omega⟩ ∈
          ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
    intro i
    exact kmswRepInverseWalk_step_mem R i.val (by omega)
  have hsource :
      KMSWWalkAdmissible ℓ r n (codesOfWalk (kmswRepInverseWalk R)) := by
    apply (kmswWalkAdmissible_codesOfWalk_iff
      (kmswRepInverseWalk R) hn hstart hsteps).2
    constructor
    · exact kmswRepInverseWalk_last R
    · intro k
      exact kmswRepInverseWalk_cone R k
  simpa only [kmswRepInverseCode] using hsource






@[expose] noncomputable def kmswRepInverseWalkClass
    (R : KMSWMapRep ℓ r n) : KMSWWalkClass ℓ r n := by
  have hn : 0 < n := by
    have h := contour_numEdges_pos R.B
    rw [R.edges] at h
    exact h
  have hstart :
      kmswRepInverseWalk R ⟨0, hn⟩ = (0, 0) :=
    kmswRepInverseWalk_zero R
  have hsteps : ∀ i : Fin (n - 1),
      kmswRepInverseWalk R ⟨i.val + 1, by omega⟩ -
        kmswRepInverseWalk R ⟨i.val, by omega⟩ ∈
          ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
    intro i
    exact kmswRepInverseWalk_step_mem R i.val (by omega)
  exact walkClassOfWalk (kmswRepInverseWalk R) hn hstart hsteps
    (kmswRepInverseWalk_last R)
    (fun k => kmswRepInverseWalk_cone R k)






theorem integrateCodes_kmswRepInverseCode
    (R : KMSWMapRep ℓ r n) (k : ℕ) (hk : k < n) :
    integrateCodes (finiteCodeExtend (kmswRepInverseCode R)) k =
      kmswRepInverseWalk R ⟨k, hk⟩ := by
  have hn : 0 < n := by
    have h := contour_numEdges_pos R.B
    rw [R.edges] at h
    exact h
  have hstart :
      kmswRepInverseWalk R ⟨0, hn⟩ = (0, 0) :=
    kmswRepInverseWalk_zero R
  have hsteps : ∀ i : Fin (n - 1),
      kmswRepInverseWalk R ⟨i.val + 1, by omega⟩ -
        kmswRepInverseWalk R ⟨i.val, by omega⟩ ∈
          ({(-1, 0), (0, 1), (1, -1)} : Set (ℤ × ℤ)) := by
    intro i
    exact kmswRepInverseWalk_step_mem R i.val (by omega)
  simpa only [kmswRepInverseCode] using
    integrateCodes_codesOfWalk (kmswRepInverseWalk R) hn hstart hsteps k hk


end DirectedDistances.KMSW
