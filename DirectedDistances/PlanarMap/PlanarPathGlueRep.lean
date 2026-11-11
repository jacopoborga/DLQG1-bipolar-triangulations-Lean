/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathGlueBasePackage
public import DirectedDistances.PlanarMap.PlanarPathGlueIso
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIsoOfRot
public import DirectedDistances.PlanarMap.LRIndClassEquiv

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {DL DL' DR DR' : Type*}
  [Fintype DL] [DecidableEq DL] [Fintype DL'] [DecidableEq DL']
  [Fintype DR] [DecidableEq DR] [Fintype DR'] [DecidableEq DR']
  {ℓ s r : ℕ}
  {BL : BipolarTriangulationWithBoundaryBase DL ℓ s}
  {BR : BipolarTriangulationWithBoundaryBase DR s r}
  {BL' : BipolarTriangulationWithBoundaryBase DL' ℓ s}
  {BR' : BipolarTriangulationWithBoundaryBase DR' s r}



@[expose] noncomputable def glueBaseIso
    (I : BipolarBoundaryBaseIso BL BL') (J : BipolarBoundaryBaseIso BR BR') :
    BipolarBoundaryBaseIso (glueBase BL BR) (glueBase BL' BR') := by
  apply bipolarBoundaryBaseIsoOfRot (glueBase BL BR) (glueBase BL' BR')
    (glueDartCongr I J)
  · intro d
    simpa only [glueBase_map, glueDirectedMap_toCombinatorialMap] using
      (glueDartCongr_rot I J d)
  · intro d
    simpa only [glueBase_map, glueDirectedMap_toCombinatorialMap,
      glueCombinatorialMap_edgeInv] using (glueDartCongr_edgeInv I J d)
  · intro d
    simpa only [glueBase_map, glueDirectedMap_tail] using
      (glueDartCongr_tail I J d)
  · refine ⟨(glueBase BL BR).map.outer, ?_, ?_⟩
    · change Equiv.Perm.SameCycle _ _ _
      exact Equiv.Perm.SameCycle.rfl
    · rw [glueBase_map, glueBase_map, glueDartCongr_outer I J]
      change Equiv.Perm.SameCycle _ _ _
      exact Equiv.Perm.SameCycle.rfl




theorem simplePath_edgeOrbit_injective {D : Type*}
    [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    {u v : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M u v n) :
    Function.Injective (fun i : Fin P.darts.length =>
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.edgeInv)
        (P.darts.get i)) := by
  intro i j h
  have hi := P.edge_step i
  have hj := P.edge_step j
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap _ _).mp
      (Quotient.exact h) with he | he
  · have hv := hj.2.2.1.trans ((congrArg (dartTailVertex M) he).trans
      hi.2.2.1.symm)
    have heq := List.nodup_iff_injective_get.mp P.vertices_nodup hv
    exact Fin.ext (congrArg Fin.val heq).symm
  · exact False.elim (((M.tail_iff _ hi.1).mp hi.2.1)
      (by rw [← he]; exact hj.2.1))



theorem rightBoundary_length_le_numEdges {D : Type*}
    [Fintype D] [DecidableEq D] {ℓ s : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ s) :
    s ≤ B.map.toCombinatorialMap.numEdges := by
  classical
  let f : Fin B.rightPath.darts.length →
      CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap := fun i =>
    Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.edgeInv)
      (B.rightPath.darts.get i)
  have hf : Function.Injective f := simplePath_edgeOrbit_injective B.rightPath
  simpa only [Fintype.card_fin, B.rightPath.darts_length,
    CombinatorialMap.numEdges] using Fintype.card_le_of_injective f hf




@[expose] noncomputable def glueRep {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b) :
    KMSWMapRep ℓ r (a + b - s) := by
  apply KMSWMapRep.ofBase (glueBase A.B Bm.B)
  have hcount := glueBase_numEdges A.B Bm.B
  rw [A.edges, Bm.edges] at hcount
  have hs : s ≤ a := by
    rw [← A.edges]
    exact rightBoundary_length_le_numEdges A.B
  omega



theorem glueRep_edges {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (_Bm : KMSWMapRep s r b) :
    (a + b - s) + s = a + b := by
  have hs : s ≤ a := by
    rw [← A.edges]
    exact rightBoundary_length_le_numEdges A.B
  omega

private theorem ofBase_iso_of_iso {D D' : Type*}
    [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    {ℓ r n : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (hB : B.map.toCombinatorialMap.numEdges = n)
    (hB' : B'.map.toCombinatorialMap.numEdges = n)
    (h : Nonempty (BipolarBoundaryBaseIso B B')) :
    Nonempty (BipolarBoundaryBaseIso (KMSWMapRep.ofBase B hB).B
      (KMSWMapRep.ofBase B' hB').B) := by
  rcases h with ⟨I⟩
  let e := Fintype.equivFin D
  let e' := Fintype.equivFin D'
  change Nonempty (BipolarBoundaryBaseIso (B.transport e) (B'.transport e'))
  exact ⟨(B.transportIso e).symm.trans (I.trans (B'.transportIso e'))⟩





theorem glueRep_iso {x : XDP} {a b : ℕ}
    {A A' : KMSWMapRep ℓ s a} {Bm Bm' : KMSWMapRep s r b}
    (_hA : IsMLRepresentative x A) (_hA' : IsMLRepresentative x A')
    (_hB : IsMRRepresentative x Bm) (_hB' : IsMRRepresentative x Bm')
    (hAA : Nonempty (BipolarBoundaryBaseIso A.B A'.B))
    (hBB : Nonempty (BipolarBoundaryBaseIso Bm.B Bm'.B)) :
    Nonempty (BipolarBoundaryBaseIso (glueRep A Bm).B
      (glueRep A' Bm').B) := by
  have hG : (glueBase A.B Bm.B).map.toCombinatorialMap.numEdges = a + b - s := by
    have hcount := glueBase_numEdges A.B Bm.B
    rw [A.edges, Bm.edges] at hcount
    have hs : s ≤ a := by
      rw [← A.edges]
      exact rightBoundary_length_le_numEdges A.B
    omega
  have hG' : (glueBase A'.B Bm'.B).map.toCombinatorialMap.numEdges = a + b - s := by
    have hcount := glueBase_numEdges A'.B Bm'.B
    rw [A'.edges, Bm'.edges] at hcount
    have hs : s ≤ a := by
      rw [← A'.edges]
      exact rightBoundary_length_le_numEdges A'.B
    omega
  change Nonempty (BipolarBoundaryBaseIso
    (KMSWMapRep.ofBase (glueBase A.B Bm.B) hG).B
    (KMSWMapRep.ofBase (glueBase A'.B Bm'.B) hG').B)
  apply ofBase_iso_of_iso hG hG'
  rcases hAA with ⟨I⟩
  rcases hBB with ⟨J⟩
  exact ⟨glueBaseIso I J⟩

end DirectedDistances.PlanarMap
