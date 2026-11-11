module

public import DirectedDistances.PlanarMap.KMSWLeftPartialization
public import DirectedDistances.PlanarMap.DirectedMapIso

import DirectedDistances.PlanarMap.BipolarBoundaryBaseIsoOfRot

/-! # Partialization of the decorated (ℓ,1) target is injective

map of a KMSW (ℓ,1) representative determines the representative up to isomorphism
not the paper result. -/

public section
namespace DirectedDistances.PlanarMap

namespace KMSWMapRep

/-- result. The forward construction uses the same dart equivalence. -/
@[expose] def partialMapIso_of_baseIso {ℓ n : ℕ} (R R' : KMSWMapRep ℓ 1 n)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    DirectedMapWithMissingIso R.partialMap R'.partialMap where
  toEquiv := I.toEquiv
  rot_comm := I.partialize_rot_comm
  edgeInv_comm := I.partialize_edgeInv_comm
  missing_iff := I.partialize_missing_iff
  tail_iff := I.partialize_tail_iff
  outer_iff := I.partialize_outer_iff

/-- result. Equal representative classes give isomorphic partial maps. -/
theorem partialMapIso_of_mk_eq_mk {ℓ n : ℕ} (R R' : KMSWMapRep ℓ 1 n)
    (h : KMSWMapIsoClass.mk R = KMSWMapIsoClass.mk R') :
    Nonempty (DirectedMapWithMissingIso R.partialMap R'.partialMap) := by
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff R R').mp h
  exact ⟨partialMapIso_of_baseIso R R' I⟩

end KMSWMapRep

private theorem left_flip_not_outer {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (hℓ : 2 ≤ ℓ) {d : D} (hd : d ∈ B.leftPath.darts) :
    ¬ B.map.IsOuter (B.map.edgeInv d) := by
  have ht : B.map.tail d := ((B.outerSplit.2.2.1 d).mp hd).2.1
  have hnt : ¬ B.map.tail (B.map.edgeInv d) :=
    (B.map.tail_iff d (B.noMissingDarts d)).mp ht
  intro ho
  have hw := B.outerSplit.1.2.1 _ ho
  have hb := B.outerSplit.2.1.mem_iff.mp hw
  simp only [List.append_nil, List.mem_append] at hb
  rcases hb with hleft | hright
  · exact hnt (((B.outerSplit.2.2.1 _).mp hleft).2.1)
  · obtain ⟨e, he, heq⟩ := List.mem_map.mp hright
    have he' : e ∈ B.rightPath.darts := List.mem_reverse.mp he
    have hed : e = d := B.map.edgeInv.injective heq
    subst e
    exact left_right_path_edge_disjoint B hℓ d hd d he' Equiv.Perm.SameCycle.rfl

/-- result. Outer-face membership recovers the erased orientation. -/
theorem KMSWMapRep.tail_iff_isOuter_of_partialMap_missing {ℓ n : ℕ}
    (hℓ : 2 ≤ ℓ) (R : KMSWMapRep ℓ 1 n) (d : Fin R.dartCount)
    (hd : R.partialMap.missing d) :
    R.B.map.tail d ↔ R.B.map.IsOuter d := by
  change d ∈ leftMissingDarts R.B ∨ R.B.map.edgeInv d ∈ leftMissingDarts R.B at hd
  rcases hd with hd | hd
  · have hl := ((mem_leftMissingDarts_iff R.B d).mp hd).1
    have hu := (R.B.outerSplit.2.2.1 d).mp hl
    exact ⟨fun _ => hu.2.2, fun _ => hu.2.1⟩
  · have hl := ((mem_leftMissingDarts_iff R.B (R.B.map.edgeInv d)).mp hd).1
    have ht := ((R.B.outerSplit.2.2.1 _).mp hl).2.1
    have hnt : ¬ R.B.map.tail d := by
      simpa only [R.B.map.edgeInv_invol] using
        (R.B.map.tail_iff _ (R.B.noMissingDarts _)).mp ht
    have hno : ¬ R.B.map.IsOuter d := by
      simpa only [R.B.map.edgeInv_invol] using left_flip_not_outer R.B hℓ hl
    exact ⟨fun h => (hnt h).elim, fun h => (hno h).elim⟩

/-- result. A partial-map isomorphism preserves every original orientation. -/
theorem KMSWMapRep.base_tail_iff_of_partialMapIso {ℓ n : ℕ}
    (hℓ : 2 ≤ ℓ) (R R' : KMSWMapRep ℓ 1 n)
    (J : DirectedMapWithMissingIso R.partialMap R'.partialMap) (d : Fin R.dartCount) :
    R'.B.map.tail (J.toEquiv d) ↔ R.B.map.tail d := by
  by_cases hd : R.partialMap.missing d
  · have hd' := (J.missing_iff d).mpr hd
    rw [R.tail_iff_isOuter_of_partialMap_missing hℓ d hd,
      R'.tail_iff_isOuter_of_partialMap_missing hℓ (J.toEquiv d) hd']
    exact J.outer_iff d
  · have hd' : ¬ R'.partialMap.missing (J.toEquiv d) :=
      fun h => hd ((J.missing_iff d).mp h)
    exact (partialize_tail_of_not_missing R'.B _ _ _ hd').symm.trans
      ((J.tail_iff d).trans (partialize_tail_of_not_missing R.B _ _ _ hd))

/-- result. Every partial-map isomorphism extends to a base-map isomorphism. -/
theorem KMSWMapRep.baseIso_of_partialMapIso {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (R R' : KMSWMapRep ℓ 1 n)
    (J : DirectedMapWithMissingIso R.partialMap R'.partialMap) :
    Nonempty (BipolarBoundaryBaseIso R.B R'.B) := by
  refine ⟨bipolarBoundaryBaseIsoOfRot R.B R'.B J.toEquiv J.rot_comm J.edgeInv_comm
    (R.base_tail_iff_of_partialMapIso hℓ R' J) ?_⟩
  have ho : R.B.map.IsOuter R.B.map.outer := Equiv.Perm.SameCycle.rfl
  exact ⟨R.B.map.outer, ho, (J.outer_iff _).mpr ho⟩

/-- result. Equality of representative classes is equivalent to isomorphism of their partial maps. -/
theorem KMSWMapRep.mk_eq_mk_iff_partialMapIso {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (R R' : KMSWMapRep ℓ 1 n) :
    KMSWMapIsoClass.mk R = KMSWMapIsoClass.mk R' ↔
      Nonempty (DirectedMapWithMissingIso R.partialMap R'.partialMap) := by
  constructor
  · exact R.partialMapIso_of_mk_eq_mk R'
  · rintro ⟨J⟩
    exact (KMSWMapIsoClass.mk_eq_mk_iff R R').mpr
      (R.baseIso_of_partialMapIso hℓ R' J)

end DirectedDistances.PlanarMap
