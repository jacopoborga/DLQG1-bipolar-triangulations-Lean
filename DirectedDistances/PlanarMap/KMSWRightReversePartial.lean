module

public import DirectedDistances.PlanarMap.KMSWRightEndpointClass
public import DirectedDistances.PlanarMap.KMSWLeftPartialization
public import DirectedDistances.PlanarMap.DirectedMapMarkMissing
public import DirectedDistances.PlanarMap.DirectedMapIso
public import DirectedDistances.PlanarMap.KMSWLeftPartialInjective

/-! # Partial maps after right endpoint reversal

The geometric edges are retained when their orientations are erased.
simple-boundary restriction not assumed; not the paper result. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- endpoint reversal is invisible after declaring the reversed boundary edges missing;
simple-boundary restriction not assumed; not the paper result. The forward darts of the right prefix. -/
@[expose] def rightPrefixDarts {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (k : ℕ) : Set D :=
  {d | ∃ i : Fin B.rightPath.darts.length,
    i.val < k ∧ B.rightPath.darts.get i = d}

/-- endpoint reversal is invisible after declaring the reversed boundary edges missing;
simple-boundary restriction not assumed; not the paper result. Selected edges belong to the outer face. -/
theorem rightPrefixDarts_outer {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (k : ℕ) :
    ∀ d ∈ rightPrefixDarts B k, B.map.IsOuter d ∨ B.map.IsOuter (B.map.edgeInv d) := by
  rintro d ⟨i, _hi, hget⟩
  apply Or.inr
  apply B.outerSplit.1.1
  apply B.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append]
  apply Or.inr
  apply List.mem_map.mpr
  refine ⟨d, List.mem_reverse.mpr ?_, rfl⟩
  exact hget ▸ List.get_mem B.rightPath.darts i

private theorem mem_rightPrefixDarts_iff {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (k : ℕ) (d : D) :
    d ∈ rightPrefixDarts B k ↔ d ∈ B.rightPath.darts.take k := by
  constructor
  · rintro ⟨i, hi, hget⟩
    exact List.mem_take_iff_getElem.mpr ⟨i.val, by omega, hget⟩
  · intro hd
    obtain ⟨i, hi, hget⟩ := List.mem_take_iff_getElem.mp hd
    change ∃ j : Fin B.rightPath.darts.length, j.val < k ∧ B.rightPath.darts.get j = d
    refine ⟨⟨i, by omega⟩, ?_, hget⟩
    exact (Nat.lt_min.mp hi).1

private theorem mem_leftMissingDarts_iff_take {ℓ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) (d : D) :
    d ∈ leftMissingDarts B ↔ d ∈ B.leftPath.darts.take (ℓ - 1) := by
  have hlen := B.leftPath.darts_length
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_take_iff_getElem.mpr ⟨i.val, by omega, rfl⟩
  · intro hd
    obtain ⟨i, hi, hget⟩ := List.mem_take_iff_getElem.mp hd
    change ∃ j : Fin B.leftPath.darts.length,
      j.val + 1 < B.leftPath.darts.length ∧ d = B.leftPath.darts.get j
    refine ⟨⟨i, by omega⟩, ?_, hget.symm⟩
    dsimp only
    omega

private theorem boundary_cast_map {a b c e : ℕ} (ha : a = c) (hb : b = e)
    (C : BoundaryMbcClass D a b) :
    (boundaryMbcClassEquiv ha hb C).val.map = C.val.map := by
  cases ha
  cases hb
  rfl

private theorem boundary_cast_leftDarts {a b c e : ℕ} (ha : a = c) (hb : b = e)
    (C : BoundaryMbcClass D a b) :
    (boundaryMbcClassEquiv ha hb C).val.leftPath.darts = C.val.leftPath.darts := by
  cases ha
  cases hb
  rfl

private theorem reverse_map {ℓ n : ℕ}
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    (kmswRightEndpointReverseRep R hℓ hbc).B.map =
      flipRightPrefix (toStrongRightEndpoint R.B hℓ) (ℓ - 1) (by omega) (by omega) := by
  change (kmswRightEndpointReverseStrong R hℓ hbc).map = _
  dsimp only [kmswRightEndpointReverseStrong, rightEndpointReversalEquiv,
    Equiv.trans_apply, Equiv.ofBijective_apply]
  rw [boundary_cast_map]
  rfl

private theorem reverse_leftDarts {ℓ n : ℕ}
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    (kmswRightEndpointReverseRep R hℓ hbc).B.leftPath.darts =
      (R.B.rightPath.darts.take (ℓ - 1)).reverse.map R.B.map.edgeInv ++
        R.B.leftPath.darts := by
  change (kmswRightEndpointReverseStrong R hℓ hbc).leftPath.darts = _
  dsimp only [kmswRightEndpointReverseStrong, rightEndpointReversalEquiv,
    Equiv.trans_apply, Equiv.ofBijective_apply]
  rw [boundary_cast_leftDarts]
  exact rightPrefixReversal_leftPath_darts
    (toStrongRightEndpoint R.B hℓ) (ℓ - 1) (by omega) (by omega)
    (toBoundaryMbcClassRightEndpoint R.B hℓ hbc).property

private theorem reverse_comb {ℓ n : ℕ}
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    (kmswRightEndpointReverseRep R hℓ hbc).B.map.toCombinatorialMap =
      R.B.map.toCombinatorialMap := by
  rw [reverse_map, flipRightPrefix_toCombinatorialMap]
  rfl

private theorem reverse_missing {ℓ n : ℕ}
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled)
    (d : Fin R.dartCount) :
    (kmswRightEndpointReverseRep R hℓ hbc).partialMap.missing d ↔
      d ∈ rightPrefixDarts R.B (ℓ - 1) ∨
        R.B.map.edgeInv d ∈ rightPrefixDarts R.B (ℓ - 1) := by
  let B : BipolarTriangulationWithBoundaryBase (Fin R.dartCount) ℓ 1 :=
    (kmswRightEndpointReverseStrong R hℓ hbc).toBase
  change (d ∈ leftMissingDarts B ∨ B.map.edgeInv d ∈ leftMissingDarts B) ↔ _
  have hl : B.leftPath.darts =
      (R.B.rightPath.darts.take (ℓ - 1)).reverse.map R.B.map.edgeInv ++
        R.B.leftPath.darts := reverse_leftDarts R hℓ hbc
  simp only [mem_leftMissingDarts_iff_take, hl]
  have hlen : ((R.B.rightPath.darts.take (ℓ - 1)).reverse.map
      R.B.map.edgeInv).length = ℓ - 1 := by
    simp only [List.length_map, List.length_reverse, List.length_take,
      R.B.rightPath.darts_length]
    omega
  have ht := List.take_append_length
    (l₁ := (R.B.rightPath.darts.take (ℓ - 1)).reverse.map R.B.map.edgeInv)
    (l₂ := R.B.leftPath.darts)
  rw [hlen] at ht
  simp only [ht]
  have hi : B.map.edgeInv = R.B.map.edgeInv :=
    congrArg CombinatorialMap.edgeInv (reverse_comb R hℓ hbc)
  rw [hi]
  simp only [List.mem_map_of_involutive R.B.map.edgeInv_invol,
    List.mem_reverse, R.B.map.edgeInv_invol, mem_rightPrefixDarts_iff, or_comm]

/-- endpoint reversal is invisible after declaring the reversed boundary edges missing;
simple-boundary restriction not assumed; not the paper result. The isomorphism fixes every dart. -/
@[expose] noncomputable def kmswRightEndpointReverseRep_partialMapIso {ℓ n : ℕ}
    (R : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ) (hbc : R.IsChanneled) :
    DirectedMapWithMissingIso (kmswRightEndpointReverseRep R hℓ hbc).partialMap
      (R.B.map.markMissing (rightPrefixDarts R.B (ℓ - 1))
        (rightPrefixDarts_outer R.B (ℓ - 1))) where
  toEquiv := Equiv.refl _
  rot_comm := by
    intro d
    change (kmswRightEndpointReverseRep R hℓ hbc).B.map.rot d = R.B.map.rot d
    exact congrArg (fun M => M.rot d) (reverse_comb R hℓ hbc)
  edgeInv_comm := by
    intro d
    change (kmswRightEndpointReverseRep R hℓ hbc).B.map.edgeInv d = R.B.map.edgeInv d
    exact congrArg (fun M => M.edgeInv d) (reverse_comb R hℓ hbc)
  missing_iff := by
    intro d
    change Fin R.dartCount at d
    change (R.B.map.missing d ∨ d ∈ rightPrefixDarts R.B (ℓ - 1) ∨
      R.B.map.edgeInv d ∈ rightPrefixDarts R.B (ℓ - 1)) ↔ _
    erw [reverse_missing R hℓ hbc]
    exact or_iff_right (R.B.noMissingDarts d)
  tail_iff := by
    intro d
    change Fin R.dartCount at d
    change (R.B.map.tail d ∧ ¬ (d ∈ rightPrefixDarts R.B (ℓ - 1) ∨
      R.B.map.edgeInv d ∈ rightPrefixDarts R.B (ℓ - 1))) ↔
        (kmswRightEndpointReverseRep R hℓ hbc).B.map.tail d ∧
          ¬ (kmswRightEndpointReverseRep R hℓ hbc).partialMap.missing d
    erw [reverse_missing R hℓ hbc]
    by_cases hd : d ∈ rightPrefixDarts R.B (ℓ - 1) ∨
        R.B.map.edgeInv d ∈ rightPrefixDarts R.B (ℓ - 1)
    · simp only [hd, not_true_eq_false, and_false]
    · have hn : d ∉ rightPrefixFlipDarts (toStrongRightEndpoint R.B hℓ) (ℓ - 1) := by
        change ¬ (d ∈ R.B.rightPath.darts.take (ℓ - 1) ∨
          R.B.map.edgeInv d ∈ R.B.rightPath.darts.take (ℓ - 1))
        simpa only [mem_rightPrefixDarts_iff] using hd
      rw [reverse_map, flipRightPrefix_tail_of_not_mem _ _ _ _ d hn]
      rfl
  outer_iff := by
    intro d
    change R.B.map.IsOuter d ↔ (kmswRightEndpointReverseRep R hℓ hbc).B.map.IsOuter d
    rw [reverse_map]
    rfl

/-- endpoint reversal is invisible after declaring the reversed boundary edges missing;
simple-boundary restriction not assumed; not the paper result. Transport from any base-isomorphic representative. -/
theorem kmswRightEndpointReverseRep_partialMapIso_of_baseIso {ℓ n : ℕ}
    (R R' : KMSWMapRep 1 ℓ n) (hℓ : 2 ≤ ℓ)
    (hbc : R.IsChanneled) (hbc' : R'.IsChanneled)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    Nonempty (DirectedMapWithMissingIso (kmswRightEndpointReverseRep R' hℓ hbc').partialMap
      (R.B.map.markMissing (rightPrefixDarts R.B (ℓ - 1))
        (rightPrefixDarts_outer R.B (ℓ - 1)))) := by
  obtain ⟨J⟩ := kmswRightEndpointReverseRep_iso hℓ R R' hbc hbc' I
  exact ⟨(KMSWMapRep.partialMapIso_of_baseIso _ _ J).symm.trans
    (kmswRightEndpointReverseRep_partialMapIso R hℓ hbc)⟩

end DirectedDistances.PlanarMap
