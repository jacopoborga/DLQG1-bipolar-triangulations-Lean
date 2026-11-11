module

public import DirectedDistances.PlanarMap.BdyReverseChanneled
public import DirectedDistances.PlanarMap.BdyReversePaths
public import DirectedDistances.PlanarMap.FiniteBipolarXDP

/-! # Restricted right-prefix reversal and injectivity

conditional on the simple-boundary carrier `BipolarTriangulationWithBoundary`.
Lemma 3.18 and are not counted in the paper inventory. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

open BipolarTriangulationWithBoundary

/-- Right-prefix reversal on the simple-boundary carrier, toward
restricted helper, not counted. -/
@[expose] noncomputable def rightPrefixReversal
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    BipolarTriangulationWithBoundary D (ℓ + k) (r - k) :=
  (Classical.choice (rightPrefixBoundaryPaths_exists B k hk hkr)).toBoundaryChanneled
    B k hk hkr hbc

section Projections

variable (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
  (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled)

/-- Exact map of the restricted reversal (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_map :
    (rightPrefixReversal B k hk hkr hbc).map = flipRightPrefix B k hk hkr := rfl

/-- Exact sink of the restricted reversal (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_sink :
    (rightPrefixReversal B k hk hkr hbc).sink = B.sink := rfl

/-- Exact source of the restricted reversal (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_source :
    (rightPrefixReversal B k hk hkr hbc).source =
      rightBoundaryVertexAt B k (Nat.le_of_lt hkr) := rfl

/-- Exact left darts of the restricted reversal (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_leftPath_darts :
    (rightPrefixReversal B k hk hkr hbc).leftPath.darts =
      (B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv ++
        B.leftPath.darts := by
  exact (Classical.choice (rightPrefixBoundaryPaths_exists B k hk hkr)).leftPath_darts

/-- Exact right darts of the restricted reversal (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_rightPath_darts :
    (rightPrefixReversal B k hk hkr hbc).rightPath.darts =
      B.rightPath.darts.drop k := by
  exact (Classical.choice (rightPrefixBoundaryPaths_exists B k hk hkr)).rightPath_darts

/-- The outer word is retained by the restricted reversal (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_outerWord :
    (rightPrefixReversal B k hk hkr hbc).outerWord = B.outerWord := rfl

/-- Membership after restricted reversal (`lem-bdy-reverse`, -/
theorem rightPrefixReversal_InMbc :
    InMbc (ℓ + k) (r - k) (rightPrefixReversal B k hk hkr hbc) :=
  toBoundaryChanneled_InMbc B k hk hkr
    (Classical.choice (rightPrefixBoundaryPaths_exists B k hk hkr)) hbc

end Projections
/-- Restricted reversal on the boundary-channeled subtype (`lem-bdy-reverse`, -/
@[expose] noncomputable def rightPrefixReversalMbc (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    {B : BipolarTriangulationWithBoundary D ℓ r // InMbc ℓ r B} →
      {B : BipolarTriangulationWithBoundary D (ℓ + k) (r - k) //
        InMbc (ℓ + k) (r - k) B} :=
  fun B => ⟨rightPrefixReversal B.val k hk hkr B.property,
    rightPrefixReversal_InMbc B.val k hk hkr B.property⟩

/-- Flipping the same prefix orbits back restores the old map -/
theorem flipRightPrefix_roundTrip
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    flipOrientation (flipRightPrefix B k hk hkr) (rightPrefixFlipDarts B k)
      (rightPrefixFlip_condition B k) = B.map :=
  flipOrientation_involutive B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlip_condition B k)

/-- Recover the old left darts by dropping the reversed prefix -/
theorem rightPrefixReversal_recover_leftPath_darts
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal B k hk hkr hbc).leftPath.darts.drop k =
      B.leftPath.darts := by
  rw [rightPrefixReversal_leftPath_darts]
  have hlen : ((B.rightPath.darts.take k).reverse.map
      B.map.toCombinatorialMap.edgeInv).length = k := by
    simp only [List.length_map, List.length_reverse, List.length_take,
      B.rightPath.darts_length]
    omega
  have h := List.drop_append_length
    (l₁ := (B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv)
    (l₂ := B.leftPath.darts)
  rw [hlen] at h
  exact h

/-- Recover the old right darts by undoing the prefix reversal -/
theorem rightPrefixReversal_recover_rightPath_darts
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    ((rightPrefixReversal B k hk hkr hbc).leftPath.darts.take k).reverse.map
        (rightPrefixReversal B k hk hkr hbc).map.toCombinatorialMap.edgeInv ++
      (rightPrefixReversal B k hk hkr hbc).rightPath.darts = B.rightPath.darts := by
  rw [rightPrefixReversal_leftPath_darts, rightPrefixReversal_rightPath_darts]
  have hlen : ((B.rightPath.darts.take k).reverse.map
      B.map.toCombinatorialMap.edgeInv).length = k := by
    simp only [List.length_map, List.length_reverse, List.length_take,
      B.rightPath.darts_length]
    omega
  have htake := List.take_append_length
    (l₁ := (B.rightPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv)
    (l₂ := B.leftPath.darts)
  rw [hlen] at htake
  rw [htake]
  change (((B.rightPath.darts.take k).reverse.map
    B.map.toCombinatorialMap.edgeInv).reverse.map
    B.map.toCombinatorialMap.edgeInv) ++ B.rightPath.darts.drop k = _
  simp only [List.map_reverse, List.reverse_reverse, List.map_map,
    Function.comp_def, B.map.toCombinatorialMap.edgeInv_invol, List.map_id_fun',
    id_eq, List.take_append_drop]

/-- Equal restricted reversals recover equal old maps and boundary dart lists -/
theorem rightPrefixReversal_eq_imp_map_and_darts
    {B C : BipolarTriangulationWithBoundary D ℓ r} (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r)
    (hbc : B.IsBoundaryChanneled) (hcc : C.IsBoundaryChanneled)
    (h : rightPrefixReversal B k hk hkr hbc = rightPrefixReversal C k hk hkr hcc) :
    B.map = C.map ∧ B.leftPath.darts = C.leftPath.darts ∧
      B.rightPath.darts = C.rightPath.darts := by
  have hlB := rightPrefixReversal_recover_leftPath_darts B k hk hkr hbc
  rw [h] at hlB
  have hl : B.leftPath.darts = C.leftPath.darts :=
    hlB.symm.trans (rightPrefixReversal_recover_leftPath_darts C k hk hkr hcc)
  have hrB := rightPrefixReversal_recover_rightPath_darts B k hk hkr hbc
  rw [h] at hrB
  have hr : B.rightPath.darts = C.rightPath.darts :=
    hrB.symm.trans (rightPrefixReversal_recover_rightPath_darts C k hk hkr hcc)
  have hf : flipRightPrefix B k hk hkr = flipRightPrefix C k hk hkr := by
    simpa only [rightPrefixReversal_map] using
      congrArg (fun X => X.map) h
  have hcm : B.map.toCombinatorialMap = C.map.toCombinatorialMap := by
    simpa only [flipRightPrefix_toCombinatorialMap] using
      congrArg DirectedMapWithMissing.toCombinatorialMap hf
  have hset : rightPrefixFlipDarts B k = rightPrefixFlipDarts C k := by
    ext d
    change (d ∈ B.rightPath.darts.take k ∨
      B.map.toCombinatorialMap.edgeInv d ∈ B.rightPath.darts.take k) ↔
      (d ∈ C.rightPath.darts.take k ∨
      C.map.toCombinatorialMap.edgeInv d ∈ C.rightPath.darts.take k)
    rw [hr, hcm]
  refine ⟨?_, hl, hr⟩
  calc
    B.map = flipOrientation (flipRightPrefix B k hk hkr) (rightPrefixFlipDarts B k)
        (rightPrefixFlip_condition B k) := (flipRightPrefix_roundTrip B k hk hkr).symm
    _ = flipOrientation (flipRightPrefix C k hk hkr) (rightPrefixFlipDarts C k)
        (rightPrefixFlip_condition C k) := by
      congr 1
    _ = C.map := flipRightPrefix_roundTrip C k hk hkr

/-- Data extensionality used for the restricted helper toward `lem-bdy-reverse` -/
private theorem boundary_eq_of_map_darts_outerWord
    {B C : BipolarTriangulationWithBoundary D ℓ r}
    (hm : B.map = C.map) (hl : B.leftPath.darts = C.leftPath.darts)
    (hr : B.rightPath.darts = C.rightPath.darts) (ho : B.outerWord = C.outerWord) :
    B = C := by
  cases B with
  | mk bm bno bp bf ba bs bt bis bsu bit btu blp brp bo bl br bd be bw =>
    cases C with
    | mk cm cno cp cf ca cs ct cis csu cit ctu clp crp co cl cr cd ce cw =>
      dsimp only at hm hl hr ho
      cases hm
      have hs : bs = cs := csu bs bis
      cases hs
      have ht : bt = ct := ctu bt bit
      cases ht
      have hleft : bl = cl := SimpleDirectedDartPath.eq_of_darts_eq hl
      cases hleft
      have hright : br = cr := SimpleDirectedDartPath.eq_of_darts_eq hr
      cases hright
      cases ho
      rfl

/-- Injectivity of right-prefix reversal on the boundary-channeled
simple-boundary subtype, toward `lem-bdy-reverse`
helper and does not prove the unrestricted printed Lemma 3.18; not counted. -/
theorem rightPrefixReversalMbc_injective (k : ℕ) (hk : 1 ≤ k) (hkr : k < r) :
    Function.Injective
      (rightPrefixReversalMbc (D := D) (ℓ := ℓ) (r := r) k hk hkr) := by
  intro B C h
  apply Subtype.ext
  have hrev : rightPrefixReversal B.val k hk hkr B.property =
      rightPrefixReversal C.val k hk hkr C.property := congrArg Subtype.val h
  obtain ⟨hm, hl, hr⟩ :=
    rightPrefixReversal_eq_imp_map_and_darts k hk hkr B.property C.property hrev
  apply boundary_eq_of_map_darts_outerWord hm hl hr
  exact (rightPrefixReversal_outerWord B.val k hk hkr B.property).symm.trans
    ((congrArg (fun X => X.outerWord) hrev).trans
      (rightPrefixReversal_outerWord C.val k hk hkr C.property))

end DirectedDistances.PlanarMap
