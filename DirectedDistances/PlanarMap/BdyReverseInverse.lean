module

public import DirectedDistances.PlanarMap.BdyReverseBijection
public import DirectedDistances.PlanarMap.MirrorMap
public import DirectedDistances.PlanarMap.EndpointBoundaryClasses

/-! # Inverse of restricted boundary reversal

simple-boundary carrier only. Not counted in the paper inventory; simple-boundary restriction remains

Unqualified general subtype bijectivity is not asserted: its inverse requires
`k < ℓ + k`, which fails at `ℓ = 0`. The endpoint application below has
`ℓ = 1`, so this obstruction does not apply. -/

public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {ℓ r a b : ℕ}

open BipolarTriangulationWithBoundary

/-- Reverse the first `k` left boundary edges by reflection. Restricted
simple-boundary helper for `lem-bdy-reverse` -/
@[expose] noncomputable def leftPrefixReversal
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    BipolarTriangulationWithBoundary D (a - k) (b + k) :=
  (rightPrefixReversal B.mirror k hk hka (mirror_isBoundaryChanneled hbc)).mirror

/-- Left darts after restricted left reversal (`lem-bdy-reverse`, -/
@[simp] theorem leftPrefixReversal_leftPath_darts
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).leftPath.darts = B.leftPath.darts.drop k := by
  change (rightPrefixReversal B.mirror k hk hka
    (mirror_isBoundaryChanneled hbc)).rightPath.darts = _
  exact rightPrefixReversal_rightPath_darts B.mirror k hk hka _

/-- Right darts after restricted left reversal (`lem-bdy-reverse`, -/
@[simp] theorem leftPrefixReversal_rightPath_darts
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).rightPath.darts =
      (B.leftPath.darts.take k).reverse.map B.map.toCombinatorialMap.edgeInv ++
        B.rightPath.darts := by
  change (rightPrefixReversal B.mirror k hk hka
    (mirror_isBoundaryChanneled hbc)).leftPath.darts = _
  exact rightPrefixReversal_leftPath_darts B.mirror k hk hka _

/-- The map of restricted left reversal flips the first left boundary edge
orbits. The set is written using the mirrored right prefix, whose darts are
exactly the original left darts. Helper for `lem-bdy-reverse` -/
@[simp] theorem leftPrefixReversal_map
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).map =
      flipOrientation B.map (rightPrefixFlipDarts B.mirror k)
        (rightPrefixFlip_condition B.mirror k) := by
  change (flipOrientation B.map.mirror (rightPrefixFlipDarts B.mirror k)
    (rightPrefixFlip_condition B.mirror k)).mirror = _
  have h : (flipOrientation B.map.mirror (rightPrefixFlipDarts B.mirror k)
      (rightPrefixFlip_condition B.mirror k)).mirror =
      flipOrientation B.map.mirror.mirror (rightPrefixFlipDarts B.mirror k)
        (rightPrefixFlip_condition B.mirror k) := rfl
  rw [h]
  congr 1
  exact DirectedMapWithMissing.mirror_mirror B.map

/-- Left reversal preserves boundary channeling on the restricted carrier -/
theorem leftPrefixReversal_InMbc
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    InMbc (a - k) (b + k) (leftPrefixReversal B k hk hka hbc) :=
  mirror_isBoundaryChanneled (rightPrefixReversal_InMbc B.mirror k hk hka _)

/-- The outer word survives restricted left reversal (`lem-bdy-reverse`, -/
@[simp] theorem leftPrefixReversal_outerWord
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).outerWord = B.outerWord := by
  have hl : (leftPrefixReversal B k hk hka hbc).outerWord.letters =
      B.outerWord.letters := by
    change ((B.outerWord.letters.reverse.map B.map.edgeInv).reverse.map
      B.map.edgeInv) = _
    simp only [List.map_reverse, List.reverse_reverse, List.map_map,
      Function.comp_def, B.map.toCombinatorialMap.edgeInv_invol, List.map_id_fun', id_eq]
  have extWord : ∀ (X Y : NonemptyWord D), X.letters = Y.letters → X = Y := by
    rintro ⟨xs, hx, hnx⟩ ⟨ys, hy, hny⟩ h
    cases h
    rfl
  exact extWord _ _ hl

/-- The inverse selects the same edge orbits as the forward reversal. -/
private theorem leftPrefix_after_right_set
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    rightPrefixFlipDarts (rightPrefixReversal B k hk hkr hbc).mirror k =
      rightPrefixFlipDarts B k := by
  change {d | d ∈ (rightPrefixReversal B k hk hkr hbc).leftPath.darts.take k ∨
    B.map.edgeInv d ∈ (rightPrefixReversal B k hk hkr hbc).leftPath.darts.take k} = _
  rw [rightPrefixReversal_leftPath_darts]
  have hlen : ((B.rightPath.darts.take k).reverse.map B.map.edgeInv).length = k := by
    simp only [List.length_map, List.length_reverse, List.length_take,
      B.rightPath.darts_length]
    omega
  have ht := List.take_append_length
    (l₁ := (B.rightPath.darts.take k).reverse.map B.map.edgeInv)
    (l₂ := B.leftPath.darts)
  rw [hlen] at ht
  rw [ht]
  ext d
  change (d ∈ (B.rightPath.darts.take k).reverse.map B.map.edgeInv ∨
    B.map.edgeInv d ∈ (B.rightPath.darts.take k).reverse.map B.map.edgeInv) ↔
    (d ∈ B.rightPath.darts.take k ∨ B.map.edgeInv d ∈ B.rightPath.darts.take k)
  simp only [List.mem_map_of_involutive B.map.toCombinatorialMap.edgeInv_invol,
    List.mem_reverse, B.map.toCombinatorialMap.edgeInv_invol, or_comm]

/-- Data extensionality across boundary lengths, for the restricted inverse -/
private theorem boundary_heq_of_map_darts_outerWord
    {B : BipolarTriangulationWithBoundary D ℓ r}
    {C : BipolarTriangulationWithBoundary D a b}
    (hm : B.map = C.map) (hl : B.leftPath.darts = C.leftPath.darts)
    (hr : B.rightPath.darts = C.rightPath.darts) (ho : B.outerWord = C.outerWord) :
    HEq B C := by
  have hℓ : ℓ = a := by
    have h := congrArg List.length hl
    simpa only [B.leftPath.darts_length, C.leftPath.darts_length] using h
  have hρ : r = b := by
    have h := congrArg List.length hr
    simpa only [B.rightPath.darts_length, C.rightPath.darts_length] using h
  cases hℓ
  cases hρ
  apply heq_of_eq
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

/-- Boundary-channeling form of the restricted right-reversal membership -/
theorem rightPrefixReversal_isBoundaryChanneled
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal B k hk hkr hbc).IsBoundaryChanneled :=
  rightPrefixReversal_InMbc B k hk hkr hbc

/-- Boundary-channeling form of the restricted left-reversal membership -/
theorem leftPrefixReversal_isBoundaryChanneled
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    (leftPrefixReversal B k hk hka hbc).IsBoundaryChanneled :=
  leftPrefixReversal_InMbc B k hk hka hbc

/-- Left reversal undoes right reversal, with the boundary lengths explicitly
transported. Restricted simple-boundary helper for `lem-bdy-reverse` -/
theorem leftPrefixReversal_rightPrefixReversal
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    leftPrefixReversal (rightPrefixReversal B k hk hkr hbc) k hk
        (by have := B.left_length_pos; omega)
        (rightPrefixReversal_isBoundaryChanneled B k hk hkr hbc) =
      cast (by congr 1 <;> omega) B := by
  have h : HEq
      (leftPrefixReversal (rightPrefixReversal B k hk hkr hbc) k hk
        (by have := B.left_length_pos; omega)
        (rightPrefixReversal_isBoundaryChanneled B k hk hkr hbc)) B := by
    apply boundary_heq_of_map_darts_outerWord
    · rw [leftPrefixReversal_map]
      trans flipOrientation (flipRightPrefix B k hk hkr)
        (rightPrefixFlipDarts B k) (rightPrefixFlip_condition B k)
      · congr 1
        exact leftPrefix_after_right_set B k hk hkr hbc
      · exact flipRightPrefix_roundTrip B k hk hkr
    · rw [leftPrefixReversal_leftPath_darts]
      exact rightPrefixReversal_recover_leftPath_darts B k hk hkr hbc
    · rw [leftPrefixReversal_rightPath_darts]
      exact rightPrefixReversal_recover_rightPath_darts B k hk hkr hbc
    · rw [leftPrefixReversal_outerWord, rightPrefixReversal_outerWord]
  apply eq_of_heq
  have hc : ∀ {α β : Type u} (e : α = β) (x : α), HEq x (cast e x) := by
    intro α β e x
    cases e
    rfl
  exact h.trans (hc _ B)

/-- Right reversal undoes left reversal, with the boundary lengths explicitly
transported. Restricted simple-boundary helper for `lem-bdy-reverse` -/
theorem rightPrefixReversal_leftPrefixReversal
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    rightPrefixReversal (leftPrefixReversal B k hk hka hbc) k hk
        (by have := B.right_length_pos; omega)
        (leftPrefixReversal_isBoundaryChanneled B k hk hka hbc) =
      cast (by congr 1 <;> omega) B := by
  have h : HEq
      (rightPrefixReversal (leftPrefixReversal B k hk hka hbc) k hk
        (by have := B.right_length_pos; omega)
        (leftPrefixReversal_isBoundaryChanneled B k hk hka hbc)) B := by
    apply boundary_heq_of_map_darts_outerWord
    · rw [rightPrefixReversal_map]
      have hs : rightPrefixFlipDarts (leftPrefixReversal B k hk hka hbc) k =
          rightPrefixFlipDarts B.mirror k :=
        leftPrefix_after_right_set B.mirror k hk hka (mirror_isBoundaryChanneled hbc)
      trans flipOrientation
        (flipOrientation B.map (rightPrefixFlipDarts B.mirror k)
          (rightPrefixFlip_condition B.mirror k))
        (rightPrefixFlipDarts B.mirror k) (rightPrefixFlip_condition B.mirror k)
      · unfold flipRightPrefix
        congr 1
        exact leftPrefixReversal_map B k hk hka hbc
      · exact flipOrientation_involutive B.map (rightPrefixFlipDarts B.mirror k)
          (rightPrefixFlip_condition B.mirror k)
    · rw [rightPrefixReversal_leftPath_darts]
      exact rightPrefixReversal_recover_rightPath_darts B.mirror k hk hka
        (mirror_isBoundaryChanneled hbc)
    · rw [rightPrefixReversal_rightPath_darts]
      exact rightPrefixReversal_recover_leftPath_darts B.mirror k hk hka
        (mirror_isBoundaryChanneled hbc)
    · rw [rightPrefixReversal_outerWord, leftPrefixReversal_outerWord]
  apply eq_of_heq
  have hc : ∀ {α β : Type u} (e : α = β) (x : α), HEq x (cast e x) := by
    intro α β e x
    cases e
    rfl
  exact h.trans (hc _ B)

/-- Construct the preimage by left reversal and transport its two lengths.
Restricted simple-boundary helper for `lem-bdy-reverse` -/
private theorem leftPrefixReversal_preimage
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hkr : k < r) (hbc : B.IsBoundaryChanneled)
    (hℓ : a - k = ℓ) (hρ : b + k = r) :
    ∃ (C : BipolarTriangulationWithBoundary D ℓ r) (hc : C.IsBoundaryChanneled),
      HEq (rightPrefixReversal C k hk hkr hc) B := by
  subst ℓ
  subst r
  refine ⟨leftPrefixReversal B k hk hka hbc,
    leftPrefixReversal_isBoundaryChanneled B k hk hka hbc, ?_⟩
  have h := rightPrefixReversal_leftPrefixReversal B k hk hka hbc
  exact (heq_of_eq h).trans (cast_heq _ B)

/-- The restricted reversal in the source applications, with left length `1`
and `k = r - 1`, is bijective (`lem-bdy-reverse`,
`EndpointBoundaryClasses` make the carrier's internal-vertex and edge
disjointness fields automatic at lengths `(1,r)` and `(r,1)` for `2 ≤ r`;
these fields therefore discard no endpoint source maps. Restricted
assert the unrestricted printed Lemma 3.18. -/
theorem rightPrefixReversalMbc_endpoint_bijective (hr : 2 ≤ r) :
    Function.Bijective
      (rightPrefixReversalMbc (D := D) (ℓ := 1) (r := r) (r - 1)
        (by omega) (by omega)) := by
  constructor
  · exact rightPrefixReversalMbc_injective (r - 1) (by omega) (by omega)
  · intro B
    obtain ⟨C, hc, h⟩ := leftPrefixReversal_preimage (ℓ := 1) (r := r)
      B.val (r - 1) (by omega) (by omega) (by omega) B.property
      (by omega) (by omega)
    refine ⟨⟨C, hc⟩, ?_⟩
    apply Subtype.ext
    change rightPrefixReversal C (r - 1) _ _ hc = B.val
    exact eq_of_heq h

end DirectedDistances.PlanarMap

