module

public import DirectedDistances.PlanarMap.KMSWLeftDecoration

/-! Supporting lemmas for paper labels `lem-kmsw-left` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ : ℕ}

private theorem leftMissingDarts_outer
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1) {d : D}
    (hd : d ∈ leftMissingDarts B) : B.map.IsOuter d := by
  apply B.outerSplit.1.1 d
  apply B.outerSplit.2.1.mem_iff.mpr
  simp only [List.append_nil, List.mem_append]
  exact Or.inl ((mem_leftMissingDarts_iff B d).mp hd).1

/-- Erase orientations on the edge orbits of a selected subset of the
canonical left decoration, retaining every geometric edge and the outer face. -/
@[expose] def partialize (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (S : Set D) (hS : S ⊆ leftMissingDarts B) : DirectedMapWithMissing D where
  toCombinatorialMap := B.map.toCombinatorialMap
  missing := fun d => d ∈ S ∨ B.map.edgeInv d ∈ S
  missing_edgeInv := by
    intro d
    simp only [B.map.edgeInv_invol d, or_comm]
  tail := fun d => B.map.tail d ∧ ¬ (d ∈ S ∨ B.map.edgeInv d ∈ S)
  tail_iff := by
    intro d hd
    have hi : ¬ (B.map.edgeInv d ∈ S ∨
        B.map.edgeInv (B.map.edgeInv d) ∈ S) := by
      simpa only [B.map.edgeInv_invol d, or_comm] using hd
    simp only [hd, hi, not_false_eq_true, and_true]
    exact B.map.tail_iff d (B.noMissingDarts d)
  tail_missing := by
    intro d hd ht
    exact ht.2 hd
  outer := B.map.outer
  missing_outer := by
    intro d hd
    rcases hd with hd | hd
    · exact Or.inl (leftMissingDarts_outer B (hS hd))
    · exact Or.inr (leftMissingDarts_outer B (hS hd))



@[simp] theorem partialize_missing_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (S : Set D) (hS : S ⊆ leftMissingDarts B) (d : D) :
    (partialize B S hS).missing d ↔ d ∈ S ∨ B.map.edgeInv d ∈ S := Iff.rfl



theorem partialize_tail_of_not_missing
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (S : Set D) (hS : S ⊆ leftMissingDarts B) (d : D)
    (hd : ¬ (partialize B S hS).missing d) :
    (partialize B S hS).tail d ↔ B.map.tail d := by
  exact ⟨And.left, fun h => ⟨h, hd⟩⟩



@[simp] theorem partialize_toCombinatorialMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (S : Set D) (hS : S ⊆ leftMissingDarts B) :
    (partialize B S hS).toCombinatorialMap = B.map.toCombinatorialMap := rfl



@[simp] theorem partialize_isOuter_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ 1)
    (S : Set D) (hS : S ⊆ leftMissingDarts B) (d : D) :
    (partialize B S hS).IsOuter d ↔ B.map.IsOuter d := Iff.rfl

namespace BipolarBoundaryBaseIso

variable {D' : Type*} [Fintype D'] [DecidableEq D']
  {B : BipolarTriangulationWithBoundaryBase D ℓ 1}
  {B' : BipolarTriangulationWithBoundaryBase D' ℓ 1}

private theorem mem_leftMissingDarts_map_iff (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv d ∈ leftMissingDarts B' ↔ d ∈ leftMissingDarts B := by
  rw [← I.image_leftMissingDarts]
  constructor
  · rintro ⟨e, he, hed⟩
    exact I.toEquiv.injective hed ▸ he
  · intro hd
    exact ⟨d, hd, rfl⟩



theorem partialize_rot_comm (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv ((partialize B (leftMissingDarts B) (fun _ h => h)).rot d) =
      (partialize B' (leftMissingDarts B') (fun _ h => h)).rot (I.toEquiv d) :=
  I.rot_comm d



theorem partialize_edgeInv_comm (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv ((partialize B (leftMissingDarts B) (fun _ h => h)).edgeInv d) =
      (partialize B' (leftMissingDarts B') (fun _ h => h)).edgeInv (I.toEquiv d) :=
  I.edgeInv_comm d



theorem partialize_missing_iff (I : BipolarBoundaryBaseIso B B') (d : D) :
    (partialize B' (leftMissingDarts B') (fun _ h => h)).missing (I.toEquiv d) ↔
      (partialize B (leftMissingDarts B) (fun _ h => h)).missing d := by
  change (I.toEquiv d ∈ leftMissingDarts B' ∨
    B'.map.edgeInv (I.toEquiv d) ∈ leftMissingDarts B') ↔
    (d ∈ leftMissingDarts B ∨ B.map.edgeInv d ∈ leftMissingDarts B)
  rw [← I.edgeInv_comm, I.mem_leftMissingDarts_map_iff, I.mem_leftMissingDarts_map_iff]



theorem partialize_tail_iff (I : BipolarBoundaryBaseIso B B') (d : D) :
    (partialize B' (leftMissingDarts B') (fun _ h => h)).tail (I.toEquiv d) ↔
      (partialize B (leftMissingDarts B) (fun _ h => h)).tail d := by
  change (B'.map.tail (I.toEquiv d) ∧ ¬
    (partialize B' (leftMissingDarts B') (fun _ h => h)).missing (I.toEquiv d)) ↔
    (B.map.tail d ∧ ¬ (partialize B (leftMissingDarts B) (fun _ h => h)).missing d)
  rw [I.tail_iff, I.partialize_missing_iff]



theorem partialize_outer_iff (I : BipolarBoundaryBaseIso B B') (d : D) :
    (partialize B' (leftMissingDarts B') (fun _ h => h)).IsOuter (I.toEquiv d) ↔
      (partialize B (leftMissingDarts B) (fun _ h => h)).IsOuter d :=
  I.outer_iff d

end BipolarBoundaryBaseIso

/-- Canonical partial map of a completed `(ℓ,1)` representative. Helper toward
paper result. -/
@[expose] def KMSWMapRep.partialMap {ℓ n : ℕ} (R : KMSWMapRep ℓ 1 n) :
    DirectedMapWithMissing (Fin R.dartCount) :=
  partialize R.B (leftMissingDarts R.B) (fun _ h => h)

/-- Number of missing geometric edge orbits of the canonical partial map. -/
@[expose] noncomputable def KMSWMapRep.partialMapMissingEdgeCount {ℓ n : ℕ}
    (R : KMSWMapRep ℓ 1 n) : ℕ := by
  classical
  exact Fintype.card
    {e : CombinatorialMap.EdgeQuotient R.partialMap.toCombinatorialMap //
      ∃ d, Quotient.mk (Equiv.Perm.SameCycle.setoid R.partialMap.edgeInv) d = e ∧
        R.partialMap.missing d}

/-- There is exactly one missing geometric edge per nonfinal left-path step. -/
theorem KMSWMapRep.partialMapMissingEdgeCount_eq {ℓ n : ℕ}
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ) :
    R.partialMapMissingEdgeCount = ℓ - 1 := by
  classical
  let B := R.B
  let q : Fin R.dartCount → CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap :=
    Quotient.mk (Equiv.Perm.SameCycle.setoid B.map.edgeInv)
  let E := {e : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
    ∃ d, q d = e ∧ R.partialMap.missing d}
  let idx : Fin (ℓ - 1) → Fin B.leftPath.darts.length :=
    fun i => ⟨i.val, by rw [B.leftPath.darts_length]; omega⟩
  let f : Fin (ℓ - 1) → E := fun i =>
    ⟨q (B.leftPath.darts.get (idx i)), B.leftPath.darts.get (idx i), rfl,
      Or.inl ⟨idx i, by
        have hi := i.isLt
        change i.val + 1 < B.leftPath.darts.length
        rw [B.leftPath.darts_length]
        omega, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hq : q (B.leftPath.darts.get (idx i)) =
          q (B.leftPath.darts.get (idx j)) := congrArg Subtype.val hij
      have hb : boundaryEdgeInjection (toStrongLeftEndpoint B hℓ) (Sum.inl (idx i)) =
          boundaryEdgeInjection (toStrongLeftEndpoint B hℓ) (Sum.inl (idx j)) := hq
      have hs := boundaryEdgeInjection_injective (toStrongLeftEndpoint B hℓ) hb
      have hi : idx i = idx j := Sum.inl.inj hs
      exact Fin.ext (congrArg (fun k : Fin B.leftPath.darts.length => k.val) hi)
    · rintro ⟨e, d, hde, hd⟩
      change d ∈ leftMissingDarts B ∨ B.map.edgeInv d ∈ leftMissingDarts B at hd
      have hfind : ∀ a, a ∈ leftMissingDarts B → q a = e →
          ∃ i, f i = (⟨e, d, hde, hd⟩ : E) := by
        intro a ha hae
        obtain ⟨j, hj, haj⟩ := ha
        have hjlt : j.val < ℓ - 1 := by
          have hlen := B.leftPath.darts_length
          omega
        let i : Fin (ℓ - 1) := ⟨j.val, hjlt⟩
        have hij : idx i = j := Fin.ext rfl
        refine ⟨i, Subtype.ext ?_⟩
        change q (B.leftPath.darts.get (idx i)) = e
        rw [hij, ← haj]
        exact hae
      rcases hd with hd | hd
      · exact hfind d hd hde
      · apply hfind (B.map.edgeInv d) hd
        apply Eq.trans _ hde
        apply Quotient.sound
        exact (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap
          (B.map.edgeInv d) d).mpr (Or.inr (B.map.edgeInv_invol d).symm)
  change Fintype.card E = ℓ - 1
  calc
    Fintype.card E = Fintype.card (Fin (ℓ - 1)) :=
      (Fintype.card_congr (Equiv.ofBijective f hf)).symm
    _ = ℓ - 1 := Fintype.card_fin _

end DirectedDistances.PlanarMap
