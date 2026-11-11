module

public import DirectedDistances.PaperProofs.Section4.ThinCutSideCarrierCompatibility

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Cross-cut retained-face transport for the half truncations. `SelectedCutSideImagesAgree`
records the left and right selected-dart image equalities in a common target (they are
proved elsewhere and enter here only as a hypothesis). Under it, a left (right) half face
is retained in one cut iff the face with the same common image is retained in the other,
given the outer-dart correspondence and the face-orbit compatibility of the common
embedding, both stated pointwise.

Not proved here: the outer-dart correspondence across cuts, the face-orbit compatibility of
the later-stage embedding, the root/target/boundary/seam mark transport, and the final
reduction of `HalfTruncateCutEqLeastGood`. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left and right selected-dart image equalities of two cuts in one common target `α`,
where `fL, gL, fR, gR` are the cuts' dart maps into the common target. -/
@[expose] def SelectedCutSideImagesAgree {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (v : MapVertex (cutLRep R hR).2.B.map) (v' : MapVertex (cutLRep S hS).2.B.map)
    (u : MapVertex (cutRRep R hR).2.B.map) (u' : MapVertex (cutRRep S hS).2.B.map)
    (fL : Fin (cutLRep R hR).2.dartCount → α) (gL : Fin (cutLRep S hS).2.dartCount → α)
    (fR : Fin (cutRRep R hR).2.dartCount → α) (gR : Fin (cutRRep S hS).2.dartCount → α) :
    Prop :=
  fL '' selectedDarts (presentation (cutLRep R hR).2 .left v) =
      gL '' selectedDarts (presentation (cutLRep S hS).2 .left v') ∧
    fR '' selectedDarts (presentation (cutRRep R hR).2 .right u) =
      gR '' selectedDarts (presentation (cutRRep S hS).2 .right u')

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Selected darts of two cuts with the same common image correspond. -/
theorem selectedDarts_iff_of_image_eq {A B α : Type*} (f : A → α) (g : B → α)
    (hf : Function.Injective f) (hg : Function.Injective g) {U : Set A} {V : Set B}
    (h : f '' U = g '' V) (d : A) (e : B) (hde : f d = g e) : d ∈ U ↔ e ∈ V := by
  constructor
  · intro hd
    have h1 : f d ∈ g '' V := h ▸ Set.mem_image_of_mem f hd
    obtain ⟨e', he', hee⟩ := h1
    exact hg (hee.trans hde) ▸ he'
  · intro he
    have h1 : g e ∈ f '' U := h ▸ Set.mem_image_of_mem g he
    obtain ⟨d', hd', hdd⟩ := h1
    exact hf (hdd.trans hde.symm) ▸ hd'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Face-orbit containment in the image of selected darts, read in a common target whose face
permutation `σ` has the same orbit as the ambient face permutation. -/
theorem faceOrbit_subset_iff_common {H A α : Type*} (σ : Equiv.Perm α)
    (F : A → α) (hF : Function.Injective F) (mapR : H → A) (faceR : Equiv.Perm A)
    (S : Set H) (d : H)
    (horb : ∀ z, Equiv.Perm.SameCycle σ (F (mapR d)) z ↔
      ∃ e, Equiv.Perm.SameCycle faceR (mapR d) e ∧ F e = z) :
    (∀ e : A, Equiv.Perm.SameCycle faceR (mapR d) e → ∃ c : S, mapR c.1 = e) ↔
      ∀ z, Equiv.Perm.SameCycle σ (F (mapR d)) z → z ∈ (F ∘ mapR) '' S := by
  constructor
  · intro h z hz
    obtain ⟨e, he, rfl⟩ := (horb z).mp hz
    obtain ⟨c, hc⟩ := h e he
    exact ⟨c.1, c.2, by simp [hc]⟩
  · intro h e he
    obtain ⟨c, hc, hce⟩ := h (F e) ((horb _).mpr ⟨e, he, rfl⟩)
    exact ⟨⟨c, hc⟩, hF hce⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Face-orbit compatibility of an embedding `F` follows from commutation with the face
permutations along the orbit of `d` only (e.g. supplied dartwise by
`outerSucc_faceSucc_castLE_of_local` for darts off the outer word). -/
theorem faceOrbit_compat_of_commute {A α : Type*} (σ : Equiv.Perm α) (F : A → α)
    (faceR : Equiv.Perm A) (d : A)
    (hc : ∀ a, Equiv.Perm.SameCycle faceR d a → σ (F a) = F (faceR a)) :
    ∀ z, Equiv.Perm.SameCycle σ (F d) z ↔
      ∃ e', Equiv.Perm.SameCycle faceR d e' ∧ F e' = z := by
  have key : ∀ i : ℤ, F ((faceR ^ i) d) = (σ ^ i) (F d) := by
    intro i
    refine Int.induction_on i ?_ ?_ ?_
    · simp
    · intro i ih
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_add, zpow_one, zpow_one, Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, ← hc _ ⟨i, rfl⟩, ih]
    · intro i ih
      have h : (-(i : ℤ) - 1) = -1 + -(i : ℤ) := by ring
      rw [h, zpow_add, zpow_add, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, zpow_neg_one,
        zpow_neg_one, ← ih]
      apply σ.injective
      have horb : Equiv.Perm.SameCycle faceR d (faceR⁻¹ ((faceR ^ (-(i : ℤ))) d)) :=
        Equiv.Perm.sameCycle_apply_right.mp (by
          rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
          exact ⟨-(i : ℤ), rfl⟩)
      rw [hc _ horb]
      simp
  intro z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(faceR ^ i) d, ⟨i, rfl⟩, key i⟩
  · rintro ⟨e', ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (key i).symm⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Under the left selected-dart image equality, a left half face is retained in one cut iff the
face with the same common image is retained in the other, given the outer-dart
correspondence and the common-target face-orbit compatibility of the two embeddings. -/
theorem cutLRep_retainedFace_iff_of_image_eq {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (v : MapVertex (cutLRep R hR).2.B.map) (v' : MapVertex (cutLRep S hS).2.B.map)
    (σ : Equiv.Perm α) (F : Fin R.dartCount → α) (G : Fin S.dartCount → α)
    (hF : Function.Injective F) (hG : Function.Injective G)
    (himg : (F ∘ cutLRepDartMap R hR) '' selectedDarts (presentation (cutLRep R hR).2 .left v) =
      (G ∘ cutLRepDartMap S hS) '' selectedDarts (presentation (cutLRep S hS).2 .left v'))
    (d : Fin (cutLRep R hR).2.dartCount) (e : Fin (cutLRep S hS).2.dartCount)
    (hde : F (cutLRepDartMap R hR d) = G (cutLRepDartMap S hS e))
    (hout : (cutLRep R hR).2.B.map.IsOuter d ↔ (cutLRep S hS).2.B.map.IsOuter e)
    (hF' : ∀ z, Equiv.Perm.SameCycle σ (F (cutLRepDartMap R hR d)) z ↔
      ∃ e', Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
        (cutLRepDartMap R hR d) e' ∧ F e' = z)
    (hG' : ∀ z, Equiv.Perm.SameCycle σ (G (cutLRepDartMap S hS e)) z ↔
      ∃ e', Equiv.Perm.SameCycle S.B.map.toCombinatorialMap.faceSucc
        (cutLRepDartMap S hS e) e' ∧ G e' = z) :
    retainedFace (presentation (cutLRep R hR).2 .left v) d ↔
      retainedFace (presentation (cutLRep S hS).2 .left v') e := by
  rw [cutLRep_retainedFace_iff_selected_image R hR v d,
    cutLRep_retainedFace_iff_selected_image S hS v' e,
    hout.not]
  refine and_congr Iff.rfl ?_
  rw [faceOrbit_subset_iff_common σ F hF (cutLRepDartMap R hR) _ _ d hF',
    faceOrbit_subset_iff_common σ G hG (cutLRepDartMap S hS) _ _ e hG', himg, hde]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Right-side counterpart of `cutLRep_retainedFace_iff_of_image_eq`. -/
theorem cutRRep_retainedFace_iff_of_image_eq {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (v : MapVertex (cutRRep R hR).2.B.map) (v' : MapVertex (cutRRep S hS).2.B.map)
    (σ : Equiv.Perm α) (F : Fin R.dartCount → α) (G : Fin S.dartCount → α)
    (hF : Function.Injective F) (hG : Function.Injective G)
    (himg : (F ∘ cutRRepDartMap R hR) '' selectedDarts (presentation (cutRRep R hR).2 .right v) =
      (G ∘ cutRRepDartMap S hS) '' selectedDarts (presentation (cutRRep S hS).2 .right v'))
    (d : Fin (cutRRep R hR).2.dartCount) (e : Fin (cutRRep S hS).2.dartCount)
    (hde : F (cutRRepDartMap R hR d) = G (cutRRepDartMap S hS e))
    (hout : (cutRRep R hR).2.B.map.IsOuter d ↔ (cutRRep S hS).2.B.map.IsOuter e)
    (hF' : ∀ z, Equiv.Perm.SameCycle σ (F (cutRRepDartMap R hR d)) z ↔
      ∃ e', Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
        (cutRRepDartMap R hR d) e' ∧ F e' = z)
    (hG' : ∀ z, Equiv.Perm.SameCycle σ (G (cutRRepDartMap S hS e)) z ↔
      ∃ e', Equiv.Perm.SameCycle S.B.map.toCombinatorialMap.faceSucc
        (cutRRepDartMap S hS e) e' ∧ G e' = z) :
    retainedFace (presentation (cutRRep R hR).2 .right v) d ↔
      retainedFace (presentation (cutRRep S hS).2 .right v') e := by
  rw [cutRRep_retainedFace_iff_selected_image R hR v d,
    cutRRep_retainedFace_iff_selected_image S hS v' e,
    hout.not]
  refine and_congr Iff.rfl ?_
  rw [faceOrbit_subset_iff_common σ F hF (cutRRepDartMap R hR) _ _ d hF',
    faceOrbit_subset_iff_common σ G hG (cutRRepDartMap S hS) _ _ e hG', himg, hde]

end DirectedDistances.PaperProofs.Section4
