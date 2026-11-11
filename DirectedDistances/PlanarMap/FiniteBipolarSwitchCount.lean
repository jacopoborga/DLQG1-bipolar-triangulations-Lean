/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarIncomingInterval

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

attribute [local instance] Classical.propDecidable

/-- Darts in the face represented by a quotient class of `faceSucc`
(`defn:planar-map-with-missing-edges`, -/
@[expose] def faceDartFiber (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) : Type _ :=
  {d : D // Quotient.mk
    (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d = q}

private def outerFaceDartFiberEquiv
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    faceDartFiber B (Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) ≃
        {d : D // B.map.IsOuter d} where
  toFun d := ⟨d.1, by
    change B.map.toCombinatorialMap.faceSucc.SameCycle B.map.outer d.1
    exact (Quotient.exact d.2).symm⟩
  invFun d := ⟨d.1, Quotient.sound d.2.symm⟩
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    rfl

/-- The fiber over the marked external face has `ℓ + r` darts, as enumerated
by the outer boundary word (`lem-lr-ind`, -/
theorem faceDartFiber_outer_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card (faceDartFiber B (Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer)) = ℓ + r := by
  classical
  calc
    Nat.card (faceDartFiber B (Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer)) =
        Nat.card {d : D // B.map.IsOuter d} :=
          Nat.card_congr (outerFaceDartFiberEquiv B)
    _ = ℓ + r := outerFace_dartCount_eq_boundaryLengths B

/-- Every inner face fiber consists of the three darts in its face cycle
(`defn:planar-map-with-missing-edges`, -/
theorem faceDartFiber_inner_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    Nat.card (faceDartFiber B q) = 3 := by
  classical
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  have hinner : ¬ B.map.IsOuter d := by
    intro hd
    apply hq
    apply Quotient.sound
    exact hd.symm
  let f := B.map.toCombinatorialMap.faceSucc
  have htri := B.innerFacesDegreeThree d hinner
  let s : Finset D := {d, f d, f (f d)}
  have hfd : f d ≠ d := htri.2.1
  have hffd : f (f d) ≠ d := htri.2.2
  have hfdffd : f d ≠ f (f d) := fun h => hfd (f.injective h.symm)
  have hbij : Set.BijOn f (s : Set D) (s : Set D) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      change x ∈ s at hx
      change f x ∈ s
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl htri.1
    · intro x hx y hy hxy
      exact f.injective hxy
    · intro y hy
      change y ∈ s at hy
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h | h
      · refine ⟨f (f d), by simp [s], ?_⟩
        rw [h]
        exact htri.1
      · exact ⟨d, by simp [s], h.symm⟩
      · exact ⟨f d, by simp [s], h.symm⟩
  let fiberEquiv : faceDartFiber B (Quotient.mk
      (Equiv.Perm.SameCycle.setoid f) d) ≃ {x : D // x ∈ s} := {
    toFun := fun x => by
      refine ⟨x.1, ?_⟩
      have hrel : f.SameCycle x.1 d := by
        exact Quotient.exact x.2
      rcases hrel.symm with ⟨i, hi⟩
      have hpow : (f ^ i) d ∈ (s : Set D) :=
        (hbij.perm_zpow i).1 (by simp [s] : d ∈ (s : Set D))
      rw [hi] at hpow
      exact Finset.mem_coe.mp hpow
    invFun := fun x => by
      refine ⟨x.1, ?_⟩
      apply Quotient.sound
      change f.SameCycle x.1 d
      have hx := x.2
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · simpa [h] using Equiv.Perm.SameCycle.rfl (f := f) (x := d)
      · rw [h]
        exact ⟨2, by change f (f (f d)) = d; exact htri.1⟩
      · rw [h]
        exact ⟨1, by change f (f (f d)) = d; exact htri.1⟩
    left_inv x := by
      apply Subtype.ext
      rfl
    right_inv x := by
      apply Subtype.ext
      rfl }
  have hs : s.card = 3 := by
    change (insert d (insert (f d) ({f (f d)} : Finset D))).card = 3
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hfd h.symm, fun h => hffd h.symm⟩),
      Finset.card_insert_of_notMem (by simpa using hfdffd)]
    simp
  calc
    Nat.card (faceDartFiber B (Quotient.mk
        (Equiv.Perm.SameCycle.setoid f) d)) =
        Nat.card {x : D // x ∈ s} := Nat.card_congr fiberEquiv
    _ = s.card := Nat.subtype_card s (by intro x; rfl)
    _ = 3 := hs

/-- The dart set is partitioned by its face fibers. -/
theorem faceDartFiber_card_sum
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Fintype.card D =
      ∑ q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap,
        Nat.card (faceDartFiber B q) := by
  classical
  let fiber := fun q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap =>
    faceDartFiber B q
  let fiberFintype : ∀ q, Fintype (fiber q) := fun q =>
    Fintype.subtype
      (Finset.univ.filter (fun d : D =>
        Quotient.mk
          (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d = q))
      (by intro d; simp)
  let sigmaFintype : Fintype (Σ q, fiber q) :=
    @Sigma.instFintype _ fiber fiberFintype inferInstance
  let faceOf : D → CombinatorialMap.FaceQuotient B.map.toCombinatorialMap :=
    fun d => Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d
  let e : D ≃ Σ q, fiber q := (Equiv.sigmaFiberEquiv faceOf).symm
  calc
    Fintype.card D = @Fintype.card (Σ q, fiber q) sigmaFintype :=
      @Fintype.card_congr D (Σ q, fiber q) inferInstance sigmaFintype e
    _ = ∑ q, @Fintype.card (fiber q) (fiberFintype q) :=
      @Fintype.card_sigma _ fiber inferInstance fiberFintype
    _ = ∑ q, Nat.card (faceDartFiber B q) := by
      apply Finset.sum_congr rfl
      intro q hq
      change @Fintype.card (fiber q) (fiberFintype q) = Nat.card (fiber q)
      exact (@Nat.card_eq_fintype_card (fiber q) (fiberFintype q)).symm

/-- The inner face classes are precisely all face classes except the marked
external class, so their count is `numInnerFaces` (`defn:planar-map-with-missing-edges`, -/
theorem innerFaceClass_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Fintype.card {q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap //
      q ≠ Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer} =
      B.map.numInnerFaces := by
  classical
  let outerQ : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap :=
    Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer
  calc
    Fintype.card {q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap // q ≠ outerQ} =
        Fintype.card (CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    _ = B.map.numInnerFaces := rfl

/-- Counting all darts face by face gives three darts per inner face and the
`ℓ + r` outer-face darts (`lem-lr-ind`, -/
theorem dartCount_eq_innerFaces
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Fintype.card D = 3 * B.map.numInnerFaces + (ℓ + r) := by
  classical
  let outerQ : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap :=
    Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer
  let fiberCard : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap → ℕ :=
    fun q => Nat.card (faceDartFiber B q)
  have hnum : (Finset.univ.erase outerQ).card = B.map.numInnerFaces := by
    calc
      (Finset.univ.erase outerQ).card =
          Fintype.card (CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) - 1 := by
        simp
      _ = B.map.numInnerFaces := rfl
  calc
    Fintype.card D = ∑ q, fiberCard q := faceDartFiber_card_sum B
    _ = fiberCard outerQ + ∑ q ∈ Finset.univ.erase outerQ, fiberCard q := by
      rw [← Finset.sum_erase_add (a := outerQ) Finset.univ fiberCard (Finset.mem_univ outerQ)]
      exact add_comm _ _
    _ = (ℓ + r) + ∑ q ∈ Finset.univ.erase outerQ, 3 := by
      congr 1
      · exact faceDartFiber_outer_card B
      · apply Finset.sum_congr rfl
        intro q hq
        apply faceDartFiber_inner_card B q
        exact (Finset.mem_erase.mp hq).1
    _ = (ℓ + r) + 3 * B.map.numInnerFaces := by
      rw [Finset.sum_const_nat (fun q hq => rfl), hnum, Nat.mul_comm]
    _ = 3 * B.map.numInnerFaces + (ℓ + r) := by
      exact Nat.add_comm _ _

end DirectedDistances.PlanarMap
