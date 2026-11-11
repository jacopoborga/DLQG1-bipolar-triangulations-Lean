/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarSwitchCount





public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The three corners of an inner triangular face have one vertex-switch and
two face-switches. Helper toward `lem-lr-ind`; not the paper result
the checked-in source). -/
theorem innerFace_switch_pattern
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    (vertexSwitchCorner B d ∧
      ¬ vertexSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      ¬ vertexSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d)) ∧
      ¬ faceSwitchCorner B d ∧
      faceSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      faceSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
    (¬ vertexSwitchCorner B d ∧
      vertexSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      ¬ vertexSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d)) ∧
      faceSwitchCorner B d ∧
      ¬ faceSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      faceSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
    (¬ vertexSwitchCorner B d ∧
      ¬ vertexSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      vertexSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d)) ∧
      faceSwitchCorner B d ∧
      faceSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      ¬ faceSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) := by
  rcases innerFace_exactly_one_vertexSwitch B d hinner with h | h | h
  · rcases h with ⟨hv₀, hv₁, hv₂⟩
    left
    refine ⟨hv₀, hv₁, hv₂, ?_, ?_, ?_⟩
    · intro hf
      exact (corner_switch_partition B d).mp hf hv₀
    · exact (corner_switch_partition B (B.map.toCombinatorialMap.faceSucc d)).mpr hv₁
    · exact (corner_switch_partition B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))).mpr hv₂
  · rcases h with ⟨hv₀, hv₁, hv₂⟩
    right
    left
    refine ⟨hv₀, hv₁, hv₂, ?_, ?_, ?_⟩
    · exact (corner_switch_partition B d).mpr hv₀
    · intro hf
      exact (corner_switch_partition B (B.map.toCombinatorialMap.faceSucc d)).mp hf hv₁
    · exact (corner_switch_partition B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))).mpr hv₂
  · rcases h with ⟨hv₀, hv₁, hv₂⟩
    right
    right
    refine ⟨hv₀, hv₁, hv₂, ?_, ?_, ?_⟩
    · exact (corner_switch_partition B d).mpr hv₀
    · exact (corner_switch_partition B (B.map.toCombinatorialMap.faceSucc d)).mpr hv₁
    · intro hf
      exact (corner_switch_partition B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))).mp hf hv₂

private theorem faceDartFiber_pred_card_eq_filter
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) (P : D → Prop) [DecidablePred P] :
    Nat.card {x : faceDartFiber B (Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d) // P x.1} =
      (({d, B.map.toCombinatorialMap.faceSucc d,
        B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d)} : Finset D).filter P).card := by
  classical
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
      have hrel : f.SameCycle x.1 d := Quotient.exact x.2
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
  let fiberPredEquiv :
      {x : faceDartFiber B (Quotient.mk
        (Equiv.Perm.SameCycle.setoid f) d) // P x.1} ≃
        {x : D // x ∈ s ∧ P x} := {
    toFun x := ⟨x.1.1, ⟨(fiberEquiv x.1).2, x.2⟩⟩
    invFun x := ⟨fiberEquiv.symm ⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv x := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv x := by
      apply Subtype.ext
      rfl
  }
  let t : Finset D := s.filter P
  have ht : ∀ x : D, x ∈ t ↔ x ∈ s ∧ P x := by
    intro x
    simp [t]
  calc
    Nat.card {x : faceDartFiber B (Quotient.mk
        (Equiv.Perm.SameCycle.setoid f) d) // P x.1} =
        Nat.card {x : D // x ∈ s ∧ P x} := Nat.card_congr fiberPredEquiv
    _ = t.card := Nat.subtype_card t ht
    _ = (({d, B.map.toCombinatorialMap.faceSucc d,
        B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d)} : Finset D).filter P).card := rfl

/-- A triangular inner-face fiber contains one vertex-switch corner.
leftmost-geodesic definition in the checked-in source). -/
theorem innerFace_vertexSwitchFiber_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    Nat.card {d : faceDartFiber B q // vertexSwitchCorner B d.1} = 1 := by
  classical
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  have hinner : ¬ B.map.IsOuter d := by
    intro hd
    apply hq
    apply Quotient.sound
    exact hd.symm
  let f := B.map.toCombinatorialMap.faceSucc
  have hfd : f d ≠ d := (B.innerFacesDegreeThree d hinner).2.1
  have hffd : f (f d) ≠ d := (B.innerFacesDegreeThree d hinner).2.2
  have hfdffd : f d ≠ f (f d) := fun h => hfd (f.injective h.symm)
  have hpattern := innerFace_switch_pattern B d hinner
  calc
    Nat.card {x : faceDartFiber B (Quotient.mk
        (Equiv.Perm.SameCycle.setoid f) d) // vertexSwitchCorner B x.1} =
      (({d, f d, f (f d)} : Finset D).filter (vertexSwitchCorner B)).card :=
      faceDartFiber_pred_card_eq_filter B d hinner (vertexSwitchCorner B)
    _ = 1 := by
      rcases hpattern with ⟨hv₀, hn₁, hn₂, _, _, _⟩ |
        ⟨hn₀, hv₁, hn₂, _, _, _⟩ |
        ⟨hn₀, hn₁, hv₂, _, _, _⟩
      · have hset : ({d, f d, f (f d)} : Finset D).filter
            (vertexSwitchCorner B) = {d} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩
            · rfl
            · exact (hn₁ h).elim
            · exact (hn₂ h).elim
          · rintro rfl
            exact ⟨by simp, hv₀⟩
        rw [hset]
        simp
      · have hset : ({d, f d, f (f d)} : Finset D).filter
            (vertexSwitchCorner B) = {f d} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩
            · exact (hn₀ h).elim
            · rfl
            · exact (hn₂ h).elim
          · rintro rfl
            exact ⟨by simp, hv₁⟩
        rw [hset]
        simp
      · have hset : ({d, f d, f (f d)} : Finset D).filter
            (vertexSwitchCorner B) = {f (f d)} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩
            · exact (hn₀ h).elim
            · exact (hn₁ h).elim
            · rfl
          · rintro rfl
            exact ⟨by simp, hv₂⟩
        rw [hset]
        simp

/-- A triangular inner-face fiber contains two face-switch corners.
leftmost-geodesic definition in the checked-in source). -/
theorem innerFace_faceSwitchFiber_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    Nat.card {d : faceDartFiber B q // faceSwitchCorner B d.1} = 2 := by
  classical
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  have hinner : ¬ B.map.IsOuter d := by
    intro hd
    apply hq
    apply Quotient.sound
    exact hd.symm
  let f := B.map.toCombinatorialMap.faceSucc
  have hfd : f d ≠ d := (B.innerFacesDegreeThree d hinner).2.1
  have hffd : f (f d) ≠ d := (B.innerFacesDegreeThree d hinner).2.2
  have hfdffd : f d ≠ f (f d) := fun h => hfd (f.injective h.symm)
  have hpattern := innerFace_switch_pattern B d hinner
  calc
    Nat.card {x : faceDartFiber B (Quotient.mk
        (Equiv.Perm.SameCycle.setoid f) d) // faceSwitchCorner B x.1} =
      (({d, f d, f (f d)} : Finset D).filter (faceSwitchCorner B)).card :=
      faceDartFiber_pred_card_eq_filter B d hinner (faceSwitchCorner B)
    _ = 2 := by
      rcases hpattern with ⟨_, _, _, hn₀, hf₁, hf₂⟩ |
        ⟨hn₀, _, _, hf₀, hn₁, hf₂⟩ |
        ⟨hn₀, hn₁, _, hf₀, hf₁, hn₂⟩
      · have hset : ({d, f d, f (f d)} : Finset D).filter
            (faceSwitchCorner B) = {f d, f (f d)} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩
            · exact (hn₀ h).elim
            · exact Or.inl rfl
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨by simp, hf₁⟩
            · exact ⟨by simp, hf₂⟩
        rw [hset]
        change (insert (f d) ({f (f d)} : Finset D)).card = 2
        rw [Finset.card_insert_of_notMem (by simp [hfdffd])]
        simp
      · have hset : ({d, f d, f (f d)} : Finset D).filter
            (faceSwitchCorner B) = {d, f (f d)} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩
            · exact Or.inl rfl
            · exact (hn₁ h).elim
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨by simp, hf₀⟩
            · exact ⟨by simp, hf₂⟩
        rw [hset]
        change (insert d ({f (f d)} : Finset D)).card = 2
        rw [Finset.card_insert_of_notMem (by
          intro h
          have heq : d = f (f d) := by simpa only [Finset.mem_singleton] using h
          exact hffd heq.symm)]
        simp
      · have hset : ({d, f d, f (f d)} : Finset D).filter
            (faceSwitchCorner B) = {d, f d} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, h⟩
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact (hn₂ h).elim
          · rintro (rfl | rfl)
            · exact ⟨by simp, hf₀⟩
            · exact ⟨by simp, hf₁⟩
        rw [hset]
        change (insert d ({f d} : Finset D)).card = 2
        rw [Finset.card_insert_of_notMem (by
          intro h
          have heq : d = f d := by simpa only [Finset.mem_singleton] using h
          exact hfd heq.symm)]
        simp

private theorem innerCorner_total_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (P : D → Prop) (k : ℕ)
    (hfiber : ∀ (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
      (_hq : q ≠ Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer),
      Nat.card {d : faceDartFiber B q // P d.1} = k) :
    Nat.card {d : D // ¬ B.map.IsOuter d ∧ P d} = k * B.map.numInnerFaces := by
  classical
  let outerQ : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap :=
    Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer
  let T := {d : D // ¬ B.map.IsOuter d ∧ P d}
  let faceOf : T → CombinatorialMap.FaceQuotient B.map.toCombinatorialMap :=
    fun d => Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d.1
  let fiber := fun q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap =>
    {x : T // faceOf x = q}
  let fiberFintype : ∀ q, Fintype (fiber q) := fun q =>
    Fintype.subtype
      (Finset.univ.filter (fun x : T => faceOf x = q))
      (by intro x; simp)
  let sigmaFintype : Fintype (Σ q, fiber q) :=
    @Sigma.instFintype _ fiber fiberFintype inferInstance
  let e : (Σ q, fiber q) ≃ T := Equiv.sigmaFiberEquiv faceOf
  have hpartition : Nat.card T = ∑ q, Nat.card (fiber q) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card T = @Fintype.card (Σ q, fiber q) sigmaFintype :=
        Fintype.card_congr e.symm
      _ = ∑ q, @Fintype.card (fiber q) (fiberFintype q) :=
        @Fintype.card_sigma _ fiber inferInstance fiberFintype
      _ = ∑ q, Nat.card (fiber q) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact (@Nat.card_eq_fintype_card (fiber q) (fiberFintype q)).symm
  have hEmpty : IsEmpty (fiber outerQ) := ⟨fun x => by
    have houter : B.map.IsOuter x.1.1 := by
      change B.map.toCombinatorialMap.faceSucc.SameCycle B.map.outer x.1.1
      exact (Quotient.exact x.2).symm
    exact x.1.2.1 houter⟩
  have hcard : ∀ q, Nat.card (fiber q) = if q = outerQ then 0 else k := by
    intro q
    by_cases hq : q = outerQ
    · subst q
      have hzero : Nat.card (fiber outerQ) = 0 :=
        @Nat.card_of_isEmpty (fiber outerQ) hEmpty
      rw [hzero]
      simp
    · have fiberEquiv : fiber q ≃ {d : faceDartFiber B q // P d.1} := {
        toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2.2⟩
        invFun := fun y => by
          have hinner : ¬ B.map.IsOuter y.1.1 := by
            intro hout
            apply hq
            calc
              q = Quotient.mk
                  (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc)
                  y.1.1 := y.1.2.symm
              _ = outerQ := (Quotient.sound hout).symm
          exact ⟨⟨y.1.1, ⟨hinner, y.2⟩⟩, y.1.2⟩
        left_inv x := by
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv y := by
          apply Subtype.ext
          apply Subtype.ext
          rfl }
      rw [Nat.card_congr fiberEquiv, hfiber q hq]
      simp [hq]
  have hnum : (Finset.univ.erase outerQ).card = B.map.numInnerFaces := by
    calc
      (Finset.univ.erase outerQ).card =
          Fintype.card (CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) - 1 := by
        simp
      _ = B.map.numInnerFaces := rfl
  have hsum : (∑ q, Nat.card (fiber q)) = k * B.map.numInnerFaces := by
    calc
      (∑ q, Nat.card (fiber q)) =
          ∑ q, if q = outerQ then 0 else k := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hcard q
      _ = (if outerQ = outerQ then 0 else k) +
          ∑ q ∈ Finset.univ.erase outerQ, if q = outerQ then 0 else k := by
        rw [← Finset.sum_erase_add (a := outerQ) Finset.univ
          (fun q => if q = outerQ then 0 else k) (Finset.mem_univ outerQ)]
        exact add_comm _ _
      _ = 0 + ∑ q ∈ Finset.univ.erase outerQ, k := by
        congr 1
        · simp
        · apply Finset.sum_congr rfl
          intro q hq
          simp [Finset.mem_erase.mp hq |>.1]
      _ = k * B.map.numInnerFaces := by
        rw [Finset.sum_const_nat (fun q hq => rfl), hnum, Nat.mul_comm]
        simp
  calc
    Nat.card {d : D // ¬ B.map.IsOuter d ∧ P d} = ∑ q, Nat.card (fiber q) := hpartition
    _ = k * B.map.numInnerFaces := hsum

/-- The number of inner vertex-switch corners equals the number of inner
faces. Helper toward `lem-lr-ind`; not the paper result
the checked-in source). -/
theorem innerVertexSwitch_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // ¬ B.map.IsOuter d ∧ vertexSwitchCorner B d} =
      B.map.numInnerFaces := by
  have h := innerCorner_total_card B (vertexSwitchCorner B) 1
    (by
      intro q hq
      exact innerFace_vertexSwitchFiber_card B q hq)
  simpa using h

/-- The number of inner face-switch corners is twice the number of inner
faces. Helper toward `lem-lr-ind`; not the paper result
the checked-in source). -/
theorem innerFaceSwitch_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // ¬ B.map.IsOuter d ∧ faceSwitchCorner B d} =
      2 * B.map.numInnerFaces := by
  exact innerCorner_total_card B (faceSwitchCorner B) 2
    (by
      intro q hq
      exact innerFace_faceSwitchFiber_card B q hq)

end DirectedDistances.PlanarMap
