/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryData

/-! # Incidence along the outer face

The face permutation follows darts with the incident face on their left:
`faceSucc d = rot⁻¹ (edgeInv d)`. Since vertices are rotation orbits, the
head of a dart is the tail vertex of its face successor. This supplies the
incidence facts needed to read finite outer-face boundary blocks as walks -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- With the face on the left as the outer-face order convention, the head of
a dart is the tail vertex of the next dart along the face. Vertices are
rotation orbits and `faceSucc d = rot⁻¹ (edgeInv d)`
Definition 3.2. -/
theorem dartHeadVertex_eq_tailVertex_faceSucc
    (M : DirectedMapWithMissing D) (d : D) :
    dartHeadVertex M d =
      dartTailVertex M (M.toCombinatorialMap.faceSucc d) := by
  apply Quotient.sound
  refine ⟨-1, ?_⟩
  simp [CombinatorialMap.faceSucc]

/-- An exact outer-face word has consecutive darts incident in its listed
order, with the external face on their left (`defn:bound-edges`, -/
theorem isOuterCycle_next_dart_incident
    (M : DirectedMapWithMissing D) (B : NonemptyWord D)
    (hB : IsOuterCycle M B) (d : D) (hd : d ∈ B.letters) :
    dartHeadVertex M d =
      dartTailVertex M (B.letters.formPerm d) := by
  calc
    dartHeadVertex M d =
        dartTailVertex M (M.toCombinatorialMap.faceSucc d) :=
      dartHeadVertex_eq_tailVertex_faceSucc M d
    _ = dartTailVertex M (B.letters.formPerm d) := by
      rw [hB.2.2 d hd]

/-- A contiguous block of length `k` in a rotation of an exact outer-face
word has incident consecutive darts. `L` is the prefix of that rotation;
the bound `k ≤ B.letters.length` makes it a genuine block of the finite word
Definition 3.2. -/
theorem outerCycle_rotate_take_consecutive_incident
    (M : DirectedMapWithMissing D) (B : NonemptyWord D)
    (hB : IsOuterCycle M B) (n k : ℕ) (L : List D)
    (hL : L = (B.letters.rotate n).take k)
    (hklen : k ≤ B.letters.length) (i : ℕ) (hi : i + 1 < k) :
    dartHeadVertex M
        (L[i]'(by simp only [hL, List.length_take, List.length_rotate]; omega)) =
      dartTailVertex M
        (L[i + 1]'(by simp only [hL, List.length_take, List.length_rotate]; omega)) := by
  let R := B.letters.rotate n
  have hRlen : R.length = B.letters.length := by simp [R]
  have hRnodup : R.Nodup := by simpa [R] using B.nodup
  have hRform : R.formPerm = B.letters.formPerm := by
    exact List.formPerm_rotate B.letters B.nodup n
  have hi0 : i < R.length := by rw [hRlen]; omega
  have hi1 : i + 1 < R.length := by rw [hRlen]; omega
  let d₀ : D := L[i]'(by
    simp only [hL, List.length_take, List.length_rotate]
    omega)
  let d₁ : D := L[i + 1]'(by
    simp only [hL, List.length_take, List.length_rotate]
    omega)
  have hd₀ : d₀ = R[i] := by
    simp [d₀, R, hL]
  have hd₁ : d₁ = R[i + 1] := by
    simp [d₁, R, hL]
  have hmemR : R[i] ∈ B.letters := by
    have hmem : R[i] ∈ R := List.mem_of_getElem rfl
    exact List.mem_rotate.mp hmem
  have hstep : R.formPerm R[i] = R[i + 1] :=
    List.formPerm_apply_lt_getElem R hRnodup i hi1
  have hinc := isOuterCycle_next_dart_incident M B hB R[i] hmemR
  rw [← hRform, hstep] at hinc
  change dartHeadVertex M d₀ = dartTailVertex M d₁
  calc
    dartHeadVertex M d₀ = dartHeadVertex M R[i] := by rw [hd₀]
    _ = dartTailVertex M R[i + 1] := hinc
    _ = dartTailVertex M d₁ := by rw [← hd₁]

/-- If every dart in a nonempty contiguous outer-face block is present and
tail-oriented, its list order is a directed dart-walk chain from the tail
vertex of its first dart to the head vertex of its last dart. The conclusion
records the oriented-edge and consecutive-incidence clauses without a
vertex-distinctness condition (`defn:bound-edges`, -/
theorem outerCycle_rotate_take_isDirectedDartWalk
    (M : DirectedMapWithMissing D) (B : NonemptyWord D)
    (hB : IsOuterCycle M B) (n k : ℕ) (L : List D)
    (hL : L = (B.letters.rotate n).take k)
    (hk : 0 < k) (hklen : k ≤ B.letters.length)
    (hdir : ∀ i, (hi : i < k) →
      ¬ M.missing (L[i]'(by
        simp only [hL, List.length_take, List.length_rotate]
        omega)) ∧
      M.tail (L[i]'(by
        simp only [hL, List.length_take, List.length_rotate]
        omega))) :
    L.length = k ∧ 0 < L.length ∧
      (∀ i, (hi : i < k) →
        ¬ M.missing (L[i]'(by
          simp only [hL, List.length_take, List.length_rotate]
          omega)) ∧
        M.tail (L[i]'(by
          simp only [hL, List.length_take, List.length_rotate]
          omega))) ∧
      (∀ i, (hi : i + 1 < k) →
        dartHeadVertex M
            (L[i]'(by
              simp only [hL, List.length_take, List.length_rotate]
              omega)) =
          dartTailVertex M
            (L[i + 1]'(by
              simp only [hL, List.length_take, List.length_rotate]
              omega))) := by
  have hlen : L.length = k := by
    rw [hL, List.length_take, List.length_rotate, Nat.min_eq_left hklen]
  refine ⟨hlen, ?_, hdir, ?_⟩
  · omega
  · intro i hi
    exact outerCycle_rotate_take_consecutive_incident
      M B hB n k L hL hklen i hi

end DirectedDistances.PlanarMap
