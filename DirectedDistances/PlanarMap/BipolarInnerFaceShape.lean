/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarInnerSwitch
public import DirectedDistances.PlanarMap.FiniteBipolarIncomingBlock

/-! Local shape helpers for inner triangular faces, toward the inverse direction
the paper results. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The two orientations in which an inner face can meet its directed long
edge. The constructors are fixed by the `faceSucc` cycle equations in
`InnerFaceShape`; `left` means the face cycle traverses the long dart in its
directed orientation. -/
inductive InnerFaceSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- A directed transitive triangle together with the cyclic order of its face
darts. The `left` case traverses the directed long edge first; the `right`
case traverses its reverse first. Helper toward the inverse direction of
`thm-kmsw` and `lem-lr-ind`; not the paper results -/
structure InnerFaceShape
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) where
  source : MapVertex B.map
  middle : MapVertex B.map
  sink : MapVertex B.map
  longDart : D
  firstShortDart : D
  secondShortDart : D
  source_ne_middle : source ≠ middle
  middle_ne_sink : middle ≠ sink
  source_ne_sink : source ≠ sink
  long_orientation : B.map.tail longDart ∧
    dartTailVertex B.map longDart = source ∧
    dartHeadVertex B.map longDart = sink
  firstShort_orientation : B.map.tail firstShortDart ∧
    dartTailVertex B.map firstShortDart = source ∧
    dartHeadVertex B.map firstShortDart = middle
  secondShort_orientation : B.map.tail secondShortDart ∧
    dartTailVertex B.map secondShortDart = middle ∧
    dartHeadVertex B.map secondShortDart = sink
  side : InnerFaceSide
  face : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap
  left_face_quotient : side = .left →
    face = Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) longDart
  right_face_quotient : side = .right →
    face = Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc)
        (B.map.toCombinatorialMap.edgeInv longDart)
  left_faceSucc_order : side = .left →
    B.map.toCombinatorialMap.faceSucc longDart =
        B.map.toCombinatorialMap.edgeInv secondShortDart ∧
      B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.edgeInv secondShortDart) =
        B.map.toCombinatorialMap.edgeInv firstShortDart ∧
      B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.edgeInv firstShortDart) = longDart
  right_faceSucc_order : side = .right →
    B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv longDart) = firstShortDart ∧
      B.map.toCombinatorialMap.faceSucc firstShortDart = secondShortDart ∧
      B.map.toCombinatorialMap.faceSucc secondShortDart =
        B.map.toCombinatorialMap.edgeInv longDart

private theorem bipolar_no_loop
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map d ≠ dartHeadVertex B.map d := by
  intro heq
  by_cases htail : B.map.tail d
  · have hstep : B.map.directedStep
        (dartTailVertex B.map d) (dartHeadVertex B.map d) := by
      refine ⟨d, B.noMissingDarts d, htail, rfl, rfl⟩
    apply B.acyclic (dartTailVertex B.map d)
    exact Relation.TransGen.single (heq ▸ hstep)
  · have hinvTail : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
      by_contra h
      exact htail ((B.map.tail_iff d (B.noMissingDarts d)).2 h)
    have hstep : B.map.directedStep
        (dartHeadVertex B.map d) (dartTailVertex B.map d) := by
      refine ⟨B.map.toCombinatorialMap.edgeInv d, ?_, hinvTail, ?_, ?_⟩
      · intro hmiss
        exact B.noMissingDarts d ((B.map.missing_edgeInv d).mpr hmiss)
      · rfl
      · simp [dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol]
    apply B.acyclic (dartTailVertex B.map d)
    exact Relation.TransGen.single (heq ▸ hstep)

private theorem tail_edgeInv_of_not_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hntail : ¬ B.map.tail d) :
    B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
  by_contra h
  exact hntail ((B.map.tail_iff d (B.noMissingDarts d)).2 h)

private theorem edgeInv_endpoints
    (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.toCombinatorialMap.edgeInv d) =
        dartHeadVertex M d ∧
      dartHeadVertex M (M.toCombinatorialMap.edgeInv d) =
        dartTailVertex M d := by
  constructor
  · rfl
  · simp [dartHeadVertex, dartTailVertex, M.toCombinatorialMap.edgeInv_invol]

private theorem faceSucc_quotient_succ
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d =
      Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc)
          (B.map.toCombinatorialMap.faceSucc d) := by
  apply Quotient.sound
  change B.map.toCombinatorialMap.faceSucc.SameCycle d
    (B.map.toCombinatorialMap.faceSucc d)
  exact ⟨1, by simp⟩

private theorem faceSucc_quotient_succ_two
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d =
      Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc)
          (B.map.toCombinatorialMap.faceSucc
            (B.map.toCombinatorialMap.faceSucc d)) := by
  apply Quotient.sound
  change B.map.toCombinatorialMap.faceSucc.SameCycle d
    (B.map.toCombinatorialMap.faceSucc
      (B.map.toCombinatorialMap.faceSucc d))
  exact ⟨2, by rw [zpow_two, Equiv.Perm.mul_apply]⟩

private theorem rot_next_of_faceSucc_eq
    (M : CombinatorialMap D) {x y : D} (h : M.faceSucc x = y) :
    M.rot y = M.edgeInv x := by
  have h' : M.rot.symm (M.edgeInv x) = y := by
    simpa [CombinatorialMap.faceSucc] using h
  have hrot := congrArg M.rot h'
  have hrot' : M.edgeInv x = M.rot y := by simpa using hrot
  exact hrot'.symm

/-- The face orbit of an inner dart consists of the three listed darts, in
`faceSucc` order, and these darts are pairwise distinct. Helper toward the
inverse direction of `thm-kmsw` and `lem-lr-ind`; not the paper results -/
theorem innerFace_dart_orbit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    let f := B.map.toCombinatorialMap.faceSucc
    f (f (f d)) = d ∧ f d ≠ d ∧ f (f d) ≠ d ∧ f d ≠ f (f d) := by
  dsimp
  obtain ⟨hcycle, h₁, h₂⟩ := B.innerFacesDegreeThree d hinner
  refine ⟨hcycle, h₁, h₂, ?_⟩
  intro h
  apply h₁
  exact B.map.toCombinatorialMap.faceSucc.injective h.symm

/-- The three corner vertices around an inner triangular face are pairwise
distinct. A repeated adjacent vertex would make one of the three darts a
loop, which contradicts bipolar acyclicity. Helper toward the inverse
direction of `thm-kmsw` and `lem-lr-ind`; not the paper results -/
theorem innerFace_vertices_pairwiseDistinct
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    dartTailVertex B.map d ≠
        dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d) ∧
      dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d) ≠
        dartTailVertex B.map
          (B.map.toCombinatorialMap.faceSucc
            (B.map.toCombinatorialMap.faceSucc d)) ∧
      dartTailVertex B.map
          (B.map.toCombinatorialMap.faceSucc
            (B.map.toCombinatorialMap.faceSucc d)) ≠
        dartTailVertex B.map d := by
  let f := B.map.toCombinatorialMap.faceSucc
  have hcycle := (B.innerFacesDegreeThree d hinner).1
  have hv01 : dartTailVertex B.map (f d) = dartHeadVertex B.map d :=
    (corner_consecutiveDarts B d).2.2
  have hv12 : dartTailVertex B.map (f (f d)) = dartHeadVertex B.map (f d) :=
    (corner_consecutiveDarts B (f d)).2.2
  have hv20 : dartTailVertex B.map d =
      dartHeadVertex B.map (f (f d)) := by
    calc
      dartTailVertex B.map d = dartTailVertex B.map (f (f (f d))) :=
        congrArg (dartTailVertex B.map) hcycle.symm
      _ = dartHeadVertex B.map (f (f d)) :=
        (corner_consecutiveDarts B (f (f d))).2.2
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact bipolar_no_loop B d (h.trans hv01)
  · intro h
    exact bipolar_no_loop B (f d) (h.trans hv12)
  · intro h
    exact bipolar_no_loop B (f (f d)) (h.trans hv20)

private theorem innerFace_tail_patterns
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    (B.map.tail d ∧ B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∧
        ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
      (B.map.tail d ∧ ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∧
        B.map.tail (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
      (¬ B.map.tail d ∧ B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∧
        B.map.tail (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
      (B.map.tail d ∧ ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∧
        ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
      (¬ B.map.tail d ∧ B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∧
        ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
      (¬ B.map.tail d ∧ ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∧
        B.map.tail (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) := by
  have horient := innerFace_has_both_boundary_orientations B d hinner
  tauto

/-- Every inner triangular face admits a transitive orientation shape. The
three vertices are its source, middle vertex, and sink; the long dart and
the two short darts retain their actual directed orientations. The `side`
field records the exact `faceSucc` order. Helper toward the inverse direction
of `thm-kmsw` and `lem-lr-ind`; not the paper results -/
theorem innerFaceShape_exists
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    ∃ S : InnerFaceShape B,
      S.face = Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d := by
  let f := B.map.toCombinatorialMap.faceSucc
  let v0 := dartTailVertex B.map d
  let v1 := dartTailVertex B.map (f d)
  let v2 := dartTailVertex B.map (f (f d))
  have hcycle := (B.innerFacesDegreeThree d hinner).1
  have hhead0 : dartHeadVertex B.map d = v1 :=
    (corner_consecutiveDarts B d).2.2.symm
  have hhead1 : dartHeadVertex B.map (f d) = v2 :=
    (corner_consecutiveDarts B (f d)).2.2.symm
  have hhead2 : dartHeadVertex B.map (f (f d)) = v0 := by
    calc
      dartHeadVertex B.map (f (f d)) =
          dartTailVertex B.map (f (f (f d))) :=
        (corner_consecutiveDarts B (f (f d))).2.2.symm
      _ = v0 := congrArg (dartTailVertex B.map) hcycle
  have hverts := innerFace_vertices_pairwiseDistinct B d hinner
  have hinv0 := edgeInv_endpoints B.map d
  have hinv1 := edgeInv_endpoints B.map (f d)
  have hinv2 := edgeInv_endpoints B.map (f (f d))
  have hinv0tail : dartTailVertex B.map
      (B.map.toCombinatorialMap.edgeInv d) = v1 := hinv0.1.trans hhead0
  have hinv0head : dartHeadVertex B.map
      (B.map.toCombinatorialMap.edgeInv d) = v0 := hinv0.2
  have hinv1tail : dartTailVertex B.map
      (B.map.toCombinatorialMap.edgeInv (f d)) = v2 := hinv1.1.trans hhead1
  have hinv1head : dartHeadVertex B.map
      (B.map.toCombinatorialMap.edgeInv (f d)) = v1 := hinv1.2
  have hinv2tail : dartTailVertex B.map
      (B.map.toCombinatorialMap.edgeInv (f (f d))) = v0 := hinv2.1.trans hhead2
  have hinv2head : dartHeadVertex B.map
      (B.map.toCombinatorialMap.edgeInv (f (f d))) = v2 := hinv2.2
  rcases innerFace_tail_patterns B d hinner with h | h | h | h | h | h
  · rcases h with ⟨h0, h1, h2⟩
    refine ⟨{
      source := v0
      middle := v1
      sink := v2
      longDart := B.map.toCombinatorialMap.edgeInv (f (f d))
      firstShortDart := d
      secondShortDart := f d
      source_ne_middle := hverts.1
      middle_ne_sink := hverts.2.1
      source_ne_sink := hverts.2.2.symm
      long_orientation := ⟨tail_edgeInv_of_not_tail B (f (f d)) h2,
        hinv2tail, hinv2head⟩
      firstShort_orientation := ⟨h0, rfl, hhead0⟩
      secondShort_orientation := ⟨h1, rfl, hhead1⟩
      side := .right
      face := Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d
      left_face_quotient := by intro hs; cases hs
      right_face_quotient := by
        intro _
        rw [B.map.toCombinatorialMap.edgeInv_invol]
        exact faceSucc_quotient_succ_two B d
      left_faceSucc_order := by intro hs; cases hs
      right_faceSucc_order := by
        intro _
        refine ⟨?_, rfl, ?_⟩
        · simpa [f, B.map.toCombinatorialMap.edgeInv_invol] using hcycle
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
    }, rfl⟩
  · rcases h with ⟨h0, h1, h2⟩
    refine ⟨{
      source := v2
      middle := v0
      sink := v1
      longDart := B.map.toCombinatorialMap.edgeInv (f d)
      firstShortDart := f (f d)
      secondShortDart := d
      source_ne_middle := hverts.2.2
      middle_ne_sink := hverts.1
      source_ne_sink := hverts.2.1.symm
      long_orientation := ⟨tail_edgeInv_of_not_tail B (f d) h1,
        hinv1tail, hinv1head⟩
      firstShort_orientation := ⟨h2, rfl, hhead2⟩
      secondShort_orientation := ⟨h0, rfl, hhead0⟩
      side := .right
      face := Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d
      left_face_quotient := by intro hs; cases hs
      right_face_quotient := by
        intro _
        rw [B.map.toCombinatorialMap.edgeInv_invol]
        exact faceSucc_quotient_succ B d
      left_faceSucc_order := by intro hs; cases hs
      right_faceSucc_order := by
        intro _
        refine ⟨?_, ?_, ?_⟩
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
        · simpa [f] using hcycle
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
    }, rfl⟩
  · rcases h with ⟨h0, h1, h2⟩
    refine ⟨{
      source := v1
      middle := v2
      sink := v0
      longDart := B.map.toCombinatorialMap.edgeInv d
      firstShortDart := f d
      secondShortDart := f (f d)
      source_ne_middle := hverts.2.1
      middle_ne_sink := hverts.2.2
      source_ne_sink := hverts.1.symm
      long_orientation := ⟨tail_edgeInv_of_not_tail B d h0,
        hinv0tail, hinv0head⟩
      firstShort_orientation := ⟨h1, rfl, hhead1⟩
      secondShort_orientation := ⟨h2, rfl, hhead2⟩
      side := .right
      face := Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d
      left_face_quotient := by intro hs; cases hs
      right_face_quotient := by
        intro _
        rw [B.map.toCombinatorialMap.edgeInv_invol]
      left_faceSucc_order := by intro hs; cases hs
      right_faceSucc_order := by
        intro _
        refine ⟨?_, ?_, ?_⟩
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
        · simp [f]
        · simpa [f, B.map.toCombinatorialMap.edgeInv_invol] using hcycle
    }, rfl⟩
  · rcases h with ⟨h0, h1, h2⟩
    refine ⟨{
      source := v0
      middle := v2
      sink := v1
      longDart := d
      firstShortDart := B.map.toCombinatorialMap.edgeInv (f (f d))
      secondShortDart := B.map.toCombinatorialMap.edgeInv (f d)
      source_ne_middle := hverts.2.2.symm
      middle_ne_sink := hverts.2.1.symm
      source_ne_sink := hverts.1
      long_orientation := ⟨h0, rfl, hhead0⟩
      firstShort_orientation := ⟨tail_edgeInv_of_not_tail B (f (f d)) h2,
        hinv2tail, hinv2head⟩
      secondShort_orientation := ⟨tail_edgeInv_of_not_tail B (f d) h1,
        hinv1tail, hinv1head⟩
      side := .left
      face := Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d
      left_face_quotient := by intro _; rfl
      right_face_quotient := by intro hs; cases hs
      left_faceSucc_order := by
        intro _
        refine ⟨?_, ?_, ?_⟩
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
        · simpa [f, B.map.toCombinatorialMap.edgeInv_invol] using hcycle
      right_faceSucc_order := by intro hs; cases hs
    }, rfl⟩

  · rcases h with ⟨h0, h1, h2⟩
    refine ⟨{
      source := v1
      middle := v0
      sink := v2
      longDart := f d
      firstShortDart := B.map.toCombinatorialMap.edgeInv d
      secondShortDart := B.map.toCombinatorialMap.edgeInv (f (f d))
      source_ne_middle := hverts.1.symm
      middle_ne_sink := hverts.2.2.symm
      source_ne_sink := hverts.2.1
      long_orientation := ⟨h1, rfl, hhead1⟩
      firstShort_orientation := ⟨tail_edgeInv_of_not_tail B d h0,
        hinv0tail, hinv0head⟩
      secondShort_orientation := ⟨tail_edgeInv_of_not_tail B (f (f d)) h2,
        hinv2tail, hinv2head⟩
      side := .left
      face := Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d
      left_face_quotient := by intro _; exact faceSucc_quotient_succ B d
      right_face_quotient := by intro hs; cases hs
      left_faceSucc_order := by
        intro _
        refine ⟨?_, ?_, ?_⟩
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
        · simpa [f, B.map.toCombinatorialMap.edgeInv_invol] using hcycle
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
      right_faceSucc_order := by intro hs; cases hs
    }, rfl⟩
  · rcases h with ⟨h0, h1, h2⟩
    refine ⟨{
      source := v2
      middle := v1
      sink := v0
      longDart := f (f d)
      firstShortDart := B.map.toCombinatorialMap.edgeInv (f d)
      secondShortDart := B.map.toCombinatorialMap.edgeInv d
      source_ne_middle := hverts.2.1.symm
      middle_ne_sink := hverts.1.symm
      source_ne_sink := hverts.2.2
      long_orientation := ⟨h2, rfl, hhead2⟩
      firstShort_orientation := ⟨tail_edgeInv_of_not_tail B (f d) h1,
        hinv1tail, hinv1head⟩
      secondShort_orientation := ⟨tail_edgeInv_of_not_tail B d h0,
        hinv0tail, hinv0head⟩
      side := .left
      face := Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d
      left_face_quotient := by intro _; exact faceSucc_quotient_succ_two B d
      right_face_quotient := by intro hs; cases hs
      left_faceSucc_order := by
        intro _
        refine ⟨?_, ?_, ?_⟩
        · simpa [f, B.map.toCombinatorialMap.edgeInv_invol] using hcycle
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
        · simp [f, B.map.toCombinatorialMap.edgeInv_invol]
      right_faceSucc_order := by intro hs; cases hs
    }, rfl⟩

/-- Every non-outer face quotient has a transitive `InnerFaceShape` anchored
to that quotient. Helper toward the inverse direction of `thm-kmsw` and
`lem-lr-ind`; not the paper results -/
theorem innerFaceShape_face_nonempty
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    Nonempty {S : InnerFaceShape B // S.face = q} := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  have hinner : ¬ B.map.IsOuter d := by
    intro hd
    apply hq
    apply Quotient.sound
    exact hd.symm
  obtain ⟨S, hS⟩ := innerFaceShape_exists B d hinner
  exact ⟨⟨S, hS⟩⟩

/-- Select the transitive shape of a non-outer face quotient. Helper toward
the inverse direction of `thm-kmsw`; not the paper result -/
noncomputable def innerFaceShapeOfFace
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    InnerFaceShape B :=
  (Classical.choice (innerFaceShape_face_nonempty B q hq)).1

/-- The selected shape is anchored to its face quotient. -/
theorem innerFaceShapeOfFace_face
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    (innerFaceShapeOfFace B q hq).face = q :=
  (Classical.choice (innerFaceShape_face_nonempty B q hq)).2

/-- The source vertex selected for an inner face quotient. Helper toward the
inverse direction of `thm-kmsw`; not the paper result -/
@[expose] noncomputable def innerFaceSource
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    MapVertex B.map :=
  (innerFaceShapeOfFace B q hq).source

/-- The middle vertex selected for an inner face quotient. Helper toward the
inverse direction of `thm-kmsw`; not the paper result -/
@[expose] noncomputable def innerFaceMiddle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    MapVertex B.map :=
  (innerFaceShapeOfFace B q hq).middle

/-- The sink vertex selected for an inner face quotient. Helper toward the
inverse direction of `thm-kmsw`; not the paper result -/
@[expose] noncomputable def innerFaceSink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer) :
    MapVertex B.map :=
  (innerFaceShapeOfFace B q hq).sink

/-- The three incident pairs of directed edges are consecutive in the vertex
rotations. The order is determined by the face side. Helper toward the
inverse direction of `thm-kmsw` and `lem-lr-ind`; not the paper results -/
theorem innerFaceShape_rotation_consecutive
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S : InnerFaceShape B) :
    (S.side = .left →
      B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.edgeInv S.secondShortDart) =
        B.map.toCombinatorialMap.edgeInv S.longDart ∧
      B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.edgeInv S.firstShortDart) =
        S.secondShortDart ∧
      B.map.toCombinatorialMap.rot S.longDart = S.firstShortDart) ∧
    (S.side = .right →
      B.map.toCombinatorialMap.rot S.firstShortDart = S.longDart ∧
      B.map.toCombinatorialMap.rot S.secondShortDart =
        B.map.toCombinatorialMap.edgeInv S.firstShortDart ∧
      B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.edgeInv S.longDart) =
        B.map.toCombinatorialMap.edgeInv S.secondShortDart) := by
  constructor
  · intro hside
    obtain ⟨h₀, h₁, h₂⟩ := S.left_faceSucc_order hside
    refine ⟨rot_next_of_faceSucc_eq B.map.toCombinatorialMap h₀, ?_, ?_⟩
    · simpa [B.map.toCombinatorialMap.edgeInv_invol] using
        rot_next_of_faceSucc_eq B.map.toCombinatorialMap h₁
    · simpa [B.map.toCombinatorialMap.edgeInv_invol] using
        rot_next_of_faceSucc_eq B.map.toCombinatorialMap h₂
  · intro hside
    obtain ⟨h₀, h₁, h₂⟩ := S.right_faceSucc_order hside
    refine ⟨?_, rot_next_of_faceSucc_eq B.map.toCombinatorialMap h₁, ?_⟩
    · simpa [B.map.toCombinatorialMap.edgeInv_invol] using
        rot_next_of_faceSucc_eq B.map.toCombinatorialMap h₀
    · simpa [B.map.toCombinatorialMap.edgeInv_invol] using
        rot_next_of_faceSucc_eq B.map.toCombinatorialMap h₂

/-- The side fixes the `tail` pattern of the three face darts and places the
unique vertex-switch corner at the middle vertex. In the `left` case the
long dart is traversed forward, followed by the two reverse short darts; in
the `right` case the reverse long dart is followed by the two forward short
darts. Helper toward the inverse direction of `thm-kmsw` and `lem-lr-ind`; -/
theorem innerFaceShape_side_and_middle_switch
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S : InnerFaceShape B) :
    (S.side = .left →
      B.map.tail S.longDart ∧
      ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv S.secondShortDart) ∧
      ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv S.firstShortDart) ∧
      vertexSwitchCorner B
        (B.map.toCombinatorialMap.edgeInv S.secondShortDart) ∧
      ¬ vertexSwitchCorner B S.longDart ∧
      ¬ vertexSwitchCorner B
        (B.map.toCombinatorialMap.edgeInv S.firstShortDart)) ∧
    (S.side = .right →
      ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv S.longDart) ∧
      B.map.tail S.firstShortDart ∧
      B.map.tail S.secondShortDart ∧
      vertexSwitchCorner B S.firstShortDart ∧
      ¬ vertexSwitchCorner B
        (B.map.toCombinatorialMap.edgeInv S.longDart) ∧
      ¬ vertexSwitchCorner B S.secondShortDart) := by
  constructor
  · intro hside
    obtain ⟨h₀, h₁, h₂⟩ := S.left_faceSucc_order hside
    have hfirstNot : ¬ B.map.tail
        (B.map.toCombinatorialMap.edgeInv S.firstShortDart) :=
      (B.map.tail_iff S.firstShortDart
        (B.noMissingDarts S.firstShortDart)).mp S.firstShort_orientation.1
    have hsecondNot : ¬ B.map.tail
        (B.map.toCombinatorialMap.edgeInv S.secondShortDart) :=
      (B.map.tail_iff S.secondShortDart
        (B.noMissingDarts S.secondShortDart)).mp S.secondShort_orientation.1
    refine ⟨S.long_orientation.1, hsecondNot, hfirstNot, ?_, ?_, ?_⟩
    · simp [vertexSwitchCorner, h₁, hfirstNot, hsecondNot]
    · simp [vertexSwitchCorner, h₀, hsecondNot, S.long_orientation.1]
    · simp [vertexSwitchCorner, h₂, hfirstNot, S.long_orientation.1]
  · intro hside
    obtain ⟨h₀, h₁, h₂⟩ := S.right_faceSucc_order hside
    have hlongNot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv S.longDart) :=
      (B.map.tail_iff S.longDart (B.noMissingDarts S.longDart)).mp
        S.long_orientation.1
    refine ⟨hlongNot, S.firstShort_orientation.1,
      S.secondShort_orientation.1, ?_, ?_, ?_⟩
    · simp [vertexSwitchCorner, h₁, S.firstShort_orientation.1,
        S.secondShort_orientation.1]
    · simp [vertexSwitchCorner, h₀, hlongNot,
        S.firstShort_orientation.1]
    · simp [vertexSwitchCorner, h₂, S.secondShort_orientation.1,
        hlongNot]

omit [Fintype D] [DecidableEq D] in
private theorem faceCycle_mem_three
    (f : Equiv.Perm D) (a b c : D)
    (hab : f a = b) (hbc : f b = c) (hca : f c = a)
    (x : D) (hax : f.SameCycle a x) :
    x = a ∨ x = b ∨ x = c := by
  let s : Set D := {a, b, c}
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact Or.inr (Or.inl hab)
    · exact Or.inr (Or.inr hbc)
    · exact Or.inl hca
  have hinj : Set.InjOn f s := fun _ _ _ _ h => f.injective h
  have hsurj : Set.SurjOn f s s := by
    intro y hy
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hya | hyb | hyc
    · exact ⟨c, by simp [s], hca.trans hya.symm⟩
    · exact ⟨a, by simp [s], hab.trans hyb.symm⟩
    · exact ⟨b, by simp [s], hbc.trans hyc.symm⟩
  have hroot : ∀ ⦃y⦄, y ∈ s → f.SameCycle a y := by
    intro y hy
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hya | hyb | hyc
    · subst y
      exact ⟨0, rfl⟩
    · subst y
      exact ⟨1, by simpa using hab⟩
    · subst y
      exact ⟨2, by rw [zpow_two, Equiv.Perm.mul_apply, hab, hbc]⟩
  have hcycle : f.IsCycleOn s := by
    refine ⟨⟨hmaps, hinj, hsurj⟩, ?_⟩
    intro y hy z hz
    exact (hroot hy).symm.trans (hroot hz)
  have hxmem : x ∈ s := by
    rw [← hcycle.range_zpow (a := a) (by simp [s])]
    rcases hax with ⟨i, hi⟩
    exact ⟨i, hi⟩
  simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
  exact hxmem

private theorem innerFaceShape_faceOrbit_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S : InnerFaceShape B) (d : D)
    (hd : S.face = Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) d) :
    d = (if S.side = .left then S.longDart
      else B.map.toCombinatorialMap.edgeInv S.longDart) ∨
    d = B.map.toCombinatorialMap.faceSucc
      (if S.side = .left then S.longDart
       else B.map.toCombinatorialMap.edgeInv S.longDart) ∨
    d = B.map.toCombinatorialMap.faceSucc
      (B.map.toCombinatorialMap.faceSucc
        (if S.side = .left then S.longDart
         else B.map.toCombinatorialMap.edgeInv S.longDart)) := by
  let f := B.map.toCombinatorialMap.faceSucc
  cases hside : S.side with
  | left =>
      have hquot := S.left_face_quotient hside
      have hsame : f.SameCycle S.longDart d := by
        change (Equiv.Perm.SameCycle.setoid f).r S.longDart d
        exact Quotient.exact (hquot.symm.trans hd)
      obtain ⟨h₀, h₁, h₂⟩ := S.left_faceSucc_order hside
      simpa [hside, f, h₀, h₁, h₂] using faceCycle_mem_three f S.longDart
        (B.map.toCombinatorialMap.edgeInv S.secondShortDart)
        (B.map.toCombinatorialMap.edgeInv S.firstShortDart)
        h₀ h₁ h₂ d hsame
  | right =>
      have hquot := S.right_face_quotient hside
      have hsame : f.SameCycle
          (B.map.toCombinatorialMap.edgeInv S.longDart) d := by
        change (Equiv.Perm.SameCycle.setoid f).r
          (B.map.toCombinatorialMap.edgeInv S.longDart) d
        exact Quotient.exact (hquot.symm.trans hd)
      obtain ⟨h₀, h₁, h₂⟩ := S.right_faceSucc_order hside
      simpa [hside, f, h₀, h₁, h₂] using faceCycle_mem_three f
        (B.map.toCombinatorialMap.edgeInv S.longDart)
        S.firstShortDart S.secondShortDart h₀ h₁ h₂ d hsame

/-- Two transitive shapes of the same face have the same corners, darts, and
side. Helper toward the inverse direction of `thm-kmsw` and `lem-lr-ind`; -/
theorem innerFaceShape_fields_eq_of_face_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S T : InnerFaceShape B) (hface : S.face = T.face) :
    S.source = T.source ∧ S.middle = T.middle ∧ S.sink = T.sink ∧
      S.longDart = T.longDart ∧ S.firstShortDart = T.firstShortDart ∧
      S.secondShortDart = T.secondShortDart ∧ S.side = T.side := by
  let f := B.map.toCombinatorialMap.faceSucc
  cases hs : S.side with
  | left =>
      cases ht : T.side with
      | left =>
          have hfaceOrbit := innerFaceShape_faceOrbit_mem B S T.longDart
            (hface.trans (T.left_face_quotient ht))
          obtain ⟨h₀, h₁, h₂⟩ := S.left_faceSucc_order hs
          have hmem : T.longDart = S.longDart ∨
              T.longDart = B.map.toCombinatorialMap.edgeInv S.secondShortDart ∨
              T.longDart = B.map.toCombinatorialMap.edgeInv S.firstShortDart := by
            simpa [hs, f, h₀, h₁, h₂] using hfaceOrbit
          have hsecondInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv S.secondShortDart) :=
            (B.map.tail_iff S.secondShortDart
              (B.noMissingDarts S.secondShortDart)).mp S.secondShort_orientation.1
          have hfirstInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv S.firstShortDart) :=
            (B.map.tail_iff S.firstShortDart
              (B.noMissingDarts S.firstShortDart)).mp S.firstShort_orientation.1
          have hlong : S.longDart = T.longDart := by
            rcases hmem with hlong | hsecond | hfirst
            · exact hlong.symm
            · exact False.elim
                (hsecondInvNot (hsecond ▸ T.long_orientation.1))
            · exact False.elim (hfirstInvNot (hfirst ▸ T.long_orientation.1))
          obtain ⟨hT₀, hT₁, hT₂⟩ := T.left_faceSucc_order ht
          have hsecondInv : B.map.toCombinatorialMap.edgeInv S.secondShortDart =
              B.map.toCombinatorialMap.edgeInv T.secondShortDart := by
            calc
              B.map.toCombinatorialMap.edgeInv S.secondShortDart = f S.longDart := h₀.symm
              _ = f T.longDart := congrArg f hlong
              _ = B.map.toCombinatorialMap.edgeInv T.secondShortDart := hT₀
          have hsecond : S.secondShortDart = T.secondShortDart := by
            have h := congrArg B.map.toCombinatorialMap.edgeInv hsecondInv
            simpa [B.map.toCombinatorialMap.edgeInv_invol] using h
          have hfirstInv : B.map.toCombinatorialMap.edgeInv S.firstShortDart =
              B.map.toCombinatorialMap.edgeInv T.firstShortDart := by
            calc
              B.map.toCombinatorialMap.edgeInv S.firstShortDart =
                  f (B.map.toCombinatorialMap.edgeInv S.secondShortDart) := h₁.symm
              _ = f (B.map.toCombinatorialMap.edgeInv T.secondShortDart) :=
                congrArg f hsecondInv
              _ = B.map.toCombinatorialMap.edgeInv T.firstShortDart := hT₁
          have hfirst : S.firstShortDart = T.firstShortDart := by
            have h := congrArg B.map.toCombinatorialMap.edgeInv hfirstInv
            simpa [B.map.toCombinatorialMap.edgeInv_invol] using h
          have hsource : S.source = T.source := by
            calc
              S.source = dartTailVertex B.map S.longDart :=
                S.long_orientation.2.1.symm
              _ = dartTailVertex B.map T.longDart := congrArg _ hlong
              _ = T.source := T.long_orientation.2.1
          have hsink : S.sink = T.sink := by
            calc
              S.sink = dartHeadVertex B.map S.longDart :=
                S.long_orientation.2.2.symm
              _ = dartHeadVertex B.map T.longDart := congrArg _ hlong
              _ = T.sink := T.long_orientation.2.2
          have hmiddle : S.middle = T.middle := by
            calc
              S.middle = dartHeadVertex B.map S.firstShortDart :=
                S.firstShort_orientation.2.2.symm
              _ = dartHeadVertex B.map T.firstShortDart := congrArg _ hfirst
              _ = T.middle := T.firstShort_orientation.2.2
          exact ⟨hsource, hmiddle, hsink, hlong, hfirst, hsecond, rfl⟩
      | right =>
          have hfaceOrbit := innerFaceShape_faceOrbit_mem B S
            (B.map.toCombinatorialMap.edgeInv T.longDart)
            (hface.trans (T.right_face_quotient ht))
          obtain ⟨h₀, h₁, h₂⟩ := S.left_faceSucc_order hs
          have hmem : B.map.toCombinatorialMap.edgeInv T.longDart =
              S.longDart ∨
            B.map.toCombinatorialMap.edgeInv T.longDart =
                B.map.toCombinatorialMap.edgeInv S.secondShortDart ∨
            B.map.toCombinatorialMap.edgeInv T.longDart =
                B.map.toCombinatorialMap.edgeInv S.firstShortDart := by
            simpa [hs, f, h₀, h₁, h₂] using hfaceOrbit
          obtain ⟨hT₀, hT₁, hT₂⟩ := T.right_faceSucc_order ht
          have hTlongInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv T.longDart) :=
            (B.map.tail_iff T.longDart (B.noMissingDarts T.longDart)).mp
              T.long_orientation.1
          have hfirstInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv S.firstShortDart) :=
            (B.map.tail_iff S.firstShortDart
              (B.noMissingDarts S.firstShortDart)).mp S.firstShort_orientation.1
          have hsecondInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv S.secondShortDart) :=
            (B.map.tail_iff S.secondShortDart
              (B.noMissingDarts S.secondShortDart)).mp S.secondShort_orientation.1
          rcases hmem with hlong | hsecond | hfirst
          · exact False.elim (hTlongInvNot (hlong ▸ S.long_orientation.1))
          · have hTfirst : T.firstShortDart =
                B.map.toCombinatorialMap.edgeInv S.firstShortDart := by
              calc
                T.firstShortDart = f (B.map.toCombinatorialMap.edgeInv T.longDart) := hT₀.symm
                _ = f (B.map.toCombinatorialMap.edgeInv S.secondShortDart) := congrArg f hsecond
                _ = B.map.toCombinatorialMap.edgeInv S.firstShortDart := h₁
            exact False.elim (hfirstInvNot (hTfirst ▸ T.firstShort_orientation.1))
          · have hTfirst : T.firstShortDart = S.longDart := by
              calc
                T.firstShortDart = f (B.map.toCombinatorialMap.edgeInv T.longDart) := hT₀.symm
                _ = f (B.map.toCombinatorialMap.edgeInv S.firstShortDart) := congrArg f hfirst
                _ = S.longDart := h₂
            have hTsecond : T.secondShortDart =
                B.map.toCombinatorialMap.edgeInv S.secondShortDart := by
              calc
                T.secondShortDart = f T.firstShortDart := hT₁.symm
                _ = f S.longDart := congrArg f hTfirst
                _ = B.map.toCombinatorialMap.edgeInv S.secondShortDart := h₀
            exact False.elim
              (hsecondInvNot (hTsecond ▸ T.secondShort_orientation.1))
      
  | right =>
      cases ht : T.side with
      | left =>
          have hfaceOrbit := innerFaceShape_faceOrbit_mem B S T.longDart
            (hface.trans (T.left_face_quotient ht))
          obtain ⟨h₀, h₁, h₂⟩ := S.right_faceSucc_order hs
          have hmem : T.longDart =
              B.map.toCombinatorialMap.edgeInv S.longDart ∨
            T.longDart = S.firstShortDart ∨ T.longDart = S.secondShortDart := by
            simpa [hs, f, h₀, h₁, h₂] using hfaceOrbit
          obtain ⟨hT₀, hT₁, hT₂⟩ := T.left_faceSucc_order ht
          have hlongInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv S.longDart) :=
            (B.map.tail_iff S.longDart (B.noMissingDarts S.longDart)).mp
              S.long_orientation.1
          have hfirstInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv S.firstShortDart) :=
            (B.map.tail_iff S.firstShortDart
              (B.noMissingDarts S.firstShortDart)).mp S.firstShort_orientation.1
          have hsecondInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv S.secondShortDart) :=
            (B.map.tail_iff S.secondShortDart
              (B.noMissingDarts S.secondShortDart)).mp S.secondShort_orientation.1
          rcases hmem with hlong | hfirst | hsecond
          · exact False.elim (hlongInvNot (hlong ▸ T.long_orientation.1))
          · have hTsecondInv : B.map.toCombinatorialMap.edgeInv T.secondShortDart =
                S.secondShortDart := by
              calc
                B.map.toCombinatorialMap.edgeInv T.secondShortDart = f T.longDart := hT₀.symm
                _ = f S.firstShortDart := congrArg f hfirst
                _ = S.secondShortDart := h₁
            have hTsecond : T.secondShortDart =
                B.map.toCombinatorialMap.edgeInv S.secondShortDart := by
              have h := congrArg B.map.toCombinatorialMap.edgeInv hTsecondInv
              simpa [B.map.toCombinatorialMap.edgeInv_invol] using h
            exact False.elim
              (hsecondInvNot (hTsecond ▸ T.secondShort_orientation.1))
          · have hTsecondInv : B.map.toCombinatorialMap.edgeInv T.secondShortDart =
                B.map.toCombinatorialMap.edgeInv S.longDart := by
              calc
                B.map.toCombinatorialMap.edgeInv T.secondShortDart = f T.longDart := hT₀.symm
                _ = f S.secondShortDart := congrArg f hsecond
                _ = B.map.toCombinatorialMap.edgeInv S.longDart := h₂
            have hTsecond : T.secondShortDart = S.longDart := by
              have h := congrArg B.map.toCombinatorialMap.edgeInv hTsecondInv
              simpa [B.map.toCombinatorialMap.edgeInv_invol] using h
            have hTfirstInv : B.map.toCombinatorialMap.edgeInv T.firstShortDart =
                S.firstShortDart := by
              calc
                B.map.toCombinatorialMap.edgeInv T.firstShortDart =
                    f (B.map.toCombinatorialMap.edgeInv T.secondShortDart) := hT₁.symm
                _ = f (B.map.toCombinatorialMap.edgeInv S.longDart) :=
                  congrArg f hTsecondInv
                _ = S.firstShortDart := h₀
            have hTfirst : T.firstShortDart =
                B.map.toCombinatorialMap.edgeInv S.firstShortDart := by
              have h := congrArg B.map.toCombinatorialMap.edgeInv hTfirstInv
              simpa [B.map.toCombinatorialMap.edgeInv_invol] using h
            exact False.elim
              (hfirstInvNot (hTfirst ▸ T.firstShort_orientation.1))
      | right =>
          have hfaceOrbit := innerFaceShape_faceOrbit_mem B S
            (B.map.toCombinatorialMap.edgeInv T.longDart)
            (hface.trans (T.right_face_quotient ht))
          obtain ⟨h₀, h₁, h₂⟩ := S.right_faceSucc_order hs
          have hmem : B.map.toCombinatorialMap.edgeInv T.longDart =
              B.map.toCombinatorialMap.edgeInv S.longDart ∨
            B.map.toCombinatorialMap.edgeInv T.longDart = S.firstShortDart ∨
            B.map.toCombinatorialMap.edgeInv T.longDart = S.secondShortDart := by
            simpa [hs, f, h₀, h₁, h₂] using hfaceOrbit
          obtain ⟨hT₀, hT₁, hT₂⟩ := T.right_faceSucc_order ht
          have hTlongInvNot : ¬ B.map.tail
              (B.map.toCombinatorialMap.edgeInv T.longDart) :=
            (B.map.tail_iff T.longDart (B.noMissingDarts T.longDart)).mp
              T.long_orientation.1
          rcases hmem with hlong | hfirst | hsecond
          · have hlong' : T.longDart = S.longDart := by
              have h := congrArg B.map.toCombinatorialMap.edgeInv hlong
              simpa [B.map.toCombinatorialMap.edgeInv_invol] using h
            have hfirst : S.firstShortDart = T.firstShortDart := by
              calc
                S.firstShortDart = f (B.map.toCombinatorialMap.edgeInv S.longDart) := h₀.symm
                _ = f (B.map.toCombinatorialMap.edgeInv T.longDart) := congrArg f hlong.symm
                _ = T.firstShortDart := hT₀
            have hsecond : S.secondShortDart = T.secondShortDart := by
              calc
                S.secondShortDart = f S.firstShortDart := h₁.symm
                _ = f T.firstShortDart := congrArg f hfirst
                _ = T.secondShortDart := hT₁
            have hsource : S.source = T.source := by
              calc
                S.source = dartTailVertex B.map S.longDart :=
                  S.long_orientation.2.1.symm
                _ = dartTailVertex B.map T.longDart := congrArg _ hlong'.symm
                _ = T.source := T.long_orientation.2.1
            have hsink : S.sink = T.sink := by
              calc
                S.sink = dartHeadVertex B.map S.longDart :=
                  S.long_orientation.2.2.symm
                _ = dartHeadVertex B.map T.longDart := congrArg _ hlong'.symm
                _ = T.sink := T.long_orientation.2.2
            have hmiddle : S.middle = T.middle := by
              calc
                S.middle = dartHeadVertex B.map S.firstShortDart :=
                  S.firstShort_orientation.2.2.symm
                _ = dartHeadVertex B.map T.firstShortDart := congrArg _ hfirst
                _ = T.middle := T.firstShort_orientation.2.2
            exact ⟨hsource, hmiddle, hsink, hlong'.symm, hfirst, hsecond, rfl⟩
          · exact False.elim (hTlongInvNot (hfirst ▸ S.firstShort_orientation.1))
          · exact False.elim (hTlongInvNot (hsecond ▸ S.secondShort_orientation.1))

/-- The source, middle, and sink vertices of a shape are determined by its
face quotient. Helper toward the inverse direction of `thm-kmsw` and
`lem-lr-ind`; not the paper results -/
theorem innerFaceShape_vertices_eq_of_face_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S T : InnerFaceShape B) (hface : S.face = T.face) :
    S.source = T.source ∧ S.middle = T.middle ∧ S.sink = T.sink :=
    let h := innerFaceShape_fields_eq_of_face_eq B S T hface
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- The source selector agrees with every shape witnessing its face quotient.
Helper toward the inverse direction of `thm-kmsw` and `lem-lr-ind`; not the -/
theorem innerFaceSource_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer)
    (S : InnerFaceShape B) (hS : S.face = q) :
    innerFaceSource B q hq = S.source := by
  change (innerFaceShapeOfFace B q hq).source = S.source
  have hface : (innerFaceShapeOfFace B q hq).face = S.face :=
    (innerFaceShapeOfFace_face B q hq).trans hS.symm
  exact (innerFaceShape_vertices_eq_of_face_eq B
    (innerFaceShapeOfFace B q hq) S hface).1

/-- The middle selector agrees with every shape witnessing its face quotient.
Helper toward the inverse direction of `thm-kmsw` and `lem-lr-ind`; not the -/
theorem innerFaceMiddle_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer)
    (S : InnerFaceShape B) (hS : S.face = q) :
    innerFaceMiddle B q hq = S.middle := by
  change (innerFaceShapeOfFace B q hq).middle = S.middle
  have hface : (innerFaceShapeOfFace B q hq).face = S.face :=
    (innerFaceShapeOfFace_face B q hq).trans hS.symm
  exact (innerFaceShape_vertices_eq_of_face_eq B
    (innerFaceShapeOfFace B q hq) S hface).2.1

/-- The sink selector agrees with every shape witnessing its face quotient.
Helper toward the inverse direction of `thm-kmsw` and `lem-lr-ind`; not the -/
theorem innerFaceSink_eq
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ Quotient.mk
      (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) B.map.outer)
    (S : InnerFaceShape B) (hS : S.face = q) :
    innerFaceSink B q hq = S.sink := by
  change (innerFaceShapeOfFace B q hq).sink = S.sink
  have hface : (innerFaceShapeOfFace B q hq).face = S.face :=
    (innerFaceShapeOfFace_face B q hq).trans hS.symm
  exact (innerFaceShape_vertices_eq_of_face_eq B
    (innerFaceShapeOfFace B q hq) S hface).2.2

/-- The middle vertex of a transitive inner-face shape is neither pole.
Helper toward the inverse direction of `thm-kmsw` and `lem-lr-ind`; not the -/
theorem innerFaceShape_middle_not_pole
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S : InnerFaceShape B) :
    S.middle ≠ B.source ∧ S.middle ≠ B.sink := by
  constructor
  · intro h
    apply B.isSource
    refine ⟨S.source, ?_⟩
    refine ⟨S.firstShortDart, B.noMissingDarts _,
      S.firstShort_orientation.1, S.firstShort_orientation.2.1, ?_⟩
    exact S.firstShort_orientation.2.2.trans h
  · intro h
    apply B.isSink
    refine ⟨S.sink, ?_⟩
    refine ⟨S.secondShortDart, B.noMissingDarts _,
      S.secondShort_orientation.1, ?_, S.secondShort_orientation.2.2⟩
    exact S.secondShort_orientation.2.1.trans h

/-- The second short dart is the canonical outgoing boundary dart at the
middle vertex: `rightmostOutgoing` on a left-side face and `leftmostOutgoing`
on a right-side face. Helper toward the inverse direction of `thm-kmsw` and
`lem-lr-ind`; not the paper results -/
theorem innerFaceShape_middle_shortDart_selectors
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (S : InnerFaceShape B) :
    (S.side = .left →
      S.secondShortDart = rightmostOutgoing B S.middle
        (innerFaceShape_middle_not_pole B S).2) ∧
    (S.side = .right →
      S.secondShortDart = leftmostOutgoing B S.middle
        (innerFaceShape_middle_not_pole B S).2) := by
  have hmiddle := innerFaceShape_middle_not_pole B S
  have hrotation := innerFaceShape_rotation_consecutive B S
  refine ⟨?_, ?_⟩
  · intro hside
    have hright := rightmostOutgoing_internal_characterization B S.middle
      hmiddle.1 hmiddle.2
    obtain ⟨_, hrot, _⟩ := hrotation.1 hside
    have hprev : B.map.toCombinatorialMap.rot.symm S.secondShortDart =
        B.map.toCombinatorialMap.edgeInv S.firstShortDart := by
      calc
        B.map.toCombinatorialMap.rot.symm S.secondShortDart =
            B.map.toCombinatorialMap.rot.symm
              (B.map.toCombinatorialMap.rot
                (B.map.toCombinatorialMap.edgeInv S.firstShortDart)) :=
          congrArg B.map.toCombinatorialMap.rot.symm hrot.symm
        _ = B.map.toCombinatorialMap.edgeInv S.firstShortDart := by simp
    have hprevNot : ¬ B.map.tail
        (B.map.toCombinatorialMap.rot.symm S.secondShortDart) := by
      rw [hprev]
      exact (B.map.tail_iff S.firstShortDart
        (B.noMissingDarts S.firstShortDart)).mp S.firstShort_orientation.1
    exact hright.2.2.2 S.secondShortDart
      S.secondShort_orientation.2.1 S.secondShort_orientation.1 hprevNot
  · intro hside
    have hleft := leftmostOutgoing_internal_characterization B S.middle
      hmiddle.1 hmiddle.2
    obtain ⟨_, hrot, _⟩ := hrotation.2 hside
    have hnextNot : ¬ B.map.tail
        (B.map.toCombinatorialMap.rot S.secondShortDart) := by
      rw [hrot]
      exact (B.map.tail_iff S.firstShortDart
        (B.noMissingDarts S.firstShortDart)).mp S.firstShort_orientation.1
    exact hleft.2.2.2 S.secondShortDart
      S.secondShort_orientation.2.1 S.secondShort_orientation.1 hnextNot

end DirectedDistances.PlanarMap
