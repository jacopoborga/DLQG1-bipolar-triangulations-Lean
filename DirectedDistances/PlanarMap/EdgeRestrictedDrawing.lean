module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.FiniteStarFirstReturn

/-! Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
abbrev RestrictedDart (D : Type*) (S : Set D) := {d : D // d ∈ S}

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
abbrev RestrictedVertex {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (_P : PLDrawing D V flip rot vert) (S : Set D) :=
  {v : V // ∃ d, d ∈ S ∧ vert d = v}

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def restrictedFlip {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (_P : PLDrawing D V flip rot vert) (S : Set D)
    (hS : ∀ d, d ∈ S ↔ flip d ∈ S) :
    RestrictedDart D S → RestrictedDart D S :=
  fun d => ⟨flip d.1, (hS d.1).mp d.2⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
@[expose] def restrictedVertex {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (S : Set D)
    (d : RestrictedDart D S) : RestrictedVertex P S :=
  ⟨vert d.1, ⟨d.1, d.2, rfl⟩⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem restrictedVertex_eq_iff {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (S : Set D)
    (d e : RestrictedDart D S) :
    restrictedVertex P S d = restrictedVertex P S e ↔ vert d.1 = vert e.1 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Restrict the drawing to a flip-invariant set of darts, retaining only incident vertices. -/
@[expose] noncomputable def restrictDrawing {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (S : Set D) (hS : ∀ d, d ∈ S ↔ flip d ∈ S) :
    PLDrawing (RestrictedDart D S) (RestrictedVertex P S)
      (restrictedFlip P S hS) (drawingFirstReturnPerm P S)
      (restrictedVertex P S) := by
  classical
  refine {
    flip_involutive := ?_
    flip_ne := ?_
    vert_rotation := ?_
    pos := fun v => P.pos v.1
    pos_injective := ?_
    arc := fun d => P.arc d.1
    arc_simple := ?_
    arc_length := ?_
    arc_start := ?_
    arc_finish := ?_
    arc_flip := ?_
    interior_disjoint := ?_
    interior_avoids_vertices := ?_
    locally_finite := ?_
    initial_nonzero := ?_
    initial_arg_injective := ?_
    rotation_agreement := ?_
  }
  · intro d
    apply Subtype.ext
    exact P.flip_involutive d.1
  · intro d h
    have hv := congrArg Subtype.val h
    exact P.flip_ne d.1 (by simpa [restrictedFlip] using hv)
  · intro d
    apply Subtype.ext
    exact drawingFirstReturn_sameVertex P S d
  · intro v w h
    apply Subtype.ext
    exact P.pos_injective h
  · intro d
    exact P.arc_simple d.1
  · intro d
    exact P.arc_length d.1
  · intro d
    change (P.arc d.1).start = P.pos (vert d.1)
    exact P.arc_start d.1
  · intro d
    change (P.arc d.1).finish = P.pos (vert (flip d.1))
    exact P.arc_finish d.1
  · intro d
    change P.arc (flip d.1) = (P.arc d.1).reverse
    exact P.arc_flip d.1
  · intro d e hed hef
    apply P.interior_disjoint
    · intro h
      exact hed (Subtype.ext h)
    · intro h
      apply hef
      apply Subtype.ext
      change e.1 = flip d.1 at h
      exact h
  · intro d v
    exact P.interior_avoids_vertices d.1 v.1
  · intro K hK
    let E : Set D := {d | (K ∩ (P.arc d).image).Nonempty}
    have hE : E.Finite := P.locally_finite K hK
    let A : Set (RestrictedDart D S) :=
      {d | (K ∩ (P.arc d.1).image).Nonempty}
    have hA : (Subtype.val '' A).Finite := hE.subset (by
      rintro e ⟨d, hd, rfl⟩
      exact hd)
    exact hA.of_finite_image (by
      intro x hx y hy h
      exact Subtype.ext h)
  · intro d
    exact P.initial_nonzero d.1
  · intro d e hv ha
    apply Subtype.ext
    apply P.initial_arg_injective d.1 e.1
    · exact congrArg Subtype.val hv
    · exact ha
  · intro d
    have hccw := drawingFirstReturnCcwObligation_holds P S d
    rcases hccw with ⟨hfin, hd, hr, hcase⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · let A : Set (RestrictedDart D S) :=
        {e | restrictedVertex P S e = restrictedVertex P S d}
      have hA : (Subtype.val '' A).Finite := hfin.subset (by
        rintro e ⟨d', hd', rfl⟩
        change restrictedVertex P S d' = restrictedVertex P S d at hd'
        exact ⟨d'.2, (restrictedVertex_eq_iff P S d' d).mp hd'⟩)
      exact hA.of_finite_image (by
        intro x hx y hy h
        exact Subtype.ext h)
    · change restrictedVertex P S d = restrictedVertex P S d
      rfl
    · change restrictedVertex P S (drawingFirstReturnPerm P S d) =
        restrictedVertex P S d
      exact (restrictedVertex_eq_iff P S _ _).2
        (drawingFirstReturn_sameVertex P S d)
    · rcases hcase with hsingle | ⟨hne, hmin⟩
      · left
        constructor
        · exact Subtype.ext hsingle.1
        · ext e
          constructor
          · intro he
            have het : e.1 ∈ {x : D | x ∈ S ∧ vert x = vert d.1} :=
              ⟨e.2, (restrictedVertex_eq_iff P S e d).mp he⟩
            have he' : e.1 = d.1 := by
              rw [hsingle.2] at het
              simpa using het
            exact Subtype.ext he'
          · intro he
            have he' : e = d := by simpa using he
            subst e
            rfl
      · right
        refine ⟨?_, ?_⟩
        · intro h
          apply hne
          exact congrArg Subtype.val h
        · intro e he hed
          have he' : e.1 ∈ S ∧ vert e.1 = vert d.1 :=
            ⟨e.2, (restrictedVertex_eq_iff P S e d).mp he⟩
          have hle := hmin e.1 he' (by
            intro h
            exact hed (Subtype.ext h))
          exact hle

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem restrictDrawing_arc {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (S : Set D)
    (hS : ∀ d, d ∈ S ↔ flip d ∈ S) (d : RestrictedDart D S) :
    (restrictDrawing P S hS).arc d = P.arc d.1 := by
  simp [restrictDrawing]

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem restrictDrawing_pos {D V : Type*} {flip : D → D} {rot : Equiv.Perm D}
    {vert : D → V} (P : PLDrawing D V flip rot vert) (S : Set D)
    (hS : ∀ d, d ∈ S ↔ flip d ∈ S) (v : RestrictedVertex P S) :
    (restrictDrawing P S hS).pos v = P.pos v.1 := by
  simp [restrictDrawing]

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
The image is the retained vertex positions together with the retained arc images. -/
theorem restrictDrawing_image_eq {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (S : Set D) (hS : ∀ d, d ∈ S ↔ flip d ∈ S) :
    (restrictDrawing P S hS).image =
      Set.range (fun v : RestrictedVertex P S => P.pos v.1) ∪
        {z | ∃ d : RestrictedDart D S, z ∈ (P.arc d.1).image} := by
  simp [PLDrawing.image, restrictDrawing]

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem restrictDrawing_image_subset {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (S : Set D) (hS : ∀ d, d ∈ S ↔ flip d ∈ S) :
    (restrictDrawing P S hS).image ⊆ P.image := by
  intro z hz
  rw [restrictDrawing_image_eq] at hz
  rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
  · left
    exact ⟨v.1, hv⟩
  · right
    exact ⟨d.1, hd⟩

end DirectedDistances.PlanarMap
