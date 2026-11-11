module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfIdentification

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Concrete half ancestry, permanent dart images, and retained face transport.
The unresolved geometric input is `AncestorPosHalfSideRangeIdentification`. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver
open scoped Classical

section FiniteHalf

variable {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
  (hR : xdpLengthBase R.B x = m) (a : ThinMapSide)
  (v : MapVertex (ancestorPosHalfRep R hR a).B.map)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ancestry in either concrete half is ancestry of its image in the uncut base. -/
theorem ancestorPos_ancestors_map_iff
    (z : MapVertex (ancestorPosHalfRep R hR a).B.map) :
    z ∈ ancestors (presentation (ancestorPosHalfRep R hR a) a v) ↔
      ancestorPosVertexMap R hR a z ∈
        ancestors (presentation R a (ancestorPosVertexMap R hR a v)) := by
  cases a with
  | left => exact cutLRep_ancestors_map_iff R hR z v
  | right => exact cutRRep_ancestors_map_iff R hR z v

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Selected half darts are exactly the darts whose two uncut endpoints are ancestors. -/
theorem ancestorPos_selectedDarts_map_iff
    (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    d ∈ selectedDarts (presentation (ancestorPosHalfRep R hR a) a v) ↔
      ancestorPosDartMap R hR a d ∈
        selectedDarts (presentation R a (ancestorPosVertexMap R hR a v)) := by
  change (_ ∈ ancestors _ ∧ _ ∈ ancestors _) ↔ (_ ∈ ancestors _ ∧ _ ∈ ancestors _)
  rw [ancestorPos_ancestors_map_iff, ancestorPos_ancestors_map_iff]
  rw [(ancestorPos_embedding_fields R hR a).2.2 d |>.1,
    (ancestorPos_embedding_fields R hR a).2.2 d |>.2]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A retained half face is inner and its entire uncut orbit is in the selected image. -/
theorem ancestorPos_retainedFace_iff_selected_image
    (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    retainedFace (presentation (ancestorPosHalfRep R hR a) a v) d ↔
      ¬ (ancestorPosHalfRep R hR a).B.map.IsOuter d ∧
        ∀ e : Fin R.dartCount,
          Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
            (ancestorPosDartMap R hR a d) e →
          ∃ c : selectedDarts (presentation (ancestorPosHalfRep R hR a) a v),
            ancestorPosDartMap R hR a c.1 = e := by
  cases a with
  | left => exact cutLRep_retainedFace_iff_selected_image R hR v d
  | right => exact cutRRep_retainedFace_iff_selected_image R hR v d

end FiniteHalf

private theorem dartFace_left_not_boundary
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D)
    (hi : ¬ B.map.IsOuter d)
    (hwhole : ∀ e, B.map.toCombinatorialMap.faceSucc.SameCycle d e →
      e ∈ pathCutLeftHalfDarts B P) :
    d ∉ pathCutLeftHalfBoundaryDarts B P := by
  let f := B.map.toCombinatorialMap.faceSucc
  have hex : ∃ e, f.SameCycle d e ∧ B.map.tail e := by
    rcases (innerFace_has_both_boundary_orientations B d hi).1 with ht | ht | ht
    · exact ⟨d, .rfl, ht⟩
    · exact ⟨f d, (Equiv.Perm.SameCycle.refl f d).apply_right, ht⟩
    · exact ⟨f (f d), (Equiv.Perm.SameCycle.refl f d).apply_right.apply_right, ht⟩
  obtain ⟨e, he, ht⟩ := hex
  have hei : ¬ B.map.IsOuter e := fun ho => hi (ho.trans he.symm)
  have heb : e ∉ pathCutLeftHalfBoundaryDarts B P := by
    rintro (⟨_, ho⟩ | ⟨p, hp, hep⟩)
    · exact hei ho
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
      exact ((B.map.tail_iff _ (B.noMissingDarts _)).mp (P.edge_step i).2.1)
        (hep ▸ ht)
  exact ((pathCutLeftHalf_inner_face_contained B P (hwhole e he) heb).2 d he.symm).2

private theorem dartFace_right_not_boundary
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D)
    (hi : ¬ B.map.IsOuter d)
    (hwhole : ∀ e, B.map.toCombinatorialMap.faceSucc.SameCycle d e →
      e ∈ pathCutRightHalfDarts B P) :
    d ∉ pathCutRightHalfBoundaryDarts B P := by
  let f := B.map.toCombinatorialMap.faceSucc
  have hex : ∃ e, f.SameCycle d e ∧ ¬ B.map.tail e := by
    rcases (innerFace_has_both_boundary_orientations B d hi).2 with ht | ht | ht
    · exact ⟨d, .rfl, ht⟩
    · exact ⟨f d, (Equiv.Perm.SameCycle.refl f d).apply_right, ht⟩
    · exact ⟨f (f d), (Equiv.Perm.SameCycle.refl f d).apply_right.apply_right, ht⟩
  obtain ⟨e, he, ht⟩ := hex
  have hei : ¬ B.map.IsOuter e := fun ho => hi (ho.trans he.symm)
  have heb : e ∉ pathCutRightHalfBoundaryDarts B P := by
    rintro (⟨_, ho⟩ | hp)
    · exact hei ho
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
      exact ht (P.edge_step i).2.1
  exact ((pathCutRightHalf_inner_face_contained B P (hwhole e he) heb).2 d he.symm).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An original inner face whose complete orbit is in a half cannot become exterior. -/
theorem ancestorPos_not_outer_of_face_range
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide)
    (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (hi : ¬ R.B.map.IsOuter (ancestorPosDartMap R hR a d))
    (hwhole : ∀ e, R.B.map.toCombinatorialMap.faceSucc.SameCycle
      (ancestorPosDartMap R hR a d) e → e ∈ Set.range (ancestorPosDartMap R hR a)) :
    ¬ (ancestorPosHalfRep R hR a).B.map.IsOuter d := by
  cases a with
  | left =>
    let P := selectedGeodesicOfLen R.B x hR
    let B := pathCutLeftHalfBase R.B P
    let J := (B.transportIso (Fintype.equivFin _)).symm
    have hb := dartFace_left_not_boundary R.B P (cutLRepDartMap R hR d) hi
      (fun e he => by
        obtain ⟨c, hc⟩ := hwhole e he
        exact hc ▸ (J.toEquiv c).2)
    intro ho
    exact hb ((pathCutLeftHalfMarked_isOuter_iff R.B P (J.toEquiv d)).mp
      ((J.outer_iff d).mpr ho))
  | right =>
    let P := selectedGeodesicOfLen R.B x hR
    let B := pathCutRightHalfBase R.B P
    let J := (B.transportIso (Fintype.equivFin _)).symm
    have hb := dartFace_right_not_boundary R.B P (cutRRepDartMap R hR d) hi
      (fun e he => by
        obtain ⟨c, hc⟩ := hwhole e he
        exact hc ▸ (J.toEquiv c).2)
    intro ho
    exact hb ((pathCutRightHalfMarked_isOuter_iff R.B P (J.toEquiv d)).mp
      ((J.outer_iff d).mpr ho))

private theorem dartFace_iso_faceSucc
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) (d : D) :
    I.toEquiv (M.toCombinatorialMap.faceSucc d) =
      N.toCombinatorialMap.faceSucc (I.toEquiv d) := by
  have hr (e : D) : I.toEquiv (M.rot.symm e) = N.rot.symm (I.toEquiv e) := by
    apply N.rot.injective
    rw [← I.rot_comm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change I.toEquiv (M.rot.symm (M.edgeInv d)) =
    N.rot.symm (N.edgeInv (I.toEquiv d))
  rw [hr, I.edgeInv_comm]

private theorem dartFace_iso_sameCycle
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) {d e : D}
    (h : M.toCombinatorialMap.faceSucc.SameCycle d e) :
    N.toCombinatorialMap.faceSucc.SameCycle (I.toEquiv d) (I.toEquiv e) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hi := Function.Semiconj.iterate_right
    (show Function.Semiconj I.toEquiv M.toCombinatorialMap.faceSucc
      N.toCombinatorialMap.faceSucc from dartFace_iso_faceSucc I) k d
  rw [perm_iterate_eq_pow, perm_iterate_eq_pow] at hi
  exact ⟨k, hi.symm.trans (congrArg I.toEquiv hk)⟩

private theorem dartFace_three_orbit
    {D : Type*} [Fintype D] [DecidableEq D] (f : Equiv.Perm D)
    (a b c d e : D) (hab : f a = b) (hbc : f b = c) (hca : f c = a)
    (hd : d ∈ [a, b, c]) :
    f.SameCycle d e ↔ e ∈ [a, b, c] := by
  have hmem : ∀ z ∈ [a, b, c], f.SameCycle a z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact .rfl
    · rw [← hab]
      exact (Equiv.Perm.SameCycle.refl f a).apply_right
    · rw [← hbc, ← hab]
      exact (Equiv.Perm.SameCycle.refl f a).apply_right.apply_right
  constructor
  · intro he
    obtain ⟨k, hk⟩ := ((hmem d hd).trans he).exists_nat_pow_eq
    have hp : ∀ k : ℕ, (f ^ k) a ∈ [a, b, c] := by
      intro k
      induction k with
      | zero => exact List.mem_cons_self
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ih ⊢
        rcases ih with ha | hb | hc
        · exact Or.inr (Or.inl ((congrArg f ha).trans hab))
        · exact Or.inr (Or.inr ((congrArg f hb).trans hbc))
        · exact Or.inl ((congrArg f hc).trans hca)
    exact hk ▸ hp k
  · intro he
    exact (hmem d hd).symm.trans (hmem e he)

private theorem dartFace_stage_triangle_orbit (w : ℕ → Fin 3) (t : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < t)
    (d e : StageDart (kmswStage w t).nextEdge)
    (hd : stageLimitDart w t d ∈ stageTriangleDartList w j) :
    (kmswMap w t).faceSucc.SameCycle d e ↔
      stageLimitDart w t e ∈ stageTriangleDartList w j := by
  let A := stageTriangleDart₁ w t j hj
  let B := stageTriangleDart₂ w t j hj
  let C := stageTriangleDart₃ w t j hj
  have hlist : [A, B, C].map (stageLimitDart w t) = stageTriangleDartList w j := rfl
  have hmem (z : StageDart (kmswStage w t).nextEdge) :
      stageLimitDart w t z ∈ stageTriangleDartList w j ↔ z ∈ [A, B, C] := by
    rw [← hlist, List.mem_map]
    constructor
    · rintro ⟨y, hy, he⟩
      exact (stageLimitDart w t).injective he ▸ hy
    · intro hz
      exact ⟨z, hz, rfl⟩
  obtain ⟨hab, hbc, hca, _⟩ := stageTriangle_isFace w j t hj
  exact (dartFace_three_orbit _ A B C d e hab hbc hca ((hmem d).mp hd)).trans
    (hmem e).symm

section TriangleImage

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
  (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide) (v : MapVertex (ancestorPosHalfRep R hR a).B.map)

local notation "H" => presentation (ancestorPosHalfRep R hR a) a v
local notation "f" => ancestorPosDartId w t R hR I a
local notation "g" => ancestorPosDartMap R hR a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An inner half face belongs to a unique already-created stage triangle, and its
entire uncut orbit is characterized by that triangle's permanent dart IDs. -/
theorem ancestorPos_inner_face_triangle
    (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (hd : ¬ (ancestorPosHalfRep R hR a).B.map.IsOuter d) :
    ∃ j : TriangleCreationTime w, j.val < t ∧
      f d ∈ stageTriangleDartList w j ∧
      ∀ e : Fin R.dartCount,
        R.B.map.toCombinatorialMap.faceSucc.SameCycle (g d) e ↔
          stageLimitDart w t (I.toEquiv e) ∈ stageTriangleDartList w j := by
  have hinner : ¬ R.B.map.IsOuter (g d) := by
    cases a with
    | left =>
      let P := selectedGeodesicOfLen R.B x hR
      let B := pathCutLeftHalfBase R.B P
      let J := (B.transportIso (Fintype.equivFin _)).symm
      have hb : (J.toEquiv d).1 ∉ pathCutLeftHalfBoundaryDarts R.B P := by
        intro hb
        exact hd ((J.outer_iff d).mp
          ((pathCutLeftHalfMarked_isOuter_iff R.B P (J.toEquiv d)).mpr hb))
      exact (pathCutLeftHalf_inner_face_contained R.B P (J.toEquiv d).2 hb).1
    | right =>
      let P := selectedGeodesicOfLen R.B x hR
      let B := pathCutRightHalfBase R.B P
      let J := (B.transportIso (Fintype.equivFin _)).symm
      have hb : (J.toEquiv d).1 ∉ pathCutRightHalfBoundaryDarts R.B P := by
        intro hb
        exact hd ((J.outer_iff d).mp
          ((pathCutRightHalfMarked_isOuter_iff R.B P (J.toEquiv d)).mpr hb))
      exact (pathCutRightHalf_inner_face_contained R.B P (J.toEquiv d).2 hb).1
  have houter : I.toEquiv (g d) ∉ stageOuterWord w t := by
    intro ho
    exact hinner ((I.outer_iff _).mp
      ((mem_iff_isOuter _ _ (Section3.kmsw_bdy_source_four_arcs w t).1.1 _).mp ho))
  obtain ⟨j, ⟨hj, hmem⟩, _⟩ :=
    (stage_dart_partition w t (I.toEquiv (g d))).resolve_left houter
  refine ⟨j, hj, hmem, ?_⟩
  intro e
  have hc : R.B.map.toCombinatorialMap.faceSucc.SameCycle (g d) e ↔
      (kmswMap w t).faceSucc.SameCycle (I.toEquiv (g d)) (I.toEquiv e) := by
    constructor
    · exact dartFace_iso_sameCycle I
    · intro he
      simpa only [DirectedMapWithMissingIso.symm, Equiv.symm_apply_apply] using
        dartFace_iso_sameCycle I.symm he
  exact hc.trans (dartFace_stage_triangle_orbit w t j hj _ _ hmem)

private theorem dartFace_triangle_fresh_mem (j : TriangleCreationTime w) :
    ((kmswStage w j.val).nextEdge, true) ∈ stageTriangleDartList w j := by
  dsimp only [stageTriangleDartList, stageTriangleDartTriple]
  split_ifs
  · cases (kmswStage w j.val).UL.dropLast.reverse <;>
      simp only [List.mem_cons, or_true, true_or]
  · simp only [List.mem_cons, or_true, true_or]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A whole triangle in the permanent half image was created before the current stage. -/
theorem ancestorPos_triangle_time_lt_of_image (j : TriangleCreationTime w)
    (hall : ∀ z ∈ stageTriangleDartList w j, z ∈ f '' selectedDarts H) :
    j.val < t := by
  obtain ⟨d, _, hd⟩ := hall _ (dartFace_triangle_fresh_mem w j)
  have hid := congrArg Prod.fst hd
  have hlt := (I.toEquiv (g d)).1.isLt
  change (I.toEquiv (g d)).1.val = (kmswStage w j.val).nextEdge at hid
  rw [hid] at hlt
  by_contra hn
  have hmono := kmswStage_nextEdge_mono w (Nat.le_of_not_gt hn)
  omega

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Retained half faces are exactly created triangles all of whose permanent darts
belong to the selected half image. No geometric side identification is assumed. -/
theorem ancestorPos_retainedFace_iff_triangle_image
    (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    retainedFace H d ↔
      ∃ j : TriangleCreationTime w, f d ∈ stageTriangleDartList w j ∧
        ∀ z ∈ stageTriangleDartList w j, z ∈ f '' selectedDarts H := by
  constructor
  · intro hd
    obtain ⟨j, hj, hmem, horbit⟩ := ancestorPos_inner_face_triangle w t R hR I a d hd.1
    refine ⟨j, hmem, ?_⟩
    intro z hz
    have hlt := stageTriangleDartList_lt w t j hj z hz
    let e : Fin R.dartCount := I.toEquiv.symm (⟨⟨z.1, hlt⟩, z.2⟩)
    have he : stageLimitDart w t (I.toEquiv e) = z := by
      dsimp only [e]
      rw [Equiv.apply_symm_apply]
      rfl
    obtain ⟨c, hc⟩ := ((ancestorPos_retainedFace_iff_selected_image R hR a v d).mp hd).2
      e ((horbit e).mpr (he.symm ▸ hz))
    refine ⟨c.1, c.2, ?_⟩
    change stageLimitDart w t (I.toEquiv (g c.1)) = z
    rw [hc, he]
  · rintro ⟨j, hmem, hall⟩
    have hj := ancestorPos_triangle_time_lt_of_image w t R hR I a v j hall
    have horbit (e : Fin R.dartCount)
        (he : R.B.map.toCombinatorialMap.faceSucc.SameCycle (g d) e) :
        stageLimitDart w t (I.toEquiv e) ∈ stageTriangleDartList w j :=
      (dartFace_stage_triangle_orbit w t j hj _ _ hmem).mp (dartFace_iso_sameCycle I he)
    have hpre (e : Fin R.dartCount)
        (he : R.B.map.toCombinatorialMap.faceSucc.SameCycle (g d) e) :
        ∃ c : selectedDarts H, g c.1 = e := by
      obtain ⟨c, hc, hce⟩ := hall _ (horbit e he)
      refine ⟨⟨c, hc⟩, I.toEquiv.injective ((stageLimitDart w t).injective hce)⟩
    have hi : ¬ R.B.map.IsOuter (g d) := by
      intro ho
      have hs := (mem_iff_isOuter _ _
        (Section3.kmsw_bdy_source_four_arcs w t).1.1 _).mpr ((I.outer_iff _).mpr ho)
      exact stageTriangleDart_not_outer w t j hj _ hmem hs
    have hhalf := ancestorPos_not_outer_of_face_range R hR a d hi
      (fun e he => by obtain ⟨c, hc⟩ := hpre e he; exact ⟨c.1, hc⟩)
    exact (ancestorPos_retainedFace_iff_selected_image R hR a v d).mpr ⟨hhalf, hpre⟩

end TriangleImage

section GeometricFace

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide) (s : ℕ) (v : MapVertex (ancestorPosHalfRep R hR a).B.map)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The dart-image obligation already implies the full retained-face membership
obligation. This equivalence is a reduction, not a geometric identification. -/
theorem ancestorPos_dart_face_iff_dart :
    (AncestorPosHalfDartImageIdentification w hfin hL htrans hRneg P t R hR I a s v ∧
      AncestorPosHalfFaceMembershipIdentification
        w hfin hL htrans hRneg P t R hR I a s v) ↔
      AncestorPosHalfDartImageIdentification
        w hfin hL htrans hRneg P t R hR I a s v := by
  constructor
  · exact And.left
  · intro hdarts
    refine ⟨hdarts, ?_⟩
    intro d
    rw [ancestorPos_retainedFace_iff_triangle_image w t R hR I a v d.1]
    rw [show ancestorPosDartId w t R hR I a ''
      selectedDarts (presentation (ancestorPosHalfRep R hR a) a v) =
      sourceAncestorDarts w hfin hL htrans hRneg P a s from hdarts]
    rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
For a genuine path prefix, the entire geometric identification reduces to dart
images alone: face membership, succession and every seam index follow. -/
theorem ancestorPos_geometricIdentification_iff_dartImage_of_prefix
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) :
    AncestorPosHalfGeometricIdentification w hfin hL htrans hRneg P t R hR I a s v ↔
      AncestorPosHalfDartImageIdentification
        w hfin hL htrans hRneg P t R hR I a s v :=
  (ancestorPos_geometricIdentification_iff_of_prefix
    w hfin hL htrans hRneg P t R hR I a s v hp).trans
      (ancestorPos_dart_face_iff_dart w hfin hL htrans hRneg P t R hR I a s v)

end GeometricFace

section PermanentAncestors

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
  (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide) (v : MapVertex (ancestorPosHalfRep R hR a).B.map)
  (hv : ancestorPosVertexId w t R hR I a v = (recordVertex w u).id)

include hut hv in
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both half ancestor sets are characterized by ambient permanent-ID reachability -/
theorem ancestorPos_ancestor_record_iff
    (z : MapVertex (ancestorPosHalfRep R hR a).B.map) :
    z ∈ ancestors (presentation (ancestorPosHalfRep R hR a) a v) ↔
      Reachable (⟨ancestorPosVertexId w t R hR I a z⟩ : PresentVertex w)
        (recordVertex w u) := by
  rw [ancestorPos_ancestors_map_iff]
  exact ancestorFinal_rep_ancestor_record_iff w t u hut R I a _ _ hv

include hut hv in
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent dart image is the actual half range restricted by ambient ancestry -/
theorem ancestorPos_selectedDarts_record_image_iff (e : ℕ × Bool) :
    e ∈ ancestorPosDartId w t R hR I a ''
        selectedDarts (presentation (ancestorPosHalfRep R hR a) a v) ↔
      e ∈ Set.range (ancestorPosDartId w t R hR I a) ∧
        Reachable (⟨edgeWest w e.1⟩ : PresentVertex w) (recordVertex w u) ∧
        Reachable (⟨edgeEast w e.1⟩ : PresentVertex w) (recordVertex w u) := by
  have hsel (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
      d ∈ selectedDarts (presentation (ancestorPosHalfRep R hR a) a v) ↔
        Reachable (⟨edgeWest w (ancestorPosDartId w t R hR I a d).1⟩ : PresentVertex w)
            (recordVertex w u) ∧
          Reachable (⟨edgeEast w (ancestorPosDartId w t R hR I a d).1⟩ : PresentVertex w)
            (recordVertex w u) := by
    rw [ancestorPos_selectedDarts_map_iff]
    exact ancestorFinal_rep_selectedDarts_record_iff w t u hut R I a _ hv _
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, rfl⟩, (hsel d).mp hd⟩
  · rintro ⟨⟨d, rfl⟩, hd⟩
    exact ⟨d, (hsel d).mpr hd, rfl⟩

end PermanentAncestors

section SideRange

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide)

local notation "f" => ancestorPosDartId w t R hR I a
local notation "F" => ancestorPosVertexId w t R hR I a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining geometric range comparison, without truncation, ancestry, faces or
boundary marks. This proposition is isolated and is not asserted to hold. -/
@[expose] noncomputable def AncestorPosHalfSideRangeIdentification : Prop :=
  ∀ e : StageDart (kmswStage w t).nextEdge,
    stageLimitDart w t e ∈ Set.range f ↔
      e.1.val ∈ sideEdges w hfin hL htrans hRneg P a

private theorem dartFace_side_reachable {u z : ℕ}
    (h : Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hRneg P a) u z) :
    Reachable (⟨u⟩ : PresentVertex w) ⟨z⟩ := by
  induction h with
  | refl => exact ⟨.nil⟩
  | @tail b c _ hbc ih =>
    obtain ⟨p⟩ := ih
    obtain ⟨e, _, hp, hw, he⟩ := hbc
    exact ⟨p.cons ⟨e, hp, hw, he⟩⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The range comparison transports finite half paths to paths confined to the
geometric side, preserving permanent edge IDs and orientation. Reduction only. -/
theorem ancestorPos_side_reachable_of_range
    (hside : AncestorPosHalfSideRangeIdentification
      w hfin hL htrans hRneg P t R hR I a)
    {b c : MapVertex (ancestorPosHalfRep R hR a).B.map}
    (h : Relation.ReflTransGen (ancestorPosHalfRep R hR a).B.map.directedStep b c) :
    Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hRneg P a) (F b) (F c) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨d, _, htail, hb, hc⟩ := hbc
    have hp := (ancestorPos_ids_oriented w t R hR I a d).mp htail
    have he := ancestorPos_ids_endpoints w t R hR I a d
    rw [hp.2] at he
    have hs : (f d).1 ∈ sideEdges w hfin hL htrans hRneg P a :=
      (hside (I.toEquiv (ancestorPosDartMap R hR a d))).mp ⟨d, rfl⟩
    exact ih.tail ⟨(f d).1, hs, hp.1,
      he.1.symm.trans (congrArg F hb), he.2.symm.trans (congrArg F hc)⟩

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
With the already available record-target and stage-allocation data, the smaller
side-range comparison suffices for dart-image equality. This is a reduction; -/
theorem ancestorPos_dartImage_of_sideRange
    (hside : AncestorPosHalfSideRangeIdentification
      w hfin hL htrans hRneg P t R hR I a)
    (s u : ℕ) (hut : u ≤ t)
    (v : MapVertex (ancestorPosHalfRep R hR a).B.map)
    (htarget : F v = thinMapBoundaryVertex w hfin hL htrans hRneg a s)
    (hrecord : recordVertex w u =
      (⟨thinMapBoundaryVertex w hfin hL htrans hRneg a s⟩ : PresentVertex w))
    (halloc : ∀ e ∈ sourceAncestorEdges w hfin hL htrans hRneg P a s,
      e < (kmswStage w t).nextEdge) :
    AncestorPosHalfDartImageIdentification w hfin hL htrans hRneg P t R hR I a s v := by
  have hvid : F v = (recordVertex w u).id := by
    rw [hrecord]
    exact htarget
  ext e
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hs : (f d).1 ∈ sideEdges w hfin hL htrans hRneg P a :=
      (hside (I.toEquiv (ancestorPosDartMap R hR a d))).mp ⟨d, rfl⟩
    have hpath (z : MapVertex (ancestorPosHalfRep R hR a).B.map)
        (hz : z ∈ ancestors (presentation (ancestorPosHalfRep R hR a) a v)) :
        Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hRneg P a)
          (F z) (thinMapBoundaryVertex w hfin hL htrans hRneg a s) := by
      rw [← htarget]
      exact ancestorPos_side_reachable_of_range w hfin hL htrans hRneg P t R hR I a
        hside hz
    have he := ancestorPos_ids_endpoints w t R hR I a d
    have hw := hpath _ hd.1
    have hh := hpath _ hd.2
    rw [he.1] at hw
    rw [he.2] at hh
    have hend := sideEdges_endpoints w hfin hL htrans hRneg P a hs
    have hpair :
        Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hRneg P a)
            (edgeWest w (f d).1) (thinMapBoundaryVertex w hfin hL htrans hRneg a s) ∧
          Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hRneg P a)
            (edgeEast w (f d).1) (thinMapBoundaryVertex w hfin hL htrans hRneg a s) := by
      cases hb : (f d).2 <;>
        simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hw hh
      · exact ⟨hw, hh⟩
      · exact ⟨hh, hw⟩
    change _ ∧ (_ ∧ _) ∧ (_ ∧ _)
    exact ⟨hs, ⟨hend.1, hpair.1⟩, ⟨hend.2, hpair.2⟩⟩
  · intro he
    have hsource : e.1 ∈ sourceAncestorEdges w hfin hL htrans hRneg P a s := he
    let d : StageDart (kmswStage w t).nextEdge := ⟨⟨e.1, halloc e.1 hsource⟩, e.2⟩
    have hrange : e ∈ Set.range f := (hside d).mpr hsource.1
    have hw := dartFace_side_reachable w hfin hL htrans hRneg P a hsource.2.1.2
    have hh := dartFace_side_reachable w hfin hL htrans hRneg P a hsource.2.2.2
    rw [← hrecord] at hw hh
    exact (ancestorPos_selectedDarts_record_image_iff w t u hut R hR I a v hvid e).mpr
      ⟨hrange, hw, hh⟩

end SideRange

section SelectedCutReduction

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
  (q : selectedCutCoherentDomain x T hT)

local notation "w" => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "hfin" => sourceAncestor_finite_incidence x T hT q
local notation "hL" => sourceAncestor_left_nonneg x T hT q
local notation "htrans" => sourceAncestor_left_transient x T hT q
local notation "hRneg" => sourceAncestor_right_unbounded x T hT q
local notation "P" => sourceAncestorPath x T hT q

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At a good cut, the only input to this dart-and-face reduction is the smaller
geometric half-range comparison. Record ancestry and stage confinement are proved
by existing lemmas. The range comparison is not asserted here. -/
theorem sourceAncestorPosHalf_dart_face_of_sideRange
    (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap w ((selectedCutTime T (k + 1) q.1).toNat - 1)))
    (v : MapVertex (ancestorPosHalfRep R hR a).B.map)
    (htarget : ancestorPosVertexId w ((selectedCutTime T (k + 1) q.1).toNat - 1)
      R hR I a v = thinMapBoundaryVertex w hfin hL htrans hRneg a s)
    (hside : AncestorPosHalfSideRangeIdentification w hfin hL htrans hRneg P
      ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a) :
    AncestorPosHalfDartImageIdentification w hfin hL htrans hRneg P
        ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a s v ∧
      AncestorPosHalfFaceMembershipIdentification w hfin hL htrans hRneg P
        ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a s v := by
  obtain ⟨u, hut, hrecord⟩ := ancestor_target_record x T hT q a s k hk
  apply (ancestorPos_dart_face_iff_dart w hfin hL htrans hRneg P
    ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a s v).mpr
  exact ancestorPos_dartImage_of_sideRange w hfin hL htrans hRneg P
    ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a hside s u hut v htarget hrecord
      (fun e he => (ancestor_edge_in_goodCut_stage x T hT q a s k hk e he).1)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
For a represented selected prefix at a good cut, the smaller range comparison
supplies the entire geometric identification consumed by the existing realization
reductions. This does not prove that range comparison or a source result. -/
theorem sourceAncestorPosHalf_geometric_of_sideRange
    (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap w ((selectedCutTime T (k + 1) q.1).toNat - 1)))
    (v : MapVertex (ancestorPosHalfRep R hR a).B.map)
    (htarget : ancestorPosVertexId w ((selectedCutTime T (k + 1) q.1).toNat - 1)
      R hR I a v = thinMapBoundaryVertex w hfin hL htrans hRneg a s)
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => (P).edge j.val))
    (hside : AncestorPosHalfSideRangeIdentification w hfin hL htrans hRneg P
      ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a) :
    AncestorPosHalfGeometricIdentification w hfin hL htrans hRneg P
      ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a s v := by
  apply (ancestorPos_geometricIdentification_iff_of_prefix w hfin hL htrans hRneg P
    ((selectedCutTime T (k + 1) q.1).toNat - 1) R hR I a s v hp).mpr
  exact sourceAncestorPosHalf_dart_face_of_sideRange x T hT q a s k hk R hR I v htarget hside

end SelectedCutReduction

section SourceReduction

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining range comparison for coherent choices of the already constructed
good-cut representatives. All witness fields are explicit to preserve their
joint dependence. This proposition is isolated and is not asserted to hold. -/
@[expose] noncomputable def SourceAncestorCutPositiveSideRangeIdentification : Prop :=
  ∀ (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
    0 < s →
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    let hfin := sourceAncestor_finite_incidence x T hT q
    let hL := sourceAncestor_left_nonneg x T hT q
    let htrans := sourceAncestor_left_transient x T hT q
    let hRneg := sourceAncestor_right_unbounded x T hT q
    let P := sourceAncestorPath x T hT q
    ∃ (ℓ r n m : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
      (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
      selectedCutSide x T a k q.1 =
        some ⟨_, ⟨_, ⟨_, KMSWMapIsoClass.mk (ancestorPosHalfRep R hR a)⟩⟩⟩ ∧
      boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v ∧
      ancestorPosVertexId w t R hR I a (ancestorPosHalfRep R hR a).B.source = 0 ∧
      ancestorPosVertexId w t R hR I a v =
        thinMapBoundaryVertex w hfin hL htrans hRneg a s ∧
      (∀ i < s, ((boundaryDarts (ancestorPosHalfRep R hR a).B a)[i]?).map
        (ancestorPosDartId w t R hR I a) =
          some (thinMapBoundaryDart w hfin hL htrans hRneg a i)) ∧
      (((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
        (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) ∧
      AncestorPosHalfSideRangeIdentification w hfin hL htrans hRneg P t R hR I a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining range comparison suffices for the original positive-half
identification. This reduction does not discharge the range comparison. -/
theorem sourceAncestorCutPositiveHalfIdentification_of_sideRange
    (h : SourceAncestorCutPositiveSideRangeIdentification x T hT) :
    SourceAncestorCutPositiveHalfIdentification x T hT := by
  intro a s k q hs hk
  obtain ⟨ℓ, r, n, m, R, hR, I, v, hrep, hv, hroot, htarget, hb, hp, hside⟩ :=
    h a s k q hs hk
  refine ⟨ℓ, r, n, m, R, hR, I, v, hrep, hv, hroot, htarget, hb, ?_⟩
  exact sourceAncestorPosHalf_geometric_of_sideRange
    x T hT q a s k hk R hR I v htarget hp hside

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The existing level-zero and positive-level reductions leave only the displayed
side-range obligation for realization. This is not an unconditional realization. -/
theorem sourceAncestorCutRealization_of_sideRange
    (h : SourceAncestorCutPositiveSideRangeIdentification x T hT) :
    SourceAncestorCutRealization x T hT :=
  sourceAncestorCutRealization_of_halfIdentification x T hT
    (sourceAncestorCutPositiveHalfIdentification_of_sideRange x T hT h)

end SourceReduction
end DirectedDistances.PaperProofs.Section4
