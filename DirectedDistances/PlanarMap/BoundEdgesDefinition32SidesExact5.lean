/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact4








public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: a locally covered upper-left boundary
edge has the left winding-side test at every open parameter of its forward arc. -/
theorem mem_upperLeftBoundary32_imp_mapFaceU_leftAtOn_of_locallyArcCovered32
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hlocal : IsLocallyArcCovered32 M B G) (e : E) :
    e ∈ upperLeftBoundary32 B →
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  intro he
  obtain ⟨hp, hborder⟩ := (mem_upperLeftBoundary32_iff_forward_dartBorders h e).mp he
  obtain ⟨i, hi⟩ := he
  obtain ⟨hp', hforward, _⟩ :=
    ((ULOkInf_iff B.presentation).mp h.presentation_facts.2.1).1 i
  have hd : B.presentation.upperLeft.darts i = (e, M.forward ⟨e, hp⟩) := by
    apply Prod.ext hi
    exact hforward.trans (congrArg M.forward (Subtype.ext hi))
  obtain ⟨N, hN, harc, hcover⟩ := hlocal.1 i
  rw [hd] at harc
  exact ⟨hp, G.dartBorders_toPath_leftAtOn_of_local_image
    (e, M.forward ⟨e, hp⟩) U hborder N hN harc hcover⟩

/-- Helper toward Definition 3.2: a locally covered lower-right boundary
edge has the right winding-side test at every open parameter of its forward arc. -/
theorem mem_lowerRightBoundary32_imp_mapFaceU_rightAtOn_of_locallyArcCovered32
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hlocal : IsLocallyArcCovered32 M B G) (e : E) :
    e ∈ lowerRightBoundary32 B →
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  intro he
  obtain ⟨hp, hborder⟩ := (mem_lowerRightBoundary32_iff_reverse_dartBorders h e).mp he
  obtain ⟨i, hi⟩ := he
  obtain ⟨hp', hreverse, _⟩ :=
    ((LROkInf_iff B.presentation).mp h.presentation_facts.2.2.2.1).1 i
  have hd : B.presentation.lowerRight.darts i = (e, !(M.forward ⟨e, hp⟩)) := by
    apply Prod.ext hi
    exact hreverse.trans (congrArg (fun b : Bool => !b)
      (congrArg M.forward (Subtype.ext hi)))
  obtain ⟨N, hN, harc, hcover⟩ := hlocal.2 i
  rw [hd, Polyline.range_toPath, G.arc_flip (e, M.forward ⟨e, hp⟩),
    Polyline.image_reverse_transfer, ← Polyline.range_toPath] at harc
  exact ⟨hp, G.dartBorders_flip_toPath_rightAtOn_of_local_image
    (e, M.forward ⟨e, hp⟩) U hborder N hN harc hcover⟩

namespace Definition32EndpointRay

/-- Helper toward Definition 3.2: an endpoint and a ray of nonincident vertices. -/
@[expose] def vertices : Set ℂ := {z | z = 1 ∨ (z.im = 0 ∧ z.re ≤ 0)}

/-- Helper toward Definition 3.2: endpoints of the one geometric edge. -/
@[expose] def endpoint (b : Bool) : vertices :=
  if b then ⟨0, Or.inr (by simp)⟩ else ⟨1, Or.inl rfl⟩

/-- Helper toward Definition 3.2: the endpoint assignment is injective. -/
theorem endpoint_injective : Function.Injective endpoint := by
  intro b c h
  have hv := congrArg Subtype.val h
  cases b <;> cases c
  · rfl
  · exact (one_ne_zero (show (1 : ℂ) = 0 from hv)).elim
  · exact (zero_ne_one (show (0 : ℂ) = 1 from hv)).elim
  · rfl

/-- Helper toward Definition 3.2: a segment with isolated vertices on the
negative real ray, accumulating at its initial endpoint. -/
@[expose] def map : DirectedPlaneMapWithMissing vertices Unit where
  src := fun _ => endpoint true
  tgt := fun _ => endpoint false
  pos := Subtype.val
  pos_injective := Subtype.val_injective
  arc := fun _ => Path.segment 0 1
  arc_injOn := fun _ => (Path.segment_injective_of_ne (zero_ne_one : (0 : ℂ) ≠ 1)).injOn
  openArc_disjoint := by
    intro e e' hne
    exact (hne (Subsingleton.elim e e')).elim
  openArc_avoids := by
    intro e v hv
    obtain ⟨t, ht, heq⟩ := hv
    change (Path.segment (0 : ℂ) 1) t = v.val at heq
    have hre := congrArg Complex.re heq
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.add_re, Complex.smul_re, Complex.zero_re, Complex.one_re,
      smul_eq_mul, mul_zero, mul_one, zero_add] at hre
    rcases v.property with hv | hv
    · rw [hv] at hre
      have : (t : ℝ) = 1 := hre
      exact (ne_of_lt ht.2) this
    · have : (t : ℝ) ≤ 0 := hre ▸ hv.2
      exact (not_le_of_gt ht.1) this
  missing := fun _ => False
  missing_on_external := by intro _ h; exact h.elim
  forward := fun _ => true

/-- Helper toward Definition 3.2: the initial dart vertex is the named endpoint. -/
theorem initial_eq_endpoint (d : Unit × Bool) :
    boundaryDartInitial map d = endpoint d.2 := by
  rw [boundaryDartInitial_eq]
  cases d.2 <;> rfl

/-- Helper toward Definition 3.2: the same drawing as a two-dart PL carrier. -/
@[expose] def drawing :
    PLDrawing (Unit × Bool) vertices (fun d => (d.1, !d.2))
      (Equiv.refl (Unit × Bool)) (boundaryDartInitial map) where
  flip_involutive := by rintro ⟨e, b⟩; cases b <;> rfl
  flip_ne := by rintro ⟨e, b⟩; cases e; cases b <;> decide
  vert_rotation := fun _ => rfl
  pos := Subtype.val
  pos_injective := Subtype.val_injective
  arc := fun d => Definition32Strip.arc d.2
  arc_simple := by
    intro d
    have hf : (Definition32Strip.arc true).IsSimple := by
      apply Polyline.isSimple_of_XMonotone
      · simp [Polyline.XMonotone, Definition32Strip.arc]
      · norm_num [Definition32Strip.arc]
    cases d.2
    · exact Polyline.isSimple_reverse_transfer _ hf
    · exact hf
  arc_length := by intro d; cases d.2 <;> norm_num [Definition32Strip.arc]
  arc_start := by intro d; rw [initial_eq_endpoint]; cases d.2 <;> rfl
  arc_finish := by intro d; rw [initial_eq_endpoint]; cases d.2 <;> rfl
  arc_flip := by intro d; cases d.2 <;> rfl
  interior_disjoint := by
    rintro ⟨e, b⟩ ⟨f, c⟩ hne hflip
    cases e; cases f; cases b <;> cases c <;> simp_all
  interior_avoids_vertices := by
    intro d v hv
    have him := Definition32Strip.arc_im hv.1
    have hre := Definition32Rectangle.arc_re hv.1
    rcases v.property with hone | hneg
    · apply hv.2
      cases d.2 <;> simp [Definition32Strip.arc, Polyline.start, Polyline.finish, hone]
    · have hzero : v.val = 0 := Complex.ext (le_antisymm hneg.2 hre.1) hneg.1
      apply hv.2
      cases d.2 <;> simp [Definition32Strip.arc, Polyline.start, Polyline.finish, hzero]
  locally_finite := fun _ _ => Set.toFinite _
  initial_nonzero := by
    intro d
    cases d.2 <;> norm_num [Definition32Strip.arc, Polyline.initialDirection,
      Polyline.point, Polyline.start]
  initial_arg_injective := by
    intro d e h _
    exact Prod.ext (Subsingleton.elim _ _)
      (endpoint_injective (by simpa only [initial_eq_endpoint] using h))
  rotation_agreement := by
    intro d
    refine ⟨Set.toFinite _, rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
    ext e
    constructor
    · intro h
      change boundaryDartInitial map e = boundaryDartInitial map d at h
      exact Prod.ext (Subsingleton.elim _ _)
        (endpoint_injective (by simpa only [initial_eq_endpoint] using h))
    · intro h
      exact congrArg (boundaryDartInitial map) h

/-- Helper toward Definition 3.2: all drawn points lie on the real ray to one. -/
theorem image_coordinates {z : ℂ} (hz : z ∈ drawing.image) : z.im = 0 ∧ z.re ≤ 1 := by
  rcases hz with ⟨v, rfl⟩ | ⟨d, hd⟩
  · change v.val.im = 0 ∧ v.val.re ≤ 1
    rcases v.property with hv | hv
    · simp [hv]
    · exact ⟨hv.1, hv.2.trans zero_le_one⟩
  · exact ⟨Definition32Strip.arc_im hd, (Definition32Rectangle.arc_re hd).2⟩

/-- Helper toward Definition 3.2: a connected corridor around the right endpoint. -/
@[expose] def corridor : Set ℂ := ({z | 0 < z.im} ∪ {z | 1 < z.re}) ∪ {z | z.im < 0}

/-- Helper toward Definition 3.2: the upper and lower half-planes connect on the right. -/
theorem corridor_isPreconnected : IsPreconnected corridor := by
  have hu : Convex ℝ {z : ℂ | 0 < z.im} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  have hr : Convex ℝ {z : ℂ | 1 < z.re} :=
    (convex_Ioi (1 : ℝ)).linear_preimage Complex.reLm
  have hl : Convex ℝ {z : ℂ | z.im < 0} :=
    (convex_Iio (0 : ℝ)).linear_preimage Complex.imLm
  exact (hu.isPreconnected.union (2 + Complex.I) (by norm_num) (by norm_num)
    hr.isPreconnected).union (2 - Complex.I) (Or.inr (by norm_num))
      (by norm_num) hl.isPreconnected

/-- Helper toward Definition 3.2: the corridor avoids every vertex and arc. -/
theorem corridor_subset_compl : corridor ⊆ drawing.imageᶜ := by
  intro z hz himage
  obtain ⟨him, hre⟩ := image_coordinates himage
  rcases hz with (hz | hz) | hz
  · exact (ne_of_gt hz) him
  · exact (not_lt_of_ge hre) hz
  · exact (ne_of_lt hz) him

/-- Helper toward Definition 3.2: the component containing the corridor. -/
@[expose] def face : drawing.Face :=
  ⟨connectedComponentIn drawing.imageᶜ Complex.I,
    Complex.I, corridor_subset_compl (Or.inl (Or.inl (by norm_num))), rfl⟩

/-- Helper toward Definition 3.2: the full corridor is in one complementary face. -/
theorem corridor_subset_face : corridor ⊆ face.val :=
  corridor_isPreconnected.subset_connectedComponentIn
    (Or.inl (Or.inl (by norm_num))) corridor_subset_compl

/-- Helper toward Definition 3.2: both oriented darts border the corridor face. -/
theorem dartBorders (d : Unit × Bool) : drawing.dartBorders d face := by
  rcases d with ⟨⟨⟩, b⟩
  refine ⟨1, zero_lt_one, ?_⟩
  intro t ε ht _ hε _
  apply corridor_subset_face
  cases b
  · apply Or.inr
    simpa [drawing, Definition32Strip.arc, Polyline.start,
      Polyline.initialDirection, Polyline.point] using neg_neg_of_pos (mul_pos ht hε)
  · apply Or.inl ∘ Or.inl
    simpa [drawing, Definition32Strip.arc, Polyline.start,
      Polyline.initialDirection, Polyline.point] using mul_pos ht hε

/-- Helper toward Definition 3.2: the corridor face is unbounded. -/
theorem face_isUnbounded : drawing.IsUnbounded face := by
  intro R
  let y : ℝ := |R| + 1
  have hy : 0 < y := by dsimp [y]; positivity
  refine ⟨(y : ℂ) * Complex.I, corridor_subset_face (Or.inl (Or.inl ?_)), ?_⟩
  · simpa using hy
  · simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hy] using
      (lt_add_of_le_of_pos (le_abs_self R) zero_lt_one)

/-- Helper toward Definition 3.2: the geometric successor flips the two darts. -/
theorem geometricExternalFaceSucc :
    IsGeometricExternalFaceSucc drawing face (fun d => (d.1, !d.2)) :=
  ⟨face_isUnbounded, fun _d _ => ⟨rfl, dartBorders _⟩⟩

/-- Helper toward Definition 3.2: explicit semicircles certify the left
side of the segment despite the nonincident vertices at its initial endpoint. -/
theorem segment_leftAtOn (s : {t : I // t ∈ openParams}) :
    LeftAtOn face.val (Path.segment (0 : ℂ) 1) s := by
  let r : ℝ := min (s.1 : ℝ) (1 - (s.1 : ℝ)) / 2
  have hr : 0 < r := half_pos (lt_min s.property.1 (sub_pos.mpr s.property.2))
  have hrs : r < (s.1 : ℝ) := by
    have := min_le_left (s.1 : ℝ) (1 - (s.1 : ℝ))
    dsimp only [r]
    linarith only [this, s.property.1]
  have hr1 : r < 1 - (s.1 : ℝ) := by
    have := min_le_right (s.1 : ℝ) (1 - (s.1 : ℝ))
    dsimp only [r]
    linarith only [this, s.property.2]
  let a : I := ⟨(s.1 : ℝ) - r, ⟨by linarith, by linarith [s.1.property.2]⟩⟩
  let b : I := ⟨(s.1 : ℝ) + r, ⟨by linarith [s.1.property.1], by linarith⟩⟩
  have ha : 0 < a := by change 0 < (s.1 : ℝ) - r; linarith
  have has : a < s.1 := by change (s.1 : ℝ) - r < (s.1 : ℝ); linarith
  have hsb : s.1 < b := by change (s.1 : ℝ) < (s.1 : ℝ) + r; linarith
  have hb : b < 1 := by change (s.1 : ℝ) + r < 1; linarith
  have hab : a < b := has.trans hsb
  have habR : (a : ℝ) < (b : ℝ) := hab
  let x : ℂ := ((s.1 : ℝ) : ℂ)
  have hγ (t : I) : Path.segment (0 : ℂ) 1 t = ((t : ℝ) : ℂ) := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  have haEval : Path.segment (0 : ℂ) 1 a = x - (r : ℂ) := by
    rw [hγ]; dsimp [a, x]; push_cast; rfl
  have hbEval : Path.segment (0 : ℂ) 1 b = x + (r : ℂ) := by
    rw [hγ]; dsimp [b, x]; push_cast; rfl
  let f : I → I := fun t => ⟨
    (((min (max t a) b : I) : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr (le_min (le_max_right _ _) hab.le))
          (sub_pos.mpr habR).le
      · exact (div_le_one (sub_pos.mpr habR)).mpr
          (sub_le_sub_right (min_le_right _ _) _)⟩
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf0 : f 0 = 0 := by apply Subtype.ext; simp [f, min_eq_left hab.le]
  have hf1 : f 1 = 1 := by
    apply Subtype.ext
    simp [f, max_eq_left a.property.2, min_eq_right b.property.2, ne_of_gt (sub_pos.mpr habR)]
  let q : Path (Path.segment (0 : ℂ) 1 b) (Path.segment (0 : ℂ) 1 a) :=
    (leftSemicircle x (r : ℂ)).cast hbEval haEval
  have hqinj : Function.Injective q := leftSemicircle_injective x (r : ℂ)
    (Complex.ofReal_ne_zero.mpr hr.ne')
  have hqF (t : I) (ht : t ∈ openParams) : q t ∈ face.val := by
    apply corridor_subset_face
    apply Or.inl ∘ Or.inl
    have hside := leftSemicircle_side_pos x (r : ℂ)
      (Complex.ofReal_ne_zero.mpr hr.ne') t ht
    have hx : x.im = 0 := by simp [x]
    change 0 < (leftSemicircle x (r : ℂ) t).im
    have hprod : 0 < r * (leftSemicircle x (r : ℂ) t).im := by
      simpa [Complex.star_def, hx] using hside
    exact (mul_pos_iff_of_pos_left hr).mp hprod
  have hloop (t : I) :
      ((edgeSubarc (Path.segment (0 : ℂ) 1) a b hab.le).trans q) t =
        (((Path.segment (x - (r : ℂ)) (x + (r : ℂ))).reparam f hf hf0 hf1).trans
          (leftSemicircle x (r : ℂ))) t := by
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · rw [edgeSubarc_segment_apply hab]
      rw [hγ]
      change _ = Path.segment (x - (r : ℂ)) (x + (r : ℂ)) (f _)
      simp only [Path.segment_apply, AffineMap.lineMap_apply_module',
        Complex.real_smul]
      dsimp only [f, a, b, x]
      push_cast
      field_simp [hr.ne']
      ring
    · rfl
  have hwind {w : ℂ} (hw : HasWinding (semicircleLoop x (r : ℂ)) w 1) :
      HasWinding ((edgeSubarc (Path.segment (0 : ℂ) 1) a b hab.le).trans q) w 1 :=
    (hasWinding_congr_fun _ _ w 1 hloop).mpr (hw.trans_reparam_left f hf hf0 hf1)
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  apply (congrArg (fun z : ℂ => z ∈ closure
    {w : ℂ | w ∈ face.val ∧ HasWinding
      ((edgeSubarc (Path.segment (0 : ℂ) 1) a b hab.le).trans q) w 1}) (hγ s.1)).mpr
  rw [Metric.mem_closure_iff]
  intro η hη
  let τ := min (1 / 2) (η / (2 * (r + 1)))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hτ1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hτη : τ * (2 * (r + 1)) ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let w : ℂ := x + (r : ℂ) * (τ * Complex.I)
  refine ⟨w, ⟨corridor_subset_face (Or.inl (Or.inl ?_)), hwind
    (hasWinding_semicircleLoop x (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne') τ hτ hτ1)⟩, ?_⟩
  · change 0 < w.im
    simpa [w, x] using mul_pos hr hτ
  · rw [dist_comm, dist_eq_norm]
    change ‖x + (r : ℂ) * (τ * Complex.I) - x‖ < η
    rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hτ, Complex.norm_I, mul_one]
    nlinarith only [hτη, hτ, hr]

/-- Helper toward Definition 3.2: the image is exactly the closed real ray to one. -/
theorem image_eq : drawing.image = {z : ℂ | z.im = 0 ∧ z.re ≤ 1} := by
  apply Set.Subset.antisymm (fun _ hz => image_coordinates hz)
  intro z hz
  by_cases hre : z.re ≤ 0
  · exact Or.inl ⟨⟨z, Or.inr ⟨hz.1, hre⟩⟩, rfl⟩
  · apply Or.inr
    refine ⟨((), true), ?_⟩
    rw [← Polyline.range_toPath]
    refine ⟨⟨z.re, ⟨(not_le.mp hre).le, hz.2⟩⟩, ?_⟩
    change Path.segment (0 : ℂ) 1 _ = z
    apply Complex.ext <;> simp [Path.segment_apply, AffineMap.lineMap_apply_module, hz.1]

/-- Helper toward Definition 3.2: the counterexample even has closed drawing image. -/
theorem image_isClosed : IsClosed drawing.image := by
  rw [image_eq]
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le Complex.continuous_re continuous_const)

/-- Helper toward Definition 3.2: the corridor exhausts the complementary face. -/
theorem face_eq_corridor : face.val = corridor := by
  apply Set.Subset.antisymm _ corridor_subset_face
  intro z hz
  have hn := drawing.face_subset_compl face hz
  rw [image_eq] at hn
  by_cases him : 0 < z.im
  · exact Or.inl (Or.inl him)
  by_cases him' : z.im < 0
  · exact Or.inr him'
  exact Or.inl (Or.inr (lt_of_not_ge (fun hre => hn ⟨le_antisymm
    (not_lt.mp him) (not_lt.mp him'), hre⟩)))

/-- Helper toward Definition 3.2: the counterexample face is open, despite
the failure of local coverage of the closed boundary arcs. -/
theorem face_isOpen : IsOpen face.val := by
  rw [face_eq_corridor]
  exact ((isOpen_lt continuous_const Complex.continuous_im).union
    (isOpen_lt continuous_const Complex.continuous_re)).union
      (isOpen_lt Complex.continuous_im continuous_const)

/-- Helper toward Definition 3.2: the endpoint-ray face is invariant under conjugation. -/
theorem conj_mem_face {z : ℂ} (hz : z ∈ face.val) : star z ∈ face.val := by
  rw [face_eq_corridor] at hz ⊢
  rcases hz with (hz | hz) | hz
  · exact Or.inr (by simpa using neg_neg_of_pos (show 0 < z.im from hz))
  · exact Or.inl (Or.inr (by simpa using hz))
  · exact Or.inl (Or.inl (by simpa using neg_pos.mpr hz))

/-- Helper toward Definition 3.2: conjugating the explicit upper semicircle
gives the right-side test along the same forward segment. -/
theorem segment_rightAtOn (s : {t : I // t ∈ openParams}) :
    RightAtOn face.val (Path.segment (0 : ℂ) 1) s := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩ := segment_leftAtOn s
  have hγ (t : I) : star (Path.segment (0 : ℂ) 1 t) = Path.segment (0 : ℂ) 1 t := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module, Complex.real_smul]
  let q' := (q.map Complex.continuous_conj).cast (hγ b).symm (hγ a).symm
  have hq'i : Function.Injective q' := by
    intro t t' h
    apply hqi
    exact star_injective h
  have hq'F (t : I) (ht : t ∈ openParams) : q' t ∈ face.val :=
    conj_mem_face (hqF t ht)
  have hab : a < b := has.trans hsb
  let L := (edgeSubarc (Path.segment (0 : ℂ) 1) a b hab.le).trans q
  let L' := (edgeSubarc (Path.segment (0 : ℂ) 1) a b hab.le).trans q'
  have hL (t : I) : (L.map Complex.continuous_conj) t = L' t := by
    change star (((edgeSubarc (Path.segment (0 : ℂ) 1) a b hab.le).trans q) t) =
      ((edgeSubarc (Path.segment (0 : ℂ) 1) a b hab.le).trans q') t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · rw [edgeSubarc_segment_apply hab]
      exact hγ _
    · rfl
  have hsubset : star '' {w : ℂ | w ∈ face.val ∧ HasWinding L w 1} ⊆
      {w : ℂ | w ∈ face.val ∧ HasWinding L' w (-1)} := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨conj_mem_face hw.1, ?_⟩
    exact (hasWinding_congr_fun _ _ (star w) (-1) hL).mp (hasWinding_conj L w 1 hw.2)
  have hc := closure_mono hsubset
    (mem_closure_image Complex.continuous_conj.continuousAt hcl)
  rw [hγ] at hc
  exact ⟨a, b, ha, has, hsb, hb, q', hq'i, hq'F, hc⟩

/-- Helper toward Definition 3.2: the literal map and PL drawing have the
same positions and geometric edge traces. -/
theorem drawsMap : DrawsMap map drawing := by
  refine ⟨rfl, ?_⟩
  rintro ⟨⟨⟩, b⟩
  cases b
  · change Set.range (Path.segment (1 : ℂ) 0) = Set.range (Path.segment (0 : ℂ) 1)
    rw [Path.range_segment, Path.range_segment, segment_symm]
  · rfl

/-- Helper toward Definition 3.2: the corridor face as a literal map face. -/
@[expose] def mapFace : (Drawing map).Face :=
  ⟨face.val, by
    obtain ⟨z, hz, hF⟩ := face.property
    exact ⟨z, drawsMap.image_eq ▸ hz, drawsMap.image_eq ▸ hF⟩⟩

/-- Helper toward Definition 3.2: the literal map face is external. -/
theorem mapFace_isExternal : (Drawing map).IsExternal mapFace := by
  change ¬ Bornology.IsBounded face.val
  rw [isBounded_iff_forall_norm_le]
  push Not
  exact face_isUnbounded

/-- Helper toward Definition 3.2: the literal map has closed image as well. -/
theorem map_isClosedDrawing : (Drawing map).IsClosedDrawing := by
  change IsClosed (Drawing map).image
  rw [← drawsMap.image_eq]
  exact image_isClosed

/-- Helper toward Definition 3.2: openness also holds for the literal map face. -/
theorem mapFace_isOpen : IsOpen mapFace.val := face_isOpen

/-- Helper toward Definition 3.2: all real points are approached from above by the face. -/
theorem real_mem_closure_face (x : ℝ) : (x : ℂ) ∈ closure face.val := by
  rw [Metric.mem_closure_iff]
  intro η hη
  refine ⟨(x : ℂ) + ((η / 2 : ℝ) : ℂ) * Complex.I,
    corridor_subset_face (Or.inl (Or.inl ?_)), ?_⟩
  · simpa using half_pos hη
  · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hη)]
    exact half_lt_self hη

/-- Helper toward Definition 3.2: the sole edge is on an external map frontier. -/
theorem externalFrontierEdge : ExternalFrontierEdge map () := by
  apply (externalFrontierEdge_iff map ()).mpr
  refine ⟨mapFace, mapFace_isExternal, ?_⟩
  apply ((Drawing map).range_subset_closure_iff_frontier_of_face_complement mapFace ()).mp
  rintro z ⟨t, rfl⟩
  change Path.segment (0 : ℂ) 1 t ∈ closure face.val
  simpa [Path.segment_apply, AffineMap.lineMap_apply_module] using real_mem_closure_face (t : ℝ)

/-- Helper toward Definition 3.2: a singleton directed boundary side with both endpoint labels. -/
@[expose] def presentSide (b : Bool) : InfiniteBoundarySide vertices Unit where
  Index := Unit
  darts := ⟨fun _ => ((), b), fun _ _ _ => Subsingleton.elim _ _⟩
  next := fun _ => none
  initialVertex? := some (endpoint b)
  terminalVertex? := some (endpoint (!b))

/-- Helper toward Definition 3.2: a missing side with no darts, marking a zero-edge path. -/
@[expose] def emptySide (v : vertices) : InfiniteBoundarySide vertices Unit where
  Index := Empty
  darts := ⟨Empty.elim, fun i => nomatch i⟩
  next := Empty.elim
  initialVertex? := some v
  terminalVertex? := some v

/-- Helper toward Definition 3.2: the one-edge UL/LR presentation with empty UR/LL runs. -/
@[expose] def presentation : InfiniteBoundaryPresentation map where
  upperLeft := presentSide true
  upperRight := emptySide (endpoint false)
  lowerRight := presentSide false
  lowerLeft := emptySide (endpoint true)

/-- Helper toward Definition 3.2: retain the supplied endpoint labels without extra junction marks. -/
@[expose] def boundary : BoundaryPresentationWithJunctions map :=
  ⟨presentation, none⟩

/-- Helper toward Definition 3.2: all boundary indices are one of the two present-side occurrences. -/
theorem index_cases (i : InfiniteBoundaryDartIndex presentation) :
    i = .upperLeft () ∨ i = .lowerRight () := by
  cases i with
  | upperLeft i => change Unit at i; cases i; exact Or.inl rfl
  | upperRight i => exact nomatch i
  | lowerRight i => change Unit at i; cases i; exact Or.inr rfl
  | lowerLeft i => exact nomatch i

/-- Helper toward Definition 3.2: upper-left orientation and winding clauses for the literal map. -/
theorem ulOkInf : ULOkInf presentation := by
  apply (ULOkInf_iff presentation).mpr
  refine ⟨fun _ => ⟨by intro h; exact h, rfl, mapFace, mapFace_isExternal, ?_⟩, ?_⟩
  · exact segment_leftAtOn
  · intro i j h
    change (none : Option Unit) = some j at h
    cases h

/-- Helper toward Definition 3.2: lower-right orientation and winding clauses for the literal map. -/
theorem lrOkInf : LROkInf presentation := by
  apply (LROkInf_iff presentation).mpr
  refine ⟨fun _ => ⟨by intro h; exact h, rfl, mapFace, mapFace_isExternal, ?_⟩, ?_⟩
  · exact segment_rightAtOn
  · intro i j h
    change (none : Option Unit) = some j at h
    cases h

/-- Helper toward Definition 3.2: the boundary lists exactly the external edge twice,
with the required opposite winding-side witnesses. -/
theorem boundaryOrder : IsBoundaryOrderOfInf map presentation := by
  apply (IsBoundaryOrderOfInf_iff presentation).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro e
    cases e
    exact ⟨fun _ => externalFrontierEdge, fun _ => ⟨.upperLeft (), rfl⟩⟩
  · intro e i j k _ _ _
    rcases index_cases i with rfl | rfl <;>
      rcases index_cases j with rfl | rfl <;>
      rcases index_cases k with rfl | rfl <;> simp
  · intro e i j _ _ _
    cases e
    refine ⟨by intro h; exact h, mapFace, mapFace,
      mapFace_isExternal, mapFace_isExternal, ?_, ?_⟩
    · change ∀ s, LeftAtOn face.val (Path.segment (0 : ℂ) 1) s
      exact segment_leftAtOn
    · change ∀ s, RightAtOn face.val (Path.segment (0 : ℂ) 1) s
      exact segment_rightAtOn

/-- Helper toward Definition 3.2: singleton present sides are simple vertex paths. -/
theorem presentSide_simple (b : Bool) : IsSimpleBoundarySide map (presentSide b) := by
  have : Subsingleton (presentSide b).Index := by change Subsingleton Unit; infer_instance
  have hleft (i : (presentSide b).Index) :
      boundarySideVertex map (presentSide b) (.inl i) = endpoint b := by
    rw [boundarySideVertex, boundaryDartInitial_eq]
    cases b <;> rfl
  have hright (i : {i : (presentSide b).Index // (presentSide b).next i = none}) :
      boundarySideVertex map (presentSide b) (.inr i) = endpoint (!b) := by
    rw [boundarySideVertex, boundaryDartTerminal_eq]
    cases b <;> rfl
  constructor
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subsingleton.elim _ _)
      | inr j =>
        have hv : endpoint b = endpoint (!b) := by
          exact (hleft i).symm.trans (hij.trans (hright j))
        have he := endpoint_injective hv
        cases b <;> contradiction
    | inr i =>
      cases j with
      | inl j =>
        have hv : endpoint (!b) = endpoint b := by
          exact (hright i).symm.trans (hij.trans (hleft j))
        have he := endpoint_injective hv
        cases b <;> contradiction
      | inr j => exact congrArg Sum.inr (Subtype.ext (Subsingleton.elim _ _))
  · intro i h
    induction h with
    | single h => cases h
    | tail _ h _ => cases h

/-- Helper toward Definition 3.2: the singleton labels are its actual first and last vertices. -/
theorem presentSide_endpointLabels (b : Bool) :
    BoundarySideEndpointLabels map (presentSide b) := by
  unfold BoundarySideEndpointLabels
  constructor
  · intro v hv
    have hv' : endpoint b = v := Option.some.inj hv
    subst v
    constructor
    · intro _
      refine ⟨(), ?_, ?_⟩
      · intro j h
        change (none : Option Unit) = some () at h
        cases h
      rw [boundaryDartInitial_eq]
      cases b <;> rfl
    · intro i _
      rw [boundaryDartInitial_eq]
      cases b <;> rfl
  · constructor
    · intro v hv
      have hv' : endpoint (!b) = v := Option.some.inj hv
      subst v
      constructor
      · intro _
        refine ⟨(), rfl, ?_⟩
        rw [boundaryDartTerminal_eq]
        cases b <;> rfl
      · intro i _
        rw [boundaryDartTerminal_eq]
        cases b <;> rfl
    · intro h
      exact (h.false ()).elim

/-- Helper toward Definition 3.2: each empty missing side has equal endpoint labels. -/
theorem emptySide_endpointLabels (v : vertices) :
    BoundarySideEndpointLabels map (emptySide v) := by
  unfold BoundarySideEndpointLabels
  constructor
  · intro z _
    exact ⟨fun h => h.elim (fun i => nomatch i), fun i => nomatch i⟩
  · constructor
    · intro z _
      exact ⟨fun h => h.elim (fun i => nomatch i), fun i => nomatch i⟩
    · intro _ z w hz hw
      exact (Option.some.inj hz).symm.trans (Option.some.inj hw)

/-- Helper toward Definition 3.2: the two boundary occurrences have positions zero and one. -/
@[expose] def position : InfiniteBoundaryDartIndex presentation ≃ Fin 2 where
  toFun i := match i with
    | .upperLeft _ => 0
    | .upperRight i => nomatch i
    | .lowerRight _ => 1
    | .lowerLeft i => nomatch i
  invFun p := if p = 0 then .upperLeft () else .lowerRight ()
  left_inv := by
    intro i
    rcases index_cases i with rfl | rfl <;> rfl
  right_inv := by
    intro p
    fin_cases p <;> rfl

/-- Helper toward Definition 3.2: the listed upper-left dart is forward. -/
theorem dart_upperLeft : InfiniteBoundaryDartIndex.dart presentation (.upperLeft ()) =
    ((), true) := by rw [InfiniteBoundaryDartIndex.dart_eq]; rfl

/-- Helper toward Definition 3.2: the listed lower-right dart is reversed. -/
theorem dart_lowerRight : InfiniteBoundaryDartIndex.dart presentation (.lowerRight ()) =
    ((), false) := by rw [InfiniteBoundaryDartIndex.dart_eq]; rfl

/-- Helper toward Definition 3.2: the cyclic word has UL followed by LR, skipping empty runs. -/
theorem positionOrder :
    FiniteBoundaryPositionOrder4 presentation (fun d => (d.1, !d.2)) := by
  refine ⟨2, position, ?_, Or.inr ⟨0, ?_, ?_⟩⟩
  · intro i j
    rcases index_cases i with rfl | rfl <;>
      rcases index_cases j with rfl | rfl <;>
      simp only [dart_upperLeft, dart_lowerRight] <;>
      dsimp [position, boundaryCycleSucc4] <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [position, sideTag, boundaryCycleOffset4] at *
  · intro i j
    rcases index_cases i with rfl | rfl <;>
      rcases index_cases j with rfl | rfl <;>
      dsimp [sideNext, sideTag, position, presentation, presentSide, boundaryCycleOffset4] <;> decide

/-- Helper toward Definition 3.2: the successor joins and all skipped endpoint labels agree. -/
theorem joinLabels : RequiredFiniteBoundaryJoinEndpointLabels7 presentation
    (fun d => (d.1, !d.2)) := by
  constructor
  · intro _ i j hij _
    rcases index_cases i with rfl | rfl <;>
      rcases index_cases j with rfl | rfl <;>
      simp only [dart_upperLeft, dart_lowerRight] at hij
    all_goals try simp only [Prod.mk.injEq, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, Bool.true_eq_false, and_false] at hij
    all_goals
      refine ⟨?_, ?_, ?_⟩
      · first | rw [dart_upperLeft] | rw [dart_lowerRight]
        rw [boundaryDartTerminal_eq]
        rfl
      · first | rw [dart_upperLeft] | rw [dart_lowerRight]
        rw [boundaryDartTerminal_eq]
        rfl
      · intro k hk hk'
        fin_cases k <;>
          norm_num [sideDistance, sideTag, sideInitialVertex?, sideTerminalVertex?,
            presentation, presentSide, emptySide, dart_upperLeft, dart_lowerRight,
            boundaryDartTerminal_eq, map] at *
  · intro h
    exact (h ⟨⟨()⟩, ⟨()⟩⟩).elim

/-- Helper toward Definition 3.2: the endpoint-ray construction satisfies every finite v7 clause. -/
theorem isBoundEdges32 : IsBoundEdges32 map boundary drawing face (fun d => (d.1, !d.2)) := by
  let : IsEmpty presentation.upperRight.Index := ⟨fun i => by change Empty at i; cases i⟩
  let : IsEmpty presentation.lowerLeft.Index := ⟨fun i => by change Empty at i; cases i⟩
  apply (IsBoundEdges32.finite_iff (Set.toFinite _)).mpr
  refine ⟨?_, suppliedFiniteJunctionLabels6_of_none rfl⟩
  change FiniteExternalFaceIntervalCore7 map presentation drawing face _
  refine ⟨boundaryOrder, ?_, ?_, geometricExternalFaceSucc, ulOkInf,
    UROkInf_of_isEmpty presentation, lrOkInf, LLOkInf_of_isEmpty presentation,
    presentSide_simple true, presentSide_simple false,
    presentSide_endpointLabels true, emptySide_endpointLabels (endpoint false),
    presentSide_endpointLabels false, emptySide_endpointLabels (endpoint true),
    positionOrder, ?_, fun _ => joinLabels⟩
  · intro d
    constructor
    · intro _
      rcases d with ⟨⟨⟩, b⟩
      cases b
      · exact ⟨.lowerRight (), by rw [InfiniteBoundaryDartIndex.dart_eq]; rfl⟩
      · exact ⟨.upperLeft (), by rw [InfiniteBoundaryDartIndex.dart_eq]; rfl⟩
    · intro _
      exact dartBorders d
  · intro i j hij
    rcases index_cases i with rfl | rfl <;>
      rcases index_cases j with rfl | rfl <;>
      simp only [dart_upperLeft, dart_lowerRight] at hij
    all_goals first | rfl | exact (Bool.false_ne_true (congrArg Prod.snd hij)).elim |
      exact (Bool.false_ne_true (congrArg Prod.snd hij).symm).elim
  · intro i j hij
    rcases index_cases i with rfl | rfl <;>
      rcases index_cases j with rfl | rfl <;>
      simp only [dart_upperLeft, dart_lowerRight] at hij ⊢
    all_goals first | exact (Bool.false_ne_true (congrArg Prod.snd hij)).elim |
      exact (Bool.false_ne_true (congrArg Prod.snd hij).symm).elim |
      rw [boundaryDartTerminal_eq, boundaryDartInitial_eq]; rfl

/-- Helper toward Definition 3.2: every neighborhood of the closed forward
arc contains nonincident vertex positions outside all arc images. -/
theorem not_local_image (N : Set ℂ) (hN : IsOpen N)
    (harc : Set.range (drawing.arc ((), true)).toPath ⊆ N) :
    ¬ (∀ z, z ∈ drawing.image → z ∈ N → z ∈ ⋃ d, (drawing.arc d).image) := by
  intro hcover
  have hzero : (0 : ℂ) ∈ N := harc ⟨0, by
    change Path.segment (0 : ℂ) 1 0 = 0
    exact Path.source _⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN 0 hzero
  let z : ℂ := ((-r / 2 : ℝ) : ℂ)
  have hzimage : z ∈ drawing.image :=
    Or.inl ⟨⟨z, Or.inr ⟨by simp [z], by change -r / 2 ≤ 0; linarith⟩⟩, rfl⟩
  have hzN : z ∈ N := by
    apply hball
    change dist z 0 < r
    simpa [z, dist_eq_norm, abs_of_pos hr] using half_lt_self hr
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (hcover z hzimage hzN)
  have hre := (Definition32Rectangle.arc_re hd).1
  change 0 ≤ -r / 2 at hre
  linarith only [hr, hre]

/-- coverage at zero, even though the full finite v7 predicate holds. -/
theorem not_isLocallyArcCovered32 : ¬ IsLocallyArcCovered32 map boundary drawing := by
  intro hlocal
  obtain ⟨N, hN, harc, hcover⟩ := hlocal.1 ()
  exact not_local_image N hN harc hcover

/-- Helper toward Definition 3.2: an explicit counterexample to deriving
local coverage from the full `IsBoundEdges32` predicate. -/
theorem isBoundEdges32_and_not_isLocallyArcCovered32 :
    IsBoundEdges32 map boundary drawing face (fun d => (d.1, !d.2)) ∧
      ¬ IsLocallyArcCovered32 map boundary drawing :=
  ⟨isBoundEdges32, not_isLocallyArcCovered32⟩

end Definition32EndpointRay













































































end DirectedDistances.PlanarMap

end
