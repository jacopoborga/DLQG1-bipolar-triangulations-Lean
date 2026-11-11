/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Counterexample

/-! # A bounded isolated-vertex obstruction to propagation along a dart

The geometric external successor does not by itself propagate an initial
left wedge along an entire arc. The construction below has both endpoint
wedges in the same unbounded complementary component, but an interior arc
point is not in its closure. This is not a full `IsBoundEdges32` instance. -/

public section

universe uUL uUR uLR uLL

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace Definition32Rectangle

/-- Helper toward Definition 3.2: isolated vertices occupy a bounded open
rectangle off the real axis, together with the two edge endpoints. -/
@[expose] def vertices : Set ℂ :=
  {z | z = 0 ∨ z = 1 ∨
    (1 / 2 < z.re ∧ z.re < 3 / 4 ∧ -1 < z.im ∧ z.im < 1 ∧ z.im ≠ 0)}

/-- Helper toward Definition 3.2: endpoints of the two opposite darts. -/
@[expose] def endpoint (b : Bool) : vertices :=
  if b then ⟨0, Or.inl rfl⟩ else ⟨1, Or.inr (Or.inl rfl)⟩

/-- Helper toward Definition 3.2: the endpoint assignment is injective. -/
theorem endpoint_injective : Function.Injective endpoint := by
  intro b c h
  have hv := congrArg Subtype.val h
  cases b <;> cases c
  · rfl
  · exact (one_ne_zero (show (1 : ℂ) = 0 from hv)).elim
  · exact (zero_ne_one (show (0 : ℂ) = 1 from hv)).elim
  · rfl

/-- Helper toward Definition 3.2: the literal map drawn by the rectangle
construction, with its sole edge present and directed from zero to one. -/
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
    have him : v.val.im = 0 := by
      rw [← heq]
      simp [Path.segment_apply, AffineMap.lineMap_apply_module]
    rcases v.property with hzero | hone | hrect
    · have h := congrArg Complex.re heq
      simp [Path.segment_apply, AffineMap.lineMap_apply_module, hzero] at h
      exact (ne_of_gt ht.1) (congrArg Subtype.val h)
    · have h := congrArg Complex.re heq
      simp [Path.segment_apply, AffineMap.lineMap_apply_module, hone] at h
      exact (ne_of_lt ht.2) (congrArg Subtype.val h)
    · exact hrect.2.2.2.2 him
  missing := fun _ => False
  missing_on_external := by intro _ h; exact h.elim
  forward := fun _ => true

/-- Helper toward Definition 3.2: the literal map has the required
dart-initial assignment. -/
theorem initial_eq_endpoint (d : Unit × Bool) :
    boundaryDartInitial map d = endpoint d.2 := by
  rw [boundaryDartInitial_eq]
  cases d.2 <;> rfl

/-- Helper toward Definition 3.2: the two darts of one straight edge,
with isolated vertices unconstrained by dart local finiteness. -/
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
    rcases v.property with hzero | hone | hrect
    · apply hv.2
      cases d.2 <;>
        simp [Definition32Strip.arc, Polyline.start, Polyline.finish, hzero]
    · apply hv.2
      cases d.2 <;>
        simp [Definition32Strip.arc, Polyline.start, Polyline.finish, hone]
    · exact hrect.2.2.2.2 him
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

/-- Helper toward Definition 3.2: an upper-left corridor avoids the blob. -/
@[expose] def upperLeft : Set ℂ := {z | z.re < 1 / 2 ∧ 0 < z.im}

/-- Helper toward Definition 3.2: a corridor above the bounded blob. -/
@[expose] def top : Set ℂ := {z | 1 < z.im}

/-- Helper toward Definition 3.2: a corridor to the right of the edge. -/
@[expose] def right : Set ℂ := {z | 1 < z.re}

/-- Helper toward Definition 3.2: a lower-right corridor at the reverse start. -/
@[expose] def lowerRight : Set ℂ := {z | 3 / 4 < z.re ∧ z.im < 0}

/-- Helper toward Definition 3.2: the four corridors form a connected detour. -/
@[expose] def corridor : Set ℂ := ((upperLeft ∪ top) ∪ right) ∪ lowerRight

/-- Helper toward Definition 3.2: the detour is preconnected. -/
theorem corridor_isPreconnected : IsPreconnected corridor := by
  have hu : Convex ℝ upperLeft :=
    ((convex_Iio (1 / 2 : ℝ)).linear_preimage Complex.reLm).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)
  have ht : Convex ℝ top :=
    (convex_Ioi (1 : ℝ)).linear_preimage Complex.imLm
  have hr : Convex ℝ right :=
    (convex_Ioi (1 : ℝ)).linear_preimage Complex.reLm
  have hl : Convex ℝ lowerRight :=
    ((convex_Ioi (3 / 4 : ℝ)).linear_preimage Complex.reLm).inter
      ((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm)
  have hut : IsPreconnected (upperLeft ∪ top) :=
    hu.isPreconnected.union (2 * Complex.I) (by norm_num [upperLeft])
      (by norm_num [top]) ht.isPreconnected
  have hutr : IsPreconnected ((upperLeft ∪ top) ∪ right) :=
    hut.union (2 + 2 * Complex.I) (Or.inr (by norm_num [top]))
      (by norm_num [right]) hr.isPreconnected
  exact hutr.union (2 - Complex.I)
    (Or.inr (by norm_num [right])) (by norm_num [lowerRight]) hl.isPreconnected

/-- Helper toward Definition 3.2: every point on an edge has real part
between zero and one. -/
theorem arc_re {b : Bool} {z : ℂ} (hz : z ∈ (Definition32Strip.arc b).image) :
    0 ≤ z.re ∧ z.re ≤ 1 := by
  rw [← Polyline.range_toPath] at hz
  obtain ⟨t, rfl⟩ := hz
  cases b
  · change 0 ≤ ((Path.segment (1 : ℂ) 0) t).re ∧
      ((Path.segment (1 : ℂ) 0) t).re ≤ 1
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module]
    simp only [Complex.add_re, Complex.smul_re, Complex.one_re, Complex.zero_re,
      smul_eq_mul, mul_one, mul_zero, add_zero]
    constructor <;> linarith only [t.property.1, t.property.2]
  · change 0 ≤ ((Path.segment (0 : ℂ) 1) t).re ∧
      ((Path.segment (0 : ℂ) 1) t).re ≤ 1
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.add_re, Complex.smul_re, Complex.one_re, Complex.zero_re,
      smul_eq_mul, mul_one, mul_zero, zero_add]
    constructor <;> linarith only [t.property.1, t.property.2]

/-- Helper toward Definition 3.2: the connected detour avoids the full image. -/
theorem corridor_subset_compl : corridor ⊆ drawing.imageᶜ := by
  intro z hz himage
  rcases himage with ⟨v, rfl⟩ | ⟨d, hd⟩
  · change v.val ∈ corridor at hz
    rcases v.property with hv | hv | hv
    · rcases hz with ((hz | hz) | hz) | hz <;>
        norm_num [upperLeft, top, right, lowerRight, hv] at hz
    · rcases hz with ((hz | hz) | hz) | hz <;>
        norm_num [upperLeft, top, right, lowerRight, hv] at hz
    · rcases hz with ((hz | hz) | hz) | hz
      · exact (not_lt_of_ge hz.1.le) hv.1
      · exact (not_lt_of_ge hz.le) hv.2.2.2.1
      · change 1 < v.val.re at hz
        linarith only [hz, hv.2.1]
      · exact (not_lt_of_ge hz.1.le) hv.2.1
  · have him := Definition32Strip.arc_im hd
    have hre := arc_re hd
    rcases hz with ((hz | hz) | hz) | hz
    · exact (ne_of_gt hz.2) him
    · change 1 < z.im at hz
      linarith only [him, hz]
    · change 1 < z.re at hz
      linarith only [hre.2, hz]
    · exact (ne_of_lt hz.2) him

/-- Helper toward Definition 3.2: the component containing the detour. -/
@[expose] def face : drawing.Face :=
  ⟨connectedComponentIn drawing.imageᶜ (2 * Complex.I),
    2 * Complex.I, corridor_subset_compl
      (Or.inl (Or.inl (Or.inr (by norm_num [top])))), rfl⟩

/-- Helper toward Definition 3.2: the whole connected detour is in one face. -/
theorem corridor_subset_face : corridor ⊆ face.val :=
  corridor_isPreconnected.subset_connectedComponentIn
    (Or.inl (Or.inl (Or.inr (by norm_num [top])))) corridor_subset_compl

/-- Helper toward Definition 3.2: the forward initial left wedge is in the face. -/
theorem forward_dartBorders : drawing.dartBorders ((), true) face := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro t ε ht htδ hε _
  apply corridor_subset_face
  apply Or.inl ∘ Or.inl ∘ Or.inl
  have heq : (drawing.arc ((), true)).start + (t : ℂ) *
      ((drawing.arc ((), true)).initialDirection +
        (ε : ℂ) * Complex.I * (drawing.arc ((), true)).initialDirection) =
      (t : ℂ) * (1 + (ε : ℂ) * Complex.I) := by
    simp [drawing, Definition32Strip.arc, Polyline.start,
      Polyline.initialDirection, Polyline.point]
  rw [heq]
  constructor
  · change ((t : ℂ) * (1 + (ε : ℂ) * Complex.I)).re < 1 / 2
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, mul_one, add_zero]
    linarith only [htδ]
  · simpa using mul_pos ht hε

/-- Helper toward Definition 3.2: unlike the infinite strip, this example
also has the reverse initial left wedge in the very same face. -/
theorem reverse_dartBorders : drawing.dartBorders ((), false) face := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro t ε ht htδ hε _
  apply corridor_subset_face
  apply Or.inr
  have heq : (drawing.arc ((), false)).start + (t : ℂ) *
      ((drawing.arc ((), false)).initialDirection +
        (ε : ℂ) * Complex.I * (drawing.arc ((), false)).initialDirection) =
      1 + (t : ℂ) * (-1 + (ε : ℂ) * Complex.I * -1) := by
    simp [drawing, Definition32Strip.arc, Polyline.start,
      Polyline.initialDirection, Polyline.point]
  rw [heq]
  constructor
  · change 3 / 4 < (1 + (t : ℂ) * (-1 + (ε : ℂ) * Complex.I * -1)).re
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.neg_re, mul_zero,
      zero_mul, sub_zero, mul_neg, mul_one, add_zero, neg_zero]
    linarith only [htδ]
  · simpa using neg_neg_of_pos (mul_pos ht hε)

/-- Helper toward Definition 3.2: every dart borders the chosen face. -/
theorem dartBorders (d : Unit × Bool) : drawing.dartBorders d face := by
  rcases d with ⟨⟨⟩, b⟩
  cases b
  · exact reverse_dartBorders
  · exact forward_dartBorders

/-- Helper toward Definition 3.2: the detour face is unbounded. -/
theorem face_isUnbounded : drawing.IsUnbounded face := by
  intro R
  let y : ℝ := |R| + 2
  have hy : 0 < y := by dsimp [y]; positivity
  refine ⟨(y : ℂ) * Complex.I, corridor_subset_face ?_, ?_⟩
  · apply Or.inl ∘ Or.inl ∘ Or.inr
    change 1 < ((y : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    dsimp [y]
    linarith only [abs_nonneg R]
  · simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hy] using
      (lt_add_of_le_of_pos (le_abs_self R) (by norm_num : (0 : ℝ) < 2))

/-- Helper toward Definition 3.2: the exact geometric external successor
condition holds, with the successor flipping the two darts. -/
theorem geometricExternalFaceSucc :
    IsGeometricExternalFaceSucc drawing face (fun d => (d.1, !d.2)) := by
  exact ⟨face_isUnbounded, fun d _ => ⟨rfl, dartBorders _⟩⟩

/-- Helper toward Definition 3.2: an open rectangle around an interior
arc point is entirely part of the drawing image. -/
theorem rectangle_subset_image {z : ℂ}
    (hz : 1 / 2 < z.re ∧ z.re < 3 / 4 ∧ -1 < z.im ∧ z.im < 1) :
    z ∈ drawing.image := by
  by_cases him : z.im = 0
  · right
    refine ⟨((), true), ?_⟩
    rw [← Polyline.range_toPath]
    refine ⟨⟨z.re, by constructor <;> linarith only [hz.1, hz.2.1]⟩, ?_⟩
    change Path.segment (0 : ℂ) 1 _ = z
    apply Complex.ext <;>
      simp [Path.segment_apply, AffineMap.lineMap_apply_module, him]
  · exact Or.inl ⟨⟨z, Or.inr (Or.inr
      ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2, him⟩)⟩, rfl⟩

/-- Helper toward Definition 3.2: the literal map and the PL drawing have
exactly the same image; the reverse dart does not add geometric points. -/
theorem map_image_eq : (Drawing map).image = drawing.image := by
  have harc (b : Bool) :
      Set.range (Definition32Strip.arc b).toPath =
        Set.range (Path.segment (0 : ℂ) 1) := by
    cases b
    · change Set.range (Path.segment (1 : ℂ) 0) = _
      rw [Path.range_segment, Path.range_segment, segment_symm]
    · rfl
  ext z
  change (z ∈ Set.range Subtype.val ∨ z ∈ ⋃ _ : Unit,
      Set.range (Path.segment (0 : ℂ) 1)) ↔
    z ∈ Set.range Subtype.val ∨ ∃ d : Unit × Bool,
      z ∈ (Definition32Strip.arc d.2).image
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · obtain ⟨_, ht⟩ := Set.mem_iUnion.mp hz
      exact Or.inr ⟨((), true), (Polyline.range_toPath _ ▸ ht)⟩
  · rintro (hz | ⟨d, hd⟩)
    · exact Or.inl hz
    · right
      apply Set.mem_iUnion.mpr
      refine ⟨(), ?_⟩
      rw [← harc d.2, Polyline.range_toPath]
      exact hd

/-- Helper toward Definition 3.2: no complementary face of the literal
map can approach the obstructed interior edge point. -/
theorem fiveEighths_not_mem_mapFace_closure (F : (Drawing map).Face) :
    (5 / 8 : ℂ) ∉ closure F.val := by
  let N : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 3 / 4 ∧ -1 < z.im ∧ z.im < 1}
  have hN : IsOpen N :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hsub : F.val ⊆ Nᶜ := by
    intro z hz hrect
    apply (Drawing map).face_subset_compl_image F hz
    rw [map_image_eq]
    exact rectangle_subset_image hrect
  have hclosure := closure_minimal hsub hN.isClosed_compl
  intro h
  exact hclosure h (by norm_num [N])

/-- Helper toward Definition 3.2: the face does not accumulate at the
interior edge point five eighths, despite bordering both darts. -/
theorem fiveEighths_not_mem_closure : (5 / 8 : ℂ) ∉ closure face.val := by
  let N : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 3 / 4 ∧ -1 < z.im ∧ z.im < 1}
  have hN : IsOpen N :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hsub : face.val ⊆ Nᶜ := by
    intro z hz hrect
    exact drawing.face_subset_compl face hz (rectangle_subset_image hrect)
  have hclosure := closure_minimal hsub hN.isClosed_compl
  intro h
  exact hclosure h (by norm_num [N])

/-- Helper toward Definition 3.2: the specified interior parameter. -/
@[expose] def fiveEighths : {t : I // t ∈ openParams} :=
  ⟨⟨5 / 8, by norm_num⟩, by
    change 0 < (5 / 8 : ℝ) ∧ (5 / 8 : ℝ) < 1
    norm_num⟩

/-- Helper toward Definition 3.2: evaluation at the obstructed parameter. -/
theorem toPath_fiveEighths :
    (drawing.arc ((), true)).toPath fiveEighths.val = (5 / 8 : ℂ) := by
  change Path.segment (0 : ℂ) 1 fiveEighths.val = _
  simp [Path.segment_apply, AffineMap.lineMap_apply_module, fiveEighths]

/-- Helper toward Definition 3.2: the all-parameter left winding test
fails even with the exact geometric external successor condition. -/
theorem not_leftAtOn_fiveEighths :
    ¬ LeftAtOn face.val (drawing.arc ((), true)).toPath fiveEighths := by
  intro h
  have hc := leftAtOn_mem_closure face.val (drawing.arc ((), true)).toPath
    fiveEighths h
  rw [toPath_fiveEighths] at hc
  exact fiveEighths_not_mem_closure hc

/-- Helper toward Definition 3.2: the right winding test fails at the
same obstructed point, since it also requires closure incidence. -/
theorem not_rightAtOn_fiveEighths :
    ¬ RightAtOn face.val (drawing.arc ((), true)).toPath fiveEighths := by
  rintro ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩
  have hsubset :
      {w : ℂ | w ∈ face.val ∧ HasWinding
        ((edgeSubarc (drawing.arc ((), true)).toPath a b
          (le_of_lt (lt_trans has hsb))).trans q) w (-1)} ⊆ face.val := by
    intro w hw
    exact hw.1
  have hc := closure_mono hsubset hcl
  rw [toPath_fiveEighths] at hc
  exact fiveEighths_not_mem_closure hc

/-- Helper toward Definition 3.2: no open neighborhood of the obstructed
point satisfies the local vertex-coverage premise, even though both darts
border the same face and the geometric successor condition holds. -/
theorem not_local_vertex_coverage (N : Set ℂ) (hN : IsOpen N)
    (hpoint : (5 / 8 : ℂ) ∈ N) :
    ¬ (∀ z, z ∈ Set.range drawing.pos → z ∈ N →
      z ∈ ⋃ d, (drawing.arc d).image) := by
  intro hcover
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN (5 / 8 : ℂ) hpoint
  let y : ℝ := min r 1 / 2
  have hy : 0 < y := half_pos (lt_min hr zero_lt_one)
  have hyr : y < r := by
    have hle := min_le_left r (1 : ℝ)
    dsimp [y]
    linarith only [hle, hr]
  have hy1 : y < 1 := by
    have hle := min_le_right r (1 : ℝ)
    dsimp [y]
    linarith only [hle]
  let z : ℂ := 5 / 8 + (y : ℂ) * Complex.I
  have hzre : z.re = 5 / 8 := by simp [z]
  have hzim : z.im = y := by simp [z]
  have hzvertex : z ∈ Set.range drawing.pos := by
    refine ⟨⟨z, Or.inr (Or.inr ?_)⟩, rfl⟩
    refine ⟨by rw [hzre]; norm_num, by rw [hzre]; norm_num, ?_, ?_, ?_⟩
    · rw [hzim]; linarith only [hy]
    · rwa [hzim]
    · rw [hzim]; exact hy.ne'
  have hzN : z ∈ N := by
    apply hball
    change dist z (5 / 8 : ℂ) < r
    simpa [z, dist_eq_norm, abs_of_pos hy] using hyr
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (hcover z hzvertex hzN)
  have him := Definition32Strip.arc_im hd
  rw [hzim] at him
  exact hy.ne' him

/-- Helper toward Definition 3.2: the literal map has no left face along
the entire edge, even though the PL geometric successor exists. -/
theorem not_leftOf (F : (Drawing map).Face) (hp : ¬ map.toPlaneMapWithMissing.missing ()) :
    ¬ LeftOf map F ⟨(), hp⟩ := by
  intro h
  have hs : LeftAtOn F.val (orientedArc map ⟨(), hp⟩) fiveEighths := h fiveEighths
  have hc := leftAtOn_mem_closure F.val (orientedArc map ⟨(), hp⟩) fiveEighths hs
  have heval : orientedArc map ⟨(), hp⟩ fiveEighths.val = (5 / 8 : ℂ) := by
    change Path.segment (0 : ℂ) 1 fiveEighths.val = _
    simp [Path.segment_apply, AffineMap.lineMap_apply_module, fiveEighths]
  rw [heval] at hc
  exact fiveEighths_not_mem_mapFace_closure F hc

/-- Helper toward Definition 3.2: the bounded-rectangle candidate cannot
be completed to exact v7 using its literal map. Unlike the strip, the
obstruction here is the map-side `ULOkInf` clause, not the geometric successor. -/
theorem not_isBoundEdges32
    (B : BoundaryPresentationWithJunctions.{0, 0, uUL, uUR, uLR, uLL} map)
    (S : Unit × Bool → Unit × Bool) :
    ¬ IsBoundEdges32 map B drawing face S := by
  intro h
  have hmem : () ∈ upperLeftBoundary32 B :=
    (mem_upperLeftBoundary32_iff_forward_dartBorders h ()).mpr
      ⟨by intro hmissing; exact hmissing, forward_dartBorders⟩
  obtain ⟨i, _⟩ := hmem
  obtain ⟨hp, _, F, _, hleft⟩ :=
    ((ULOkInf_iff B.presentation).mp h.presentation_facts.2.1).1 i
  exact not_leftOf F hp hleft

end Definition32Rectangle

/-- Helper toward Definition 3.2: geometric successor closure, even with
every dart bordering the one unbounded face, does not imply the winding
test along every open parameter. This does not refute exact v7. -/
theorem not_forall_geometricExternalFaceSucc_toPath_leftAtOn :
    ¬ (∀ (V E : Type) (M : DirectedPlaneMapWithMissing V E)
      (rot : Equiv.Perm (E × Bool))
      (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M))
      (U : G.Face) (S : E × Bool → E × Bool),
      IsGeometricExternalFaceSucc G U S →
      (∀ d, G.dartBorders d U) →
      ∀ (d : E × Bool) (s : {t : I // t ∈ openParams}),
        LeftAtOn U.val (G.arc d).toPath s) := by
  intro h
  exact Definition32Rectangle.not_leftAtOn_fiveEighths
    (h _ _ Definition32Rectangle.map _ Definition32Rectangle.drawing
      Definition32Rectangle.face _ Definition32Rectangle.geometricExternalFaceSucc
      Definition32Rectangle.dartBorders ((), true) Definition32Rectangle.fiveEighths)
























































































end DirectedDistances.PlanarMap

end
