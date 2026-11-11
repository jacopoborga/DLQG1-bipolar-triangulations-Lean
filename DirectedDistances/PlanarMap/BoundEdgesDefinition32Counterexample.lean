/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact
public import DirectedDistances.PlanarMap.PLDrawingWindingSides

/-! # Testing the strip obstruction against the exact Definition 3.2 predicate

They do not establish either exact winding-side equivalence. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: both v7 branches retain the geometric
external-face successor clause. -/
theorem IsBoundEdges32.geometricExternalFaceSucc
    {V : Type uV} {E : Type uE}
    {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S) : IsGeometricExternalFaceSucc G U S := by
  rcases h with ⟨_, hcore, _⟩ | ⟨_, _, h3⟩
  · exact hcore.2.2.2.1
  · exact h3.1.1.2.2.1

/-- Helper toward Definition 3.2: at a fixed rotation, a bordering dart's
reversal must border the same external face under the geometric successor
clause. This is a necessary condition, not an extra source premise. -/
theorem PLDrawing.dartBorders_flip_of_geometricExternalFaceSucc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (F : P.Face) (S : D → D)
    (h : IsGeometricExternalFaceSucc P F S) (d : D)
    (hrot : rot (flip d) = flip d) (hd : P.dartBorders d F) :
    P.dartBorders (flip d) F := by
  have hs := h.2 d hd
  have hfixed : rot.symm (flip d) = flip d := by
    apply rot.injective
    rw [rot.apply_symm_apply, hrot]
  rw [hs.1, hfixed] at hs
  exact hs.2

/-- Helper toward Definition 3.2: exact v7 data cannot have a bordering dart
whose reversed dart is excluded when rotation fixes that reversed dart. -/
theorem not_isBoundEdges32_of_dartBorders_not_flip
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) (d : E × Bool)
    (hrot : rot (d.1, !d.2) = (d.1, !d.2))
    (hd : G.dartBorders d U) (hflip : ¬ G.dartBorders (d.1, !d.2) U) :
    ¬ IsBoundEdges32 M B G U S := by
  intro h
  exact hflip (G.dartBorders_flip_of_geometricExternalFaceSucc U S
    h.geometricExternalFaceSucc d hrot hd)

/-- Helper toward Definition 3.2: a simple PL dart has different initial
and terminal vertices, even in the presence of isolated vertices. -/
theorem PLDrawing.vert_flip_ne
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) : vert (flip d) ≠ vert d := by
  intro hv
  have heq : (P.arc d).start = (P.arc d).finish := by
    rw [P.arc_start, P.arc_finish, hv]
  have hp : (P.arc d).toPath 0 = (P.arc d).toPath 1 :=
    (Path.source _).trans (heq.trans (Path.target _).symm)
  have ht := ((P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d)) hp
  exact (zero_ne_one : (0 : I) ≠ 1) ht

/-- Helper toward Definition 3.2: the geometric external successor cannot
fix a bordering dart, since rotation preserves its initial vertex. -/
theorem PLDrawing.geometricExternalFaceSucc_ne_self
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (F : P.Face) (S : D → D)
    (h : IsGeometricExternalFaceSucc P F S) (d : D)
    (hd : P.dartBorders d F) : S d ≠ d := by
  intro hs
  have heq := (h.2 d hd).1
  rw [hs] at heq
  have hrot : rot d = flip d := by
    exact (congrArg rot heq).trans (rot.apply_symm_apply _)
  exact P.vert_flip_ne d ((congrArg vert hrot).symm.trans (P.vert_rotation d))

/-- Helper toward Definition 3.2: listing only one boundary dart cannot
satisfy exact v7, independently of the finite endpoint-label conventions. -/
theorem not_isBoundEdges32_of_single_boundary_dart
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    [Subsingleton (InfiniteBoundaryDartIndex B.presentation)]
    [Nonempty (InfiniteBoundaryDartIndex B.presentation)]
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool) :
    ¬ IsBoundEdges32 M B G U S := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty (InfiniteBoundaryDartIndex B.presentation)›
  have hcover := h.presentation_facts.1
  have hi := (hcover _).mpr ⟨i, rfl⟩
  have hgeom := h.geometricExternalFaceSucc
  obtain ⟨j, hj⟩ := (hcover _).mp ((hgeom.2 _ hi).2)
  have hji : j = i := Subsingleton.elim _ _
  rw [hji] at hj
  exact G.geometricExternalFaceSucc_ne_self U S hgeom _ hi hj.symm

namespace Definition32Strip

/-- Helper toward Definition 3.2: the isolated vertices fill the entire
off-axis strip, in addition to the endpoints of the single geometric edge. -/
@[expose] def vertices : Set ℂ :=
  {z | z = 0 ∨ z = 1 ∨ (1 / 2 < z.re ∧ z.re < 1 ∧ z.im ≠ 0)}

/-- Helper toward Definition 3.2: the true dart starts at zero; the false
dart starts at one. -/
@[expose] def endpoint (b : Bool) : vertices :=
  if b then ⟨0, Or.inl rfl⟩ else ⟨1, Or.inr (Or.inl rfl)⟩

/-- Helper toward Definition 3.2: the two endpoint vertices are distinct. -/
theorem endpoint_injective : Function.Injective endpoint := by
  intro b c h
  have hv := congrArg Subtype.val h
  cases b <;> cases c
  · rfl
  · exact (one_ne_zero (show (1 : ℂ) = 0 from hv)).elim
  · exact (zero_ne_one (show (0 : ℂ) = 1 from hv)).elim
  · rfl

/-- Helper toward Definition 3.2: a single present edge, with all the strip
points retained as isolated geometric vertices. -/
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
    rcases v.property with hzero | hone | hstrip
    · have h := congrArg Complex.re heq
      simp [Path.segment_apply, AffineMap.lineMap_apply_module, hzero] at h
      exact (ne_of_gt ht.1) (congrArg Subtype.val h)
    · have h := congrArg Complex.re heq
      simp [Path.segment_apply, AffineMap.lineMap_apply_module, hone] at h
      exact (ne_of_lt ht.2) (congrArg Subtype.val h)
    · exact hstrip.2.2 him
  missing := fun _ => False
  missing_on_external := by intro _ h; exact h.elim
  forward := fun _ => true

/-- Helper toward Definition 3.2: the stored map endpoints agree with the
Boolean endpoint convention of the PL drawing. -/
theorem initial_eq_endpoint (d : Unit × Bool) :
    boundaryDartInitial map d = endpoint d.2 := by
  rw [boundaryDartInitial_eq]
  cases d.2 <;> rfl

/-- Helper toward Definition 3.2: the two opposite straight polylines. -/
@[expose] def arc : Bool → Polyline
  | true => ⟨[0, 1], by simp⟩
  | false => ⟨[1, 0], by simp⟩

/-- Helper toward Definition 3.2: both dart images lie on the real axis. -/
theorem arc_im {b : Bool} {z : ℂ} (hz : z ∈ (arc b).image) : z.im = 0 := by
  rw [← Polyline.range_toPath] at hz
  obtain ⟨t, rfl⟩ := hz
  cases b
  · change ((Path.segment (1 : ℂ) 0) t).im = 0
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  · change ((Path.segment (0 : ℂ) 1) t).im = 0
    simp [Path.segment_apply, AffineMap.lineMap_apply_module]

/-- Helper toward Definition 3.2: the strip example uses the exact dart
carrier and initial-vertex map required by `IsBoundEdges32`. -/
@[expose] def drawing :
    PLDrawing (Unit × Bool) vertices (fun d => (d.1, !d.2))
      (Equiv.refl (Unit × Bool)) (boundaryDartInitial map) where
  flip_involutive := by rintro ⟨e, b⟩; cases b <;> rfl
  flip_ne := by rintro ⟨e, b⟩; cases e; cases b <;> decide
  vert_rotation := fun _ => rfl
  pos := Subtype.val
  pos_injective := Subtype.val_injective
  arc := fun d => arc d.2
  arc_simple := by
    intro d
    have hf : (arc true).IsSimple := by
      apply Polyline.isSimple_of_XMonotone
      · simp [Polyline.XMonotone, arc]
      · norm_num [arc]
    cases d.2
    · exact Polyline.isSimple_reverse_transfer _ hf
    · exact hf
  arc_length := by intro d; cases d.2 <;> norm_num [arc]
  arc_start := by
    intro d
    rw [initial_eq_endpoint]
    cases d.2 <;> rfl
  arc_finish := by
    intro d
    rw [initial_eq_endpoint]
    cases d.2 <;> rfl
  arc_flip := by intro d; cases d.2 <;> rfl
  interior_disjoint := by
    rintro ⟨e, b⟩ ⟨f, c⟩ hne hflip
    cases e; cases f; cases b <;> cases c <;> simp_all
  interior_avoids_vertices := by
    intro d v hv
    have him := arc_im hv.1
    rcases v.property with hzero | hone | hstrip
    · apply hv.2
      cases d.2 <;> simp [arc, Polyline.start, Polyline.finish, hzero]
    · apply hv.2
      cases d.2 <;> simp [arc, Polyline.start, Polyline.finish, hone]
    · exact hstrip.2.2 him
  locally_finite := fun _ _ => Set.toFinite _
  initial_nonzero := by
    intro d
    cases d.2 <;> norm_num [arc, Polyline.initialDirection,
      Polyline.point, Polyline.start]
  initial_arg_injective := by
    intro d e h _
    apply Prod.ext (Subsingleton.elim _ _)
    apply endpoint_injective
    simpa only [initial_eq_endpoint] using h
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

/-- Helper toward Definition 3.2: every point of the open vertical strip
belongs to the drawing, including the real-axis part supplied by the edge. -/
theorem strip_subset_image {z : ℂ} (hz : 1 / 2 < z.re ∧ z.re < 1) :
    z ∈ drawing.image := by
  by_cases him : z.im = 0
  · right
    refine ⟨((), true), ?_⟩
    rw [← Polyline.range_toPath]
    refine ⟨⟨z.re, by constructor <;> linarith only [hz.1, hz.2]⟩, ?_⟩
    change Path.segment (0 : ℂ) 1 _ = z
    apply Complex.ext <;>
      simp [Path.segment_apply, AffineMap.lineMap_apply_module, him]
  · exact Or.inl ⟨⟨z, Or.inr (Or.inr ⟨hz.1, hz.2, him⟩)⟩, rfl⟩

/-- Helper toward Definition 3.2: the reverse dart has no initial left
wedge in any complementary face, since that wedge enters the filled strip. -/
theorem not_reverse_dartBorders (F : drawing.Face) :
    ¬ drawing.dartBorders ((), false) F := by
  rintro ⟨δ, hδ, hw⟩
  let t : ℝ := min δ (1 / 2) / 2
  have ht : 0 < t := half_pos (lt_min hδ (by norm_num))
  have htδ : t < δ := by
    have hle := min_le_left δ (1 / 2 : ℝ)
    dsimp [t]
    linarith only [hle, hδ]
  have htHalf : t < 1 / 2 := by
    have hle := min_le_right δ (1 / 2 : ℝ)
    dsimp [t]
    linarith only [hle]
  have hz := hw t (δ / 2) ht htδ (half_pos hδ) (by linarith only [hδ])
  apply drawing.face_subset_compl F hz
  apply strip_subset_image
  change 1 / 2 < ((drawing.arc ((), false)).start + (t : ℂ) *
      ((drawing.arc ((), false)).initialDirection +
        ((δ / 2 : ℝ) : ℂ) * Complex.I *
          (drawing.arc ((), false)).initialDirection)).re ∧ _
  norm_num [drawing, arc, Polyline.start, Polyline.initialDirection,
    Polyline.point]
  constructor <;> linarith only [ht, htHalf]

/-- Helper toward Definition 3.2: a convex region in the complement near
the forward dart's initial point. -/
@[expose] def upperLeft : Set ℂ := {z | z.re < 1 / 2 ∧ 0 < z.im}

/-- Helper toward Definition 3.2: the initial upper-left region is convex. -/
theorem upperLeft_convex : Convex ℝ upperLeft :=
  ((convex_Iio (1 / 2 : ℝ)).linear_preimage Complex.reLm).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)

/-- Helper toward Definition 3.2: the initial upper-left region avoids
both the geometric edge and every isolated vertex. -/
theorem upperLeft_subset_compl : upperLeft ⊆ drawing.imageᶜ := by
  intro z hz himage
  rcases himage with hvertex | ⟨d, hd⟩
  · obtain ⟨v, rfl⟩ := hvertex
    rcases v.property with hzero | hone | hstrip
    · have h := hz.2
      change 0 < v.val.im at h
      simp [hzero] at h
    · have h := hz.2
      change 0 < v.val.im at h
      simp [hone] at h
    · exact (not_lt_of_ge hz.1.le) hstrip.1
  · exact (ne_of_gt hz.2) (arc_im hd)

/-- Helper toward Definition 3.2: the complementary component containing
the initial upper-left region. -/
@[expose] def face : drawing.Face :=
  ⟨connectedComponentIn drawing.imageᶜ Complex.I,
    Complex.I, upperLeft_subset_compl (by norm_num [upperLeft]), rfl⟩

/-- Helper toward Definition 3.2: the convex region lies in this component. -/
theorem upperLeft_subset_face : upperLeft ⊆ face.val :=
  upperLeft_convex.isPreconnected.subset_connectedComponentIn
    (by norm_num [upperLeft]) upperLeft_subset_compl

/-- Helper toward Definition 3.2: the forward dart has an initial bordering
wedge in the chosen face, exactly as in the unrestricted strip example. -/
theorem forward_dartBorders : drawing.dartBorders ((), true) face := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro t ε ht htδ hε _
  apply upperLeft_subset_face
  have heq : (drawing.arc ((), true)).start + (t : ℂ) *
      ((drawing.arc ((), true)).initialDirection +
        (ε : ℂ) * Complex.I * (drawing.arc ((), true)).initialDirection) =
      (t : ℂ) * (1 + (ε : ℂ) * Complex.I) := by
    simp [drawing, arc, Polyline.start, Polyline.initialDirection, Polyline.point]
  rw [heq]
  constructor
  · change ((t : ℂ) * (1 + (ε : ℂ) * Complex.I)).re < 1 / 2
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, mul_one, add_zero]
    linarith only [htδ]
  · simpa using mul_pos ht hε

/-- Helper toward Definition 3.2: unboundedness does hold for the strip's
chosen face; it is the successor requirement that excludes this example. -/
theorem face_isUnbounded : drawing.IsUnbounded face := by
  intro R
  let y : ℝ := |R| + 1
  have hy : 0 < y := by dsimp [y]; positivity
  refine ⟨(y : ℂ) * Complex.I, upperLeft_subset_face ?_, ?_⟩
  · constructor
    · change ((y : ℂ) * Complex.I).re < 1 / 2
      norm_num
    · simpa using hy
  · simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hy] using
      (lt_add_of_le_of_pos (le_abs_self R) zero_lt_one)

/-- Helper toward Definition 3.2: the strip's forward-bordering face cannot
be part of any exact v7 boundary presentation, regardless of endpoint labels
or successor choices. The geometric successor clause already fails. -/
theorem not_isBoundEdges32
    (B : BoundaryPresentationWithJunctions.{0, 0, uUL, uUR, uLR, uLL} map)
    (S : Unit × Bool → Unit × Bool) :
    ¬ IsBoundEdges32 map B drawing face S := by
  exact not_isBoundEdges32_of_dartBorders_not_flip map B drawing face S
    ((), true) rfl forward_dartBorders (not_reverse_dartBorders face)

/-- Helper toward Definition 3.2: the later edge point at three quarters
cannot even be approached from the chosen face. -/
theorem threeQuarters_not_mem_closure : (3 / 4 : ℂ) ∉ closure face.val := by
  let N : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 1}
  have hN : IsOpen N :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsub : face.val ⊆ Nᶜ := by
    intro z hz hstrip
    exact drawing.face_subset_compl face hz (strip_subset_image hstrip)
  have hclosure := closure_minimal hsub hN.isClosed_compl
  intro h
  exact hclosure h (by norm_num [N])

/-- Helper toward Definition 3.2: the tested interior parameter is exactly
three quarters along the forward straight segment. -/
@[expose] def threeQuarters : {t : I // t ∈ openParams} :=
  ⟨⟨3 / 4, by norm_num⟩, by
    change 0 < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) < 1
    norm_num⟩

/-- Helper toward Definition 3.2: the forward path evaluates to the
obstructed point at the specified parameter. -/
theorem toPath_threeQuarters :
    (drawing.arc ((), true)).toPath threeQuarters.val = (3 / 4 : ℂ) := by
  change Path.segment (0 : ℂ) 1 threeQuarters.val = _
  simp [Path.segment_apply, AffineMap.lineMap_apply_module, threeQuarters]

/-- Helper toward Definition 3.2: the strip's initial-border example fails
the winding-side test, but is excluded by the exact v7 predicate. -/
theorem not_leftAtOn_threeQuarters :
    ¬ LeftAtOn face.val (drawing.arc ((), true)).toPath threeQuarters := by
  intro h
  have hc := leftAtOn_mem_closure face.val (drawing.arc ((), true)).toPath
    threeQuarters h
  rw [toPath_threeQuarters] at hc
  exact threeQuarters_not_mem_closure hc

/-- Helper toward Definition 3.2: no open neighborhood of the obstructed
edge point has the local vertex-coverage property used in `SidesExact`. -/
theorem not_local_vertex_coverage (N : Set ℂ) (hN : IsOpen N)
    (hpoint : (3 / 4 : ℂ) ∈ N) :
    ¬ (∀ z, z ∈ Set.range drawing.pos → z ∈ N →
      z ∈ ⋃ d, (drawing.arc d).image) := by
  intro hcover
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN (3 / 4 : ℂ) hpoint
  let z : ℂ := 3 / 4 + ((r / 2 : ℝ) : ℂ) * Complex.I
  have hzre : z.re = 3 / 4 := by simp [z]
  have hzim : z.im = r / 2 := by simp [z]
  have hzvertex : z ∈ Set.range drawing.pos := by
    refine ⟨⟨z, Or.inr (Or.inr ?_)⟩, rfl⟩
    refine ⟨by rw [hzre]; norm_num, by rw [hzre]; norm_num, ?_⟩
    rw [hzim]
    exact ne_of_gt (half_pos hr)
  have hzN : z ∈ N := by
    apply hball
    change dist z (3 / 4 : ℂ) < r
    have hdist : dist z (3 / 4 : ℂ) = r / 2 := by
      simp [z, dist_eq_norm, abs_of_pos hr]
    rw [hdist]
    exact half_lt_self hr
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (hcover z hzvertex hzN)
  have him := arc_im hd
  rw [hzim] at him
  exact (ne_of_gt (half_pos hr)) him

/-- Helper toward Definition 3.2: the full-arc local-image premise proposed
in `SidesExact` is also unavailable for this strip example. -/
theorem not_local_image_along_forward_arc
    (N : Set ℂ) (hN : IsOpen N)
    (harc : Set.range (drawing.arc ((), true)).toPath ⊆ N) :
    ¬ (∀ z, z ∈ drawing.image → z ∈ N →
      z ∈ ⋃ d, (drawing.arc d).image) := by
  intro hlocal
  apply not_local_vertex_coverage N hN
    (toPath_threeQuarters ▸ harc (Set.mem_range_self threeQuarters.val))
  intro z hz hzN
  exact hlocal z (Or.inl hz) hzN

end Definition32Strip























































































end DirectedDistances.PlanarMap

end
