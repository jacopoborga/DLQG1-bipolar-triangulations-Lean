/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingTransfer
public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceOrbits
public import DirectedDistances.PlanarMap.GeneralPlaneMap
public import Mathlib.Analysis.Convex.PathConnected

/-! # From piecewise linear drawings to the general plane carrier


Helpers toward Definitions 3.1 / 5.8. The polyline interior used here is exactly
`Polyline.interior`, namely the closed segment image minus its two endpoints. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

/-- Helper toward Definitions 3.1 / 5.8: traverse a nonempty list in order,
allocating half the remaining parameter interval to each successive segment. -/
@[expose] def listPath (a : ℂ) : (l : List ℂ) → Path a ((a :: l).getLast (by simp))
  | [] => Path.refl a
  | [b] => Path.segment a b
  | b :: c :: l => (Path.segment a b).trans (listPath b (c :: l))

/-- Helper toward Definitions 3.1 / 5.8: the ordered continuous traversal of a polyline.
For a singleton this is the constant path. -/
@[expose] def toPath (p : Polyline) : Path p.start p.finish :=
  match h : p.points with
  | [] => False.elim (p.nonempty h)
  | a :: l => (listPath a l).cast (by simp [start, h]) (by simp [finish, h])


/-- Helper toward Definitions 3.1 / 5.8. -/
theorem point_ofHead_zero (a : ℂ) (l : List ℂ) : (ofHead a l).point 0 = a := by
  simp [point, ofHead, start]

/-- Helper toward Definitions 3.1 / 5.8. -/
theorem point_ofHead_succ (a b : ℂ) (l : List ℂ) (i : ℕ)
    (hi : i < (b :: l).length) :
    (ofHead a (b :: l)).point (i + 1) = (ofHead b l).point i := by
  simp [point, ofHead, List.getElem?_eq_getElem hi]

/-- Helper toward Definitions 3.1 / 5.8: split the segment image at its first segment. -/
theorem image_ofHead_cons (a b : ℂ) (l : List ℂ) :
    (ofHead a (b :: l)).image = segment ℝ a b ∪ (ofHead b l).image := by
  ext z
  simp only [image, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · exact Or.inl (by simpa [ofHead, start] using (hz ▸ left_mem_segment ℝ a b))
    · cases i with
      | zero =>
        left
        simpa [segmentAt, point, ofHead, start] using hz
      | succ i =>
        right; right
        have hi' : i + 2 < (a :: b :: l).length := hi
        refine ⟨i, by simpa [ofHead] using hi, ?_⟩
        simpa only [segmentAt, point_ofHead_succ a b l i (by simp only [List.length_cons] at hi' ⊢; omega),
          point_ofHead_succ a b l (i + 1) (by simpa [ofHead] using hi)] using hz
  · rintro (hz | (hz | ⟨i, hi, hz⟩))
    · exact Or.inr ⟨0, by simp [ofHead], by simpa [segmentAt, point, ofHead, start] using hz⟩
    · right
      -- The next vertex already lies in the first segment.
      exact ⟨0, by simp [ofHead], by simpa [segmentAt, point, ofHead, start] using (hz ▸ right_mem_segment ℝ a b)⟩
    · right
      refine ⟨i + 1, by simpa [ofHead] using hi, ?_⟩
      simpa only [segmentAt, point_ofHead_succ a b l i (by simp only [ofHead] at hi; omega),
        point_ofHead_succ a b l (i + 1) (by simpa [ofHead] using hi)] using hz

/-- Helper toward Definitions 3.1 / 5.8: range of the ordered list traversal. -/
theorem range_listPath (a : ℂ) (l : List ℂ) :
    Set.range (listPath a l) = (ofHead a l).image := by
  induction l generalizing a with
  | nil =>
    change Set.range (Path.refl a) = _
    rw [Path.refl_range]
    simp [image, ofHead, start]
  | cons b l ih =>
    rw [image_ofHead_cons]
    cases l with
    | nil =>
      change Set.range (Path.segment a b) = _
      rw [Path.range_segment]
      simp [image, ofHead, start, right_mem_segment]
    | cons c l =>
      change Set.range ((Path.segment a b).trans (listPath b (c :: l))) = _
      rw [Path.trans_range, Path.range_segment, ih]

/-- Helper toward Definitions 3.1 / 5.8: the continuous traversal traces precisely
all consecutive closed segments, including both endpoints. -/
theorem range_toPath (p : Polyline) : Set.range p.toPath = p.image := by
  obtain ⟨l, hn⟩ := p
  cases l with
  | nil => exact False.elim (hn rfl)
  | cons a l => simpa [toPath, ofHead] using range_listPath a l

/-- Helper toward Definitions 3.1 / 5.8: simplicity passes to a nonempty tail. -/
theorem isSimple_tail (a b : ℂ) (l : List ℂ)
    (h : (ofHead a (b :: l)).IsSimple) : (ofHead b l).IsSimple := by
  have point_eq (i : ℕ) (hi : i < (b :: l).length) := point_ofHead_succ a b l i hi
  have seg_eq (i : ℕ) (hi : i + 1 < (b :: l).length) :
      (ofHead a (b :: l)).segmentAt (i + 1) = (ofHead b l).segmentAt i := by
    simp only [segmentAt, point_eq i (by omega), point_eq (i + 1) hi]
  rcases h with ⟨hn, ha, hd⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi' : i + 1 < (b :: l).length := hi
    simpa only [point_eq i (by omega), point_eq (i + 1) hi'] using
      hn (i + 1) (by simp only [ofHead, List.length_cons] at hi ⊢; omega)
  · intro i hi
    have hi' : i + 2 < (b :: l).length := hi
    simpa only [seg_eq i (by omega), seg_eq (i + 1) hi', point_eq (i + 1) (by omega)] using
      ha (i + 1) (by simp only [ofHead, List.length_cons] at hi ⊢; omega)
  · intro i j hi hj hij
    have hi' : i + 1 < (b :: l).length := hi
    have hj' : j + 1 < (b :: l).length := hj
    simpa only [seg_eq i hi', seg_eq j hj'] using
      hd (i + 1) (j + 1) (by simp only [ofHead, List.length_cons] at hi ⊢; omega)
        (by simp only [ofHead, List.length_cons] at hj ⊢; omega) (by omega)

/-- Helper toward Definitions 3.1 / 5.8. -/
theorem segmentAt_ofHead_zero (a b : ℂ) (l : List ℂ) :
    (ofHead a (b :: l)).segmentAt 0 = segment ℝ a b := by
  simp [segmentAt, point, ofHead, start]

/-- Helper toward Definitions 3.1 / 5.8. -/
theorem segmentAt_ofHead_succ (a b : ℂ) (l : List ℂ) (i : ℕ)
    (hi : i + 1 < (b :: l).length) :
    (ofHead a (b :: l)).segmentAt (i + 1) = (ofHead b l).segmentAt i := by
  simp only [segmentAt, point_ofHead_succ a b l i (by omega),
    point_ofHead_succ a b l (i + 1) hi]

/-- Helper toward Definitions 3.1 / 5.8: the first segment meets the remaining
simple polyline only at their shared endpoint. -/
theorem first_segment_inter_tail (a b : ℂ) (l : List ℂ)
    (h : (ofHead a (b :: l)).IsSimple) {z : ℂ}
    (hz : z ∈ segment ℝ a b) (ht : z ∈ (ofHead b l).image) : z = b := by
  rcases ht with ht | ⟨i, hi, ht⟩
  · simpa [ofHead, start] using ht
  · have hi' : i + 1 < (b :: l).length := hi
    have hz' : z ∈ (ofHead a (b :: l)).segmentAt 0 := by
      rwa [segmentAt_ofHead_zero]
    have ht' : z ∈ (ofHead a (b :: l)).segmentAt (i + 1) := by
      rwa [segmentAt_ofHead_succ a b l i hi']
    cases i with
    | zero =>
      have he := h.2.1 0 (by simp only [ofHead, List.length_cons] at hi ⊢; omega)
      have hm : z ∈ (ofHead a (b :: l)).segmentAt 0 ∩
          (ofHead a (b :: l)).segmentAt 1 := ⟨hz', ht'⟩
      rw [he] at hm
      simpa [point, ofHead, start] using hm
    | succ i =>
      exact False.elim ((Set.disjoint_left.mp
        (h.2.2 0 (i + 1 + 1) (by simp [ofHead])
          (by simp only [ofHead, List.length_cons] at hi ⊢; omega) (by omega))) hz' ht')

/-- Helper toward Definitions 3.1 / 5.8: the ordered traversal of a simple
polyline with at least two points is injective, including the endpoints. -/
theorem listPath_injective (a : ℂ) (l : List ℂ)
    (hlen : 2 ≤ (a :: l).length) (h : (ofHead a l).IsSimple) :
    Function.Injective (listPath a l) := by
  induction l generalizing a with
  | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
  | cons b l ih =>
    have hab : a ≠ b := by
      simpa [point, ofHead, start] using h.1 0 (by simp [ofHead])
    cases l with
    | nil => exact Path.segment_injective_of_ne hab
    | cons c l =>
      have ht := ih b (by simp) (isSimple_tail a b (c :: l) h)
      intro s t hst
      change ((Path.segment a b).trans (listPath b (c :: l))) s =
        ((Path.segment a b).trans (listPath b (c :: l))) t at hst
      rw [Path.trans_apply, Path.trans_apply] at hst
      split_ifs at hst with hs ht' ht'
      · have he := Path.segment_injective_of_ne hab hst
        apply Subtype.ext
        have hv := congrArg Subtype.val he
        dsimp at hv
        linarith only [hv]
      · have hb := first_segment_inter_tail a b (c :: l) h
          (Path.range_segment a b ▸ Set.mem_range_self _)
          (by rw [← range_listPath]; exact ⟨_, hst.symm⟩)
        have he := ht (hst.symm.trans hb |>.trans (Path.source _).symm)
        have hv := congrArg Subtype.val he
        dsimp at hv
        have := not_le.mp ht'
        linarith only [hv, this]
      · have hb := first_segment_inter_tail a b (c :: l) h
          (Path.range_segment a b ▸ Set.mem_range_self _)
          (by rw [← range_listPath]; exact ⟨_, hst⟩)
        have he := ht (hst.trans hb |>.trans (Path.source _).symm)
        have hv := congrArg Subtype.val he
        dsimp at hv
        have := not_le.mp hs
        linarith only [hv, this]
      · have he := ht hst
        apply Subtype.ext
        have hv := congrArg Subtype.val he
        dsimp at hv
        linarith only [hv]

/-- Helper toward Definitions 3.1 / 5.8: simplicity gives an injective traversal
without adding any geometric assumption. -/
theorem toPath_injective (p : Polyline) (hlen : 2 ≤ p.points.length) (h : p.IsSimple) :
    Function.Injective p.toPath := by
  obtain ⟨l, hn⟩ := p
  cases l with
  | nil => exact False.elim (hn rfl)
  | cons a l => simpa [toPath, ofHead] using listPath_injective a l hlen h

/-- Helper toward Definitions 3.1 / 5.8: the required open-parameter injectivity. -/
theorem toPath_injOn (p : Polyline) (hlen : 2 ≤ p.points.length) (h : p.IsSimple) :
    Set.InjOn p.toPath openParams := (p.toPath_injective hlen h).injOn

/-- Helper toward Definitions 3.1 / 5.8: the open traversal image is exactly
`p.image \ {p.start, p.finish}`, the existing polyline interior. -/
theorem toPath_image_openParams (p : Polyline) (hlen : 2 ≤ p.points.length)
    (h : p.IsSimple) : p.toPath '' openParams = p.interior := by
  have hinj := p.toPath_injective hlen h
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨p.range_toPath ▸ Set.mem_range_self t, ?_⟩
    rintro (he | he)
    · have ht0 := hinj (he.trans (Path.source p.toPath).symm)
      have hv := congrArg Subtype.val ht0
      have hp := ht.1
      change (t : ℝ) = 0 at hv
      linarith only [hp, hv]
    · have ht1 := hinj (he.trans (Path.target p.toPath).symm)
      have hv := congrArg Subtype.val ht1
      have hp := ht.2
      change (t : ℝ) = 1 at hv
      linarith only [hp, hv]
  · rintro ⟨hz, hn⟩
    rw [← p.range_toPath] at hz
    obtain ⟨t, rfl⟩ := hz
    have h0 : t ≠ 0 := by
      intro ht; subst t
      exact hn (Or.inl (Path.source p.toPath))
    have h1 : t ≠ 1 := by
      intro ht; subst t
      exact hn (Or.inr (Path.target p.toPath))
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · exact (unitInterval.pos_iff_ne_zero).mpr h0
    · exact (unitInterval.lt_one_iff_ne_one).mpr h1

end Polyline

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward Definitions 3.1 / 5.8: darts represent the same geometric
edge exactly when they agree or are related by flip. -/
@[expose] def edgeSetoid (P : PLDrawing D V flip rot vert) : Setoid D where
  r d e := d = e ∨ d = flip e
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · rintro d e (h | h)
      · exact Or.inl h.symm
      · exact Or.inr ((P.flip_involutive e).symm.trans (congrArg flip h.symm))
    · rintro d e f (rfl | hde) hef
      · exact hef
      · rcases hef with rfl | hef
        · exact Or.inr hde
        · exact Or.inl (hde.trans ((congrArg flip hef).trans (P.flip_involutive f)))

/-- Helper toward Definitions 3.1 / 5.8: geometric edges retain flip-orbit
identity, including distinct parallel edges. -/
abbrev GeometricEdge (P : PLDrawing D V flip rot vert) := Quotient P.edgeSetoid

variable (P : PLDrawing D V flip rot vert)

/-- Helper toward Definitions 3.1 / 5.8. -/
theorem geometricEdge_flip (d : D) :
    Quotient.mk P.edgeSetoid (flip d) = Quotient.mk P.edgeSetoid d :=
  Quotient.sound (Or.inr rfl)

/-- Helper toward Definitions 3.1 / 5.8: a representative differs from any
other dart of its edge only by reversal. -/
theorem geometricEdge_out_mk (d : D) :
    (Quotient.mk P.edgeSetoid d).out = d ∨
      (Quotient.mk P.edgeSetoid d).out = flip d :=
  @Quotient.exact D P.edgeSetoid (Quotient.mk P.edgeSetoid d).out d
    (Quotient.out_eq (Quotient.mk P.edgeSetoid d))

/-- Helper toward Definitions 3.1 / 5.8: the geometric arc image is independent
of the representative dart. Reversal is supplied by `arc_flip`. -/
theorem arc_image_flip (d : D) : (P.arc (flip d)).image = (P.arc d).image := by
  rw [P.arc_flip, Polyline.image_reverse_transfer]

/-- Helper toward Definitions 3.1 / 5.8: representative independence of the
open geometric arc. -/
theorem arc_interior_flip (d : D) : (P.arc (flip d)).interior = (P.arc d).interior := by
  rw [P.arc_flip, Polyline.interior_reverse_transfer]

/-- plane carrier by choosing one dart per geometric edge. Both stored endpoints
and the entire ordered path are taken from this dart. -/
@[expose] def toPlaneGraphDrawing : PlaneGraphDrawing V P.GeometricEdge where
  src e := vert e.out
  tgt e := vert (flip e.out)
  pos := P.pos
  pos_injective := P.pos_injective
  arc e := (P.arc e.out).toPath.cast (P.arc_start e.out).symm (P.arc_finish e.out).symm
  arc_injOn e := (P.arc e.out).toPath_injOn (P.arc_length e.out) (P.arc_simple e.out)
  openArc_disjoint := by
    intro e f hef
    change Disjoint ((P.arc e.out).toPath '' openParams)
      ((P.arc f.out).toPath '' openParams)
    rw [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _),
      Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)]
    apply P.interior_disjoint
    · intro h
      apply hef
      exact (Quotient.out_eq e).symm.trans
        ((congrArg (Quotient.mk P.edgeSetoid) h.symm).trans (Quotient.out_eq f))
    · intro h
      apply hef
      exact (Quotient.out_eq e).symm.trans
        (((P.geometricEdge_flip e.out).symm.trans
          (congrArg (Quotient.mk P.edgeSetoid) h.symm)).trans (Quotient.out_eq f))
  openArc_avoids := by
    intro e v
    change P.pos v ∉ (P.arc e.out).toPath '' openParams
    rw [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)]
    exact P.interior_avoids_vertices e.out v

/-- Helper toward Definitions 3.1 / 5.8: the selected representative traces
exactly the same closed arc as either dart of the geometric edge. -/
theorem toPlaneGraphDrawing_arc_range (d : D) :
    Set.range (P.toPlaneGraphDrawing.arc (Quotient.mk P.edgeSetoid d)) =
      (P.arc d).image := by
  change Set.range (P.arc (Quotient.mk P.edgeSetoid d).out).toPath = _
  rw [Polyline.range_toPath]
  rcases P.geometricEdge_out_mk d with h | h
  · rw [h]
  · rw [h, P.arc_image_flip]

/-- Helper toward Definitions 3.1 / 5.8: representative independence also
holds for the open arc, with the existing polyline interior. -/
theorem toPlaneGraphDrawing_openArc_mk (d : D) :
    P.toPlaneGraphDrawing.openArc (Quotient.mk P.edgeSetoid d) =
      (P.arc d).interior := by
  change (P.arc (Quotient.mk P.edgeSetoid d).out).toPath '' openParams = _
  rw [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)]
  rcases P.geometricEdge_out_mk d with h | h
  · rw [h]
  · rw [h, P.arc_interior_flip]

/-- Helper toward Definitions 3.1 / 5.8: passing to geometric edges preserves
the entire drawing image, including isolated vertices. -/
theorem toPlaneGraphDrawing_image : P.toPlaneGraphDrawing.image = P.image := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · obtain ⟨e, ht⟩ := Set.mem_iUnion.mp hz
      right
      exact ⟨e.out, (Polyline.range_toPath (P.arc e.out)) ▸ ht⟩
  · rintro (hz | ⟨d, hz⟩)
    · exact Or.inl hz
    · right
      apply Set.mem_iUnion.mpr
      refine ⟨Quotient.mk P.edgeSetoid d, ?_⟩
      rwa [P.toPlaneGraphDrawing_arc_range]

/-- Helper toward Definitions 3.1 / 5.8: faces are identical subtypes of
sets of complex numbers, since their defining complementary image agrees. -/
theorem toPlaneGraphDrawing_face_eq : P.toPlaneGraphDrawing.Face = P.Face := by
  unfold PlaneGraphDrawing.Face Face
  rw [P.toPlaneGraphDrawing_image]

/-- Helper toward Definitions 3.1 / 5.8: identify faces without changing
their underlying subsets of the plane. -/
@[expose] def toPlaneGraphDrawingFaceEquiv : P.toPlaneGraphDrawing.Face ≃ P.Face where
  toFun F := ⟨F.val, by simpa only [P.toPlaneGraphDrawing_image] using F.property⟩
  invFun F := ⟨F.val, by simpa only [P.toPlaneGraphDrawing_image] using F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Helper toward Definitions 3.1 / 5.8: the general carrier's externality
is exactly the PL drawing's unbounded-face predicate. -/
theorem toPlaneGraphDrawing_isExternal_iff (F : P.toPlaneGraphDrawing.Face) :
    P.toPlaneGraphDrawing.IsExternal F ↔
      P.IsUnbounded (P.toPlaneGraphDrawingFaceEquiv F) := by
  change (¬ Bornology.IsBounded F.val) ↔ ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖
  rw [isBounded_iff_forall_norm_le]
  push Not
  rfl

/-- Helper toward Definitions 3.1 / 5.8: every point of an edge bordering a
face belongs to that face's closure. Surjectivity of dart incidence is passed
explicitly to the geometric local-isolation theorems. -/
theorem dartBorders_arc_subset_closure (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) :
    (P.arc d).image ⊆ closure F.val := by
  have hopen (i : ℕ) (hi : i + 1 < (P.arc d).points.length) :
      openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)) ⊆ closure F.val := by
    intro q hq
    let a := (P.arc d).point i
    let b := (P.arc d).point (i + 1)
    let u := b - a
    have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
    obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hi hq
    let t := r / (4 * (‖u‖ + 1))
    have ht : 0 < t := div_pos hr (by positivity)
    have htprod : t * (4 * (‖u‖ + 1)) = r := div_mul_cancel₀ r (by positivity)
    have hsmall : t * ‖u‖ < r / 2 := by nlinarith only [htprod, ht, hnu]
    let z := q + t • (Complex.I * u)
    have hzq : dist z q = t * ‖u‖ := by
      rw [dist_eq_norm]
      change ‖q + t • (Complex.I * u) - q‖ = _
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        norm_mul, Complex.norm_I, one_mul]
    have hzqpos : 0 < dist z q := hzq ▸ mul_pos ht hnu
    have hmin : ∀ y ∈ P.image, dist z q ≤ dist z y := by
      intro y hy
      by_cases hyr : y ∈ Metric.ball q r
      · have hyseg := hlocal y hyr hy
        have hside := segment_contact_side_eq_zero a b q y
          (openSegment_subset_segment ℝ a b hq) hyseg
        have him : (star u * (z - y)).im = t * Complex.normSq u := by
          have he : z - y = t • (Complex.I * u) - (y - q) := by dsimp [z]; module
          rw [he, mul_sub, Complex.sub_im, mul_smul_comm, Complex.smul_im]
          have hn : (star u * (Complex.I * u)).im = Complex.normSq u := by
            rw [show star u * (Complex.I * u) = Complex.I * (star u * u) by ring,
              Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
            simp
          change t * (star u * (Complex.I * u)).im - (star u * (y - q)).im = _
          rw [hn, hside, sub_zero]
        have hb := Complex.im_le_norm (star u * (z - y))
        rw [him, norm_mul, norm_star, Complex.normSq_eq_norm_sq] at hb
        rw [hzq, dist_eq_norm]
        nlinarith only [hb, hnu]
      · have hry : r ≤ dist q y := by
          simpa only [Metric.mem_ball, dist_comm, not_lt] using hyr
        have htri := dist_triangle q z y
        rw [dist_comm q z, hzq] at htri
        rw [hzq]
        linarith only [hry, htri, hsmall]
    have hznot : z ∉ P.image := by
      intro hz
      have hm := hmin z hz
      rw [dist_self] at hm
      exact (not_le_of_gt hzqpos) hm
    obtain ⟨K, hzK⟩ := (P.faces_cover_compl z).mpr hznot
    have hball : Metric.ball z (dist z q) ⊆ K.val := by
      have hsafe : Metric.ball z (dist z q) ⊆ P.imageᶜ := by
        intro y hy hym
        exact (not_lt_of_ge (hmin y hym)) (by simpa only [Metric.mem_ball, dist_comm] using hy)
      obtain ⟨x, _, hK⟩ := K.property
      rw [hK] at hzK ⊢
      rw [connectedComponentIn_eq hzK]
      exact (convex_ball z (dist z q)).isPreconnected.subset_connectedComponentIn
        (Metric.mem_ball_self hzqpos) hsafe
    have hpos : 0 < (star u * (z - q)).im := by
      have he : z - q = t • (Complex.I * u) := by dsimp [z]; abel
      rw [he, mul_smul_comm, Complex.smul_im]
      have hn : (star u * (Complex.I * u)).im = Complex.normSq u := by
        rw [show star u * (Complex.I * u) = Complex.I * (star u * u) by ring,
          Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
        simp
      rw [hn]
      exact mul_pos ht (Complex.normSq_pos.mpr hu)
    have hdK := P.face_nearest_openSegment_dartBorders_of_pos hvert K z q d hi hq
      (dist_pos.mp hzqpos) hball hmin hpos
    have hKF : K = F := P.dartBorders_face_unique d K F hdK hF
    rw [← hKF]
    apply closure_mono hball
    rw [closure_ball z (ne_of_gt hzqpos)]
    exact Metric.mem_closedBall.mpr (le_of_eq (dist_comm q z))
  have hseg (i : ℕ) (hi : i + 1 < (P.arc d).points.length) :
      (P.arc d).segmentAt i ⊆ closure F.val :=
    segment_subset_closure_openSegment.trans ((closure_mono (hopen i hi)).trans
      (by rw [closure_closure]))
  rintro z (hz | ⟨i, hi, hz⟩)
  · apply hseg 0 (by have := P.arc_length d; omega)
    rw [Set.mem_singleton_iff] at hz
    rw [hz, Polyline.segmentAt, Polyline.point_zero_eq_start]
    exact left_mem_segment ℝ _ _
  · exact hseg i hi hz

end PLDrawing

open DirectedDistances.KMSW DirectedDistances.RandomWalk

section Assembly

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa

/-- Helper toward Definitions 3.1 / 5.8: the assembly has the general plane
carrier with missing edges excluded from the oriented edge set. A missing
edge's entire arc lies in the unique unbounded face closure. Present edges
are oriented from their west endpoint to their east endpoint. -/
@[expose] def uibhbotAssemblyDirectedPlaneMapWithMissing :
    DirectedPlaneMapWithMissing (WholePlaneVertex W) (G).GeometricEdge where
  toPlaneGraphDrawing := (G).toPlaneGraphDrawing
  missing e := ¬ wholePlaneEdgePresent W e.out.1
  missing_on_external := by
    intro e he
    obtain ⟨U, hU, _⟩ := uibhbot_assembly_unbounded_face_existsUnique
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
    let d : WholePlaneDart W := (e.out.1, true)
    have hd : (G).dartBorders d U :=
      (uibhbot_assembly_unbounded_dartBorders_iff
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos U hU d).mpr ⟨rfl, he⟩
    have hcl := (G).dartBorders_arc_subset_closure
      (uibhbot_faceOrbit_dartVertex_surjective W H) d U hd
    refine ⟨(G).toPlaneGraphDrawingFaceEquiv.symm U, ?_, ?_⟩
    · exact ((G).toPlaneGraphDrawing_isExternal_iff _).mpr hU
    · change Set.range ((G).arc e.out).toPath ⊆ closure U.val
      rw [Polyline.range_toPath]
      have him : ((G).arc e.out).image = ((G).arc d).image := by
        rcases ho : e.out with ⟨j, b⟩
        cases b with
        | true => simp [d, ho]
        | false =>
          have hh := (G).arc_image_flip (j, true)
          change ((G).arc (j, false)).image = ((G).arc (j, true)).image at hh
          simpa only [d, ho] using hh
      rw [him]
      exact hcl
  forward e := !e.val.out.2

local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definitions 3.1 / 5.8: the general-carrier assembly
orientation is acyclic, by transport to the existing rotation-orbit directed
graph acyclicity theorem. -/
theorem uibhbotAssemblyDirectedPlaneMapWithMissing_isAcyclic : (M).IsAcyclic := by
  let surj := uibhbot_faceOrbit_dartVertex_surjective W H
  let f : WholePlaneVertex W →
      RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) :=
    fun v => rootedLocallyFiniteVertexClass (wholePlaneRotation W H) (surj v).choose
  have hfclass (d : WholePlaneDart W) :
      f (wholePlaneDartVertex W d) =
        rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d := by
    apply Quotient.sound
    apply wholePlaneRotation_sameVertex_sameCycle_proof W H
    exact (surj (wholePlaneDartVertex W d)).choose_spec
  have hstep {u v : WholePlaneVertex W} (huv : (M).step u v) :
      rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
        (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W) (f u) (f v) := by
    obtain ⟨e, hu, hv⟩ := huv
    let d : WholePlaneDart W := (e.val.out.1, false)
    have htail : (M).tail e = wholePlaneDartVertex W d := by
      change (if !e.val.out.2 then wholePlaneDartVertex W e.val.out
        else wholePlaneDartVertex W (wholePlaneDartFlip W e.val.out)) = _
      rcases ho : e.val.out with ⟨j, b⟩
      cases b <;> simp [d, ho, wholePlaneDartFlip]
      rfl
    have hhead : (M).head e = wholePlaneDartVertex W (wholePlaneDartFlip W d) := by
      change (if !e.val.out.2 then wholePlaneDartVertex W (wholePlaneDartFlip W e.val.out)
        else wholePlaneDartVertex W e.val.out) = _
      rcases ho : e.val.out with ⟨j, b⟩
      cases b <;> simp [d, ho, wholePlaneDartFlip]
      rfl
    have hpresent : wholePlaneEdgePresent W d.1 := not_not.mp e.property
    refine ⟨d, e.property, ⟨by simp [d], hpresent⟩, ?_, ?_⟩
    · exact (hfclass d).symm.trans (congrArg f (htail.symm.trans hu))
    · exact (hfclass (wholePlaneDartFlip W d)).symm.trans
        (congrArg f (hhead.symm.trans hv))
  have hmap {u v : WholePlaneVertex W} (hpath : Relation.TransGen (M).step u v) :
      Relation.TransGen
        (rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
          (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W)) (f u) (f v) := by
    induction hpath with
    | single h => exact Relation.TransGen.single (hstep h)
    | tail h hlast ih => exact ih.tail (hstep hlast)
  intro v hcycle
  exact wholePlaneDart_acyclic W H (f v) (hmap hcycle)

/-- Helper toward Definitions 3.1 / 5.8: missing status is exactly the
source's globally absent edge predicate, for either representing dart. -/
theorem uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk (d : WholePlaneDart W) :
    (M).missing (Quotient.mk (G).edgeSetoid d) ↔ ¬ wholePlaneEdgePresent W d.1 := by
  change (¬ wholePlaneEdgePresent W (Quotient.mk (G).edgeSetoid d).out.1) ↔ _
  rcases (G).geometricEdge_out_mk d with ho | ho
  · rw [ho]
  · rw [ho]
    rfl

/-- Helper toward Definitions 3.1 / 5.8: the orientation bit of a present
edge selects the west-to-east orientation regardless of representative choice. -/
theorem uibhbotAssemblyDirectedPlaneMapWithMissing_forward
    (e : {e : (G).GeometricEdge // ¬ (M).missing e}) : (M).forward e = !e.val.out.2 := rfl

end Assembly
end DirectedDistances.PlanarMap

