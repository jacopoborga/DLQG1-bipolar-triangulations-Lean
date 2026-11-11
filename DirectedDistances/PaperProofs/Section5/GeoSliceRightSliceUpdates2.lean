/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRightSliceUpdates
public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice5

/-! Oriented geometric crossings for the corrected right-side reconstruction. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Set Metric
open scoped Classical Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: a strict ambient crossing from a left face
into a right face borders the former by a forward geodesic dart. -/
theorem m0GeodesicFaceChain_left_right_crossing
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} F G)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp Q .left)
    (hGR : G.val ⊆ m0GeodesicSideOpenRegion hp Q .right) :
    ∃ n : ℕ, (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (Q.codePath.edge n, false)) F := by
  have hret := m0GeodesicFaceChainStep_strict_ambient_retained hp hFG
  obtain ⟨e, heF, heG, _⟩ := m0GeodesicFaceChainStep_strict_ambient_runZero hp hFG
  have he : e.1 ∈ m0GeodesicEdges Q := by
    by_contra hoff
    have heL := (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp Q
      hoff e.2 F hret.1 heF .left).mpr hFL
    have hGL := (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp Q
      hoff (!e.2) G hret.2 heG .left).mp heL
    obtain ⟨z, hz, hG⟩ := G.property
    have hzG : z ∈ G.val := hG ▸ mem_connectedComponentIn hz
    exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q) (hGL hzG) (hGR hzG)
  obtain ⟨n, hn⟩ := he
  have hbit : e.2 = false := by
    cases hb : e.2 with
    | false => rfl
    | true =>
      have hFR := m0Geodesic_reverse_seam_face_right hp Q n F hret.1
        (by simpa only [show e = (Q.codePath.edge n, true) from Prod.ext hn.symm hb] using heF)
      obtain ⟨z, hz, hF⟩ := F.property
      have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
      exact False.elim (disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q)
        (hFL hzF) (hFR hzF))
  exact ⟨n, (Prod.ext hn.symm hbit : e = (Q.codePath.edge n, false)) ▸ heF⟩

/-- Helper toward Lemma 5.6: crossings between two retained left faces
use an edge outside the ray, with both bordering orientations explicit. -/
theorem m0GeodesicFaceChainStep_left_off_ray
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {k : ℤ} {longest : Bool}
    (Q : M0CutInfiniteGeodesic W H h hLL k longest)
    {F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hFG : m0GeodesicFaceChainStep hp
      {z : ℂ | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im} F G)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp Q .left)
    (hGL : G.val ⊆ m0GeodesicSideOpenRegion hp Q .left) :
    ∃ e : ℕ × Bool, e.1 ∉ m0GeodesicEdges Q ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 e) F ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (e.1, !e.2)) G := by
  have hret := m0GeodesicFaceChainStep_strict_ambient_retained hp hFG
  obtain ⟨e, heF, heG, _⟩ := m0GeodesicFaceChainStep_strict_ambient_runZero hp hFG
  refine ⟨e, ?_, heF, heG⟩
  rintro ⟨n, hn⟩
  have hno (A : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
      (hAL : A.val ⊆ m0GeodesicSideOpenRegion hp Q .left)
      (hAM : A.val ⊆ m0GeodesicAmbientRegion W H h)
      (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (Q.codePath.edge n, true)) A) : False := by
    have hAR := m0Geodesic_reverse_seam_face_right hp Q n A hAM hb
    obtain ⟨z, hz, hA⟩ := A.property
    have hzA : z ∈ A.val := hA ▸ mem_connectedComponentIn hz
    exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp Q) (hAL hzA) (hAR hzA)
  cases hb : e.2 with
  | false =>
    apply hno G hGL hret.2
    simpa only [← hn, hb, Bool.not_false] using heG
  | true =>
    exact hno F hFL hret.1
      ((Prod.ext hn.symm hb : e = (Q.codePath.edge n, true)) ▸ heF)

/-- Helper toward Lemma 5.6: canonical inclusion of literal slice cells
in the preceding right side, retaining both orientations and edge identity. -/
@[expose] def m0CutGeodesicSliceRightCell
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    GeometricSideCell (m0CutGeodesicSlice (hp := hp) P k a b hab) →
      GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)
  | .inl v => .inl ⟨v.val, v.property.1.1⟩
  | .inr d => .inr ⟨d.val, d.property.1.1⟩

/-- Helper toward Lemma 5.6: the slice inclusion preserves individual cells. -/
theorem m0CutGeodesicSliceRightCell_injective
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    Function.Injective (m0CutGeodesicSliceRightCell hp P k a b hab) := by
  intro c e hce
  cases c <;> cases e
  · dsimp only [m0CutGeodesicSliceRightCell] at hce
    have hv := congrArg Subtype.val (Sum.inl.inj hce)
    exact congrArg Sum.inl (Subtype.ext hv)
  · exact False.elim (Sum.inl_ne_inr hce)
  · exact False.elim (Sum.inr_ne_inl hce)
  · dsimp only [m0CutGeodesicSliceRightCell] at hce
    have hd := congrArg Subtype.val (Sum.inr.inj hce)
    exact congrArg Sum.inr (Subtype.ext hd)

/-- Helper toward Lemma 5.6: the image of the right inclusion is exactly
the literal source carrier, without any intrinsic exhaustion assumption. -/
theorem m0CutGeodesicSliceRightCell_mem_range_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    c ∈ Set.range (m0CutGeodesicSliceRightCell hp P k a b hab) ↔
      match c with
      | .inl v => v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
      | .inr d => d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges := by
  cases c with
  | inl v =>
    constructor
    · rintro ⟨u, hu⟩
      cases u with
      | inl u =>
        change v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
        exact (congrArg Subtype.val (Sum.inl.inj hu)) ▸ u.property
      | inr u => exact False.elim (Sum.inr_ne_inl hu)
    · intro hv
      exact ⟨.inl ⟨v.val, hv⟩, rfl⟩
  | inr d =>
    constructor
    · rintro ⟨u, hu⟩
      cases u with
      | inl u => exact False.elim (Sum.inl_ne_inr hu)
      | inr u =>
        change d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges
        exact (congrArg (fun x : ℕ × Bool => x.1)
          (congrArg Subtype.val (Sum.inr.inj hu))) ▸ u.property
    · intro hd
      exact ⟨.inr ⟨d.val, hd⟩, rfl⟩

/-- Helper toward Lemma 5.6: the two finite positive chain presentations
have precisely the same steps and omitted intermediate cells. -/
theorem rightSliceRotationChain2_iff_enclosed {α : Type*}
    (R : α → α → Prop) (S : Set α) (a b : α) :
    RightSliceRotationChain2 R S a b ↔ EnclosedSliceRotationChain R S a b := by
  constructor
  · intro h
    induction h with
    | single h => exact .single h
    | cons h hb _ ih => exact .cons h hb ih
  · intro h
    induction h with
    | single h => exact .single h
    | cons h hb _ ih => exact .cons h hb ih

/-- Helper toward Lemma 5.6: source slice rotation is nested first
return through the preceding right side. The retained set is the literal
slice image; carrier exhaustion is not assumed. -/
theorem m0CutGeodesicSlice_rotation_iff_right_chain
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges}) :
    (m0CutGeodesicSlice (hp := hp) P k a b hab).rotation d.val e.val ↔
      RightSliceRotationChain2
        (geometricSideRelation (m0GeodesicSide hp (P (k - 1)) .right) .rotation)
        (Set.range (m0CutGeodesicSliceRightCell hp P k a b hab))
        (m0CutGeodesicSliceRightCell hp P k a b hab (.inr d))
        (m0CutGeodesicSliceRightCell hp P k a b hab (.inr e)) := by
  let M := m0GeodesicSide hp (P (k - 1)) .right
  let S : Set (ℕ × Bool) := {d | d.1 ∈ M.edges}
  let T : Set (ℕ × Bool) :=
    {d | d.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges}
  let f := (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)
  let inc : S → GeometricSideCell M := fun d => .inr d
  let dS : S := ⟨d.val, d.property.1.1⟩
  let eS : S := ⟨e.val, e.property.1.1⟩
  have hTS : T ⊆ S := fun _ hd => hd.1.1
  have hsub := enclosedSliceRotationChain_injective_iff
    (fun x : S => x.val) Subtype.val_injective
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := fun x y => y ∈ S ∧ enclosedSliceFirstReturn f S x y)
    (S := {x : S | x.val ∈ T}) (S' := T)
    (fun x y => ⟨fun h => ⟨y.property, h⟩, fun h => h.2⟩)
    (fun _ => Iff.rfl) (fun _ y hy => ⟨⟨y, hy.1⟩, rfl⟩) dS eS
  have hcell := enclosedSliceRotationChain_injective_iff inc
    (fun _ _ hh => Sum.inr.inj hh)
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := geometricSideRelation M .rotation)
    (S := {x : S | x.val ∈ T})
    (S' := Set.range (m0CutGeodesicSliceRightCell hp P k a b hab))
    (fun _ _ => Iff.rfl)
    (fun x => (m0CutGeodesicSliceRightCell_mem_range_iff hp P k a b hab (inc x)).symm)
    (by
      intro x y hxy
      cases y with
      | inl y => exact False.elim hxy
      | inr y => exact ⟨y, rfl⟩) dS eS
  exact ((enclosedSliceFirstReturn_nested f S T hTS e.property).trans
    (hsub.symm.trans hcell)).trans
      (rightSliceRotationChain2_iff_enclosed _ _ _ _).symm

/-- Helper toward Lemma 5.6: every relation of the literal slice is
the corrected right restriction on its literal cell image. This identifies
rotation, oriented faces, root and all marks without carrier exhaustion. -/
theorem m0CutGeodesicSlice_relation_iff_rightSliceRelation2
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (t : TruncationRelation)
    (c e : GeometricSideCell (m0CutGeodesicSlice (hp := hp) P k a b hab)) :
    geometricSideRelation (m0CutGeodesicSlice (hp := hp) P k a b hab) t c e ↔
      rightSliceRelation2 (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k)
        (Set.range (m0CutGeodesicSliceRightCell hp P k a b hab)) t
        (m0CutGeodesicSliceRightCell hp P k a b hab c)
        (m0CutGeodesicSliceRightCell hp P k a b hab e) := by
  cases t with
  | rotation =>
    cases c with
    | inl c =>
      cases e <;> refine ⟨False.elim, ?_⟩ <;> intro hh <;>
        cases hh with
        | single h => exact False.elim h
        | cons h _ _ => exact False.elim h
    | inr c =>
      cases e with
      | inl e =>
        refine ⟨False.elim, ?_⟩
        intro hh
        have he := enclosedSliceRotationChain_last
          ((rightSliceRotationChain2_iff_enclosed _ _ _ _).mp hh)
        obtain ⟨d, hd⟩ := he
        cases d <;> exact False.elim hd
      | inr e => exact m0CutGeodesicSlice_rotation_iff_right_chain hp P k a b hab c e
  | faceNext =>
    cases c with
    | inl c => cases e <;> exact ⟨False.elim, fun h => h.1.elim⟩
    | inr c =>
      cases e with
      | inl e => exact ⟨False.elim, fun h => h.1.elim⟩
      | inr e =>
        exact m0CutGeodesicSlice_faceNext_iff_rightSliceRelation2 hp P T hleft hc
          k a b hab ⟨c.val, c.property.1.1⟩ ⟨e.val, e.property.1.1⟩
  | seam i =>
    cases c with
    | inl c => exact ⟨False.elim, fun hh => (Sum.inl_ne_inr hh).elim⟩
    | inr c =>
      change ((P k).codePath.edge i, false) = c.val ↔ Sum.inr _ = Sum.inr _
      rw [Sum.inr.injEq, Subtype.ext_iff]
      exact eq_comm
  | boundary i => cases c <;> cases e <;> rfl
  | vertex => cases c <;> cases e <;> rfl
  | root => cases c <;> cases e <;> rfl
  | incident => cases c <;> cases e <;> rfl
  | opposite => cases c <;> cases e <;> rfl
  | oriented => cases c <;> cases e <;> rfl
  | target => cases c <;> cases e <;> rfl

/-- Helper toward Lemma 5.6: the actual slice realizes the full corrected
restriction on its literal image. Only identification of this image with
`rightSliceKeep2` remains before applying the optional reader. -/
theorem m0CutGeodesicSlice_rightRestrictionRealizes2_literal_range
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    rightRestrictionRealizes2 (m0GeodesicSide hp (P (k - 1)) .right)
      (Set.range (m0CutGeodesicSliceRightCell hp P k a b hab))
      (rightSliceRelation2 (m0GeodesicSide hp (P (k - 1)) .right)
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k)
        (Set.range (m0CutGeodesicSliceRightCell hp P k a b hab)))
      (m0CutGeodesicSlice (hp := hp) P k a b hab) := by
  let f := m0CutGeodesicSliceRightCell hp P k a b hab
  let g : GeometricSideCell (m0CutGeodesicSlice (hp := hp) P k a b hab) →
      Set.range f := fun c => ⟨f c, Set.mem_range_self c⟩
  have hg : Function.Bijective g := by
    constructor
    · intro c e hce
      exact m0CutGeodesicSliceRightCell_injective hp P k a b hab
        (congrArg Subtype.val hce)
    · rintro ⟨_, c, rfl⟩
      exact ⟨c, rfl⟩
  exact ⟨Equiv.ofBijective g hg,
    m0CutGeodesicSlice_relation_iff_rightSliceRelation2 hp P T hleft hc k a b hab⟩

/-- Helper toward Lemma 5.6: any forward next-ray dart bordering a
retained preceding-right face lies strictly before the next offset.
Forward common-tail darts border the preceding left side instead. -/
theorem m0GeodesicRightSide_forward_overlap_face_index_lt
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (n : ℕ) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 ((P k).codePath.edge n, false)) F) : n < b := by
  by_contra hn
  have hbn : b ≤ n := Nat.le_of_not_gt hn
  have he := wholePlaneEdgeι_injective W 0 (hab.1 (n - b))
  rw [Nat.add_sub_of_le hbn] at he
  have hFL := boundaryGluing_forward_seam_face_left W h (k - 1) longest hp
    (P (k - 1)) (a + (n - b)) F (fun z hz => (hFR hz).1)
    (by simpa only [m0GeodesicSeam, he] using hb)
  obtain ⟨z, hz, hval⟩ := F.property
  have hzF : z ∈ F.val := hval ▸ mem_connectedComponentIn hz
  exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp (P (k - 1)))
    (hFL hzF) (hFR hzF)

/-- Helper toward Lemma 5.6: at zero next offset the intrinsic left
candidate contains only the next ray's own vertex and dart cells. Thus a
zero-offset off-ray domain cannot be discharged by a face seed. -/
theorem m0GeodesicRightSide_intrinsic_left_iff_ray_of_zero_next_coalescence
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a 0)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    geometricSide_intrinsic_left _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c ↔
      geometricSide_ray_vertex _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k) c ∨
      geometricSide_ray_dart _
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c := by
  constructor
  · rintro (hv | hd | ⟨q, hq, _⟩)
    · exact Or.inl hv
    · exact Or.inr hd
    · exact False.elim (m0GeodesicRightSide_no_left_seed_of_zero_next_coalescence
        hp P T hleft hc k a hab q hq)
  · rintro (hv | hd)
    · exact Or.inl hv
    · exact Or.inr (Or.inl hd)

/-- Helper toward Lemma 5.6: every retained future triangle has a
bordering forward dart, obtained from its actual creation triple. -/
theorem m0Geodesic_retained_face_has_forward_dart
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFA : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    ∃ e : ℕ, (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (e, false)) F := by
  obtain ⟨F0, hF0, hval⟩ := m0Geodesic_retained_face_runZero hp F hFA
  obtain ⟨j, hj⟩ := (boundedFace_iff_creation_orbit (shiftedStream W 0)
    (H.1 0) h F0).mp hF0
  let d := (stageTriangleDartTriple (shiftedStream W 0) j).1
  have hbit : d.2 = false := by
    dsimp only [d, stageTriangleDartTriple]
    split
    · split <;> rfl
    · rfl
  have hmem : d ∈ stageTriangleDartList (shiftedStream W 0) j := by
    exact List.mem_cons_self
  have hb0 := (cap_border_iff (shiftedStream W 0) (H.1 0) j d).mpr hmem
  have hb := (PLDrawing.dartBorders_congr _ _ F0 F
    (WholePlanePastGlueM0Restriction.restrict_arc W h hp H d) hval).mpr
      (hj.symm ▸ hb0)
  exact ⟨d.1, (Prod.ext rfl hbit : d = (d.1, false)) ▸ hb⟩

/-- Helper toward Lemma 5.6: at zero next offset, a genuine retained
overlap face supplies a cell in the modified OPEN L domain with no possible
next-left seed. Therefore proving that domain empty requires excluding
overlap faces, not merely excluding the preceding boundary segment. -/
theorem m0GeodesicRightSide_zero_next_overlap_face_obstruction
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hc : ∀ m : ℤ, ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
    (k : ℤ) (a : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a 0)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right) :
    ∃ c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right),
      (match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left) ∧
      c ∉ m0GeodesicRightSideDeletedTailCells hp P k a 0 ∧
      ¬ geometricSide_ray_vertex _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k) c ∧
      ¬ geometricSide_ray_dart _
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c ∧
      c ∉ rightSlicePrecedingSegment _
        (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
        (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a ∧
      ¬ ∃ q, geometricSide_left_face_seed _
          (m0GeodesicRightSideNextDarts hp P T hleft hc k) q ∧
        Relation.ReflTransGen
          (geometricSide_slit_step _
            (m0GeodesicRightSideNextVertices hp P T hleft hc k)
            (m0GeodesicRightSideNextDarts hp P T hleft hc k)) q c := by
  obtain ⟨e, hb⟩ := m0Geodesic_retained_face_has_forward_dart hp F
    (fun z hz => (hFR hz).1)
  have heR := m0Geodesic_side_edge_of_bordering_face hp (P (k - 1)) .right
    (e, false) F hFR hb
  have heL := m0Geodesic_side_edge_of_bordering_face hp (P k) .left
    (e, false) F hFL hb
  let d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
    ⟨(e, false), heR⟩
  have hoffOld : e ∉ m0GeodesicEdges (P (k - 1)) := by
    rintro ⟨n, hn⟩
    have hi := m0GeodesicRightSide_face_dart_invariant hp
      (P (k - 1)) (P (k - 1)) .right d F hb hFR
    exact hi.2 n (Prod.ext hn.symm rfl)
  have hoffNext : e ∉ m0GeodesicEdges (P k) := by
    rintro ⟨n, hn⟩
    have he := wholePlaneEdgeι_injective W 0 (hab.1 n)
    simp only [Nat.zero_add] at he
    exact hoffOld ⟨a + n, he.trans hn⟩
  refine ⟨.inr d, heL, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact hoffOld ⟨a + n, hn⟩
    · exact hoffNext ⟨0 + n, hn⟩
  · rintro ⟨n, hn⟩
    exact Sum.inr_ne_inl hn
  · intro hray
    exact hoffNext ((m0GeodesicRightSide_ray_dart_iff hp P k
      (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) d).mp hray)
  · intro hs
    obtain ⟨n, _, hn⟩ := (rightSlicePrecedingSegment_source_iff hp P k a (.inr d)).mp hs
    exact hoffOld ⟨n, hn.symm⟩
  · rintro ⟨q, hq, _⟩
    exact m0GeodesicRightSide_no_left_seed_of_zero_next_coalescence
      hp P T hleft hc k a hab q hq

/-- Helper toward Lemma 5.6: a finite diagnostic side whose raw rotation
can leave its edge carrier. This tests the imported first-return definition,
and is not a proposed model of a paper map. -/
private def rightSliceRotationEscapeExample (escape : Bool) :
    GeometricSideSubmap where
  vertices := {0}
  edges := {0}
  west := fun _ => 0
  east := fun _ => 0
  present := ∅
  rotation d e := escape = true ∧
    ((d = (0, false) ∧ e = (1, false)) ∨ (d = (1, false) ∧ e = (0, false)))
  faceNext := fun _ _ => False
  root := 0
  boundary := fun _ => (0, false)
  seam := fun _ => (0, false)

/-- Helper toward Lemma 5.6: the two diagnostic sides have the same
complete typed marked relations, including typed rotation. -/
private theorem rightSliceRotationEscapeExample_markedIso :
    Nonempty (GeometricSideMarkedIso
      (rightSliceRotationEscapeExample true) (rightSliceRotationEscapeExample false)) := by
  refine ⟨⟨Equiv.refl _, ?_⟩⟩
  intro t c e
  cases t <;> cases c <;> cases e <;> try rfl
  rename_i d e
  have hd : d.val.1 = 0 := d.property
  have he : e.val.1 = 0 := e.property
  change (true = true ∧ _) ↔ (false = true ∧ _)
  constructor
  · rintro ⟨_, ⟨hd0, he1⟩ | ⟨hd1, he0⟩⟩
    · have hh := congrArg Prod.fst he1
      exact False.elim (by omega)
    · have hh := congrArg Prod.fst hd1
      exact False.elim (by omega)
  · rintro ⟨hf, _⟩
    exact Bool.noConfusion hf

/-- Helper toward Lemma 5.6: typed marked isomorphism alone does not
transport the imported raw-dart first-return predicate. A two-step return
through an absent edge is visible to that predicate and invisible to the
typed isomorphism. This isolates an obstruction to the proposed descent
proof, without asserting a counterexample to source geometry. -/
theorem geoSliceRightFirstReturn_not_determined_by_typed_markedIso :
    ∃ M N : GeometricSideSubmap, Nonempty (GeometricSideMarkedIso M N) ∧
      geoSliceRightFirstReturn M {0} (0, false) (0, false) ∧
      ¬ geoSliceRightFirstReturn N {0} (0, false) (0, false) := by
  refine ⟨rightSliceRotationEscapeExample true, rightSliceRotationEscapeExample false,
    rightSliceRotationEscapeExample_markedIso, ?_, ?_⟩
  · refine ⟨rfl, rfl, 2, by omega,
      (fun j : Fin 3 => if j.val = 1 then (1, false) else (0, false)),
      rfl, rfl, ?_, ?_⟩
    · intro j
      fin_cases j <;> simp [rightSliceRotationEscapeExample]
    · intro j hj hjn
      have hjeq : j.val = 1 := by omega
      simp only [hjeq, ↓reduceIte, Set.mem_singleton_iff, ne_eq]
      decide
  · rintro ⟨_, _, n, hn, f, _, _, hstep, _⟩
    have hs := hstep ⟨0, hn⟩
    exact Bool.noConfusion hs.1

end DirectedDistances.PaperProofs.Section5















































































































































