/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart5
public import DirectedDistances.PlanarMap.D39PLDiskArcGluing4
import Mathlib.Topology.Perfect

/- # Polygon disk chart induction -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology
namespace Polyline

/-- Helper toward Proposition 5.16: cyclic simplicity excludes all lists shorter
than the triangle's four listed points. -/
theorem four_le_length_of_isCyclicSimple (c : Polyline) (hc : c.IsCyclicSimple) :
    4 ≤ c.points.length := hc.1

/-- Helper toward Proposition 5.16: the three distinct triangle vertices are
noncollinear, including when the source chooses a different extreme vertex. -/
theorem triangle_not_collinear (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : c.points.length = 4) :
    ¬ Collinear ℝ ({c.point 0, c.point 1, c.point 2} : Set ℂ) := by
  obtain ⟨i, hi, _, hnc⟩ := c.exists_noncollinear_lexicographic_min_vertex hc
  have hclose : c.point 3 = c.point 0 := by simpa [hlen] using hc.2.1.symm
  have hi3 : i < 3 := by omega
  intro h
  apply hnc
  interval_cases i <;> convert h using 1 <;>
    ext z <;> simp [hlen, hclose] <;> tauto

/-- Helper toward Proposition 5.16: a triangle's image is exactly its three
closed geometric sides. -/
theorem triangle_image (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : c.points.length = 4) :
    c.image = segment ℝ (c.point 0) (c.point 1) ∪
      segment ℝ (c.point 1) (c.point 2) ∪ segment ℝ (c.point 2) (c.point 0) := by
  have hclose : c.point 3 = c.point 0 := by simpa [hlen] using hc.2.1.symm
  ext z
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · left; left
      rw [← c.point_zero_eq_start] at hz
      exact hz ▸ left_mem_segment ℝ _ _
    · have hi3 : i < 3 := by omega
      interval_cases i
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr hz)
      · exact Or.inr (by simpa only [segmentAt, hclose] using hz)
  · rintro ((hz | hz) | hz)
    · exact Or.inr ⟨0, by omega, hz⟩
    · exact Or.inr ⟨1, by omega, hz⟩
    · exact Or.inr ⟨2, by omega, by simpa only [segmentAt, hclose] using hz⟩

/-- Helper toward Proposition 5.16: the winding-defined inside of a triangle
is precisely the interior of its convex hull. -/
theorem triangle_inside (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : c.points.length = 4) :
    c.inside = _root_.interior
      (convexHull ℝ ({c.point 0, c.point 1, c.point 2} : Set ℂ)) := by
  let K := convexHull ℝ ({c.point 0, c.point 1, c.point 2} : Set ℂ)
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hc.2.1
  have hnc := c.triangle_not_collinear hc hlen
  have him := c.triangle_image hc hlen
  have hfront : frontier (_root_.interior K) = c.image :=
    (frontier_triangle_interior _ _ _ hnc).trans him.symm
  have himK : c.image ⊆ K := by
    rw [← hfront]
    exact frontier_subset_closure.trans (by
      rw [show closure (_root_.interior K) = K from
        closure_triangle_interior _ _ _ hnc])
  have havoid : Kᶜ ⊆ c.imageᶜ := fun _ hz hw => hz (himK hw)
  have hout : Kᶜ ⊆ c.outside := by
    rcases c.subset_inside_or_outside_of_isPreconnected hclosed Kᶜ
        (isPathConnected_triangle_compl _ _ _).isConnected.isPreconnected havoid with h | h
    · obtain ⟨R, hR⟩ := c.exists_radius_exterior_subset_outside hclosed
      obtain ⟨z, hz, hzR⟩ := exists_norm_gt_triangle_compl
        (c.point 0) (c.point 1) (c.point 2) R
      exact False.elim ((h hz).2 (hR z hzR).2)
    · exact h
  have hinK : c.inside ⊆ K := by
    intro z hz
    by_contra hn
    exact hz.2 (hout hn).2
  have hin : c.inside ⊆ _root_.interior K :=
    interior_maximal hinK (c.isOpen_inside hclosed)
  apply Set.Subset.antisymm hin
  have havoid' : _root_.interior K ⊆ c.imageᶜ := by
    intro z hz hw
    have hf : z ∈ frontier (_root_.interior K) := hfront.symm ▸ hw
    exact hf.2 (by simpa only [interior_interior] using hz)
  rcases c.subset_inside_or_outside_of_isPreconnected hclosed (_root_.interior K)
      (convex_convexHull ℝ _).interior.isPreconnected havoid' with h | h
  · exact h
  · obtain ⟨z, hz⟩ := c.inside_nonempty_cyclic hc
    exact False.elim (hz.2 (h (hin hz)).2)

/-- Helper toward Proposition 5.16: the closed winding region of a triangle
is its filled convex hull. -/
theorem triangle_closure_inside (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : c.points.length = 4) :
    closure c.inside = convexHull ℝ ({c.point 0, c.point 1, c.point 2} : Set ℂ) := by
  rw [c.triangle_inside hc hlen]
  exact closure_triangle_interior _ _ _ (c.triangle_not_collinear hc hlen)

/-- Helper toward Proposition 5.16: every cyclically simple triangle has the
required disk chart, with its entire polygon boundary on the unit circle. -/
theorem exists_triangle_polygon_disk_chart (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : c.points.length = 4) :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure c.inside,
      ∀ z : Metric.closedBall (0 : ℂ) 1,
        (h z : ℂ) ∈ c.image ↔ ‖(z : ℂ)‖ = 1 := by
  obtain ⟨h, hb⟩ := exists_triangle_disk_chart
    (c.point 0) (c.point 1) (c.point 2) (c.triangle_not_collinear hc hlen)
  refine ⟨h.trans (Homeomorph.setCongr (c.triangle_closure_inside hc hlen).symm), ?_⟩
  intro z
  change (h z : ℂ) ∈ c.image ↔ _
  rw [c.triangle_image hc hlen]
  exact hb z

/-- Helper toward Proposition 5.16: the full boundary of a cyclically simple
polygon cannot be a closed straight segment. -/
theorem image_ne_segment (c : Polyline) (hc : c.IsCyclicSimple) (a b : ℂ) :
    c.image ≠ segment ℝ a b := by
  intro heq
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hc.2.1
  obtain ⟨z, hz⟩ := c.inside_nonempty_cyclic hc
  have hzseg : z ∈ (segment ℝ a b)ᶜ := by
    change z ∉ segment ℝ a b
    rw [← heq]
    exact hz.1
  rcases c.subset_inside_or_outside_of_isPreconnected hclosed (segment ℝ a b)ᶜ
      (isPathConnected_segment_compl a b).isConnected.isPreconnected
      (by rw [heq]) with hin | hout
  · obtain ⟨R, hR⟩ := c.exists_radius_exterior_subset_outside hclosed
    obtain ⟨w, hw, hwR⟩ := exists_norm_gt_segment_compl a b R
    exact (hin hw).2 (hR w hwR).2
  · exact hz.2 (hout hzseg).2

/-- Helper toward Proposition 5.16: a diagonal contained in a cyclic polygon's
boundary is a proper subset of that boundary. -/
theorem segment_ssubset_image (c : Polyline) (hc : c.IsCyclicSimple) (a b : ℂ)
    (hsub : segment ℝ a b ⊆ c.image) : segment ℝ a b ⊂ c.image := by
  exact Set.ssubset_iff_subset_ne.mpr ⟨hsub, (c.image_ne_segment hc a b).symm⟩

/-- Helper toward Proposition 5.16: deleting two distinct points from a cyclic
polygon boundary leaves a dense subset of that boundary. -/
theorem image_subset_closure_diff_pair (c : Polyline) (hc : c.IsCyclicSimple)
    (a b : ℂ) (hab : a ≠ b) : c.image ⊆ closure (c.image \ {a, b}) := by
  have hconn : IsConnected c.image := by
    rw [← c.range_toPath]
    exact isConnected_range c.toPath.continuous
  have hnon : c.image.Nontrivial := ⟨c.point 0, c.point_mem_image (by have := hc.1; omega),
    c.point 1, c.point_mem_image (by have := hc.1; omega), hc.2.2.1 0 (by have := hc.1; omega)⟩
  have hperf := hconn.isPreconnected.preperfect_of_nontrivial hnon
  have endpoint (x y : ℂ) (hxy : x ≠ y) (hx : x ∈ c.image) :
      x ∈ closure (c.image \ {x, y}) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hV : U ∩ ({y} : Set ℂ)ᶜ ∈ nhds x :=
      Filter.inter_mem hU (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hxy))
    obtain ⟨w, ⟨⟨hwU, hwy⟩, hw⟩, hwx⟩ := (accPt_iff_nhds.mp (hperf x hx)) _ hV
    exact ⟨w, hwU, hw, by simpa using And.intro hwx hwy⟩
  intro z hz
  by_cases hza : z = a
  · subst z
    exact endpoint a b hab hz
  by_cases hzb : z = b
  · subst z
    simpa only [Set.pair_comm b a] using endpoint b a hab.symm hz
  · apply subset_closure
    refine ⟨hz, ?_⟩
    simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hza hzb

/-- Helper toward Proposition 5.16: deleting the interior diagonal from the
original boundary leaves a dense subset of the original boundary. -/
theorem closure_image_diff_diagonal (c : Polyline) (hc : c.IsCyclicSimple)
    (a b : ℂ) (hab : a ≠ b)
    (hin : openSegment ℝ a b ⊆ c.inside) :
    closure (c.image \ segment ℝ a b) = c.image := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.sdiff_subset c.isCompact_image.isClosed
  · refine (c.image_subset_closure_diff_pair hc a b hab).trans (closure_mono ?_)
    rintro z ⟨hz, hzne⟩
    refine ⟨hz, ?_⟩
    intro hzs
    have hza : z ≠ a := fun h => hzne (Or.inl h)
    have hzb : z ≠ b := fun h => hzne (Or.inr h)
    exact (hin (mem_openSegment_of_ne_left_right hza.symm hzb.symm hzs)).1 hz

/-- Helper toward Proposition 5.16: the two remaining polygon boundaries,
with endpoint limits retained, cover exactly the original polygon boundary. -/
theorem split_outer_boundary (c c₁ c₂ : Polyline) (hc : c.IsCyclicSimple)
    (a b : ℂ) (hab : a ≠ b) (hin : openSegment ℝ a b ⊆ c.inside)
    (hunion : c₁.image ∪ c₂.image = c.image ∪ segment ℝ a b) :
    closure (c₁.image \ segment ℝ a b) ∪ closure (c₂.image \ segment ℝ a b) =
      c.image := by
  rw [← closure_union, ← Set.union_sdiff_distrib, hunion]
  have heq : (c.image ∪ segment ℝ a b) \ segment ℝ a b =
      c.image \ segment ℝ a b := by ext z; simp only [mem_sdiff, mem_union]; tauto
  rw [heq]
  exact c.closure_image_diff_diagonal hc a b hab hin

end Polyline

/-- Helper toward Proposition 5.16: the precise proper-boundary-arc gluing
obligation. This definition asserts no proof of the obligation. -/
@[expose] def D39PLArcGluingStatement : Prop :=
  ∀ (S₁ S₂ T₁ T₂ gamma : Set ℂ)
    (hT₁ : T₁ ⊆ S₁) (hT₂ : T₂ ⊆ S₂)
    (h₁ : Metric.closedBall (0 : ℂ) 1 ≃ₜ S₁)
    (h₂ : Metric.closedBall (0 : ℂ) 1 ≃ₜ S₂)
    (hb₁ : ∀ z : Metric.closedBall (0 : ℂ) 1,
      (h₁ z : ℂ) ∈ T₁ ↔ ‖(z : ℂ)‖ = 1)
    (hb₂ : ∀ z : Metric.closedBall (0 : ℂ) 1,
      (h₂ z : ℂ) ∈ T₂ ↔ ‖(z : ℂ)‖ = 1)
    (hinter : S₁ ∩ S₂ = gamma)
    (hgamma₁ : gamma ⊆ T₁) (hgamma₂ : gamma ⊆ T₂)
    (phi : Set.Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hproper₁ : gamma ≠ T₁) (hproper₂ : gamma ≠ T₂),
    ∃ H : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥(S₁ ∪ S₂),
      Set.range (fun z : {x : Metric.closedBall (0 : ℂ) 1 //
        ‖(x : ℂ)‖ = 1} => (H z : ℂ)) =
        closure (T₁ \ gamma) ∪ closure (T₂ \ gamma)

/-- Helper toward Proposition 5.16: the affine parameterization of a
nondegenerate segment by the interval `[-1,1]`. -/
@[expose] def polygonSegmentHomeomorph (a b : ℂ) (hab : a ≠ b) :
    Set.Icc (-1 : ℝ) 1 ≃ₜ segment ℝ a b := by
  let e := iccHomeoI (-1 : ℝ) 1 (by norm_num)
  let f : Set.Icc (0 : ℝ) 1 → segment ℝ a b := fun t =>
    ⟨Path.segment a b t, (Path.range_segment a b).le ⟨t, rfl⟩⟩
  have hf : Continuous f := (Path.segment a b).continuous.subtype_mk _
  have hfi : Function.Injective f := by
    intro t u h
    exact Path.segment_injective_of_ne hab (congrArg Subtype.val h)
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨t, ht⟩ := (Path.range_segment a b).ge z.property
    exact ⟨t, Subtype.ext ht⟩
  exact e.trans (hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩))

/-- Helper toward Proposition 5.16: the segment parameterization is explicitly
affine, with coefficient `(t+1)/2`. -/
theorem polygonSegmentHomeomorph_apply (a b : ℂ) (hab : a ≠ b)
    (t : Set.Icc (-1 : ℝ) 1) :
    (polygonSegmentHomeomorph a b hab t : ℂ) =
      (((t : ℝ) + 1) / 2) • (b - a) + a := by
  change AffineMap.lineMap a b ((iccHomeoI (-1 : ℝ) 1 (by norm_num)) t : ℝ) = _
  rw [iccHomeoI_apply_coe, AffineMap.lineMap_apply_module']
  norm_num

/-- Helper toward Proposition 5.16: the affine segment chart has the specified
left endpoint. -/
theorem polygonSegmentHomeomorph_left (a b : ℂ) (hab : a ≠ b) :
    (polygonSegmentHomeomorph a b hab ⟨-1, by norm_num⟩ : ℂ) = a := by
  rw [polygonSegmentHomeomorph_apply]
  norm_num

/-- Helper toward Proposition 5.16: the affine segment chart has the specified
right endpoint. -/
theorem polygonSegmentHomeomorph_right (a b : ℂ) (hab : a ≠ b) :
    (polygonSegmentHomeomorph a b hab ⟨1, by norm_num⟩ : ℂ) = b := by
  rw [polygonSegmentHomeomorph_apply]
  norm_num

namespace Polyline

/-- Helper toward Proposition 5.16: an interior-diagonal split supplies all
geometric side conditions for proper-boundary-arc gluing, independently of
any disk chart or gluing assumption. -/
theorem exists_diagonal_disk_gluing_data (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : 5 ≤ c.points.length) :
    ∃ (a b : ℂ) (c₁ c₂ : Polyline)
      (phi : Set.Icc (-1 : ℝ) 1 ≃ₜ segment ℝ a b),
      a ∈ c.image ∧ b ∈ c.image ∧ a ≠ b ∧
      c₁.IsCyclicSimple ∧ c₂.IsCyclicSimple ∧
      c₁.points.length < c.points.length ∧ c₂.points.length < c.points.length ∧
      openSegment ℝ a b ⊆ c.inside ∧
      c₁.image ∪ c₂.image = c.image ∪ segment ℝ a b ∧
      c₁.image ∩ c₂.image = segment ℝ a b ∧
      segment ℝ a b ⊂ c₁.image ∧ segment ℝ a b ⊂ c₂.image ∧
      closure c₁.inside ∩ closure c₂.inside = segment ℝ a b ∧
      closure (c₁.image \ segment ℝ a b) ∪ closure (c₂.image \ segment ℝ a b) = c.image ∧
      closure c₁.inside ∪ closure c₂.inside = closure c.inside ∧
      (∀ t : Set.Icc (-1 : ℝ) 1,
        (phi t : ℂ) = (((t : ℝ) + 1) / 2) • (b - a) + a) := by
  obtain ⟨a, b, c₁, c₂, ha, hb, hab, hc₁, hc₂, hlen₁, hlen₂,
    hin, hunion, hinter, hclunion, hclinter⟩ := c.exists_diagonal_closed_region_split hc hlen
  have hgamma₁ : segment ℝ a b ⊆ c₁.image := fun _ hz => (hinter.ge hz).1
  have hgamma₂ : segment ℝ a b ⊆ c₂.image := fun _ hz => (hinter.ge hz).2
  exact ⟨a, b, c₁, c₂, polygonSegmentHomeomorph a b hab,
    ha, hb, hab, hc₁, hc₂, hlen₁, hlen₂, hin, hunion, hinter,
    c₁.segment_ssubset_image hc₁ a b hgamma₁,
    c₂.segment_ssubset_image hc₂ a b hgamma₂, hclinter,
    c.split_outer_boundary c₁ c₂ hc a b hab hin hunion,
    hclunion.symm, polygonSegmentHomeomorph_apply a b hab⟩

/- Helper toward Proposition 5.16: strong induction constructs a disk chart
for every cyclically simple polygon, conditional only on the explicitly -/
theorem exists_polygon_disk_chart_of_arc_gluing
    (hglue : D39PLArcGluingStatement) :
    ∀ (c : Polyline), c.IsCyclicSimple →
      ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure c.inside,
        ∀ z : Metric.closedBall (0 : ℂ) 1,
          (h z : ℂ) ∈ c.image ↔ ‖(z : ℂ)‖ = 1 := by
  have main : ∀ n : ℕ, ∀ c : Polyline, c.points.length = n → c.IsCyclicSimple →
      ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure c.inside,
        ∀ z : Metric.closedBall (0 : ℂ) 1,
          (h z : ℂ) ∈ c.image ↔ ‖(z : ℂ)‖ = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hlen hc
      by_cases htriangle : c.points.length = 4
      · exact c.exists_triangle_polygon_disk_chart hc htriangle
      have hlarge : 5 ≤ c.points.length := by have := hc.1; omega
      obtain ⟨a, b, c₁, c₂, phi, _, _, _, hc₁, hc₂, hlen₁, hlen₂,
        _, _, _, hproper₁, hproper₂, hinter, houter, hunion, _⟩ :=
        c.exists_diagonal_disk_gluing_data hc hlarge
      obtain ⟨h₁, hb₁⟩ := ih c₁.points.length (by omega) c₁ rfl hc₁
      obtain ⟨h₂, hb₂⟩ := ih c₂.points.length (by omega) c₂ rfl hc₂
      have hT₁ : c₁.image ⊆ closure c₁.inside := by
        rw [c₁.closure_inside_eq_union_image hc₁]
        exact Set.subset_union_right
      have hT₂ : c₂.image ⊆ closure c₂.inside := by
        rw [c₂.closure_inside_eq_union_image hc₂]
        exact Set.subset_union_right
      obtain ⟨H, hcircle⟩ := hglue
        (closure c₁.inside) (closure c₂.inside) c₁.image c₂.image (segment ℝ a b)
        hT₁ hT₂ h₁ h₂ hb₁ hb₂ hinter hproper₁.subset hproper₂.subset phi
        (ne_of_lt hproper₁) (ne_of_lt hproper₂)
      have hrange : Set.range (fun z : {x : Metric.closedBall (0 : ℂ) 1 //
          ‖(x : ℂ)‖ = 1} => (H z : ℂ)) = c.image := hcircle.trans houter
      refine ⟨H.trans (Homeomorph.setCongr hunion), ?_⟩
      intro z
      change (H z : ℂ) ∈ c.image ↔ ‖(z : ℂ)‖ = 1
      constructor
      · intro hz
        obtain ⟨w, hw⟩ := hrange.ge hz
        have hwz : (w : Metric.closedBall (0 : ℂ) 1) = z :=
          H.injective (Subtype.ext hw)
        exact hwz ▸ w.property
      · intro hz
        exact hrange.le ⟨⟨z, hz⟩, rfl⟩
  intro c hc
  exact main c.points.length c rfl hc

end Polyline


























end DirectedDistances.PlanarMap

