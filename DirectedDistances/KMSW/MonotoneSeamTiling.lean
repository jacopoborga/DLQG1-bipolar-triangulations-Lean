module

public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.KMSW.MonotoneFamilyFaceData
public import DirectedDistances.KMSW.MonotoneXminGrowth
public import DirectedDistances.KMSW.FreshLeftRecurrence
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary
public import Mathlib.Order.Int.LeastGreatest

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

noncomputable section

variable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)







@[expose] def seamX (k : ℤ) : ℝ :=
  ((monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
    (boundaryVertex w h k)).re




private theorem seam_pos_layout (n v : ℕ) (hv : v < (kmswStage w n).nextVertex) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v = layoutPos w n v := by
  exact monotoneLimitDrawing_pos_layout w hfin _ n v hv




theorem seamX_lt_succ (k : ℤ) : seamX w h hfin k < seamX w h hfin (k + 1) := by
  let e := boundaryOuterEdge w h k
  have he := kmsw_edge_allocated_by_self w e
  have hv := kmswStage_endpoints_lt_nextVertex w e e he
  have hend := edge_endpoints_eq w he
  have hb := boundaryOuterEdge_endpoints w h k
  have hw : (kmswStage w e).west e = boundaryVertex w h k := hend.1.trans hb.1
  have ht : (kmswStage w e).east e = boundaryVertex w h (k + 1) :=
    hend.2.trans hb.2.1
  unfold seamX
  rw [← hw, ← ht, seam_pos_layout w hfin e _ hv.1,
    seam_pos_layout w hfin e _ hv.2]
  change (kmswStageRank w e ((kmswStage w e).west e) : ℝ) <
    (kmswStageRank w e ((kmswStage w e).east e) : ℝ)
  exact_mod_cast kmswStageRank_strict w e e he




theorem seamX_strictMono : StrictMono (seamX w h hfin) :=
  strictMono_int_of_lt_succ (seamX_lt_succ w h hfin)




private theorem seam_lower_vertex (n e v : ℕ)
    (he : e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR)
    (hv : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ k : ℤ, seamX w h hfin k = (layoutPos w n v).re := by
  obtain ⟨k, hk⟩ := stageLLLRVertex_eq_boundaryVertex w h v
    ⟨n, e, List.mem_append.mp he, hv⟩
  have heB := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
    simp only [List.mem_append] at he ⊢
    tauto)
  have hvB : v < (kmswStage w n).nextVertex := by
    rcases hv with rfl | rfl
    · exact (kmswStage_endpoints_lt_nextVertex w n e heB).1
    · exact (kmswStage_endpoints_lt_nextVertex w n e heB).2
  refine ⟨k, ?_⟩
  unfold seamX
  rw [hk, seam_pos_layout w hfin n v hvB]




private theorem seam_stage_extrema (n : ℕ) :
    (∃ k, seamX w h hfin k = (familyG w (monotone_family_all w) n).xmin) ∧
      (∃ k, seamX w h hfin k = (familyG w (monotone_family_all w) n).xmax) := by
  let G := familyG w (monotone_family_all w) n
  let es := (kmswStage w n).LL ++ (kmswStage w n).LR
  have hn := (kmswStage_boundary_nonempty w n).2
  have he := kmswStage_boundary_endpoints w n
  constructor
  · obtain ⟨k, hk⟩ := seam_lower_vertex w h hfin n (es.head hn) _
      (List.head_mem hn) (Or.inl rfl)
    refine ⟨k, hk.trans ?_⟩
    rw [← he.1]
    exact G.xmin_eq_upper_start.symm
  · obtain ⟨k, hk⟩ := seam_lower_vertex w h hfin n (es.getLast hn) _
      (List.getLast_mem hn) (Or.inr rfl)
    refine ⟨k, hk.trans ?_⟩
    rw [← he.2]
    exact G.xmax_eq_upper_end.symm




theorem seamX_unbounded (M : ℝ) :
    (∃ k, M < seamX w h hfin k) ∧ (∃ k, seamX w h hfin k < -M) := by
  have hL : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    refine ⟨n, ?_⟩
    have hm := le_max_left (-a) 1
    omega
  let Q := familyQ w (monotone_family_all w)
  let G := familyG w (monotone_family_all w)
  obtain ⟨N, hN⟩ := monotoneStage_xmax_unbounded (w := w) hR Q G (M + 1)
  obtain ⟨K, hK⟩ := monotoneStage_xmin_unbounded_below w
    (infinitelyManyFreshLeft_of_L_unbounded_below w hL) Q G (-M - 1)
  obtain ⟨i, hi⟩ := (seam_stage_extrema w h hfin N).2
  obtain ⟨j, hj⟩ := (seam_stage_extrema w h hfin K).1
  constructor
  · refine ⟨i, ?_⟩
    rw [hi]
    exact lt_of_lt_of_le (by linarith) (hN N le_rfl)
  · refine ⟨j, ?_⟩
    rw [hj]
    exact lt_of_le_of_lt (hK K le_rfl) (by linarith)




theorem seamX_tiling (x : ℝ) :
    ∃ k : ℤ, seamX w h hfin k ≤ x ∧ x ≤ seamX w h hfin (k + 1) := by
  obtain ⟨b, hb⟩ := (seamX_unbounded w h hfin x).1
  obtain ⟨a, ha⟩ := (seamX_unbounded w h hfin (-x)).2
  have ha' : seamX w h hfin a ≤ x := by linarith only [ha]
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun i => seamX w h hfin i ≤ x)
    ⟨b, fun i hi => (seamX_strictMono w h hfin).le_iff_le.mp (hi.trans hb.le)⟩
    ⟨a, ha'⟩
  refine ⟨k, hk, le_of_not_gt ?_⟩
  intro hlt
  have hh := hmax (k + 1) hlt.le
  omega




private theorem seam_reverse_image_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · have hz' : z = p.finish := by
      simpa only [Polyline.start_reverse, Set.mem_singleton_iff] using hz
    rw [hz', ← p.point_last_eq_finish]
    by_cases hlen : 2 ≤ p.points.length
    · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
      have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
      rw [Polyline.segmentAt, hidx]
      exact right_mem_segment ℝ _ _
    · have hlen1 : p.points.length = 1 := by
        have := List.length_pos_iff.mpr p.nonempty
        omega
      simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
      exact Or.inl rfl
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    have hrev : ∀ j, j < p.points.length →
        p.reverse.point j = p.point (p.points.length - 1 - j) := by
      intro j hj
      have hj' : p.points.length - 1 - j < p.points.length := by omega
      change p.points.reverse.getD j p.reverse.start =
        p.points.getD (p.points.length - 1 - j) p.start
      rw [List.getD_reverse j hj]
      rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj']
      rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj']
    have hidx : p.points.length - 1 - (i + 1) + 1 = p.points.length - 1 - i := by
      omega
    refine Or.inr ⟨p.points.length - 1 - (i + 1), by omega, ?_⟩
    simp only [Polyline.segmentAt, hrev i (by omega), hrev (i + 1) hi'] at hz
    simpa only [Polyline.segmentAt, hidx, segment_symm] using hz




private theorem seam_reverse_image (p : Polyline) : p.reverse.image = p.image := by
  apply Set.Subset.antisymm (seam_reverse_image_subset p)
  simpa only [Polyline.reverse_reverse] using seam_reverse_image_subset p.reverse





theorem seam_arc_image_graph (k : ℤ) :
    ∃ f : ℝ → ℝ,
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
        (futureMapBoundaryDart w h k)).image =
      {z : ℂ | seamX w h hfin k ≤ z.re ∧ z.re ≤ seamX w h hfin (k + 1) ∧
        z.im = f z.re} := by
  let e := boundaryOuterEdge w h k
  have he := kmsw_edge_allocated_by_self w e
  have hv := kmswStage_endpoints_lt_nextVertex w e e he
  have hend := edge_endpoints_eq w he
  have hb := boundaryOuterEdge_endpoints w h k
  have hw : (kmswStage w e).west e = boundaryVertex w h k := hend.1.trans hb.1
  have ht : (kmswStage w e).east e = boundaryVertex w h (k + 1) :=
    hend.2.trans hb.2.1
  obtain ⟨f, hf⟩ := layoutArc_image_graph w e e he
  refine ⟨f, ?_⟩
  have harc : (monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (futureMapBoundaryDart w h k) = (layoutArc w e e).reverse := by
    exact monotoneLimitDrawing_arc_layout w hfin _ e e he true
  rw [harc, seam_reverse_image, hf]
  have hl : seamX w h hfin k = (layoutPos w e ((kmswStage w e).west e)).re := by
    unfold seamX
    rw [← hw, seam_pos_layout w hfin e _ hv.1]
  have hr : seamX w h hfin (k + 1) =
      (layoutPos w e ((kmswStage w e).east e)).re := by
    unfold seamX
    rw [← ht, seam_pos_layout w hfin e _ hv.2]
  rw [hl, hr]





theorem seam_arc_vertical_sections (k : ℤ) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    (∀ z ∈ (P.arc (futureMapBoundaryDart w h k)).image,
      seamX w h hfin k ≤ z.re ∧ z.re ≤ seamX w h hfin (k + 1)) ∧
    ∀ x : ℝ, seamX w h hfin k ≤ x → x ≤ seamX w h hfin (k + 1) →
      ∃! z : ℂ, z ∈ (P.arc (futureMapBoundaryDart w h k)).image ∧ z.re = x := by
  obtain ⟨f, hf⟩ := seam_arc_image_graph w h hfin k
  constructor
  · intro z hz
    rw [hf] at hz
    exact ⟨hz.1, hz.2.1⟩
  · intro x hx hy
    refine ⟨⟨x, f x⟩, ⟨?_, rfl⟩, ?_⟩
    · rw [hf]
      exact ⟨hx, hy, rfl⟩
    · intro z hz
      rw [hf] at hz
      apply Complex.ext hz.2
      exact hz.1.2.2.trans (congrArg f hz.2)

end
end DirectedDistances.KMSW
