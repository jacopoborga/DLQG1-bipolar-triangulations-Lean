module

public import DirectedDistances.PaperProofs.Section4.ThinMapSideConfinement

/-! # Arc confinement in the closed side regions

Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Proper graph rays identify the frontier; embedding disjointness then confines each arc. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter Quiver Set
open scoped Topology

namespace Polyline

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem segmentAt_iff_heightFn {p : Polyline} (hp : p.XMonotone)
    {i : ℕ} (hi : i + 1 < p.points.length) {z : ℂ} :
    z ∈ p.segmentAt i ↔
      (p.point i).re ≤ z.re ∧ z.re ≤ (p.point (i + 1)).re ∧
        z.im = p.heightFn z.re := by
  have hab : (p.point i).re < (p.point (i + 1)).re :=
    p.point_re_lt hp (Nat.lt_succ_self i) hi
  rw [Polyline.segmentAt, mem_segment_iff_height hab]
  constructor
  · rintro ⟨hl, hr, hz⟩
    have hlinear := p.heightFn_linear_on_segment hp hi hl hr
    have hlinear' : p.heightFn z.re = segmentHeight (p.point i)
        (p.point (i + 1)) z.re := by
      simpa [segmentHeight] using hlinear
    exact ⟨hl, hr, hz.trans hlinear'.symm⟩
  · rintro ⟨hl, hr, hz⟩
    have hlinear := p.heightFn_linear_on_segment hp hi hl hr
    have hlinear' : p.heightFn z.re = segmentHeight (p.point i)
        (p.point (i + 1)) z.re := by
      simpa [segmentHeight] using hlinear
    exact ⟨hl, hr, hz.trans hlinear'⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem exists_segment_covering {p : Polyline}
    (hlen : 2 ≤ p.points.length) {x : ℝ} (hlo : p.start.re < x)
    (hhi : x ≤ p.finish.re) :
    ∃ i, i + 1 < p.points.length ∧
      (p.point i).re ≤ x ∧ x ≤ (p.point (i + 1)).re := by
  let n := p.points.length - 1
  have hn : n < p.points.length := by dsimp [n]; omega
  have hlast : p.point n = p.finish := by
    dsimp [n]
    exact p.point_last_eq_finish
  have hex : ∃ j, x ≤ (p.point j).re := ⟨n, by rw [hlast]; exact hhi⟩
  let j := Nat.find hex
  have hj : x ≤ (p.point j).re := Nat.find_spec hex
  have hjle : j ≤ n := Nat.find_min' hex (by rw [hlast]; exact hhi)
  have hjlt : j < p.points.length := lt_of_le_of_lt hjle hn
  have hp0 : p.point 0 = p.start := p.point_zero_eq_start
  have hjpos : 0 < j := by
    by_contra hjnot
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos hjnot
    have hj' : x ≤ (p.point 0).re := by simpa [hjzero] using hj
    rw [hp0] at hj'
    exact (not_le_of_gt hlo) hj'
  let i := j - 1
  have hij : i + 1 = j := by dsimp [i]; omega
  have hilt : i + 1 < p.points.length := by rw [hij]; exact hjlt
  have hleft : (p.point i).re < x := by
    apply lt_of_not_ge
    intro hxi
    have hnot := Nat.find_min hex (show i < j by dsimp [i]; omega)
    exact hnot hxi
  exact ⟨i, hilt, hleft.le, by simpa [hij] using hj⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem image_eq_heightFn_graph {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) :
    p.image = {z | p.start.re ≤ z.re ∧ z.re ≤ p.finish.re ∧
      z.im = p.heightFn z.re} := by
  have hp0 : p.point 0 = p.start := p.point_zero_eq_start
  have hn : p.points.length - 1 < p.points.length := by omega
  have hlast : p.point (p.points.length - 1) = p.finish :=
    p.point_last_eq_finish
  have hstartfinish : p.start.re < p.finish.re := by
    rw [← hp0, ← hlast]
    exact p.point_re_lt hp (by omega) hn
  ext z
  constructor
  · intro hz
    rcases hz with rfl | ⟨i, hi, hseg⟩
    · have hval : p.heightFn p.start.re = p.start.im := by
        rw [← hp0]
        exact p.heightFn_point hp (by omega)
      exact ⟨le_rfl, hstartfinish.le, hval.symm⟩
    · have hi0 : i < p.points.length := by omega
      have hleft : p.start.re ≤ (p.point i).re := by
        rw [← hp0]
        exact p.point_re_le_of_le hp (Nat.zero_le i) hi0
      have hiright : (p.point (i + 1)).re ≤ p.finish.re := by
        rw [← hlast]
        apply p.point_re_le_of_le hp
        · omega
        · exact hn
      obtain ⟨hl, hr, hh⟩ := (segmentAt_iff_heightFn hp hi).mp hseg
      exact ⟨hleft.trans hl, hr.trans hiright, hh⟩
  · rintro ⟨hl, hr, hh⟩
    by_cases hx : z.re = p.start.re
    · have hval : p.heightFn z.re = p.start.im := by
        rw [hx, ← hp0]
        exact p.heightFn_point hp (by omega)
      have hz' : z = p.start := by
        apply Complex.ext
        · exact hx
        · exact hh.trans hval
      subst z
      exact Or.inl rfl
    · have hlo : p.start.re < z.re := lt_of_le_of_ne hl (Ne.symm hx)
      obtain ⟨i, hi, hiL, hiR⟩ :=
        exists_segment_covering hlen hlo hr
      apply Or.inr
      refine ⟨i, hi, ?_⟩
      exact (segmentAt_iff_heightFn hp hi).mpr ⟨hiL, hiR, hh⟩

end Polyline

private theorem continuous_arc_graph (p : Polyline) :
    Continuous (fun x : ℝ => (⟨x, p.heightFn x⟩ : ℂ)) := by
  have hf := Complex.continuous_ofReal.add
    ((Complex.continuous_ofReal.comp p.continuous_heightFn).mul
      (continuous_const (y := Complex.I)))
  convert hf using 1
  funext x
  apply Complex.ext <;> simp

private theorem arc_subset_of_frontier_avoidance {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) {S : Set ℂ} (hS : IsClosed S)
    (hstart : p.start ∈ S)
    (havoid : ∀ z ∈ p.image, z ≠ p.finish → z ∉ frontier S) : p.image ⊆ S := by
  let f : ℝ → ℂ := fun x => ⟨x, p.heightFn x⟩
  have hf : Continuous f := continuous_arc_graph p
  have hgraph := Polyline.image_eq_heightFn_graph hp hlen
  have hab : p.start.re < p.finish.re := by
    rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
    exact p.point_re_lt hp (by omega) (by omega)
  have hfi : ∀ t ∈ Icc p.start.re p.finish.re, f t ∈ p.image := by
    intro t ht
    rw [hgraph]
    exact ⟨ht.1, ht.2, rfl⟩
  have hfs : f p.start.re = p.start := by
    apply Complex.ext
    · rfl
    · change p.heightFn p.start.re = p.start.im
      rw [← p.point_zero_eq_start]
      exact p.heightFn_point hp (by omega)
  have hconn : IsPreconnected (f '' Ico p.start.re p.finish.re) :=
    isPreconnected_Ico.image f hf.continuousOn
  have hinside : f '' Ico p.start.re p.finish.re ⊆ interior S := by
    apply hconn.subset_of_closure_inter_subset isOpen_interior
    · refine ⟨p.start, ⟨p.start.re, ⟨le_rfl, hab⟩, hfs⟩, ?_⟩
      exact (self_sdiff_frontier S) ▸ ⟨hstart, havoid _ (Or.inl rfl)
        (fun h => hab.ne (congrArg Complex.re h))⟩
    · rintro z ⟨hz, t, ht, rfl⟩
      have hzS : f t ∈ S := hS.closure_subset (closure_mono interior_subset hz)
      have hznot := havoid (f t) (hfi t ⟨ht.1, ht.2.le⟩)
        (fun h => ht.2.ne (congrArg Complex.re h))
      exact (self_sdiff_frontier S) ▸ ⟨hzS, hznot⟩
  have hcl : closure (f '' Ico p.start.re p.finish.re) ⊆ S :=
    closure_minimal (hinside.trans interior_subset) hS
  intro z hz
  obtain ⟨hl, hr, hh⟩ := (Set.ext_iff.mp hgraph z).mp hz
  apply hcl
  apply image_closure_subset_closure_image hf
  refine ⟨z.re, ?_, ?_⟩
  · rw [closure_Ico hab.ne]
    exact ⟨hl, hr⟩
  · apply Complex.ext
    · rfl
    · exact hh.symm

private theorem rayDomain_mem_nhds {x₀ x : ℝ} {X : WithTop ℝ}
    (hx : x₀ < x) (hX : (x : WithTop ℝ) < X) : rayDomain x₀ X ∈ 𝓝 x := by
  induction X using WithTop.recTopCoe with
  | top =>
    filter_upwards [eventually_gt_nhds hx] with t ht
    exact ⟨ht.le, WithTop.coe_lt_top _⟩
  | coe b =>
    have hxb : x < b := WithTop.coe_lt_coe.mp hX
    filter_upwards [eventually_gt_nhds hx, eventually_lt_nhds hxb] with t ht hb
    exact ⟨ht.le, WithTop.coe_lt_coe.mpr hb⟩

private theorem closedBetween_frontier_subset_traces {S T : Set ℂ} {x₀ : ℝ}
    (hS : ProperGraphRay S x₀) (hT : ProperGraphRay T x₀)
    (hsource : ∃ q ∈ S ∩ T, q.re = x₀) :
    frontier (closedBetween S T) ⊆ S ∪ T := by
  have hclosed := isClosed_closedBetween hS hT
  obtain ⟨XS, fS, hXS, hSc, eS, hSesc⟩ := hS
  obtain ⟨XT, fT, hXT, hTc, eT, _⟩ := hT
  obtain ⟨q, ⟨hqS, hqT⟩, hq⟩ := hsource
  have hqS' := (Set.ext_iff.mp eS q).mp hqS
  have hqT' := (Set.ext_iff.mp eT q).mp hqT
  have heq : fS x₀ = fT x₀ := by
    rw [← hq]
    exact hqS'.2.symm.trans hqT'.2
  intro z hz
  have hzreg := (mem_closedBetween_iff eS eT z).mp (hclosed.frontier_subset hz)
  by_contra hn
  have hnS : z ∉ S := fun h => hn (Or.inl h)
  have hnT : z ∉ T := fun h => hn (Or.inr h)
  have hlow : fT z.re < z.im := by
    apply lt_of_le_of_ne hzreg.2.1
    intro he
    exact hnT ((Set.ext_iff.mp eT z).mpr ⟨hzreg.1, he.symm⟩)
  have hx₀ : x₀ < z.re := by
    apply lt_of_le_of_ne hzreg.1.1
    intro he
    have hu := hzreg.2.2 (show z.re ∈ rayDomain x₀ XS from
      ⟨he ▸ le_rfl, he ▸ hXS⟩)
    rw [← he, heq] at hu
    rw [← he] at hlow
    exact (not_lt_of_ge hu) hlow
  have hdomT := rayDomain_mem_nhds hx₀ hzreg.1.2
  have hct := hTc.continuousAt hdomT
  have hnearT : ∀ᶠ u : ℂ in 𝓝 z,
      u.re ∈ rayDomain x₀ XT ∧ fT u.re < u.im := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually hdomT,
      (hct.comp Complex.continuous_re.continuousAt).eventually_lt
        Complex.continuous_im.continuousAt hlow] with u hu hh
    exact ⟨hu, hh⟩
  have hnearS : ∀ᶠ u : ℂ in 𝓝 z,
      u.re ∈ rayDomain x₀ XS → u.im ≤ fS u.re := by
    by_cases hxS : z.re ∈ rayDomain x₀ XS
    · have hu : z.im < fS z.re := by
        apply lt_of_le_of_ne (hzreg.2.2 hxS)
        intro he
        exact hnS ((Set.ext_iff.mp eS z).mpr ⟨hxS, he⟩)
      have hc := hSc.continuousAt (rayDomain_mem_nhds hx₀ hxS.2)
      filter_upwards [Complex.continuous_im.continuousAt.eventually_lt
        (hc.comp Complex.continuous_re.continuousAt) hu] with u hu
      exact fun _ => hu.le
    · obtain ⟨a, ha, hbig⟩ := hSesc (z.im + 1)
      have hza : a < z.re := by
        by_contra hh
        apply hxS
        exact ⟨hx₀.le, lt_of_le_of_lt (WithTop.coe_le_coe.mpr (le_of_not_gt hh)) ha.2⟩
      filter_upwards [Complex.continuous_re.continuousAt.eventually
        (eventually_gt_nhds hza), Complex.continuous_im.continuousAt.eventually
        (eventually_lt_nhds (lt_add_one z.im))] with u hu hiy
      intro hud
      exact hiy.le.trans (hbig u.re hud hu.le)
  have hinterior : z ∈ interior (closedBetween S T) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hnearT, hnearS] with u hu hv
    exact (mem_closedBetween_iff eS eT u).mpr ⟨hu.1, hu.2.le, hv⟩
  exact (mem_frontier_iff_notMem_interior (hclosed.frontier_subset hz)).mp hz hinterior

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
  (P : InfinitePresentPath w ⟨0⟩)

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)

private theorem drawingFamily (w : ℕ → Fin 3) :
    ∀ n, ∃ Q : StageDrawing w n, Nonempty (MonotoneStageInvariant w n Q) :=
  fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
    ((monotone_family_all w) n).choose_spec⟩

local notation "F" => drawingFamily w

private theorem path_proper (Q : InfinitePresentPath w ⟨0⟩) :
    ProperGraphRay (pathTrace G (fun i => (Q.edge i, false))) ((G).pos 0).re := by
  have h := infinitePresentPath_properGraphRay hfin F Q
  have hs : ((monotoneLimitDrawing w hfin F).arc (Q.edge 0, false)).start =
      (G).pos 0 := by
    rw [(monotoneLimitDrawing w hfin F).arc_start]
    exact congrArg (G).pos Q.first_edge_outgoing.2
  rw [hs] at h
  exact h

private theorem boundary_proper (a : ThinMapSide) :
    ProperGraphRay (pathTrace G (thinMapBoundaryDart w hfin hL htrans hR a))
      ((G).pos 0).re := by
  cases a with
  | left => exact path_proper w hfin (thinMapLeftBoundaryPath w hfin hL htrans hR)
  | right => exact path_proper w hfin (kmswRightmostPath w hfin hL htrans hR 0)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
theorem thinMapSideRegion_isClosed (a : ThinMapSide) :
    IsClosed (thinMapSideRegion w hfin hL htrans hR P a) := by
  cases a with
  | left =>
    exact isClosed_closedBetween (boundary_proper w hfin hL htrans hR .left)
      (path_proper w hfin P)
  | right =>
    exact isClosed_closedBetween (path_proper w hfin P)
      (boundary_proper w hfin hL htrans hR .right)

private theorem boundary_west (a : ThinMapSide) (i : ℕ) :
    edgeWest w (thinMapBoundaryDart w hfin hL htrans hR a i).1 =
      thinMapBoundaryVertex w hfin hL htrans hR a i := by
  cases a with
  | left =>
    cases i with
    | zero => exact (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.1
    | succ i => exact ((kmswLeftBoundary_infinite_present_path w htrans hL hR).2.1 i).symm
  | right =>
    let B := kmswRightmostPath w hfin hL htrans hR 0
    cases i with
    | zero => exact B.first_edge_outgoing.2
    | succ i => exact (infinitePresentPath_edge_chain B i).symm

private theorem arc_avoids_trace (es vs : ℕ → ℕ)
    (hw : ∀ i, edgeWest w (es i) = vs i)
    (he : ∀ i, edgeEast w (es i) = vs (i + 1)) (e : ℕ)
    (hne : ∀ i, edgeWest w e ≠ vs i) {z : ℂ}
    (hz : z ∈ ((G).arc (e, false)).image)
    (hzf : z ≠ ((G).arc (e, false)).finish) :
    z ∉ pathTrace G (fun i => (es i, false)) := by
  intro ht
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
  let p := (G).arc (e, false)
  let q := (G).arc (es i, false)
  have hpv (v : ℕ) (hv : z = (G).pos v) : z = p.start := by
    by_contra hs
    exact (G).interior_avoids_vertices (e, false) v
      (hv ▸ ⟨hz, by simpa only [mem_insert_iff, mem_singleton_iff, not_or]
        using And.intro hs hzf⟩)
  have hnstart (j : ℕ) : z ≠ (G).pos (vs j) := by
    intro hj
    have hs := hpv (vs j) hj
    have hpos : (G).pos (edgeWest w e) = (G).pos (vs j) := by
      exact ((G).arc_start (e, false)).symm.trans (hs.symm.trans hj)
    exact hne j ((G).pos_injective hpos)
  have hqs : z ≠ q.start := by
    rw [(G).arc_start]
    change z ≠ (G).pos (edgeWest w (es i))
    rw [hw i]
    exact hnstart i
  have hqf : z ≠ q.finish := by
    rw [(G).arc_finish]
    change z ≠ (G).pos (edgeEast w (es i))
    rw [he i]
    exact hnstart (i + 1)
  have hqi : z ∈ q.interior := ⟨hi, by
    simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hqs hqf⟩
  by_cases hs : z = p.start
  · have hs' : z = (G).pos (edgeWest w e) := hs.trans ((G).arc_start _)
    exact (G).interior_avoids_vertices (es i, false) (edgeWest w e) (hs' ▸ hqi)
  · have hpi : z ∈ p.interior := ⟨hz, by
      simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hs hzf⟩
    have hneq : (es i, false) ≠ (e, false) := by
      intro hh
      have hh' : es i = e := congrArg Prod.fst hh
      exact hne i (hh' ▸ hw i)
    have hdis := (G).interior_disjoint (e, false) (es i, false) hneq (by simp)
    exact Set.disjoint_left.mp hdis hpi hqi

private theorem source_mem_trace (Q : InfinitePresentPath w ⟨0⟩) :
    (G).pos 0 ∈ pathTrace G (fun i => (Q.edge i, false)) := by
  refine Set.mem_iUnion.mpr ⟨0, ?_⟩
  have hs : ((G).arc (Q.edge 0, false)).start = (G).pos 0 := by
    rw [(G).arc_start]
    exact congrArg (G).pos Q.first_edge_outgoing.2
  rw [← hs]
  exact Or.inl rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The frontier of the side region lies on the seam or exterior boundary trace. -/
theorem thinMapSideRegion_frontier_subset_traces (a : ThinMapSide) :
    frontier (thinMapSideRegion w hfin hL htrans hR P a) ⊆
      pathTrace G (fun i => (P.edge i, false)) ∪
        pathTrace G (thinMapBoundaryDart w hfin hL htrans hR a) := by
  have hs := source_mem_trace w hfin P
  have hb : (G).pos 0 ∈ pathTrace G (thinMapBoundaryDart w hfin hL htrans hR a) := by
    cases a with
    | left => exact source_mem_trace w hfin (thinMapLeftBoundaryPath w hfin hL htrans hR)
    | right => exact source_mem_trace w hfin (kmswRightmostPath w hfin hL htrans hR 0)
  cases a with
  | left =>
    intro z hz
    have h := closedBetween_frontier_subset_traces
      (boundary_proper w hfin hL htrans hR .left) (path_proper w hfin P)
      ⟨(G).pos 0, ⟨hb, hs⟩, rfl⟩ hz
    exact h.elim Or.inr Or.inl
  | right =>
    exact closedBetween_frontier_subset_traces (path_proper w hfin P)
      (boundary_proper w hfin hL htrans hR .right) ⟨(G).pos 0, ⟨hs, hb⟩, rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A present edge starting in the side away from both boundary vertex sequences has
its entire arc in that side, including an east endpoint on either boundary. -/
theorem thinMapInteriorArcConfinement (a : ThinMapSide) :
    ThinMapInteriorArcConfinement w hfin hL htrans hR P a := by
  have hfront := thinMapSideRegion_frontier_subset_traces w hfin hL htrans hR P a
  intro e _ hv hseam hboundary
  have hm : ((G).arc (e, false)).XMonotone := by
    change ((monotoneLimitDrawing w hfin F).arc (e, false)).XMonotone
    rw [monotoneLimitDrawing_arc_layout w hfin F e e
      (kmsw_edge_allocated_by_self w e) false]
    exact layoutArc_points_pairwise w e e (kmsw_edge_allocated_by_self w e)
  apply arc_subset_of_frontier_avoidance hm ((G).arc_length (e, false))
    (thinMapSideRegion_isClosed w hfin hL htrans hR P a)
  · rw [(G).arc_start]
    exact hv
  · intro z hz hzf hf
    rcases hfront hf with hs | hb
    · exact arc_avoids_trace w hfin P.edge (fun i => (P.initial i).1.id)
        (fun i => (P.edge_outgoing_at_initial w i).2)
        (fun i => (P.edge_incoming_at_succ w i).2) e hseam hz hzf hs
    · have he : ∀ i, edgeEast w
          (thinMapBoundaryDart w hfin hL htrans hR a i).1 =
            thinMapBoundaryVertex w hfin hL htrans hR a (i + 1) := fun _ => rfl
      have hd : thinMapBoundaryDart w hfin hL htrans hR a =
          (fun i => ((thinMapBoundaryDart w hfin hL htrans hR a i).1, false)) := by
        funext i
        cases a <;> rfl
      rw [hd] at hb
      exact arc_avoids_trace w hfin
        (fun i => (thinMapBoundaryDart w hfin hL htrans hR a i).1)
        (thinMapBoundaryVertex w hfin hL htrans hR a)
        (boundary_west w hfin hL htrans hR a) he e hboundary hz hzf hb

end DirectedDistances.PaperProofs.Section4
