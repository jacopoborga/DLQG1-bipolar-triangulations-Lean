module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfSideRange
public import DirectedDistances.PaperProofs.Section4.ThinMapArcConfinement

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Off-prefix geometric arcs avoid the infinite seam in their interiors, whether or
not their edges have an orientation. Boundary arcs and the connectedness argument
reduce confinement to one fixed interior point per nonboundary edge. The remaining
claim is `AncestorPosHalfOffPrefixArcSeedIdentification`; it is not asserted.

The good-cut witnesses include their prefix equation. Source side-range
identification and realization are proved only conditional on -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver Set
open scoped Classical Topology

section Drawing

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Distinct geometric edges have interiors disjoint from any specified edge trace.
No orientation or edge-presence assumption is used. -/
theorem thinMapArc_interior_disjoint_trace (e : ℕ) (es : ℕ → ℕ)
    (hne : ∀ i, e ≠ es i) :
    Disjoint ((G).arc (e, false)).interior
      (pathTrace G (fun i => (es i, false))) := by
  apply Set.disjoint_left.mpr
  intro z hz ht
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
  have hs : z ≠ ((G).arc (es i, false)).start := by
    intro hh
    rw [(G).arc_start] at hh
    exact (G).interior_avoids_vertices (e, false) (edgeWest w (es i)) (hh ▸ hz)
  have hf : z ≠ ((G).arc (es i, false)).finish := by
    intro hh
    rw [(G).arc_finish] at hh
    exact (G).interior_avoids_vertices (e, false) (edgeEast w (es i)) (hh ▸ hz)
  have hqi : z ∈ ((G).arc (es i, false)).interior := ⟨hi, by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using And.intro hs hf⟩
  have hd := (G).interior_disjoint (e, false) (es i, false)
    (fun hh => hne i (congrArg Prod.fst hh).symm) (by simp)
  exact Set.disjoint_left.mp hd hz hqi

end Drawing

section Half

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
  (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every concrete half dart has an edge allocated in its uncut stage. -/
theorem ancestorPos_edge_allocated (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    (ancestorPosDartId w t R hR I a d).1 < (kmswStage w t).nextEdge :=
  (I.toEquiv (ancestorPosDartMap R hR a d)).1.isLt

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An off-prefix half edge differs from every edge of the infinite seam, including
all indices beyond the represented finite path. -/
theorem ancestorPos_offPrefix_ne_seamEdge (P : InfinitePresentPath w ⟨0⟩)
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (hoff : ∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val)
    (i : ℕ) : (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i := by
  intro he
  have hb : P.edge i < (kmswStage w t).nextEdge := by
    rw [← he]
    exact ancestorPos_edge_allocated w t R hR I a d
  have hi := ancestorPos_seam_index_lt_of_allocated w t R hR I P hp i hb
  exact hoff ⟨i, hi⟩ he

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The complete infinite seam misses the interior of every off-prefix half edge.
This includes geometric edges without a directed orientation. -/
theorem ancestorPos_offPrefix_interior_disjoint_seamTrace
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (P : InfinitePresentPath w ⟨0⟩)
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (hoff : ∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val) :
    Disjoint
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
        ((ancestorPosDartId w t R hR I a d).1, false)).interior
      (pathTrace (monotoneFamilyDrawing w hfin (monotone_family_all w))
        (fun i => (P.edge i, false))) :=
  thinMapArc_interior_disjoint_trace w hfin _ P.edge
    (ancestorPos_offPrefix_ne_seamEdge w t R hR I a P hp d hoff)

end Half

namespace Polyline

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seed_segmentAt_iff_heightFn {p : Polyline} (hp : p.XMonotone)
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
private theorem seed_exists_segment_covering {p : Polyline}
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
private theorem seed_image_eq_heightFn_graph {p : Polyline} (hp : p.XMonotone)
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
      obtain ⟨hl, hr, hh⟩ := (seed_segmentAt_iff_heightFn hp hi).mp hseg
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
        seed_exists_segment_covering hlen hlo hr
      apply Or.inr
      refine ⟨i, hi, ?_⟩
      exact (seed_segmentAt_iff_heightFn hp hi).mpr ⟨hiL, hiR, hh⟩


/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The interior is the continuous graph on the open endpoint interval. -/
private theorem seed_interior_eq_graph {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) :
    p.interior = (fun t : ℝ => (⟨t, p.heightFn t⟩ : ℂ)) ''
      Ioo p.start.re p.finish.re := by
  have hg := seed_image_eq_heightFn_graph hp hlen
  have hs : p.heightFn p.start.re = p.start.im := by
    rw [← p.point_zero_eq_start]
    exact p.heightFn_point hp (by omega)
  have hf : p.heightFn p.finish.re = p.finish.im := by
    rw [← p.point_last_eq_finish]
    exact p.heightFn_point hp (by omega)
  ext z
  constructor
  · rintro ⟨hz, hn⟩
    have hb := (Set.ext_iff.mp hg z).mp hz
    have hl : p.start.re < z.re := by
      refine lt_of_le_of_ne hb.1 ?_
      intro he
      have hz : z = p.start := Complex.ext he.symm (by rw [hb.2.2, ← he, hs])
      exact hn (Or.inl hz)
    have hr : z.re < p.finish.re := by
      refine lt_of_le_of_ne hb.2.1 ?_
      intro he
      have hz : z = p.finish := Complex.ext he (by rw [hb.2.2, he, hf])
      exact hn (Or.inr hz)
    exact ⟨z.re, ⟨hl, hr⟩, Complex.ext rfl hb.2.2.symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(Set.ext_iff.mp hg _).mpr ⟨ht.1.le, ht.2.le, rfl⟩, ?_⟩
    rintro (hs | hf)
    · exact ht.1.ne (congrArg Complex.re hs).symm
    · exact ht.2.ne (congrArg Complex.re hf)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seed_continuous_graph (p : Polyline) :
    Continuous (fun t : ℝ => (⟨t, p.heightFn t⟩ : ℂ)) := by
  have hf := Complex.continuous_ofReal.add
    ((Complex.continuous_ofReal.comp p.continuous_heightFn).mul
      (continuous_const (y := Complex.I)))
  convert hf using 1
  funext t
  apply Complex.ext <;> simp

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Removing both endpoints leaves a preconnected arc dense in the complete arc. -/
private theorem seed_interior_preconnected_dense {p : Polyline} (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) :
    IsPreconnected p.interior ∧ p.image ⊆ closure p.interior := by
  have he := seed_interior_eq_graph hp hlen
  have hc := seed_continuous_graph p
  constructor
  · rw [he]
    exact isPreconnected_Ioo.image _ hc.continuousOn
  · intro z hz
    have hg := seed_image_eq_heightFn_graph hp hlen
    obtain ⟨hl, hr, hh⟩ := (Set.ext_iff.mp hg z).mp hz
    have hab : p.start.re < p.finish.re := by
      rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
      exact p.point_re_lt hp (by omega) (by omega)
    rw [he]
    apply image_closure_subset_closure_image hc
    refine ⟨z.re, ?_, Complex.ext rfl hh.symm⟩
    rw [closure_Ioo hab.ne]
    exact ⟨hl, hr⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
One interior point determines the closed side of an arc avoiding its frontier. -/
private theorem seed_image_subset_of_frontier_avoidance {p : Polyline}
    (hp : p.XMonotone) (hlen : 2 ≤ p.points.length) {S : Set ℂ} (hS : IsClosed S)
    (hmeet : (p.interior ∩ S).Nonempty)
    (havoid : Disjoint p.interior (frontier S)) : p.image ⊆ S := by
  obtain ⟨hconn, hdense⟩ := seed_interior_preconnected_dense hp hlen
  have hi : p.interior ⊆ interior S := by
    apply hconn.subset_of_closure_inter_subset isOpen_interior
    · obtain ⟨z, hz, hzS⟩ := hmeet
      refine ⟨z, hz, ?_⟩
      exact (self_sdiff_frontier S) ▸
        ⟨hzS, fun hf => Set.disjoint_left.mp havoid hz hf⟩
    · rintro z ⟨hz, hzp⟩
      have hzS := hS.closure_subset (closure_mono interior_subset hz)
      exact (self_sdiff_frontier S) ▸
        ⟨hzS, fun hf => Set.disjoint_left.mp havoid hzp hf⟩
  exact hdense.trans (closure_minimal (hi.trans interior_subset) hS)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The first-segment midpoint is interior to every nondegenerate monotone arc. -/
private theorem seed_midpoint_mem_interior (p : Polyline) (hm : p.XMonotone)
    (hlen : 2 ≤ p.points.length) :
    midpoint ℝ (p.point 0) (p.point 1) ∈ p.interior := by
  let z := midpoint ℝ (p.point 0) (p.point 1)
  have hfirst := p.point_re_lt hm (show 0 < 1 by omega) (show 1 < _ by omega)
  have hlast := p.point_re_le_of_le hm (show 1 ≤ p.points.length - 1 by omega)
    (show p.points.length - 1 < p.points.length by omega)
  rw [p.point_last_eq_finish] at hlast
  have hmean : z.re + z.re = (p.point 0).re + (p.point 1).re :=
    congrArg Complex.re (midpoint_add_self ℝ (p.point 0) (p.point 1))
  have hs : z ≠ p.start := by
    intro he
    have hh := congrArg Complex.re he
    rw [← p.point_zero_eq_start] at hh
    linarith only [hh, hmean, hfirst]
  have hf : z ≠ p.finish := by
    intro he
    have hh := congrArg Complex.re he
    linarith only [hh, hmean, hfirst, hlast]
  refine ⟨Or.inr ⟨0, by omega, midpoint_mem_segment _ _⟩, ?_⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using And.intro hs hf

end Polyline

section ArcSeeds

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A fixed interior test point retains the geometric edge identity. -/
@[expose] noncomputable def thinMapArcSeed (e : ℕ) : ℂ :=
  midpoint ℝ (((G).arc (e, false)).point 0) (((G).arc (e, false)).point 1)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Forward geometric arcs are monotone irrespective of directed presence. -/
theorem thinMapArc_xMonotone (e : ℕ) : ((G).arc (e, false)).XMonotone := by
  let F : ∀ n, ∃ Q : StageDrawing w n, Nonempty (MonotoneStageInvariant w n Q) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  change ((monotoneLimitDrawing w hfin F).arc (e, false)).XMonotone
  rw [monotoneLimitDrawing_arc_layout w hfin F e e
    (kmsw_edge_allocated_by_self w e) false]
  exact layoutArc_points_pairwise w e e (kmsw_edge_allocated_by_self w e)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The test point is interior to its geometric arc, including for missing edges. -/
theorem thinMapArcSeed_mem_interior (e : ℕ) :
    thinMapArcSeed w hfin e ∈ ((G).arc (e, false)).interior :=
  Polyline.seed_midpoint_mem_interior _ (thinMapArc_xMonotone w hfin e)
    ((G).arc_length (e, false))

variable (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Off-seam arc containment is equivalent to membership of one fixed interior point.
Boundary edges are handled directly; directed presence is not required. -/
theorem thinMapArc_subset_sideRegion_iff_seed (a : ThinMapSide) (e : ℕ)
    (hne : ∀ i, e ≠ P.edge i) :
    ((G).arc (e, false)).image ⊆ thinMapSideRegion w hfin hL htrans hRneg P a ↔
      thinMapArcSeed w hfin e ∈ thinMapSideRegion w hfin hL htrans hRneg P a := by
  constructor
  · intro h
    exact h (thinMapArcSeed_mem_interior w hfin e).1
  · intro hseed
    have hb : pathTrace G (thinMapBoundaryDart w hfin hL htrans hRneg a) ⊆
        thinMapSideRegion w hfin hL htrans hRneg P a := by
      cases a with
      | left => exact leftBoundaryTrace_subset_sideRegion w hfin hL htrans hRneg P
      | right => exact rightBoundaryTrace_subset_sideRegion w hfin hL htrans hRneg P
    have hd : thinMapBoundaryDart w hfin hL htrans hRneg a =
        (fun i => ((thinMapBoundaryDart w hfin hL htrans hRneg a i).1, false)) := by
      funext i
      cases a <;> rfl
    by_cases hboundary : ∃ i, e = (thinMapBoundaryDart w hfin hL htrans hRneg a i).1
    · obtain ⟨i, rfl⟩ := hboundary
      intro z hz
      apply hb
      rw [hd]
      exact Set.mem_iUnion.mpr ⟨i, hz⟩
    · apply Polyline.seed_image_subset_of_frontier_avoidance
        (thinMapArc_xMonotone w hfin e) ((G).arc_length (e, false))
        (thinMapSideRegion_isClosed w hfin hL htrans hRneg P a)
      · exact ⟨thinMapArcSeed w hfin e, thinMapArcSeed_mem_interior w hfin e, hseed⟩
      · apply Set.disjoint_left.mpr
        intro z hz hf
        rcases thinMapSideRegion_frontier_subset_traces w hfin hL htrans hRneg P a hf
          with hs | ht
        · exact Set.disjoint_left.mp
            (thinMapArc_interior_disjoint_trace w hfin e P.edge hne) hz hs
        · rw [hd] at ht
          exact Set.disjoint_left.mp (thinMapArc_interior_disjoint_trace w hfin e
            (fun i => (thinMapBoundaryDart w hfin hL htrans hRneg a i).1)
            (fun i hi => hboundary ⟨i, hi⟩)) hz ht

end ArcSeeds

section HalfSeeds

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining geometric obligation is membership of one explicit interior point,
only for half edges off the finite seam and off the selected exterior boundary.
This proposition is isolated and is not asserted to hold. -/
@[expose] noncomputable def AncestorPosHalfOffPrefixArcSeedIdentification
    (a : ThinMapSide) : Prop :=
  ∀ d : Fin (ancestorPosHalfRep R hR a).dartCount,
    (∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val) →
    (∀ i : ℕ, (ancestorPosDartId w t R hR I a d).1 ≠
      (thinMapBoundaryDart w hfin hL htrans hRneg a i).1) →
    thinMapArcSeed w hfin (ancestorPosDartId w t R hR I a d).1 ∈
      thinMapSideRegion w hfin hL htrans hRneg P a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
For a represented prefix, full arc confinement is equivalent to the single-point
obligation away from the exterior boundary. Boundary edges need no seed hypothesis.
This equivalence does not discharge the single-point obligation. -/
theorem ancestorPos_offPrefixArcConfinement_iff_arcSeeds
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) (a : ThinMapSide) :
    AncestorPosHalfOffPrefixArcConfinement w hfin hL htrans hRneg P t R hR I a ↔
      AncestorPosHalfOffPrefixArcSeedIdentification
        w hfin hL htrans hRneg P t R hR I a := by
  constructor
  · intro h d hoff _
    exact h d hoff (thinMapArcSeed_mem_interior w hfin _).1
  · intro h d hoff
    by_cases hb : ∃ i, (ancestorPosDartId w t R hR I a d).1 =
        (thinMapBoundaryDart w hfin hL htrans hRneg a i).1
    · obtain ⟨i, hi⟩ := hb
      rw [hi]
      exact (thinMapBoundaryDart_mem_sourceAncestorEdges w hfin hL htrans hRneg P a i).1
    · apply (thinMapArc_subset_sideRegion_iff_seed w hfin hL htrans hRneg P a _
        (ancestorPos_offPrefix_ne_seamEdge w t R hR I a P hp d hoff)).mpr
      exact h d hoff (fun i hi => hb ⟨i, hi⟩)

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both complete half-range comparisons reduce to the single-point obligations;
seam indices, reversed darts, missing edges and reverse inclusions are accounted for. -/
theorem ancestorPos_sideRanges_iff_arcSeeds
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) :
    (∀ a, AncestorPosHalfSideRangeIdentification w hfin hL htrans hRneg P t R hR I a) ↔
      (∀ a, AncestorPosHalfOffPrefixArcSeedIdentification
        w hfin hL htrans hRneg P t R hR I a) := by
  rw [ancestorPos_sideRanges_iff_offPrefixArcConfinement
    w hfin hL htrans hRneg P t R hR I hp]
  constructor
  · intro h a
    exact (ancestorPos_offPrefixArcConfinement_iff_arcSeeds
      w hfin hL htrans hRneg P t R hR I hp a).mp (h a)
  · intro h a
    exact (ancestorPos_offPrefixArcConfinement_iff_arcSeeds
      w hfin hL htrans hRneg P t R hR I hp a).mpr (h a)

end HalfSeeds

section SourceWitnesses

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
The existing good-cut witnesses simultaneously carry all exterior boundary data
and the indexed selected-path prefix. No geometric identification is assumed. -/
theorem sourceAncestorPosHalf_boundary_prefix_embedding (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
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
        (fun d => d.1.val) = List.ofFn (fun j : Fin m => (P).edge j.val)) := by
  intro t
  obtain ⟨ℓ, m, R, hR, I, _, _, hb, ht, hc⟩ :=
    selectedCutPastCuts_representatives_boundary_stageIso x T hT q k s hk
  let F := fun z => (stageMapVertex w t (cutMapIsoVertexEquiv I z)).id
  have htarget : (boundaryTarget R.B a s).map F =
      some (thinMapBoundaryVertex w hfin hL htrans hRneg a s) := by
    rw [ancestor_boundaryVertex_eq]
    have hp := selectedCut_past_boundary_target_record x T hT q a k s hk
    cases s <;> exact (ht a _).trans hp
  have hhalf := congrArg (Option.map F) (ancestorPos_boundaryTarget_map R hR a s)
  rw [Option.map_map, htarget] at hhalf
  obtain ⟨v, hv, hvid⟩ := Option.map_eq_some_iff.mp hhalf
  refine ⟨ℓ, _, _, m, R, hR, I, v, ?_, hv, ?_, hvid, ?_, ?_⟩
  · cases a with
    | left => exact congrArg Prod.fst hc
    | right => exact congrArg Prod.snd hc
  · change F (ancestorPosVertexMap R hR a (ancestorPosHalfRep R hR a).B.source) = 0
    rw [ancestorPos_source_map]
    exact Option.some.inj (ht a 0)
  · intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q a k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb a)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (ancestorPos_boundaryDarts_map R hR a)
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    rw [ancestor_boundaryDart_eq]
    exact hm.trans hs

  · exact sourceAncestorPosHalf_path_prefix x T hT q s k hk R hR I hb hc

end SourceWitnesses

section SourceReduction

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The local single-point obligation specialized to represented selected prefixes. -/
@[expose] noncomputable def SourceAncestorCutPositiveArcSeeds : Prop :=
  ∀ (q : selectedCutCoherentDomain x T hT) (k : ℕ),
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    let hfin := sourceAncestor_finite_incidence x T hT q
    let hL := sourceAncestor_left_nonneg x T hT q
    let htrans := sourceAncestor_left_transient x T hT q
    let hRneg := sourceAncestor_right_unbounded x T hT q
    let P := sourceAncestorPath x T hT q
    ∀ {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t)),
      (((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
        (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) →
      ∀ a, AncestorPosHalfOffPrefixArcSeedIdentification
        w hfin hL htrans hRneg P t R hR I a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining single-point identification gives the full source side-range
obligation using the already proved good-cut witnesses. Conditional reduction only. -/
theorem sourceAncestorCutPositiveSideRangeIdentification_of_arcSeeds
    (h : SourceAncestorCutPositiveArcSeeds x T hT) :
    SourceAncestorCutPositiveSideRangeIdentification x T hT := by
  intro a s k q _ hk
  obtain ⟨ℓ, r, n, m, R, hR, I, v, hrep, hv, hroot, htarget, hb, hp⟩ :=
    sourceAncestorPosHalf_boundary_prefix_embedding x T hT q a s k hk
  refine ⟨ℓ, r, n, m, R, hR, I, v, hrep, hv, hroot, htarget, hb, hp, ?_⟩
  exact (ancestorPos_sideRanges_iff_arcSeeds _ _ _ _ _ _ _ R hR I hp).mpr
    (h q k R hR I hp) a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
All remaining realization assembly is conditional on the displayed single-point
geometric obligation. No unconditional source realization is asserted. -/
theorem sourceAncestorCutRealization_of_arcSeeds
    (h : SourceAncestorCutPositiveArcSeeds x T hT) :
    SourceAncestorCutRealization x T hT :=
  sourceAncestorCutRealization_of_sideRange x T hT
    (sourceAncestorCutPositiveSideRangeIdentification_of_arcSeeds x T hT h)

end SourceReduction
end DirectedDistances.PaperProofs.Section4
