module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfDartFace









public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver
open scoped Classical

section FiniteCarrier

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
  (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual half embedding has exactly the finite closed-half carrier. -/
theorem ancestorPosDartMap_range :
    Set.range (ancestorPosDartMap R hR a) =
      match a with
      | .left => pathCutLeftHalfDarts R.B (selectedGeodesicOfLen R.B x hR)
      | .right => pathCutRightHalfDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  cases a with
  | left => exact cutLRepDartMap_range R hR
  | right => exact cutRRepDartMap_range R hR

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Permanent-ID range membership transports back to the concrete uncut dart. -/
theorem ancestorPos_stage_range_iff (d : Fin R.dartCount) :
    stageLimitDart w t (I.toEquiv d) ∈ Set.range (ancestorPosDartId w t R hR I a) ↔
      d ∈ Set.range (ancestorPosDartMap R hR a) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, I.toEquiv.injective ((stageLimitDart w t).injective he)⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both orientations of a geometric edge have identical half-range membership. -/
theorem ancestorPos_range_opposite_iff (e : ℕ × Bool) :
    (e.1, !e.2) ∈ Set.range (ancestorPosDartId w t R hR I a) ↔
      e ∈ Set.range (ancestorPosDartId w t R hR I a) := by
  have flip (d : ℕ × Bool)
      (hd : d ∈ Set.range (ancestorPosDartId w t R hR I a)) :
      (d.1, !d.2) ∈ Set.range (ancestorPosDartId w t R hR I a) := by
    obtain ⟨c, rfl⟩ := hd
    exact ⟨(ancestorPosHalfRep R hR a).B.map.edgeInv c,
      ancestorPos_ids_opposite w t R hR I a c⟩
  constructor
  · intro he
    have hh := flip (e.1, !e.2) he
    simpa only [Bool.not_not, Prod.mk.eta] using hh
  · exact flip e

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every finite seam dart belongs to either concrete half, with both orientations. -/
theorem ancestorPos_seam_mem_range (d : Fin R.dartCount)
    (hd : d ∈ pathCutSeamDarts R.B (selectedGeodesicOfLen R.B x hR)) :
    stageLimitDart w t (I.toEquiv d) ∈ Set.range (ancestorPosDartId w t R hR I a) := by
  apply (ancestorPos_stage_range_iff w t R hR I a d).mpr
  rw [ancestorPosDartMap_range]
  cases a <;> exact Or.inr hd

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every edge of a represented infinite-path prefix lies in the finite half range.
This includes the opposite dart and preserves the edge ID. -/
theorem ancestorPos_prefix_mem_range (P : InfinitePresentPath w ⟨0⟩)
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (i : Fin m) (b : Bool) :
    (P.edge i.val, b) ∈ Set.range (ancestorPosDartId w t R hR I a) := by
  have hi : P.edge i.val ∈ List.ofFn (fun j : Fin m => P.edge j.val) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [← hp] at hi
  obtain ⟨d, hd, hid⟩ := List.mem_map.mp hi
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  have hr := ancestorPos_seam_mem_range w t R hR I a c (Or.inl hc)
  have hf := directedPath_stageIso_darts_forward I
    (selectedGeodesicOfLen R.B x hR) c hc
  have heq : stageLimitDart w t (I.toEquiv c) = (P.edge i.val, false) :=
    Prod.ext hid hf
  rw [heq] at hr
  cases b with
  | false => exact hr
  | true => exact (ancestorPos_range_opposite_iff w t R hR I a
      (P.edge i.val, false)).mpr hr

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The two concrete half ranges cover every allocated stage dart. -/
theorem ancestorPos_ranges_cover (e : StageDart (kmswStage w t).nextEdge) :
    stageLimitDart w t e ∈ Set.range (ancestorPosDartId w t R hR I .left) ∨
      stageLimitDart w t e ∈ Set.range (ancestorPosDartId w t R hR I .right) := by
  let d := I.toEquiv.symm e
  have he : I.toEquiv d = e := I.toEquiv.apply_symm_apply e
  rcases pathCut_halves_cover R.B (selectedGeodesicOfLen R.B x hR) d with hl | hr
  · left
    rw [← he, ancestorPos_stage_range_iff, ancestorPosDartMap_range]
    exact hl
  · right
    rw [← he, ancestorPos_stage_range_iff, ancestorPosDartMap_range]
    exact hr

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
No later edge of the infinite seam is already allocated in the represented stage. -/
theorem ancestorPos_seam_index_lt_of_allocated (P : InfinitePresentPath w ⟨0⟩)
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (i : ℕ) (hi : P.edge i < (kmswStage w t).nextEdge) : i < m := by
  let e : StageDart (kmswStage w t).nextEdge := (⟨P.edge i, hi⟩, false)
  have hsink := ancestorPos_sink_id_of_prefix w t P R hR I hp
  have hbound (a : ThinMapSide)
      (he : stageLimitDart w t e ∈ Set.range (ancestorPosDartId w t R hR I a)) :
      i < m := by
    obtain ⟨d, hd⟩ := he
    have hb := (ancestorPos_seam_iff_of_prefix w t P R hR I hp hsink a i d).mpr hd.symm
    have hlen := congrArg List.length (ancestorPos_seamDarts_map R hR a)
    rw [List.length_map, (selectedGeodesicOfLen R.B x hR).darts_length] at hlen
    have hlt := (List.getElem?_eq_some_iff.mp hb).1
    omega
  exact (ancestorPos_ranges_cover w t R hR I e).elim (hbound .left) (hbound .right)

end FiniteCarrier

section GeometricComparison

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The two closed geometric sides intersect exactly along the seam trace. -/
theorem thinMapSideRegions_inter_eq_seamTrace :
    thinMapSideRegion w hfin hL htrans hRneg P .left ∩
        thinMapSideRegion w hfin hL htrans hRneg P .right =
      pathTrace (monotoneFamilyDrawing w hfin (monotone_family_all w))
        (fun i => (P.edge i, false)) := by
  ext z
  constructor
  · rintro ⟨hl, hr⟩
    obtain ⟨p, hp, hre, hlo⟩ := hl.1
    have hhi := hr.2 p hp hre
    have heq : p = z := Complex.ext hre (le_antisymm hlo hhi)
    exact heq ▸ hp
  · intro hz
    exact ⟨seamTrace_subset_sideRegion w hfin hL htrans hRneg P .left hz,
      seamTrace_subset_sideRegion w hfin hL htrans hRneg P .right hz⟩

private theorem sideRange_interior_nonempty (p : Polyline) (hm : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : p.interior.Nonempty := by
  let z := midpoint ℝ (p.point 0) (p.point 1)
  have hfirst := p.point_re_lt hm (show 0 < 1 by omega) (show 1 < _ by omega)
  have hlast := p.point_re_le_of_le hm (show 1 ≤ p.points.length - 1 by omega)
    (show p.points.length - 1 < p.points.length by omega)
  rw [p.point_last_eq_finish] at hlast
  have hmean : z.re + z.re = (p.point 0).re + (p.point 1).re := by
    exact congrArg Complex.re (midpoint_add_self ℝ (p.point 0) (p.point 1))
  have hs : z ≠ p.start := by
    intro he
    have hh := congrArg Complex.re he
    rw [← p.point_zero_eq_start] at hh
    linarith only [hh, hmean, hfirst]
  have hf : z ≠ p.finish := by
    intro he
    have hh := congrArg Complex.re he
    linarith only [hh, hmean, hfirst, hlast]
  refine ⟨z, ⟨Or.inr ⟨0, by omega, midpoint_mem_segment _ _⟩, ?_⟩⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using And.intro hs hf

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An edge lying in both geometric sides is a seam edge, including geometric edges
without a directed orientation. Edge identity, rather than adjacency, is retained. -/
theorem thinMapSideEdges_inter_eq_seamEdges :
    sideEdges w hfin hL htrans hRneg P .left ∩
        sideEdges w hfin hL htrans hRneg P .right = Set.range P.edge := by
  let G := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let F : ∀ n, ∃ Q : StageDrawing w n, Nonempty (MonotoneStageInvariant w n Q) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  ext e
  constructor
  · rintro ⟨hl, hr⟩
    have hm : (G.arc (e, false)).XMonotone := by
      change ((monotoneLimitDrawing w hfin F).arc (e, false)).XMonotone
      rw [monotoneLimitDrawing_arc_layout w hfin F e e
        (kmsw_edge_allocated_by_self w e) false]
      exact layoutArc_points_pairwise w e e (kmsw_edge_allocated_by_self w e)
    obtain ⟨z, hz, hzends⟩ := sideRange_interior_nonempty
      (G.arc (e, false)) hm (G.arc_length (e, false))
    have ht : z ∈ pathTrace G (fun i => (P.edge i, false)) := by
      rw [← thinMapSideRegions_inter_eq_seamTrace w hfin hL htrans hRneg P]
      exact ⟨hl hz, hr hz⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    by_cases he : P.edge i = e
    · exact ⟨i, he⟩
    · have hqs : z ≠ (G.arc (P.edge i, false)).start := by
        intro hh
        rw [G.arc_start] at hh
        exact G.interior_avoids_vertices (e, false) (edgeWest w (P.edge i))
          (hh ▸ ⟨hz, hzends⟩)
      have hqf : z ≠ (G.arc (P.edge i, false)).finish := by
        intro hh
        rw [G.arc_finish] at hh
        exact G.interior_avoids_vertices (e, false) (edgeEast w (P.edge i))
          (hh ▸ ⟨hz, hzends⟩)
      have hqi : z ∈ (G.arc (P.edge i, false)).interior := ⟨hi, by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          using And.intro hqs hqf⟩
      have hd := G.interior_disjoint (e, false) (P.edge i, false)
        (fun hh => he (congrArg Prod.fst hh)) (by simp)
      exact False.elim (Set.disjoint_left.mp hd ⟨hz, hzends⟩ hqi)
  · rintro ⟨i, rfl⟩
    exact ⟨seamEdge_mem_sideEdges w hfin hL htrans hRneg P .left i,
      seamEdge_mem_sideEdges w hfin hL htrans hRneg P .right i⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining local comparison is restricted to one dart per edge off the finite
prefix seam. This proposition is isolated and is not asserted to hold. -/
@[expose] noncomputable def AncestorPosHalfOffPrefixSideRangeIdentification : Prop :=
  ∀ e : Fin (kmswStage w t).nextEdge,
    (∀ i : Fin m, e.val ≠ P.edge i.val) →
    ((e.val, false) ∈ Set.range (ancestorPosDartId w t R hR I a) ↔
      e.val ∈ sideEdges w hfin hL htrans hRneg P a)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
For a represented prefix, the seam and reverse-dart cases need no geometric input.
The complete comparison is equivalent to the displayed off-prefix obligation.
This equivalence does not discharge that obligation. -/
theorem ancestorPos_sideRange_iff_offPrefix
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) :
    AncestorPosHalfSideRangeIdentification w hfin hL htrans hRneg P t R hR I a ↔
      AncestorPosHalfOffPrefixSideRangeIdentification
        w hfin hL htrans hRneg P t R hR I a := by
  constructor
  · intro h e _
    exact h (e, false)
  · intro h e
    have he : ((e.1.val, false) ∈ Set.range (ancestorPosDartId w t R hR I a) ↔
        e.1.val ∈ sideEdges w hfin hL htrans hRneg P a) := by
      by_cases hs : ∃ i : Fin m, e.1.val = P.edge i.val
      · obtain ⟨i, hi⟩ := hs
        rw [hi]
        exact iff_of_true (ancestorPos_prefix_mem_range w t R hR I a P hp i false)
          (seamEdge_mem_sideEdges w hfin hL htrans hRneg P a i.val)
      · exact h e.1 (fun i hi => hs ⟨i, hi⟩)
    rcases e with ⟨e, b⟩
    cases b with
    | false => exact he
    | true =>
      exact (ancestorPos_range_opposite_iff w t R hR I a (e.val, false)).trans he

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining forward geometric obligation: an off-prefix edge in the concrete
half has its arc in the selected closed side. No ancestry, face, exhaustion or
reverse-inclusion claim is part of this proposition. It is not asserted to hold. -/
@[expose] noncomputable def AncestorPosHalfOffPrefixArcConfinement : Prop :=
  ∀ d : Fin (ancestorPosHalfRep R hR a).dartCount,
    (∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val) →
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      ((ancestorPosDartId w t R hR I a d).1, false)).image ⊆
        thinMapSideRegion w hfin hL htrans hRneg P a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
For both represented halves together, only forward arc confinement remains.
The reverse direction follows from finite-half coverage and the fact that the
two geometric sides share only seam edges. The confinement is not proved here. -/
theorem ancestorPos_sideRanges_iff_offPrefixArcConfinement
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) :
    (∀ a, AncestorPosHalfSideRangeIdentification
      w hfin hL htrans hRneg P t R hR I a) ↔
    (∀ a, AncestorPosHalfOffPrefixArcConfinement
      w hfin hL htrans hRneg P t R hR I a) := by
  constructor
  · intro h a d _
    exact (h a (I.toEquiv (ancestorPosDartMap R hR a d))).mp ⟨d, rfl⟩
  · intro h
    have hforward (a : ThinMapSide) (e : StageDart (kmswStage w t).nextEdge)
        (he : stageLimitDart w t e ∈ Set.range (ancestorPosDartId w t R hR I a)) :
        e.1.val ∈ sideEdges w hfin hL htrans hRneg P a := by
      obtain ⟨d, hd⟩ := he
      have hid : (ancestorPosDartId w t R hR I a d).1 = e.1.val :=
        congrArg Prod.fst hd
      by_cases hs : ∃ i : Fin m, e.1.val = P.edge i.val
      · obtain ⟨i, hi⟩ := hs
        rw [hi]
        exact seamEdge_mem_sideEdges w hfin hL htrans hRneg P a i.val
      · rw [← hid]
        exact h a d (fun i hi => hs ⟨i, hid.symm.trans hi⟩)
    have hseam (a : ThinMapSide) (e : StageDart (kmswStage w t).nextEdge)
        (he : e.1.val ∈ Set.range P.edge) :
        stageLimitDart w t e ∈ Set.range (ancestorPosDartId w t R hR I a) := by
      obtain ⟨i, hi⟩ := he
      have hiBound := ancestorPos_seam_index_lt_of_allocated w t R hR I P hp i
        (show P.edge i < (kmswStage w t).nextEdge by rw [hi]; exact e.1.isLt)
      have hh := ancestorPos_prefix_mem_range w t R hR I a P hp ⟨i, hiBound⟩ e.2
      change (e.1.val, e.2) ∈ _
      simpa only [hi] using hh
    intro a e
    constructor
    · exact hforward a e
    · intro he
      rcases ancestorPos_ranges_cover w t R hR I e with hl | hr
      · cases a with
        | left => exact hl
        | right =>
          apply hseam .right e
          rw [← thinMapSideEdges_inter_eq_seamEdges w hfin hL htrans hRneg P]
          exact ⟨hforward .left e hl, he⟩
      · cases a with
        | left =>
          apply hseam .left e
          rw [← thinMapSideEdges_inter_eq_seamEdges w hfin hL htrans hRneg P]
          exact ⟨he, hforward .right e hr⟩
        | right => exact hr

end GeometricComparison
end DirectedDistances.PaperProofs.Section4
