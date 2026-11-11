module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfLaunchSeed
public import DirectedDistances.PaperProofs.Section4.ThinIndRenewalProvider
public import DirectedDistances.PlanarMap.PlanarPathCutLeftmostRegion
import DirectedDistances.PlanarMap.SlopeAngularOrder

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The finite outgoing sectors are proved for both actual halves, including the source.
The geometric seed criterion is exactly strict initial angular order. Transfer of the
source realization and renewal fidelity are therefore not asserted. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver Set
open DirectedDistances.Paper.Section4
open scoped Classical Topology

section FiniteSector

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r m : ℕ}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every nonseam outgoing dart lies in the left half exactly when it precedes the seam
in canonical outgoing order. Index zero uses the source sector separately. -/
theorem thinMapCut_left_sector_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (Q : SimpleDirectedDartPath B.map B.source B.sink m)
    (i : Fin m) (d : D)
    (hv : dartTailVertex B.map d =
      Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
    (ht : B.map.tail d) (hoff : d ∉ pathCutSeamDarts B Q) :
    d ∈ pathCutLeftHalfDarts B Q ↔
      (canonicalOutgoingOrder B
        (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end Q i.val i.isLt)).idxOf d <
      (canonicalOutgoingOrder B
        (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end Q i.val i.isLt)).idxOf
          (Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩) := by
  have hne : d ≠ Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩ := by
    intro he
    exact hoff (Or.inl (he ▸ List.get_mem Q.darts _))
  have hsector : d ∈ pathCutLeftDarts B Q \ pathCutSeamDarts B Q ↔
      (canonicalOutgoingOrder B
        (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end Q i.val i.isLt)).idxOf d <
      (canonicalOutgoingOrder B
        (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end Q i.val i.isLt)).idxOf
          (Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩) := by
    by_cases hi : i.val = 0
    · have hv0 : dartTailVertex B.map d = B.source := by
        simpa only [hi, Q.start_vertex] using hv
      simpa only [hi, Q.start_vertex] using
        pathCutLeft_offSeam_iff_precedes_pathDart_of_source B Q d hv0 ht
          (by simpa only [hi] using hne)
    · have hi0 : 0 < i.val := Nat.pos_of_ne_zero hi
      by_cases hleft : Q.vertices.get
          ⟨i.val, by rw [Q.vertices_length]; omega⟩ ∈ B.leftPath.vertices
      · exact pathCutLeft_offSeam_iff_precedes_pathDart_of_leftBoundary
          B Q i.val hi0 i.isLt hleft d hv ht hne
      · by_cases hright : Q.vertices.get
            ⟨i.val, by rw [Q.vertices_length]; omega⟩ ∈ B.rightPath.vertices
        · exact pathCutLeft_offSeam_iff_precedes_pathDart_of_rightBoundary
            B Q i.val hi0 i.isLt hright d hv ht hne
        · exact pathCutLeft_offSeam_iff_precedes_pathDart_of_interiorVertex
            B Q i.val hi0 i.isLt hleft hright d hv ht hne
  simpa only [pathCutLeftHalfDarts, Set.mem_union, Set.mem_sdiff, hoff,
    or_false, and_true, not_false_eq_true] using hsector

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right sector is the strict opposite outgoing order, with the seam excluded. -/
theorem thinMapCut_right_sector_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (Q : SimpleDirectedDartPath B.map B.source B.sink m)
    (i : Fin m) (d : D)
    (hv : dartTailVertex B.map d =
      Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
    (ht : B.map.tail d) (hoff : d ∉ pathCutSeamDarts B Q) :
    d ∈ pathCutRightHalfDarts B Q ↔
      (canonicalOutgoingOrder B
        (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end Q i.val i.isLt)).idxOf
          (Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩) <
      (canonicalOutgoingOrder B
        (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end Q i.val i.isLt)).idxOf d := by
  let O := canonicalOutgoingOrder B
    (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
    (simplePath_vertex_ne_end Q i.val i.isLt)
  let p := Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩
  have hd : d ∈ O := (mem_canonicalOutgoingOrder_iff B _ _ d).mpr ⟨hv, ht⟩
  have hne : O.idxOf d ≠ O.idxOf p := by
    intro hh
    have he : d = p := (List.idxOf_inj hd).mp hh
    exact hoff (Or.inl (he ▸ List.get_mem Q.darts _))
  have hleft := thinMapCut_left_sector_iff B Q i d hv ht hoff
  have hcomplement : d ∈ pathCutRightHalfDarts B Q ↔
      d ∉ pathCutLeftHalfDarts B Q := by
    constructor
    · intro hr hl
      exact hoff ((pathCut_halves_inter_eq_seam B Q) ▸ And.intro hl hr)
    · intro hl
      exact (pathCut_halves_cover B Q d).resolve_left hl
  rw [hcomplement, hleft]
  change (¬ O.idxOf d < O.idxOf p) ↔ O.idxOf p < O.idxOf d
  omega

end FiniteSector

section HalfSector

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (P : InfinitePresentPath w ⟨0⟩) (t : ℕ) (R : KMSWMapRep ℓ r n)
  (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
    (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))

include hp

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The prefix equation identifies each forward seam dart individually. -/
theorem ancestorPos_prefixDart_id (i : Fin m) :
    (I.toEquiv ((selectedGeodesicOfLen R.B x hR).darts.get
      ⟨i.val, by rw [(selectedGeodesicOfLen R.B x hR).darts_length]; exact i.isLt⟩)).1.val =
        P.edge i.val := by
  let Q := selectedGeodesicOfLen R.B x hR
  let j : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩
  have hd : Q.darts[i.val]? = some (Q.darts.get j) := List.getElem?_eq_getElem j.isLt
  have hh := congrArg (fun ds => ds[i.val]?) hp
  rw [List.getElem?_map, List.getElem?_map, hd, Option.map_some, Option.map_some,
    List.getElem?_ofFn, dite_eq_left i.isLt] at hh
  exact Option.some.inj hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent ID of every finite seam vertex agrees with the infinite prefix. -/
theorem ancestorPos_prefixVertex_id (i : Fin m) :
    (stageMapVertex w t (cutMapIsoVertexEquiv I
      ((selectedGeodesicOfLen R.B x hR).vertices.get
        ⟨i.val, by rw [(selectedGeodesicOfLen R.B x hR).vertices_length]; omega⟩))).id =
      (P.initial i.val).1.id := by
  let Q := selectedGeodesicOfLen R.B x hR
  let j : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩
  have he := (Q.edge_step j).2.2.1
  rw [he, (cutMapIsoVertexEquiv_endpoints I (Q.darts.get j)).1, stageMapVertex_tail]
  have hf := directedPath_stageIso_darts_forward I Q (Q.darts.get j)
    (List.get_mem Q.darts j)
  change (if (I.toEquiv (Q.darts.get j)).2 then _ else _) = _
  simp only [hf, Bool.false_eq_true, ite_false]
  rw [(edge_endpoints_eq w (I.toEquiv (Q.darts.get j)).1.isLt).1,
    ancestorPos_prefixDart_id w P t R hR I hp i]
  exact (P.edge_outgoing_at_initial w i.val).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Off-prefix half darts avoid both orientations of every finite seam edge. -/
theorem ancestorPos_offPrefix_not_mem_finiteSeam
    (a : ThinMapSide) (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (hoff : ∀ i : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge i.val) :
    ancestorPosDartMap R hR a d ∉
      pathCutSeamDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  let Q := selectedGeodesicOfLen R.B x hR
  intro hd
  rcases hd with hd | hd
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
    let i : Fin m := ⟨j.val, by
      have hjlt := j.isLt
      have hlen := (selectedGeodesicOfLen R.B x hR).darts_length
      omega⟩
    have hid := ancestorPos_prefixDart_id w P t R hR I hp i
    change (I.toEquiv (Q.darts.get j)).1.val = P.edge i.val at hid
    rw [hj] at hid
    exact hoff i hid
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
    let i : Fin m := ⟨j.val, by
      have hjlt := j.isLt
      have hlen := (selectedGeodesicOfLen R.B x hR).darts_length
      omega⟩
    have hid := ancestorPos_prefixDart_id w P t R hR I hp i
    change (I.toEquiv (Q.darts.get j)).1.val = P.edge i.val at hid
    rw [hj, I.edgeInv_comm] at hid
    exact hoff i hid

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A permanent seam launch identifies the exact finite path vertex, including index zero. -/
theorem ancestorPos_seamLaunch_tailVertex
    (a : ThinMapSide) (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (ht : (ancestorPosHalfRep R hR a).B.map.tail d) (i : Fin m)
    (hi : edgeWest w (ancestorPosDartId w t R hR I a d).1 =
      (P.initial i.val).1.id) :
    dartTailVertex R.B.map (ancestorPosDartMap R hR a d) =
      (selectedGeodesicOfLen R.B x hR).vertices.get
        ⟨i.val, by rw [(selectedGeodesicOfLen R.B x hR).vertices_length]; omega⟩ := by
  apply (cutMapIsoVertexEquiv I).injective
  apply stageMapVertex_injective w t
  suffices hh : (stageMapVertex w t (cutMapIsoVertexEquiv I
      (dartTailVertex R.B.map (ancestorPosDartMap R hR a d)))).id =
      (stageMapVertex w t (cutMapIsoVertexEquiv I
        ((selectedGeodesicOfLen R.B x hR).vertices.get
          ⟨i.val, by rw [(selectedGeodesicOfLen R.B x hR).vertices_length]; omega⟩))).id
      from congrArg StagePresentVertex.mk hh
  rw [(cutMapIsoVertexEquiv_endpoints I _).1, stageMapVertex_tail]
  have hf := ((ancestorPos_ids_oriented w t R hR I a d).mp ht).2
  change (I.toEquiv (ancestorPosDartMap R hR a d)).2 = false at hf
  change (if (I.toEquiv (ancestorPosDartMap R hR a d)).2 then _ else _) = _
  simp only [hf, Bool.false_eq_true, ite_false]
  rw [(edge_endpoints_eq w
    (I.toEquiv (ancestorPosDartMap R hR a d)).1.isLt).1]
  exact hi.trans (ancestorPos_prefixVertex_id w P t R hR I hp i).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every actual seam launch lies in its strict finite outgoing sector. Both the source
and positive indices are covered; the geometric drawing comparison remains separate. -/
theorem ancestorPos_seamLaunch_finite_sector
    (a : ThinMapSide) (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (ht : (ancestorPosHalfRep R hR a).B.map.tail d)
    (hoff : ∀ j : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge j.val)
    (i : Fin m) (hi : edgeWest w (ancestorPosDartId w t R hR I a d).1 =
      (P.initial i.val).1.id) :
    let Q := selectedGeodesicOfLen R.B x hR
    let O := canonicalOutgoingOrder R.B
      (Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩)
      (simplePath_vertex_ne_end Q i.val i.isLt)
    let p := Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩
    let e := ancestorPosDartMap R hR a d
    match a with
    | .left => O.idxOf e < O.idxOf p
    | .right => O.idxOf p < O.idxOf e := by
  have hv := ancestorPos_seamLaunch_tailVertex w P t R hR I hp a d ht i hi
  have hn := ancestorPos_offPrefix_not_mem_finiteSeam w P t R hR I hp a d hoff
  have htail : R.B.map.tail (ancestorPosDartMap R hR a d) := by
    cases a with
    | left => exact ((cutLRep_embedding_fields R hR).2.2.2.1 d).mp ht
    | right => exact ((cutRRep_embedding_fields R hR).2.2.2.1 d).mp ht
  have hmem : ancestorPosDartMap R hR a d ∈
      Set.range (ancestorPosDartMap R hR a) := ⟨d, rfl⟩
  rw [ancestorPosDartMap_range] at hmem
  cases a with
  | left => exact (thinMapCut_left_sector_iff R.B _ i _ hv htail hn).mp hmem
  | right => exact (thinMapCut_right_sector_iff R.B _ i _ hv htail hn).mp hmem

end HalfSector

section LaunchGeometry

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A point on the graph over the first segment belongs to the actual polyline. -/
private theorem seam_first_segment_mem (p : Polyline) (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) (x : ℝ)
    (hx : x ∈ Icc p.start.re (p.point 1).re) :
    (⟨x, p.heightFn x⟩ : ℂ) ∈ p.image := by
  have hr := p.point_re_lt hp (show 0 < 1 by omega) (show 1 < _ by omega)
  rw [p.point_zero_eq_start] at hr
  refine Or.inr ⟨0, by omega, ?_⟩
  rw [Polyline.segmentAt, p.point_zero_eq_start, mem_segment_iff_height hr]
  refine ⟨hx.1, hx.2, ?_⟩
  have hh := p.heightFn_linear_on_segment hp (i := 0) (by omega)
    (xval := x) (by simpa only [p.point_zero_eq_start] using hx.1) hx.2
  simpa only [Nat.zero_add, p.point_zero_eq_start, segmentHeight] using hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Strict outgoing angular order gives two ordered points at the same abscissa. -/
private theorem seam_initial_order_points (p q : Polyline)
    (hp : p.XMonotone) (hq : q.XMonotone)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hs : p.start = q.start)
    (ha : Complex.arg p.initialDirection < Complex.arg q.initialDirection) :
    ∃ z ∈ p.image, ∃ y ∈ q.image, z.re = y.re ∧ z.im < y.im := by
  have hpdir := p.initialDirection_re_pos hp hlenp
  have hqdir := q.initialDirection_re_pos hq hlenq
  have hsl := (east_arg_lt_iff_slope_lt hpdir hqdir).mp ha
  have hpr : p.start.re < (p.point 1).re := by
    exact sub_pos.mp hpdir
  have hqr : p.start.re < (q.point 1).re := by
    rw [hs]
    exact sub_pos.mp hqdir
  let b := min (p.point 1).re (q.point 1).re
  let x := (p.start.re + b) / 2
  have hpb : p.start.re < b := lt_min hpr hqr
  have hpx : p.start.re < x := by dsimp only [x]; linarith only [hpb]
  have hxb : x < b := by dsimp only [x]; linarith only [hpb]
  have hxp : x ≤ (p.point 1).re := hxb.le.trans (min_le_left _ _)
  have hxq : x ≤ (q.point 1).re := hxb.le.trans (min_le_right _ _)
  have hpheight := p.heightFn_linear_on_segment hp (i := 0) (by omega)
    (xval := x) (by simpa only [p.point_zero_eq_start] using hpx.le) hxp
  have hqheight := q.heightFn_linear_on_segment hq (i := 0) (by omega)
    (xval := x) (by simpa only [q.point_zero_eq_start, ← hs] using hpx.le) hxq
  have hpheight' : p.heightFn x = p.start.im +
      p.initialDirection.im / p.initialDirection.re * (x - p.start.re) := by
    simpa only [Nat.zero_add, p.point_zero_eq_start, Polyline.initialDirection,
      Complex.sub_re, Complex.sub_im] using hpheight
  have hqheight' : q.heightFn x = q.start.im +
      q.initialDirection.im / q.initialDirection.re * (x - q.start.re) := by
    simpa only [Nat.zero_add, q.point_zero_eq_start, Polyline.initialDirection,
      Complex.sub_re, Complex.sub_im] using hqheight
  refine ⟨⟨x, p.heightFn x⟩, seam_first_segment_mem p hp hlenp x ⟨hpx.le, hxp⟩,
    ⟨x, q.heightFn x⟩, seam_first_segment_mem q hq hlenq x
      ⟨by simpa only [← hs] using hpx.le, hxq⟩, rfl, ?_⟩
  change p.heightFn x < q.heightFn x
  rw [hpheight', hqheight', ← hs]
  exact add_lt_add_right (mul_lt_mul_of_pos_right hsl (sub_pos.mpr hpx)) _

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seamDrawingFamily (w : ℕ → Fin 3) :
    ∀ n, ∃ Q : StageDrawing w n, Nonempty (MonotoneStageInvariant w n Q) :=
  fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
    ((monotone_family_all w) n).choose_spec⟩

local notation "F" => seamDrawingFamily w

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The seam has at most one point above any fixed abscissa. -/
private theorem seam_trace_vertical_unique {z y : ℂ}
    (hz : z ∈ pathTrace G (fun i => (P.edge i, false)))
    (hy : y ∈ pathTrace G (fun i => (P.edge i, false))) (hxy : z.re = y.re) : z = y := by
  have he := infinitePresentPath_trace_eq_graph hfin F P
  have hzi := ((Set.ext_iff.mp he z).mp hz).2
  have hyi := ((Set.ext_iff.mp he y).mp hy).2
  exact Complex.ext hxy (hzi.trans ((congrArg _ hxy).trans hyi.symm))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Membership of an off-seam launch seed in either side forces the corresponding strict
angular order. This includes the source without any incoming-seam assumption. -/
theorem thinMapArcSeed_launch_arg_of_mem
    (e : ℕ) (i : ℕ) (hi : edgeWest w e = (P.initial i).1.id)
    (hoff : ∀ j, e ≠ P.edge j) (a : ThinMapSide)
    (hseed : thinMapArcSeed w hfin e ∈ thinMapSideRegion w hfin hL htrans hRneg P a) :
    let u := ((G).arc (e, false)).initialDirection
    let v := ((G).arc (P.edge i, false)).initialDirection
    match a with
    | .left => Complex.arg v < Complex.arg u
    | .right => Complex.arg u < Complex.arg v := by
  have hs : ((G).arc (e, false)).start = ((G).arc (P.edge i, false)).start := by
    rw [(G).arc_start, (G).arc_start]
    exact congrArg (G).pos (hi.trans (P.edge_outgoing_at_initial w i).2.symm)
  have hne : Complex.arg ((G).arc (e, false)).initialDirection ≠
      Complex.arg ((G).arc (P.edge i, false)).initialDirection := by
    intro h
    apply hoff i
    exact congrArg Prod.fst ((G).initial_arg_injective (e, false) (P.edge i, false)
      (hi.trans (P.edge_outgoing_at_initial w i).2.symm) h)
  have harc := (thinMapArc_subset_sideRegion_iff_seed
    w hfin hL htrans hRneg P a e hoff).mpr hseed
  cases a with
  | left =>
    apply lt_of_not_ge
    intro hn
    have ha := lt_of_le_of_ne hn hne
    obtain ⟨z, hz, y, hy, hre, him⟩ := seam_initial_order_points
      ((G).arc (e, false)) ((G).arc (P.edge i, false))
      (thinMapArc_xMonotone w hfin e) (thinMapArc_xMonotone w hfin (P.edge i))
      ((G).arc_length _) ((G).arc_length _) hs ha
    obtain ⟨q, hq, hqre, hqim⟩ := (harc hz).1
    have hqy : q = y := seam_trace_vertical_unique w hfin P hq
      (Set.mem_iUnion.mpr ⟨i, hy⟩) (hqre.trans hre)
    rw [hqy] at hqim
    exact (not_lt_of_ge hqim) him
  | right =>
    apply lt_of_not_ge
    intro hn
    have ha := lt_of_le_of_ne hn hne.symm
    obtain ⟨z, hz, y, hy, hre, him⟩ := seam_initial_order_points
      ((G).arc (P.edge i, false)) ((G).arc (e, false))
      (thinMapArc_xMonotone w hfin (P.edge i)) (thinMapArc_xMonotone w hfin e)
      ((G).arc_length _) ((G).arc_length _) hs.symm ha
    have hle := (harc hy).2 z (Set.mem_iUnion.mpr ⟨i, hz⟩) hre
    exact (not_lt_of_ge hle) him

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private noncomputable def seamPrepend {w : ℕ → Fin 3} {u v : PresentVertex w}
    (e : u ⟶ v) (Q : InfinitePresentPath w v) : InfinitePresentPath w u where
  edge
    | 0 => e.val
    | n + 1 => Q.edge n
  initial
    | 0 => ⟨u, .nil⟩
    | n + 1 => ⟨(Q.initial n).1, e.toPath.comp (Q.initial n).2⟩
  prefix_length n := by
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Path.length_comp, Path.length_toPath, Q.prefix_length, Nat.add_comm]
  prefix_edges n := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [pathEdgeList_comp, Q.prefix_edges, List.ofFn_succ]
      rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_extendPath {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) (S : InfinitePresentPath w v) :
    ∃ Q : InfinitePresentPath w u, Set.range S.edge ⊆ Set.range Q.edge := by
  induction p with
  | nil => exact ⟨S, Subset.rfl⟩
  | @cons v z p e ih =>
    obtain ⟨Q, hQ⟩ := ih (seamPrepend e S)
    refine ⟨Q, ?_⟩
    rintro f ⟨i, rfl⟩
    exact hQ ⟨i + 1, rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A forward edge launched at any seam vertex has its seed in one of the two sides. -/
theorem thinMapArcSeed_mem_side_union_of_seam_launch
    (e : ℕ) (he : EdgePresent w e) (i : ℕ)
    (hi : edgeWest w e = (P.initial i).1.id) :
    thinMapArcSeed w hfin e ∈ thinMapSideRegion w hfin hL htrans hRneg P .left ∪
      thinMapSideRegion w hfin hL htrans hRneg P .right := by
  let f : (P.initial i).1 ⟶ (⟨edgeEast w e⟩ : PresentVertex w) := ⟨e, he, hi, rfl⟩
  let S := seamPrepend f (kmswRightmostPath w hfin hL htrans hRneg (edgeEast w e))
  obtain ⟨Q, hQ⟩ := seam_extendPath (P.initial i).2 S
  obtain ⟨j, hj⟩ := hQ (show e ∈ Set.range S.edge from ⟨0, rfl⟩)
  apply thinMapPathTrace_subset_sideRegions w hfin hL htrans hRneg P Q
  exact Set.mem_iUnion.mpr ⟨j, hj ▸ (thinMapArcSeed_mem_interior w hfin e).1⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The exact geometric seam-launch criterion is strict initial angular order, at the
source as well as every positive seam index. No order comparison is assumed here. -/
theorem thinMapArcSeed_mem_side_iff_launch_arg
    (e : ℕ) (he : EdgePresent w e) (i : ℕ)
    (hi : edgeWest w e = (P.initial i).1.id) (hoff : ∀ j, e ≠ P.edge j)
    (a : ThinMapSide) :
    thinMapArcSeed w hfin e ∈ thinMapSideRegion w hfin hL htrans hRneg P a ↔
      let u := ((G).arc (e, false)).initialDirection
      let v := ((G).arc (P.edge i, false)).initialDirection
      match a with
      | .left => Complex.arg v < Complex.arg u
      | .right => Complex.arg u < Complex.arg v := by
  constructor
  · intro hs
    cases a <;> exact thinMapArcSeed_launch_arg_of_mem
      w hfin hL htrans hRneg P e i hi hoff _ hs
  · intro ha
    have hu := thinMapArcSeed_mem_side_union_of_seam_launch
      w hfin hL htrans hRneg P e he i hi
    cases a with
    | left =>
      rcases hu with hl | hr
      · exact hl
      · exact False.elim (lt_asymm ha (thinMapArcSeed_launch_arg_of_mem
          w hfin hL htrans hRneg P e i hi hoff .right hr))
    | right =>
      rcases hu with hl | hr
      · exact False.elim (lt_asymm ha (thinMapArcSeed_launch_arg_of_mem
          w hfin hL htrans hRneg P e i hi hoff .left hl))
      · exact hr

end LaunchGeometry

section RemainingOrder

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining order transfer at one fixed seam index. Finite outgoing order has been
Index zero is the source case; positive indices are the other seam vertices. -/
@[expose] noncomputable def AncestorPosHalfSeamLaunchArgumentOrderAt
    (a : ThinMapSide) (i : Fin m) : Prop :=
  ∀ d : Fin (ancestorPosHalfRep R hR a).dartCount,
    (ancestorPosHalfRep R hR a).B.map.tail d →
    (∀ j : Fin m, (ancestorPosDartId w t R hR I a d).1 ≠ P.edge j.val) →
    (∀ j : ℕ, (ancestorPosDartId w t R hR I a d).1 ≠
      (thinMapBoundaryDart w hfin hL htrans hRneg a j).1) →
    edgeWest w (ancestorPosDartId w t R hR I a d).1 = (P.initial i.val).1.id →
    let u := ((G).arc ((ancestorPosDartId w t R hR I a d).1, false)).initialDirection
    let v := ((G).arc (P.edge i.val, false)).initialDirection
    match a with
    | .left => Complex.arg v < Complex.arg u
    | .right => Complex.arg u < Complex.arg v

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Neither side of this equivalence is asserted to hold. -/
theorem ancestorPos_seamLaunch_iff_argumentOrder
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) :
    AncestorPosHalfSeamLaunchArcSeeds w hfin hL htrans hRneg P t R hR I a ↔
      ∀ i : Fin m,
        AncestorPosHalfSeamLaunchArgumentOrderAt w hfin hL htrans hRneg P t R hR I a i := by
  constructor
  · intro h i d ht hoff hb hi
    have hn := ancestorPos_offPrefix_ne_seamEdge w t R hR I a P hp d hoff
    have he := ((ancestorPos_ids_oriented w t R hR I a d).mp ht).1
    cases a <;> exact (thinMapArcSeed_mem_side_iff_launch_arg
      w hfin hL htrans hRneg P _ he i.val hi hn _).mp (h d ht hoff hb ⟨i, hi⟩)
  · intro h d ht hoff hb ⟨i, hi⟩
    have hn := ancestorPos_offPrefix_ne_seamEdge w t R hR I a P hp d hoff
    have he := ((ancestorPos_ids_oriented w t R hR I a d).mp ht).1
    cases a <;> exact (thinMapArcSeed_mem_side_iff_launch_arg
      w hfin hL htrans hRneg P _ he i.val hi hn _).mpr (h i d ht hoff hb hi)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining angular order separates into source launches and positive-index launches.
Both are isolated obligations, never hypotheses of an unconditional source theorem. -/
theorem ancestorPos_seamLaunch_iff_zero_and_positive_argumentOrder
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (a : ThinMapSide) :
    AncestorPosHalfSeamLaunchArcSeeds w hfin hL htrans hRneg P t R hR I a ↔
      (∀ i : Fin m, i.val = 0 →
        AncestorPosHalfSeamLaunchArgumentOrderAt w hfin hL htrans hRneg P t R hR I a i) ∧
      (∀ i : Fin m, 0 < i.val →
        AncestorPosHalfSeamLaunchArgumentOrderAt w hfin hL htrans hRneg P t R hR I a i) := by
  rw [ancestorPos_seamLaunch_iff_argumentOrder w hfin hL htrans hRneg P t R hR I hp a]
  constructor
  · intro h
    exact ⟨fun i _ => h i, fun i _ => h i⟩
  · rintro ⟨hzero, hpos⟩ i
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · exact hzero i hi
    · exact hpos i hi

end RemainingOrder

end DirectedDistances.PaperProofs.Section4
