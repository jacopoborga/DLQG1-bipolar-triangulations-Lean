module

public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.PlanarMap.PLDrawingEscape
public import DirectedDistances.KMSW.LimitRotationVertex
public import DirectedDistances.KMSW.InfiniteRotation
import DirectedDistances.PlanarMap.MonotonePolyline

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

noncomputable section

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

include hfin in
private theorem vertex_allocated (v : ℕ) : ∃ n, v < (kmswStage w n).nextVertex := by
  classical
  by_contra h
  have hb (n : ℕ) : (kmswStage w n).nextVertex ≤ v := by
    by_contra hn
    exact h ⟨n, by omega⟩
  have hf := (Set.finite_Iio v).biUnion (fun u _ => hfin u)
  have hu : (Set.univ : Set ℕ).Finite := hf.subset (by
    intro e _
    have he := kmsw_edge_allocated_by_self w e
    have hw := (kmswStage_endpoints_lt_nextVertex w e e he).1
    exact Set.mem_iUnion₂.mpr
      ⟨(kmswStage w e).west e, hw.trans_le (hb e), e, he, Or.inl rfl⟩)
  exact Set.infinite_univ hu

private theorem pos_stable {n m v : ℕ} (hnm : n ≤ m)
    (hv : v < (kmswStage w n).nextVertex) : layoutPos w m v = layoutPos w n v := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [layoutPos_old_vertex w m v (hv.trans_le (CutConverse.nextVertex_mono w hnm)), ih]

private theorem arc_stable {n m e : ℕ} (hnm : n ≤ m)
    (he : e < (kmswStage w n).nextEdge) : layoutArc w m e = layoutArc w n e := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [layoutArc_old w m e (he.trans_le (kmswStage_nextEdge_mono w hnm)), ih]

private def unionPos (v : ℕ) : ℂ :=
  layoutPos w (Nat.find (vertex_allocated w hfin v)) v

private def unionArc (d : ℕ × Bool) : Polyline :=
  if d.2 then (layoutArc w d.1 d.1).reverse else layoutArc w d.1 d.1

private theorem unionPos_eq (n v : ℕ) (hv : v < (kmswStage w n).nextVertex) :
    unionPos w hfin v = layoutPos w n v := by
  unfold unionPos
  let k := Nat.find (vertex_allocated w hfin v)
  have hk : v < (kmswStage w k).nextVertex := Nat.find_spec (vertex_allocated w hfin v)
  exact (pos_stable w (le_max_left k n) hk).symm.trans
    (pos_stable w (le_max_right k n) hv)

private theorem unionArc_eq (n e : ℕ) (he : e < (kmswStage w n).nextEdge) (b : Bool) :
    unionArc w (e, b) = if b then (layoutArc w n e).reverse else layoutArc w n e := by
  have ha : layoutArc w e e = layoutArc w n e :=
    (arc_stable w (le_max_left e n) (kmsw_edge_allocated_by_self w e)).symm.trans
      (arc_stable w (le_max_right e n) he)
  simp only [unionArc, ha]

private theorem endpoint_eq (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    kmswLimitDartVertex w (d.1.val, d.2) = (stageVertex w n d).val := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp [kmswLimitDartVertex, stageVertex, stageEndpoint, hb, hw, he]

variable (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P))

private def family (n : ℕ) : StageDrawing w n := (hfam n).choose

private def invariant (n : ℕ) : MonotoneStageInvariant w n (family w hfam n) :=
  Classical.choice (hfam n).choose_spec

private theorem pos_family (n : ℕ) (v : Fin (kmswStage w n).nextVertex) :
    unionPos w hfin v.val = (family w hfam n).pos v :=
  (unionPos_eq w hfin n v.val v.isLt).trans ((invariant w hfam n).pos_layout v).symm

private theorem arc_family (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    unionArc w (d.1.val, d.2) = (family w hfam n).arc d :=
  (unionArc_eq w n d.1.val d.1.isLt d.2).trans
    ((invariant w hfam n).arc_layout d).symm

private theorem pos_injective : Function.Injective (unionPos w hfin) := by
  intro u v huv
  obtain ⟨m, hm⟩ := vertex_allocated w hfin u
  obtain ⟨n, hn⟩ := vertex_allocated w hfin v
  have hu := hm.trans_le (CutConverse.nextVertex_mono w (le_max_left m n))
  have hv := hn.trans_le (CutConverse.nextVertex_mono w (le_max_right m n))
  rw [unionPos_eq w hfin (max m n) u hu, unionPos_eq w hfin (max m n) v hv] at huv
  exact layoutPos_injective w (max m n) u v hu hv huv

private theorem dartVal_injective (n : ℕ) :
    Function.Injective (fun d : StageDart (kmswStage w n).nextEdge => (d.1.val, d.2)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  obtain ⟨he, hb⟩ := Prod.mk.inj h
  cases Fin.ext he
  cases hb
  rfl

include hfam in
private theorem arc_simple (d : ℕ × Bool) : (unionArc w d).IsSimple := by
  rw [arc_family w hfam d.1 (⟨d.1, kmsw_edge_allocated_by_self w d.1⟩, d.2)]
  exact (family w hfam d.1).arc_simple _

include hfam in
private theorem arc_length (d : ℕ × Bool) : 2 ≤ (unionArc w d).points.length := by
  rw [arc_family w hfam d.1 (⟨d.1, kmsw_edge_allocated_by_self w d.1⟩, d.2)]
  exact (family w hfam d.1).arc_length _

include hfam in
private theorem arc_start (d : ℕ × Bool) :
    (unionArc w d).start = unionPos w hfin (kmswLimitDartVertex w d) := by
  let x : StageDart (kmswStage w d.1).nextEdge :=
    (⟨d.1, kmsw_edge_allocated_by_self w d.1⟩, d.2)
  rw [arc_family w hfam d.1 x, (family w hfam d.1).arc_start,
    endpoint_eq w d.1 x, pos_family w hfin hfam]

include hfam in
private theorem arc_finish (d : ℕ × Bool) :
    (unionArc w d).finish = unionPos w hfin (kmswLimitDartVertex w (d.1, !d.2)) := by
  let x : StageDart (kmswStage w d.1).nextEdge :=
    (⟨d.1, kmsw_edge_allocated_by_self w d.1⟩, d.2)
  rw [arc_family w hfam d.1 x]
  have hv := endpoint_eq w d.1 (edgeFlip _ x)
  change kmswLimitDartVertex w (d.1, !d.2) =
    (stageVertex w d.1 (edgeFlip _ x)).val at hv
  exact ((family w hfam d.1).arc_finish x).trans
    ((pos_family w hfin hfam d.1 (stageVertex w d.1 (edgeFlip _ x))).symm.trans
      (congrArg (unionPos w hfin) hv.symm))

private theorem arc_flip (d : ℕ × Bool) :
    unionArc w (d.1, !d.2) = (unionArc w d).reverse := by
  cases hb : d.2 <;> simp [unionArc, hb]

include hfam in
private theorem initial_nonzero (d : ℕ × Bool) :
    (unionArc w d).initialDirection ≠ 0 := by
  rw [arc_family w hfam d.1 (⟨d.1, kmsw_edge_allocated_by_self w d.1⟩, d.2)]
  exact (family w hfam d.1).initial_nonzero _

include hfam in
private theorem interior_disjoint (d e : ℕ × Bool) (hne : e ≠ d)
    (hflip : e ≠ (d.1, !d.2)) :
    Disjoint (unionArc w d).interior (unionArc w e).interior := by
  let n := max d.1 e.1
  let x : StageDart (kmswStage w n).nextEdge :=
    (⟨d.1, kmsw_nextEdge_unbounded w d.1 n (le_max_left _ _)⟩, d.2)
  let y : StageDart (kmswStage w n).nextEdge :=
    (⟨e.1, kmsw_nextEdge_unbounded w e.1 n (le_max_right _ _)⟩, e.2)
  rw [arc_family w hfam n x, arc_family w hfam n y]
  apply (family w hfam n).interior_disjoint x y
  · intro h
    exact hne (congrArg (fun z => (z.1.val, z.2)) h)
  · intro h
    exact hflip (congrArg (fun z => (z.1.val, z.2)) h)

include hfam in
private theorem interior_avoids_vertices (d : ℕ × Bool) (v : ℕ) :
    unionPos w hfin v ∉ (unionArc w d).interior := by
  obtain ⟨m, hm⟩ := vertex_allocated w hfin v
  let n := max d.1 m
  let x : StageDart (kmswStage w n).nextEdge :=
    (⟨d.1, kmsw_nextEdge_unbounded w d.1 n (le_max_left _ _)⟩, d.2)
  let u : Fin (kmswStage w n).nextVertex :=
    ⟨v, hm.trans_le (CutConverse.nextVertex_mono w (le_max_right _ _))⟩
  rw [arc_family w hfam n x, pos_family w hfin hfam n u]
  exact (family w hfam n).interior_avoids_vertices x u

include hfam in
private theorem initial_arg_injective (d e : ℕ × Bool)
    (hv : kmswLimitDartVertex w d = kmswLimitDartVertex w e)
    (ha : Complex.arg (unionArc w d).initialDirection =
      Complex.arg (unionArc w e).initialDirection) : d = e := by
  let n := max d.1 e.1
  let x : StageDart (kmswStage w n).nextEdge :=
    (⟨d.1, kmsw_nextEdge_unbounded w d.1 n (le_max_left _ _)⟩, d.2)
  let y : StageDart (kmswStage w n).nextEdge :=
    (⟨e.1, kmsw_nextEdge_unbounded w e.1 n (le_max_right _ _)⟩, e.2)
  have hv' : stageVertex w n x = stageVertex w n y := by
    apply Fin.ext
    rw [← endpoint_eq w n x, ← endpoint_eq w n y]
    exact hv
  rw [arc_family w hfam n x, arc_family w hfam n y] at ha
  exact congrArg (fun z => (z.1.val, z.2))
    ((family w hfam n).initial_arg_injective x y hv' ha)

include hfin in
private theorem complete_exists (u : ℕ) : ∃ n, kmswVertexComplete w n u := by
  obtain ⟨B, hB⟩ := (hfin u).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hmem : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hmem).trans_lt (kmsw_edge_allocated_by_self w B)

private theorem star_allocated {n u : ℕ} (hc : kmswVertexComplete w n u)
    (d : ℕ × Bool) (hd : kmswLimitDartVertex w d = u) :
    d.1 < (kmswStage w n).nextEdge := by
  apply hc d.1
  cases hb : d.2
  · exact Or.inl (by simpa [kmswLimitDartVertex, hb] using hd)
  · exact Or.inr (by simpa [kmswLimitDartVertex, hb] using hd)

include hfam in
private theorem rotation_agreement (d : ℕ × Bool) :
    CcwSuccessor {e | kmswLimitDartVertex w e = kmswLimitDartVertex w d}
      (fun e => (unionArc w e).initialDirection) d (kmswInfRot w hfin d) := by
  obtain ⟨n, hc⟩ := complete_exists w hfin (kmswLimitDartVertex w d)
  let x : StageDart (kmswStage w n).nextEdge :=
    (⟨d.1, star_allocated w hc d rfl⟩, d.2)
  have hx : (stageVertex w n x).val = kmswLimitDartVertex w d :=
    (endpoint_eq w n x).symm
  have hr := kmswInfRot_eq_stage w hfin n x (by
    change kmswVertexComplete w n (stageVertex w n x).val
    rw [hx]
    exact hc)
  have hs := (family w hfam n).rotation_agreement x
  refine ⟨kmswLimitDart_star_finite w hfin _, rfl,
    kmswLimitDartVertex_rot w hfin d, ?_⟩
  rcases hs.2.2.2 with ⟨hrx, hsingle⟩ | ⟨hrx, hnext⟩
  · left
    refine ⟨?_, ?_⟩
    · exact hr.trans (congrArg (fun z => (z.1.val, z.2)) hrx)
    · ext e
      constructor
      · intro he
        let y : StageDart (kmswStage w n).nextEdge :=
          (⟨e.1, star_allocated w hc e he⟩, e.2)
        have hy : y ∈ {y | stageVertex w n y = stageVertex w n x} := by
          apply Fin.ext
          rw [← endpoint_eq w n y, hx]
          exact he
        rw [hsingle] at hy
        exact congrArg (fun z => (z.1.val, z.2)) (Set.mem_singleton_iff.mp hy)
      · intro he
        have he' : e = d := he
        rw [he']
        rfl
  · right
    refine ⟨?_, ?_⟩
    · intro he
      apply hrx
      apply dartVal_injective w n
      exact hr.symm.trans he
    · intro e he hne
      let y : StageDart (kmswStage w n).nextEdge :=
        (⟨e.1, star_allocated w hc e he⟩, e.2)
      have hy : stageVertex w n y = stageVertex w n x := by
        apply Fin.ext
        rw [← endpoint_eq w n y, hx]
        exact he
      have hne' : y ≠ x := by
        intro h
        exact hne (congrArg (fun z => (z.1.val, z.2)) h)
      have h := hnext y hy hne'
      change ccwTurn (unionArc w (x.1.val, x.2)).initialDirection
          (unionArc w (kmswInfRot w hfin (x.1.val, x.2))).initialDirection ≤
        ccwTurn (unionArc w (x.1.val, x.2)).initialDirection
          (unionArc w (y.1.val, y.2)).initialDirection
      rw [hr, arc_family w hfam n x, arc_family w hfam n (stageRot w n x),
        arc_family w hfam n y]
      exact h

private theorem point_mem_image (p : Polyline) (i : ℕ) (hi : i < p.points.length) :
    p.point i ∈ p.image := by
  by_cases hzero : i = 0
  · subst i
    rw [p.point_zero_eq_start]
    exact Or.inl rfl
  · refine Or.inr ⟨i - 1, by omega, ?_⟩
    have heq : i - 1 + 1 = i := by omega
    rw [Polyline.segmentAt, heq]
    exact right_mem_segment ℝ _ _

private theorem points_mem_image (p : Polyline) (z : ℂ) (hz : z ∈ p.points) :
    z ∈ p.image := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  have hp : p.point i = p.points[i] := by
    change p.points.getD i p.start = p.points[i]
    exact List.getD_eq_getElem p.points p.start hi
  rw [← hp]
  exact point_mem_image p i hi

private theorem image_height_lower (p : Polyline) (C : ℝ)
    (hp : ∀ z ∈ p.points, C ≤ z.im) : ∀ z ∈ p.image, C ≤ z.im := by
  intro z hz
  rcases hz with hz | ⟨i, hi, hz⟩
  · have hz' : z = p.start := hz
    rw [hz']
    exact hp _ (List.head_mem p.nonempty)
  · have hpoint (j : ℕ) (hj : j < p.points.length) : C ≤ (p.point j).im := by
      have heq : p.point j = p.points[j] := by
        change p.points.getD j p.start = p.points[j]
        exact List.getD_eq_getElem p.points p.start hj
      rw [heq]
      exact hp _ (List.getElem_mem hj)
    have ha := hpoint i (by omega)
    have hb := hpoint (i + 1) hi
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    have hsa := mul_le_mul_of_nonneg_left ha hs
    have htb := mul_le_mul_of_nonneg_left hb ht
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    calc
      C = s * C + t * C := by rw [← add_mul, hst, one_mul]
      _ ≤ s * (p.point i).im + t * (p.point (i + 1)).im := add_le_add hsa htb

private theorem unionArc_height_lower (d : ℕ × Bool) (z : ℂ)
    (hz : z ∈ (unionArc w d).image) :
    min (unionPos w hfin (kmswLimitDartVertex w d)).im
      (unionPos w hfin (kmswLimitDartVertex w (d.1, !d.2))).im ≤ z.im := by
  let n := d.1
  have he := kmsw_edge_allocated_by_self w d.1
  obtain ⟨hw, hh⟩ := edge_endpoints_eq w he
  obtain ⟨hvw, hve⟩ := kmswStage_endpoints_lt_nextVertex w n d.1 he
  have hwp : unionPos w hfin (edgeWest w d.1) =
      layoutPos w n ((kmswStage w n).west d.1) := by
    rw [← hw]
    exact unionPos_eq w hfin n _ hvw
  have hep : unionPos w hfin (edgeEast w d.1) =
      layoutPos w n ((kmswStage w n).east d.1) := by
    rw [← hh]
    exact unionPos_eq w hfin n _ hve
  have H := layoutArc_height_lower w n d.1 he
  cases hb : d.2
  · have hz' : z ∈ (layoutArc w n d.1).image := by
      simpa [unionArc, hb, n] using hz
    simpa [kmswLimitDartVertex, hb, hwp, hep] using H z hz'
  · have hp : ∀ q ∈ (layoutArc w n d.1).reverse.points,
        min (layoutPos w n ((kmswStage w n).west d.1)).im
          (layoutPos w n ((kmswStage w n).east d.1)).im ≤ q.im := by
      intro q hq
      exact H q (points_mem_image _ q (List.mem_reverse.mp hq))
    have hz' : z ∈ (layoutArc w n d.1).reverse.image := by
      simpa [unionArc, hb, n] using hz
    simpa [kmswLimitDartVertex, hb, hwp, hep, min_comm] using
      image_height_lower _ _ hp z hz'

private theorem nextVertex_step_bound (n : ℕ) :
    (kmswStage w (n + 1)).nextVertex ≤ (kmswStage w n).nextVertex + 1 := by
  rw [kmswStage, kmswStep]
  cases kmswCodeStep (w n) with
  | down =>
    cases hs : (kmswStage w n).UR <;> simp [kmswStepOfStep, hs, State.addEdge]
  | left =>
    cases hs : (kmswStage w n).UL.dropLast.reverse <;>
      simp [kmswStepOfStep, hs, State.addEdge]
  | up => simp [kmswStepOfStep, State.addEdge]

private theorem height_controls_allocation (v n : ℕ)
    (hv : (unionPos w hfin v).im ≤ n) : v < (kmswStage w n).nextVertex := by
  let k := Nat.find (vertex_allocated w hfin v)
  have hk : v < (kmswStage w k).nextVertex := Nat.find_spec (vertex_allocated w hfin v)
  suffices hkn : k ≤ n from hk.trans_le (CutConverse.nextVertex_mono w hkn)
  cases hkval : k with
  | zero => exact Nat.zero_le n
  | succ m =>
    have hold : ¬v < (kmswStage w m).nextVertex := by
      exact Nat.find_min (vertex_allocated w hfin v) (by omega)
    have hb := nextVertex_step_bound w m
    have hvbirth : v = (kmswStage w m).nextVertex := by rw [hkval] at hk; omega
    have hgrow : (kmswStage w (m + 1)).nextVertex =
        (kmswStage w m).nextVertex + 1 := by rw [hkval] at hk; omega
    have hheight : (unionPos w hfin v).im = (m + 1 : ℕ) := by
      rw [unionPos_eq w hfin k v hk, hkval, hvbirth]
      exact layoutHeight_created_vertex w m hgrow
    rw [hheight] at hv
    have hmn : m + 1 ≤ n := by exact_mod_cast hv
    omega

private theorem finite_height_sublevel (R : ℝ) :
    {v | (unionPos w hfin v).im ≤ R}.Finite := by
  obtain ⟨n, hn⟩ := exists_nat_ge R
  apply (Set.finite_Iio (kmswStage w n).nextVertex).subset
  intro v hv
  exact height_controls_allocation w hfin v n (hv.trans hn)

include hfin in
private theorem locally_finite :
    ∀ K : Set ℂ, Bornology.IsBounded K →
      {d | (K ∩ (unionArc w d).image).Nonempty}.Finite := by
  apply locally_finite_of_heightHalfPlane (fun d => (d.1, !d.2))
    (kmswLimitDartVertex w) (unionPos w hfin) (unionArc w)
  · exact unionArc_height_lower w hfin
  · exact finite_height_sublevel w hfin
  · intro v
    have hf := (kmswLimitDart_star_finite w hfin v).image
      (fun d : ℕ × Bool => (d.1, !d.2))
    apply ((kmswLimitDart_star_finite w hfin v).union hf).subset
    intro d hd
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨(d.1, !d.2), hd, by simp⟩




@[expose] noncomputable def monotoneLimitDrawing (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P)) :
    PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w) where
  flip_involutive := by rintro ⟨e, b⟩; cases b <;> rfl
  flip_ne := by rintro ⟨e, b⟩; cases b <;> simp
  vert_rotation := kmswLimitDartVertex_rot w hfin
  pos := fun v => layoutPos w (Nat.find (show ∃ n, v < (kmswStage w n).nextVertex from by
    exact vertex_allocated w hfin v)) v
  pos_injective := by exact pos_injective w hfin
  arc := fun d => if d.2 then (layoutArc w d.1 d.1).reverse else layoutArc w d.1 d.1
  arc_simple := by exact arc_simple w hfam
  arc_length := by exact arc_length w hfam
  arc_start := by exact arc_start w hfin hfam
  arc_finish := by exact arc_finish w hfin hfam
  arc_flip := by exact arc_flip w
  interior_disjoint := by exact interior_disjoint w hfam
  interior_avoids_vertices := by exact interior_avoids_vertices w hfin hfam
  locally_finite := by exact locally_finite w hfin
  initial_nonzero := by exact initial_nonzero w hfam
  initial_arg_injective := by exact initial_arg_injective w hfam
  rotation_agreement := by exact rotation_agreement w hfin hfam




theorem monotoneLimitDrawing_pos_layout (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    (monotoneLimitDrawing w hfin hfam).pos v = layoutPos w n v :=
  unionPos_eq w hfin n v hv




theorem monotoneLimitDrawing_arc_layout (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) (b : Bool) :
    (monotoneLimitDrawing w hfin hfam).arc (e, b) =
      if b then (layoutArc w n e).reverse else layoutArc w n e :=
  unionArc_eq w n e he b




theorem monotoneLimitDrawing_agrees (Q : ∀ n, StageDrawing w n)
    (hpos : ∀ n (v : Fin (kmswStage w n).nextVertex), (Q n).pos v = layoutPos w n v.val)
    (harc : ∀ n (d : StageDart (kmswStage w n).nextEdge),
      (Q n).arc d = if d.2 then (layoutArc w n d.1.val).reverse else layoutArc w n d.1.val) :
    (∀ n v, (monotoneLimitDrawing w hfin hfam).pos v.val = (Q n).pos v) ∧
      (∀ n d, (monotoneLimitDrawing w hfin hfam).arc (d.1.val, d.2) = (Q n).arc d) := by
  constructor
  · intro n v
    exact (monotoneLimitDrawing_pos_layout w hfin hfam n v.val v.isLt).trans
      (hpos n v).symm
  · intro n d
    exact (monotoneLimitDrawing_arc_layout w hfin hfam n d.1.val d.1.isLt d.2).trans
      (harc n d).symm

end
end DirectedDistances.KMSW
