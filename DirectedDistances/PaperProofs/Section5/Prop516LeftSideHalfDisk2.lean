/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516LeftSideHalfDisk
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact12

/-! # Return paths away from a local disk toward Proposition 5.16

The original winding witness is retained while constructing a simple polygonal
middle path outside a common closed disk. Boundary connectors and transfer of
and integration belong to the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

open DirectedDistances.PlanarMap Set Metric unitInterval

/-- Helper toward Proposition 5.16: a return path with open traversal in a
complementary face meets the entire drawing exactly at its two endpoints.
Consequently endpoint-only intersection is automatic for any replacement
whose open traversal stays in that same face. -/
theorem returnPath_inter_drawing
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (a b : I) (q : Path ((P.arc d).toPath b) ((P.arc d).toPath a))
    (hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val) :
    Set.range q ∩ P.image = {(P.arc d).toPath b, (P.arc d).toPath a} := by
  have harc (t : I) : (P.arc d).toPath t ∈ P.image :=
    Or.inr ⟨d, (Polyline.range_toPath (P.arc d)) ▸ Set.mem_range_self t⟩
  apply Set.Subset.antisymm
  · rintro w ⟨⟨t, rfl⟩, hw⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl q.source
    by_cases ht1 : t = 1
    · subst t
      exact Or.inr q.target
    exact (P.face_subset_compl F
      (hqF t ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
        unitInterval.lt_one_iff_ne_one.mpr ht1⟩) hw).elim
  · rintro w (hw | hw)
    · subst w
      exact ⟨⟨0, q.source⟩, harc b⟩
    · subst w
      exact ⟨⟨1, q.target⟩, harc a⟩

/-- Helper toward Proposition 5.16: a winding-left return witness admits a
closed disk about the tested edge point avoiding its entire image. Every two
distinct interior points of that same return path can be joined by a simple
polyline in the face outside the disk. The original winding accumulation is
retained for the original loop, with no winding assertion for the new path. -/
theorem exists_leftAtOn_return_simple_polyline_away
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face) (s : {t : I // t ∈ openParams})
    (hleft : LeftAtOn F.val (P.arc d).toPath s) :
    ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b)
      (_hb : b < 1),
      ∃ q : Path ((P.arc d).toPath b) ((P.arc d).toPath a),
        Function.Injective q ∧
        (∀ t : I, t ∈ openParams → q t ∈ F.val) ∧
        (P.arc d).toPath s.1 ∈ closure
          {w : ℂ | w ∈ F.val ∧ HasWinding
            ((edgeSubarc (P.arc d).toPath a b
              (le_of_lt (lt_trans _has _hsb))).trans q) w 1} ∧
        ∃ r : ℝ, 0 < r ∧
          Disjoint (closedBall ((P.arc d).toPath s.1) r) (Set.range q) ∧
          ∀ t₁ t₂ : I, t₁ ∈ openParams → t₂ ∈ openParams → t₁ ≠ t₂ →
            ∃ c : Polyline, c.IsSimple ∧ c.start = q t₁ ∧ c.finish = q t₂ ∧
              c.image ⊆ F.val ∩ (closedBall ((P.arc d).toPath s.1) r)ᶜ := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩ := hleft
  obtain ⟨R, hR, havoid⟩ := P.exists_ball_disjoint_returnPath32 d F a b s has hsb q hqF
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : Disjoint (closedBall ((P.arc d).toPath s.1) r) (Set.range q) :=
    havoid.mono_left (closedBall_subset_ball (half_lt_self hR))
  let U : Set ℂ := F.val ∩ (closedBall ((P.arc d).toPath s.1) r)ᶜ
  have hUopen : IsOpen U :=
    (P.face_isOpen_of_locallyFiniteVertexImage32 hfinite F).inter
      isClosed_closedBall.isOpen_compl
  have hqU : q '' openParams ⊆ U := by
    rintro w ⟨t, ht, rfl⟩
    exact ⟨hqF t ht, fun hw => Set.disjoint_left.mp hclosed hw (Set.mem_range_self t)⟩
  have hparams : IsPreconnected (openParams : Set I) := by
    have heq : (openParams : Set I) = Set.Ioo 0 1 := by
      ext t
      rfl
    rw [heq]
    exact isPreconnected_Ioo
  have hconn : IsPreconnected (q '' openParams) :=
    hparams.image q q.continuous.continuousOn
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl, r, hr, hclosed, ?_⟩
  intro t₁ t₂ ht₁ ht₂ htne
  have h₁ : q t₁ ∈ q '' openParams := ⟨t₁, ht₁, rfl⟩
  have h₂ : q t₂ ∈ q '' openParams := ⟨t₂, ht₂, rfl⟩
  have hsub := hconn.subset_connectedComponentIn h₁ hqU
  obtain ⟨c, hcsimple, hcs, hcf, hcim⟩ :=
    exists_simple_polyline_in_open_connected hUopen.connectedComponentIn
      (isConnected_connectedComponentIn_iff.mpr (hqU h₁))
      (hsub h₁) (hsub h₂) (fun heq => htne (hqi heq))
  exact ⟨c, hcsimple, hcs, hcf,
    hcim.trans (connectedComponentIn_subset U (q t₁))⟩

/-- Helper toward Proposition 5.16: the simple polygonal winding bound also
applies to the actual concatenation of the two path traversals, including
endpoint casts. Avoidance follows from the winding witness itself. -/
theorem simple_polylines_trans_hasWinding_bounds
    (p q : Polyline) (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hjoin : p.finish = q.start) (hclose : q.finish = p.start)
    (hne : p.start ≠ p.finish)
    (hinter : p.image ∩ q.image = {p.start, p.finish})
    (w : ℂ) (n : ℤ)
    (hw : HasWinding (p.toPath.trans (q.toPath.cast hjoin hclose.symm)) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  have havoid : w ∉ p.image ∪ q.image := by
    have h := hw.not_mem_range
    rw [Path.trans_range] at h
    change w ∉ Set.range p.toPath ∪ Set.range q.toPath at h
    simpa only [Polyline.range_toPath] using h
  have hparts := (hasLiftIncrement_trans_iff p.toPath
    (q.toPath.cast hjoin hclose.symm)).mp hw
  have hcat : HasLiftIncrement (p.boundaryConcat q).toPath w
      (2 * Real.pi * Complex.I * n) := by
    have h := (hasLiftIncrement_boundaryConcat_iff (ContinuousMap.id ℂ)
      p q hlenp hlenq hjoin w (2 * Real.pi * Complex.I * n)).mpr hparts
    exact (hasLiftIncrement_congr_fun _ _ (fun _ => rfl)).mp h
  have hlenqr : 2 ≤ q.reverse.points.length := by
    simpa only [Polyline.reverse, List.length_reverse] using hlenq
  have hs : p.start = q.reverse.start := by
    rw [Polyline.start_reverse]
    exact hclose.symm
  have hf : p.finish = q.reverse.finish := by
    rw [Polyline.finish_reverse]
    exact hjoin
  have hclosed := Polyline.closedConcat_closed p q.reverse hlenqr hs
  have hc : Polyline.closedConcat p q.reverse = p.boundaryConcat q := by
    simp only [Polyline.closedConcat, Polyline.reverse_reverse]
    rfl
  have hloop : HasWinding
      ((Polyline.closedConcat p q.reverse).toPath.cast rfl hclosed) w n := by
    change HasLiftIncrement (Polyline.closedConcat p q.reverse).toPath w
      (2 * Real.pi * Complex.I * n)
    rw [hc]
    exact hcat
  exact Polyline.closedConcat_hasWinding_bounds32 p q.reverse hp
    (Polyline.isSimple_reverse_transfer q hq) hlenp hlenqr hs hf hne
    (by simpa only [Polyline.image_reverse_transfer] using hinter) w n
    (by simpa only [Polyline.image_reverse_transfer] using havoid) hloop

/-- Helper toward Proposition 5.16: closing a nondegenerate straight segment
by a simple polygonal return meeting it only at its endpoints gives winding
between minus one and one for the concatenated path. -/
theorem segment_polygonal_return_hasWinding_bounds
    {a b : ℂ} (hab : a ≠ b) (q : Polyline) (hq : q.IsSimple)
    (hstart : q.start = b) (hfinish : q.finish = a)
    (hinter : segment ℝ a b ∩ q.image = {a, b})
    (w : ℂ) (n : ℤ)
    (hw : HasWinding ((Path.segment a b).trans
      (q.toPath.cast hstart.symm hfinish.symm)) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  let p : Polyline := ⟨[a, b], by simp⟩
  have hp : p.IsSimple := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
      subst i
      simpa [p, Polyline.point, Polyline.start] using hab
    · intro i hi
      change i + 2 < 2 at hi
      omega
    · intro i j hi hj hij
      change i + 1 < 2 at hi
      change j + 1 < 2 at hj
      omega
  have himage : p.image = segment ℝ a b := by
    rw [← Polyline.range_toPath p]
    change Set.range (Path.segment a b) = segment ℝ a b
    exact Path.range_segment a b
  have hlenq : 2 ≤ q.points.length :=
    Polyline.length_two_of_start_ne_finish q (by
      rw [hstart, hfinish]
      exact hab.symm)
  exact simple_polylines_trans_hasWinding_bounds p q hp hq (by simp [p]) hlenq
    hstart.symm hfinish hab (by
      rw [himage]
      exact hinter) w n hw

/-- Helper toward Proposition 5.16: for a segment and an endpoint-only
simple polygonal return, winding on a small left half-disk is zero or one,
and on the right half-disk it is minus one or zero. In particular the
right-side winding-one obstruction is impossible for this polygonal loop. -/
theorem exists_segment_polygonal_return_halfDiscs_winding_bounds
    {a b x : ℂ} (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b)
    (q : Polyline) (hq : q.IsSimple)
    (hstart : q.start = b) (hfinish : q.finish = a)
    (hinter : segment ℝ a b ∩ q.image = {a, b}) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ Polyline.leftHalfDisc x (b - a) r, ∀ n : ℤ,
        HasWinding ((Path.segment a b).trans
          (q.toPath.cast hstart.symm hfinish.symm)) u n → 0 ≤ n ∧ n ≤ 1) ∧
      (∀ v ∈ Polyline.rightHalfDisc x (b - a) r, ∀ n : ℤ,
        HasWinding ((Path.segment a b).trans
          (q.toPath.cast hstart.symm hfinish.symm)) v n → -1 ≤ n ∧ n ≤ 0) := by
  have hxa : x ≠ a := fun h => hab (left_mem_openSegment_iff.mp (h ▸ hx))
  have hxb : x ≠ b := fun h => hab (right_mem_openSegment_iff.mp (h ▸ hx))
  have hxq : x ∉ q.image := by
    intro hxq
    have hmem : x ∈ ({a, b} : Set ℂ) :=
      hinter ▸ ⟨openSegment_subset_segment ℝ a b hx, hxq⟩
    rcases hmem with h | h
    · exact hxa h
    · exact hxb h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    q.isCompact_image.isClosed.isOpen_compl x hxq
  let Q := q.toPath.cast hstart.symm hfinish.symm
  have hdisj : Disjoint (ball x r) (Set.range Q) := by
    change Disjoint (ball x r) (Set.range q.toPath)
    rw [Polyline.range_toPath]
    exact Set.disjoint_left.mpr (fun _ hw => hball hw)
  obtain ⟨k, hleft, hright⟩ :=
    exists_segment_return_halfDisk_winding32 hab hx hr Q hdisj
  have hdir : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨u, hu⟩ := Polyline.leftHalfDisc_nonempty x (b - a) r hdir hr
  obtain ⟨v, hv⟩ := Polyline.rightHalfDisc_nonempty x (b - a) r hdir hr
  have hku := segment_polygonal_return_hasWinding_bounds hab q hq hstart hfinish
    hinter u (k + 1) (hleft u hu.1 hu.2)
  have hkv := segment_polygonal_return_hasWinding_bounds hab q hq hstart hfinish
    hinter v k (hright v hv.1 hv.2)
  refine ⟨r, hr, ?_, ?_⟩
  · intro w hw n hn
    have heq := hasWinding_unique hn (hleft w hw.1 hw.2)
    omega
  · intro w hw n hn
    have heq := hasWinding_unique hn (hright w hw.1 hw.2)
    omega
















































































































end DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

end
