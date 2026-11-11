/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPendantInsertion
public import DirectedDistances.PlanarMap.D39PLChordInsertion
public import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen2
public import DirectedDistances.PlanarMap.D39PLFaceExtension3

/-! # Polygonal access to vertex corners

to the sole coordinator. The open-set simple-arc theorem is an explicit
premise, not an axiom or an assertion of completion. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Metric Topology



@[expose] def SimpleArcInOpenStatement : Prop :=
  ∀ (U : Set ℂ), IsOpen U → IsConnected U →
    ∀ x y, x ∈ U → y ∈ U → x ≠ y →
      ∃ p : Polyline, p.IsSimple ∧ p.start = x ∧ p.finish = y ∧ p.image ⊆ U

namespace Polyline

/-- Helper toward Proposition 5.16: the straight access chain. -/
@[expose] def cornerSegment (x y : ℂ) : Polyline := ⟨[x, y], by simp⟩

/-- Helper toward Proposition 5.16: endpoints and direction of a straight
access chain. -/
theorem cornerSegment_data (x y : ℂ) :
    (cornerSegment x y).start = x ∧ (cornerSegment x y).finish = y ∧
      (cornerSegment x y).initialDirection = y - x := by
  simp [cornerSegment, start, finish, initialDirection, point]

/-- Helper toward Proposition 5.16: the straight access chain has exactly
the prescribed closed segment as image. -/
theorem image_cornerSegment (x y : ℂ) :
    (cornerSegment x y).image = segment ℝ x y := by
  ext z
  constructor
  · intro hz
    rcases hz with hz | ⟨i, hi, hz⟩
    · have hzx : z = x := hz
      subst z
      exact left_mem_segment ℝ x y
    · have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
      subst i
      simpa [cornerSegment, segmentAt, point, start] using hz
  · intro hz
    refine Or.inr ⟨0, by simp [cornerSegment], ?_⟩
    simpa [cornerSegment, segmentAt, point, start] using hz

/-- Helper toward Proposition 5.16: a polyline contains its terminal point. -/
theorem finish_mem_image_cornerAccess (p : Polyline) : p.finish ∈ p.image := by
  rw [← point_last_eq_finish]
  exact p.point_mem_image (by have := List.length_pos_iff.mpr p.nonempty; omega)

/-- Helper toward Proposition 5.16: a nondegenerate straight access chain
is simple. -/
theorem isSimple_cornerSegment {x y : ℂ} (hxy : x ≠ y) :
    (cornerSegment x y).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
    subst i
    simpa [cornerSegment, point, start] using hxy
  · intro i hi
    change i + 2 < 2 at hi
    omega
  · intro i j hi hj hij
    change i + 1 < 2 at hi
    change j + 1 < 2 at hj
    omega

/-- Helper toward Proposition 5.16: an interval of a simple polyline is
simple, with no change to its ordered source segments. -/
theorem isSimple_intervalPolyline (p : Polyline) (hp : p.IsSimple) (i n : ℕ)
    (hbound : i + n < p.points.length) : (p.intervalPolyline i n).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [length_intervalPolyline] at hj
    rw [point_intervalPolyline _ _ _ _ (by omega),
      point_intervalPolyline _ _ _ _ (by omega)]
    exact hp.1 (i + j) (by omega)
  · intro j hj
    rw [length_intervalPolyline] at hj
    rw [segmentAt_intervalPolyline _ _ _ _ (by omega),
      segmentAt_intervalPolyline _ _ _ _ (by omega),
      point_intervalPolyline _ _ _ _ (by omega)]
    simpa only [Nat.add_assoc] using hp.2.1 (i + j) (by omega)
  · intro j k hj hk hjk
    rw [length_intervalPolyline] at hj hk
    rw [segmentAt_intervalPolyline _ _ _ _ (by omega),
      segmentAt_intervalPolyline _ _ _ _ (by omega)]
    exact hp.2.2 (i + j) (i + k) (by omega) (by omega) (by omega)

/-- Helper toward Proposition 5.16: a segment of a simple polyline meets
the subsequent vertex suffix only at their joining vertex. -/
theorem segment_inter_suffix (p : Polyline) (hp : p.IsSimple) (k : ℕ)
    (hk : k + 1 < p.points.length) :
    p.segmentAt k ∩ (p.intervalPolyline (k + 1) (p.points.length - (k + 1) - 1)).image =
      {p.point (k + 1)} := by
  let n := p.points.length - (k + 1) - 1
  have hbound : (k + 1) + n < p.points.length := by dsimp [n]; omega
  ext w
  constructor
  · rintro ⟨hwk, hws⟩
    rcases hws with hwstart | ⟨j, hj, hwj⟩
    · change w = (p.intervalPolyline (k + 1) n).start at hwstart
      exact mem_singleton_iff.mpr (hwstart.trans (start_intervalPolyline _ _ _))
    · change j + 1 < (p.intervalPolyline (k + 1) n).points.length at hj
      rw [length_intervalPolyline] at hj
      rw [segmentAt_intervalPolyline p (k + 1) n j (by omega)] at hwj
      by_cases hj0 : j = 0
      · subst j
        have hm := hp.2.1 k (by dsimp [n] at hj; omega)
        apply mem_singleton_iff.mp
        rw [← hm]
        exact ⟨hwk, by simpa only [Nat.add_zero] using hwj⟩
      · exact False.elim (Set.disjoint_left.mp
          (hp.2.2 k (k + 1 + j) hk (by dsimp [n] at hj; omega) (by omega)) hwk hwj)
  · intro hw
    have hweq : w = p.point (k + 1) := hw
    subst w
    exact ⟨right_mem_segment ℝ _ _, Or.inl (start_intervalPolyline _ _ _).symm⟩

/-- Helper toward Proposition 5.16: cutting a simple polyline at any
image point retains a simple polygonal suffix. -/
theorem exists_simple_suffix (p : Polyline) (hp : p.IsSimple) {z : ℂ}
    (hz : z ∈ p.image) :
    ∃ q : Polyline, q.IsSimple ∧ q.start = z ∧ q.finish = p.finish ∧ q.image ⊆ p.image := by
  by_cases hzs : z = p.start
  · exact ⟨p, hp, hzs.symm, rfl, subset_rfl⟩
  obtain ⟨k, hk, hzk⟩ : ∃ k, k + 1 < p.points.length ∧ z ∈ p.segmentAt k := by
    rcases hz with hz | hz
    · exact False.elim (hzs hz)
    · exact hz
  let n := p.points.length - (k + 1) - 1
  let s := p.intervalPolyline (k + 1) n
  have hbound : (k + 1) + n < p.points.length := by dsimp [n]; omega
  have hsf : s.finish = p.finish := by
    rw [finish_intervalPolyline, show k + 1 + n = p.points.length - 1 by dsimp [n]; omega,
      point_last_eq_finish]
  have hsim := p.isSimple_intervalPolyline hp (k + 1) n hbound
  have hsub : s.image ⊆ p.image := p.image_intervalPolyline_subset _ _ hbound
  by_cases hze : z = p.point (k + 1)
  · exact ⟨s, hsim, (start_intervalPolyline _ _ _).trans hze.symm, hsf, hsub⟩
  let t := cornerSegment z (p.point (k + 1))
  have hts : t.start = z := (cornerSegment_data _ _).1
  have htf : t.finish = p.point (k + 1) := (cornerSegment_data _ _).2.1
  have hjoin : t.finish = s.start := htf.trans (start_intervalPolyline _ _ _).symm
  have htim : t.image ⊆ p.segmentAt k := by
    rw [image_cornerSegment]
    exact (convex_segment _ _).segment_subset hzk (right_mem_segment ℝ _ _)
  by_cases hn : n = 0
  · have hlast : k + 1 = p.points.length - 1 := by dsimp [n] at hn; omega
    have htf' : t.finish = p.finish := htf.trans (hlast ▸ p.point_last_eq_finish)
    exact ⟨t, isSimple_cornerSegment hze, hts, htf', htim.trans (p.segmentAt_subset_image hk)⟩
  · have hint : t.image ∩ s.image = {t.finish} := by
      apply Set.Subset.antisymm
      · intro w hw
        have hm := p.segment_inter_suffix hp k hk
        have hweq : w = p.point (k + 1) := by
          apply mem_singleton_iff.mp
          rw [← hm]
          exact ⟨htim hw.1, hw.2⟩
        exact hweq.trans htf.symm
      · intro w hw
        have hweq : w = t.finish := hw
        subst w
        exact ⟨by rw [htf, image_cornerSegment]; exact right_mem_segment ℝ _ _,
          Or.inl hjoin⟩
    refine ⟨boundaryConcat t s,
      isSimple_boundaryConcat t s (isSimple_cornerSegment hze) hsim
        (by simp [t, cornerSegment]) (by rw [length_intervalPolyline]; omega) hjoin hint,
      (start_boundaryConcat _ _).trans hts,
      (finish_boundaryConcat_of_join _ _ hjoin).trans hsf, ?_⟩
    rw [image_boundaryConcat _ _ hjoin]
    exact union_subset (htim.trans (p.segmentAt_subset_image hk)) hsub

/-- Helper toward Proposition 5.16: a simple polyline's vertex prefix
meets its next segment only at the joining vertex. -/
theorem prefix_inter_segment (p : Polyline) (hp : p.IsSimple) (k : ℕ)
    (hk : k + 1 < p.points.length) :
    (p.intervalPolyline 0 k).image ∩ p.segmentAt k = {p.point k} := by
  ext w
  constructor
  · rintro ⟨hwpre, hwk⟩
    rcases hwpre with hws | ⟨j, hj, hwj⟩
    · have hws' : w = p.start := by
        have hweq : w = (p.intervalPolyline 0 k).start := hws
        simpa only [start_intervalPolyline, point_zero_eq_start] using hweq
      by_cases hk0 : k = 0
      · simpa only [hk0, point_zero_eq_start, mem_singleton_iff] using hws'
      · have hlen : 2 ≤ p.points.length := by omega
        exact False.elim (hk0 (p.segmentAt_index_eq_zero_of_start_mem hp hlen hk (hws' ▸ hwk)))
    · rw [length_intervalPolyline] at hj
      rw [segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add] at hwj
      by_cases hjk : j + 1 = k
      · have hm := hp.2.1 j (by omega)
        apply mem_singleton_iff.mpr
        have hweq : w = p.point (j + 1) := by
          apply mem_singleton_iff.mp
          rw [← hm]
          exact ⟨hwj, hjk ▸ hwk⟩
        exact hweq.trans (congrArg p.point hjk)
      · exact False.elim (Set.disjoint_left.mp (hp.2.2 j k (by omega) hk (by omega)) hwj hwk)
  · intro hw
    have hweq : w = p.point k := hw
    subst w
    exact ⟨by
      have hsf : (p.intervalPolyline 0 k).finish = p.point k := by
        rw [finish_intervalPolyline, Nat.zero_add]
      rw [← hsf]
      exact (p.intervalPolyline 0 k).finish_mem_image_cornerAccess,
      left_mem_segment ℝ _ _⟩

/-- Helper toward Proposition 5.16: cutting at a noninitial point retains
a simple prefix with the same initial direction argument. -/
theorem exists_simple_prefix_preserving_arg (p : Polyline) (hp : p.IsSimple) {z : ℂ}
    (hz : z ∈ p.image) (hzstart : z ≠ p.start) :
    ∃ q : Polyline, q.IsSimple ∧ q.start = p.start ∧ q.finish = z ∧
      q.image ⊆ p.image ∧ q.initialDirection.arg = p.initialDirection.arg := by
  obtain ⟨k, hk, hzk⟩ : ∃ k, k + 1 < p.points.length ∧ z ∈ p.segmentAt k := by
    rcases hz with hz | hz
    · exact False.elim (hzstart hz)
    · exact hz
  by_cases hk0 : k = 0
  · subst k
    have hzseg0 := hzk
    rw [segmentAt, point_zero_eq_start, segment_eq_image'] at hzk
    obtain ⟨t, ht, htz⟩ := hzk
    change p.start + t • (p.point 1 - p.start) = z at htz
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
      intro ht0
      apply hzstart
      rw [← htz, ← ht0, zero_smul, add_zero])
    let q := cornerSegment p.start z
    have hqim : q.image ⊆ p.image := by
      rw [image_cornerSegment]
      apply Set.Subset.trans _ (p.segmentAt_subset_image hk)
      exact (convex_segment _ _).segment_subset
        (by rw [point_zero_eq_start]; exact left_mem_segment ℝ _ _) hzseg0
    refine ⟨q, isSimple_cornerSegment hzstart.symm,
      (cornerSegment_data _ _).1, (cornerSegment_data _ _).2.1, hqim, ?_⟩
    rw [(cornerSegment_data _ _).2.2, ← htz, add_sub_cancel_left]
    change (t • p.initialDirection).arg = p.initialDirection.arg
    rw [Complex.real_smul, Complex.arg_real_mul _ htpos]
  · let s := p.intervalPolyline 0 k
    have hsim := p.isSimple_intervalPolyline hp 0 k (by omega)
    have hss : s.start = p.start := by rw [start_intervalPolyline, point_zero_eq_start]
    have hsf : s.finish = p.point k := by rw [finish_intervalPolyline, Nat.zero_add]
    have hsub := p.image_intervalPolyline_subset 0 k (by omega)
    have hsdir : s.initialDirection = p.initialDirection := by
      unfold initialDirection
      rw [point_intervalPolyline _ _ _ _ (by omega), Nat.zero_add, hss]
    by_cases hzkpt : z = p.point k
    · exact ⟨s, hsim, hss, hsf.trans hzkpt.symm, hsub, congrArg Complex.arg hsdir⟩
    let t := cornerSegment (p.point k) z
    have hts : t.start = p.point k := (cornerSegment_data _ _).1
    have htf : t.finish = z := (cornerSegment_data _ _).2.1
    have hjoin : s.finish = t.start := hsf.trans hts.symm
    have htim : t.image ⊆ p.segmentAt k := by
      rw [image_cornerSegment]
      exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hzk
    have hint : s.image ∩ t.image = {s.finish} := by
      apply Set.Subset.antisymm
      · intro w hw
        have hweq : w = p.point k := by
          apply mem_singleton_iff.mp
          rw [← p.prefix_inter_segment hp k hk]
          exact ⟨hw.1, htim hw.2⟩
        exact hweq.trans hsf.symm
      · intro w hw
        have hweq : w = s.finish := hw
        subst w
        exact ⟨s.finish_mem_image_cornerAccess,
          Or.inl hjoin⟩
    refine ⟨boundaryConcat s t,
      isSimple_boundaryConcat s t hsim (isSimple_cornerSegment (Ne.symm hzkpt))
        (by rw [length_intervalPolyline]; omega) (by simp [t, cornerSegment]) hjoin hint,
      (start_boundaryConcat _ _).trans hss,
      (finish_boundaryConcat_of_join _ _ hjoin).trans htf, ?_, ?_⟩
    · rw [image_boundaryConcat _ _ hjoin]
      exact union_subset hsub (htim.trans (p.segmentAt_subset_image hk))
    · have hdir : (boundaryConcat s t).initialDirection = s.initialDirection := by
        unfold initialDirection
        rw [point_boundaryConcat_left _ _ 1 (by rw [length_intervalPolyline]; omega),
          start_boundaryConcat]
      rw [hdir, hsdir]

end Polyline

/-- Helper toward Proposition 5.16: a radial segment from a point outside
a closed set has a first contact with that set, at a positive parameter. -/
theorem exists_first_contact_segment {K : Set ℂ} (hK : IsClosed K) {x y : ℂ}
    (hx : x ∉ K) (hy : y ∈ K) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      x + t • (y - x) ∈ K ∧
      segment ℝ x (x + t • (y - x)) ∩ K = {x + t • (y - x)} := by
  let f : ℝ → ℂ := fun t => x + t • (y - x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  let T : Set ℝ := Icc 0 1 ∩ f ⁻¹' K
  have hcompact : IsCompact T := isCompact_Icc.inter_right (hK.preimage hf)
  have h1 : (1 : ℝ) ∈ T := by
    refine ⟨⟨by norm_num, le_rfl⟩, ?_⟩
    simpa [f] using hy
  obtain ⟨t, ht, hmin⟩ := hcompact.exists_isMinOn ⟨1, h1⟩ continuous_id.continuousOn
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1.1
    intro hzero
    apply hx
    have hmem : f t ∈ K := ht.2
    simpa [f, ← hzero] using hmem
  refine ⟨t, htpos, ht.1.2, ht.2, ?_⟩
  ext w
  constructor
  · rintro ⟨hwseg, hwK⟩
    rw [segment_eq_image'] at hwseg
    obtain ⟨s, hs, rfl⟩ := hwseg
    change x + s • (x + t • (y - x) - x) ∈ K at hwK
    have hEq : x + s • (x + t • (y - x) - x) = f (s * t) := by
      simp only [f, add_sub_cancel_left, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
    have hst : s * t ∈ T := by
      refine ⟨⟨mul_nonneg hs.1 htpos.le, ?_⟩, ?_⟩
      · exact (mul_le_of_le_one_left htpos.le hs.2).trans ht.1.2
      · rwa [hEq] at hwK
    have hle : t ≤ s * t := hmin hst
    have hs1 : s = 1 := le_antisymm hs.2 (by nlinarith only [hle, htpos])
    change x + s • (x + t • (y - x) - x) = x + t • (y - x)
    rw [hs1, one_smul, add_sub_cancel]
  · intro hw
    have hweq : w = x + t • (y - x) := hw
    subst w
    exact ⟨right_mem_segment ℝ _ _, ht.2⟩

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: a point of the strict corner sector
has a direction strictly before the next dart direction. -/
theorem ccwTurn_lt_of_mem_initialSector (d : D) (r : ℝ) {z : ℂ}
    (hz : z ∈ P.initialSector d r) :
    ccwTurn (P.arc d).initialDirection (z - P.pos (vert d)) <
      ccwTurn (P.arc d).initialDirection (P.arc (rot d)).initialDirection := by
  obtain ⟨⟨ρ, θ⟩, ⟨hρ, hθ⟩, rfl⟩ := hz
  dsimp only [Prod.fst, Prod.snd] at *
  rw [add_sub_cancel_left]
  have hturn : ccwTurn (P.arc d).initialDirection
      ((ρ : ℂ) * Complex.exp
        ((((P.arc d).initialDirection.arg + θ : ℝ) : ℂ) * Complex.I)) = θ := by
    unfold ccwTurn
    rw [Complex.arg_real_mul _ hρ.1]
    exact d39_ccwTurn_polar _ _ hθ.1 (hθ.2.trans_le (ccwTurn_le_two_pi _ _))
  rw [hturn]
  exact hθ.2

/-- Helper toward Proposition 5.16: straight access to any sector point
satisfies simplicity, image avoidance, and the strict insertion slot. -/
theorem cornerSegment_access [Finite D] {hvert : Function.Surjective vert}
    (S : P.D39PLSeparationData hvert) (d : D) {z : ℂ}
    (hz : z ∈ P.initialSector d S.radius) :
    let g := Polyline.cornerSegment (P.pos (vert d)) z
    g.IsSimple ∧ g.start = P.pos (vert d) ∧ g.finish = z ∧
      z ∉ P.image ∧ Disjoint g.interior P.image ∧
      ccwTurn (P.arc d).initialDirection g.initialDirection <
        ccwTurn (P.arc d).initialDirection (P.arc (rot d)).initialDirection := by
  have hznot := Set.disjoint_left.mp (P.initialSector_disjoint_image S d) hz
  have hvimage : P.pos (vert d) ∈ P.image := Or.inl ⟨vert d, rfl⟩
  have hvz : P.pos (vert d) ≠ z := fun h => hznot (h ▸ hvimage)
  dsimp only
  refine ⟨Polyline.isSimple_cornerSegment hvz,
    (Polyline.cornerSegment_data _ _).1,
    (Polyline.cornerSegment_data _ _).2.1, hznot, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro w hw hwimage
    have hwseg : w ∈ segment ℝ (P.pos (vert d)) z :=
      Polyline.image_cornerSegment _ _ ▸ hw.1
    have hwne : w ∉ ({P.pos (vert d)} : Set ℂ) := by
      intro heq
      apply hw.2
      exact Or.inl heq
    exact Set.disjoint_left.mp (P.initialSector_disjoint_image S d)
      (P.segment_diff_vertex_subset_initialSector d S.radius hz ⟨hwseg, hwne⟩) hwimage
  · rw [(Polyline.cornerSegment_data _ _).2.2]
    exact P.ccwTurn_lt_of_mem_initialSector d S.radius hz




theorem exists_pendant_arc_in_face [Finite D] (hArc : SimpleArcInOpenStatement)
    (hvert : Function.Surjective vert) (S : P.D39PLSeparationData hvert)
    (a : D) (F : P.Face) (haF : P.dartBorders a F) {c : ℂ} (hc : c ∈ F.val) :
    ∃ g : Polyline, g.IsSimple ∧ g.start = P.pos (vert a) ∧ g.finish = c ∧
      c ∉ P.image ∧ Disjoint g.interior P.image ∧
      g.image \ {P.pos (vert a)} ⊆ F.val ∧
      ccwTurn (P.arc a).initialDirection g.initialDirection <
        ccwTurn (P.arc a).initialDirection (P.arc (rot a)).initialDirection := by
  have hsector := P.initialSector_subset_of_dartBorders hvert S a F haF
  have hcnot := P.face_subset_compl F hc
  have hvimage : P.pos (vert a) ∈ P.image := Or.inl ⟨vert a, rfl⟩
  have local_access (z : ℂ) (hz : z ∈ P.initialSector a S.radius) :
      ∃ g : Polyline, g.IsSimple ∧ g.start = P.pos (vert a) ∧ g.finish = z ∧
        z ∉ P.image ∧ Disjoint g.interior P.image ∧
        g.image \ {P.pos (vert a)} ⊆ F.val ∧
        ccwTurn (P.arc a).initialDirection g.initialDirection <
          ccwTurn (P.arc a).initialDirection (P.arc (rot a)).initialDirection := by
    obtain ⟨hsim, hs, hf, hnot, hdis, hslot⟩ := P.cornerSegment_access S a hz
    refine ⟨Polyline.cornerSegment (P.pos (vert a)) z,
      hsim, hs, hf, hnot, hdis, ?_, hslot⟩
    rw [Polyline.image_cornerSegment]
    exact (P.segment_diff_vertex_subset_initialSector a S.radius hz).trans hsector
  obtain ⟨y, hy⟩ := (P.isConnected_initialSector a S.radius_pos).nonempty
  by_cases hyc : y = c
  · exact local_access c (hyc ▸ hy)
  obtain ⟨p, hpsim, hps, hpf, hpim⟩ := hArc F.val
    (P.face_open_frontier_subset_image hvert F).1
    (P.face_isPathConnected hvert F).isConnected y c (hsector hy) hc hyc
  have hvnot : P.pos (vert a) ∉ p.image := by
    intro hvp
    exact P.face_subset_compl F (hpim hvp) hvimage
  have hyp : y ∈ p.image := hps ▸ (show p.start ∈ p.image from Or.inl rfl)
  obtain ⟨t, ht, ht1, hzmem, hmeet⟩ :=
    exists_first_contact_segment p.isCompact_image.isClosed hvnot hyp
  let z := P.pos (vert a) + t • (y - P.pos (vert a))
  have hzsector : z ∈ P.initialSector a S.radius := P.affine_mem_initialSector a S.radius hy ht ht1
  by_cases hzc : z = c
  · exact local_access c (hzc ▸ hzsector)
  obtain ⟨q, hqsim, hqs, hqf, hqim⟩ := p.exists_simple_suffix hpsim hzmem
  let s := Polyline.cornerSegment (P.pos (vert a)) z
  obtain ⟨hssim, hss, hsf, _, _, hslot⟩ := P.cornerSegment_access S a hzsector
  have hjoin : s.finish = q.start := hsf.trans hqs.symm
  have hinter : s.image ∩ q.image = {s.finish} := by
    apply Set.Subset.antisymm
    · intro w hw
      have hweq : w = z := by
        apply mem_singleton_iff.mp
        rw [← hmeet]
        exact ⟨Polyline.image_cornerSegment _ _ ▸ hw.1, hqim hw.2⟩
      exact hweq.trans hsf.symm
    · intro w hw
      have hweq : w = s.finish := hw
      subst w
      exact ⟨by rw [hsf, Polyline.image_cornerSegment]; exact right_mem_segment ℝ _ _,
        Or.inl hjoin⟩
  let g := Polyline.boundaryConcat s q
  have hgstart : g.start = P.pos (vert a) :=
    (Polyline.start_boundaryConcat _ _).trans hss
  have hgfinish : g.finish = c :=
    (Polyline.finish_boundaryConcat_of_join _ _ hjoin).trans (hqf.trans hpf)
  have hgim : g.image \ {P.pos (vert a)} ⊆ F.val := by
    intro w hw
    rw [Polyline.image_boundaryConcat _ _ hjoin] at hw
    rcases hw.1 with hws | hwq
    · have hwseg : w ∈ segment ℝ (P.pos (vert a)) z :=
        Polyline.image_cornerSegment _ _ ▸ hws
      exact hsector (P.segment_diff_vertex_subset_initialSector a S.radius hzsector
        ⟨hwseg, hw.2⟩)
    · exact hpim (hqim hwq)
  have hgdir : g.initialDirection = s.initialDirection := by
    unfold Polyline.initialDirection
    rw [Polyline.point_boundaryConcat_left _ _ 1 (by simp [s, Polyline.cornerSegment]),
      Polyline.start_boundaryConcat]
  refine ⟨g, Polyline.isSimple_boundaryConcat s q hssim hqsim
      (by simp [s, Polyline.cornerSegment])
      (Polyline.length_two_of_start_ne_finish q (by
        rw [hqs, hqf, hpf]; exact hzc)) hjoin hinter,
    hgstart, hgfinish, hcnot, ?_, hgim, ?_⟩
  · apply Set.disjoint_left.mpr
    intro w hw
    apply P.face_subset_compl F
    apply hgim
    refine ⟨hw.1, ?_⟩
    intro hweq
    apply hw.2
    exact Or.inl ((show w = P.pos (vert a) from hweq).trans hgstart.symm)
  · rw [hgdir]
    exact hslot

/-- Helper toward Proposition 5.16: two distinct vertex corners bordering
one face admit a simple chord with both strict corner directions. -/
theorem exists_chord_arc_in_face [Finite D] (hArc : SimpleArcInOpenStatement)
    (hvert : Function.Surjective vert) (S : P.D39PLSeparationData hvert)
    (a b : D) (hvab : vert a ≠ vert b) (F : P.Face)
    (haF : P.dartBorders a F) (hbF : P.dartBorders b F) :
    ∃ g : Polyline, g.IsSimple ∧ g.start = P.pos (vert a) ∧
      g.finish = P.pos (vert b) ∧ Disjoint g.interior P.image ∧
      g.interior ⊆ F.val ∧
      ccwTurn (P.arc a).initialDirection g.initialDirection <
        ccwTurn (P.arc a).initialDirection (P.arc (rot a)).initialDirection ∧
      ccwTurn (P.arc b).initialDirection g.reverse.initialDirection <
        ccwTurn (P.arc b).initialDirection (P.arc (rot b)).initialDirection := by
  have hbsector := P.initialSector_subset_of_dartBorders hvert S b F hbF
  obtain ⟨y, hy⟩ := (P.isConnected_initialSector b S.radius_pos).nonempty
  obtain ⟨p, hpsim, hps, hpf, _, _, hpim, hpslot⟩ :=
    P.exists_pendant_arc_in_face hArc hvert S a F haF (hbsector hy)
  have hvane : P.pos (vert a) ≠ P.pos (vert b) := fun h => hvab (P.pos_injective h)
  have hvbimage : P.pos (vert b) ∈ P.image := Or.inl ⟨vert b, rfl⟩
  have hvnot : P.pos (vert b) ∉ p.image := by
    intro hvp
    exact P.face_subset_compl F (hpim ⟨hvp, Ne.symm hvane⟩) hvbimage
  have hyp : y ∈ p.image := hpf ▸ p.finish_mem_image_cornerAccess
  obtain ⟨t, ht, ht1, hzmem, hmeet⟩ :=
    exists_first_contact_segment p.isCompact_image.isClosed hvnot hyp
  let z := P.pos (vert b) + t • (y - P.pos (vert b))
  have hzsector : z ∈ P.initialSector b S.radius := P.affine_mem_initialSector b S.radius hy ht ht1
  have hzne : z ≠ p.start := by
    intro heq
    have hzimage : z ∈ P.image := by rw [heq, hps]; exact Or.inl ⟨vert a, rfl⟩
    exact P.face_subset_compl F (hbsector hzsector) hzimage
  obtain ⟨q, hqsim, hqs, hqf, hqim, hqarg⟩ :=
    p.exists_simple_prefix_preserving_arg hpsim hzmem hzne
  let s := Polyline.cornerSegment (P.pos (vert b)) z
  obtain ⟨hssim, hss, hsf, _, _, hsslot⟩ := P.cornerSegment_access S b hzsector
  have hjoin : q.finish = s.reverse.start := hqf.trans ((Polyline.start_reverse s).trans hsf).symm
  have hinter : q.image ∩ s.reverse.image = {q.finish} := by
    apply Set.Subset.antisymm
    · intro w hw
      have hws : w ∈ s.image := Polyline.image_reverse_transfer s ▸ hw.2
      have hweq : w = z := by
        apply mem_singleton_iff.mp
        rw [← hmeet]
        exact ⟨Polyline.image_cornerSegment _ _ ▸ hws, hqim hw.1⟩
      exact hweq.trans hqf.symm
    · intro w hw
      have hweq : w = q.finish := hw
      subst w
      exact ⟨q.finish_mem_image_cornerAccess, Or.inl hjoin⟩
  let g := Polyline.boundaryConcat q s.reverse
  have hqlen : 2 ≤ q.points.length := Polyline.length_two_of_start_ne_finish q (by
    rw [hqs, hqf]; exact Ne.symm hzne)
  have hslen : 2 ≤ s.reverse.points.length := by simp [s, Polyline.cornerSegment, Polyline.reverse]
  have hgs : g.start = P.pos (vert a) :=
    (Polyline.start_boundaryConcat _ _).trans (hqs.trans hps)
  have hgf : g.finish = P.pos (vert b) :=
    (Polyline.finish_boundaryConcat_of_join _ _ hjoin).trans ((Polyline.finish_reverse s).trans hss)
  have hgdir : g.initialDirection = q.initialDirection := by
    unfold Polyline.initialDirection
    rw [Polyline.point_boundaryConcat_left _ _ 1 (by omega), Polyline.start_boundaryConcat]
  have hgrdir : g.reverse.initialDirection = s.initialDirection := by
    have hglen : 2 ≤ g.points.length := by
      rw [Polyline.length_boundaryConcat]
      omega
    have hidx : g.points.length - 2 = q.points.length - 1 + 0 := by
      rw [Polyline.length_boundaryConcat]
      have hs2 : s.reverse.points.length = 2 := by
        simp [s, Polyline.cornerSegment, Polyline.reverse]
      omega
    unfold Polyline.initialDirection
    rw [Polyline.reverse_point_one g hglen, Polyline.start_reverse, hgf, hidx,
      Polyline.point_boundaryConcat_right q s.reverse hjoin 0 (by omega),
      Polyline.point_zero_eq_start, Polyline.start_reverse, hsf]
    exact (Polyline.cornerSegment_data _ _).2.2.symm
  have hgint : g.interior ⊆ F.val := by
    intro w hw
    have hwva : w ≠ P.pos (vert a) := by
      intro heq; apply hw.2; exact Or.inl (heq.trans hgs.symm)
    have hwvb : w ≠ P.pos (vert b) := by
      intro heq; apply hw.2; exact Or.inr (heq.trans hgf.symm)
    have hwimage := hw.1
    rw [Polyline.image_boundaryConcat _ _ hjoin] at hwimage
    rcases hwimage with hwq | hws
    · exact hpim ⟨hqim hwq, hwva⟩
    · rw [Polyline.image_reverse_transfer, Polyline.image_cornerSegment] at hws
      exact hbsector (P.segment_diff_vertex_subset_initialSector b S.radius hzsector ⟨hws, hwvb⟩)
  refine ⟨g, Polyline.isSimple_boundaryConcat q s.reverse hqsim
      (Polyline.isSimple_reverse_transfer s hssim) hqlen hslen hjoin hinter,
    hgs, hgf, Set.disjoint_left.mpr (fun w hw => P.face_subset_compl F (hgint hw)),
    hgint, ?_, ?_⟩
  · rw [hgdir]
    unfold ccwTurn at *
    rw [hqarg]
    exact hpslot
  · rw [hgrdir]
    exact hsslot

end PLDrawing

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)

/-- Helper toward Proposition 5.16: every point in the dart's face admits
an arc satisfying the pendant drawing insertion hypotheses. -/
theorem exists_pendant_arc (hArc : SimpleArcInOpenStatement)
    (S : P.D39PLSeparationData hvert) (a : B.D) {c : ℂ}
    (hc : c ∈ (B.plDartFace vert P hvert a).val) :
    ∃ g : Polyline, g.IsSimple ∧ g.start = P.pos (vert a) ∧ g.finish = c ∧
      c ∉ P.image ∧ Disjoint g.interior P.image ∧
      g.image \ {P.pos (vert a)} ⊆ (B.plDartFace vert P hvert a).val ∧
      ccwTurn (P.arc a).initialDirection g.initialDirection <
        ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection :=
  P.exists_pendant_arc_in_face hArc hvert S a _
    ((B.plDartFace_eq_iff vert P hvert a _).mp rfl) hc

/-- Helper toward Proposition 5.16: strict insertion in two distinct
corners implies the four augmented successor conditions for chord insertion. -/
theorem chord_corner_successors_of_strict_turns (a b : B.D) (hvab : vert a ≠ vert b)
    (g : Polyline)
    (hta : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (htb : ccwTurn (P.arc b).initialDirection g.reverse.initialDirection <
      ccwTurn (P.arc b).initialDirection (P.arc (B.map.rot b)).initialDirection) :
    CcwSuccessor {e | B.chordVert vert a b e = vert a}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inl a) (.inr true) ∧
    CcwSuccessor {e | B.chordVert vert a b e = vert a}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inr true) (.inl (B.map.rot a)) ∧
    CcwSuccessor {e | B.chordVert vert a b e = vert b}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inl b) (.inr false) ∧
    CcwSuccessor {e | B.chordVert vert a b e = vert b}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inr false) (.inl (B.map.rot b)) := by
  have hdir : (fun e => (B.chordArc vert P g e).initialDirection) =
      (fun e => (B.pendantArc vert P g e).initialDirection) := by
    funext e
    cases e with
    | inl d => rfl
    | inr t => cases t <;> rfl
  have hstar_a : {e | B.chordVert vert a b e = vert a} =
      {e | B.pendantVert vert a e = some (vert a)} := by
    ext e
    cases e with
    | inl d => simp [chordVert, pendantVert]
    | inr t => cases t <;> simp [chordVert, pendantVert, Ne.symm hvab]
  have ha := B.pendant_attachment_successors vert P a g hta
  have ha' : CcwSuccessor {e | B.chordVert vert a b e = vert a}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inl a) (.inr true) ∧
      CcwSuccessor {e | B.chordVert vert a b e = vert a}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inr true) (.inl (B.map.rot a)) := by
    rw [hstar_a, hdir]
    exact ha
  have hb : CcwSuccessor {e | B.chordVert vert a b e = vert b}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inl b) (.inr false) := by
    refine ⟨Set.toFinite _, rfl, rfl, Or.inr ⟨by simp, ?_⟩⟩
    intro e he hne
    cases e with
    | inl d =>
      have hd : vert d = vert b := he
      exact htb.le.trans (P.rotation_turn_le b d hd)
    | inr t =>
      cases t
      · exact le_rfl
      · exact False.elim (hvab he)
  have hstar_b : {e | B.chordVert vert a b e = vert b} =
      insert (.inr false) (Sum.inl '' {d | vert d = vert b}) := by
    ext e
    cases e with
    | inl d => simp [chordVert]
    | inr t => cases t <;> simp [chordVert, hvab]
  have hgb : CcwSuccessor {e | B.chordVert vert a b e = vert b}
      (fun e => (B.chordArc vert P g e).initialDirection) (.inr false) (.inl (B.map.rot b)) := by
    rw [hstar_b]
    apply ccwSuccessor_insert_next (Sum.inl '' {d | vert d = vert b})
      (fun e => (B.chordArc vert P g e).initialDirection)
      (.inl b) (.inl (B.map.rot b)) (.inr false) (Set.toFinite _)
    · intro p hp q hq hpq heq
      have hpv : B.chordVert vert a b p = vert b := by
        change p ∈ {e | B.chordVert vert a b e = vert b}
        rw [hstar_b]
        exact hp
      have hqv : B.chordVert vert a b q = vert b := by
        change q ∈ {e | B.chordVert vert a b e = vert b}
        rw [hstar_b]
        exact hq
      exact hpq (B.chordArc_initial_arg_injective vert P a b hvab g hta htb p q
        (hpv.trans hqv.symm) heq)
    · rw [hdir]
      exact B.pendant_old_successor vert P g b
    · simp
    · exact htb
  exact ⟨ha'.1, ha'.2, hb, hgb⟩

/-- Helper toward Proposition 5.16: corners of distinct vertices in the
same dart face admit a chord satisfying all drawing insertion hypotheses. -/
theorem exists_chord_arc (hArc : SimpleArcInOpenStatement)
    (S : P.D39PLSeparationData hvert) (a b : B.D) (hvab : vert a ≠ vert b)
    (hface : B.plDartFace vert P hvert a = B.plDartFace vert P hvert b) :
    ∃ g : Polyline, g.IsSimple ∧ g.start = P.pos (vert a) ∧
      g.finish = P.pos (vert b) ∧ Disjoint g.interior P.image ∧
      g.interior ⊆ (B.plDartFace vert P hvert a).val ∧
      CcwSuccessor {e | B.chordVert vert a b e = vert a}
        (fun e => (B.chordArc vert P g e).initialDirection) (.inl a) (.inr true) ∧
      CcwSuccessor {e | B.chordVert vert a b e = vert a}
        (fun e => (B.chordArc vert P g e).initialDirection) (.inr true) (.inl (B.map.rot a)) ∧
      CcwSuccessor {e | B.chordVert vert a b e = vert b}
        (fun e => (B.chordArc vert P g e).initialDirection) (.inl b) (.inr false) ∧
      CcwSuccessor {e | B.chordVert vert a b e = vert b}
        (fun e => (B.chordArc vert P g e).initialDirection) (.inr false) (.inl (B.map.rot b)) ∧
      (P.arc a).initialDirection.arg ≠ g.initialDirection.arg ∧
      (P.arc b).initialDirection.arg ≠ g.reverse.initialDirection.arg := by
  obtain ⟨g, hg, hs, hf, hdis, him, hta, htb⟩ :=
    P.exists_chord_arc_in_face hArc hvert S a b hvab (B.plDartFace vert P hvert a)
      ((B.plDartFace_eq_iff vert P hvert a _).mp rfl)
      ((B.plDartFace_eq_iff vert P hvert b _).mp hface.symm)
  obtain ⟨ha, hga, hb, hgb⟩ := B.chord_corner_successors_of_strict_turns vert P a b hvab g hta htb
  exact ⟨g, hg, hs, hf, hdis, him, ha, hga, hb, hgb,
    Ne.symm (B.chord_direction_ne_old vert P a g.initialDirection hta a rfl),
    Ne.symm (B.chord_direction_ne_old vert P b g.reverse.initialDirection htb b rfl)⟩

/-- Helper toward Proposition 5.16: every point in the initial corner
sector admits a pendant insertion arc, with its punctured image in the
specified dart face. This is the local sector case. -/
theorem exists_pendant_arc_of_mem_initialSector (S : P.D39PLSeparationData hvert)
    (a : B.D) {c : ℂ} (hc : c ∈ P.initialSector a S.radius) :
    ∃ g : Polyline, g.IsSimple ∧ g.start = P.pos (vert a) ∧ g.finish = c ∧
      c ∉ P.image ∧ Disjoint g.interior P.image ∧
      g.image \ {P.pos (vert a)} ⊆ (B.plDartFace vert P hvert a).val ∧
      ccwTurn (P.arc a).initialDirection g.initialDirection <
        ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection := by
  obtain ⟨hsimple, hs, hf, hnot, hdis, hslot⟩ := P.cornerSegment_access S a hc
  refine ⟨Polyline.cornerSegment (P.pos (vert a)) c,
    hsimple, hs, hf, hnot, hdis, ?_, hslot⟩
  rw [Polyline.image_cornerSegment]
  exact B.segment_diff_vertex_subset_plDartFace vert P hvert S a hc

/-- Helper toward Proposition 5.16: the displayed open-set simple-arc
premise supplies a simple connector between distinct points in a dart face. -/
theorem exists_simple_connector_in_plDartFace (hArc : SimpleArcInOpenStatement)
    (a : B.D) {x y : ℂ}
    (hx : x ∈ (B.plDartFace vert P hvert a).val)
    (hy : y ∈ (B.plDartFace vert P hvert a).val) (hxy : x ≠ y) :
    ∃ p : Polyline, p.IsSimple ∧ p.start = x ∧ p.finish = y ∧
      p.image ⊆ (B.plDartFace vert P hvert a).val ∧ Disjoint p.image P.image := by
  let F := B.plDartFace vert P hvert a
  obtain ⟨p, hp, hs, hf, him⟩ := hArc F.val
    (P.face_open_frontier_subset_image hvert F).1
    (P.face_isPathConnected hvert F).isConnected x y hx hy hxy
  refine ⟨p, hp, hs, hf, him, Set.disjoint_left.mpr ?_⟩
  intro z hz
  exact P.face_subset_compl F (him hz)

end D39FiniteBall

end DirectedDistances.PlanarMap
end
