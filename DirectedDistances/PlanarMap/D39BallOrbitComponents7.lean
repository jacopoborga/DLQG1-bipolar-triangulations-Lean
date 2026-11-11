/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents6

/-! # Return paths for nonbridge edge insertion

to the coordinator; these declarations do not assert paper completion. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Topology

namespace Polyline

/-- Helper toward Proposition 5.16: loop erasure preserves both endpoints,
image containment and any predicate on the ordered original segments. -/
theorem exists_vertex_injective_preserving_edges (c : Polyline)
    (R : ℂ → ℂ → Prop)
    (hR : ∀ k, k + 1 < c.points.length → R (c.point k) (c.point (k + 1))) :
    ∃ q : Polyline, q.start = c.start ∧ q.finish = c.finish ∧ q.image ⊆ c.image ∧
      (∀ a b, a < q.points.length → b < q.points.length →
        q.point a = q.point b → a = b) ∧
      ∀ k, k + 1 < q.points.length → R (q.point k) (q.point (k + 1)) := by
  classical
  suffices H : ∀ n, ∀ p : Polyline, p.points.length = n →
      (∀ k, k + 1 < p.points.length → R (p.point k) (p.point (k + 1))) →
      ∃ q : Polyline, q.start = p.start ∧ q.finish = p.finish ∧ q.image ⊆ p.image ∧
        (∀ a b, a < q.points.length → b < q.points.length →
          q.point a = q.point b → a = b) ∧
        ∀ k, k + 1 < q.points.length → R (q.point k) (q.point (k + 1)) from
    H c.points.length c rfl hR
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hlen hpR
    by_cases hinj : ∀ a b, a < p.points.length → b < p.points.length →
        p.point a = p.point b → a = b
    · exact ⟨p, rfl, rfl, Subset.rfl, hinj, hpR⟩
    push Not at hinj
    obtain ⟨a, b, ha, hb, hab, hne⟩ := hinj
    have hrep : ∃ i j, i < j ∧ j < p.points.length ∧ p.point i = p.point j := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨a, b, hlt, hb, hab⟩
      · exact ⟨b, a, hgt, ha, hab.symm⟩
    obtain ⟨i, j, hij, hj, heq⟩ := hrep
    let N := p.points.length - 1
    have hpos : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    have hlast : j + (N - j) = N := by dsimp [N]; omega
    let l := p.intervalPolyline 0 i
    let t := p.intervalPolyline j (N - j)
    let s := boundaryConcat l t
    have hjoin : l.finish = t.start := by
      simp only [l, t, finish_intervalPolyline, start_intervalPolyline, Nat.zero_add]
      exact heq
    have hsstart : s.start = p.start := by
      simp only [s, start_boundaryConcat, l, start_intervalPolyline, point_zero_eq_start]
    have hsfinish : s.finish = p.finish := by
      rw [show s = boundaryConcat l t from rfl, finish_boundaryConcat_of_join l t hjoin]
      simp only [t, finish_intervalPolyline, hlast, N, point_last_eq_finish]
    have hsimage : s.image ⊆ p.image := by
      rw [show s = boundaryConcat l t from rfl, image_boundaryConcat l t hjoin]
      exact union_subset (p.image_intervalPolyline_subset 0 i (by omega))
        (p.image_intervalPolyline_subset j (N - j) (by dsimp [N] at hlast ⊢; omega))
    have hsR : ∀ k, k + 1 < s.points.length → R (s.point k) (s.point (k + 1)) :=
      edges_boundaryConcat l t hjoin R
        (p.edges_intervalPolyline R hpR 0 i (by omega))
        (p.edges_intervalPolyline R hpR j (N - j) (by dsimp [N] at hlast ⊢; omega))
    have hslen : s.points.length < n := by
      simp only [s, length_boundaryConcat, l, t, length_intervalPolyline]
      dsimp [N]
      omega
    obtain ⟨q, hqs, hqf, hqi, hqv, hqR⟩ := ih s.points.length hslen s rfl hsR
    exact ⟨q, hqs.trans hsstart, hqf.trans hsfinish, hqi.trans hsimage, hqv, hqR⟩

/-- Helper toward Proposition 5.16: a vertex-injective chain with only
endpoint intersections between different segments is a simple open arc. -/
theorem isSimple_of_vertex_injective_of_segment_endpoints (c : Polyline)
    (hinj : ∀ a b, a < c.points.length → b < c.points.length →
      c.point a = c.point b → a = b)
    (hmeet : ∀ i j, i + 1 < c.points.length → j + 1 < c.points.length → i ≠ j →
      ∀ z, z ∈ c.segmentAt i → z ∈ c.segmentAt j →
        (z = c.point i ∨ z = c.point (i + 1)) ∧
        (z = c.point j ∨ z = c.point (j + 1))) : c.IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi heq
    have := hinj i (i + 1) (by omega) hi heq
    omega
  · intro i hi
    apply Subset.antisymm
    · rintro z ⟨hzi, hzj⟩
      obtain ⟨hz, hw⟩ := hmeet i (i + 1) (by omega) hi (by omega) z hzi hzj
      rcases hz with hz | hz
      · rcases hw with hw | hw
        all_goals
          have := hinj _ _ (by omega) (by omega) (hz.symm.trans hw)
          omega
      · exact hz
    · rintro z rfl
      exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · intro i j hi hj hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨hz, hw⟩ := hmeet i j hi hj (by omega) z hzi hzj
    rcases hz with hz | hz <;> rcases hw with hw | hw
    all_goals
      have := hinj _ _ (by omega) (by omega) (hz.symm.trans hw)
      omega

end Polyline

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: erasing repeated vertices in a drawing
walk gives a geometrically simple arc when all retained segments are actual
segments of the drawing, including reversed arcs and multiedges. -/
theorem isSimple_of_arc_segment_sources (c : Polyline)
    (hinj : ∀ a b, a < c.points.length → b < c.points.length →
      c.point a = c.point b → a = b)
    (hsource : ∀ k, k + 1 < c.points.length → ∃ d : D, ∃ a : ℕ,
      a + 1 < (P.arc d).points.length ∧ c.point k = (P.arc d).point a ∧
        c.point (k + 1) = (P.arc d).point (a + 1)) : c.IsSimple := by
  apply c.isSimple_of_vertex_injective_of_segment_endpoints hinj
  intro i j hi hj hij z hzi hzj
  obtain ⟨d, a, ha, hia, hia1⟩ := hsource i hi
  obtain ⟨e, b, hb, hjb, hjb1⟩ := hsource j hj
  have hza : z ∈ (P.arc d).segmentAt a := by
    simpa only [Polyline.segmentAt, hia, hia1] using hzi
  have hzb : z ∈ (P.arc e).segmentAt b := by
    simpa only [Polyline.segmentAt, hjb, hjb1] using hzj
  by_cases hed : e = d
  · subst e
    have hab : a ≠ b := by
      intro hab
      exact hij (hinj i j (by omega) (by omega) (by rw [hia, hjb, hab]))
    rw [hia, hia1, hjb, hjb1]
    exact (P.arc d).segmentAt_intersection_endpoints (P.arc_simple d) a b ha hb hab hza hzb
  by_cases hef : e = flip d
  · subst e
    rw [P.arc_flip] at hb hjb hjb1 hzb
    have hb' : b + 1 < (P.arc d).points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hb
    let b' := (P.arc d).points.length - 2 - b
    have hb'valid : b' + 1 < (P.arc d).points.length := by dsimp [b']; omega
    have hjrev : c.point j = (P.arc d).point (b' + 1) := by
      rw [hjb, Polyline.point_reverse_transfer _ (by omega)]
      congr 1
      dsimp [b']; omega
    have hjrev1 : c.point (j + 1) = (P.arc d).point b' := by
      rw [hjb1, Polyline.point_reverse_transfer _ hb']
      congr 1
      dsimp [b']; omega
    rw [Polyline.segmentAt_reverse_transfer _ hb'] at hzb
    have hab : a ≠ b' := by
      intro hab
      have h1 := hinj i (j + 1) (by omega) hj (by rw [hia, hjrev1, hab])
      have h2 := hinj (i + 1) j hi (by omega) (by rw [hia1, hjrev, hab])
      omega
    obtain ⟨hzae, hzbe⟩ := (P.arc d).segmentAt_intersection_endpoints
      (P.arc_simple d) a b' ha hb'valid hab hza hzb
    rw [hia, hia1, hjrev, hjrev1]
    exact ⟨hzae, hzbe.symm⟩
  · rw [hia, hia1, hjb, hjb1]
    exact P.arc_segment_intersection_endpoints d e hed hef a b ha hb hza hzb

/-- Helper toward Proposition 5.16: an arbitrary finite drawing walk has
an endpoint-preserving simple loop erasure using only original segments. -/
theorem exists_simple_of_arc_segment_sources (c : Polyline)
    (hsource : ∀ k, k + 1 < c.points.length → ∃ d : D, ∃ a : ℕ,
      a + 1 < (P.arc d).points.length ∧ c.point k = (P.arc d).point a ∧
        c.point (k + 1) = (P.arc d).point (a + 1)) :
    ∃ q : Polyline, q.IsSimple ∧ q.start = c.start ∧ q.finish = c.finish ∧
      q.image ⊆ c.image ∧
      ∀ k, k + 1 < q.points.length → ∃ d : D, ∃ a : ℕ,
        a + 1 < (P.arc d).points.length ∧ q.point k = (P.arc d).point a ∧
          q.point (k + 1) = (P.arc d).point (a + 1) := by
  obtain ⟨q, hqs, hqf, hqi, hqv, hqR⟩ :=
    c.exists_vertex_injective_preserving_edges
      (fun x y => ∃ d : D, ∃ a : ℕ, a + 1 < (P.arc d).points.length ∧
        x = (P.arc d).point a ∧ y = (P.arc d).point (a + 1)) hsource
  exact ⟨q, P.isSimple_of_arc_segment_sources q hqv hqR, hqs, hqf, hqi, hqR⟩

/-- Helper toward Proposition 5.16: reversing an actual drawing segment
still gives an actual segment, on the reversed dart with its exact index. -/
theorem arc_segment_source_symm {x y : ℂ}
    (h : ∃ d : D, ∃ a : ℕ, a + 1 < (P.arc d).points.length ∧
      x = (P.arc d).point a ∧ y = (P.arc d).point (a + 1)) :
    ∃ d : D, ∃ a : ℕ, a + 1 < (P.arc d).points.length ∧
      y = (P.arc d).point a ∧ x = (P.arc d).point (a + 1) := by
  obtain ⟨d, a, ha, rfl, rfl⟩ := h
  let b := (P.arc d).points.length - 2 - a
  have hb : b + 1 < (P.arc d).points.length := by dsimp [b]; omega
  refine ⟨flip d, b, ?_, ?_, ?_⟩
  · simpa only [P.arc_flip, Polyline.reverse, List.length_reverse] using hb
  · rw [P.arc_flip, Polyline.point_reverse_transfer _ (by omega)]
    congr 1
    dsimp [b]; omega
  · rw [P.arc_flip, Polyline.point_reverse_transfer _ hb]
    congr 1
    dsimp [b]; omega

/-- Helper toward Proposition 5.16: combinatorial dart connectivity gives
an actual finite polyline in the drawing, retaining ordered segment sources. -/
theorem exists_polyline_of_eqvGen (d e : D)
    (h : Relation.EqvGen (fun x y => rot x = y ∨ flip x = y) d e) :
    ∃ c : Polyline, c.start = P.pos (vert d) ∧ c.finish = P.pos (vert e) ∧
      c.image ⊆ P.image ∧
      ∀ k, k + 1 < c.points.length → ∃ f : D, ∃ a : ℕ,
        a + 1 < (P.arc f).points.length ∧ c.point k = (P.arc f).point a ∧
          c.point (k + 1) = (P.arc f).point (a + 1) := by
  have hconstant (d : D) :
      ∃ c : Polyline, c.start = P.pos (vert d) ∧ c.finish = P.pos (vert d) ∧
        c.image ⊆ P.image ∧
        ∀ k, k + 1 < c.points.length → ∃ f : D, ∃ a : ℕ,
          a + 1 < (P.arc f).points.length ∧ c.point k = (P.arc f).point a ∧
            c.point (k + 1) = (P.arc f).point (a + 1) := by
    refine ⟨Polyline.ofHead (P.pos (vert d)) [], rfl, rfl, ?_, ?_⟩
    · intro z hz
      have hz' : z = P.pos (vert d) := by
        simpa [Polyline.image, Polyline.ofHead, Polyline.start] using hz
      exact Or.inl ⟨vert d, hz'.symm⟩
    · intro k hk
      simp only [Polyline.ofHead, List.length_cons, List.length_nil] at hk
      omega
  induction h with
  | rel d e hstep =>
    rcases hstep with rfl | rfl
    · simpa only [P.vert_rotation] using hconstant d
    · exact ⟨P.arc d, P.arc_start d, P.arc_finish d,
        fun z hz => Or.inr ⟨d, hz⟩, fun k hk => ⟨d, k, hk, rfl, rfl⟩⟩
  | refl d => exact hconstant d
  | symm d e _ ih =>
    obtain ⟨c, hcs, hcf, hci, hcR⟩ := ih
    refine ⟨c.reverse, (Polyline.start_reverse c).trans hcf,
      (Polyline.finish_reverse c).trans hcs, ?_, ?_⟩
    · rw [Polyline.image_reverse_transfer]
      exact hci
    · intro k hk
      have hk' : k + 1 < c.points.length := by
        simpa only [Polyline.reverse, List.length_reverse] using hk
      let j := c.points.length - 2 - k
      have hj : j + 1 < c.points.length := by dsimp [j]; omega
      have hrev := P.arc_segment_source_symm (hcR j hj)
      rw [Polyline.point_reverse_transfer c (by omega),
        Polyline.point_reverse_transfer c hk']
      simpa only [show c.points.length - 1 - k = j + 1 by dsimp [j]; omega,
        show c.points.length - 1 - (k + 1) = j by dsimp [j]; omega] using hrev
  | trans d e f _ _ ih₁ ih₂ =>
    obtain ⟨c, hcs, hcf, hci, hcR⟩ := ih₁
    obtain ⟨q, hqs, hqf, hqi, hqR⟩ := ih₂
    have hjoin : c.finish = q.start := hcf.trans hqs.symm
    refine ⟨Polyline.boundaryConcat c q,
      (Polyline.start_boundaryConcat c q).trans hcs,
      (Polyline.finish_boundaryConcat_of_join c q hjoin).trans hqf, ?_, ?_⟩
    · rw [Polyline.image_boundaryConcat c q hjoin]
      exact union_subset hci hqi
    · exact Polyline.edges_boundaryConcat c q hjoin
        (fun x y => ∃ f : D, ∃ a : ℕ, a + 1 < (P.arc f).points.length ∧
          x = (P.arc f).point a ∧ y = (P.arc f).point (a + 1)) hcR hqR

/-- Helper toward Proposition 5.16: any two incident vertices in a
combinatorially connected drawing admit a simple old-drawing return arc. -/
theorem exists_simple_polyline_of_eqvGen (d e : D)
    (h : Relation.EqvGen (fun x y => rot x = y ∨ flip x = y) d e) :
    ∃ q : Polyline, q.IsSimple ∧ q.start = P.pos (vert d) ∧
      q.finish = P.pos (vert e) ∧ q.image ⊆ P.image := by
  obtain ⟨c, hcs, hcf, hci, hcR⟩ := P.exists_polyline_of_eqvGen d e h
  obtain ⟨q, hq, hqs, hqf, hqi, _⟩ := P.exists_simple_of_arc_segment_sources c hcR
  exact ⟨q, hq, hqs.trans hcs, hqf.trans hcf, hqi.trans hci⟩

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: a polygon in the drawing containing
an oriented dart segment separates that dart's left and right named faces.
The proof uses the winding jump and connectedness of each actual face. -/
theorem plDartFace_ne_flip_of_cyclicSimple_segment {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (c : Polyline) (hc : c.IsCyclicSimple)
    (himage : c.image ⊆ P.image) (d : B.D) (i j : ℕ)
    (hi : i + 1 < c.points.length) (hj : j + 1 < (P.arc d).points.length)
    (h₀ : c.point i = (P.arc d).point j)
    (h₁ : c.point (i + 1) = (P.arc d).point (j + 1)) :
    B.plDartFace vert P hvert d ≠ B.plDartFace vert P hvert (B.map.edgeInv d) := by
  let x := midpoint ℝ (c.point i) (c.point (i + 1))
  have hne : c.point i ≠ c.point (i + 1) := hc.2.2.1 i hi
  have hx : x ∈ openSegment ℝ (c.point i) (c.point (i + 1)) :=
    midpoint_mem_openSegment _ _
  have hxa : x ≠ c.point i := by
    intro h
    exact hne (left_mem_openSegment_iff.mp (h ▸ hx))
  have hxb : x ≠ c.point (i + 1) := by
    intro h
    exact hne (right_mem_openSegment_iff.mp (h ▸ hx))
  have hxarc : x ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)) := by
    simpa only [h₀, h₁] using hx
  let L := B.plDartFace vert P hvert d
  let R := B.plDartFace vert P hvert (B.map.edgeInv d)
  have hLb : P.dartBorders d L := (B.plDartFace_eq_iff vert P hvert d L).mp rfl
  have hRb : P.dartBorders (B.map.edgeInv d) R :=
    (B.plDartFace_eq_iff vert P hvert (B.map.edgeInv d) R).mp rfl
  obtain ⟨rL, hrL, hL⟩ := P.exists_ball_left_subset_of_dartBorders hvert d L hLb hj hxarc
  obtain ⟨rR, hrR, hR⟩ :=
    P.exists_ball_right_subset_of_dartBorders_flip hvert d R hRb hj hxarc
  obtain ⟨ε, hε, hjump⟩ := c.angleSum_edge_jump_cyclic hc i hi x
    (openSegment_subset_segment ℝ _ _ hx) hxa hxb
  let r := min ε (min rL rR)
  have hr : 0 < r := lt_min hε (lt_min hrL hrR)
  have hd : c.point (i + 1) - c.point i ≠ 0 := sub_ne_zero.mpr hne.symm
  obtain ⟨u, hu⟩ := Polyline.leftHalfDisc_nonempty x _ r hd hr
  obtain ⟨v, hv⟩ := Polyline.rightHalfDisc_nonempty x _ r hd hr
  have huL : u ∈ L.val := hL u
    (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu.1)
    (by simpa only [Set.mem_ofPred_eq, h₀, h₁] using hu.2)
  have hvR : v ∈ R.val := hR v
    (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hv.1)
    (by simpa only [Set.mem_ofPred_eq, h₀, h₁] using hv.2)
  have hnot (H : P.Face) : H.val ⊆ c.imageᶜ :=
    fun z hz hzc => P.face_subset_compl H hz (himage hzc)
  have hjump' := hjump u v (hnot L huL) (hnot R hvR)
    (lt_of_lt_of_le hu.1 (min_le_left _ _))
    (lt_of_lt_of_le hv.1 (min_le_left _ _)) (mul_neg_of_pos_of_neg hu.2 hv.2)
  intro heq
  change L = R at heq
  have hvL : v ∈ L.val := by rw [heq]; exact hvR
  have hclosed : c.start = c.finish := by
    rw [← c.point_zero_eq_start, ← c.point_last_eq_finish]
    exact hc.2.1
  have heqangle := c.angleSum_eq_of_isPreconnected hclosed L.val
    (P.face_isPathConnected hvert L).isConnected.isPreconnected (hnot L) u v huL hvL
  rw [heqangle, sub_self, abs_zero] at hjump'
  exact zero_ne_one hjump'

/-- Helper toward Proposition 5.16: inserting an edge into a face of a
connected old drawing gives distinct faces on its two sides. An old-drawing
return walk is constructed and loop-erased before applying polygonal winding
separation; no orbit correspondence or Euler formula is assumed. -/
theorem plDartFace_new_ne_flip_of_nonbridge_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hflip : ∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d))
    (hvertι : ∀ d : B'.D, vert (ι d) = vert' d)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F' : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F'.val) :
    B.plDartFace vert P hvert newDart ≠
      B.plDartFace vert P hvert (B.map.edgeInv newDart) := by
  let p := P.arc newDart
  have hp : p.IsSimple := P.arc_simple newDart
  have hplen : 2 ≤ p.points.length := P.arc_length newDart
  have hne : p.start ≠ p.finish := by
    intro heq
    have ht : p.toPath 0 = p.toPath 1 := by
      rw [Path.source, Path.target]
      exact heq
    have h01 := p.toPath_injective hplen hp ht
    exact zero_ne_one h01
  obtain ⟨d, hd⟩ := hvert' (vert newDart)
  obtain ⟨e, he⟩ := hvert' (vert (B.map.edgeInv newDart))
  obtain ⟨q, hq, hqs, hqf, hqi⟩ :=
    P'.exists_simple_polyline_of_eqvGen d e (hconn' d e)
  have hstart : p.start = q.start := by
    rw [hqs, hd]
    exact (P.arc_start newDart).trans (hpos _)
  have hfinish : p.finish = q.finish := by
    rw [hqf, he]
    exact (P.arc_finish newDart).trans (hpos _)
  have hqlen : 2 ≤ q.points.length := q.length_two_of_start_ne_finish
    (by rw [← hstart, ← hfinish]; exact hne)
  have hint : p.image ∩ q.image = {p.start, p.finish} := by
    apply Subset.antisymm
    · rintro z ⟨hzp, hzq⟩
      by_contra hz
      have hzint : z ∈ p.interior := ⟨hzp, hz⟩
      exact P'.face_subset_compl F' (hinterior hzint) (hqi hzq)
    · intro z hz
      rcases hz with rfl | hz
      · refine ⟨Or.inl rfl, ?_⟩
        rw [hstart]
        exact Or.inl rfl
      · rw [mem_singleton_iff] at hz
        subst z
        constructor
        · rw [← p.point_last_eq_finish]
          exact p.point_mem_image (by omega)
        · rw [hfinish, ← q.point_last_eq_finish]
          exact q.point_mem_image (by omega)
  let c := Polyline.closedConcat p q
  have hc : c.IsCyclicSimple :=
    Polyline.closedConcat_isCyclicSimple p q hp hq hplen hqlen hstart hfinish hne hint
  have him := plImage_eq_union_of_edge_insertion B' B vert' vert P' P newDart ι himage hpos harcs
  have hcimage : c.image ⊆ P.image := by
    rw [show c = Polyline.closedConcat p q from rfl, Polyline.image_closedConcat p q hfinish]
    apply union_subset
    · exact fun z hz => Or.inr ⟨newDart, hz⟩
    · intro z hz
      rw [him]
      exact Or.inl (hqi hz)
  apply B.plDartFace_ne_flip_of_cyclicSimple_segment vert P hvert c hc hcimage newDart 0 0
    (by have := hc.1; omega) (by change 1 < p.points.length; omega)
  · exact Polyline.point_closedConcat_left p q 0 (by omega)
  · exact Polyline.point_closedConcat_left p q 1 (by omega)

/-- Helper toward Proposition 5.16: a nonbridge insertion splits its old
face into exactly two distinct relative components, identified with the
left and right dart faces. -/
theorem exists_exactly_two_components_of_nonbridge_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hflip : ∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d))
    (hvertι : ∀ d : B'.D, vert (ι d) = vert' d)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F' : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F'.val) :
    ∃ u v : ℂ, u ∈ F'.val \ (P.arc newDart).image ∧
      v ∈ F'.val \ (P.arc newDart).image ∧
      connectedComponentIn (F'.val \ (P.arc newDart).image) u =
        (B.plDartFace vert P hvert newDart).val ∧
      connectedComponentIn (F'.val \ (P.arc newDart).image) v =
        (B.plDartFace vert P hvert (B.map.edgeInv newDart)).val ∧
      connectedComponentIn (F'.val \ (P.arc newDart).image) u ≠
        connectedComponentIn (F'.val \ (P.arc newDart).image) v ∧
      ∀ z ∈ F'.val \ (P.arc newDart).image,
        connectedComponentIn (F'.val \ (P.arc newDart).image) z =
          connectedComponentIn (F'.val \ (P.arc newDart).image) u ∨
        connectedComponentIn (F'.val \ (P.arc newDart).image) z =
          connectedComponentIn (F'.val \ (P.arc newDart).image) v := by
  obtain ⟨u, v, hu, hv, hL, hR⟩ :=
    exists_components_eq_plDartFaces_of_edge_insertion B' B vert' vert P' P
      hvert' hvert newDart ι himage hpos harcs F' hinterior
  have hne := plDartFace_new_ne_flip_of_nonbridge_edge_insertion B' B vert' vert P' P
    hvert' hvert hconn' newDart ι himage hflip hvertι hpos harcs F' hinterior
  refine ⟨u, v, hu, hv, hL, hR, ?_, ?_⟩
  · rw [hL, hR]
    exact fun h => hne (Subtype.ext h)
  · intro z hz
    rw [hL, hR]
    exact component_face_diff_eq_plDartFace_or_flip_of_edge_insertion B' B vert' vert P' P
      hvert' hvert newDart ι himage hpos harcs F' hinterior z hz

/-- Helper toward Proposition 5.16: the two new dart orientations belong
to different face-successor orbits after a nonbridge insertion. This is
only orbit separation, not the common-face orbit-uniqueness induction step. -/
theorem not_sameCycle_new_flip_of_nonbridge_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hflip : ∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d))
    (hvertι : ∀ d : B'.D, vert (ι d) = vert' d)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F' : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F'.val) :
    ¬ B.map.faceSucc.SameCycle newDart (B.map.edgeInv newDart) := by
  intro hcycle
  exact plDartFace_new_ne_flip_of_nonbridge_edge_insertion B' B vert' vert P' P
    hvert' hvert hconn' newDart ι himage hflip hvertι hpos harcs F' hinterior
    (B.plDartFace_eq_of_sameCycle vert P hvert _ _ hcycle)

end D39FiniteBall



















































































end DirectedDistances.PlanarMap
end

