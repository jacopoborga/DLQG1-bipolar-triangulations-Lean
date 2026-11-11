/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLDrawingAugmentation
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness6

/-! Helpers toward Proposition 5.16: first contact for polygonal access to an
No simplicity of the original exterior face is assumed. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace Polyline

/-- Helper toward Proposition 5.16: the first segment meeting a closed set
can be clipped and preceded by the original vertex prefix. The resulting
polyline meets the closed set only at its finish and stays in the old image. -/
theorem exists_first_contact_polyline (p : Polyline) {K : Set ℂ}
    (hK : IsClosed K) (hstart : p.start ∉ K) (hmeet : (p.image ∩ K).Nonempty) :
    ∃ q : Polyline, q.start = p.start ∧ q.finish ∈ K ∧
      q.image ⊆ p.image ∧ q.image ∩ K = {q.finish} ∧
      (p.IsSimple → q.IsSimple ∧ q.initialDirection.arg = p.initialDirection.arg) := by
  classical
  have hex : ∃ k : ℕ, k + 1 < p.points.length ∧ (p.segmentAt k ∩ K).Nonempty := by
    obtain ⟨z, hz, hzK⟩ := hmeet
    rcases hz with hz | ⟨k, hk, hzk⟩
    · exact (hstart (hz ▸ hzK)).elim
    · exact ⟨k, hk, z, hzk, hzK⟩
  let k := Nat.find hex
  have hk : k + 1 < p.points.length := (Nat.find_spec hex).1
  have hprevious (j : ℕ) (hj : j < k) : Disjoint (p.segmentAt j) K := by
    apply Set.disjoint_left.mpr
    intro z hz hzK
    exact Nat.find_min hex hj ⟨by omega, z, hz, hzK⟩
  let s := p.intervalPolyline 0 k
  have hss : s.start = p.start := by rw [start_intervalPolyline, point_zero_eq_start]
  have hsf : s.finish = p.point k := by rw [finish_intervalPolyline, Nat.zero_add]
  have hsK : Disjoint s.image K := by
    apply Set.disjoint_left.mpr
    intro z hz hzK
    rcases hz with hz | ⟨j, hj, hzj⟩
    · exact hstart ((show z = p.start from hz.trans hss) ▸ hzK)
    · rw [length_intervalPolyline] at hj
      rw [segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add] at hzj
      exact Set.disjoint_left.mp (hprevious j (by omega)) hzj hzK
  have hx : p.point k ∉ K := by
    rw [← hsf]
    exact fun h => Set.disjoint_left.mp hsK s.finish_mem_image_cornerAccess h
  obtain ⟨y, hyseg, hyK⟩ := (Nat.find_spec hex).2
  obtain ⟨t, ht, ht1, hzK, hcontact⟩ := exists_first_contact_segment hK hx hyK
  let z := p.point k + t • (y - p.point k)
  let r := cornerSegment (p.point k) z
  have hrs : r.start = p.point k := (cornerSegment_data _ _).1
  have hrf : r.finish = z := (cornerSegment_data _ _).2.1
  have hjoin : s.finish = r.start := hsf.trans hrs.symm
  have hzseg : z ∈ p.segmentAt k := by
    have hzxy : z ∈ segment ℝ (p.point k) y := by
      rw [segment_eq_image']
      exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩
    exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hyseg hzxy
  have hrsub : r.image ⊆ p.segmentAt k := by
    rw [image_cornerSegment]
    exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hzseg
  have hzne : z ≠ p.point k := fun h => hx (h ▸ hzK)
  refine ⟨boundaryConcat s r, (start_boundaryConcat _ _).trans hss, ?_, ?_, ?_, ?_⟩
  · rw [finish_boundaryConcat_of_join _ _ hjoin, hrf]
    exact hzK
  · rw [image_boundaryConcat _ _ hjoin]
    exact union_subset (p.image_intervalPolyline_subset 0 k (by omega))
      (hrsub.trans (p.segmentAt_subset_image hk))
  · rw [image_boundaryConcat _ _ hjoin, union_inter_distrib_right,
      Set.disjoint_iff_inter_eq_empty.mp hsK, empty_union,
      image_cornerSegment, hcontact, finish_boundaryConcat_of_join _ _ hjoin, hrf]
  · intro hp
    by_cases hk0 : k = 0
    · have hqr : boundaryConcat s r = r := by
        dsimp [boundaryConcat, s, intervalPolyline, r, cornerSegment]
        congr 1
        simp [hk0, List.ofFn_succ]
      rw [hqr]
      refine ⟨isSimple_cornerSegment hzne.symm, ?_⟩
      have hzk := hzseg
      rw [hk0, segmentAt, point_zero_eq_start, segment_eq_image'] at hzk
      obtain ⟨u, hu, huz⟩ := hzk
      change p.start + u • (p.point 1 - p.start) = z at huz
      have hup : 0 < u := lt_of_le_of_ne hu.1 (by
        intro hu0
        apply hzne
        rw [hk0, point_zero_eq_start, ← huz, ← hu0, zero_smul, add_zero])
      rw [(cornerSegment_data _ _).2.2, hk0, point_zero_eq_start, ← huz,
        add_sub_cancel_left]
      change (u • p.initialDirection).arg = p.initialDirection.arg
      rw [Complex.real_smul, Complex.arg_real_mul _ hup]
    · have hint : s.image ∩ r.image = {s.finish} := by
        apply Set.Subset.antisymm
        · intro w hw
          have heq : w = p.point k := by
            apply mem_singleton_iff.mp
            rw [← p.prefix_inter_segment hp k hk]
            exact ⟨hw.1, hrsub hw.2⟩
          exact heq.trans hsf.symm
        · intro w hw
          have heq : w = s.finish := hw
          subst w
          exact ⟨s.finish_mem_image_cornerAccess, Or.inl hjoin⟩
      refine ⟨isSimple_boundaryConcat s r (p.isSimple_intervalPolyline hp 0 k (by omega))
        (isSimple_cornerSegment hzne.symm) (by rw [length_intervalPolyline]; omega)
        (by simp [r, cornerSegment]) hjoin hint, ?_⟩
      have hdir : (boundaryConcat s r).initialDirection = p.initialDirection := by
        unfold initialDirection
        rw [point_boundaryConcat_left _ _ 1 (by rw [length_intervalPolyline]; omega),
          start_boundaryConcat, point_intervalPolyline _ _ _ _ (by omega),
          Nat.zero_add, hss]
      exact congrArg Complex.arg hdir

/-- Helper toward Proposition 5.16: a polyline starting strictly inside a
square and ending outside its closed square has a first boundary-contact
prefix. Simplicity and the initial direction argument are retained. -/
theorem exists_first_contact_enclosingSquare (p : Polyline) (R : ℝ) (hR : 0 < R)
    (hs : max |p.start.re| |p.start.im| < R)
    (hf : R < max |p.finish.re| |p.finish.im|) :
    ∃ q : Polyline, q.start = p.start ∧ q.finish ∈ (enclosingSquare R).image ∧
      q.image ⊆ p.image ∧ q.image ∩ (enclosingSquare R).image = {q.finish} ∧
      (p.IsSimple → q.IsSimple ∧ q.initialDirection.arg = p.initialDirection.arg) := by
  let f : ℂ → ℝ := fun z => max |z.re| |z.im|
  have hcont : Continuous f :=
    (continuous_abs.comp Complex.continuous_re).max
      (continuous_abs.comp Complex.continuous_im)
  have hlevel (z : ℂ) : z ∈ (enclosingSquare R).image ↔ f z = R := by
    rw [mem_enclosingSquare_image_iff R hR]
    constructor
    · rintro ⟨hre, him, hside⟩
      have hra := abs_le.mpr hre
      have hia := abs_le.mpr him
      rcases hside with h | h | h | h
      · simp only [f, h, abs_neg, abs_of_pos hR, max_eq_left hia]
      · simp only [f, h, abs_of_pos hR, max_eq_left hia]
      · simp only [f, h, abs_neg, abs_of_pos hR, max_eq_right hra]
      · simp only [f, h, abs_of_pos hR, max_eq_right hra]
    · intro hz
      have hra : |z.re| ≤ R := (le_max_left _ _).trans_eq hz
      have hia : |z.im| ≤ R := (le_max_right _ _).trans_eq hz
      refine ⟨abs_le.mp hra, abs_le.mp hia, ?_⟩
      rcases max_eq_iff.mp hz with h | h
      · rcases (abs_eq hR.le).mp h.1 with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
      · rcases (abs_eq hR.le).mp h.1 with h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
  have hmeet : (p.image ∩ (enclosingSquare R).image).Nonempty := by
    obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1
      (hcont.comp p.toPath.continuous) (show f (p.toPath 0) ≤ R ∧ R ≤ f (p.toPath 1) by
        simpa only [Path.source, Path.target] using And.intro hs.le hf.le)
    refine ⟨p.toPath t, ?_, (hlevel _).mpr ht⟩
    rw [← range_toPath]
    exact Set.mem_range_self t
  exact p.exists_first_contact_polyline (enclosingSquare R).isCompact_image.isClosed
    (fun h => (ne_of_lt hs) ((hlevel _).mp h)) hmeet

/-- Helper toward Proposition 5.16: a set strictly enclosed by a square
is disjoint from its geometric boundary. -/
theorem disjoint_enclosingSquare_image_of_bound {S : Set ℂ} (R : ℝ) (hR : 0 < R)
    (hbound : ∀ z ∈ S, max |z.re| |z.im| < R) :
    Disjoint S (enclosingSquare R).image := by
  apply Set.disjoint_left.mpr
  intro z hz hzframe
  have hb := hbound z hz
  have hr := abs_lt.mp ((le_max_left _ _).trans_lt hb)
  have hi := abs_lt.mp ((le_max_right _ _).trans_lt hb)
  obtain ⟨_, _, hside⟩ := (mem_enclosingSquare_image_iff R hR z).mp hzframe
  rcases hside with h | h | h | h <;> linarith only [hr.1, hr.2, hi.1, hi.2, h]

end Polyline

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: first contact from an open dart face
retains avoidance of the drawing, with no condition on the face boundary. -/
theorem exists_first_contact_in_plDartFace {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (a : B.D) (p : Polyline)
    (hp : p.image ⊆ (B.plDartFace vert P hvert a).val)
    (R : ℝ) (hR : 0 < R)
    (hs : max |p.start.re| |p.start.im| < R)
    (hf : R < max |p.finish.re| |p.finish.im|) :
    ∃ q : Polyline, q.start = p.start ∧ q.finish ∈ (Polyline.enclosingSquare R).image ∧
      q.image ⊆ p.image ∧ q.image ∩ (Polyline.enclosingSquare R).image = {q.finish} ∧
      Disjoint q.image P.image := by
  obtain ⟨q, hqs, hqf, hsub, hcontact, _⟩ := p.exists_first_contact_enclosingSquare R hR hs hf
  exact ⟨q, hqs, hqf, hsub, hcontact, Set.disjoint_left.mpr
    (fun _ hz => P.face_subset_compl _ (hp (hsub hz)))⟩

/-- Helper toward Proposition 5.16: the access-arc construction used in
`exists_star_pendant_drawings`, clipped at its first frame contact, inserts
a pendant ending on the enclosing square. Every old dart arc is preserved. -/
theorem exists_pendant_drawing_to_enclosingSquare {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (a : B.D)
    (hext : ¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val)
    (R : ℝ) (hR : 0 < R)
    (hbound : ∀ z ∈ P.image, max |z.re| |z.im| < R) :
    ∃ Q : PLDrawing (B.insertPendant a).D (Option V)
        (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a),
      (∀ v, Q.pos (some v) = P.pos v) ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      Q.pos none ∈ (Polyline.enclosingSquare R).image ∧
      (Q.arc (.inr true)).image ∩ (Polyline.enclosingSquare R).image = {Q.pos none} ∧
      Q.image ∩ (Polyline.enclosingSquare R).image = {Q.pos none} := by
  classical
  have hex : ∃ c ∈ (B.plDartFace vert P hvert a).val, R < max |c.re| |c.im| := by
    by_contra hn
    push Not at hn
    apply hext
    rw [isBounded_iff_forall_norm_le]
    refine ⟨2 * R, fun z hz => ?_⟩
    have hb := hn z hz
    have hr := (le_max_left |z.re| |z.im|).trans hb
    have hi := (le_max_right |z.re| |z.im|).trans hb
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith only [hr, hi])
  obtain ⟨c, hc, hcR⟩ := hex
  obtain ⟨S, _⟩ := P.exists_D39PLSeparationData hvert
  obtain ⟨g, hg, hgs, hgf, _hcnot, _hgdis, hgface, hslot⟩ :=
    B.exists_pendant_arc vert P hvert star_simpleArcInOpen S a hc
  have hgR : max |g.start.re| |g.start.im| < R := by
    rw [hgs]
    exact hbound _ (Or.inl ⟨vert a, rfl⟩)
  obtain ⟨q, hqs, hqf, hsub, hcontact, hsimple⟩ :=
    g.exists_first_contact_enclosingSquare R hR hgR (by rwa [hgf])
  obtain ⟨hq, harg⟩ := hsimple hg
  have hqstart : q.start = P.pos (vert a) := hqs.trans hgs
  have hframe := Polyline.disjoint_enclosingSquare_image_of_bound R hR hbound
  have hnot : q.finish ∉ P.image := by
    intro h
    exact Set.disjoint_left.mp hframe h hqf
  have hdis : Disjoint q.interior P.image := by
    apply Set.disjoint_left.mpr
    intro z hz
    apply P.face_subset_compl (B.plDartFace vert P hvert a)
    apply hgface
    refine ⟨hsub hz.1, ?_⟩
    intro heq
    apply hz.2
    exact Or.inl ((show z = P.pos (vert a) from heq).trans hqstart.symm)
  have hqslot : ccwTurn (P.arc a).initialDirection q.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection := by
    simpa only [ccwTurn, harg] using hslot
  refine ⟨B.insertPendantDrawing vert P a q.finish hnot q hq hqstart rfl hdis hqslot,
    fun _ => rfl, fun _ => rfl, hqf, hcontact, ?_⟩
  change (B.insertPendantDrawing vert P a q.finish hnot q hq hqstart rfl hdis hqslot).image ∩
    (Polyline.enclosingSquare R).image = {q.finish}
  rw [B.insertPendantDrawing_image vert P a q.finish hnot q hq hqstart rfl hdis hqslot,
    union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hframe,
    empty_union, hcontact]

/-- Helper toward Proposition 5.16: both drawings admit pendants from the
same exterior-face corner to a common enclosing square. Each pendant first
meets the frame at its new vertex, and all original whole dart arcs survive. -/
theorem exists_pendant_drawings_to_common_enclosingSquare
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (a : B.D)
    (hext : (¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val) ∧
      (¬ Bornology.IsBounded (B.plDartFace vert P' hvert a).val)) :
    ∃ (R : ℝ)
      (Q Q' : PLDrawing (B.insertPendant a).D (Option V)
        (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a)),
      0 < R ∧
      (∀ z ∈ P.image ∪ P'.image, max |z.re| |z.im| < R) ∧
      (∀ v, Q.pos (some v) = P.pos v) ∧
      (∀ v, Q'.pos (some v) = P'.pos v) ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) ∧
      Q.pos none ∈ (Polyline.enclosingSquare R).image ∧
      Q'.pos none ∈ (Polyline.enclosingSquare R).image ∧
      (Q.arc (.inr true)).image ∩ (Polyline.enclosingSquare R).image = {Q.pos none} ∧
      (Q'.arc (.inr true)).image ∩ (Polyline.enclosingSquare R).image = {Q'.pos none} ∧
      Q.image ∩ (Polyline.enclosingSquare R).image = {Q.pos none} ∧
      Q'.image ∩ (Polyline.enclosingSquare R).image = {Q'.pos none} := by
  obtain ⟨A, hA⟩ := (P.isBounded_image.union P'.isBounded_image).exists_norm_le
  let R := max A 0 + 1
  have hR : 0 < R := lt_of_le_of_lt (le_max_right A 0) (lt_add_one _)
  have hb (z : ℂ) (hz : z ∈ P.image ∪ P'.image) : max |z.re| |z.im| < R := by
    exact (max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)).trans_lt
      ((hA z hz).trans_lt (lt_of_le_of_lt (le_max_left A 0) (lt_add_one _)))
  obtain ⟨Q, hp, harc, hq, hcontact, hwhole⟩ :=
    B.exists_pendant_drawing_to_enclosingSquare vert P hvert a hext.1 R hR
      (fun z hz => hb z (Or.inl hz))
  obtain ⟨Q', hp', harc', hq', hcontact', hwhole'⟩ :=
    B.exists_pendant_drawing_to_enclosingSquare vert P' hvert a hext.2 R hR
      (fun z hz => hb z (Or.inr hz))
  exact ⟨R, Q, Q', hR, hb, hp, hp', harc, harc', hq, hq', hcontact, hcontact',
    hwhole, hwhole'⟩

end D39FiniteBall
end DirectedDistances.PlanarMap

end






























































