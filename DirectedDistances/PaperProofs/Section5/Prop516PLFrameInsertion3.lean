/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLFrameInsertion2

/-! Helpers toward Proposition 5.16: successive straight sides of the corner frame. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology
namespace Polyline

/-- Helper toward Proposition 5.16: deleting the closing side of a simple
quadrilateral leaves a simple chain of three straight sides. -/
theorem isSimple_three_sides_of_quadrilateral (c A B C : ℂ)
    (hF : (ofHead c [A, B, C, c]).IsCyclicSimple) :
    (ofHead c [A, B, C]).IsSimple := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    change i + 1 < 4 at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact hF.2.2.1 0 (by change 1 < 5; omega)
    · exact hF.2.2.1 1 (by change 2 < 5; omega)
    · exact hF.2.2.1 2 (by change 3 < 5; omega)
  · intro i hi
    change i + 2 < 4 at hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact hF.2.2.2.1 0 (by change 2 < 5; omega)
    · exact hF.2.2.2.1 1 (by change 3 < 5; omega)
  · intro i j hi hj hij
    change i + 1 < 4 at hi
    change j + 1 < 4 at hj
    have hi0 : i = 0 := by omega
    have hj2 : j = 2 := by omega
    subst i
    subst j
    exact hF.2.2.2.2.1 0 2 (by change 1 < 5; omega)
      (by change 3 < 5; omega) (by omega) (by change ¬ (0 = 0 ∧ 4 = 5); omega)

/-- Helper toward Proposition 5.16: a next segment meets the base drawing
and the preceding prefix only at its joining vertex. -/
theorem segmentAt_inter_base_union_prefix (p : Polyline) (hp : p.IsSimple)
    (K : Set ℂ) (hcontact : p.image ∩ K = {p.start})
    (k : ℕ) (hk : k + 1 < p.points.length) :
    p.segmentAt k ∩ (K ∪ (p.intervalPolyline 0 k).image) = {p.point k} := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hzK | hzpre⟩
    · have heq : z = p.start := hcontact.subset ⟨p.segmentAt_subset_image hk hz, hzK⟩
      apply (p.prefix_inter_segment hp k hk).subset
      refine ⟨?_, hz⟩
      exact Or.inl (heq.trans ((p.point_zero_eq_start).symm.trans
        (p.start_intervalPolyline 0 k).symm))
    · exact (p.prefix_inter_segment hp k hk).subset ⟨hzpre, hz⟩
  · rintro z rfl
    exact ⟨left_mem_segment ℝ _ _, Or.inr
      (by simpa only [p.finish_intervalPolyline, Nat.zero_add] using
        (p.intervalPolyline 0 k).finish_mem_image_cornerAccess)⟩

/-- Helper toward Proposition 5.16: appending one segment to a vertex
prefix appends exactly that segment to its image. -/
theorem image_prefix_succ (p : Polyline) (k : ℕ) :
    (p.intervalPolyline 0 (k + 1)).image =
      (p.intervalPolyline 0 k).image ∪ p.segmentAt k := by
  apply Set.Subset.antisymm
  · rintro z (hz | ⟨j, hj, hz⟩)
    · exact Or.inl (Or.inl (by simpa only [start_intervalPolyline] using hz))
    · rw [length_intervalPolyline] at hj
      rw [segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add] at hz
      by_cases hjk : j = k
      · exact Or.inr (hjk ▸ hz)
      · exact Or.inl (Or.inr ⟨j, by rw [length_intervalPolyline]; omega,
          by rwa [segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add]⟩)
  · rintro z ((hz | ⟨j, hj, hz⟩) | hz)
    · exact Or.inl (by simpa only [start_intervalPolyline] using hz)
    · rw [length_intervalPolyline] at hj
      refine Or.inr ⟨j, by rw [length_intervalPolyline]; omega, ?_⟩
      rw [segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add] at hz ⊢
      exact hz
    · exact Or.inr ⟨k, by rw [length_intervalPolyline]; omega,
        by rwa [segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add]⟩

/-- Helper toward Proposition 5.16: the final straight side meets the
base and the three inserted sides exactly at its two prescribed endpoints. -/
theorem closing_side_inter_base_three_sides (c A B C : ℂ)
    (hF : (ofHead c [A, B, C, c]).IsCyclicSimple) (K : Set ℂ)
    (hcontact : (ofHead c [A, B, C, c]).image ∩ K = {c}) :
    (cornerSegment C c).image ∩ (K ∪ (ofHead c [A, B, C]).image) = {C, c} := by
  let F := ofHead c [A, B, C, c]
  have hg : (cornerSegment C c).image = F.segmentAt 3 := image_cornerSegment C c
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hzK | hzpre⟩
    · exact Or.inr (hcontact.subset
        ⟨F.segmentAt_subset_image (i := 3) (by change 4 < 5; omega) (hg ▸ hz), hzK⟩)
    · rcases hzpre with hzpre | ⟨j, hj, hzpre⟩
      · exact Or.inr hzpre
      · change j + 1 < 4 at hj
        rw [hg] at hz
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
        · exact Or.inr (hF.2.2.2.2.2.subset ⟨hzpre, hz⟩)
        · exact False.elim (Set.disjoint_left.mp
            (hF.2.2.2.2.1 1 3 (by change 2 < 5; omega)
              (by change 4 < 5; omega) (by omega) (by omega)) hzpre hz)
        · exact Or.inl ((hF.2.2.2.1 2 (by change 4 < 5; omega)).subset ⟨hzpre, hz⟩)
  · intro z hz
    rcases hz with hz | hz
    · change z = C at hz
      rw [hz]
      refine ⟨Or.inl rfl, Or.inr ?_⟩
      exact (ofHead c [A, B, C]).finish_mem_image_cornerAccess
    · change z = c at hz
      rw [hz]
      exact ⟨(cornerSegment C c).finish_mem_image_cornerAccess, Or.inr (Or.inl rfl)⟩

/-- Helper toward Proposition 5.16: the closing side is simple and its
interior avoids the base and all three previously inserted frame sides. -/
theorem closing_side_simple_disjoint (c A B C : ℂ)
    (hF : (ofHead c [A, B, C, c]).IsCyclicSimple) (K : Set ℂ)
    (hcontact : (ofHead c [A, B, C, c]).image ∩ K = {c}) :
    (cornerSegment C c).IsSimple ∧
      Disjoint (cornerSegment C c).interior (K ∪ (ofHead c [A, B, C]).image) := by
  refine ⟨isSimple_cornerSegment (hF.2.2.1 3 (by change 4 < 5; omega)), ?_⟩
  apply Set.disjoint_left.mpr
  intro z hz hzK
  have he := (closing_side_inter_base_three_sides c A B C hF K hcontact).subset ⟨hz.1, hzK⟩
  rcases he with he | he
  · exact hz.2 (Or.inl he)
  · exact hz.2 (Or.inr he)

/-- Helper toward Proposition 5.16: once the frame is present and the
whole drawing is on its closed inside, its outside is an actual complementary
component. This does not identify the boundary-walk orbit. -/
theorem outside_component_of_enclosing_set (p : Polyline) (hp : p.IsCyclicSimple)
    (K : Set ℂ) (hboundary : p.image ⊆ K) (hinside : K ⊆ closure p.inside)
    (z : ℂ) (hz : z ∈ p.outside) :
    connectedComponentIn Kᶜ z = p.outside := by
  have hclosed : p.start = p.finish := by
    rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
    exact hp.2.1
  have havoid : p.outside ⊆ Kᶜ := by
    intro w hw hwK
    exact (p.closure_sides_avoid hclosed).1 (hinside hwK) hw
  apply Set.Subset.antisymm
  · exact (connectedComponentIn_mono z (Set.compl_subset_compl.mpr hboundary)).trans
      (p.component_subset_outside hclosed z hz)
  · exact (p.isConnected_inside_outside_cyclic hp).2.isPreconnected.subset_connectedComponentIn
      hz havoid

end Polyline
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: insert the next prescribed side of a
simple chain at its current leaf, retaining every arc and vertex position. -/
theorem exists_next_chain_side_drawing {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (Q : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (hleaf : B.map.rot a = a)
    (p : Polyline) (hp : p.IsSimple) (K : Set ℂ)
    (hcontact : p.image ∩ K = {p.start}) (k : ℕ)
    (hk : k + 1 < p.points.length)
    (hpos : Q.pos (vert a) = p.point k)
    (himage : Q.image = K ∪ (p.intervalPolyline 0 k).image) :
    ∃ T : PLDrawing (B.insertPendant a).D (Option V)
      (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a),
      (∀ x, T.pos (some x) = Q.pos x) ∧
      (∀ d : B.D, T.arc (.inl d) = Q.arc d) ∧
      T.pos none = p.point (k + 1) ∧
      T.arc (.inr true) = Polyline.cornerSegment (p.point k) (p.point (k + 1)) ∧
      T.image = Q.image ∪ p.segmentAt k := by
  let g := Polyline.cornerSegment (p.point k) (p.point (k + 1))
  have hct : g.image ∩ Q.image = {g.start} := by
    rw [Polyline.image_cornerSegment, himage]
    exact p.segmentAt_inter_base_union_prefix hp K hcontact k hk
  obtain ⟨T, hv, ha, hn, hg, hi⟩ := B.exists_pendantDrawing_at_leaf vert Q a hleaf
    g (Polyline.isSimple_cornerSegment (hp.1 k hk)) (by change 2 ≤ 2; omega)
    hpos.symm hct
  exact ⟨T, hv, ha, hn, hg, by
    simpa only [g, Polyline.image_cornerSegment, Polyline.segmentAt] using hi⟩

/-- Helper toward Proposition 5.16: the first three sides of a simple
four-vertex chain can be inserted successively at its leaves. The entire
base drawing is retained, and every added side is the prescribed segment. -/
theorem exists_three_chain_sides_drawing {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (Q : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (hleaf : B.map.rot a = a)
    (p : Polyline) (hp : p.IsSimple) (hlen : p.points.length = 4)
    (hs : p.start = Q.pos (vert a)) (hcontact : p.image ∩ Q.image = {p.start}) :
    let D₁ := B.insertPendant a
    let v₁ := B.pendantVert vert a
    let D₂ := D₁.insertPendant (.inr false)
    let v₂ := D₁.pendantVert v₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let v₃ := D₂.pendantVert v₂ (.inr false)
    ∃ T : PLDrawing D₃.D (Option (Option (Option V)))
        D₃.map.edgeInv D₃.map.rot v₃,
      (∀ x, T.pos (some (some (some x))) = Q.pos x) ∧
      (∀ d : B.D, T.arc (.inl (.inl (.inl d))) = Q.arc d) ∧
      T.pos (some (some none)) = p.point 1 ∧
      T.pos (some none) = p.point 2 ∧ T.pos none = p.point 3 ∧
      T.arc (.inl (.inl (.inr true))) = Polyline.cornerSegment (p.point 0) (p.point 1) ∧
      T.arc (.inl (.inr true)) = Polyline.cornerSegment (p.point 1) (p.point 2) ∧
      T.arc (.inr true) = Polyline.cornerSegment (p.point 2) (p.point 3) ∧
      T.image = Q.image ∪ p.image := by
  dsimp only
  have hzero : (p.intervalPolyline 0 0).image = {p.start} := by
    apply Set.Subset.antisymm
    · rintro z (hz | ⟨j, hj, _⟩)
      · simpa only [Polyline.start_intervalPolyline, Polyline.point_zero_eq_start] using hz
      · rw [Polyline.length_intervalPolyline] at hj
        omega
    · rintro z rfl
      exact Or.inl (by simp only [Polyline.start_intervalPolyline,
        Polyline.point_zero_eq_start, Set.mem_singleton_iff])
  have hi₀ : Q.image = Q.image ∪ (p.intervalPolyline 0 0).image := by
    rw [hzero]
    exact (Set.union_eq_left.mpr (by rintro z rfl; exact Or.inl ⟨vert a, hs.symm⟩)).symm
  obtain ⟨T₁, hv₁, ha₁, hn₁, hg₁, hi₁⟩ :=
    B.exists_next_chain_side_drawing vert Q a hleaf p hp Q.image hcontact 0
      (by omega) (by rw [Polyline.point_zero_eq_start]; exact hs.symm) hi₀
  have hi₁' : T₁.image = Q.image ∪ (p.intervalPolyline 0 1).image := by
    rw [p.image_prefix_succ 0, ← Set.union_assoc, ← hi₀]
    exact hi₁
  obtain ⟨T₂, hv₂, ha₂, hn₂, hg₂, hi₂⟩ :=
    (B.insertPendant a).exists_next_chain_side_drawing (B.pendantVert vert a)
      T₁ (.inr false) (by rfl) p hp Q.image hcontact 1 (by omega) hn₁ hi₁'
  have hi₂' : T₂.image = Q.image ∪ (p.intervalPolyline 0 2).image := by
    rw [p.image_prefix_succ 1, ← Set.union_assoc, ← hi₁']
    exact hi₂
  obtain ⟨T₃, hv₃, ha₃, hn₃, hg₃, hi₃⟩ :=
    ((B.insertPendant a).insertPendant (.inr false)).exists_next_chain_side_drawing
      ((B.insertPendant a).pendantVert (B.pendantVert vert a) (.inr false))
      T₂ (.inr false) (by rfl) p hp Q.image hcontact 2 (by omega) hn₂ hi₂'
  have hfull : (p.intervalPolyline 0 3).image = p.image := by
    apply Set.Subset.antisymm
    · exact p.image_intervalPolyline_subset 0 3 (by omega)
    · rintro z (hz | ⟨j, hj, hz⟩)
      · exact Or.inl (by simpa only [Polyline.start_intervalPolyline,
          Polyline.point_zero_eq_start] using hz)
      · refine Or.inr ⟨j, by rw [Polyline.length_intervalPolyline]; omega, ?_⟩
        rwa [Polyline.segmentAt_intervalPolyline _ _ _ _ (by omega), Nat.zero_add]
  refine ⟨T₃, ?_, ?_, ?_, ?_, hn₃, ?_, ?_, hg₃, ?_⟩
  · intro x
    rw [hv₃, hv₂, hv₁]
  · intro d
    exact (ha₃ (.inl (.inl d))).trans ((ha₂ (.inl d)).trans (ha₁ d))
  · rw [hv₃, hv₂, hn₁]
  · rw [hv₃, hn₂]
  · exact (ha₃ (.inl (.inr true))).trans ((ha₂ (.inr true)).trans hg₁)
  · exact (ha₃ (.inr true)).trans hg₂
  · rw [← hfull, p.image_prefix_succ 2, ← Set.union_assoc, ← hi₂']
    exact hi₃

/-- Helper toward Proposition 5.16: three sides of a disjoint corner
quadrilateral extend the first-contact pendant drawing, preserving all its
arcs and positions. No hypothesis on simplicity of the old face is used. -/
theorem exists_three_quadrilateral_sides_drawing {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (a : B.D)
    (Q : PLDrawing (B.insertPendant a).D (Option V)
      (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a))
    (A B₁ C : ℂ)
    (hF : (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).IsCyclicSimple)
    (hcontact : (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).image ∩ Q.image =
      {Q.pos none}) :
    let D := B.insertPendant a
    let w := B.pendantVert vert a
    let D₁ := D.insertPendant (.inr false)
    let w₁ := D.pendantVert w (.inr false)
    let D₂ := D₁.insertPendant (.inr false)
    let w₂ := D₁.pendantVert w₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let w₃ := D₂.pendantVert w₂ (.inr false)
    ∃ T : PLDrawing D₃.D (Option (Option (Option (Option V))))
        D₃.map.edgeInv D₃.map.rot w₃,
      (∀ x, T.pos (some (some (some x))) = Q.pos x) ∧
      (∀ d : D.D, T.arc (.inl (.inl (.inl d))) = Q.arc d) ∧
      T.pos (some (some none)) = A ∧ T.pos (some none) = B₁ ∧ T.pos none = C ∧
      T.arc (.inl (.inl (.inr true))) = Polyline.cornerSegment (Q.pos none) A ∧
      T.arc (.inl (.inr true)) = Polyline.cornerSegment A B₁ ∧
      T.arc (.inr true) = Polyline.cornerSegment B₁ C ∧
      T.image = Q.image ∪ (Polyline.ofHead (Q.pos none) [A, B₁, C]).image := by
  let p := Polyline.ofHead (Q.pos none) [A, B₁, C]
  have hp := Polyline.isSimple_three_sides_of_quadrilateral (Q.pos none) A B₁ C hF
  have hsub : p.image ⊆ (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).image := by
    rintro z (hz | ⟨j, hj, hz⟩)
    · exact Or.inl hz
    · change j + 1 < 4 at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact Or.inr ⟨0, by change 1 < 5; omega, hz⟩
      · exact Or.inr ⟨1, by change 2 < 5; omega, hz⟩
      · exact Or.inr ⟨2, by change 3 < 5; omega, hz⟩
  have hct : p.image ∩ Q.image = {p.start} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hcontact.subset ⟨hsub hz.1, hz.2⟩
    · rintro z rfl
      exact ⟨Or.inl rfl, Or.inl ⟨none, rfl⟩⟩
  exact (B.insertPendant a).exists_three_chain_sides_drawing
    (B.pendantVert vert a) Q (.inr false) (by rfl) p hp rfl rfl hct

/-- Helper toward Proposition 5.16: the second and third frame sides,
together with the first, are inserted in both drawings on the same map.
Every pre-existing dart retains its entire arc, including both access darts. -/
theorem exists_three_quadrilateral_sides_drawings {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (a : B.D)
    (Q Q' : PLDrawing (B.insertPendant a).D (Option V)
      (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a))
    (A B₁ C A' B₁' C' : ℂ)
    (hF : (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).IsCyclicSimple)
    (hF' : (Polyline.ofHead (Q'.pos none) [A', B₁', C', Q'.pos none]).IsCyclicSimple)
    (hcontact : (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).image ∩ Q.image =
      {Q.pos none})
    (hcontact' : (Polyline.ofHead (Q'.pos none) [A', B₁', C', Q'.pos none]).image ∩ Q'.image =
      {Q'.pos none}) :
    let D := B.insertPendant a
    let w := B.pendantVert vert a
    let D₁ := D.insertPendant (.inr false)
    let w₁ := D.pendantVert w (.inr false)
    let D₂ := D₁.insertPendant (.inr false)
    let w₂ := D₁.pendantVert w₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let w₃ := D₂.pendantVert w₂ (.inr false)
    ∃ T T' : PLDrawing D₃.D (Option (Option (Option (Option V))))
        D₃.map.edgeInv D₃.map.rot w₃,
      (∀ x, T.pos (some (some (some x))) = Q.pos x) ∧
      (∀ x, T'.pos (some (some (some x))) = Q'.pos x) ∧
      (∀ d : D.D, T.arc (.inl (.inl (.inl d))) = Q.arc d) ∧
      (∀ d : D.D, T'.arc (.inl (.inl (.inl d))) = Q'.arc d) ∧
      T.pos (some (some none)) = A ∧ T.pos (some none) = B₁ ∧ T.pos none = C ∧
      T'.pos (some (some none)) = A' ∧ T'.pos (some none) = B₁' ∧ T'.pos none = C' ∧
      T.arc (.inl (.inl (.inr true))) = Polyline.cornerSegment (Q.pos none) A ∧
      T.arc (.inl (.inr true)) = Polyline.cornerSegment A B₁ ∧
      T.arc (.inr true) = Polyline.cornerSegment B₁ C ∧
      T'.arc (.inl (.inl (.inr true))) = Polyline.cornerSegment (Q'.pos none) A' ∧
      T'.arc (.inl (.inr true)) = Polyline.cornerSegment A' B₁' ∧
      T'.arc (.inr true) = Polyline.cornerSegment B₁' C' ∧
      T.image = Q.image ∪ (Polyline.ofHead (Q.pos none) [A, B₁, C]).image ∧
      T'.image = Q'.image ∪ (Polyline.ofHead (Q'.pos none) [A', B₁', C']).image ∧
      (Polyline.cornerSegment C (Q.pos none)).IsSimple ∧
      Disjoint (Polyline.cornerSegment C (Q.pos none)).interior T.image ∧
      (Polyline.cornerSegment C' (Q'.pos none)).IsSimple ∧
      Disjoint (Polyline.cornerSegment C' (Q'.pos none)).interior T'.image := by
  obtain ⟨T, hv, ha, hA, hB, hC, hg₀, hg₁, hg₂, hi⟩ :=
    B.exists_three_quadrilateral_sides_drawing vert a Q A B₁ C hF hcontact
  obtain ⟨T', hv', ha', hA', hB', hC', hg₀', hg₁', hg₂', hi'⟩ :=
    B.exists_three_quadrilateral_sides_drawing vert a Q' A' B₁' C' hF' hcontact'
  obtain ⟨hc, hd⟩ := Polyline.closing_side_simple_disjoint (Q.pos none) A B₁ C hF
    Q.image hcontact
  obtain ⟨hc', hd'⟩ := Polyline.closing_side_simple_disjoint (Q'.pos none) A' B₁' C' hF'
    Q'.image hcontact'
  exact ⟨T, T', hv, hv', ha, ha', hA, hB, hC, hA', hB', hC',
    hg₀, hg₁, hg₂, hg₀', hg₁', hg₂', hi, hi', hc, hi.symm ▸ hd, hc', hi'.symm ▸ hd'⟩

/-- Helper toward Proposition 5.16: closing a three-pendant chain at its
original attachment corner produces a face-successor orbit of period four.
This is a combinatorial assertion, independent of geometric chord insertion. -/
theorem three_pendant_closing_chord_period (B : D39FiniteBall) (a : B.D) :
    let D₁ := B.insertPendant a
    let D₂ := D₁.insertPendant (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let x : D₃.D := .inr false
    let y : D₃.D := .inl (.inl (.inl a))
    let hxy : x ≠ y := by exact Sum.inr_ne_inl
    Function.minimalPeriod (D₃.chordMap x y hxy).faceSucc (.inr false) = 4 := by
  dsimp only
  let D₁ := B.insertPendant a
  let D₂ := D₁.insertPendant (.inr false)
  let D₃ := D₂.insertPendant (.inr false)
  have h₁ := B.star_pendant_face_period a
  have h₂ := D₁.star_pendant_face_period (.inr false)
  have h₃ := D₂.star_pendant_face_period (.inr false)
  have hi : 3 < Function.minimalPeriod D₃.map.faceSucc (.inr false) := by
    change 3 < Function.minimalPeriod (D₂.pendantMap (.inr false)).faceSucc (.inr false)
    rw [h₃]
    change 3 < Function.minimalPeriod (D₁.pendantMap (.inr false)).faceSucc (.inr false) + 2
    rw [h₂]
    change 3 < Function.minimalPeriod (B.pendantMap a).faceSucc (.inr false) + 2 + 2
    rw [h₁]
    omega
  have hwalk : (D₃.map.faceSucc : D₃.D → D₃.D)^[3] (.inr false) =
      .inl (.inl (.inl a)) := by
    rfl
  exact D₃.chordMap_faceSucc_minimalPeriod_new (.inr false) (.inl (.inl (.inl a)))
    (by exact Sum.inr_ne_inl) false 3 hi hwalk

/-- Helper toward Proposition 5.16: the four vertices on the combinatorial
closing-chord face are the attachment vertex and the three distinct new
vertices. No geometric or exterior-face assertion is inferred from this. -/
theorem three_pendant_closing_chord_vertices_injOn {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V) (a : B.D) :
    let D₁ := B.insertPendant a
    let w₁ := B.pendantVert vert a
    let D₂ := D₁.insertPendant (.inr false)
    let w₂ := D₁.pendantVert w₁ (.inr false)
    let D₃ := D₂.insertPendant (.inr false)
    let w₃ := D₂.pendantVert w₂ (.inr false)
    let x : D₃.D := .inr false
    let y : D₃.D := .inl (.inl (.inl a))
    let hxy : x ≠ y := by exact Sum.inr_ne_inl
    Set.InjOn (fun k : ℕ => D₃.chordVert w₃ x y
      (((D₃.chordMap x y hxy).faceSucc : (D₃.D ⊕ Bool) → (D₃.D ⊕ Bool))^[k]
        (.inr false))) (Set.Iio 4) := by
  dsimp only
  intro n hn m hm heq
  simp only [Set.mem_Iio] at hn hm
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl | rfl
  all_goals
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with rfl | rfl | rfl | rfl
  all_goals first | rfl | cases heq

/-- Helper toward Proposition 5.16: a geometrically enclosing simple
polygon identifies an unbounded orbit face, without any simple-exterior
premise. Identification with the specific closing-chord orbit is separate. -/
theorem exists_unbounded_orbit_face_of_enclosing_polygon {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (p : Polyline) (hp : p.IsCyclicSimple)
    (hboundary : p.image ⊆ P.image) (hinside : P.image ⊆ closure p.inside) :
    ∃ O : D39BallFaceCycleOrbit B,
      (B.plOrbitFace vert P hvert O).val = p.outside ∧
      ¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O).val := by
  have hclosed : p.start = p.finish := by
    rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
    exact hp.2.1
  obtain ⟨z, hz, _⟩ := p.outside_unbounded hclosed 0
  have hznot : z ∉ P.image := by
    intro h
    exact (p.closure_sides_avoid hclosed).1 (hinside h) hz
  obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr hznot
  have hF : F.val = p.outside := by
    obtain ⟨w, hw, hFw⟩ := F.property
    calc
      F.val = connectedComponentIn P.imageᶜ z :=
        hFw.trans (connectedComponentIn_eq (hFw ▸ hzF))
      _ = p.outside := p.outside_component_of_enclosing_set hp P.image hboundary hinside z hz
  obtain ⟨O, hO⟩ := B.plOrbitFace_surjective vert P hvert F
  refine ⟨O, (congrArg Subtype.val hO).trans hF, ?_⟩
  rw [(congrArg Subtype.val hO).trans hF]
  intro hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  obtain ⟨w, hw, hRw⟩ := p.outside_unbounded hclosed R
  exact (not_le_of_gt hRw) (hR w hw)

end D39FiniteBall
end DirectedDistances.PlanarMap

end









































































































































