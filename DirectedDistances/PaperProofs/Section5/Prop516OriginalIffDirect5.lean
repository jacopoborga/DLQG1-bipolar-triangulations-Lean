/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect3
import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact20
import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact21

/-! Helper toward Proposition 5.16. The SidesExact20 bound applies directly to
the bent polygonal edge subarc in a `LeftAtOn` witness. The remaining signed
localization and the two general-drawing face obligations are recorded below. -/

public section

namespace DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

open DirectedDistances.PlanarMap
open Set unitInterval

/-- Helper toward Proposition 5.16: a face-contained simple return gives the
unrestricted polygonal edge-subarc winding bound, including when that subarc
contains bends. -/
theorem edgeSubarc_winding_bounds_of_face_return
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (a b : unitInterval) (hab : a < b)
    (q : Path ((P.arc d).toPath b) ((P.arc d).toPath a))
    (hqi : Function.Injective q)
    (hqF : ∀ t : unitInterval, t ∈ openParams → q t ∈ F.val)
    (w : ℂ) (n : ℤ)
    (hw : HasWinding
      ((edgeSubarc (P.arc d).toPath a b hab.le).trans q) w n) :
    -1 ≤ n ∧ n ≤ 1 := by
  let γ := (P.arc d).toPath
  have hreturn : Set.range q ∩ P.image = {γ b, γ a} :=
    returnPath_inter_drawing P d F a b q hqF
  have hedge : Set.range (edgeSubarc γ a b hab.le) ⊆ P.image := by
    intro z hz
    rw [range_edgeSubarc_eq_image_Icc32 γ a b hab.le] at hz
    rcases hz with ⟨t, ht, rfl⟩
    exact Or.inr ⟨d, (Polyline.range_toPath (P.arc d)) ▸ Set.mem_range_self t⟩
  have hinter :
      Set.range (edgeSubarc γ a b hab.le) ∩ Set.range q = {γ a, γ b} := by
    ext z
    constructor
    · rintro ⟨hzarc, hzq⟩
      have hzimage : z ∈ P.image := hedge hzarc
      have hzends : z ∈ ({γ b, γ a} : Set ℂ) := by
        rw [← hreturn]
        exact ⟨hzq, hzimage⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzends ⊢
      exact hzends.symm
    · intro hzends
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzends
      rcases hzends with hza | hzb
      · subst z
        exact ⟨⟨0, (edgeSubarc γ a b hab.le).source⟩, ⟨1, q.target⟩⟩
      · subst z
        exact ⟨⟨1, (edgeSubarc γ a b hab.le).target⟩, ⟨0, q.source⟩⟩
  exact edgeSubarc_simple_polyline_injective_return_hasWinding_bounds32
    (P.arc d) (P.arc_simple d) (P.arc_length d) a b hab q hqi hinter w n hw

/-- Helper toward Proposition 5.16: the exact winding witness supplied by
`LeftAtOn` can be retained together with the SidesExact20 bound for every
winding number on its full, possibly bent, edge subarc. -/
theorem leftAtOn_witness_with_bounded_winding
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (s : {t : unitInterval // t ∈ openParams})
    (hleft : LeftAtOn F.val (P.arc d).toPath s) :
    ∃ a b : unitInterval, ∃ (_ha : 0 < a) (_has : a < s.1)
      (_hsb : s.1 < b) (_hb : b < 1),
      ∃ q : Path ((P.arc d).toPath b) ((P.arc d).toPath a),
        Function.Injective q ∧
        (∀ t : unitInterval, t ∈ openParams → q t ∈ F.val) ∧
        (P.arc d).toPath s.1 ∈ closure
          {w : ℂ | w ∈ F.val ∧ HasWinding
            ((edgeSubarc (P.arc d).toPath a b
              (le_of_lt (lt_trans _has _hsb))).trans q) w 1} ∧
        ∀ (w : ℂ) (n : ℤ),
          HasWinding
            ((edgeSubarc (P.arc d).toPath a b
              (le_of_lt (lt_trans _has _hsb))).trans q) w n →
          -1 ≤ n ∧ n ≤ 1 := by
  rcases hleft with ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl, ?_⟩
  intro w n hw
  exact edgeSubarc_winding_bounds_of_face_return P d F a b (has.trans hsb)
    q hqi hqF w n hw














































































end DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk
