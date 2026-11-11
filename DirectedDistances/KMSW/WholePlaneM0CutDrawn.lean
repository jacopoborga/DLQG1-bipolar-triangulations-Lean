module

public import DirectedDistances.KMSW.M0CutSeam
public import DirectedDistances.KMSW.WholePlaneM0Drawing

public section
namespace DirectedDistances.KMSW.WholePlaneM0CutDrawn

open DirectedDistances.PlanarMap Set WholePlanePastGlueData WholePlanePastGlueGeometry

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0) (monotone_family_all w0)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hp H
local notation "Upper" => Set.ofPred (fun z : ℂ => f0 (Complex.re z) < Complex.im z)
local notation "closedUpper" => Set.ofPred (fun z : ℂ => f0 (Complex.re z) ≤ Complex.im z)
local notation "Lower" => Set.ofPred (fun z : ℂ => Complex.im z < f0 (Complex.re z))

variable (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
  (wholePlaneEdgeι W 0
    (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h0 (k - 1)))))

include hLL in



theorem cut_arc_on_graph (D : WholePlaneDart W) (hD : m0CutSeamEdge W H D.1) :
    ((G).arc D).image ⊆ {z | z.im = f0 z.re} := by
  obtain ⟨e, he, heD⟩ := (m0Cut_seamEdge_iff W H h0 hLL D.1).mp hD
  obtain ⟨k, rfl⟩ := (boundaryOuterEdge_range w0 h0).symm ▸ he
  have hD' : D = wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 k, D.2) :=
    Prod.ext heD.symm rfl
  rw [hD']
  exact seam_arc_graph W h0 hp H k D.2




private theorem arc_interior_nonempty (D : WholePlaneDart W) :
    ((G).arc D).interior.Nonempty := by
  let p := (G).arc D
  let a := midpoint ℝ p.start (p.point 1)
  let b := midpoint ℝ p.start a
  have hne : p.start ≠ p.point 1 := by
    intro he
    exact (G).initial_nonzero D (sub_eq_zero.mpr he.symm)
  have ha : a ≠ p.start := fun he => hne ((midpoint_eq_left_iff ℝ).mp he)
  have hb : b ≠ p.start := by
    intro he
    exact ha ((midpoint_eq_left_iff ℝ).mp he).symm
  have hba : b ≠ a := by
    intro he
    exact ha ((midpoint_eq_right_iff ℝ).mp he).symm
  have ham : a ∈ segment ℝ p.start (p.point 1) :=
    midpoint_mem_segment p.start (p.point 1)
  have hbm : b ∈ segment ℝ p.start (p.point 1) :=
    (convex_segment p.start (p.point 1)).segment_subset
      (left_mem_segment ℝ p.start (p.point 1)) ham (midpoint_mem_segment p.start a)
  have himage {z : ℂ} (hz : z ∈ segment ℝ p.start (p.point 1)) : z ∈ p.image := by
    refine Or.inr ⟨0, ?_, ?_⟩
    · have hl := (G).arc_length D
      change 2 ≤ p.points.length at hl
      omega
    · change z ∈ segment ℝ (p.point 0) (p.point 1)
      rw [Polyline.point_zero_eq_start]
      exact hz
  by_cases haf : a = p.finish
  · refine ⟨b, himage hbm, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hb, fun he => hba (he.trans haf.symm)⟩
  · refine ⟨a, himage ham, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha, haf⟩

include hLL in



theorem on_graph_is_cut (D : WholePlaneDart W)
    (h : ((G).arc D).image ⊆ {z | z.im = f0 z.re}) : m0CutSeamEdge W H D.1 := by
  have hup : ((G).arc D).image ⊆ closedUpper := by
    intro z hz
    exact (h hz).ge
  obtain ⟨d, rfl⟩ := (WholePlaneM0Drawing.m0_dart_iff W h0 hp H D).mp hup
  by_contra hn
  have hd : ∀ k : ℤ, d.1 ≠ boundaryOuterEdge w0 h0 k := by
    intro k hk
    apply hn
    apply (m0Cut_seamEdge_iff W H h0 hLL _).mpr
    exact ⟨d.1, (boundaryOuterEdge_range w0 h0) ▸ ⟨k, hk.symm⟩, rfl⟩
  obtain ⟨z, hz⟩ := arc_interior_nonempty W h0 hp H (wholePlaneDartι W 0 d)
  have ha := runZero_interior_above W h0 hp H d hd hz
  have he := h hz.1
  change f0 z.re < z.im at ha
  exact (ne_of_lt ha) he.symm

include hLL in



theorem cut_union_eq_graph :
    {z | ∃ D : WholePlaneDart W, m0CutSeamEdge W H D.1 ∧ z ∈ ((G).arc D).image} =
      {z | z.im = f0 z.re} := by
  ext z
  constructor
  · rintro ⟨D, hD, hz⟩
    exact cut_arc_on_graph W h0 hp H hLL D hD hz
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp
      (show z ∈ ⋃ k : ℤ, ((P0).arc (futureMapBoundaryDart w0 h0 k)).image from
        (seamFun_graph w0 h0 ((And.left H) 0)) ▸ hz)
    refine ⟨wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k), ?_, ?_⟩
    · apply (m0Cut_seamEdge_iff W H h0 hLL _).mpr
      exact ⟨boundaryOuterEdge w0 h0 k,
        (boundaryOuterEdge_range w0 h0) ▸ Set.mem_range_self k, rfl⟩
    · change z ∈ (gluedArc W h0 hp H
        (wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k))).image
      rw [gluedArc_runZero]
      exact hk




private theorem closure_upper_subset : closure Upper ⊆ closedUpper := by
  apply closure_minimal
  · intro z hz
    exact (show f0 z.re < z.im from hz).le
  · exact isClosed_le ((seamFun_continuous w0 h0 ((And.left H) 0)).comp
      Complex.continuous_re) Complex.continuous_im

include hLL in





theorem left_of_cut :
    ({z | ∃ D : WholePlaneDart W,
      m0CutSeamEdge W H D.1 ∧ z ∈ ((G).arc D).image}ᶜ = Upper ∪ Lower) ∧
    Disjoint Upper Lower ∧
    (∀ V : WholePlaneVertex W, (G).pos V ∈ closure Upper →
      V ∈ Set.range (wholePlaneVertexι W 0)) ∧
    (∀ D : WholePlaneDart W, ((G).arc D).image ⊆ closure Upper →
      D ∈ Set.range (wholePlaneDartι W 0)) ∧
    (∀ F : (G).Face, F.val ⊆ closure Upper →
      ∃ F0 : (P0).Face, ¬ (P0).IsUnbounded F0 ∧ F.val = F0.val) := by
  have hcl := closure_upper_subset W h0 H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cut_union_eq_graph W h0 hp H hLL]
    ext z
    change z.im ≠ f0 z.re ↔ f0 z.re < z.im ∨ z.im < f0 z.re
    exact ne_iff_lt_or_gt.trans or_comm
  · apply disjoint_left.mpr
    intro z hu hl
    change f0 z.re < z.im at hu
    change z.im < f0 z.re at hl
    exact (not_lt_of_gt hu) hl
  · intro V hV
    exact (WholePlaneM0Drawing.m0_vertex_iff W h0 hp H V).mp (hcl hV)
  · intro D hD
    exact (WholePlaneM0Drawing.m0_dart_iff W h0 hp H D).mp (hD.trans hcl)
  · intro F hF
    apply (WholePlaneM0Drawing.m0_face_iff W h0 hp H F).mp
    rcases WholePlaneM0Drawing.face_side W h0 hp H F with hu | hl
    · exact hu
    · intro z hz
      have ha : f0 z.re ≤ z.im := hcl (hF hz)
      have hb : z.im < f0 z.re := hl hz
      exact (not_lt_of_ge ha hb).elim

end
end DirectedDistances.KMSW.WholePlaneM0CutDrawn
