module

public import DirectedDistances.KMSW.WholePlanePastGlueData
public import DirectedDistances.KMSW.MonotoneSeamVertices

public section
namespace DirectedDistances.KMSW.WholePlanePastGlueGeometry

open DirectedDistances.PlanarMap Set WholePlanePastGlueData

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0) (monotone_family_all w0)
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "fp" => seamFun wp hp (past_finiteIncidence W H)
local notation "pos" => gluedPos W h0 hp H
local notation "arc" => gluedArc W h0 hp H




theorem runZero_arc_above (d : ℕ × Bool) {z : ℂ}
    (hz : z ∈ (arc (wholePlaneDartι W 0 d)).image) : f0 z.re ≤ z.im := by
  rw [gluedArc_runZero] at hz
  exact monotoneFamilyDrawing_above_seam w0 h0 ((And.left H) 0) (Or.inr ⟨d, hz⟩)




theorem runZero_interior_above (d : ℕ × Bool)
    (hd : ∀ k : ℤ, d.1 ≠ boundaryOuterEdge w0 h0 k) :
    (arc (wholePlaneDartι W 0 d)).interior ⊆ {z | f0 z.re < z.im} := by
  rw [gluedArc_runZero]
  exact monotoneFamilyDrawing_nonseam_interior_above_seam w0 h0 ((And.left H) 0) d hd




theorem past_interior_below (d : ℕ × Bool) (hd : ¬ kmswPastSeamEdge W d.1) :
    (arc (kmswPastDart W d)).interior ⊆ {z | z.im < f0 z.re} := by
  rw [gluedArc_past W h0 hp H d hd, (pastDrawing_arc W h0 hp H d).2]
  rintro z ⟨q, hq, rfl⟩
  have hn (k : ℤ) : d.1 ≠ boundaryOuterEdge wp hp k := by
    intro he
    apply hd
    obtain ⟨n, hn⟩ := boundaryOuterEdge_mem_finite_LL_LR wp hp k
    exact ⟨n, he ▸ List.mem_append.mpr hn⟩
  have ha := monotoneFamilyDrawing_nonseam_interior_above_seam wp hp
    (past_finiteIncidence W H) d hn q hq
  have ht := pastTransfer_height (PastDrawingTransfer.phi w0 wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)) f0 fp q
  change (pastTransfer _ f0 fp q).im < f0 (pastTransfer _ f0 fp q).re
  linarith only [ha, ht]




theorem seam_arc_graph (k : ℤ) (b : Bool) :
    (arc (wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 k, b))).image ⊆
      {z | z.im = f0 z.re} := by
  rw [gluedArc_runZero]
  intro z hz
  rw [seamFun_graph w0 h0 ((And.left H) 0)]
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  cases b with
  | true => exact hz
  | false =>
    have hr := (P0).arc_flip (boundaryOuterEdge w0 h0 k, true)
    change (P0).arc (boundaryOuterEdge w0 h0 k, false) = _ at hr
    have hi := Polyline.image_reverse_transfer ((P0).arc (boundaryOuterEdge w0 h0 k, true))
    rw [hr, hi] at hz
    exact hz




theorem past_seam_arc_graph (k : ℤ) (b : Bool) :
    (arc (kmswPastDart W (boundaryOuterEdge wp hp k, b))).image ⊆
      {z | z.im = f0 z.re} := by
  change (arc (kmswPastEdge W (boundaryOuterEdge wp hp k), !b)).image ⊆ _
  rw [kmswPastEdge_seam_match_neg W h0 hp k]
  exact seam_arc_graph W h0 hp H (-k) (!b)




theorem runZero_pos_above (v : ℕ) :
    f0 (pos (wholePlaneVertexι W 0 v)).re ≤ (pos (wholePlaneVertexι W 0 v)).im := by
  rw [gluedPos_runZero]
  exact monotoneFamilyDrawing_above_seam w0 h0 ((And.left H) 0) (Or.inl ⟨v, rfl⟩)




theorem runZero_pos_strictly_above (v : ℕ)
    (hv : ∀ k : ℤ, v ≠ boundaryVertex w0 h0 k) :
    f0 (pos (wholePlaneVertexι W 0 v)).re < (pos (wholePlaneVertexι W 0 v)).im := by
  rw [gluedPos_runZero]
  exact vertex_strictly_above_seam w0 h0 ((And.left H) 0) v hv




theorem past_pos_strictly_below (v : ℕ)
    (hv : ∀ k : ℤ, v ≠ boundaryVertex wp hp k) :
    (pos (kmswPastVertex W v)).im < f0 (pos (kmswPastVertex W v)).re := by
  rw [gluedPos_past]
  have ha := vertex_strictly_above_seam wp hp (past_finiteIncidence W H) v hv
  have ht := pastTransfer_height (PastDrawingTransfer.phi w0 wp h0 hp
    ((And.left H) 0) (past_finiteIncidence W H)) f0 fp ((Pp).pos v)
  change (pastTransfer _ f0 fp ((Pp).pos v)).im <
    f0 (pastTransfer _ f0 fp ((Pp).pos v)).re
  linarith only [ha, ht]




theorem seam_pos_graph (k : ℤ) :
    (pos (wholePlaneVertexι W 0 (boundaryVertex w0 h0 k))).im =
      f0 (pos (wholePlaneVertexι W 0 (boundaryVertex w0 h0 k))).re := by
  rw [gluedPos_runZero, boundaryVertex_pos_eq w0 h0 ((And.left H) 0)]




theorem past_seam_pos_graph (k : ℤ) :
    (pos (kmswPastVertex W (boundaryVertex wp hp k))).im =
      f0 (pos (kmswPastVertex W (boundaryVertex wp hp k))).re := by
  rw [seam_vertex W h0 hp]
  exact seam_pos_graph W h0 hp H (1 - k)




theorem cross_pos_eq (u v : ℕ)
    (he : pos (wholePlaneVertexι W 0 u) = pos (kmswPastVertex W v)) :
    wholePlaneVertexι W 0 u = kmswPastVertex W v := by
  classical
  by_cases hv : ∃ k : ℤ, v = boundaryVertex wp hp k
  · obtain ⟨k, rfl⟩ := hv
    rw [seam_vertex W h0 hp k] at he ⊢
    rw [gluedPos_runZero, gluedPos_runZero] at he
    exact congrArg (wholePlaneVertexι W 0) ((P0).pos_injective he)
  · have hn : ∀ k : ℤ, v ≠ boundaryVertex wp hp k := by
      intro k hk
      exact hv ⟨k, hk⟩
    have ha := runZero_pos_above W h0 hp H u
    have hb := past_pos_strictly_below W h0 hp H v hn
    rw [he] at ha
    exact (not_lt_of_ge ha hb).elim




theorem glued_pos_injective : Function.Injective pos := by
  intro U V he
  rcases vertex_cover W U with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;>
    rcases vertex_cover W V with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [gluedPos_runZero, gluedPos_runZero] at he
    exact congrArg (wholePlaneVertexι W 0) ((P0).pos_injective he)
  · exact cross_pos_eq W h0 hp H u v he
  · exact (cross_pos_eq W h0 hp H v u he.symm).symm
  · rw [gluedPos_pastDrawing, gluedPos_pastDrawing] at he
    exact congrArg (kmswPastVertex W) ((Pt).pos_injective he)





theorem cross_interior_disjoint (d e : ℕ × Bool)
    (he : ¬ kmswPastSeamEdge W e.1) :
    Disjoint (arc (wholePlaneDartι W 0 d)).interior
      (arc (kmswPastDart W e)).interior := by
  apply disjoint_left.mpr
  intro z hz hz'
  have ha := runZero_arc_above W h0 hp H d hz.1
  have hb := past_interior_below W h0 hp H e he hz'
  exact not_lt_of_ge ha hb





theorem glued_interior_disjoint (D E : WholePlaneDart W)
    (hne : E ≠ D) (hflip : E ≠ wholePlaneDartFlip W D) :
    Disjoint (arc D).interior (arc E).interior := by
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩ <;>
    rcases dart_cover_off_seam W h0 E with ⟨e, rfl⟩ | ⟨e, he, rfl⟩
  · rw [gluedArc_runZero, gluedArc_runZero]
    apply (P0).interior_disjoint d e
    · intro h
      exact hne (congrArg (wholePlaneDartι W 0) h)
    · intro h
      apply hflip
      exact congrArg (wholePlaneDartι W 0) h
  · exact cross_interior_disjoint W h0 hp H d e he
  · exact (cross_interior_disjoint W h0 hp H e d hd).symm
  · rw [gluedArc_past W h0 hp H d hd, gluedArc_past W h0 hp H e he]
    apply (Pt).interior_disjoint d e
    · intro h
      exact hne (congrArg (kmswPastDart W) h)
    · intro h
      apply hflip
      rw [pastDart_flip]
      exact congrArg (kmswPastDart W) h





theorem past_interior_avoids_runZero (d : ℕ × Bool)
    (hd : ¬ kmswPastSeamEdge W d.1) (v : ℕ) :
    pos (wholePlaneVertexι W 0 v) ∉ (arc (kmswPastDart W d)).interior := by
  intro hv
  exact not_lt_of_ge (runZero_pos_above W h0 hp H v)
    (past_interior_below W h0 hp H d hd hv)





theorem runZero_interior_avoids_past (d : ℕ × Bool) (v : ℕ) :
    pos (kmswPastVertex W v) ∉ (arc (wholePlaneDartι W 0 d)).interior := by
  classical
  by_cases hv : ∃ k : ℤ, v = boundaryVertex wp hp k
  · obtain ⟨k, rfl⟩ := hv
    rw [seam_vertex W h0 hp, gluedPos_runZero, gluedArc_runZero]
    exact (P0).interior_avoids_vertices d _
  · intro hz
    have hn : ∀ k : ℤ, v ≠ boundaryVertex wp hp k := by
      intro k hk
      exact hv ⟨k, hk⟩
    exact not_lt_of_ge (runZero_arc_above W h0 hp H d hz.1)
      (past_pos_strictly_below W h0 hp H v hn)





theorem glued_interior_avoids_vertices (D : WholePlaneDart W) (V : WholePlaneVertex W) :
    pos V ∉ (arc D).interior := by
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩ <;>
    rcases vertex_cover W V with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · rw [gluedArc_runZero, gluedPos_runZero]
    exact (P0).interior_avoids_vertices d v
  · exact runZero_interior_avoids_past W h0 hp H d v
  · exact past_interior_avoids_runZero W h0 hp H d hd v
  · rw [gluedArc_past W h0 hp H d hd, gluedPos_pastDrawing]
    exact (Pt).interior_avoids_vertices d v





theorem glued_locally_finite (K : Set ℂ) (hK : Bornology.IsBounded K) :
    {D | (K ∩ (arc D).image).Nonempty}.Finite := by
  have h0f := ((P0).locally_finite K hK).image (wholePlaneDartι W 0)
  have hpf := ((Pt).locally_finite K hK).image (kmswPastDart W)
  apply (h0f.union hpf).subset
  intro D hD
  change (K ∩ (arc D).image).Nonempty at hD
  rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
  · apply Or.inl
    apply mem_image_of_mem
    rwa [gluedArc_runZero] at hD
  · apply Or.inr
    apply mem_image_of_mem
    rwa [gluedArc_past W h0 hp H d hd] at hD


end
end DirectedDistances.KMSW.WholePlanePastGlueGeometry
