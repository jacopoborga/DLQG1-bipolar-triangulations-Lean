/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization5
public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteStageExterior2

/-! # Original face boundaries in the glued whole-plane drawing

The canonical patch comparisons preserve every vertex of each cap closure,
including the exclusion of vertices allocated outside the finite patch.
No StageGeom certificate or geometric ball isomorphism is assumed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open WholePlanePastGlueData Set unitInterval

private theorem vertex_on_transferred_image
    {D V D' V' : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
    (P : PLDrawing D V flip rot vert) (G : PLDrawing D' V' flip' rot' vert')
    (h : ℂ ≃ₜ ℂ) (f : V → V')
    (hpos : ∀ a, h (P.pos a) = G.pos (f a))
    (harc : ∀ d, ∃ d', (G.arc d').image = h '' (P.arc d).image ∧
      (G.arc d').start = h ((P.arc d).start) ∧
      (G.arc d').finish = h ((P.arc d).finish))
    (v : V') (hv : G.pos v ∈ h '' P.image) : ∃ a, f a = v := by
  obtain ⟨z, hz, hzv⟩ := hv
  rcases hz with ⟨a, rfl⟩ | ⟨d, hd⟩
  · exact ⟨a, G.pos_injective ((hpos a).symm.trans hzv)⟩
  · obtain ⟨d', him, hstart, hfinish⟩ := harc d
    have hm : G.pos v ∈ (G.arc d').image := by
      rw [him]
      exact ⟨z, hd, hzv⟩
    have hend : G.pos v = (G.arc d').start ∨ G.pos v = (G.arc d').finish := by
      by_contra hn
      exact G.interior_avoids_vertices d' v
        ⟨hm, by simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    rcases hend with hs | ht
    · refine ⟨vert d, G.pos_injective ?_⟩
      rw [← hpos, ← P.arc_start, ← hstart]
      exact hs.symm
    · refine ⟨vert (flip d), G.pos_injective ?_⟩
      rw [← hpos, ← P.arc_finish, ← hfinish]
      exact ht.symm

private theorem transferred_face_boundary_vertices
    {D V D' V' : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
    (P : PLDrawing D V flip rot vert) (G : PLDrawing D' V' flip' rot' vert')
    (hvert : Function.Surjective vert) (h : ℂ ≃ₜ ℂ) (f : V → V')
    (hpos : ∀ a, h (P.pos a) = G.pos (f a))
    (harc : ∀ d, ∃ d', (G.arc d').image = h '' (P.arc d).image ∧
      (G.arc d').start = h ((P.arc d).start) ∧
      (G.arc d').finish = h ((P.arc d).finish))
    (F : P.Face) (F' : G.Face) (hF : h '' F.val = F'.val) (v : V') :
    G.pos v ∈ closure F'.val ↔ ∃ a, f a = v ∧ P.pos a ∈ closure F.val := by
  have hcl : h '' closure F.val = closure F'.val := by rw [h.image_closure, hF]
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := hcl.symm ▸ hv
    have hznot : z ∉ F.val := by
      intro hzF
      have hvF : G.pos v ∈ F'.val := by rw [← hF]; exact ⟨z, hzF, hzv⟩
      exact G.face_subset_compl F' hvF (Or.inl ⟨v, rfl⟩)
    have hzfront : z ∈ frontier F.val := by
      rw [frontier, (P.face_open_frontier_subset_image hvert F).1.interior_eq]
      exact ⟨hz, hznot⟩
    have hzimage := (P.face_open_frontier_subset_image hvert F).2 hzfront
    obtain ⟨a, ha⟩ := vertex_on_transferred_image P G h f hpos harc v ⟨z, hzimage, hzv⟩
    refine ⟨a, ha, ?_⟩
    have hza : z = P.pos a := h.injective (hzv.trans (ha ▸ (hpos a).symm))
    exact hza ▸ hz
  · rintro ⟨a, rfl, ha⟩
    rw [← hcl]
    exact ⟨P.pos a, ha, hpos a⟩

/-- Helper toward Proposition 3.9: every bounded original face of a
canonical finite drawing is one of its recorded caps. No convex StageGeom
certificate is used. -/
theorem uibotCanonicalStage_boundedFace_is_cap (w : ℕ → Fin 3) (n : ℕ)
    (F : (familyQ w (monotone_family_all w) n).Face)
    (hF : ¬ (familyQ w (monotone_family_all w) n).IsUnbounded F) :
    ∃ i : Fin (kmswStage w n).triangles.length,
      F.val = ((familyG w (monotone_family_all w) n).cap i).region := by
  let P := familyQ w (monotone_family_all w) n
  let C := familyG w (monotone_family_all w) n
  obtain ⟨hcaps, U, hU, hu, _, _⟩ := C.face_partition
  obtain ⟨z, hz, hzF⟩ := F.property
  have hzmem : z ∈ F.val := hzF.symm ▸ mem_connectedComponentIn hz
  have hzK : z ∈ closedGraphRegion C.xmin C.xmax C.lower C.upper := by
    by_contra hn
    have hzU : z ∈ U.val := hU.symm ▸ hn
    have he : F = U := P.faces_eq_of_mem hzmem hzU
    exact hF (he.symm ▸ hu)
  rw [← C.cover] at hzK
  rcases hzK with hi | hc
  · exact (hz hi).elim
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    obtain ⟨Fi, hFi⟩ := hcaps i
    have hicl : z ∈ closure Fi.val := hFi.symm ▸ hi
    have himem : z ∈ Fi.val := by
      rw [closure_eq_self_union_frontier] at hicl
      rcases hicl with hi | hi
      · exact hi
      · exact (hz ((P.face_open_frontier_subset_image
          (kmswStageDrawing_vertex_surjective w n) Fi).2 hi)).elim
    exact ⟨i, congrArg Subtype.val (P.faces_eq_of_mem hzmem himem) |>.trans hFi⟩

private theorem finiteDart_limitVertex (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    kmswLimitDartVertex w (d.1.val, d.2) = (stageVertex w n d).val := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp [kmswLimitDartVertex, stageVertex, stageEndpoint, hb, hw, he]

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
local notation "Qf" => familyQ (shiftedStream W 0) (monotone_family_all (shiftedStream W 0))
local notation "Qp" => familyQ (kmswPastCode W) (monotone_family_all (kmswPastCode W))
local notation "T" => PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W)
  h0 hpast ((And.left H) 0) (past_finiteIncidence W H)

/-- Helper toward Proposition 3.9: a canonical future cap has the same
original open face after gluing, and its whole-plane boundary vertices are
exactly the images of its finite-stage boundary vertices. -/
theorem uibotGlued_futureStage_cap_boundary (n : ℕ)
    (i : Fin (kmswStage (shiftedStream W 0) n).triangles.length) :
    ∃ F : (Qf n).Face, ∃ F' : (G).Face,
      F.val = ((familyG _ (monotone_family_all _) n).cap i).region ∧
      F'.val = F.val ∧
      ∀ v : WholePlaneVertex W, (G).pos v ∈ closure F'.val ↔
        ∃ a : Fin (kmswStage (shiftedStream W 0) n).nextVertex,
          wholePlaneVertexι W 0 a.val = v ∧ (Qf n).pos a ∈ closure F.val := by
  obtain ⟨F, F', hF, hmap⟩ := uibotGlued_futureStage_cap_face W h0 hpast H n i
  refine ⟨F, F', hF, hmap, ?_⟩
  intro v
  apply transferred_face_boundary_vertices (Qf n) (G)
    (kmswStageDrawing_vertex_surjective _ _) (Homeomorph.refl ℂ)
    (fun a => wholePlaneVertexι W 0 a.val)
  · intro a
    exact (uibotGlued_futureStage_pos W h0 hpast H n a).symm
  · intro d
    refine ⟨wholePlaneDartι W 0 (d.1.val, d.2), ?_, ?_, ?_⟩
    · rw [uibotGlued_futureStage_arc]
      simp only [Homeomorph.refl_apply, image_id]
    · rw [uibotGlued_futureStage_arc]
      rfl
    · rw [uibotGlued_futureStage_arc]
      rfl
  · simpa only [Homeomorph.refl_apply, image_id] using hmap.symm

/-- Helper toward Proposition 3.9: a canonical past cap and its actual
transferred face have exactly corresponding boundary vertices, including
all vertices on seam arcs and excluding all other whole-plane vertices. -/
theorem uibotGlued_pastStage_cap_boundary (n : ℕ)
    (i : Fin (kmswStage (kmswPastCode W) n).triangles.length) :
    ∃ F : (Qp n).Face, ∃ F' : (G).Face,
      F.val = ((familyG _ (monotone_family_all _) n).cap i).region ∧
      F'.val = T '' F.val ∧
      ∀ v : WholePlaneVertex W, (G).pos v ∈ closure F'.val ↔
        ∃ a : Fin (kmswStage (kmswPastCode W) n).nextVertex,
          kmswPastVertex W a.val = v ∧ (Qp n).pos a ∈ closure F.val := by
  obtain ⟨F, F', hF, hmap⟩ := uibotGlued_pastStage_cap_face W h0 hpast H n i
  refine ⟨F, F', hF, hmap, ?_⟩
  intro v
  apply transferred_face_boundary_vertices (Qp n) (G)
    (kmswStageDrawing_vertex_surjective _ _) T (fun a => kmswPastVertex W a.val)
  · intro a
    exact (uibotGlued_pastStage_pos W h0 hpast H n a).symm
  · intro d
    refine ⟨kmswPastDart W (d.1.val, d.2),
      uibotGlued_pastStage_arc_image_all W h0 hpast H n d, ?_, ?_⟩
    · rw [(G).arc_start, pastDart_vertex, finiteDart_limitVertex,
        uibotGlued_pastStage_pos, (Qp n).arc_start]
    · rw [(G).arc_finish, pastDart_flip, (Qp n).arc_finish]
      change (G).pos (wholePlaneDartVertex W (kmswPastDart W (d.1.val, !d.2))) = _
      rw [pastDart_vertex]
      have he := finiteDart_limitVertex (kmswPastCode W) n (edgeFlip _ d)
      change kmswLimitDartVertex _ (d.1.val, !d.2) = _ at he
      rw [he, uibotGlued_pastStage_pos]
  · exact hmap.symm

/-- Helper toward Proposition 3.9: every bounded original future-stage
face survives gluing with exactly its finite-stage boundary vertices. -/
theorem uibotGlued_futureStage_boundedFace_boundary (n : ℕ)
    (F : (Qf n).Face) (hF : ¬ (Qf n).IsUnbounded F) :
    ∃ F' : (G).Face, F'.val = F.val ∧
      ∀ v : WholePlaneVertex W, (G).pos v ∈ closure F'.val ↔
        ∃ a : Fin (kmswStage (shiftedStream W 0) n).nextVertex,
          wholePlaneVertexι W 0 a.val = v ∧ (Qf n).pos a ∈ closure F.val := by
  obtain ⟨i, hi⟩ := uibotCanonicalStage_boundedFace_is_cap _ n F hF
  obtain ⟨F₀, F', hF₀, hmap, hbd⟩ := uibotGlued_futureStage_cap_boundary W h0 hpast H n i
  have he : F₀ = F := Subtype.ext (hF₀.trans hi.symm)
  exact he ▸ ⟨F', hmap, hbd⟩

/-- Helper toward Proposition 3.9: every bounded original past-stage
face survives the transfer, with a complete correspondence of its boundary
vertices, including those on the glued seam. -/
theorem uibotGlued_pastStage_boundedFace_boundary (n : ℕ)
    (F : (Qp n).Face) (hF : ¬ (Qp n).IsUnbounded F) :
    ∃ F' : (G).Face, F'.val = T '' F.val ∧
      ∀ v : WholePlaneVertex W, (G).pos v ∈ closure F'.val ↔
        ∃ a : Fin (kmswStage (kmswPastCode W) n).nextVertex,
          kmswPastVertex W a.val = v ∧ (Qp n).pos a ∈ closure F.val := by
  obtain ⟨i, hi⟩ := uibotCanonicalStage_boundedFace_is_cap _ n F hF
  obtain ⟨F₀, F', hF₀, hmap, hbd⟩ := uibotGlued_pastStage_cap_boundary W h0 hpast H n i
  have he : F₀ = F := Subtype.ext (hF₀.trans hi.symm)
  exact he ▸ ⟨F', hmap, hbd⟩

/-- Helper toward Proposition 3.9: every original glued face is an
actual cap of a finite canonical future or past stage, with the same open
component set and the actual past transfer. -/
theorem uibotGlued_face_finitePatch (F : (G).Face) :
    (∃ n, ∃ i : Fin (kmswStage (shiftedStream W 0) n).triangles.length,
      F.val = ((familyG _ (monotone_family_all _) n).cap i).region) ∨
    (∃ n, ∃ i : Fin (kmswStage (kmswPastCode W) n).triangles.length,
      F.val = T '' ((familyG _ (monotone_family_all _) n).cap i).region) := by
  rcases WholePlanePastGlueDrawing.glueDrawing_faces W h0 hpast H F with
    ⟨F0, hb, he⟩ | ⟨Fp, hb, he⟩
  · obtain ⟨j, rfl⟩ := (boundedFace_iff_creation_orbit
      (shiftedStream W 0) (H.1 0) h0 F0).mp hb
    exact Or.inl ⟨j.val + 1, _, he.trans (capFace_spec _ _ j).1⟩
  · obtain ⟨j, rfl⟩ := (boundedFace_iff_creation_orbit
      (kmswPastCode W) (past_finiteIncidence W H) hpast Fp).mp hb
    exact Or.inr ⟨j.val + 1, _, he.trans
      (congrArg (fun s : Set ℂ => T '' s) (capFace_spec _ _ j).1)⟩

end DirectedDistances.PaperProofs.Section3
end
