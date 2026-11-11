module

public import DirectedDistances.KMSW.WholePlanePastGlueGeometry
public import DirectedDistances.KMSW.MonotoneSeamRegions
public import DirectedDistances.PlanarMap.PastTransferMap
public import DirectedDistances.PlanarMap.PLDrawingFaceTransfer

public section
namespace DirectedDistances.KMSW.WholePlanePastGlueImage

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
  DirectedDistances.KMSW.WholePlanePastGlueGeometry

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




@[expose] def gluedImage : Set ℂ :=
  Set.range (gluedPos W h0 hp H) ∪
    {z | ∃ D, z ∈ (gluedArc W h0 hp H D).image}




theorem mem_gluedImage_iff (z : ℂ) :
    z ∈ gluedImage W h0 hp H ↔
      (∃ V, gluedPos W h0 hp H V = z) ∨
        ∃ D, z ∈ (gluedArc W h0 hp H D).image := Iff.rfl




theorem runZero_image_subset : (P0).image ⊆ {z | f0 z.re ≤ z.im} :=
  monotoneFamilyDrawing_above_seam w0 h0 ((And.left H) 0)




theorem past_image_subset : T '' (Pp).image ⊆ {z | z.im ≤ f0 z.re} := by
  calc
    T '' (Pp).image ⊆ T '' {q : ℂ | fp q.re ≤ q.im} :=
      image_mono (monotoneFamilyDrawing_above_seam wp hp (past_finiteIncidence W H))
    _ = {z | z.im ≤ f0 z.re} :=
      pastTransfer_image_onOrAbove (PastDrawingTransfer.phi w0 wp h0 hp
        ((And.left H) 0) (past_finiteIncidence W H)) f0 fp




theorem gluedImage_inter_upper :
    gluedImage W h0 hp H ∩ {z | f0 z.re < z.im} =
      (P0).image ∩ {z | f0 z.re < z.im} := by
  ext z
  constructor
  · rintro ⟨hz, hup⟩
    change f0 z.re < z.im at hup
    refine ⟨?_, hup⟩
    change z ∈ Set.range pos ∪ {z | ∃ D, z ∈ (arc D).image} at hz
    rcases hz with ⟨V, rfl⟩ | ⟨D, hzD⟩
    · rcases vertex_cover W V with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · rw [gluedPos_runZero] at hup
        rw [gluedPos_runZero W h0 hp H v]
        rw [PLDrawing.image]
        exact Or.inl ⟨v, rfl⟩
      · by_cases hseam : ∃ k : ℤ, v = boundaryVertex wp hp k
        · obtain ⟨k, rfl⟩ := hseam
          have hgraph := WholePlanePastGlueGeometry.past_seam_pos_graph W h0 hp H k
          rw [hgraph] at hup
          exact (lt_irrefl _ hup).elim
        · have hn : ∀ k : ℤ, v ≠ boundaryVertex wp hp k := by
            intro k hk
            exact hseam ⟨k, hk⟩
          exact (lt_asymm
            (WholePlanePastGlueGeometry.past_pos_strictly_below W h0 hp H v hn)
            hup).elim
    · rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
      · rw [gluedArc_runZero] at hzD
        change z ∈ Set.range (P0).pos ∪
          {z | ∃ d, z ∈ ((P0).arc d).image}
        exact Or.inr ⟨d, hzD⟩
      · rw [gluedArc_past W h0 hp H d hd] at hzD
        rw [(pastDrawing_arc W h0 hp H d).1] at hzD
        have harc : ((Pp).arc d).image ⊆ {q : ℂ | fp q.re ≤ q.im} := by
          intro q hq
          exact monotoneFamilyDrawing_above_seam wp hp (past_finiteIncidence W H)
            (Or.inr ⟨d, hq⟩)
        have hside : T '' ((Pp).arc d).image ⊆ {q : ℂ | q.im ≤ f0 q.re} := by
          calc
            T '' ((Pp).arc d).image ⊆ T '' {q : ℂ | fp q.re ≤ q.im} :=
              image_mono harc
            _ = {q : ℂ | q.im ≤ f0 q.re} :=
              pastTransfer_image_onOrAbove
                (PastDrawingTransfer.phi w0 wp h0 hp
                  ((And.left H) 0) (past_finiteIncidence W H)) f0 fp
        have hsidez : z.im ≤ f0 z.re := hside hzD
        exact (not_lt_of_ge hsidez hup).elim
  · rintro ⟨hz, hup⟩
    refine ⟨?_, hup⟩
    change z ∈ Set.range (P0).pos ∪ {z | ∃ d, z ∈ ((P0).arc d).image} at hz
    rcases hz with ⟨v, rfl⟩ | ⟨d, hd⟩
    · change (P0).pos v ∈ Set.range pos ∪ {z | ∃ D, z ∈ (arc D).image}
      exact Or.inl ⟨wholePlaneVertexι W 0 v,
        gluedPos_runZero W h0 hp H v⟩
    · change z ∈ Set.range pos ∪ {z | ∃ D, z ∈ (arc D).image}
      apply Or.inr
      refine ⟨wholePlaneDartι W 0 d, ?_⟩
      rw [gluedArc_runZero]
      exact hd




theorem gluedImage_inter_graph :
    gluedImage W h0 hp H ∩ {z | z.im = f0 z.re} = {z | z.im = f0 z.re} := by
  ext z
  constructor
  · exact And.right
  · intro hz
    refine ⟨?_, hz⟩
    change z ∈ Set.range pos ∪ {z | ∃ D, z ∈ (arc D).image}
    have hseam : z ∈ ⋃ k : ℤ,
        ((P0).arc (futureMapBoundaryDart w0 h0 k)).image := by
      have hgraph : z ∈ {z | z.im = f0 z.re} := hz
      rw [seamFun_graph w0 h0 ((And.left H) 0)] at hgraph
      exact hgraph
    obtain ⟨k, hk⟩ := mem_iUnion.mp hseam
    exact Or.inr ⟨wholePlaneDartι W 0 (futureMapBoundaryDart w0 h0 k), by
      rw [gluedArc_runZero]
      exact hk⟩




theorem gluedImage_inter_lower :
    gluedImage W h0 hp H ∩ {z | z.im < f0 z.re} =
      T '' (Pp).image ∩ {z | z.im < f0 z.re} := by
  classical
  ext z
  constructor
  · rintro ⟨hz, hlow⟩
    change z.im < f0 z.re at hlow
    refine ⟨?_, hlow⟩
    rcases (mem_gluedImage_iff W h0 hp H z).mp hz with ⟨V, rfl⟩ | ⟨D, hzD⟩
    · rcases vertex_cover W V with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact (not_lt_of_ge (runZero_pos_above W h0 hp H v) hlow).elim
      · rw [gluedPos_past]
        exact mem_image_of_mem T (Or.inl ⟨v, rfl⟩)
    · rcases dart_cover_off_seam W h0 D with ⟨d, rfl⟩ | ⟨d, hd, rfl⟩
      · exact (not_lt_of_ge (runZero_arc_above W h0 hp H d hzD) hlow).elim
      · rw [gluedArc_past W h0 hp H d hd, (pastDrawing_arc W h0 hp H d).1] at hzD
        obtain ⟨q, hq, rfl⟩ := hzD
        exact mem_image_of_mem T (Or.inr ⟨d, hq⟩)
  · rintro ⟨⟨q, hq, rfl⟩, hlow⟩
    refine ⟨?_, hlow⟩
    change q ∈ Set.range (Pp).pos ∪ {q | ∃ d, q ∈ ((Pp).arc d).image} at hq
    rw [mem_gluedImage_iff]
    rcases hq with ⟨v, rfl⟩ | ⟨d, hq⟩
    · exact Or.inl ⟨kmswPastVertex W v, gluedPos_past W h0 hp H v⟩
    · by_cases hs : kmswPastSeamEdge W d.1
      · rcases d with ⟨e, b⟩
        obtain ⟨k, hk⟩ := kmswPastSeamEdge_image_boundary W h0 e hs
        have he : e = boundaryOuterEdge wp hp (-k) := by
          apply kmswPastEdge_injective W
          rw [hk, kmswPastEdge_seam_match_neg W h0 hp, neg_neg]
        rw [he] at hq
        have hqgraph : q ∈ {q | q.im = fp q.re} := by
          rw [seamFun_graph wp hp (past_finiteIncidence W H)]
          apply mem_iUnion.mpr
          refine ⟨-k, ?_⟩
          cases b with
          | true => exact hq
          | false =>
            have hr := (Pp).arc_flip (boundaryOuterEdge wp hp (-k), true)
            change (Pp).arc (boundaryOuterEdge wp hp (-k), false) = _ at hr
            rw [hr, Polyline.image_reverse_transfer] at hq
            exact hq
        have htgraph : T q ∈ {z | z.im = f0 z.re} := by
          rw [← pastTransfer_image_graph (PastDrawingTransfer.phi w0 wp h0 hp
            ((And.left H) 0) (past_finiteIncidence W H)) f0 fp]
          exact ⟨q, hqgraph, rfl⟩
        exact (not_lt_of_ge (le_of_eq htgraph.symm) hlow).elim
      · apply Or.inr
        refine ⟨kmswPastDart W d, ?_⟩
        rw [gluedArc_past W h0 hp H d hs, (pastDrawing_arc W h0 hp H d).1]
        exact mem_image_of_mem T hq

end
end DirectedDistances.KMSW.WholePlanePastGlueImage
