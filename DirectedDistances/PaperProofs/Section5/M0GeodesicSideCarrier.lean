module

public import DirectedDistances.PaperProofs.Section5.GeoInftyIdentified
public import DirectedDistances.KMSW.WholePlanePastGlueDrawing
public import DirectedDistances.KMSW.InfinitePathGraphRay
public import DirectedDistances.KMSW.MonotoneSeamVertices
public import DirectedDistances.PaperProofs.Section4.ThinSideCodeFidelity

/-! epigraph of the Definition 1.3 seam, and the left component is based at x_{k-1}.
All geometric carriers use run-zero IDs, including missing geometric edges.
The probabilistic identification with the independent thin-side codes is separate. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
  {k : ℤ} {longest : Bool}



@[expose] def m0GeodesicSeam
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) : ℕ × Bool :=
  (P.codePath.edge i, false)



@[expose] def m0GeodesicEdges
    (P : M0CutInfiniteGeodesic W H h hLL k longest) : Set ℕ :=
  Set.range P.codePath.edge



@[expose] def m0GeodesicVertices
    (P : M0CutInfiniteGeodesic W H h hLL k longest) : Set ℕ :=
  Set.range (fun i => (P.codePath.initial i).1.id)



@[expose] noncomputable def m0GeodesicTrace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) : Set ℂ :=
  pathTrace (WholePlanePastGlueDrawing.glueDrawing W h hp H)
    (fun i => wholePlaneDartι W 0 (m0GeodesicSeam P i))



theorem m0GeodesicSeam_mem_edges
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) :
    (m0GeodesicSeam P i).1 ∈ m0GeodesicEdges P :=
  ⟨i, rfl⟩



theorem m0Geodesic_initial_mem_vertices
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) :
    (P.codePath.initial i).1.id ∈ m0GeodesicVertices P :=
  ⟨i, rfl⟩



theorem m0Geodesic_initial_zero
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    (P.codePath.initial 0).1.id = boundaryVertex (shiftedStream W 0) h k := by
  have hz := (P.codePath.initial 0).2.eq_of_length_zero (P.codePath.prefix_length 0)
  exact congrArg PresentVertex.id hz.symm



theorem m0Geodesic_root_mem_vertices
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    boundaryVertex (shiftedStream W 0) h k ∈ m0GeodesicVertices P :=
  ⟨0, m0Geodesic_initial_zero P⟩



theorem m0GeodesicTrace_eq_runZero
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicTrace hp P =
      pathTrace (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0)))
        (m0GeodesicSeam P) := by
  unfold m0GeodesicTrace pathTrace
  congr 1
  funext i
  exact congrArg Polyline.image
    (WholePlanePastGlueData.gluedArc_runZero W h hp H (m0GeodesicSeam P i))




theorem m0GeodesicTrace_properGraphRay
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    ProperGraphRay (m0GeodesicTrace hp P)
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).pos
          (boundaryVertex (shiftedStream W 0) h k)).re := by
  rw [m0GeodesicTrace_eq_runZero]
  let hfam : ∀ n, ∃ A : StageDrawing (shiftedStream W 0) n,
      Nonempty (MonotoneStageInvariant (shiftedStream W 0) n A) := fun n =>
    ⟨monotoneLayoutDrawing (shiftedStream W 0) n
      ((monotone_family_all (shiftedStream W 0)) n).choose,
      ((monotone_family_all (shiftedStream W 0)) n).choose_spec⟩
  have hproper := infinitePresentPath_properGraphRay (H.1 0) hfam P.codePath
  have hstart := (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))).arc_start (P.codePath.edge 0, false)
  have hroot := (P.codePath.edge_outgoing_at_initial (shiftedStream W 0) 0).2.trans
    (m0Geodesic_initial_zero P)
  change ProperGraphRay
    (pathTrace (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))) (m0GeodesicSeam P))
    (((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc
        (P.codePath.edge 0, false)).start.re) at hproper
  rw [hstart] at hproper
  change ProperGraphRay _
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).pos
        (edgeWest (shiftedStream W 0) (P.codePath.edge 0))).re at hproper
  rw [hroot] at hproper
  exact hproper



theorem m0Geodesic_arc_subset_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam P i))).image ⊆
        m0GeodesicTrace hp P := by
  intro z hz
  exact Set.mem_iUnion.mpr ⟨i, hz⟩



theorem m0Geodesic_initial_pos_mem_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (i : ℕ) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (P.codePath.initial i).1.id) ∈
        m0GeodesicTrace hp P := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  have hs : (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).start =
      G.pos (wholePlaneVertexι W 0 (P.codePath.initial i).1.id) := by
    exact (G.arc_start (wholePlaneDartι W 0 (m0GeodesicSeam P i))).trans
      (congrArg G.pos ((wholePlaneDartVertex_ι W 0 (m0GeodesicSeam P i)).trans
        (congrArg (wholePlaneVertexι W 0)
          (P.codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2)))
  apply m0Geodesic_arc_subset_trace hp P i
  rw [← hs]
  exact Or.inl rfl



theorem m0Geodesic_root_pos_mem_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x k) ∈ m0GeodesicTrace hp P := by
  rw [P.startsAtCutBoundary]
  exact m0Geodesic_initial_pos_mem_trace hp P 0

/-- closed ambient region of M₀,∞ is the epigraph of the Definition 1.3 seam. -/
@[expose] noncomputable def m0GeodesicAmbientRegion
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) : Set ℂ :=
  {z | seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im}

/-- left open region means the component relative to the closed future-map region.
It includes the west exterior boundary; it need not be open in ℂ. -/
@[expose] noncomputable def m0GeodesicLeftOpen
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) : Set ℂ :=
  connectedComponentIn (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P)
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x (k - 1)))

/-- both closed sides are restricted to the ambient future-map region. -/
@[expose] noncomputable def m0GeodesicSideRegion
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) : Set ℂ :=
  match s with
  | .left => closure (m0GeodesicLeftOpen hp P) ∩ m0GeodesicAmbientRegion W H h
  | .right => m0GeodesicAmbientRegion W H h \ m0GeodesicLeftOpen hp P

/-- retained faces are contained in the corresponding open region. -/
@[expose] noncomputable def m0GeodesicSideOpenRegion
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) : Set ℂ :=
  match s with
  | .left => m0GeodesicLeftOpen hp P
  | .right => m0GeodesicAmbientRegion W H h \ closure (m0GeodesicLeftOpen hp P)

/-- side vertices, pulled back along the run-zero inclusion. -/
@[expose] noncomputable def m0GeodesicSideVertices
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) : Set ℕ :=
  {v | (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
    (wholePlaneVertexι W 0 v) ∈ m0GeodesicSideRegion hp P s}

/-- an entire geometric arc must lie in the closed side. Missing edges are included. -/
@[expose] noncomputable def m0GeodesicSideEdges
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) : Set ℕ :=
  {e | ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
    (wholePlaneDartι W 0 (e, false))).image ⊆ m0GeodesicSideRegion hp P s}

/-- the indexed exterior half-boundary starts at x_k. Left runs toward x_{k-1},
with reversed geometric darts; right runs toward x_{k+1}. The seam marking is
separate, as in `Section4.ThinSideCodeFidelity.geometricSideSubmap`. -/
@[expose] noncomputable def m0GeodesicBoundaryDart
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ)
    (s : ThinMapSide) (i : ℕ) : ℕ × Bool :=
  match s with
  | .left => (boundaryOuterEdge w h (k - 1 - (i : ℤ)), true)
  | .right => (boundaryOuterEdge w h (k + (i : ℤ)), false)

/-- the literal closed geometric side, with induced run-zero rotation, succession
of retained glued faces, and separate exterior-boundary and geodesic markings.
Presence records the run-zero directed edges, independently of geometric edges. -/
@[expose] noncomputable def m0GeodesicSide
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    GeometricSideSubmap where
  vertices := m0GeodesicSideVertices hp P s
  edges := m0GeodesicSideEdges hp P s
  west := edgeWest (shiftedStream W 0)
  east := edgeEast (shiftedStream W 0)
  present := {e | EdgePresent (shiftedStream W 0) e}
  rotation d e := ∃ n : ℕ, 0 < n ∧
    (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n] d = e ∧
      ∀ j : ℕ, 0 < j → j < n →
        ((kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∉
          m0GeodesicSideEdges hp P s
  faceNext d e :=
    (∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 d) F ∧ F.val ⊆ m0GeodesicSideOpenRegion hp P s) ∧
      kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d = e
  root := boundaryVertex (shiftedStream W 0) h k
  boundary := m0GeodesicBoundaryDart (shiftedStream W 0) h k s
  seam := m0GeodesicSeam P



theorem m0Geodesic_pos_runZero
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (v : ℕ) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos (wholePlaneVertexι W 0 v) =
      (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).pos v :=
  WholePlanePastGlueData.gluedPos_runZero W h hp H v



theorem m0Geodesic_pos_mem_ambient
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (v : ℕ) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos (wholePlaneVertexι W 0 v) ∈
      m0GeodesicAmbientRegion W H h := by
  rw [m0Geodesic_pos_runZero hp]
  exact monotoneFamilyDrawing_above_seam (shiftedStream W 0) h (H.1 0)
    (Or.inl ⟨v, rfl⟩)



theorem m0Geodesic_previous_pos_not_mem_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x (k - 1)) ∉ m0GeodesicTrace hp P := by
  obtain ⟨X, f, _, _, htrace, _⟩ := m0GeodesicTrace_properGraphRay hp P
  intro hz
  rw [htrace] at hz
  have hx := hz.1.1
  rw [(m0CutData W H h hLL).x_eq h hLL (k - 1), m0Geodesic_pos_runZero hp] at hx
  exact (not_le_of_gt (seamX_strictMono (shiftedStream W 0) h (H.1 0)
    (show k - 1 < k by omega))) hx

/-- the component basepoint belongs to the ambient region minus the trace. -/
theorem m0Geodesic_previous_pos_mem_complement
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x (k - 1)) ∈
        m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
  refine ⟨?_, m0Geodesic_previous_pos_not_mem_trace hp P⟩
  rw [(m0CutData W H h hLL).x_eq h hLL (k - 1)]
  exact m0Geodesic_pos_mem_ambient hp _



theorem m0Geodesic_previous_not_mem_vertices
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    boundaryVertex (shiftedStream W 0) h (k - 1) ∉ m0GeodesicVertices P := by
  rintro ⟨i, hi⟩
  apply m0Geodesic_previous_pos_not_mem_trace hp P
  rw [(m0CutData W H h hLL).x_eq h hLL (k - 1), ← hi]
  exact m0Geodesic_initial_pos_mem_trace hp P i



theorem m0Geodesic_previous_pos_mem_leftOpen
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x (k - 1)) ∈ m0GeodesicLeftOpen hp P :=
  mem_connectedComponentIn (m0Geodesic_previous_pos_mem_complement hp P)



theorem m0GeodesicLeftOpen_subset
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicLeftOpen hp P ⊆ m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P :=
  connectedComponentIn_subset _ _



theorem m0GeodesicSideRegion_union
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicSideRegion hp P .left ∪ m0GeodesicSideRegion hp P .right =
      m0GeodesicAmbientRegion W H h := by
  classical
  apply Set.Subset.antisymm
  · rintro z (hz | hz)
    · exact hz.2
    · exact hz.1
  · intro z hz
    by_cases hl : z ∈ m0GeodesicLeftOpen hp P
    · exact Or.inl ⟨subset_closure hl, hz⟩
    · exact Or.inr ⟨hz, hl⟩



theorem m0GeodesicSideVertices_cover
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (v : ℕ) :
    v ∈ m0GeodesicSideVertices hp P .left ∨ v ∈ m0GeodesicSideVertices hp P .right := by
  have hz := m0Geodesic_pos_mem_ambient (h := h) hp (H := H) v
  rw [← m0GeodesicSideRegion_union hp P] at hz
  exact hz



theorem m0GeodesicSideOpenRegion_disjoint
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    Disjoint (m0GeodesicSideOpenRegion hp P .left)
      (m0GeodesicSideOpenRegion hp P .right) := by
  exact Set.disjoint_left.mpr (fun _ hl hr => hr.2 (subset_closure hl))

private theorem runZero_edge_re_lt (e : ℕ) :
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).pos
        (edgeWest (shiftedStream W 0) e)).re <
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).pos
        (edgeEast (shiftedStream W 0) e)).re := by
  let w := shiftedStream W 0
  have he := kmsw_edge_allocated_by_self w e
  have hv := kmswStage_endpoints_lt_nextVertex w e e he
  have hend := edge_endpoints_eq w he
  have hpos (v : ℕ) (hv : v < (kmswStage w e).nextVertex) :
      (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)).pos v =
        layoutPos w e v :=
    monotoneLimitDrawing_pos_layout w (H.1 0) _ e v hv
  rw [← hend.1, ← hend.2, hpos _ hv.1, hpos _ hv.2]
  change (kmswStageRank w e ((kmswStage w e).west e) : ℝ) <
    (kmswStageRank w e ((kmswStage w e).east e) : ℝ)
  exact_mod_cast kmswStageRank_strict w e e he

private theorem runZero_path_re_le {a b : PresentVertex (shiftedStream W 0)}
    (p : Quiver.Path a b) :
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).pos a.id).re ≤
    ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).pos b.id).re := by
  induction p with
  | nil => exact le_rfl
  | @cons b c p e ih =>
    have he := runZero_edge_re_lt (H := H) e.val
    rw [e.property.2.1, e.property.2.2] at he
    exact ih.trans he.le




theorem m0Geodesic_previous_not_reachable (k : ℤ) :
    ¬ m0CutReachable W H (m0CutData W H h hLL).seam
      ((m0CutData W H h hLL).x k) ((m0CutData W H h hLL).x (k - 1)) := by
  intro hr
  rw [(m0CutData W H h hLL).x_eq h hLL k,
    (m0CutData W H h hLL).x_eq h hLL (k - 1)] at hr
  obtain ⟨p⟩ := (m0Cut_reachable_iff_present W H h hLL
    (m0CutData W H h hLL).seam (m0Cut_seamEdge_iff W H h hLL) _ _).mp hr
  exact (not_le_of_gt (seamX_strictMono (shiftedStream W 0) h (H.1 0)
    (show k - 1 < k by omega))) (runZero_path_re_le (H := H) p)



theorem m0Geodesic_pos_mem_trace_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (v : ℕ) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos (wholePlaneVertexι W 0 v) ∈
      m0GeodesicTrace hp P ↔ v ∈ m0GeodesicVertices P := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    have hends : G.pos (wholePlaneVertexι W 0 v) =
        (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).start ∨
      G.pos (wholePlaneVertexι W 0 v) =
        (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).finish := by
      by_contra hn
      apply G.interior_avoids_vertices (wholePlaneDartι W 0 (m0GeodesicSeam P i))
        (wholePlaneVertexι W 0 v)
      exact ⟨hi, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hn⟩
    rcases hends with hs | ht
    · have hs' := hs.trans (G.arc_start (wholePlaneDartι W 0 (m0GeodesicSeam P i)))
      have hv : v = edgeWest (shiftedStream W 0) (P.codePath.edge i) :=
        wholePlaneVertexι_injective W 0 (G.pos_injective hs')
      exact ⟨i, ((P.codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2.symm.trans
        hv.symm)⟩
    · have ht' := ht.trans (G.arc_finish (wholePlaneDartι W 0 (m0GeodesicSeam P i)))
      have hv : v = edgeEast (shiftedStream W 0) (P.codePath.edge i) :=
        wholePlaneVertexι_injective W 0 (G.pos_injective ht')
      exact ⟨i + 1, ((P.codePath.edge_incoming_at_succ (shiftedStream W 0) i).2.symm.trans
        hv.symm)⟩
  · rintro ⟨i, rfl⟩
    exact m0Geodesic_initial_pos_mem_trace hp P i

/-- the relative boundary of the chosen component lies on the geodesic trace.
This is relative closedness of connected components, with no separation axiom
or conclusion-shaped hypothesis added to the geodesic data. -/
theorem m0GeodesicLeftOpen_closure_inter_complement_subset
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    closure (m0GeodesicLeftOpen hp P) ∩
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) ⊆
        m0GeodesicLeftOpen hp P := by
  intro z hz
  have hc : IsPreconnected (insert z (m0GeodesicLeftOpen hp P)) :=
    isPreconnected_connectedComponentIn.subset_closure
      (Set.subset_insert _ _) (Set.insert_subset hz.1 subset_closure)
  have hsub : insert z (m0GeodesicLeftOpen hp P) ⊆
      m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P :=
    Set.insert_subset hz.2 (m0GeodesicLeftOpen_subset hp P)
  exact hc.subset_connectedComponentIn
    (Set.mem_insert_of_mem _ (m0Geodesic_previous_pos_mem_leftOpen hp P)) hsub
      (Set.mem_insert _ _)



theorem m0GeodesicSideRegion_inter_subset_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicSideRegion hp P .left ∩ m0GeodesicSideRegion hp P .right ⊆
      m0GeodesicTrace hp P := by
  classical
  intro z hz
  by_contra hn
  exact hz.2.2 (m0GeodesicLeftOpen_closure_inter_complement_subset hp P
    ⟨hz.1.1, hz.1.2, hn⟩)



theorem m0GeodesicSideVertices_exactly_one
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (v : ℕ)
    (hv : v ∉ m0GeodesicVertices P) :
    (v ∈ m0GeodesicSideVertices hp P .left ∧
      v ∉ m0GeodesicSideVertices hp P .right) ∨
    (v ∈ m0GeodesicSideVertices hp P .right ∧
      v ∉ m0GeodesicSideVertices hp P .left) := by
  have hnot : ¬ (v ∈ m0GeodesicSideVertices hp P .left ∧
      v ∈ m0GeodesicSideVertices hp P .right) := by
    intro hz
    exact hv ((m0Geodesic_pos_mem_trace_iff hp P v).mp
      (m0GeodesicSideRegion_inter_subset_trace hp P hz))
  rcases m0GeodesicSideVertices_cover hp P v with hl | hr
  · exact Or.inl ⟨hl, fun hr => hnot ⟨hl, hr⟩⟩
  · exact Or.inr ⟨hr, fun hl => hnot ⟨hl, hr⟩⟩



theorem m0Geodesic_arc_subset_ambient
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (e : ℕ) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).image ⊆ m0GeodesicAmbientRegion W H h := by
  rw [show (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false)) =
    (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all (shiftedStream W 0))).arc (e, false) from
    WholePlanePastGlueData.gluedArc_runZero W h hp H (e, false)]
  intro z hz
  exact monotoneFamilyDrawing_above_seam (shiftedStream W 0) h (H.1 0)
    (Or.inr ⟨(e, false), hz⟩)



theorem m0GeodesicEdges_subset_right
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicEdges P ⊆ m0GeodesicSideEdges hp P .right := by
  rintro e ⟨i, rfl⟩ z hz
  refine ⟨m0Geodesic_arc_subset_ambient hp _ hz, ?_⟩
  intro hl
  exact (m0GeodesicLeftOpen_subset hp P hl).2 (m0Geodesic_arc_subset_trace hp P i hz)



theorem m0GeodesicVertices_subset_right
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicVertices P ⊆ m0GeodesicSideVertices hp P .right := by
  intro v hv
  refine ⟨m0Geodesic_pos_mem_ambient hp _, ?_⟩
  intro hl
  exact (m0GeodesicLeftOpen_subset hp P hl).2
    ((m0Geodesic_pos_mem_trace_iff hp P v).mpr hv)

private theorem graphRay_raise_mem_component
    {S : Set ℂ} {x₀ a : ℝ} {X : WithTop ℝ} {g f : ℝ → ℝ}
    (hgraph : S = {z | z.re ∈ rayDomain x₀ X ∧ z.im = g z.re})
    (hg : ContinuousOn g (rayDomain x₀ X)) (hf : Continuous f)
    (ha : a < x₀) {z : ℂ} (hz : z ∈ S) (hzf : f z.re ≤ z.im)
    {ε : ℝ} (hε : 0 < ε) :
    (⟨z.re, z.im + ε⟩ : ℂ) ∈
      connectedComponentIn ({q : ℂ | f q.re ≤ q.im} \ S) (⟨a, f a⟩ : ℂ) := by
  have hzg := hz
  rw [hgraph] at hzg
  let b := z.re
  let roof : ℝ → ℝ := fun x => max (f x) (g (max x₀ x)) + ε
  have hab : a ≤ b := ha.le.trans hzg.1.1
  have hmap : Set.MapsTo (fun x : ℝ => max x₀ x) (Set.Icc a b) (rayDomain x₀ X) := by
    intro x hx
    exact ⟨le_max_left _ _, lt_of_le_of_lt
      (WithTop.coe_le_coe.mpr (max_le hzg.1.1 hx.2)) hzg.1.2⟩
  have hroof : ContinuousOn roof (Set.Icc a b) :=
    (continuous_max.comp_continuousOn (hf.continuousOn.prodMk
      (hg.comp (continuous_const.max continuous_id).continuousOn hmap))).add continuousOn_const
  let V : Set ℂ := (fun y : ℝ => (⟨a, y⟩ : ℂ)) '' Set.Icc (f a) (roof a)
  let T := graphOver a b roof ∪ V
  have hfa : f a ≤ roof a :=
    (le_max_left _ _).trans (le_add_of_nonneg_right hε.le)
  have hV : IsPreconnected V :=
    isPreconnected_Icc.image (fun y : ℝ => (⟨a, y⟩ : ℂ)) (by
      simp only [Complex.mk_eq_add_mul_I]
      fun_prop)
  have hT : IsPreconnected T := by
    exact IsPreconnected.union'
      ⟨⟨a, roof a⟩, ⟨le_rfl, hab, rfl⟩, ⟨roof a, ⟨hfa, le_rfl⟩, rfl⟩⟩
      (isPathConnected_graphOver hab hroof).isConnected.isPreconnected hV
  have hTS : T ⊆ {q : ℂ | f q.re ≤ q.im} \ S := by
    rintro q (hq | hq)
    · have hqroof : q.im = roof q.re := hq.2.2
      refine ⟨?_, ?_⟩
      · change f q.re ≤ q.im
        rw [hqroof]
        exact (le_max_left _ _).trans (le_add_of_nonneg_right hε.le)
      · intro hqS
        rw [hgraph] at hqS
        have hqmax : max x₀ q.re = q.re := max_eq_right hqS.1.1
        have hlt : g q.re < roof q.re := by
          dsimp [roof]
          rw [hqmax]
          exact lt_of_le_of_lt (le_max_right _ _) (lt_add_of_pos_right _ hε)
        exact (ne_of_lt hlt) (hqS.2.symm.trans hqroof)
    · obtain ⟨y, hy, rfl⟩ := hq
      refine ⟨hy.1, ?_⟩
      intro hqS
      rw [hgraph] at hqS
      exact (not_le_of_gt ha) hqS.1.1
  have hbase : (⟨a, f a⟩ : ℂ) ∈ T :=
    Or.inr ⟨f a, ⟨le_rfl, hfa⟩, rfl⟩
  apply hT.subset_connectedComponentIn hbase hTS
  apply Or.inl
  refine ⟨hab, le_rfl, ?_⟩
  change z.im + ε = max (f z.re) (g (max x₀ z.re)) + ε
  rw [max_eq_right hzg.1.1, ← hzg.2, max_eq_right hzf]



theorem m0GeodesicTrace_subset_ambient
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicTrace hp P ⊆ m0GeodesicAmbientRegion W H h := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact m0Geodesic_arc_subset_ambient hp (P.codePath.edge i) hi

/-- each point of P is a limit of points of the component based at x_{k-1}.
The proof raises a finite graph segment above P, inside the ambient epigraph. -/
theorem m0GeodesicTrace_subset_closure_leftOpen
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicTrace hp P ⊆ closure (m0GeodesicLeftOpen hp P) := by
  let f := seamFun (shiftedStream W 0) h (H.1 0)
  let a := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  have hbase : (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x (k - 1)) = (⟨a, f a⟩ : ℂ) := by
    rw [(m0CutData W H h hLL).x_eq h hLL (k - 1), m0Geodesic_pos_runZero hp]
    exact boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) (k - 1)
  obtain ⟨X, g, _, hg, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp P
  intro z hz
  let raise : ℝ → ℂ := fun ε => ⟨z.re, z.im + ε⟩
  have hc : Continuous raise := by
    dsimp [raise]
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  have hraise : raise '' Set.Ioi 0 ⊆ m0GeodesicLeftOpen hp P := by
    rintro q ⟨ε, hε, rfl⟩
    unfold m0GeodesicLeftOpen
    rw [hbase]
    exact graphRay_raise_mem_component hgraph hg
      (seamFun_continuous (shiftedStream W 0) h (H.1 0))
      (seamX_strictMono (shiftedStream W 0) h (H.1 0) (show k - 1 < k by omega))
      hz (m0GeodesicTrace_subset_ambient hp P hz) hε
  have hzero : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact le_rfl
  have hlim := image_closure_subset_closure_image hc ⟨0, hzero, rfl⟩
  have hz0 : raise 0 = z := by apply Complex.ext <;> simp [raise]
  rw [hz0] at hlim
  exact closure_mono hraise hlim



theorem m0GeodesicSideRegion_inter
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicSideRegion hp P .left ∩ m0GeodesicSideRegion hp P .right =
      m0GeodesicTrace hp P := by
  apply Set.Subset.antisymm (m0GeodesicSideRegion_inter_subset_trace hp P)
  intro z hz
  have hR := m0GeodesicTrace_subset_ambient hp P hz
  refine ⟨⟨m0GeodesicTrace_subset_closure_leftOpen hp P hz, hR⟩, hR, ?_⟩
  intro hl
  exact (m0GeodesicLeftOpen_subset hp P hl).2 hz



theorem m0GeodesicEdges_subset_both
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicEdges P ⊆ m0GeodesicSideEdges hp P .left ∩
      m0GeodesicSideEdges hp P .right := by
  rintro e ⟨i, rfl⟩
  have hs : ∀ z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (m0GeodesicSeam P i))).image,
      z ∈ m0GeodesicSideRegion hp P .left ∩ m0GeodesicSideRegion hp P .right := by
    intro z hz
    rw [m0GeodesicSideRegion_inter hp P]
    exact m0Geodesic_arc_subset_trace hp P i hz
  exact ⟨fun z hz => (hs z hz).1, fun z hz => (hs z hz).2⟩



theorem m0GeodesicSideVertices_inter
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicSideVertices hp P .left ∩ m0GeodesicSideVertices hp P .right =
      m0GeodesicVertices P := by
  ext v
  change _ ∈ m0GeodesicSideRegion hp P .left ∩ m0GeodesicSideRegion hp P .right ↔ _
  rw [m0GeodesicSideRegion_inter hp P, m0Geodesic_pos_mem_trace_iff hp P v]

private theorem m0Geodesic_preconnected_side
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {F : Set ℂ} (hF : IsPreconnected F)
    (hsub : F ⊆ m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) :
    F ⊆ m0GeodesicSideOpenRegion hp P .left ∨
      F ⊆ m0GeodesicSideOpenRegion hp P .right := by
  classical
  by_cases hl : F ⊆ m0GeodesicLeftOpen hp P
  · exact Or.inl hl
  · right
    intro z hz
    refine ⟨(hsub hz).1, ?_⟩
    intro hc
    have hzL := m0GeodesicLeftOpen_closure_inter_complement_subset hp P ⟨hc, hsub hz⟩
    have heq : connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z =
          m0GeodesicLeftOpen hp P := (connectedComponentIn_eq hzL).symm
    exact hl (heq ▸ hF.subset_connectedComponentIn hz hsub)



theorem m0GeodesicTrace_subset_drawing
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    m0GeodesicTrace hp P ⊆ (WholePlanePastGlueDrawing.glueDrawing W h hp H).image := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact Or.inr ⟨wholePlaneDartι W 0 (m0GeodesicSeam P i), hi⟩

/-- every glued face contained in the future-map region lies in exactly one of
the prescribed open regions. No face is duplicated across the seam. -/
theorem m0GeodesicFace_exactly_one
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    ∃! s : ThinMapSide, F.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨z, hz, hF⟩ := F.property
  have hconn : IsConnected F.val := by
    rw [hF]
    exact isConnected_connectedComponentIn_iff.mpr hz
  have hsub : F.val ⊆ m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
    intro q hq
    exact ⟨hFR hq, fun hqP => G.face_subset_compl F hq
      (m0GeodesicTrace_subset_drawing hp P hqP)⟩
  obtain ⟨q, hq⟩ := hconn.nonempty
  rcases m0Geodesic_preconnected_side hp P hconn.isPreconnected hsub with hl | hr
  · refine ⟨.left, hl, ?_⟩
    intro s hs
    cases s with
    | left => rfl
    | right =>
      exact False.elim
        (Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp P) (hl hq) (hs hq))
  · refine ⟨.right, hr, ?_⟩
    intro s hs
    cases s with
    | left =>
      exact False.elim
        (Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp P) (hs hq) (hr hq))
    | right => rfl



theorem m0GeodesicSide_root
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    (m0GeodesicSide hp P s).root = boundaryVertex (shiftedStream W 0) h k := rfl



theorem m0GeodesicSide_seam
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) (i : ℕ) :
    (m0GeodesicSide hp P s).seam i = m0GeodesicSeam P i := rfl



theorem m0GeodesicSide_root_mem_vertices
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    (m0GeodesicSide hp P s).root ∈ (m0GeodesicSide hp P s).vertices := by
  have hr := m0Geodesic_root_mem_vertices P
  rw [← m0GeodesicSideVertices_inter hp P] at hr
  cases s with
  | left => exact hr.1
  | right => exact hr.2

private theorem polyline_height_on_image {p : Polyline} (hp : p.XMonotone)
    {z : ℂ} (hz : z ∈ p.image) : z.im = p.heightFn z.re := by
  rcases hz with rfl | ⟨i, hi, hz⟩
  · have h := p.heightFn_point hp (show 0 < p.points.length from
      List.length_pos_iff.mpr p.nonempty)
    rw [p.point_zero_eq_start] at h
    exact h.symm
  · have hlt := p.point_re_lt hp (Nat.lt_succ_self i) hi
    have hm := (mem_segment_iff_height hlt).mp hz
    have hh := p.heightFn_linear_on_segment hp hi hm.1 hm.2.1
    exact hm.2.2.trans hh.symm

private theorem runZero_arc_graph
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (e : ℕ) :
    let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))
    p.image = graphOver p.start.re p.finish.re p.heightFn ∧ p.XMonotone := by
  let w := shiftedStream W 0
  have he := kmsw_edge_allocated_by_self w e
  have harc : (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false)) = layoutArc w e e := by
    apply (WholePlanePastGlueData.gluedArc_runZero W h hp H (e, false)).trans
    exact monotoneLimitDrawing_arc_layout w (H.1 0) _ e e he false
  dsimp only
  rw [harc]
  let p := layoutArc w e e
  have hm : p.XMonotone := layoutArc_points_pairwise w e e he
  refine ⟨?_, hm⟩
  obtain ⟨f, hf⟩ := layoutArc_image_graph w e e he
  have hg : p.image = graphOver p.start.re p.finish.re f := by
    change p.image = {z | p.start.re ≤ z.re ∧ z.re ≤ p.finish.re ∧ z.im = f z.re}
    rw [show p.start = layoutPos w e ((kmswStage w e).west e) from
      (layoutArc_endpoints w e e he).1,
      show p.finish = layoutPos w e ((kmswStage w e).east e) from
      (layoutArc_endpoints w e e he).2]
    exact hf
  ext z
  constructor
  · intro hz
    have hb : z ∈ graphOver p.start.re p.finish.re f := hg ▸ hz
    exact ⟨hb.1, hb.2.1, polyline_height_on_image hm hz⟩
  · intro hz
    have hq : (⟨z.re, f z.re⟩ : ℂ) ∈ p.image := by
      rw [hg]
      exact ⟨hz.1, hz.2.1, rfl⟩
    have hh := polyline_height_on_image hm hq
    have hqz : (⟨z.re, f z.re⟩ : ℂ) = z := Complex.ext rfl (hh.trans hz.2.2.symm)
    exact hqz ▸ hq

private theorem polyline_interior_connected_dense {p : Polyline}
    (hm : p.XMonotone) (hlen : 2 ≤ p.points.length)
    (hg : p.image = graphOver p.start.re p.finish.re p.heightFn) :
    IsPreconnected p.interior ∧ p.image ⊆ closure p.interior := by
  have hab : p.start.re < p.finish.re := by
    rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
    exact p.point_re_lt hm (by omega) (by omega)
  have hstart : graphParam p.heightFn p.start.re = p.start := by
    apply Complex.ext
    · simp [graphParam]
    · simpa [graphParam] using (polyline_height_on_image hm (Or.inl rfl)).symm
  have hfinish : graphParam p.heightFn p.finish.re = p.finish := by
    have hh := p.heightFn_point hm (show p.points.length - 1 < p.points.length by omega)
    rw [p.point_last_eq_finish] at hh
    apply Complex.ext
    · simp [graphParam]
    · simpa [graphParam] using hh
  have hi : p.interior = graphParam p.heightFn '' Set.Ioo p.start.re p.finish.re := by
    ext z
    constructor
    · rintro ⟨hz, hne⟩
      rw [hg, graphOver_eq_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ p.start.re := by
        intro heq
        exact hne (by simp [heq, hstart])
      have hxb : x ≠ p.finish.re := by
        intro heq
        exact hne (by simp [heq, hfinish])
      exact ⟨x, ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hg, graphOver_eq_image]
        exact ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
      · intro hn
        rcases hn with hn | hn
        · have heq := congrArg Complex.re hn
          simp only [graphParam, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, sub_self, add_zero] at heq
          exact (ne_of_gt hx.1) heq
        · have heq := congrArg Complex.re hn
          simp only [graphParam, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, sub_self, add_zero] at heq
          exact (ne_of_lt hx.2) heq
  have hc : Continuous (graphParam p.heightFn) := by
    unfold graphParam
    have := p.continuous_heightFn
    fun_prop
  refine ⟨?_, ?_⟩
  · rw [hi]
    exact isPreconnected_Ioo.image _ hc.continuousOn
  · rw [hg, graphOver_eq_image, hi, ← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image hc

private theorem m0Geodesic_arc_interior_avoids_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) :
    Disjoint ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior (m0GeodesicTrace hp P) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  apply Set.disjoint_left.mpr
  intro z hz hzP
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzP
  have hne (b : Bool) : wholePlaneDartι W 0 (m0GeodesicSeam P i) ≠
      wholePlaneDartι W 0 (e, b) := by
    intro hh
    exact he ⟨i, wholePlaneEdgeι_injective W 0 (congrArg Prod.fst hh)⟩
  have hnotStart : z ≠ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).start := by
    intro hh
    exact G.interior_avoids_vertices (wholePlaneDartι W 0 (e, false)) _
      ((hh.trans (G.arc_start _)) ▸ hz)
  have hnotFinish : z ≠ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).finish := by
    intro hh
    exact G.interior_avoids_vertices (wholePlaneDartι W 0 (e, false)) _
      ((hh.trans (G.arc_finish _)) ▸ hz)
  have hiz : z ∈ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).interior :=
    ⟨hi, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
      And.intro hnotStart hnotFinish⟩
  exact Set.disjoint_left.mp
    (G.interior_disjoint (wholePlaneDartι W 0 (e, false))
      (wholePlaneDartι W 0 (m0GeodesicSeam P i)) (hne false) (hne true)) hz hiz

private theorem m0Geodesic_dense_preconnected_side
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {A U : Set ℂ} (hU : IsPreconnected U)
    (hUS : U ⊆ m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P)
    (hAR : A ⊆ m0GeodesicAmbientRegion W H h) (hAU : A ⊆ closure U) :
    A ⊆ m0GeodesicSideRegion hp P .left ∨ A ⊆ m0GeodesicSideRegion hp P .right := by
  classical
  by_cases hUL : U ⊆ m0GeodesicLeftOpen hp P
  · exact Or.inl (fun _ hz => ⟨closure_mono hUL (hAU hz), hAR hz⟩)
  · right
    intro z hz
    refine ⟨hAR hz, ?_⟩
    intro hzL
    have hc : IsPreconnected (insert z U) :=
      hU.subset_closure (Set.subset_insert _ _) (Set.insert_subset (hAU hz) subset_closure)
    have hsub : insert z U ⊆ m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P :=
      Set.insert_subset (m0GeodesicLeftOpen_subset hp P hzL) hUS
    have heq : connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z =
          m0GeodesicLeftOpen hp P := (connectedComponentIn_eq hzL).symm
    have hcomp := hc.subset_connectedComponentIn (Set.mem_insert z U) hsub
    rw [heq] at hcomp
    exact hUL (fun u hu => hcomp (Set.mem_insert_of_mem z hu))

/-- every M₀,∞ geometric edge lies wholly in at least one closed side.
This includes missing edges and does not infer arc coverage from point coverage. -/
theorem m0GeodesicSideEdges_cover
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (e : ℕ) :
    e ∈ m0GeodesicSideEdges hp P .left ∨ e ∈ m0GeodesicSideEdges hp P .right := by
  classical
  by_cases he : e ∈ m0GeodesicEdges P
  · exact Or.inl (m0GeodesicEdges_subset_both hp P he).1
  · obtain ⟨hg, hm⟩ := runZero_arc_graph (h := h) (H := H) hp e
    have hlen := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc_length
      (wholePlaneDartι W 0 (e, false))
    obtain ⟨hc, hd⟩ := polyline_interior_connected_dense hm hlen hg
    exact m0Geodesic_dense_preconnected_side hp P hc
      (fun z hz => ⟨m0Geodesic_arc_subset_ambient hp e hz.1,
        fun hzP => Set.disjoint_left.mp (m0Geodesic_arc_interior_avoids_trace hp P he) hz hzP⟩)
      (m0Geodesic_arc_subset_ambient hp e) hd



theorem m0GeodesicSide_endpoints
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) (e : ℕ)
    (he : e ∈ (m0GeodesicSide hp P s).edges) :
    (m0GeodesicSide hp P s).west e ∈ (m0GeodesicSide hp P s).vertices ∧
      (m0GeodesicSide hp P s).east e ∈ (m0GeodesicSide hp P s).vertices := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let d := wholePlaneDartι W 0 (e, false)
  change (G.arc d).image ⊆ m0GeodesicSideRegion hp P s at he
  change G.pos (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) e)) ∈
      m0GeodesicSideRegion hp P s ∧
    G.pos (wholePlaneVertexι W 0 (edgeEast (shiftedStream W 0) e)) ∈
      m0GeodesicSideRegion hp P s
  have hs : (G.arc d).start = G.pos (wholePlaneVertexι W 0
      (edgeWest (shiftedStream W 0) e)) := G.arc_start d
  have ht : (G.arc d).finish = G.pos (wholePlaneVertexι W 0
      (edgeEast (shiftedStream W 0) e)) := G.arc_finish d
  have hlen := G.arc_length d
  have hfinish : (G.arc d).finish ∈ (G.arc d).image := by
    refine Or.inr ⟨(G.arc d).points.length - 2, by omega, ?_⟩
    unfold Polyline.segmentAt
    have hi : (G.arc d).points.length - 2 + 1 = (G.arc d).points.length - 1 := by omega
    rw [hi, Polyline.point_last_eq_finish]
    exact right_mem_segment ℝ _ _
  exact ⟨hs ▸ he (Or.inl rfl), ht ▸ he hfinish⟩




theorem m0GeodesicBoundaryDart_left_vertex
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) (i : ℕ) :
    kmswLimitDartVertex w (m0GeodesicBoundaryDart w h k .left i) =
      boundaryVertex w h (k - (i : ℤ)) := by
  change edgeEast w (boundaryOuterEdge w h (k - 1 - (i : ℤ))) = _
  have he := (boundaryOuterEdge_endpoints w h (k - 1 - (i : ℤ))).2.1
  simpa only [show k - 1 - (i : ℤ) + 1 = k - (i : ℤ) by omega] using he



theorem m0GeodesicBoundaryDart_right_vertex
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) (i : ℕ) :
    kmswLimitDartVertex w (m0GeodesicBoundaryDart w h k .right i) =
      boundaryVertex w h (k + (i : ℤ)) :=
  (boundaryOuterEdge_endpoints w h (k + (i : ℤ))).1

end DirectedDistances.PaperProofs.Section5

