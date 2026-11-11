module

public import DirectedDistances.PlanarMap.D39DrawingRepresentation2

/- # Candidate topological drawing representation for Definition 3.8

paper-completion claim.

`PlaneGraphDrawing` represents edges by continuous embedded paths. The
topological local order of a finite star is expressed here by an
orientation-preserving homeomorphism that straightens initial subarcs to
radial segments. This uses no tangent or smoothness data. The angular
`CcwSuccessor` relation is applied only after this topological straightening.

The installed face-side predicates do not by themselves distinguish the
different cyclic orders of a tree star, since both sides can lie in the same
complementary face. The exact source identification of this local-star
straightening condition, its transport under the geometric isomorphism API, -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. The topological cyclic successor relation
for a finite family of arcs from one point. An orientation-preserving plane
homeomorphism sends an initial subarc of each incidence to a radial segment;
the `CcwSuccessor` test is made on those straightened segments. -/
@[expose] def D39TopologicalCcwSuccessor {D : Type*}
    (star : Set D) (arc : D → I → ℂ) (d e : D) : Prop :=
  ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
  ∃ dir : D → ℂ,
    (∀ x ∈ star, dir x ≠ 0) ∧
    (∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y) ∧
    CcwSuccessor star dir d e ∧
    ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      H '' (arc x '' Set.Icc (0 : I) t) =
        {z : ℂ | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) * dir x}

/-- Helper toward Proposition 5.16. Reindexing the incidences of a star
preserves its topological cyclic successor relation. -/
theorem d39TopologicalCcwSuccessor_map_equiv {D E : Type*} (ι : D ≃ E)
    {star : Set D} {arc : D → I → ℂ} {d e : D}
    (h : D39TopologicalCcwSuccessor star arc d e) :
    D39TopologicalCcwSuccessor (ι '' star)
      (fun x t => arc (ι.symm x) t) (ι d) (ι e) := by
  rcases h with ⟨H, hH, dir, hdir, harg, hsucc, hstraight⟩
  refine ⟨H, hH, fun x => dir (ι.symm x), ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hdir y hy
  · intro x hx y hy hxy
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨y0, hy0, rfl⟩ := hy
    have hxy' : Complex.arg (dir x0) = Complex.arg (dir y0) := by
      simpa using hxy
    exact congrArg ι (harg x0 hx0 y0 hy0 hxy')
  · exact d39CcwSuccessor_map_equiv ι hsucc
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    simpa using hstraight x0 hx0

/-- Helper toward Proposition 5.16. A dart is drawn using its stored edge path
when its representation bit is true, and the reversed path otherwise. -/
@[expose] def d39DrawingDartArc (B : D39DomainRootedMapV2)
    (data : D39DrawingRepresentationData M B) (d : M.core.D) : I → ℂ :=
  if (data.dartEquiv d).2 then
    B.map.toPlaneMapWithMissing.arc (data.dartEquiv d).1
  else
    (B.map.toPlaneMapWithMissing.arc (data.dartEquiv d).1).symm

/-- Helper toward Proposition 5.16. A drawing representation augmented by
the topological cyclic order at every vertex and the v2 frontier/incidence
clause. -/
structure D39DrawingRepresentationData3 (M : D39RootedMap)
    (B : D39DomainRootedMapV2) extends D39DrawingRepresentationData M B where
  /-- The represented rotation is the topological cyclic order of the whole
  finite dart star, with loops and parallel edges kept as separate darts. -/
  rotation_topological_successor : ∀ d,
    D39TopologicalCcwSuccessor
      {e | rootedLocallyFiniteVertexClass M.core.rot e =
        rootedLocallyFiniteVertexClass M.core.rot d}
      (d39DrawingDartArc B toD39DrawingRepresentationData) d (M.core.rot d)
  /-- A represented face has a vertex on its frontier exactly when that
  vertex is incident to a dart in the corresponding combinatorial face orbit. -/
  vertex_frontier_incidence : ∀ d v,
    B.map.toPlaneMapWithMissing.pos
        (toD39DrawingRepresentationData.vertexEquiv v) ∈
      frontier (toD39DrawingRepresentationData.faceOfDart d).val ↔
    ∃ e,
      Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
        rootedLocallyFiniteVertexClass M.core.rot e = v

/-- Helper toward Proposition 5.16. The proposition-valued v3 candidate
representation predicate. -/
@[expose] def D39DrawingRepresents3 (M : D39RootedMap)
    (B : D39DomainRootedMapV2) : Prop :=
  Nonempty (D39DrawingRepresentationData3 M B)

/-- Helper toward Proposition 5.16. Forgetting the topological-order and
frontier/incidence data recovers the v1 candidate representation. -/
theorem D39DrawingRepresents3.toV1
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (h : D39DrawingRepresents3 M B) :
    Nonempty (D39DrawingRepresentationData M B) := by
  rcases h with ⟨data⟩
  exact ⟨data.toD39DrawingRepresentationData⟩

namespace D39DrawingRepresentationData3

variable {M N : D39RootedMap} {B : D39DomainRootedMapV2}

/-- Helper toward Proposition 5.16. Transport v3 representation data across a
combinatorial isomorphism, retaining the same geometric drawing. -/
@[expose] noncomputable def transportCombinatorialData
    (iso : D39RootedMapIso M N) (h : D39DrawingRepresentationData3 M B) :
    D39DrawingRepresentationData3 N B := by
  classical
  let hbase := h.toD39DrawingRepresentationData.transportCombinatorialData iso
  refine
    { toD39DrawingRepresentationData := hbase
      rotation_topological_successor := ?_
      vertex_frontier_incidence := ?_ }
  · intro d
    let dM := iso.toEquiv.symm d
    have hstar :
        {e | rootedLocallyFiniteVertexClass N.core.rot e =
          rootedLocallyFiniteVertexClass N.core.rot d} =
        iso.toEquiv '' {e | rootedLocallyFiniteVertexClass M.core.rot e =
          rootedLocallyFiniteVertexClass M.core.rot dM} := by
      ext e
      constructor
      · intro he
        refine ⟨iso.toEquiv.symm e, ?_, Equiv.apply_symm_apply _ _⟩
        have he' : iso.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot (iso.toEquiv.symm e)) =
            rootedLocallyFiniteVertexClass N.core.rot e := by
          change iso.vertexMap (d39VertexClass M (iso.toEquiv.symm e)) =
            d39VertexClass N e
          rw [iso.vertexMap_dart, Equiv.apply_symm_apply]
        have hd' : iso.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot dM) =
            rootedLocallyFiniteVertexClass N.core.rot d := by
          change iso.vertexMap (d39VertexClass M dM) = d39VertexClass N d
          rw [iso.vertexMap_dart]
          simp [dM]
        apply iso.vertexEquiv.injective
        rw [he', hd']
        exact he
      · rintro ⟨eM, heM, rfl⟩
        have he' := congrArg iso.vertexEquiv heM
        have heMap : iso.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot eM) =
            rootedLocallyFiniteVertexClass N.core.rot (iso.toEquiv eM) := by
          change iso.vertexMap (d39VertexClass M eM) =
            d39VertexClass N (iso.toEquiv eM)
          exact iso.vertexMap_dart eM
        have hdMap : iso.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot dM) =
            rootedLocallyFiniteVertexClass N.core.rot d := by
          change iso.vertexMap (d39VertexClass M dM) = d39VertexClass N d
          rw [iso.vertexMap_dart]
          simp [dM]
        rw [heMap, hdMap] at he'
        exact he'
    have hsucc := d39TopologicalCcwSuccessor_map_equiv iso.toEquiv
      (h.rotation_topological_successor dM)
    rw [← hstar] at hsucc
    have hpaths : d39DrawingDartArc B hbase =
        fun x => d39DrawingDartArc B h.toD39DrawingRepresentationData
          (iso.toEquiv.symm x) := by
      funext x t
      rfl
    rw [hpaths]
    simpa [dM, iso.rot_comm] using hsucc
  · intro d v
    let dM := iso.toEquiv.symm d
    change B.map.toPlaneMapWithMissing.pos (hbase.vertexEquiv v) ∈
        frontier (hbase.faceOfDart d).val ↔ _
    constructor
    · intro hfront
      have hfrontM :
          B.map.toPlaneMapWithMissing.pos
              (h.vertexEquiv (iso.vertexEquiv.symm v)) ∈
            frontier (h.faceOfDart dM).val := by
        simpa [hbase, dM, D39DrawingRepresentationData.transportCombinatorialData]
          using hfront
      obtain ⟨eM, hcycle, hvM⟩ :=
        (h.vertex_frontier_incidence dM (iso.vertexEquiv.symm v)).mp hfrontM
      refine ⟨iso.toEquiv eM, ?_, ?_⟩
      · simpa [dM] using (iso.faceSameCycle_iff dM eM).mp hcycle
      · have heMap : iso.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot eM) =
            rootedLocallyFiniteVertexClass N.core.rot (iso.toEquiv eM) := by
          change iso.vertexMap (d39VertexClass M eM) =
            d39VertexClass N (iso.toEquiv eM)
          exact iso.vertexMap_dart eM
        have hv := congrArg iso.vertexEquiv hvM
        rw [heMap] at hv
        simpa using hv
    · rintro ⟨eN, hcycle, hvN⟩
      let eM := iso.toEquiv.symm eN
      have hcycleM :
          Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) dM eM := by
        apply (iso.faceSameCycle_iff dM eM).mpr
        simpa [dM, eM, Equiv.apply_symm_apply] using hcycle
      have hvM : rootedLocallyFiniteVertexClass M.core.rot eM =
          iso.vertexEquiv.symm v := by
        apply iso.vertexEquiv.injective
        have heMap : iso.vertexEquiv
            (rootedLocallyFiniteVertexClass M.core.rot eM) =
            rootedLocallyFiniteVertexClass N.core.rot (iso.toEquiv eM) := by
          change iso.vertexMap (d39VertexClass M eM) =
            d39VertexClass N (iso.toEquiv eM)
          exact iso.vertexMap_dart eM
        rw [heMap]
        simpa only [eM, Equiv.apply_symm_apply] using hvN
      have hfrontM :=
        (h.vertex_frontier_incidence dM (iso.vertexEquiv.symm v)).mpr
          ⟨eM, hcycleM, hvM⟩
      simpa [hbase, dM, D39DrawingRepresentationData.transportCombinatorialData]
        using hfrontM

end D39DrawingRepresentationData3

/-- Helper toward Proposition 5.16. Transport the v3 candidate representation
predicate across a combinatorial rooted-map isomorphism. -/
theorem D39DrawingRepresents3.transportCombinatorial
    {M N : D39RootedMap} {B : D39DomainRootedMapV2}
    (iso : D39RootedMapIso M N) (h : D39DrawingRepresents3 M B) :
    D39DrawingRepresents3 N B := by
  rcases h with ⟨data⟩
  exact ⟨data.transportCombinatorialData iso⟩




























end DirectedDistances.PlanarMap

end
