module

public import DirectedDistances.PlanarMap.D39DrawingRepresentation
public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.SlopeAngularOrder

/-! Helper toward Definition 3.8. This module defines a candidate representation
makes no paper-completion claim.

The additional rotation clause uses the existing `CcwSuccessor` notion on
initial directions of oriented geometric arcs. The general `PlaneGraphDrawing`
carrier stores continuous paths and has no initial-direction API, so this file
defines an initial direction by the limit of normalized secants as the path
parameter decreases to its initial endpoint. This is a prominent fidelity
doubt: the paper's topological plane drawings need not have such tangent limits,
and an orientation-preserving homeomorphism need not preserve them. The clause
does count darts, not edge identities, so loops and repeated incidences remain
separate. The second added clause is the vertex-frontier/incidence equivalence
from the fourth clause of the Proposition 5.9 mirror-continuity package.

The relation between this limiting-direction order and Definition 3.8's
topological embedding, and geometric-isomorphism transport of that relation,
do not determine the cyclic order at a vertex of a plane tree. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

/-- Helper toward Definition 3.8. A path has initial direction `u` when its
normalized secants converge to the unit direction of `u` from the right at
parameter zero. This is a candidate analytic notion for a path's initial ray;
it is stronger than the topological arc data in the paper's general drawing
carrier. -/
@[expose] def D39PathHasInitialDirection (γ : I → ℂ) (u : ℂ) : Prop :=
  u ≠ 0 ∧
    Filter.Tendsto
      (fun t : I =>
        if γ t = γ 0 then 0 else
          (‖(γ t - γ 0)‖ : ℂ)⁻¹ * (γ t - γ 0))
      (𝓝[>] (0 : I)) (𝓝 ((‖u‖ : ℂ)⁻¹ * u))

/-- Helper toward Definition 3.8. Reindex a counterclockwise-successor witness
along a dart equivalence. -/
theorem d39CcwSuccessor_map_equiv {D E : Type*} (ι : D ≃ E)
    {star : Set D} {dir : D → ℂ} {d e : D}
    (h : CcwSuccessor star dir d e) :
    CcwSuccessor (ι '' star) (fun x => dir (ι.symm x)) (ι d) (ι e) := by
  rcases h with ⟨hfin, hd, he, hcase⟩
  refine ⟨hfin.image ι, ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩, ?_⟩
  rcases hcase with ⟨hed, hsingleton⟩ | ⟨hed, hmin⟩
  · exact Or.inl ⟨congrArg ι hed, by simp [hsingleton]⟩
  · apply Or.inr
    refine ⟨fun heq => hed (ι.injective heq), ?_⟩
    intro x hx hxne
    rcases hx with ⟨y, hy, rfl⟩
    have hyne : y ≠ d := by
      intro hEq
      apply hxne
      exact congrArg ι hEq
    simpa using hmin y hy hyne

/-- Helper toward Definition 3.8. A strengthened representation candidate
whose dart rotation agrees with the counterclockwise successor order of the
limiting initial directions of the represented geometric arcs. -/
structure D39DrawingRepresentationData2 (M : D39RootedMap)
    (B : D39DomainRootedMapV2) extends D39DrawingRepresentationData M B where
  /-- Initial direction of the represented oriented dart arc. -/
  dartInitialDirection : M.core.D → ℂ
  /-- Every represented arc has the chosen limiting initial direction. -/
  dartInitialDirection_is_path_direction : ∀ d,
    if (toD39DrawingRepresentationData.dartEquiv d).2 then
      D39PathHasInitialDirection
        (B.map.toPlaneMapWithMissing.arc
          (toD39DrawingRepresentationData.dartEquiv d).1)
        (dartInitialDirection d)
    else
      D39PathHasInitialDirection
        ((B.map.toPlaneMapWithMissing.arc
          (toD39DrawingRepresentationData.dartEquiv d).1).symm)
        (dartInitialDirection d)
  /-- Distinct dart incidences at one vertex have distinct initial arguments. -/
  dartInitialDirection_arg_injective : ∀ d e,
    rootedLocallyFiniteVertexClass M.core.rot d =
      rootedLocallyFiniteVertexClass M.core.rot e →
    Complex.arg (dartInitialDirection d) =
      Complex.arg (dartInitialDirection e) → d = e
  /-- The image of `rot d` is the counterclockwise successor of the image of
  `d` among all dart ends at that vertex. The star is a set of darts, so loops
  and repeated incidences are counted separately. -/
  rotation_counterclockwise_successor : ∀ d,
    CcwSuccessor
      {e | rootedLocallyFiniteVertexClass M.core.rot e =
        rootedLocallyFiniteVertexClass M.core.rot d}
      dartInitialDirection d (M.core.rot d)
  /-- A represented face has a vertex on its frontier exactly when that vertex
  is incident to a dart in the corresponding combinatorial face orbit. -/
  vertex_frontier_incidence : ∀ d v,
    B.map.toPlaneMapWithMissing.pos
        (toD39DrawingRepresentationData.vertexEquiv v) ∈
      frontier ((toD39DrawingRepresentationData.faceOfDart d).val) ↔
    ∃ e,
      Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
        rootedLocallyFiniteVertexClass M.core.rot e = v

namespace D39DrawingRepresentationData2

variable {M N : D39RootedMap} {B : D39DomainRootedMapV2}

/-- Helper toward Definition 3.8. Transport the strengthened representation
across a combinatorial isomorphism, retaining the same concrete drawing. -/
@[expose] noncomputable def transportCombinatorialData
    (iso : D39RootedMapIso M N) (h : D39DrawingRepresentationData2 M B) :
    D39DrawingRepresentationData2 N B := by
  classical
  let hbase := h.toD39DrawingRepresentationData.transportCombinatorialData iso
  refine
    { toD39DrawingRepresentationData := hbase
      dartInitialDirection := fun d => h.dartInitialDirection (iso.toEquiv.symm d)
      dartInitialDirection_is_path_direction := ?_
      dartInitialDirection_arg_injective := ?_
      rotation_counterclockwise_successor := ?_
      vertex_frontier_incidence := ?_ }
  · intro d
    change (if (h.dartEquiv (iso.toEquiv.symm d)).2 then
      D39PathHasInitialDirection
        (B.map.toPlaneMapWithMissing.arc (h.dartEquiv (iso.toEquiv.symm d)).1)
        (h.dartInitialDirection (iso.toEquiv.symm d))
      else D39PathHasInitialDirection
        ((B.map.toPlaneMapWithMissing.arc (h.dartEquiv (iso.toEquiv.symm d)).1).symm)
        (h.dartInitialDirection (iso.toEquiv.symm d)))
    exact h.dartInitialDirection_is_path_direction (iso.toEquiv.symm d)
  · intro d e hv harg
    have hvM : rootedLocallyFiniteVertexClass M.core.rot (iso.toEquiv.symm d) =
        rootedLocallyFiniteVertexClass M.core.rot (iso.toEquiv.symm e) := by
      apply iso.vertexEquiv.injective
      change iso.vertexMap (d39VertexClass M (iso.toEquiv.symm d)) =
        iso.vertexMap (d39VertexClass M (iso.toEquiv.symm e))
      rw [iso.vertexMap_dart, iso.vertexMap_dart]
      simpa [d39VertexClass] using hv
    simpa only [Equiv.apply_symm_apply] using congrArg iso.toEquiv
      (h.dartInitialDirection_arg_injective
        (iso.toEquiv.symm d) (iso.toEquiv.symm e) hvM harg)
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
    have hsucc := d39CcwSuccessor_map_equiv iso.toEquiv
      (h.rotation_counterclockwise_successor dM)
    rw [← hstar] at hsucc
    simpa [dM, Equiv.apply_symm_apply, iso.rot_comm] using hsucc
  · intro d v
    let dM := iso.toEquiv.symm d
    change B.map.toPlaneMapWithMissing.pos (hbase.vertexEquiv v) ∈
        frontier (hbase.faceOfDart d).val ↔ _
    constructor
    · intro hfront
      have hfrontM :
          B.map.toPlaneMapWithMissing.pos (h.vertexEquiv (iso.vertexEquiv.symm v)) ∈
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

end D39DrawingRepresentationData2

/-- Helper toward Definition 3.8. The proposition-valued candidate predicate -/
@[expose] def D39DrawingRepresents2 (M : D39RootedMap)
    (B : D39DomainRootedMapV2) : Prop :=
  Nonempty (D39DrawingRepresentationData2 M B)

/-- Helper toward Definition 3.8. Forget the additional rotation and
frontier/incidence clauses to recover the v1 candidate data. -/
@[expose] def D39DrawingRepresentationData2.toV1
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (h : D39DrawingRepresentationData2 M B) :
    D39DrawingRepresentationData M B :=
  h.toD39DrawingRepresentationData

/-- Helper toward Definition 3.8. The strengthened predicate implies the v1
candidate predicate by projection. -/
theorem D39DrawingRepresents2.toV1
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (h : D39DrawingRepresents2 M B) :
    Nonempty (D39DrawingRepresentationData M B) := by
  rcases h with ⟨data⟩
  exact Nonempty.intro data.toV1

/-- Helper toward Definition 3.8. Transport the strengthened candidate
predicate across a whole-map combinatorial isomorphism. -/
theorem D39DrawingRepresents2.transportCombinatorial
    {M N : D39RootedMap} {B : D39DomainRootedMapV2}
    (iso : D39RootedMapIso M N) (h : D39DrawingRepresents2 M B) :
    D39DrawingRepresents2 N B := by
  rcases h with ⟨data⟩
  exact ⟨data.transportCombinatorialData iso⟩

/-- Helper toward Definition 3.8. For a fixed finite dart star with distinct
initial arguments, the counterclockwise successor is unique. This gives the
local sanity check needed when comparing two rotation systems on the same
geometric incidences. -/
theorem d39CcwSuccessor_unique {D : Type*} {star : Set D} {dir : D → ℂ}
    {d e f : D}
    (harg : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (he : CcwSuccessor star dir d e)
    (hf : CcwSuccessor star dir d f) : e = f := by
  rcases he with ⟨hfin, hd, heStar, heCase⟩
  rcases hf with ⟨_, _, hfStar, hfCase⟩
  rcases heCase with ⟨heq, hsingleton⟩ | ⟨hene, hminE⟩
  · rcases hfCase with ⟨hfq, _⟩ | ⟨hfne, _⟩
    · exact heq.trans hfq.symm
    · exfalso
      exact hfne (by simpa [hsingleton] using hfStar)
  · rcases hfCase with ⟨hfq, hsingleton⟩ | ⟨hfne, hminF⟩
    · exfalso
      exact hene (by simpa [hsingleton] using heStar)
    · have hle1 := hminE f hfStar hfne
      have hle2 := hminF e heStar hene
      have hturn : ccwTurn (dir d) (dir e) = ccwTurn (dir d) (dir f) :=
        le_antisymm hle1 hle2
      have hargEq : Complex.arg (dir e) = Complex.arg (dir f) :=
        ccwTurn_left_injective hturn
      exact harg e heStar f hfStar hargEq

/-- Helper toward Definition 3.8. Two rotation permutations that are both
the counterclockwise successor on the same dart stars and direction function
must agree. In particular, two plane-tree drawings with the same identified
dart incidences and initial directions cannot represent different cyclic
orders at a vertex. -/
theorem d39Rotation_eq_of_same_geometric_successors {D : Type*}
    {rot₁ rot₂ : Equiv.Perm D} {star : D → Set D} {dir : D → ℂ}
    (harg : ∀ d x, x ∈ star d → ∀ y, y ∈ star d →
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (h₁ : ∀ d, CcwSuccessor (star d) dir d (rot₁ d))
    (h₂ : ∀ d, CcwSuccessor (star d) dir d (rot₂ d)) : rot₁ = rot₂ := by
  ext d
  exact d39CcwSuccessor_unique (harg d) (h₁ d) (h₂ d)






















end DirectedDistances.PlanarMap

end
