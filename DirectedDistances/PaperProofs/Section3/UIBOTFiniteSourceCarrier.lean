/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitFinal
public import DirectedDistances.Paper.Section3.KMSW
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRotationField
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation4
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation12

/-! # Finite source carrier and actual-edge sampling

The installed, counted Theorem 3.5 is `Paper.Section3.kmsw`; its codomain is
already `KMSWMapIsoClass`, defined at `PlanarMap/KMSWMapIsoClass.lean:689–717`.
There is no second source carrier to identify by a new identity equivalence.

Below the uniform edge is an actual edge-involution orbit of a representative,
including boundary edges and parallel edges separately. The dependent sample
carrier merely chooses coordinates in each unrooted class; it does not quotient
remain with the sole coordinator. No Proposition 3.9 completion is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory
open scoped ENNReal Topology
open unitInterval

/-- Helper toward Proposition 3.9: the counted source KMSW theorem has
exactly the finite class carrier used by the UIBOT approximants. -/
theorem uibotFiniteSourceCarrier_bijective (ℓ ρ n : ℕ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n) :
    Function.Bijective (@kmswToMapIsoClass ℓ ρ n hn) :=
  DirectedDistances.Paper.Section3.kmsw ℓ ρ n hℓ hρ hn

/-- Helper toward Proposition 3.9: a finite class together with one actual
geometric edge of its chosen representative, without automorphism weighting. -/
@[expose] def UIBOTFiniteSourceEdgeSample (ℓ ρ n : ℕ) :=
  Σ q : KMSWMapIsoClass ℓ ρ n,
    CombinatorialMap.EdgeQuotient q.out.B.map.toCombinatorialMap

/-- Helper toward Proposition 3.9: Peano order identifies every index with
one actual edge, separately in each sampled unrooted class. -/
@[expose] def uibotFiniteSourceEdgeSampleEquiv (ℓ ρ n : ℕ) :
    (KMSWMapIsoClass ℓ ρ n × Fin n) ≃ UIBOTFiniteSourceEdgeSample ℓ ρ n where
  toFun p := ⟨p.1, uibotPeanoEdgeEquiv p.1.out p.2⟩
  invFun p := (p.1, (uibotPeanoEdgeEquiv p.1.out).symm p.2)
  left_inv p := by
    exact Prod.ext rfl ((uibotPeanoEdgeEquiv p.1.out).symm_apply_apply p.2)
  right_inv p := by
    rcases p with ⟨q, e⟩
    exact congrArg (Sigma.mk q) ((uibotPeanoEdgeEquiv q.out).apply_symm_apply e)

/-- Helper toward Proposition 3.9: enumerate the actual class-and-edge
samples using the proved all-edge bijection. -/
@[expose, instance_reducible] def uibotFiniteSourceEdgeSampleFintype
    (ℓ ρ n : ℕ) (hn : 1 ≤ n) : Fintype (UIBOTFiniteSourceEdgeSample ℓ ρ n) := by
  letI uibotFiniteSourceCarrierMapFintype := uibotFiniteMapFintype ℓ ρ n hn
  exact Fintype.ofEquiv (KMSWMapIsoClass ℓ ρ n × Fin n)
    (uibotFiniteSourceEdgeSampleEquiv ℓ ρ n)

section Law

variable (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
  (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))

local instance uibotFiniteSourceCarrierClassMeasurable :
    MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
local instance uibotFiniteSourceCarrierIndexMeasurable : MeasurableSpace (Fin n) := ⊤
local instance uibotFiniteSourceCarrierEdgeMeasurable :
    MeasurableSpace (UIBOTFiniteSourceEdgeSample ℓ ρ n) := ⊤
local instance uibotFiniteSourceCarrierGeomMeasurable :
    MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass

/-- Helper toward Proposition 3.9: the independent uniform map/index law
is uniform counting measure on the full product, since every map has n edges. -/
theorem uibotFiniteUniformSampleLaw_eq_uniform_product :
    letI _uibotFiniteSourceCarrierProductFintype := uibotFiniteMapFintype ℓ ρ n hn
    uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne =
      uniformCountingMeasure (KMSWMapIsoClass ℓ ρ n × Fin n) := by
  let uibotFiniteSourceCarrierProductFintype := uibotFiniteMapFintype ℓ ρ n hn
  rw [uibotFiniteUniformSampleLaw_eq]
  apply Measure.ext_of_singleton
  rintro ⟨q, j⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [uniformCountingMeasure, Fintype.card_prod, ENNReal.mul_inv]

/-- Helper toward Proposition 3.9: replacing the independent uniform index
by its actual edge gives the uniform class-and-edge sample law. -/
theorem uibotFiniteUniformSampleLaw_map_source_edge :
    letI _uibotFiniteSourceCarrierLawFintype := uibotFiniteSourceEdgeSampleFintype ℓ ρ n hn
    (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map
        (uibotFiniteSourceEdgeSampleEquiv ℓ ρ n) =
      uniformCountingMeasure (UIBOTFiniteSourceEdgeSample ℓ ρ n) := by
  let uibotFiniteSourceCarrierMapLawFintype := uibotFiniteMapFintype ℓ ρ n hn
  let uibotFiniteSourceCarrierLawFintype := uibotFiniteSourceEdgeSampleFintype ℓ ρ n hn
  rw [uibotFiniteUniformSampleLaw_eq_uniform_product]
  exact uniformCountingMeasure_map_of_bijective _
    (uibotFiniteSourceEdgeSampleEquiv ℓ ρ n).bijective

/-- Helper toward Proposition 3.9: the geometric class of an unrooted
source map rooted at an actual edge, using its unique forward Peano index. -/
@[expose] def uibotFiniteSourceEdgeGeometricClassMap :
    UIBOTFiniteSourceEdgeSample ℓ ρ n → D39GeomRootedMapClass :=
  uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne ∘
    (uibotFiniteSourceEdgeSampleEquiv ℓ ρ n).symm

/-- Helper toward Proposition 3.9: the geometric pushforward of the finite
sample equals the law of a uniform finite source class with a uniform actual
edge root. All n edges, including boundary edges, are sampled. -/
theorem uibotFiniteUniformSampleLaw_geometric_eq_source_edge :
    letI _uibotFiniteSourceCarrierGeometricFintype :=
      uibotFiniteSourceEdgeSampleFintype ℓ ρ n hn
    (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map
        (uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne) =
      (uniformCountingMeasure (UIBOTFiniteSourceEdgeSample ℓ ρ n)).map
        (uibotFiniteSourceEdgeGeometricClassMap ℓ ρ n hℓ hρ hn hne) := by
  let uibotFiniteSourceCarrierGeometricMapFintype := uibotFiniteMapFintype ℓ ρ n hn
  let uibotFiniteSourceCarrierGeometricFintype :=
    uibotFiniteSourceEdgeSampleFintype ℓ ρ n hn
  rw [← uibotFiniteUniformSampleLaw_map_source_edge ℓ ρ n hℓ hρ hn hne,
    Measure.map_map measurable_from_top (measurable_of_countable _)]
  congr 1
  funext p
  exact congrArg (uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne)
    ((uibotFiniteSourceEdgeSampleEquiv ℓ ρ n).symm_apply_apply p).symm

end Law

/-- Helper toward Proposition 3.9: every bordering dart of the geometric
left face is in the exact combinatorial face orbit, in either direction. -/
theorem uibotFiniteStage_dartBorders_leftFace_iff
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (d e : StageDart (kmswStage w m).nextEdge) :
    P.dartBorders e (kmswStageDrawing_leftFace P d) ↔
      Equiv.Perm.SameCycle ((stageRot w m).symm * edgeFlip _) d e := by
  rw [← kmswStageDrawing_leftFace_eq_iff]
  exact ⟨fun h => kmswStageDrawing_sameCycle_of_leftFace_eq P d e h.symm,
    fun h => (kmswStageDrawing_leftFace_eq_of_sameCycle P d e h).symm⟩

/-- Helper toward Proposition 3.9: the complete frontier of every finite
left face consists exactly of arcs in its combinatorial face orbit. -/
theorem uibotFiniteStage_leftFace_frontier
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (d : StageDart (kmswStage w m).nextEdge) :
    frontier (kmswStageDrawing_leftFace P d).val =
      ⋃ e, ⋃ (_ : Equiv.Perm.SameCycle ((stageRot w m).symm * edgeFlip _) d e),
        (P.arc e).image := by
  rw [P.frontier_face_eq_iUnion_dartBorders_arcs
    (kmswStageDrawing_vertex_surjective w m)]
  simp_rw [uibotFiniteStage_dartBorders_leftFace_iff]

/-- Helper toward Proposition 3.9: the stage rotation is the topological
counterclockwise successor of the full PL dart star in every stage drawing. -/
theorem uibotFiniteStage_rotation_topological_successor
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (d : StageDart (kmswStage w m).nextEdge) :
    D39TopologicalCcwSuccessor {e | stageVertex w m e = stageVertex w m d}
      (fun e t => (P.arc e).toPath t) d (stageRot w m d) :=
  plDrawing_toPath_rotation_topological_ccwSuccessor P d

/-- Helper toward Proposition 3.9: the source dart map rooted at the same
chronological edge as the finite geometric law, allowing every earlier root. -/
@[expose] def uibotFiniteChronologicalD39Map (w : ℕ → Fin 3) (m j : ℕ)
    (hj : j ≤ m) : D39RootedMap :=
  { core := (kmswStageD39RootedMap w m).core
    rootMark := .present (uibotChronologicalRootedStage w m j hj).root
      (uibotChronologicalRootedStage w m j hj).root_present
      (uibotChronologicalRootedStage w m j hj).root_tail }

/-- Helper toward Proposition 3.9: the exact geometric representative of
the finite law in the representation API's domain record. -/
@[expose] def uibotFiniteSourceDrawingDomain
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) : D39DomainRootedMapV2 :=
  let B := uibotFiniteClassDrawingRootedMap P U hU hborder j hj
  ⟨B.V, B.E, B.map, B.root, B.domain⟩

/-- Helper toward Proposition 3.9: explicit face, edge and vertex
representation of the exterior-certified drawing at every chronological root.
The fields are exposed so their exact paths and faces can be characterized. -/
@[expose] def uibotFiniteSourceDrawingBase
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) :
    D39DrawingRepresentationData (uibotFiniteChronologicalD39Map w m j hj)
      (uibotFiniteSourceDrawingDomain P U hU hborder j hj) := by
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  refine {
    vertexEquiv := kmswStageD39RootedMap_vertexEquiv w m
    positions_injective := P.pos_injective
    dartEquiv := E
    dart_tail_vertex := fun d =>
      kmswStageDrawingDartEdgeDirectionEquiv_tail_endpoint P U hU hborder d
    dart_head_vertex := fun d =>
      kmswStageDrawingDartEdgeDirectionEquiv_head_endpoint P U hU hborder d
    dart_edgeInv := fun d => kmswStageDrawingDartEdgeDirectionEquiv_edgeFlip P d
    dart_missing := fun d =>
      kmswStageDrawingDartEdgeDirectionEquiv_missing P U hU hborder d
    dart_orientation := fun d hd =>
      kmswStageDrawingDartEdgeDirectionEquiv_orientation P U hU hborder d hd
    root_mark := ?_
    faceOfDart := fun d => P.toPlaneGraphDrawingFaceEquiv.symm
      (kmswStageDrawing_leftFace P d)
    faceOrbit_iff := ?_
    face_surjective := kmswStageDrawing_leftFace_transported_surjective P
    face_left_of_dart := ?_ }
  · let d := (uibotChronologicalRootedStage w m j hj).root
    change E d = _
    rw [← uibotFiniteClassDrawing_orderedDart_eq P d]
    change (Quotient.mk P.edgeSetoid d, (Quotient.mk P.edgeSetoid d).out.2 == false) =
      (Quotient.mk P.edgeSetoid d, !(Quotient.mk P.edgeSetoid d).out.2)
    cases (Quotient.mk P.edgeSetoid d).out.2 <;> rfl
  · intro d e
    constructor
    · intro h
      apply kmswStageDrawing_sameCycle_of_leftFace_eq P d e
      exact P.toPlaneGraphDrawingFaceEquiv.symm.injective h
    · intro h
      exact congrArg P.toPlaneGraphDrawingFaceEquiv.symm
        (kmswStageDrawing_leftFace_eq_of_sameCycle P d e h)
  · intro d
    change StageDart (kmswStage w m).nextEdge at d
    change if (E d).2 then P.toPlaneGraphDrawing.SideLeftOf
        (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d)) (E d).1
      else P.toPlaneGraphDrawing.SideRightOf
        (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d)) (E d).1
    cases hbit : (E d).2 with
    | false => exact kmswStageDrawing_leftFace_reverse_sideRightOf P d hbit
    | true =>
      have hd : d = (E d).1.out := by
        have hrec := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P d
        simpa only [E, hbit, ↓reduceIte] using hrec
      intro s
      have hb : P.dartBorders (E d).1.out (kmswStageDrawing_leftFace P d) := by
        rw [← hd]
        exact (kmswStageDrawing_leftFace_eq_iff P d _).mp rfl
      apply (P.toPlaneGraphDrawing_leftAtOn_iff (E d).1
        (P.toPlaneGraphDrawingFaceEquiv.symm (kmswStageDrawing_leftFace P d)) s).mpr
      rw [Equiv.apply_symm_apply]
      exact P.dartBorders_toPath_leftAtOn
        (kmswStageDrawing_vertex_surjective w m) (E d).1.out _ hb s

/-- Helper toward Proposition 3.9: full frontier incidence for the
explicit exterior representation, including both endpoints of every edge. -/
theorem uibotFiniteSourceDrawingBase_frontier
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) :
    let M := uibotFiniteChronologicalD39Map w m j hj
    let B := uibotFiniteSourceDrawingDomain P U hU hborder j hj
    let R := uibotFiniteSourceDrawingBase P U hU hborder j hj
    ∀ d v, B.map.pos (R.vertexEquiv v) ∈ frontier (R.faceOfDart d).val ↔
      ∃ e, Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
        rootedLocallyFiniteVertexClass M.core.rot e = v := by
  dsimp only
  intro d v
  change P.pos (kmswStageD39RootedMap_vertexEquiv w m v) ∈
      frontier (kmswStageDrawing_leftFace P d).val ↔ _
  rw [P.mem_pos_frontier_iff_exists_dartBorders_endpoint
    (kmswStageDrawing_vertex_surjective w m)]
  constructor
  · rintro ⟨e, he, hv | hv⟩
    · refine ⟨e, (uibotFiniteStage_dartBorders_leftFace_iff P d e).mp he, ?_⟩
      apply (kmswStageD39RootedMap_vertexEquiv w m).injective
      exact hv
    · let e' := (stageRot w m).symm (edgeFlip _ e)
      have hstep : Equiv.Perm.SameCycle ((stageRot w m).symm * edgeFlip _) e e' :=
        ⟨1, by simp only [zpow_one, Equiv.Perm.mul_apply]; rfl⟩
      refine ⟨e', ((uibotFiniteStage_dartBorders_leftFace_iff P d e).mp he).trans hstep, ?_⟩
      apply (kmswStageD39RootedMap_vertexEquiv w m).injective
      change stageVertex w m e' = _
      have hrot : Equiv.Perm.SameCycle (stageRot w m) e' (edgeFlip _ e) :=
        ⟨1, by simp only [e', zpow_one, Equiv.apply_symm_apply]⟩
      have hend : stageVertex w m e' = stageVertex w m (edgeFlip _ e) :=
        Fin.ext ((stageRot_sameCycle_iff_endpoint_eq w m _ _).mp hrot)
      exact hend.trans hv
  · rintro ⟨e, he, hv⟩
    exact ⟨e, (uibotFiniteStage_dartBorders_leftFace_iff P d e).mpr he,
      Or.inl (congrArg (kmswStageD39RootedMap_vertexEquiv w m) hv)⟩

/-- Helper toward Proposition 3.9: the represented dart path is an
endpoint-preserving reparameterization of its exact stage PL path. -/
theorem uibotFiniteSourceDrawingBase_dartArc_reparam
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m)
    (d : StageDart (kmswStage w m).nextEdge) :
    ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧ ∀ t,
      d39DrawingDartArc (uibotFiniteSourceDrawingDomain P U hU hborder j hj)
        (uibotFiniteSourceDrawingBase P U hU hborder j hj) d t =
          (P.arc d).toPath (φ t) := by
  let E := kmswStageDrawingDartEdgeDirectionEquiv P
  have hformula (t : I) :
      d39DrawingDartArc (uibotFiniteSourceDrawingDomain P U hU hborder j hj)
        (uibotFiniteSourceDrawingBase P U hU hborder j hj) d t =
      if (E d).2 then (P.arc (E d).1.out).toPath t
      else (P.arc (E d).1.out).toPath.symm t := by
    unfold d39DrawingDartArc
    have hE : (uibotFiniteSourceDrawingBase P U hU hborder j hj).dartEquiv d = E d := rfl
    rw [hE]
    cases hbit : (E d).2 <;> rfl
  cases hbit : (E d).2
  · have hd : d = edgeFlip _ (E d).1.out := by
      have hrec := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P d
      simpa only [E, hbit, Bool.false_eq_true, ↓reduceIte] using hrec
    obtain ⟨φ, h0, h1, hφ⟩ := polyline_reverse_toPath_exists_reparam
      (P.arc (E d).1.out) (P.arc_length _) (P.arc_simple _)
    refine ⟨φ, h0, h1, ?_⟩
    intro t
    rw [hformula, hbit]
    change (P.arc (E d).1.out).toPath.symm t = (P.arc d).toPath (φ t)
    have harc : P.arc d = (P.arc (E d).1.out).reverse := by
      calc
        P.arc d = P.arc (edgeFlip _ (E d).1.out) := congrArg P.arc hd
        _ = (P.arc (E d).1.out).reverse := P.arc_flip _
    rw [harc]
    exact hφ t
  · have hd : d = (E d).1.out := by
      have hrec := kmswStageDrawingDartEdgeDirectionEquiv_reconstructs P d
      simpa only [E, hbit, ↓reduceIte] using hrec
    refine ⟨Homeomorph.refl I, rfl, rfl, ?_⟩
    intro t
    rw [hformula, hbit]
    change (P.arc (E d).1.out).toPath t = (P.arc d).toPath t
    exact congrArg (fun a => (P.arc a).toPath t) hd.symm

/-- Helper toward Proposition 3.9: topological rotation for the explicit
exterior representation follows from the full stage star and path transport. -/
theorem uibotFiniteSourceDrawingBase_rotation
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) :
    let M := uibotFiniteChronologicalD39Map w m j hj
    let B := uibotFiniteSourceDrawingDomain P U hU hborder j hj
    let R := uibotFiniteSourceDrawingBase P U hU hborder j hj
    ∀ d, D39TopologicalCcwSuccessor
      {e | rootedLocallyFiniteVertexClass M.core.rot e =
        rootedLocallyFiniteVertexClass M.core.rot d}
      (d39DrawingDartArc B R) d (M.core.rot d) := by
  dsimp only
  intro d
  have hparams := uibotFiniteSourceDrawingBase_dartArc_reparam P U hU hborder j hj
  choose φ h0 h1 hpath using hparams
  have harcs : d39DrawingDartArc
      (uibotFiniteSourceDrawingDomain P U hU hborder j hj)
      (uibotFiniteSourceDrawingBase P U hU hborder j hj) =
        fun e t => (P.arc e).toPath (φ e t) := by
    funext e t
    exact hpath e t
  have hstar : {e | rootedLocallyFiniteVertexClass (stageRot w m) e =
      rootedLocallyFiniteVertexClass (stageRot w m) d} =
        {e | stageVertex w m e = stageVertex w m d} := by
    ext e
    exact (kmswStageD39RootedMap_vertexEquiv w m).injective.eq_iff.symm
  change D39TopologicalCcwSuccessor
    {e | rootedLocallyFiniteVertexClass (stageRot w m) e =
      rootedLocallyFiniteVertexClass (stageRot w m) d} _ d (stageRot w m d)
  rw [harcs, hstar]
  exact d39TopologicalCcwSuccessor_comp_intervalHomeomorph _ _ φ h0 h1
    (uibotFiniteStage_rotation_topological_successor P d)

/-- Helper toward Proposition 3.9: the full geometric representation of
every exterior-certified finite drawing, at every chronological active root.
No `StageGeom` certificate or representation premise is required. -/
@[expose] def uibotFiniteSourceDrawingData3
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) :
    D39DrawingRepresentationData3 (uibotFiniteChronologicalD39Map w m j hj)
      (uibotFiniteSourceDrawingDomain P U hU hborder j hj) where
  toD39DrawingRepresentationData := uibotFiniteSourceDrawingBase P U hU hborder j hj
  rotation_topological_successor := uibotFiniteSourceDrawingBase_rotation P U hU hborder j hj
  vertex_frontier_incidence := uibotFiniteSourceDrawingBase_frontier P U hU hborder j hj

/-- Helper toward Proposition 3.9: the exact stronger representation
statement recorded in UIBOTPeanoStageIdentification, now as a proved corollary
of the exterior-only construction, for every admissible code and every root. -/
theorem uibotPeanoStageDrawing_representation {ℓ ρ n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ ρ n) (j : Fin n)
    (P : StageDrawing (codeExtend c) (n - 1))
    (Q : StageGeom (codeExtend c) (n - 1) P) :
    let S := uibotChronologicalRootedStage (codeExtend c) (n - 1) j.val
      (by have := j.isLt; omega)
    let M : D39RootedMap :=
      ⟨(kmswStageD39RootedMap (codeExtend c) (n - 1)).core,
        .present S.root S.root_present S.root_tail⟩
    let B : D39DomainRootedMapV2 :=
      ⟨_, _, kmswStageDrawingDirectedPlaneMap P Q,
        uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega),
        uibotFiniteStageGeometricMap_domain P Q j.val (by have := j.isLt; omega)⟩
    Nonempty (D39DrawingRepresentationData3 M B) := by
  exact ⟨uibotFiniteSourceDrawingData3 P Q.exteriorFace Q.exteriorFace_unbounded
    Q.dartBorders_iff j.val (by have := j.isLt; omega)⟩

/-- Helper toward Proposition 3.9: the marker-free directed plane map of
an actual finite source representative, retaining its entire rotation system. -/
@[expose] def uibotFiniteSourceMapCore {ℓ ρ n : ℕ}
    (R : KMSWMapRep ℓ ρ n) : D39MapCore where
  D := Fin R.dartCount
  rot := R.B.map.rot
  edgeInv := R.B.map.toCombinatorialMap.edgeInv
  edgeInv_invol := R.B.map.toCombinatorialMap.edgeInv_invol
  edgeInv_ne := R.B.map.toCombinatorialMap.edgeInv_ne
  missing := R.B.map.missing
  missing_edgeInv := R.B.map.missing_edgeInv
  tail := R.B.map.tail
  tail_iff := R.B.map.tail_iff
  tail_missing := R.B.map.tail_missing
  outer := R.B.map.outer
  missing_outer := R.B.map.missing_outer
  locallyFinite := fun _ => Set.toFinite _
  connected := R.B.planar.1
  acyclic := R.B.acyclic

/-- Helper toward Proposition 3.9: a finite source representative rooted
at its j-th forward Peano dart, with the same complete directed plane map. -/
@[expose] def uibotFiniteSourcePeanoD39Map {ℓ ρ n : ℕ}
    (R : KMSWMapRep ℓ ρ n) (j : Fin n) : D39RootedMap where
  core := uibotFiniteSourceMapCore R
  rootMark := .present (uibotPeanoRootedAt R j).root
    (uibotPeanoRootedAt R j).root_present (uibotPeanoRootedAt R j).root_tail

/-- Helper toward Proposition 3.9: the same-index Peano isomorphism is a
local topology rooted-map isomorphism, preserving the full plane rotation and ordered root. -/
@[expose] def uibotFiniteSourcePeanoD39Iso {ℓ ρ n : ℕ} (hn : 1 ≤ n)
    (q : KMSWMapIsoClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = q) (j : Fin n) :
    D39RootedMapIso (uibotFiniteSourcePeanoD39Map R j)
      (uibotFiniteChronologicalD39Map
        (codeExtend ((kmswProcedureEquiv ℓ ρ n hn).symm q)) (n - 1)
        j.val (by have := j.isLt; omega)) := by
  let iso := uibotFiniteGeometricClassPeanoIso hn q R hR j
  exact {
    toEquiv := iso.dartEquiv
    rot_comm := iso.rot_comm
    edgeInv_comm := iso.edgeFlip_comm
    missing_iff := fun d => (iso.missing_iff d).symm
    tail_iff := fun d _ => (iso.tail_iff d).symm
    root_dart_comm := iso.root_comm }

/-- Helper toward Proposition 3.9: the exact finite geometric class-law
representative fully represents every source representative of the sampled
class, including topological rotation, face orbits and full frontier incidence.
No geometric representation is assumed as a premise. -/
@[expose] def uibotFiniteGeometricClassMap_sourceRepresentation
    {ℓ ρ n : ℕ} (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (q : KMSWMapIsoClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = q) (j : Fin n) :
    let B := uibotFiniteGeometricClassRepresentative ℓ ρ n hℓ hρ hn hne (q, j)
    D39DrawingRepresentationData3 (uibotFiniteSourcePeanoD39Map R j)
      (⟨B.V, B.E, B.map, B.root, B.domain⟩ : D39DomainRootedMapV2) := by
  let c := (kmswProcedureEquiv ℓ ρ n hn).symm q
  let D := uibotFiniteClassDrawingChoice (codeExtend c) (n - 1)
  exact (uibotFiniteSourceDrawingData3 D.drawing D.exterior D.unbounded D.borders
    j.val (by have := j.isLt; omega)).transportCombinatorialData
      (uibotFiniteSourcePeanoD39Iso hn q R hR j).symm

/-- Helper toward Proposition 3.9: the finite geometric law has no missing
geometric edges, as required by the source finite triangulation carrier. -/
theorem uibotFiniteGeometricClassRepresentative_no_missing
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (p : KMSWMapIsoClass ℓ ρ n × Fin n) :
    let B := uibotFiniteGeometricClassRepresentative ℓ ρ n hℓ hρ hn hne p
    ∀ e : B.E, ¬ B.map.missing e := by
  dsimp only
  let R := p.1.out
  let data := uibotFiniteGeometricClassMap_sourceRepresentation hℓ hρ hn hne
    p.1 R (Quotient.out_eq p.1) p.2
  intro e
  obtain ⟨d, hd⟩ := data.dartEquiv.surjective (e, true)
  have hm := data.dart_missing d
  rw [hd] at hm
  exact hm.not.mpr (R.B.noMissingDarts d)

/-- Helper toward Proposition 3.9: root the finite source representative
at an actual edge using the unique forward dart of that edge. -/
@[expose] def uibotFiniteSourceEdgeD39Map {ℓ ρ n : ℕ}
    (p : UIBOTFiniteSourceEdgeSample ℓ ρ n) : D39RootedMap :=
  uibotFiniteSourcePeanoD39Map p.1.out ((uibotPeanoEdgeEquiv p.1.out).symm p.2)

/-- Helper toward Proposition 3.9: the ordered root in the source local topology map
has exactly the selected actual edge, rather than an automorphism orbit. -/
theorem uibotFiniteSourceEdgeD39Map_root {ℓ ρ n : ℕ}
    (p : UIBOTFiniteSourceEdgeSample ℓ ρ n) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid p.1.out.B.map.toCombinatorialMap.edgeInv)
      (uibotFiniteSourceEdgeD39Map p).rootMark.dart = p.2 :=
  (uibotPeanoEdgeEquiv p.1.out).apply_symm_apply p.2

/-- Helper toward Proposition 3.9: every geometric class in the actual-edge
law has a full Data3 representation of the selected finite source map and edge. -/
@[expose] def uibotFiniteSourceEdgeGeometricClassMap_representation
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (p : UIBOTFiniteSourceEdgeSample ℓ ρ n) :
    let B := uibotFiniteGeometricClassRepresentative ℓ ρ n hℓ hρ hn hne
      ((uibotFiniteSourceEdgeSampleEquiv ℓ ρ n).symm p)
    D39DrawingRepresentationData3 (uibotFiniteSourceEdgeD39Map p)
      (⟨B.V, B.E, B.map, B.root, B.domain⟩ : D39DomainRootedMapV2) :=
  uibotFiniteGeometricClassMap_sourceRepresentation hℓ hρ hn hne p.1 p.1.out
    (Quotient.out_eq p.1) ((uibotPeanoEdgeEquiv p.1.out).symm p.2)

/- The finite source carrier is the counted Theorem 3.5 codomain, not a newly
postulated geometric carrier. Its source fidelity uses the existing scoped legal-step convention
author ruling. The finite law identity has the complete scope
  (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
  (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)).
The full representative geometry has the complete scope
  {ℓ ρ n : ℕ} (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
  (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
  (q : KMSWMapIsoClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
  (hR : KMSWMapIsoClass.mk R = q) (j : Fin n).
For all these binders, `uibotFiniteGeometricClassMap_sourceRepresentation`
supplies the full Data3 record without a geometric premise. The weaker
StageGeom-conditioned open statement in UIBOTPeanoStageIdentification is
covered by the exterior-only construction and the existing equality of its
geometric map with the StageGeom map. There is no open rotation, face-orbit or
frontier field of this new representation. Choosing a representative by
Quotient.out, choosing existing exterior drawings and changing the domain
record type are representation choices; they supply no assumed theorem.

No whole-plane source realization or source-local-topology identification is
samples; it does not by itself identify the limit with the paper's UIBOT. -/

end DirectedDistances.PaperProofs.Section3
end
