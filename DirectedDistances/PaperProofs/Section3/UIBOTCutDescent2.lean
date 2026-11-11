/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCutDescent
public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart6
public import DirectedDistances.KMSW.KMSWMeasurability
public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso13
public import DirectedDistances.KMSW.FutureMapHatLawShift
public import DirectedDistances.PaperProofs.Section1.FutureMapFaces

/-! # Geometric invariance of the common cut marks

The deterministic transport below uses actual geometric isomorphisms, not
assumed recovery of the code. The Borel factors recover the complete run-zero
side fields and boundary labels on one shared realization event. Intrinsic
complementary-component face descent remains separate. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory Filter Set
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section1

section GeometricTransport

variable {W W' : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {H' : WholePlaneRotationHypothesis W'}
    {G : WholePlaneDrawing W H} {G' : WholePlaneDrawing W' H'}
    {hp : ∀ e, wholePlaneEdgePresent W e}
    {hp' : ∀ e, wholePlaneEdgePresent W' e}

/-- Helper toward Proposition 3.9: a geometric whole-map isomorphism acts
on raw darts with their actual west/east incidences, retaining edge identity. -/
@[expose] def uibotCutGeomDartEquiv
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G')) :
    WholePlaneDart W ≃ WholePlaneDart W' :=
  I.edgeEquiv.prodCongr (Equiv.refl Bool)

/-- Helper toward Proposition 3.9: the geometric dart transport preserves
the ambient rotation, using finite geometric enclosure of the vertex star. -/
theorem uibotCutGeomDartEquiv_rotation
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : WholePlaneDart W) :
    uibotCutGeomDartEquiv I (wholePlaneRotation W H d) =
      wholePlaneRotation W' H' (uibotCutGeomDartEquiv I d) := by
  classical
  obtain ⟨r, hr⟩ := uibotRecovery_finite_vertices_enclosed
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    (uibotWholePlaneSourceDomain W H G hp).domain {wholePlaneDartVertex W d}
  have hv := hr _ (Finset.mem_singleton_self _)
  have hd := uibotRecovery_dart_edge_mem_succ (G := G) (hp := hp) d hv
  obtain ⟨hrot, he⟩ := uibotRecovery_ballDartEquiv_rotation_interior
    (I.toBallIsoV2 (r + 1) (Nat.succ_pos r)) ⟨d, hd⟩ hv
  exact he

/-- Helper toward Proposition 3.9: the same dart transport preserves
the actual initial vertex of every dart, regardless of stored endpoint order. -/
theorem uibotCutGeomDartEquiv_vertex
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : WholePlaneDart W) :
    I.vertexEquiv (wholePlaneDartVertex W d) =
      wholePlaneDartVertex W' (uibotCutGeomDartEquiv I d) := by
  classical
  obtain ⟨r, hr⟩ := uibotRecovery_finite_vertices_enclosed
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    (uibotWholePlaneSourceDomain W H G hp).domain {wholePlaneDartVertex W d}
  have hv := hr _ (Finset.mem_singleton_self _)
  have hd := uibotRecovery_dart_edge_mem_succ (G := G) (hp := hp) d hv
  exact uibotRecovery_ballDartEquiv_vertex
    (I.toBallIsoV2 (r + 1) (Nat.succ_pos r)) ⟨d, hd⟩

private theorem geomDart_flip
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : WholePlaneDart W) :
    uibotCutGeomDartEquiv I (wholePlaneDartFlip W d) =
      wholePlaneDartFlip W' (uibotCutGeomDartEquiv I d) := rfl

private theorem geomDart_tail
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : WholePlaneDart W) :
    wholePlaneDartTail W' (uibotCutGeomDartEquiv I d) ↔ wholePlaneDartTail W d := by
  change (¬ d.2 = true ∧ wholePlaneEdgePresent W' _) ↔
    (¬ d.2 = true ∧ wholePlaneEdgePresent W _)
  exact ⟨fun h => ⟨h.1, hp _⟩, fun h => ⟨h.1, hp' _⟩⟩

private theorem geomDart_root
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G')) :
    uibotCutGeomDartEquiv I (wholePlaneDartι W 0 (0, false)) =
      wholePlaneDartι W' 0 (0, false) :=
  Prod.ext I.root_edge_map rfl

/-- Helper toward Proposition 3.9: geometric whole-map equivalence
determines the code on the recurrent all-present domain. Code equality is
proved here from geometry; it is not an input to cut transport. -/
theorem uibotCut_code_eq_of_geometric_iso
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (hh' : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W' N))
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G')) :
    W = W' :=
  uibotCode_eq_of_rooted_rotation_equiv W W' H H' hp hp' hh hh'
    (uibotCutGeomDartEquiv I) (uibotCutGeomDartEquiv_rotation I)
    (geomDart_flip I) (geomDart_tail I) (geomDart_root I)

/-- Helper toward Proposition 3.9: on two drawings of the same recurrent
code, every rooted geometric isomorphism fixes all actual edge and vertex
identities. This rules out arbitrary permutations of parallel edges. -/
theorem uibotCut_geometric_iso_fixes_ids
    {G' : WholePlaneDrawing W H}
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W H G' hp) (uibotWholePlaneSourceRoot W H G')) :
    (∀ a : WholePlaneEdge W, I.edgeEquiv a = a) ∧
      (∀ v : WholePlaneVertex W, I.vertexEquiv v = v) := by
  have hedge (a : WholePlaneEdge W) : I.edgeEquiv a = a := by
    have ht : wholePlaneDartTail W (a, false) :=
      ⟨by change ¬ (false = true); decide, hp a⟩
    obtain ⟨n, hn⟩ := (uibotChronologicalDart_range W (a, false)).2 ht
    have he := uibotChronologicalDart_equiv W W H H hp hp hh hh
      (uibotCutGeomDartEquiv I) (uibotCutGeomDartEquiv_rotation I)
      (geomDart_flip I) (geomDart_tail I) (geomDart_root I) n
    rw [hn] at he
    exact congrArg Prod.fst he
  refine ⟨hedge, ?_⟩
  intro v
  obtain ⟨d, rfl⟩ := uibhbot_faceOrbit_dartVertex_surjective W H v
  have he : uibotCutGeomDartEquiv I d = d := Prod.ext (hedge d.1) rfl
  exact (uibotCutGeomDartEquiv_vertex I d).trans (congrArg _ he)

/-- Helper toward Proposition 3.9: one geometric isomorphism transports
all common cut labels, both extremal rays, the root, inclusions, seam,
missing tags, orientation and inverse cut rotation simultaneously. The
boundary chains retain their geometric edges, including missing cut edges.
No code equality or code-recovery hypothesis is assumed. -/
theorem uibotCut_geometric_iso_marks
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (hh' : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W' N))
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (D : M0CutData W H) (D' : M0CutData W' H') :
    (∀ k : ℤ, I.vertexEquiv (D.x k) = D'.x k) ∧
    (∀ n : ℕ, I.vertexEquiv (D.betaR.vertex n) = D'.betaR.vertex n ∧
      I.edgeEquiv (D.betaR.edge n) = D'.betaR.edge n ∧
      I.vertexEquiv (D.betaL.vertex n) = D'.betaL.vertex n ∧
      I.edgeEquiv (D.betaL.edge n) = D'.betaL.edge n) ∧
    uibotCutGeomDartEquiv I D.rootDart = D'.rootDart ∧
    (∀ v : WholePlaneVertex W,
      v ∈ m0CutLeftVertices W H D.seam ↔
        I.vertexEquiv v ∈ m0CutLeftVertices W' H' D'.seam) ∧
    (∀ a : WholePlaneEdge W,
      (a ∈ D.edges ↔ I.edgeEquiv a ∈ D'.edges) ∧
      (D.seam a ↔ D'.seam (I.edgeEquiv a)) ∧
      (D.missing a ↔ D'.missing (I.edgeEquiv a))) ∧
    (∀ d : WholePlaneDart W,
      (d ∈ D.darts ↔ uibotCutGeomDartEquiv I d ∈ D'.darts) ∧
      (D.tail d ↔ D'.tail (uibotCutGeomDartEquiv I d))) ∧
    (∀ d a : WholePlaneDart W,
      D.IsRot d a ↔ D'.IsRot (uibotCutGeomDartEquiv I d)
        (uibotCutGeomDartEquiv I a)) := by
  have hW := uibotCut_code_eq_of_geometric_iso hh hh' I
  subst W'
  obtain ⟨he, hv⟩ := uibotCut_geometric_iso_fixes_ids hh I
  have hd (d : WholePlaneDart W) : uibotCutGeomDartEquiv I d = d :=
    Prod.ext (he d.1) rfl
  obtain ⟨hrv, hre, hlv, hle, hx⟩ := m0CutData_eq_fields W H (hh 0)
    (fun _ _ => hp _) D D'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [hv, congrFun hx k]
  · intro n
    exact ⟨(hv _).trans (congrFun hrv n), (he _).trans (congrFun hre n),
      (hv _).trans (congrFun hlv n), (he _).trans (congrFun hle n)⟩
  · exact hd D.rootDart
  · intro v
    rw [hv]
    rfl
  · intro a
    rw [he]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  · intro d
    rw [hd]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · intro d a
    rw [hd, hd]
    rfl

end GeometricTransport

section BorelBoundary

local instance uibotCutDescent2MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotCutDescent2BorelSpace : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
local instance uibotCutDescent2BoundaryOptionMeasurableSpace :
    MeasurableSpace (Option ((ℤ → ℕ) × (ℤ → ℕ))) :=
  MeasurableSpace.map some inferInstance

private theorem measurable_runZero :
    Measurable (fun W : ℤ → Fin 3 => shiftedStream W 0) :=
  measurable_pi_iff.mpr (fun n => measurable_pi_apply ((n : ℤ) - 0))

/-- Helper toward Proposition 3.9: the natural domain of the complete
boundary enumeration is Borel; both coordinate-hit families are retained. -/
theorem measurableSet_uibotCut_boundary_domain :
    MeasurableSet {W : ℤ → Fin 3 | BoundaryHitWitnesses (shiftedStream W 0)} := by
  have he : {W : ℤ → Fin 3 | BoundaryHitWitnesses (shiftedStream W 0)} =
      {W | (∀ k : ℤ, 1 ≤ k → ∃ n : ℕ, R (shiftedStream W 0) n = -k) ∧
        (∀ k : ℤ, k ≤ -1 → ∃ n : ℕ, L (shiftedStream W 0) n = k)} := by
    ext W
    exact ⟨fun h => ⟨h.rightHit, h.leftHit⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [he]
  simp only [Set.ofPred_and]
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun n =>
        (measurableSet_R n (fun z => z = -k)).preimage measurable_runZero
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun n =>
        (measurableSet_L n (fun z => z = k)).preimage measurable_runZero

private theorem measurable_boundaryHit_on_domain (k : ℤ) :
    Measurable (fun W : {W : ℤ → Fin 3 |
        BoundaryHitWitnesses (shiftedStream W 0)} =>
      boundaryHitTime (shiftedStream W.1 0) W.2 k) := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp only [boundaryHitTime_zero]
    exact measurable_const
  · by_cases hkpos : 0 < k
    · simpa only [boundaryHitTime, hk0, hkpos, dite_false, dite_true] using
        measurable_find (fun W => W.2.rightHit k (by omega))
          (fun n => (measurableSet_R n (fun z => z = -k)).preimage
            (measurable_runZero.comp measurable_subtype_coe))
    · simpa only [boundaryHitTime, hk0, hkpos, dite_false] using
        measurable_find (fun W => W.2.leftHit k (by omega))
          (fun n => (measurableSet_L n (fun z => z = k)).preimage
            (measurable_runZero.comp measurable_subtype_coe))

private theorem measurable_stage_field {β : Type*} [MeasurableSpace β]
    (n : ℕ) (f : State → β) :
    Measurable (fun w : ℕ → Fin 3 => f (kmswStage w n)) :=
  measurable_of_factors_prefix n _ (fun _ _ h => congrArg f (kmswStage_congr h))

private theorem measurable_boundary_select {β : Type*} [MeasurableSpace β]
    (f : ℕ → (ℕ → Fin 3) → β) (hf : ∀ n, Measurable (f n)) (k : ℤ) :
    Measurable (fun W : {W : ℤ → Fin 3 |
        BoundaryHitWitnesses (shiftedStream W 0)} =>
      f (boundaryHitTime (shiftedStream W.1 0) W.2 k) (shiftedStream W.1 0)) := by
  have hm : Measurable (fun p : (ℕ → Fin 3) × ℕ => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact hm.comp ((measurable_runZero.comp measurable_subtype_coe).prodMk
    (measurable_boundaryHit_on_domain k))

private theorem measurable_boundaryVertex_on_domain (k : ℤ) :
    Measurable (fun W : {W : ℤ → Fin 3 |
        BoundaryHitWitnesses (shiftedStream W 0)} =>
      boundaryVertex (shiftedStream W.1 0) W.2 k) := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simpa only [boundaryVertex_zero] using
      (measurable_const : Measurable (fun _ : {W : ℤ → Fin 3 |
        BoundaryHitWitnesses (shiftedStream W 0)} => (0 : ℕ)))
  by_cases hk1 : k = 1
  · subst k
    simpa only [boundaryVertex_one] using
      (measurable_const : Measurable (fun _ : {W : ℤ → Fin 3 |
        BoundaryHitWitnesses (shiftedStream W 0)} => (1 : ℕ)))
  simp only [boundaryVertex, hk0, hk1, dite_false]
  apply measurable_boundary_select (fun n w => activeInitial w n) _ k
  intro n
  have he : (fun w : ℕ → Fin 3 => activeInitial w n) =
      (fun w : ℕ → Fin 3 => (kmswStage w n).west (kmswStage w n).active) := by
    funext w
    exact (edge_endpoints_eq w (act_lt_nextEdge w le_rfl)).1.symm
  rw [he]
  exact measurable_stage_field n (fun s => s.west s.active)

private theorem measurable_boundaryEdge_on_domain (k : ℤ) :
    Measurable (fun W : {W : ℤ → Fin 3 |
        BoundaryHitWitnesses (shiftedStream W 0)} =>
      boundaryOuterEdge (shiftedStream W.1 0) W.2 k) := by
  by_cases hkneg : k ≤ -1
  · simp only [boundaryOuterEdge, hkneg, ite_true]
    exact measurable_boundary_select (fun n w => kmswLLCreatedEdge w n)
      (fun n => measurable_stage_field n (fun s => s.nextEdge - 1)) k
  by_cases hkpos : 1 ≤ k
  · have he : (fun W : {W : ℤ → Fin 3 |
          BoundaryHitWitnesses (shiftedStream W 0)} =>
        boundaryOuterEdge (shiftedStream W.1 0) W.2 k) =
        (fun W => act (shiftedStream W.1 0)
          (boundaryHitTime (shiftedStream W.1 0) W.2 k)) := by
      funext W
      rw [boundaryOuterEdge_of_positive _ _ hkpos,
        ← (boundaryHitTime_right_boundary_edge _ W.2 (j := k.toNat) (by omega)).1]
      congr 2
      exact Int.toNat_of_nonneg (by omega)
    rw [he]
    exact measurable_boundary_select (fun n w => act w n)
      (fun n => measurable_stage_field n (fun s => s.active)) k
  · have hk : k = 0 := by omega
    subst k
    simpa only [boundaryOuterEdge_zero] using
      (measurable_const : Measurable (fun _ : {W : ℤ → Fin 3 |
        BoundaryHitWitnesses (shiftedStream W 0)} => (0 : ℕ)))

/-- Helper toward Proposition 3.9: the complete optional boundary code is
measurable jointly in every integer vertex and edge coordinate. Negative
edge coordinates retain the identities of the missing cut edges. -/
theorem measurable_uibotCutBoundaryCodeOption : Measurable uibotCutBoundaryCodeOption := by
  classical
  have hs : Measurable (some : ((ℤ → ℕ) × (ℤ → ℕ)) →
      Option ((ℤ → ℕ) × (ℤ → ℕ))) := fun _ h => h
  unfold uibotCutBoundaryCodeOption
  exact Measurable.dite
    (hs.comp ((measurable_pi_iff.mpr measurable_boundaryVertex_on_domain).prodMk
      (measurable_pi_iff.mpr measurable_boundaryEdge_on_domain)))
    measurable_const measurableSet_uibotCut_boundary_domain

/-- Helper toward Proposition 3.9: the full boundary vertex/edge
enumeration has a Borel geometric factor. The proved inverse is consumed
inside the proof, with no code-recovery premise in this statement. -/
theorem exists_measurable_uibotCutBoundaryCodeOption_factor :
    ∃ Phi : D39GeomRootedMapClass.{0} → Option ((ℤ → ℕ) × (ℤ → ℕ)),
      Measurable Phi ∧ uibotCutBoundaryCodeOption =ᵐ[wholePlaneIIDCodeMeasure]
        Phi ∘ uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
  obtain ⟨G, hG, hinv⟩ := uibotRecovery_exists_borel_inverse
  refine ⟨uibotCutBoundaryCodeOption ∘ G,
    measurable_uibotCutBoundaryCodeOption.comp hG, ?_⟩
  filter_upwards [hinv] with W hW
  exact (congrArg uibotCutBoundaryCodeOption hW).symm

local instance uibotCutDescent2SideOptionMeasurableSpace :
    MeasurableSpace (Option GeometricSideSubmap) :=
  MeasurableSpace.map some inferInstance

/-- Helper toward Proposition 3.9: the complete ten-field marked run-zero
side, with an absent value precisely when its construction domain fails.
It records individual geometric edge IDs, including the missing edges. -/
@[expose] def uibotCutSideOption (W : ℤ → Fin 3) : Option GeometricSideSubmap := by
  classical
  exact if futureMapShiftedCodePath 0 W ∈ kmswSideDomain then
    some (kmswCodeGeometricSideTotal (futureMapShiftedCodePath 0 W)) else none

/-- Helper toward Proposition 3.9: the optional marked side is jointly
measurable in all ten fields, without any geometric recovery hypothesis. -/
theorem measurable_uibotCutSideOption : Measurable uibotCutSideOption := by
  classical
  have hs : Measurable (some : GeometricSideSubmap → Option GeometricSideSubmap) :=
    fun _ h => h
  exact Measurable.ite (measurableSet_kmswSideDomain.preimage
      (measurable_futureMapShiftedCodePath 0))
    (hs.comp (measurable_kmswCodeGeometricSideTotal.comp
      (measurable_futureMapShiftedCodePath 0))) measurable_const

private theorem runZero_tail (W : ℤ → Fin 3) :
    (fun i => futureMapShiftedCodePath 0 W (i + 1)) = shiftedStream W 0 := by
  rw [futureMapShiftedCodePath_tail]
  funext i
  simp only [futureMapShiftedStream, shiftedStream, add_zero]

/-- Helper toward Proposition 3.9: on every actual cut construction,
the optional side equals the full marked KMSW side for those same witnesses.
This supplies every field, rather than just a mark-forgetting class equality. -/
theorem uibotCutSideOption_eq_some
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) :
    uibotCutSideOption W = some (kmswCodeGeometricSide (futureMapShiftedCodePath 0 W)
      (by simpa only [runZero_tail] using h)
      (by simpa only [runZero_tail] using H.1 0)) := by
  classical
  have hb : BoundaryHitWitnesses
      (fun i => futureMapShiftedCodePath 0 W (i + 1)) := by
    simpa only [runZero_tail] using h
  have hf : KMSWFiniteIncidence
      (fun i => futureMapShiftedCodePath 0 W (i + 1)) := by
    simpa only [runZero_tail] using H.1 0
  rw [uibotCutSideOption, ite_eq_left ⟨hb, hf⟩, kmswCodeGeometricSideTotal_eq _ hb hf]

/-- Helper toward Proposition 3.9: the full marked side and all integer
boundary vertex/edge labels descend jointly to one Borel observable of the
ambient rooted geometric class. Equality holds on one common conull event. -/
theorem exists_measurable_uibotCutSideBoundary_factor :
    ∃ Phi : D39GeomRootedMapClass.{0} →
        Option GeometricSideSubmap × Option ((ℤ → ℕ) × (ℤ → ℕ)),
      Measurable Phi ∧
        (fun W => (uibotCutSideOption W, uibotCutBoundaryCodeOption W))
          =ᵐ[wholePlaneIIDCodeMeasure]
        Phi ∘ uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
  obtain ⟨G, hG, hinv⟩ := uibotRecovery_exists_borel_inverse
  refine ⟨(fun W => (uibotCutSideOption W, uibotCutBoundaryCodeOption W)) ∘ G,
    (measurable_uibotCutSideOption.prodMk measurable_uibotCutBoundaryCodeOption).comp hG, ?_⟩
  filter_upwards [hinv] with W hW
  exact (congrArg (fun W => (uibotCutSideOption W, uibotCutBoundaryCodeOption W)) hW).symm

/-- Helper toward Proposition 3.9: the recovered ten-field side has the
actual cut inclusions, root, both boundary edge sequences, missing status,
orientation, inverse rotation and face succession, all for the same datum.
The face clause concerns succession; complementary-component faces are not
identified by this statement. -/
theorem uibotCutSideOption_cut_identification
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (D : M0CutData W H) :
    ∃ S : GeometricSideSubmap, uibotCutSideOption W = some S ∧
      wholePlaneVertexι W 0 '' S.vertices = m0CutLeftVertices W H D.seam ∧
      wholePlaneEdgeι W 0 '' S.edges = D.edges ∧
      wholePlaneVertexι W 0 S.root = D.x 0 ∧
      (∀ a : ℕ,
        wholePlaneVertexι W 0 (S.west a) = wholePlaneEdgeWest W (wholePlaneEdgeι W 0 a) ∧
        wholePlaneVertexι W 0 (S.east a) = wholePlaneEdgeEast W (wholePlaneEdgeι W 0 a) ∧
        (a ∈ S.present ↔ ¬ D.missing (wholePlaneEdgeι W 0 a))) ∧
      (∀ n : ℕ,
        wholePlaneEdgeι W 0 (S.boundary n).1 = D.betaL.edge n ∧
        (S.boundary n).2 = true ∧
        wholePlaneEdgeι W 0 (S.seam (n + 1)).1 = D.betaR.edge n ∧
        (S.seam (n + 1)).2 = false) ∧
      (∀ d : ℕ × Bool,
        D.tail (wholePlaneDartι W 0 d) ↔ d.1 ∈ S.present ∧ d.2 = false) ∧
      (∀ d e : ℕ × Bool,
        S.rotation d e ↔ D.IsRot (wholePlaneDartι W 0 e) (wholePlaneDartι W 0 d)) ∧
      (∀ d e : ℕ × Bool,
        S.faceNext d e ↔ D.IsRot (wholePlaneDartFlip W (wholePlaneDartι W 0 d))
          (wholePlaneDartι W 0 e)) := by
  classical
  let S := kmswCodeGeometricSide (futureMapShiftedCodePath 0 W)
    (by simpa only [runZero_tail] using h)
    (by simpa only [runZero_tail] using H.1 0)
  have hS := uibotCutSideOption_eq_some W H h
  have hv : S.vertices = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨e, _, he⟩ := kmswM0_vertex_outgoing (shiftedStream W 0) (H.1 0) h v
    change ∃ e, edgeWest (fun i => futureMapShiftedCodePath 0 W (i + 1)) e = v ∨ _
    rw [runZero_tail]
    exact ⟨e, Or.inl he⟩
  have he : S.edges = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    exact ⟨a, kmsw_edge_allocated_by_self _ a⟩
  have hinj := (futureMap_dart_coordinates W H D h hLL).1
  refine ⟨S, hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, Set.image_univ,
      m0Cut_leftVertices_eq_runZero W H h D.seam (m0Cut_seamEdge_iff W H h hLL)]
  · rw [he, Set.image_univ, D.edges_eq h hLL]
  · have hroot : S.root = 0 := by
      dsimp only [S, kmswCodeGeometricSide]
      exact boundaryVertex_zero _ _
    rw [hroot]
    rfl
  · intro a
    change wholePlaneVertexι W 0 (edgeWest _ a) = _ ∧
      wholePlaneVertexι W 0 (edgeEast _ a) = _ ∧ (EdgePresent _ a ↔ _)
    simp only [runZero_tail, D.missing_eq h hLL, not_not]
    exact ⟨rfl, rfl, trivial⟩
  · intro n
    have hb := uibotCut_boundary_edge_identifications W H h hLL D
    have hcode : BoundaryHitWitnesses
        (fun j => futureMapShiftedCodePath 0 W (j + 1)) := by
      simpa only [runZero_tail] using h
    change wholePlaneEdgeι W 0 (boundaryOuterEdge _ hcode (-(n : ℤ) - 1)) = _ ∧
      true = true ∧ wholePlaneEdgeι W 0
        (boundaryOuterEdge _ hcode ((n + 1 : ℕ) : ℤ)) = _ ∧
      false = false
    simp only [runZero_tail, Nat.cast_add, Nat.cast_one]
    exact ⟨hb.2.2.1 n, trivial, hb.2.1 n, trivial⟩
  · intro d
    change D.tail (wholePlaneDartι W 0 d) ↔ EdgePresent _ d.1 ∧ d.2 = false
    rw [runZero_tail, D.tail_eq h hLL]
    exact and_comm
  · intro d e
    change kmswInfRot _ _ d = e ↔ _
    simp only [runZero_tail]
    constructor
    · intro hde
      apply (futureMap_rotation_iff D h hLL e (wholePlaneDartι W 0 d)).2
      have hde' : kmswInfRot (shiftedStream W 0) (H.1 0) d = e := hde
      rw [← hde', Equiv.symm_apply_apply]
    · intro hde
      have hi := (futureMap_rotation_iff D h hLL e (wholePlaneDartι W 0 d)).1 hde
      exact (congrArg (kmswInfRot (shiftedStream W 0) (H.1 0)) (hinj hi)).trans
        ((kmswInfRot (shiftedStream W 0) (H.1 0)).apply_symm_apply e)
  · intro d e
    change kmswInfFaceSucc _ _ d = e ↔ _
    simp only [runZero_tail]
    constructor
    · intro hde
      apply (futureMap_face_successor_iff W H D h hLL d (wholePlaneDartι W 0 e)).2
      exact congrArg (wholePlaneDartι W 0) hde.symm
    · intro hde
      exact (hinj ((futureMap_face_successor_iff W H D h hLL d
        (wholePlaneDartι W 0 e)).1 hde)).symm

/-- Helper toward Proposition 3.9: the joint Borel side/boundary factor is
identified on a single event with the same geometric representative, cut
datum, root, ordered endpoint labels, boundary rays and run inclusions.
The existential witnesses precede every simultaneous boundary quantifier. -/
theorem exists_measurable_uibotCut_factor_shared_realization :
    ∃ Phi : D39GeomRootedMapClass.{0} →
        Option GeometricSideSubmap × Option ((ℤ → ℕ) × (ℤ → ℕ)),
      Measurable Phi ∧
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        ∃ (H : WholePlaneRotationHypothesis W)
          (h0 : BoundaryHitWitnesses (shiftedStream W 0))
          (hpast : BoundaryHitWitnesses (kmswPastCode W))
          (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
          (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
            (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h0 (k - 1)))))
          (hdom : D39GeomDomain
            (uibotWholePlaneGeometricMap W H
              (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
            (uibotWholePlaneGeometricRoot W H
              (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))),
          let D := m0CutData W H h0 hLL
          let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
          let M := uibotWholePlaneGeometricMap W H G hp
          let rho := uibotWholePlaneGeometricRoot W H G
          Phi (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) =
            (some (kmswCodeGeometricSideTotal (futureMapShiftedCodePath 0 W)),
              some (boundaryVertex (shiftedStream W 0) h0,
                boundaryOuterEdge (shiftedStream W 0) h0)) ∧
          uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W =
            uibotCutRootClass W H h0 hpast hp hdom ∧
          (rho.1 = Quotient.mk G.edgeSetoid D.rootDart ∧
            d39GeomRootVertex M rho = D.x 0 ∧
            d39GeomRootOtherVertex M rho = D.x 1) ∧
          (∀ (k : ℤ) (v : WholePlaneVertex W),
            m0CutBoundaryLabel W H k v ↔ v = D.x k) ∧
          (∀ k : ℤ, D.x k = wholePlaneVertexι W 0
            (boundaryVertex (shiftedStream W 0) h0 k)) ∧
          (∀ n : ℕ, D.betaR.vertex n = D.x ((n : ℤ) + 1)) ∧
          (∀ n : ℕ, D.betaL.vertex n = D.x (-(n : ℤ))) ∧
          D.edges = Set.range (wholePlaneEdgeι W 0) ∧
          D.darts = Set.range (wholePlaneDartι W 0) := by
  obtain ⟨Phi, hPhi, hfactor⟩ := exists_measurable_uibotCutSideBoundary_factor
  refine ⟨Phi, hPhi, ?_⟩
  filter_upwards [hfactor, uibotCut_ae_shared_root_boundary] with W hfactor hW
  obtain ⟨H, h0, hpast, hp, hLL, hdom, hrest⟩ := hW
  refine ⟨H, h0, hpast, hp, hLL, hdom, ?_, hrest⟩
  have hside : uibotCutSideOption W =
      some (kmswCodeGeometricSideTotal (futureMapShiftedCodePath 0 W)) := by
    have hgood : futureMapShiftedCodePath 0 W ∈ kmswSideDomain := by
      constructor
      · simpa only [runZero_tail] using h0
      · simpa only [runZero_tail] using H.1 0
    exact ite_eq_left hgood
  change Phi (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) = _
  dsimp only [Function.comp_apply] at hfactor
  rw [← hfactor, hside, uibotCutBoundaryCodeOption_eq_some W h0]

end BorelBoundary

/- REMAINDER: the boundary-option factor left open in UIBOTCutDescent is now
proved above. The ten-field side factor and its cut characterization retain
the combinatorial face successor. They do not certify the following stronger
geometric face transport, recorded here with full binders (an obligation,
not a premise or an admitted declaration):

  ∀ (W W' : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis W')
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (h0' : BoundaryHitWitnesses (shiftedStream W' 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hpast' : BoundaryHitWitnesses (kmswPastCode W'))
    (hp : ∀ a : WholePlaneEdge W, wholePlaneEdgePresent W a)
    (hp' : ∀ a : WholePlaneEdge W', wholePlaneEdgePresent W' a),
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let G' := WholePlanePastGlueDrawing.glueDrawing W' h0' hpast' H'
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G)
      (uibotWholePlaneGeometricMap W' H' G' hp') (uibotWholePlaneGeometricRoot W' H' G'),
      ∃ f : FutureMapInternalFaceOrbit W H ≃ FutureMapInternalFaceOrbit W' H',
        ∀ q : FutureMapInternalFaceOrbit W H,
          I.h '' (futureMapInternalGluedFace W H h0 hpast q).val =
            (futureMapInternalGluedFace W' H' h0' hpast' (f q)).val

Also outstanding for the full consumer: an intrinsic geometric formulation
and Borel realization of that complementary-component face collection, with
its incidences and the actual submap inclusion. The factors proved here use
the full run-zero coordinate fields; they do not define a new measurable
quotient of embedded cuts. No consumer qualifier or numbered result is closed. -/

end DirectedDistances.PaperProofs.Section3
end
