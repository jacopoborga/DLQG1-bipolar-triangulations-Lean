module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirror
public import DirectedDistances.PlanarMap.MirrorMap

/-! The all-geometric distance includes the missing frame edge. The lower carrier
reflection is constructed here. Extension to the planar carrier and the faced
coordinate identification remain explicit open obligations. -/

public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open MeasureTheory TopologicalSpace

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private def rootedMirrorVertexEquiv {D : Type} (rot : Equiv.Perm D) :
    RootedLocallyFiniteVertex D rot ≃ RootedLocallyFiniteVertex D rot.symm where
  toFun := Quotient.map id (fun _ _ h => Equiv.Perm.sameCycle_inv.mpr h)
  invFun := Quotient.map id (fun _ _ h => Equiv.Perm.sameCycle_inv.mp h)
  left_inv := by intro v; induction v using Quotient.inductionOn; rfl
  right_inv := by intro v; induction v using Quotient.inductionOn; rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Reflection preserves outer-face cycles after exchanging edge incidences. -/
private theorem rootedMirrorFaceCycle (M : RootedLocallyFiniteMap) (a b : M.D) :
    Equiv.Perm.SameCycle (M.rot * M.edgeInv) (M.edgeInv a) (M.edgeInv b) ↔
      Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) a b := by
  have hi : M.edgeInv⁻¹ = M.edgeInv := by
    ext d
    apply M.edgeInv.injective
    change M.edgeInv (M.edgeInv.symm d) = M.edgeInv (M.edgeInv d)
    rw [M.edgeInv.apply_symm_apply, M.edgeInv_invol]
  have hf : M.rot * M.edgeInv =
      M.edgeInv * (M.rot.symm * M.edgeInv)⁻¹ * M.edgeInv⁻¹ := by
    rw [mul_inv_rev, hi, Equiv.Perm.inv_def, Equiv.symm_symm]
    have he : M.edgeInv * M.edgeInv = 1 := by
      ext d
      exact M.edgeInv_invol d
    rw [← mul_assoc, he, one_mul]
  rw [hf, Equiv.Perm.sameCycle_conj, hi]
  simpa only [M.edgeInv_invol] using
    (Equiv.Perm.sameCycle_inv (f := M.rot.symm * M.edgeInv) (x := a) (y := b))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The reflected lower carrier reverses the ordered missing frame edge. Root
representatives are normalized to frame incidences, and optional marks preserve
presence while moving to the former root. Planarity is a separate obligation. -/
@[expose, reducible] def mirrorRootedLocallyFiniteMap (M : RootedLocallyFiniteMap) :
    RootedLocallyFiniteMap where
  D := M.D
  countableD := M.countableD
  rot := M.rot.symm
  edgeInv := M.edgeInv
  edgeInv_invol := M.edgeInv_invol
  edgeInv_ne := M.edgeInv_ne
  missing := M.missing
  missing_edgeInv := M.missing_edgeInv
  tail := M.tail
  tail_iff := M.tail_iff
  tail_missing := M.tail_missing
  outer := M.edgeInv M.outer
  missing_outer := by
    intro d hd
    change Equiv.Perm.SameCycle (M.rot * M.edgeInv) (M.edgeInv M.outer) d ∨ _
    rcases M.missing_outer d hd with h | h
    · right
      exact (rootedMirrorFaceCycle M M.outer d).2 h
    · left
      have hm := (rootedMirrorFaceCycle M M.outer (M.edgeInv d)).2 h
      rw [M.edgeInv_invol] at hm
      exact hm
  rootDart := M.edgeInv M.frameEdgeDart
  frameEdgeDart := M.edgeInv M.frameEdgeDart
  frameEdge_missing := (M.missing_edgeInv _).1 M.frameEdge_missing
  frameEdge_at_root := Equiv.Perm.SameCycle.rfl
  frameOtherDart := M.frameOtherDart.map (fun _ => M.frameEdgeDart)
  frameOtherDart_valid := by
    intro y hy
    cases ho : M.frameOtherDart with
    | none => simp only [ho, Option.map_none, reduceCtorEq] at hy
    | some d =>
      have he : M.frameEdgeDart = y := by
        simpa only [ho, Option.map_some, Option.some.injEq] using hy
      rw [M.edgeInv_invol, ← he]
  locallyFinite := by
    intro d
    exact (M.locallyFinite d).subset (fun _ h => Equiv.Perm.sameCycle_inv.mp h)
  connected := by
    intro d e
    induction M.connected d e with
    | refl => exact .refl
    | tail _ h ih =>
      apply ih.tail
      rcases h with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  acyclic := by
    intro v hv
    let e := rootedMirrorVertexEquiv M.rot
    apply M.acyclic (e.symm v)
    exact Relation.TransGen.lift e.symm (by
      rintro a b ⟨d, hd, ht, ha, hb⟩
      exact ⟨d, hd, ht, congrArg e.symm ha, congrArg e.symm hb⟩) v v hv

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Twice reversing the frame recovers its exact dart; the root recovers the same -/
private theorem mirrorRootedLocallyFiniteMap_twice_frame (M : RootedLocallyFiniteMap) :
    (mirrorRootedLocallyFiniteMap (mirrorRootedLocallyFiniteMap M)).frameEdgeDart =
      M.frameEdgeDart ∧
    M.rot.SameCycle
      (mirrorRootedLocallyFiniteMap (mirrorRootedLocallyFiniteMap M)).rootDart M.rootDart :=
  ⟨M.edgeInv_invol _, by
    change M.rot.SameCycle (M.edgeInv (M.edgeInv M.frameEdgeDart)) M.rootDart
    rw [M.edgeInv_invol]
    exact M.frameEdge_at_root.symm⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Normalize the representatives of the root and optional opposite endpoint while -/
@[expose] def normalizeRootedLocallyFiniteFrame (M : RootedLocallyFiniteMap) :
    RootedLocallyFiniteMap :=
  { M with
    rootDart := M.frameEdgeDart
    frameEdge_at_root := Equiv.Perm.SameCycle.rfl
    frameOtherDart := M.frameOtherDart.map (fun _ => M.edgeInv M.frameEdgeDart)
    frameOtherDart_valid := by
      intro y hy
      cases ho : M.frameOtherDart with
      | none => simp only [ho, Option.map_none, reduceCtorEq] at hy
      | some d =>
        have he : M.edgeInv M.frameEdgeDart = y := by
          simpa only [ho, Option.map_some, Option.some.injEq] using hy
        rw [← he] }

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The complete lower carrier is involutive up to frame representative normalization.
This includes the optional endpoint mark and all geometric and orientation data. -/
theorem mirrorRootedLocallyFiniteMap_involutive (M : RootedLocallyFiniteMap) :
    mirrorRootedLocallyFiniteMap (mirrorRootedLocallyFiniteMap M) =
      normalizeRootedLocallyFiniteFrame M := by
  simp only [mirrorRootedLocallyFiniteMap, normalizeRootedLocallyFiniteFrame,
    Equiv.symm_symm, M.edgeInv_invol, Option.map_map, Function.comp_def]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
A reflected geometric step is the same geometric edge on transported vertices. -/
private theorem rootedMirrorGeometricStep (M : RootedLocallyFiniteMap)
    {v w : RootedLocallyFiniteVertex M.D M.rot.symm}
    (h : rootedLocallyFiniteGeometricStep M.rot.symm M.edgeInv v w) :
    rootedLocallyFiniteGeometricStep M.rot M.edgeInv
      ((rootedMirrorVertexEquiv M.rot).symm v)
      ((rootedMirrorVertexEquiv M.rot).symm w) := by
  obtain ⟨d, hd, he⟩ := h
  exact ⟨d, congrArg (rootedMirrorVertexEquiv M.rot).symm hd,
    congrArg (rootedMirrorVertexEquiv M.rot).symm he⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Transport radius bounds across geometric steps with a one-edge initial displacement. -/
private theorem radius_transport_shift (M N : RootedLocallyFiniteMap)
    (e : RootedLocallyFiniteVertex N.D N.rot → RootedLocallyFiniteVertex M.D M.rot)
    (hroot : rootedLocallyFiniteWithinRadius M 1
      (e (rootedLocallyFiniteVertexClassOf N N.rootDart)))
    (hstep : ∀ {v w}, rootedLocallyFiniteGeometricStep N.rot N.edgeInv v w →
      rootedLocallyFiniteGeometricStep M.rot M.edgeInv (e v) (e w))
    {r v} (h : rootedLocallyFiniteWithinRadius N r v) :
    rootedLocallyFiniteWithinRadius M (r + 1) (e v) := by
  induction h with
  | root => exact hroot
  | stay _ ih => exact .stay ih
  | edge _ he ih => exact .edge ih (hstep he)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The reflected radius-r vertex set lies in the original radius-(r+1) set. -/
private theorem rootedMirrorWithinRadius_shift (M : RootedLocallyFiniteMap) {r : ℕ}
    {v : RootedLocallyFiniteVertex M.D M.rot.symm}
    (h : rootedLocallyFiniteWithinRadius (mirrorRootedLocallyFiniteMap M) r v) :
    rootedLocallyFiniteWithinRadius M (r + 1)
      ((rootedMirrorVertexEquiv M.rot).symm v) := by
  apply radius_transport_shift M (mirrorRootedLocallyFiniteMap M)
    (rootedMirrorVertexEquiv M.rot).symm ?_ (fun he => rootedMirrorGeometricStep M he) h
  apply rootedLocallyFiniteWithinRadius.edge rootedLocallyFiniteWithinRadius.root
  exact ⟨M.frameEdgeDart, Quotient.sound M.frameEdge_at_root.symm, rfl⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The actual all-geometric dart balls obey the one-edge inclusion, despite the -/
theorem rootedMirrorBallDarts_shift (M : RootedLocallyFiniteMap) (r : ℕ) (d : M.D)
    (hd : d ∈ rootedLocallyFiniteBallDarts (mirrorRootedLocallyFiniteMap M) r) :
    d ∈ rootedLocallyFiniteBallDarts M (r + 1) := by
  rw [mem_rootedLocallyFiniteBallDarts] at hd ⊢
  constructor
  · exact (mem_rootedLocallyFiniteRadiusVertices M _ _).2
      (rootedMirrorWithinRadius_shift M
        ((mem_rootedLocallyFiniteRadiusVertices _ _ _).1 hd.1))
  · exact (mem_rootedLocallyFiniteRadiusVertices M _ _).2
      (rootedMirrorWithinRadius_shift M
        ((mem_rootedLocallyFiniteRadiusVertices _ _ _).1 hd.2))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Open obligation: every positive-radius ball of the constructed lower mirror
has genus zero. No proof is supplied or assumed. -/
@[expose] def RootedLocallyFiniteMirrorBallPlanarity
    (M : RootedLocallyFinitePlanarMap) : Prop :=
  ∀ r, 0 < r →
    let A := mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap
    letI : DecidableEq {d : A.D // d ∈ rootedLocallyFiniteBallDarts A r} :=
      Classical.decEq _
    (rootedLocallyFiniteBallCombinatorialMap A r).IsPlanar

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Open obligation: the mirrored outer face and selected frame incidence are
captured together in a finite mirrored ball. No proof is supplied or assumed. -/
@[expose] def RootedLocallyFiniteMirrorOuterCapture
    (M : RootedLocallyFinitePlanarMap) : Prop :=
  let A := mirrorRootedLocallyFiniteMap M.toRootedLocallyFiniteMap
  ∀ r, 0 < r → ∀ d, d ∈ rootedLocallyFiniteBallDarts A r →
    Equiv.Perm.SameCycle (A.rot.symm * A.edgeInv) A.outer d →
    ∃ R, r ≤ R ∧ ∃ hdR : d ∈ rootedLocallyFiniteBallDarts A R,
      ∃ hfR : rootedLocallyFiniteOuterFrameDart A ∈ rootedLocallyFiniteBallDarts A R,
        letI : DecidableEq {d : A.D // d ∈ rootedLocallyFiniteBallDarts A R} :=
          Classical.decEq _
        CombinatorialMap.IsOuter (rootedLocallyFiniteBallCombinatorialMap A R)
          ⟨rootedLocallyFiniteOuterFrameDart A, hfR⟩ ⟨d, hdR⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The exact shifted coordinate equation for a proposed planar-carrier mirror. -/
@[expose] def RootedLocallyFiniteMirrorShiftedCoordinateEquation
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap)
    (c : ℕ → FacedFramedBallClass → FacedFramedBallClass) : Prop :=
  ∀ r M, rootedLocallyFiniteFacedBallClass r (mirrorMap M) =
    c r (rootedLocallyFiniteFacedBallClass (r + 1) M)




@[expose] def RootedLocallyFiniteMirrorShiftedClassDeterminacy
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap) : Prop :=
  ∀ r M N, rootedLocallyFiniteFacedBallClass (r + 1) M =
      rootedLocallyFiniteFacedBallClass (r + 1) N →
    rootedLocallyFiniteFacedBallClass r (mirrorMap M) =
      rootedLocallyFiniteFacedBallClass r (mirrorMap N)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Existence of a shifted coordinate action is equivalent to faced-class determinacy.
The extension can be arbitrary on classes never realized at the source radius.
This equivalence does not prove geometric determinacy. -/
theorem rootedMirrorShiftedCoordinateEquation_iff
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap) :
    (∃ c, RootedLocallyFiniteMirrorShiftedCoordinateEquation mirrorMap c) ↔
      RootedLocallyFiniteMirrorShiftedClassDeterminacy mirrorMap := by
  constructor
  · rintro ⟨c, hc⟩ r M N heq
    rw [hc r M, hc r N, heq]
  · intro h
    refine ⟨fun r => Function.extend (rootedLocallyFiniteFacedBallClass (r + 1))
      (rootedLocallyFiniteFacedBallClass r ∘ mirrorMap) id, ?_⟩
    intro r M
    have hf : Function.FactorsThrough (rootedLocallyFiniteFacedBallClass r ∘ mirrorMap)
        (rootedLocallyFiniteFacedBallClass (r + 1)) := by
      intro M N heq
      exact h r M N heq
    exact (hf.extend_apply id M).symm

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
A shifted coordinate equation implies continuity in the helper topology.
This conditional theorem does not discharge that equation. -/
theorem continuous_mirrorRootedLocallyFinitePlanarMap_of_shiftedCoordinateEquation
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap)
    (c : ℕ → FacedFramedBallClass → FacedFramedBallClass)
    (h : RootedLocallyFiniteMirrorShiftedCoordinateEquation mirrorMap c) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    Continuous mirrorMap := by
  rw [bsLocalDistanceTopology_eq_localClassTopologyGeneric]
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    localClassTopology rootedLocallyFiniteFacedBallClass
  change @Continuous _ _ _ (generateFrom
    (localCylinders rootedLocallyFiniteFacedBallClass)) mirrorMap
  apply continuous_generateFrom_iff.mpr
  rintro s ⟨r, q, rfl⟩
  have hc : Continuous (c r ∘ rootedLocallyFiniteFacedBallClass (r + 1)) :=
    continuous_of_discreteTopology.comp
      (continuous_localClass rootedLocallyFiniteFacedBallClass (r + 1))
  have heq : rootedLocallyFiniteFacedBallClass r ∘ mirrorMap =
      c r ∘ rootedLocallyFiniteFacedBallClass (r + 1) := funext (h r)
  change IsOpen ((rootedLocallyFiniteFacedBallClass r ∘ mirrorMap) ⁻¹' {q})
  rw [heq]
  exact hc.isOpen_preimage {q} (isOpen_discrete _)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
A shifted coordinate equation implies Borel measurability in the helper topology. -/
theorem measurable_mirrorRootedLocallyFinitePlanarMap_of_shiftedCoordinateEquation
    (mirrorMap : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap)
    (c : ℕ → FacedFramedBallClass → FacedFramedBallClass)
    (h : RootedLocallyFiniteMirrorShiftedCoordinateEquation mirrorMap c) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    Measurable mirrorMap := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  exact (continuous_mirrorRootedLocallyFinitePlanarMap_of_shiftedCoordinateEquation
    mirrorMap c h).measurable

end DirectedDistances.PlanarMap
