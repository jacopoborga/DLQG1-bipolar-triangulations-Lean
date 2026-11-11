module

public import DirectedDistances.PlanarMap.D39DrawingRepresentation3

/-! # Topological transport for Definition 3.8

Helper toward Proposition 5.16. This module is a bounded transport helper and
makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. Reverse the interval parameter precisely
when a dart traverses its stored edge backward. -/
@[expose] def d39DartParamReversal (forward : Bool) : I ≃ₜ I :=
  if forward then Homeomorph.refl I else unitInterval.symmHomeomorph

/-- Helper toward Proposition 5.16. The interval map induced by a geometric
isomorphism on a dart. -/
@[expose] def d39GeometricDartParam {M : D39RootedMap}
    {B C : D39DomainRootedMapV2}
    (R : D39GeomRootedMapIsoV2 B.map B.root C.map C.root)
    (data : D39DrawingRepresentationData3 M B) (d : M.core.D) : I ≃ₜ I :=
  (d39DartParamReversal (data.dartEquiv d).2).trans
    (R.edgeParam (data.dartEquiv d).1) |>.trans
      (d39DartParamReversal
        (Bool.xor (data.dartEquiv d).2
          (R.edgeFlip (data.dartEquiv d).1)))

/-- Helper toward Proposition 5.16. The induced dart parameter map is
strictly increasing. -/
theorem d39GeometricDartParam_strictMono {M : D39RootedMap}
    {B C : D39DomainRootedMapV2}
    (R : D39GeomRootedMapIsoV2 B.map B.root C.map C.root)
    (data : D39DrawingRepresentationData3 M B) (d : M.core.D) :
    StrictMono (d39GeometricDartParam R data d) := by
  let p := data.dartEquiv d
  unfold d39GeometricDartParam
  have hs : StrictAnti unitInterval.symm := unitInterval.strictAnti_symm
  cases hb : p.2 <;> cases hf : R.edgeFlip p.1
  · simp only [p, hb, hf, Bool.xor_false, Bool.false_xor,
      d39DartParamReversal, Homeomorph.trans_apply] at ⊢
    change StrictMono (fun t : I =>
      unitInterval.symm (R.edgeParam p.1 (unitInterval.symm t)))
    intro x y hxy
    have h1 : unitInterval.symm y < unitInterval.symm x := hs hxy
    have h2 := R.edgeParam_mono p.1 hf h1
    exact hs h2
  · simp only [p, hb, hf, Bool.xor_false, Bool.false_xor,
      d39DartParamReversal, Homeomorph.trans_apply] at ⊢
    change StrictMono (fun t : I =>
      R.edgeParam p.1 (unitInterval.symm t))
    intro x y hxy
    have h1 : unitInterval.symm y < unitInterval.symm x := hs hxy
    have h2 := R.edgeParam_anti p.1 hf h1
    exact h2
  · simp only [p, hb, hf, Bool.xor_false, Bool.false_xor,
      d39DartParamReversal, Homeomorph.trans_apply] at ⊢
    change StrictMono (fun t : I =>
      R.edgeParam p.1 t)
    exact R.edgeParam_mono p.1 hf
  · simp only [p, hb, hf, Bool.xor_false, Bool.false_xor,
      d39DartParamReversal, Homeomorph.trans_apply] at ⊢
    change StrictMono (fun t : I =>
      unitInterval.symm (R.edgeParam p.1 t))
    intro x y hxy
    have h1 := R.edgeParam_anti p.1 hf hxy
    exact hs h1

/-- Helper toward Proposition 5.16. The target dart path is the image of the
source path under the plane homeomorphism and induced reparameterization. -/
theorem d39DrawingDartArc_geometric_map {M : D39RootedMap}
    {B C : D39DomainRootedMapV2}
    (R : D39GeomRootedMapIsoV2 B.map B.root C.map C.root)
    (data : D39DrawingRepresentationData3 M B) (d : M.core.D) (t : I) :
    R.h (d39DrawingDartArc B data.toD39DrawingRepresentationData d t) =
      d39DrawingDartArc C (data.toD39DrawingRepresentationData.transportGeometricData R)
        d (d39GeometricDartParam R data d t) := by
  let p := data.dartEquiv d
  have hdart :
      (data.toD39DrawingRepresentationData.transportGeometricData R).dartEquiv d =
        (R.edgeEquiv p.1, Bool.xor p.2 (R.edgeFlip p.1)) := rfl
  cases hb : p.2 <;> cases hf : R.edgeFlip p.1
  · simp [d39DrawingDartArc, d39GeometricDartParam, d39DartParamReversal,
      D39DrawingRepresentationData.transportGeometricData,
      D39DrawingRepresentationData.d39DrawingDartOrderEquiv,
      p, hb, hf, R.arc_map]
    change (C.map.toPlaneMapWithMissing.arc (R.edgeEquiv p.1))
        (R.edgeParam p.1 (unitInterval.symm t)) =
      (C.map.toPlaneMapWithMissing.arc (R.edgeEquiv p.1))
        (unitInterval.symm (unitInterval.symm
          (R.edgeParam p.1 (unitInterval.symm t))))
    simp
  · simp [d39DrawingDartArc, d39GeometricDartParam, d39DartParamReversal,
      D39DrawingRepresentationData.transportGeometricData,
      D39DrawingRepresentationData.d39DrawingDartOrderEquiv,
      p, hb, hf, R.arc_map] <;> rfl
  · simp [d39DrawingDartArc, d39GeometricDartParam, d39DartParamReversal,
      D39DrawingRepresentationData.transportGeometricData,
      D39DrawingRepresentationData.d39DrawingDartOrderEquiv,
      p, hb, hf, R.arc_map] <;> rfl
  · simp [d39DrawingDartArc, d39GeometricDartParam, d39DartParamReversal,
      D39DrawingRepresentationData.transportGeometricData,
      D39DrawingRepresentationData.d39DrawingDartOrderEquiv,
      p, hb, hf, R.arc_map]
    change (C.map.toPlaneMapWithMissing.arc (R.edgeEquiv p.1))
        (R.edgeParam p.1 t) =
      (C.map.toPlaneMapWithMissing.arc (R.edgeEquiv p.1))
        (unitInterval.symm (unitInterval.symm (R.edgeParam p.1 t)))
    simp

/-- Helper toward Proposition 5.16. A strictly increasing interval
homeomorphism fixes both endpoints. -/
theorem d39StrictMonoIntervalEndpoints (φ : I ≃ₜ I)
    (hφ : StrictMono φ) : φ 0 = 0 ∧ φ 1 = 1 := by
  have h0 : φ 0 ≤ 0 := by
    have h := hφ.monotone (show (0 : I) ≤ φ.symm 0 from (φ.symm 0).property.1)
    simpa using h
  have h1 : 1 ≤ φ 1 := by
    have hle : φ.symm 1 ≤ (1 : I) := by
      change (φ.symm 1).val ≤ (1 : ℝ)
      exact (φ.symm 1).property.2
    have h := hφ.monotone hle
    simpa using h
  exact ⟨le_antisymm h0 (show (0 : I) ≤ φ 0 from (φ 0).property.1),
    le_antisymm (φ 1).property.2 h1⟩

/-- Helper toward Proposition 5.16. An orientation-preserving plane
homeomorphism transports the successor witness under increasing
reparameterizations. -/
theorem d39TopologicalCcwSuccessor_map_orientedHomeomorph
    {D : Type*} (star : Set D) (arc arc' : D → I → ℂ)
    (param : D → I ≃ₜ I) (d e : D)
    (R : ℂ ≃ₜ ℂ) (hR : OrientationPreserving R)
    (hparam : ∀ x ∈ star, StrictMono (param x))
    (hmap : ∀ x ∈ star, ∀ t, R (arc x t) = arc' x (param x t))
    (h : D39TopologicalCcwSuccessor star arc d e) :
    D39TopologicalCcwSuccessor star arc' d e := by
  rcases h with ⟨H, hH, dir, hdir, harg, hsucc, hstraight⟩
  refine ⟨R.symm.trans H,
    OrientationPreserving.trans (OrientationPreserving.symm hR) hH,
    dir, hdir, harg, hsucc, ?_⟩
  intro x hx
  obtain ⟨t, ht0, ht1, hset⟩ := hstraight x hx
  let φ := param x
  have hφ := hparam x hx
  have hend := d39StrictMonoIntervalEndpoints φ hφ
  have hinv_mono : Monotone φ.symm := by
    intro a b hab
    by_contra hnot
    have hlt : φ.symm b < φ.symm a := lt_of_not_ge hnot
    have hlt' := hφ hlt
    have : b < a := by simpa [φ] using hlt'
    exact (not_lt_of_ge hab) this
  have ht0I : (0 : I) < t := by exact_mod_cast ht0
  have ht1I : t < (1 : I) := by exact_mod_cast ht1
  have ht0'I : (0 : I) < φ t := by rw [← hend.1]; exact hφ ht0I
  have ht1'I : φ t < (1 : I) := by rw [← hend.2]; exact hφ ht1I
  have ht0' : 0 < φ t := by exact_mod_cast ht0'I
  have ht1' : φ t < 1 := by exact_mod_cast ht1'I
  have hpreimage :
      R.symm '' (arc' x '' Set.Icc (0 : I) (φ t)) =
        arc x '' Set.Icc (0 : I) t := by
    ext z
    constructor
    · rintro ⟨w, ⟨s, hs, rfl⟩, hRz⟩
      have hs0 : (0 : I) ≤ φ.symm s := by
        have hzero : φ.symm 0 = 0 := by
          calc
            φ.symm 0 = φ.symm (φ 0) := by rw [hend.1]
            _ = 0 := φ.symm_apply_apply 0
        simpa [hzero] using hinv_mono hs.1
      have hst : φ.symm s ≤ t := by
        have := hinv_mono hs.2
        simpa using this
      have hback : R.symm (arc' x s) = arc x (φ.symm s) := by
        have hm := congrArg R.symm (hmap x hx (φ.symm s))
        simpa [φ] using hm.symm
      refine ⟨φ.symm s, ⟨hs0, hst⟩, ?_⟩
      exact hback.symm.trans hRz
    · rintro ⟨s, hs, rfl⟩
      refine ⟨arc' x (φ s), ⟨φ s, ?_, rfl⟩, ?_⟩
      · constructor
        · simpa [hend.1] using hφ.monotone hs.1
        · exact hφ.monotone hs.2
      · have hm := hmap x hx s
        simpa [φ] using (congrArg R.symm hm).symm
  have hstraight' :
      (R.symm.trans H) '' (arc' x '' Set.Icc (0 : I) (φ t)) =
        {z : ℂ | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
          z = (s : ℂ) * dir x} := by
    calc
      (R.symm.trans H) '' (arc' x '' Set.Icc (0 : I) (φ t)) =
          H '' (R.symm '' (arc' x '' Set.Icc (0 : I) (φ t))) := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨R.symm w, ⟨w, hw, rfl⟩, rfl⟩
        · rintro ⟨w, hw, rfl⟩
          rcases hw with ⟨w', hw', rfl⟩
          exact ⟨w', hw', rfl⟩
      _ = {z : ℂ | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
          z = (s : ℂ) * dir x} := by rw [hpreimage]; exact hset
  exact ⟨φ t, ht0', ht1', hstraight'⟩

/-- Helper toward Proposition 5.16. Transport v3 drawing data across an
orientation-preserving geometric rooted-map isomorphism. -/
@[expose] noncomputable def D39DrawingRepresentationData3.transportGeometricData
    {M : D39RootedMap} {B C : D39DomainRootedMapV2}
    (R : D39GeomRootedMapIsoV2 B.map B.root C.map C.root)
    (h : D39DrawingRepresentationData3 M B) :
    D39DrawingRepresentationData3 M C := by
  classical
  let hbase := h.toD39DrawingRepresentationData.transportGeometricData R
  refine
    { toD39DrawingRepresentationData := hbase
      rotation_topological_successor := ?_
      vertex_frontier_incidence := ?_ }
  · intro d
    let star := {e | rootedLocallyFiniteVertexClass M.core.rot e =
      rootedLocallyFiniteVertexClass M.core.rot d}
    have hsucc := d39TopologicalCcwSuccessor_map_orientedHomeomorph
      star (d39DrawingDartArc B h.toD39DrawingRepresentationData)
      (d39DrawingDartArc C hbase)
      (fun x => d39GeometricDartParam R h x) d (M.core.rot d)
      R.h R.orientationPreserving
      (fun x hx => d39GeometricDartParam_strictMono R h x)
      (fun x hx t => d39DrawingDartArc_geometric_map R h x t)
      (h.rotation_topological_successor d)
    simpa [star, hbase] using hsucc
  · intro d v
    let pos := B.map.toPlaneMapWithMissing.pos (h.vertexEquiv v)
    let face := h.faceOfDart d
    have hpos :
        C.map.toPlaneMapWithMissing.pos (hbase.vertexEquiv v) = R.h pos := by
      change C.map.toPlaneMapWithMissing.pos
          (R.vertexEquiv (h.vertexEquiv v)) = _
      exact (R.pos_map (h.vertexEquiv v)).symm
    have hface : hbase.faceOfDart d = R.faceEquiv face := rfl
    have hfront : R.h pos ∈ frontier (R.h '' face.val) ↔ pos ∈ frontier face.val := by
      rw [← R.h.image_frontier]
      constructor
      · rintro ⟨w, hw, hEq⟩
        have hwpos : w = pos := R.h.injective hEq
        simpa [hwpos] using hw
      · intro hw
        exact ⟨pos, hw, rfl⟩
    change C.map.toPlaneMapWithMissing.pos (hbase.vertexEquiv v) ∈
        frontier (hbase.faceOfDart d).val ↔ _
    rw [hpos, hface, R.faceEquiv_val]
    exact hfront.trans (h.vertex_frontier_incidence d v)

/-- Helper toward Proposition 5.16. Transport the v3 candidate representation
predicate across an orientation-preserving geometric rooted-map isomorphism. -/
theorem D39DrawingRepresents3.transportGeometric
    {M : D39RootedMap} {B C : D39DomainRootedMapV2}
    (R : D39GeomRootedMapIsoV2 B.map B.root C.map C.root)
    (h : D39DrawingRepresents3 M B) : D39DrawingRepresents3 M C := by
  rcases h with ⟨data⟩
  exact ⟨data.transportGeometricData R⟩


/- The following full-binder target is not yet a declaration.

Separate-star uniqueness:
∀ {M N : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N B)
    (ι : M.core.D ≃ N.core.D),
  (∀ d, y.dartEquiv (ι d) = x.dartEquiv d) →
  (∀ d, y.vertexEquiv
      (rootedLocallyFiniteVertexClass N.core.rot (ι d)) =
    x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d)) →
  ∀ d, ι (M.core.rot d) = N.core.rot (ι d)

Three proof routes for this remaining statement were checked. The existing
`d39CcwSuccessor_unique` applies only when both witnesses use the same
direction function. Identifying the arc data does not identify the two
straightening homeomorphisms or their direction functions. Composing one
straightening homeomorphism with the inverse of the other reduces the issue
to proving that an orientation-preserving homeomorphism carrying radial
segments to radial segments preserves their angular cyclic order. Finally,
the winding-preservation definition of `OrientationPreserving` suggests a
proof by winding of loops around radial segments, but no checked API lemma
currently converts that winding statement to `CcwSuccessor`. No tangent,
smoothness, or regularity hypothesis was added. -/

end DirectedDistances.PlanarMap

end
